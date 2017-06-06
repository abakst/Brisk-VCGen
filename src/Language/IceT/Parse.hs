module Language.IceT.Parse where
import Language.IceT.Types
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token


{-
Core languange:
---------------
 prog(ds, t)         : declarations ds, trace t
 decl(x, s)          : declare x, sort s

 int                 : sorts
 map(s, s)           :
 set                 :

 par([A,B,C])        : A || B || C.
 seq([A,B,C])        : A; B; C.
 skip                : no-operation.
 send(p, x, v)       : process p sends value v to
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
 send(p, x, type, v)  : send a message of type "type".
 recv(p, v)          : process p receives value v.
 recv(p, x, v)       : process p receives value v from
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
  | x=type(t)        :       - of type t.
 recv(p, x, type, v) : receive messages of type "type", only.
 sym(P, S, A)        : composition of symmetric processes p in set s with source A.
                       s must be distinct from process ids.
 for(m, P, S, A)     : process m executes A for each process p in s.
 iter(p, k, A)       : process p executes A k-times.
 while(p, cond, A)   : process p executes A while cond is true.
 nondet(P, s, A)        : process P is chosen non-deterministically in A.
 assign(p, x, v)     : process p assigns value v to variable x.
 ite(P, Cond, A, B)  : process p executes A if Cond holds and B, otherwise.
 if(P, Cond, A)      : Short for ite(P, Cond, A, skip).
 pair(x, y)          : pair of values x and y.
 cases(p, x, C, d)   : proccess p performs a case switch on x with cases specified in
 | C=case(p, exp, A) : C and default case d.
 seq([x,y,z])
-}  

{-> parseString "for(P, X, bs, seq([assign(X,v,0),skip]))"
-}

type ParsedAnnot = Id  
type ParsedProgram = Program ParsedAnnot

parseFile :: String -> IO ParsedProgram
parseFile file
  = readFile file >>= return . parseString

parseString :: String -> ParsedProgram
parseString str
  = case parse iceTParser "" str of
      Left e  -> error $ show e
      Right r -> r

iceTParser :: Parser ParsedProgram  
iceTParser = whiteSpace >> program

program :: Parser ParsedProgram
program = do reserved "prog"  
             p <- parens $ do
               _    <- ident
               comma
               vars <- list decl
               comma
               p    <- functor "ensures" prop
               comma
               t     <- stmt
               return Prog { decls = vars
                           , ensures = p
                           , prog  = t
                           }
             dot
             return p

decl :: Parser Binder
decl = do reserved "decl"
          parens $ do
            v <- ident
            comma
            s <- sort
            return $ Bind v s

sort :: Parser Sort
sort = int <|> set <|> array

int, set, array :: Parser Sort
int   = reserved "int"    >> return Int
set   = reserved "set"    >> return Set
array = do reserved "map"
           parens $ do
             t1 <- index
             comma
             t2 <- sort
             return $ Map t1 t2

index :: Parser Index
index = (reserved "int" >> return IntIdx)
    <|> (reserved "set" >> parens ident >>= return . SetIdx)
            

stmt :: Parser (Stmt ParsedAnnot)
stmt =  skip
    <|> assignment
    <|> seqs
    <|> cases
    <|> foreach
    <|> while

skip, assignment, seqs, cases, foreach, while :: Parser (Stmt ParsedAnnot)
skip = reserved "skip" >> return (Skip "")

assignment = do reserved "assign"
                parens $ do
                  p <- ident
                  comma
                  x <- ident
                  comma
                  v <- expr
                  return $ Assign (Bind x Int) v p

seqs = do reserved "seq"
          stmts <- parens $ list stmt
          case stmts of
            [s] -> return s
            _   -> return $ Seq stmts ""

cases = functor "cases" $ do
  p <- ident
  comma
  discr <- expr
  comma
  cs <- list casestmt
  comma
  stmt
  return $ Cases discr cs p

casestmt = functor "case" $ do
  p <- ident
  comma
  e <- expr
  comma
  s <- stmt
  return $ Case e s p

foreach = functor "for" $ do
  x   <- ident
  comma
  xs  <- ident
  comma
  rest <- ident
  comma
  inv  <- prop
  comma
  s   <- stmt
  return $ ForEach (Bind x Int)
                   (Bind xs Set)
                   (rest, inv)
                   s
prop = (reserved "true"  >> return TT)
   <|> (reserved "false" >> return FF)
   <|> atom
   <|> implies
   <|> andProp
   <|> orProp
   <|> notProp
   <|> forallProp
   <|> elemProp

atom = do e1 <- expr
          r  <- rel
          e2 <- expr
          return $ Atom r e1 e2

rel = symbol "=" >> return Eq

forallProp = functor "forall" $ do
  ds <- list decl
  comma
  p <- prop
  return $ Forall ds p

implies = functor "implies" $ do
  p1 <- prop
  comma
  p2 <- prop
  return (p1 :=>: p2)

andProp = functor "and" $ do
  ps <- list prop
  return $ And ps

orProp = functor "or" $ do
  ps <- list prop
  return $ Or ps

notProp = functor "not" $ (Not <$> prop)

elemProp = functor "elem" $ do
  e1 <- expr
  comma
  e2 <- expr
  return $ Atom SetMem e1 e2

while = do reserved "While"
           parens $ do
             who <- ident
             comma
             (Var x) <- expr
             comma
             s <- stmt
             return $ While x s who

expr = num <|> var <|> sel <|> sel' <|> ndet

num = do i <- integer
         return $ Const (fromInteger i)
var = do i <- ident
         return $ Var i
sel = functor "sel" $ do
  e1 <- expr
  comma
  e2 <- expr
  return (Select e1 e2)
sel' = functor "ref" $ do
  e1 <- expr
  comma
  e2 <- expr
  return (Select e1 e2)

ndet = functor "ndet" whiteSpace >> return NonDetValue

list p = brackets $ commaSep p
functor f p = reserved f >> parens p

lexer      = Token.makeTokenParser languageDef
ident      = Token.identifier lexer
reserved   = Token.reserved lexer
integer    = Token.integer lexer
comma      = Token.comma lexer
dot        = Token.dot lexer
whiteSpace = Token.whiteSpace lexer
parens     = Token.parens lexer
brackets   = Token.brackets lexer
commaSep   = Token.commaSep lexer
symbol     = Token.symbol lexer

languageDef =
  emptyDef { Token.identStart    = letter
           , Token.identLetter   = alphaNum
           , Token.reservedNames = [ "par"
                                   , "seq"
                                   , "skip"
                                   , "for"
                                   , "iter"
                                   , "while"
                                   , "nondet"
                                   , "ndet"
                                   , "assign"
                                   , "cases"
                                   , "case"
                                   , "skip"
                                   , "prog"
                                   , "int"
                                   , "decl"
                                   , "map"
                                   , "true"
                                   , "false"
                                   , "implies"
                                   , "forall"
                                   , "and"
                                   , "or"
                                   , "not"
                                   , "elem"
                                   , "sel"
                                   , "ref"
                                   , "ensures"
                                   ]
           , Token.reservedOpNames = [ "+", "<" ]
           }
