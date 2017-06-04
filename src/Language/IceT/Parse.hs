module Language.IceT.Parse where
import Language.IceT.Types
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token


{-
Core languange:
---------------
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

parseString :: String -> Stmt ()
parseString str
  = case parse iceTParser "" str of
      Left e  -> error $ show e
      Right r -> r

iceTParser :: Parser (Stmt ())  
iceTParser = whiteSpace >> stmt

stmt =  skip
    <|> assignment
    <|> seqs
    <|> foreach
    <|> while

skip = reserved "skip" >> return (Skip ())

assignment = do reserved "assign"
                parens $ do
                  p <- ident
                  comma
                  x <- ident
                  comma
                  v <- expr
                  return $ Bind x Int :<-: v

seqs = do reserved "seq"
          stmts <- parens $ list stmt
          case stmts of
            [s] -> return s
            _   -> return $ Seq stmts ()

foreach = do reserved "for"  
             parens $ do
               who <- ident
               comma
               x   <- ident
               comma
               xs  <- ident
               comma
               s   <- stmt
               return $ ForEach (Bind x Int)
                                (Bind xs Set)
                                s
                                ("_rest", TT)
while = do reserved "While"
           parens $ do
             who <- ident
             comma
             (Var x) <- expr
             comma
             s <- stmt
             return $ While x s

list p = brackets $ commaSep p
  
expr = num <|> var

num = do i <- integer
         return $ Const (fromInteger i)
var = do i <- ident
         return $ Var i

lexer      = Token.makeTokenParser languageDef
ident      = Token.identifier lexer
reserved   = Token.reserved lexer
integer    = Token.integer lexer
comma      = Token.comma lexer
whiteSpace = Token.whiteSpace lexer
parens     = Token.parens lexer
brackets   = Token.brackets lexer
commaSep   = Token.commaSep lexer

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
                                   , "assign"
                                   , "cases"
                                   , "skip"
                                   ]
           , Token.reservedOpNames = [ "+", "<" ]
           }
