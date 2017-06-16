module Language.IceT.Types where
import Prelude hiding (and, or)
import Control.Monad.State
import Data.Map.Strict as M
import Data.List as L hiding (and, or)
-------------------------------------------------------------------------------
-- Programs
-------------------------------------------------------------------------------
type Id = String

data Program a = Prog { decls   :: [Binder]
                      , prog    :: Stmt a
                      , ensures :: Prop a
                      }  
  deriving (Show)

data Stmt a = Skip a
            | Par Id Id (Prop a) (Stmt a) a
            | Assign Id Binder Id (Expr a) a
            | Seq [Stmt a] a
            | Atomic (Stmt a) a
            | Assume (Prop a) a
            | Assert (Prop a) Bool a
            | If (Prop a) (Stmt a) (Stmt a) a
            | Cases (Expr a) [Case a] a
            | ForEach Binder Binder (Id, Prop a) (Stmt a) a
            | While Id (Stmt a) a
            deriving (Eq, Show)

data Case a = Case { caseGuard :: Expr a
                   , caseStmt  :: Stmt a
                   , caseAnnot :: a
                   }
  deriving (Eq, Show)
            
data Expr a = Const Int
            | EmptySet
            | NonDetValue
            | Var Id
            | Select (Expr a) (Expr a)
            | Store (Expr a) (Expr a) (Expr a)
            | Bin Op (Expr a) (Expr a)
  deriving (Eq, Show)

data Op     = Plus
            | Minus
            | SetSubSingle -- Xs - {x}
            | SetAdd
  deriving (Eq, Show)

pc :: Id -> Id -> Expr a
pc ps p = Select (Var (pcName ps)) (Var p)

pcName :: Id -> Id
pcName ps = "pc!" ++ ps
  

writes :: Stmt a -> [Binder]
writes = nub . go
  where
    go (Skip _)           = []
    go (If _ s1 s2 _)     = go s1 ++ go s2
    go (Atomic s _)       = go s
    go (Assign _ x _ _ _) = [x]
    go (Seq stmts _)      = stmts >>= go
    go (ForEach x _ _ s _)= x : go s
    go (While _ s _)      = go s
    go (Cases _ cs _)     = cs >>= go . caseStmt
    go (Par _ _ _ s _)    = go s
    go (Assert _ _ _)     = []
    go (Assume _ _ )      = []
-------------------------------------------------------------------------------
-- Actions
-------------------------------------------------------------------------------
data Action a = Action [Binder] [Prop a] Int [(Prop a, Int)] (Stmt a)
  deriving Show

ins :: Int -> Prop a -> Maybe [(Prop a, Int)] -> Maybe [(Prop a, Int)]
ins v g Nothing   = Just [(g,v)]
ins v g (Just vs) = Just ((g,v):vs)

data CFG a = CFG { c     :: Int
                 , path  :: [Prop a]
                 , binds :: [Binder]
                 , m     :: M.Map Int [(Prop a, Int)]
                 }  
type CfgM s a = State (CFG s) a
buildCFG :: Int -> Stmt a -> CfgM a (Int, [Action a])
buildCFG from (Atomic s _)
  = do i  <- gets c
       p  <- gets path
       bs <- gets binds
       modify $ \s -> s { c = i + 1, m = M.alter (ins (from + 1) TT) from (m s) }
       return (from+1, [Action bs p (from+1) [] s])
buildCFG from s@(Assign _ _ _ _ l)
  = buildCFG from (Atomic s l)
buildCFG from (Skip _)
  = return (from, [])
buildCFG from (ForEach x xs (r, i) s l)
  = do pushForLoop x xs $ do
         (out, as) <- buildCFG from s
         modify $ \s -> s { m = M.alter (ins (from+1) TT) out (m s) }
         return (out, as)
buildCFG from (Seq ss _) = do (l, as) <- foldM go (from, []) ss
                              return (l, concat as)
  where
    go (l, s0) s = do (l', s') <- buildCFG l s
                      return (l', s':s0)
buildCFG _ s = error "buildCFG"

pushForLoop :: Binder -> Binder -> CfgM s a -> CfgM s a
pushForLoop x xs act
  = do vs0 <- gets binds
       p0  <- gets path
       modify $ \s -> s { binds = x : vs0
                        , path = Atom SetMem (Var $ bvar x) (Var $ bvar xs) : p0
                        }
       r  <- act
       modify $ \s -> s { binds = vs0, path = p0 }
       return r 

assgn :: Id -> Id -> Stmt ()
assgn x y = Atomic (Assign "" (Bind x Int) "" (Var y) ()) ()

actions :: Stmt a -> CFG a -> ([Action a], [Int])
actions s st0
  = ([ Action bs ps i (getOuts i) s | Action bs ps i _ s <- as ], exitNodes cfg)
  where
     cfg           = m st
     ((_, as), st) = runState (buildCFG 0 s) st0  
     getOuts i     = M.findWithDefault [] i cfg

exitNodes :: M.Map Int [(Prop a, Int)] -> [Int]
exitNodes m = [ i | i <- outs, i `notElem` ins ]
  where
    ins  = M.keys m
    outs = nub $ M.foldr' (\outs0 outs -> outs ++ (snd <$> outs0)) [] m
  
cfg s = m . snd $ runState (buildCFG 0 s) (CFG 0 [] [] M.empty)


-------------------------------------------------------------------------------
-- Formulas
-------------------------------------------------------------------------------
data Prop a = TT
            | FF
            | Atom Rel (Expr a) (Expr a)
            | Not (Prop a)
            | And [Prop a]
            | Or [Prop a]
            | Prop a :=>: Prop a
            | Forall [Binder] (Prop a)
            | Here (Expr a)
            | Prop Int
            | NonDetProp
            deriving (Eq, Show)
data Binder = Bind { bvar :: Id, bsort :: Sort }
  deriving (Eq, Show)
data Sort = Int | Set | Map Index Sort
  deriving (Eq, Show)
data Index = SetIdx Id
           | IntIdx
  deriving (Eq, Show)

data Rel = Eq | Le |  Lt | SetMem
  deriving (Eq, Show)

and :: [Prop a] -> Prop a
and ps  = case compact ps of
            []  -> TT
            [p] -> p
            ps'  -> And ps'
or ps = case compact ps of
          [] -> FF
          [p] -> p
          ps' -> Or ps'
compact ps = L.filter (/= TT) (simplify <$> ps)
simplify (p :=>: TT) = TT
simplify (TT :=>: p) = p
simplify (And ps)    = and ps
simplify (Or ps)     = or  ps
simplify p           = p

class Subst b where
  subst :: Id -> (Expr a) -> b a -> b a

instance Subst Expr where
  subst _ _ (Const i)
    = Const i
  subst x e v@(Var y)
    | x == y    = e
    | otherwise = v
  subst x e (Bin o e1 e2)
    = Bin o (subst x e e1) (subst x e e2)
  subst x e (Select e1 e2)
    = Select (subst x e e1) (subst x e e2)
  subst x e (Store e1 e2 e3)
    = Store (subst x e e1) (subst x e e2) (subst x e e3)
  subst _ _ EmptySet
    = EmptySet
  subst _ _ NonDetValue
    = NonDetValue

instance Subst Prop where
  subst x e                 = go
    where go (Atom r e1 e2) = Atom r (subst x e e1) (subst x e e2)
          go (Not p)        = Not (subst x e p)
          go (And ps)       = And (go <$> ps)
          go (Or ps)        = Or (go <$> ps)
          go (p :=>: q)     = go p :=>: go q
          go (Forall xs p)
            | x `elem` (bvar <$> xs)
            = Forall xs p
            | otherwise
            = Forall xs (go p)
          go TT             = TT
          go FF             = FF
          go (Prop i)       = Prop i
          go (Here e')      = Here $ subst x e e'
          go (NonDetProp)   = NonDetProp
