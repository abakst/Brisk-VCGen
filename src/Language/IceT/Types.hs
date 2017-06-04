module Language.IceT.Types where
import Data.List
-------------------------------------------------------------------------------
-- Programs
-------------------------------------------------------------------------------
type Id = String

data Stmt a = Skip a
            | Binder :<-: (Expr a)
            | Seq [Stmt a] a
            | Cases (Expr a) [Case a] a
            | ForEach Binder Binder (Id, Prop a) (Stmt a)
            | While Id (Stmt a)
            deriving (Eq, Show)

data Case a = Case { caseGuard :: Expr a
                   , caseStmt  :: Stmt a
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
  deriving (Eq, Show)

writes :: Stmt a -> [Binder]
writes = nub . go
  where
    go (Skip _)           = []
    go (x :<-: _)         = [x]
    go (Seq stmts _)      = stmts >>= go
    go (ForEach x _ _ s)  = x : go s
    go (While _ s)        = go s
    go (Cases _ cs _)     = cs >>= go . caseStmt
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
            deriving (Eq, Show)
data Binder = Bind { bvar :: Id, bsort :: Sort }
  deriving (Eq, Show)
data Sort = Int | Set | Map Sort Sort
  deriving (Eq, Show)

data Rel = Eq | Lt | SetMem
  deriving (Eq, Show)

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
