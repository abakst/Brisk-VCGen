module Language.IceT.SMT where
import Language.IceT.Types
import Text.PrettyPrint.HughesPJ

class SMT a where
  smt :: a -> Doc

instance SMT (Prop a) where
  smt TT             = text "true"
  smt FF             = text "false"
  smt (Atom r e1 e2) = parens (smt r <+> smt e1 <+> smt e2)
  smt (Not p)        = parens (text "not" <+> (smt p))
  smt (And ps)       = parens (text "and" $$ vcat (fmap smt ps))
  smt (Or ps)        = parens (text "or"  $$ vcat (fmap smt ps))
  smt (p :=>: q)     = parens (text "=>" <+> (smt p $+$ smt q))
  smt (Forall xs p)  = parens (text "forall" <+> parens (vcat (fmap smt xs))
                                             $+$ smt p)
instance SMT Binder where
  smt b = parens (text (bvar b) <+> smt (bsort b))

instance SMT Index where
  smt _ = smt Int

instance SMT Sort where
  smt Int       = text "Int"
  smt Set       = text "Set"
  smt (Map s t) = parens (text "Array" <+> smt s <+> smt t)

instance SMT (Expr a) where
  smt NonDetValue   = error "nondetvalue"
  smt (Const i)     = int i
  smt (Var x)       = text x
  smt (Bin o e1 e2) = parens (smt o <+> smt e1 <+> smt e2)
  smt (Select x y)  = parens (text "select" <+> smt x <+> smt y)
  smt (Store x y z) = parens (text "store" <+> smt x <+> smt y <+> smt z)
  smt EmptySet      = text "set_emp"

instance SMT Op where
  smt Plus  = text "+"
  smt Minus = text "-"
  smt SetSubSingle = text "set_minus"
  smt SetAdd = text "set_add"
  
instance SMT Rel where
  smt Eq     = text "="
  smt Lt     = text "<"
  smt SetMem = text "set_mem"
