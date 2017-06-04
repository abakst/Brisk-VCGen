{-# LANGUAGE ConstraintKinds #-}
module Language.IceT.VCGen where

import Control.Monad.State
import Language.IceT.Types
import Language.IceT.SMT
import Text.PrettyPrint.HughesPJ
import Text.Printf

type VCAnnot a = Show a 

vcGen :: VCAnnot a => Stmt a -> Prop a -> Doc
vcGen s p
  = vcat $ fmap smt vcs
  where
    vcs       = pre : reverse (cond <$> sides st)
    (pre, st) = runState (wlp s p) (VCState { sides = [] })

-------------------------------------------------------------------------------
-- Weakest Liberal Preconditions
-------------------------------------------------------------------------------
wlp :: VCAnnot a => Stmt a -> Prop a -> VCGen a (Prop a)   
wlp (Skip _) p
  = return p

-- Fresh var
wlp (_ :<-: NonDetValue) p
  = return p

wlp (x :<-: e) p
  = return $ subst (bvar x) e p

wlp (Seq stmts _) p
  = foldM (flip wlp) p (reverse stmts)

wlp (Cases e cs _) p
  = Or <$> mapM go cs
  where
    go c
      = do wp <- wlp (caseStmt c) p
           return (Atom Eq e (caseGuard c)  :=>: wp)

wlp (ForEach x xs (rest, i) s) p
  = do pre <- wlp s $ subst rest (Bin SetSubSingle erest ex) i
       return $ And [ subst rest EmptySet i
                    , Forall vs $ And [ i
                                      , Atom SetMem ex exs 
                                      , Not $ Atom SetMem ex erest
                                      ]
                                  :=>:
                                  pre
                    , Forall vs $ subst rest (Var (bvar xs)) i :=>: p
                    ]
  where
    ex        = Var (bvar x)
    exs       = Var (bvar xs)
    erest     = Var rest
    vs        = x : Bind rest Set : writes s

wlp s _
  = error (printf "wlp TBD: %s" (show s))

-------------------------------------------------------------------------------
-- Monads
-------------------------------------------------------------------------------
data VCState a = VCState { sides :: [SideCondition a] }
type VCGen a r = State (VCState a) r 
data SideCondition a = Initiation { cond :: Prop a }
                     | Inductive  { cond :: Prop a }

addSideCondition :: SideCondition a -> VCGen a ()
addSideCondition p
  = modify $ \s -> s { sides = p : sides s }


-------------------------------------------------------------------------------
-- Scratch
-------------------------------------------------------------------------------
testLoop :: Stmt a
testLoop =
  ForEach (Bind "x" Int) (Bind "xs" Set)
    ("rest", Forall [Bind "i" Int] $
               Atom SetMem (Var "i") (Var "rest") :=>:
               Atom Eq (Var "i") (Const 1))
    (Bind "y" Int :<-: Const 0)

testProp :: Prop a
testProp =
  Forall [Bind "i" Int] $
    (Atom SetMem (Var "i") (Var "xs")) :=>:
    (Atom Eq (Var "i") (Const 0))

-------------------
-- Two Phase Commit
-------------------
vint :: Id -> Binder
vint x = Bind x Int

vmap :: Id -> Binder
vmap x = Bind x (Map Int Int)

twoPhase :: Stmt ()
twoPhase
  = Seq [ vint "committed" :<-: false
        , vint "abort" :<-: false

        , ForEach (vint "p") (Bind "P" Set)
          ( "_rest"
          , Forall [Bind "i" Int]
            ( Atom SetMem (Var "i") (Var "_rest")
              :=>:
              Atom Eq (Select (Var "val") (Var "i"))
              (Var "proposal")
            )
          ) $
          Seq [ vmap "id"  :<-: Store (Var "id") (Var "p") (Var "c")
               , vmap "val" :<-: Store (Var "val") (Var "p") (Var "proposal")
               ] ()

        , ForEach (vint "p") (Bind "P" Set)
          ( "_rest"
          , Forall [Bind "i" Int] $
            And [ Atom SetMem (Var "i") (Var "_rest")
                , Atom Eq (Var "committed") true
                ]
            :=>:
            Atom Eq (Select (Var "value") (Var "i"))
                    (Select (Var "val") (Var "i"))
          )
          (Seq [ vint "ndet" :<-: NonDetValue
               , Cases (Var "ndet") [ Case true $
                                      Seq [ vint "msg"  :<-: vcommit
                                          , vmap "pmsg" :<-: Store (Var "pmsg") (Var "p") vcommit
                                          ]
                                      ()
                               
                                    , Case false $
                                      Seq [ vint "msg"   :<-: vabort
                                          , vint "abort" :<-: true
                                          , vmap "pmsg"  :<-: Store (Var "pmsg") (Var "p") vabort
                                          ]
                                      ()
                                    ]
                 ()
               ]
            ())

        , Cases (Var "abort") [ Case false $
                                Seq [ vint "reply" :<-: vcommit
                                    , vint "committed" :<-: true
                                    ]
                                ()

                              , Case true $
                                vint "reply" :<-: vabort
                              ]
        ()

        , ForEach (vint "p") (Bind "P" Set)
          ("_rest", TT) $
          Seq [ vmap "decision" :<-: Store (Var "decision") (Var "p") (Var "reply")
              , Cases (Select (Var "decision") (Var "p"))
                [ Case vcommit $
                  vmap "value" :<-: Store (Var "value") (Var "p") (Select (Var "val") (Var "p"))

                , Case vabort $
                  Skip ()
                ]
                ()
              ]
          ()
        ]
    ()
  where
    false = Const 0
    true  = Const 1

    vabort  = Const 0
    vcommit = Const 1
{-> vcGen twoPhase TT -}
