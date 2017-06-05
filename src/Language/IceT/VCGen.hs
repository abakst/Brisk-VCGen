{-# LANGUAGE ConstraintKinds #-}
module Language.IceT.VCGen where
import Language.IceT.Types
import Language.IceT.SMT

import Control.Monad.State
import Data.List
import Text.PrettyPrint.HughesPJ
import Text.Printf
import System.Exit
import System.Process
import GHC.IO.Handle

-------------------------------------------------------------------------------
-- IO one-stop-shop
-------------------------------------------------------------------------------
verify :: VCAnnot a
       => [Binder] -- Variable Declarations
       -> Stmt a   -- Program to verify
       -> Prop a   -- Property to satisfy
       -> IO Bool
verify decls s φ
  = do (inp, out, err, pid) <- runInteractiveProcess "z3" ["-smt2", "-in"] Nothing Nothing
       hPutStr inp vcstr
       hFlush inp
       ec   <- waitForProcess pid
       outp <- hGetContents out
       errp <- hGetContents err
       putStrLn outp
       case ec of
         ExitSuccess   -> return ("unsat" `isInfixOf` outp)
         ExitFailure _ -> do putStrLn errp
                             return False
  where
    vcstr = render $ vcGen decls s φ
-------------------------------------------------------------------------------
-- Build the VC
-------------------------------------------------------------------------------
type VCAnnot a = Show a 

vcGen :: VCAnnot a
      => [Binder]
      -> Stmt a
      -> Prop a
      -> Doc
vcGen g s p
  = vcat (prelude : declBinds g ++ [checkValid (And vcs)])
  where
    vcs       = pre : reverse (cond <$> sides st)
    (pre, st) = runState (wlp s p) (VCState { sides = [] })

checkValid :: Prop a -> Doc
checkValid f = parens (text "assert" <+> smt (Not f)) $+$ text "(check-sat)"

declBinds :: [Binder] -> [Doc]
declBinds = map declBind
  where
    declBind (Bind x s) = parens (text "declare-const" <+> text x <+> smt s)

prelude :: Doc
prelude
  = text $ unlines [ "(define-sort Elt () Int)"
                   , "(define-sort Set () (Array Elt Bool))"
                   , "(define-sort IntMap () (Array Elt Elt))"
                   , "(define-fun set_emp () Set ((as const Set) false))"
                   , "(define-fun set_mem ((x Elt) (s Set)) Bool (select s x))"
                   , "(define-fun set_add ((s Set) (x Elt)) Set  (store s x true))"
                   , "(define-fun set_cap ((s1 Set) (s2 Set)) Set ((_ map and) s1 s2))"
                   , "(define-fun set_cup ((s1 Set) (s2 Set)) Set ((_ map or) s1 s2))"
                   , "(define-fun set_com ((s Set)) Set ((_ map not) s))"
                   , "(define-fun set_dif ((s1 Set) (s2 Set)) Set (set_cap s1 (set_com s2)))"
                   , "(define-fun set_sub ((s1 Set) (s2 Set)) Bool (= set_emp (set_dif s1 s2)))"
                   , "(define-fun set_minus ((s1 Set) (x Elt)) Set (set_dif s1 (set_add set_emp x)))"
                   ]

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
  = do pre <- wlp s $ subst rest (Bin SetAdd erest ex) i
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

vset :: Id -> Binder
vset x = Bind x Set

twoPhaseDecls :: [Binder]
twoPhaseDecls = [ vint "proposal"
                , vset "P"
                , vint "committed"
                , vint "abort"
                , vmap "val"
                , vmap "value"
                , vint "c"
                , vmap "id"
                , vint "msg"
                , vmap "pmsg"
                , vint "reply"
                ]

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

twoPhaseDebug :: Prop ()
twoPhaseDebug
  = Forall [vint "i"] $
      And [ Atom SetMem (Var "i") (Var "P") ]
      :=>:
      Atom Eq (Select (Var "val") (Var "i")) (Var "proposal")

twoPhaseSafety :: Prop ()
twoPhaseSafety
  = Forall [vint "i"] $
      And [ Atom SetMem (Var "i") (Var "P"), Atom Eq (Var "committed") (Const 1) ]
      :=>:
      Atom Eq (Var "proposal")
              (Select (Var "value") (Var "i"))
{-> vcGen twoPhaseDecls twoPhase twoPhaseSafety
-}
