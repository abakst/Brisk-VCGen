{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
module Language.IceT.VCGen (verifyFile, verifyProgram) where
import Language.IceT.Types
import Language.IceT.SMT
import Language.IceT.Parse (parseFile, parseString)

import Control.Monad.State
import Data.List
import qualified Data.Map.Strict as M
import Text.PrettyPrint.HughesPJ
import Text.Printf
import System.Exit
import System.Process
import GHC.IO.Handle

-- import Debug.Trace
-- dbg :: Show a => String -> a -> a
-- dbg msg x = trace (printf "[%s]: %s\n" msg (show x)) x
-------------------------------------------------------------------------------
-- IO one-stop-shop
-------------------------------------------------------------------------------
verifyProgram :: String -> IO Bool
verifyProgram 
  = verify . parseString
  
verifyFile :: FilePath -> IO Bool
verifyFile fp
  = parseFile fp >>= verify

verify :: VCAnnot a
       => Program a
       -> IO Bool
verify p
  = do (inp, out, err, pid) <- runInteractiveProcess "z3" ["-smt2", "-in"] Nothing Nothing
       hPutStr inp vcstr
       -- putStrLn vcstr
       hFlush inp
       ec   <- waitForProcess pid
       outp <- hGetContents out
       errp <- hGetContents err
       case ec of
         ExitSuccess ->
           return ("unsat" `isInfixOf` outp)
           
         ExitFailure _ -> do
           putStrLn outp
           putStrLn errp
           return False
  where
    vcstr = render $ vcGen (decls p) (prog p) (ensures p)
-------------------------------------------------------------------------------
-- Build the VC
-------------------------------------------------------------------------------
type VCAnnot a = (Show a, Process a)

class Process a where
  process :: a -> Id

instance Process Id where
  process = id

vcGen :: VCAnnot a
      => [Binder]
      -> Stmt a
      -> Prop a
      -> Doc
vcGen g s p
  = vcat (prelude : declBinds g ++ [checkValid (And vcs)])
  where
    vcs       = pre : reverse (cond <$> sides st)
    γ         = tyEnv g
    (pre, st) = runState (liftSetStmt s >>= flip wlp p) (VCState { sides = [], tenv = γ, constrs = M.empty })

-- The parsed types are wrong
liftSetStmt :: VCAnnot a => Stmt a -> VCGen a (Stmt a)  
liftSetStmt (Assign x e p)
  = do t   <- getType (bvar x)
       e'  <- ifM (isIndex t pid) isIdx (return e)
       return $ Assign x{ bsort = t } e' p

  where
    pid   = process p
    isIdx = do e' <- liftSetExpr e pid
               return (Store (Var (bvar x)) (Var pid) e')
liftSetStmt (ForEach x xs inv s)
  = do addElem (bvar xs) (bvar x)
       s' <- liftSetStmt s
       removeElem (bvar x)
       return (ForEach x xs inv s')
liftSetStmt (Cases e cs p)
  = do e'  <- liftSetExpr e (process p)
       cs' <- mapM go cs
       return $ Cases e' cs' p
  where
    go (Case g s q) = do g' <- liftSetExpr g (process q)
                         s' <- liftSetStmt s
                         return (Case g' s' q)
liftSetStmt (While x s p)
  = do s' <- liftSetStmt s
       return (While x s' p)
liftSetStmt (Seq stmts l)
  = Seq <$> mapM liftSetStmt stmts <*> pure l
liftSetStmt (Skip l)
  = return $ Skip l


liftSetExpr :: VCAnnot a => Expr a -> Id -> VCGen a (Expr a)
liftSetExpr v@(Var x) p
  = do t <- getType x
       ifM (isIndex t p)
           (return $ Select v (Var p)) 
           (return v)
liftSetExpr (Select e1 e2) p
  = Select <$> liftSetExpr e1 p <*> liftSetExpr e2 p
liftSetExpr (Store e1 e2 e3) p
  = Store <$> liftSetExpr e1 p <*> liftSetExpr e2 p <*> liftSetExpr e3 p
liftSetExpr (Bin o e1 e2) p
  = Bin o <$> liftSetExpr e1 p <*> liftSetExpr e2 p
liftSetExpr e _
  = return e

isIndex :: Sort -> Id -> VCGen a Bool
isIndex (Map (SetIdx ps) _) p
  = return True --isElem p ps
isIndex _ _
  = return False

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mb t e
  = do b <- mb
       if b then t else e

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
wlp (Assign _ NonDetValue _) p
  = return p

wlp (Assign x e _) p
  = return $ subst (bvar x) e p

wlp (Seq stmts _) p
  = foldM (flip wlp) p (reverse stmts)

wlp (Cases NonDetValue cs _) p
  = And <$> mapM (flip wlp p . caseStmt) cs
wlp (Cases e cs _) p
  = And <$> mapM go cs
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
data VCState a = VCState { sides :: [SideCondition a]
                         , tenv  :: M.Map Id Sort
                         , constrs :: M.Map Id Id
                         }
type VCGen a r = State (VCState a) r 
data SideCondition a = Initiation { cond :: Prop a }
                     | Inductive  { cond :: Prop a }

addSideCondition :: SideCondition a -> VCGen a ()
addSideCondition p
  = modify $ \s -> s { sides = p : sides s }

tyEnv :: [Binder] -> M.Map Id Sort
tyEnv bs = M.fromList [ (x,t) | Bind x t <- bs ]

addElem :: Id -> Id -> VCGen a ()  
addElem ps p
  = modify $ \s -> s { constrs = M.insert p ps (constrs s) }

removeElem :: Id -> VCGen a ()
removeElem p
  = modify $ \s -> s { constrs = M.delete p (constrs s) }

isElem :: Id -> Id -> VCGen a Bool
isElem p ps
  = do g <- gets constrs
       return $ maybe False (==ps) $ M.lookup p g

getType :: Id -> VCGen a Sort
getType x
  = do γ <- gets tenv
       case M.lookup x γ of
         Just t  -> return t
         Nothing -> error (printf "Unknown id: %s" x)
  
-------------------------------------------------------------------------------
-- Scratch
-------------------------------------------------------------------------------
-- testLoop :: Stmt a
-- testLoop =
--   ForEach (Bind "x" Int) (Bind "xs" Set)
--     ("rest", Forall [Bind "i" Int] $
--                Atom SetMem (Var "i") (Var "rest") :=>:
--                Atom Eq (Var "i") (Const 1))
--     (Bind "y" Int :<-: Const 0)

-- testProp :: Prop a
-- testProp =
--   Forall [Bind "i" Int] $
--     (Atom SetMem (Var "i") (Var "xs")) :=>:
--     (Atom Eq (Var "i") (Const 0))

-------------------
-- Two Phase Commit
-------------------
-- vint :: Id -> Binder
-- vint x = Bind x Int

-- vmap :: Id -> Binder
-- vmap x = Bind x (Map IntIdx Int)

-- vset :: Id -> Binder
-- vset x = Bind x Set

-- twoPhaseDecls :: [Binder]
-- twoPhaseDecls = [ vint "proposal"
--                 , vset "P"
--                 , vint "committed"
--                 , vint "abort"
--                 , vmap "val"
--                 , vmap "value"
--                 , vint "c"
--                 , vmap "id"
--                 , vint "msg"
--                 , vmap "pmsg"
--                 , vint "reply"
--                 ]

-- twoPhase :: Stmt ()
-- twoPhase
--   = Seq [ vint "committed" :<-: false
--         , vint "abort" :<-: false

--         , ForEach (vint "p") (Bind "P" Set)
--           ( "_rest"
--           , Forall [Bind "i" Int]
--             ( Atom SetMem (Var "i") (Var "_rest")
--               :=>:
--               Atom Eq (Select (Var "val") (Var "i"))
--               (Var "proposal")
--             )
--           ) $
--           Seq [ vmap "id"  :<-: Store (Var "id") (Var "p") (Var "c")
--               , vmap "val" :<-: Store (Var "val") (Var "p") (Var "proposal")
--               ] ()

--         , ForEach (vint "p") (Bind "P" Set)
--           ( "_rest"
--           , Forall [Bind "i" Int] $
--             And [ Atom SetMem (Var "i") (Var "_rest")
--                 , Atom Eq (Var "committed") true
--                 ]
--             :=>:
--             Atom Eq (Select (Var "value") (Var "i"))
--                     (Select (Var "val") (Var "i"))
--           )
--           (Seq [ vint "ndet" :<-: NonDetValue
--                , Cases (Var "ndet") [ Case true $
--                                       Seq [ vint "msg"  :<-: vcommit
--                                           , vmap "pmsg" :<-: Store (Var "pmsg") (Var "p") vcommit
--                                           ]
--                                       ()
                               
--                                     , Case false $
--                                       Seq [ vint "msg"   :<-: vabort
--                                           , vint "abort" :<-: true
--                                           , vmap "pmsg"  :<-: Store (Var "pmsg") (Var "p") vabort
--                                           ]
--                                       ()
--                                     ]
--                  ()
--                ]
--             ())

--         , Cases (Var "abort") [ Case false $
--                                 Seq [ vint "reply" :<-: vcommit
--                                     , vint "committed" :<-: true
--                                     ]
--                                 ()

--                               , Case true $
--                                 vint "reply" :<-: vabort
--                               ]
--         ()
--         , ForEach (vint "p") (Bind "P" Set)
--           ("_rest", TT) $
--           Seq [ vmap "decision" :<-: Store (Var "decision") (Var "p") (Var "reply")
--               , Cases (Select (Var "decision") (Var "p"))
--                 [ Case vcommit $
--                   vmap "value" :<-: Store (Var "value") (Var "p") (Select (Var "val") (Var "p"))

--                 , Case vabort $
--                   Skip ()
--                 ]
--                 ()
--               ]
--           ()
--         ]
--     ()
--   where
--     false = Const 0
--     true  = Const 1

--     vabort  = Const 0
--     vcommit = Const 1

-- twoPhaseDebug :: Prop ()
-- twoPhaseDebug
--   = Forall [vint "i"] $
--       And [ Atom SetMem (Var "i") (Var "P") ]
--       :=>:
--       Atom Eq (Select (Var "val") (Var "i")) (Var "proposal")

-- twoPhaseSafety :: Prop ()
-- twoPhaseSafety
--   = Forall [vint "i"] $
--       And [ Atom SetMem (Var "i") (Var "P"), Atom Eq (Var "committed") (Const 1) ]
--       :=>: FF
      -- Atom Eq (Var "proposal")
      --         (Select (Var "value") (Var "i"))
{-> vcGen twoPhaseDecls twoPhase twoPhaseSafety
-}
