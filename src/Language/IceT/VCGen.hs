{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
module Language.IceT.VCGen (verifyFile, verifyProgram) where
import Prelude hiding (and, or)
import Language.IceT.Types
import Language.IceT.SMT
import Language.IceT.Pretty (pp, render)
import Language.IceT.Parse (parseFile, parseString)

import Control.Monad.State
import Data.List hiding (and, or)
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
{-> parseFile "tests/par.input"

Prog {decls = [Bind {bvar = "s", bsort = Set},Bind {bvar = "m", bsort = Int},Bind {bvar = "g", bsort = Int},Bind {bvar = "id", bsort = Map (SetIdx "s") Int}]
, prog = Par "P" "s" TT (Seq [Seq [Assign (Bind {bvar = "id", bsort = Int}) (Const 0) "P",Assert (Atom Le (Const 0) (Var "id")) "P"] "",Seq [Assign (Bind {bvar = "id", bsort = Int}) (Bin Plus (Var "id") (Const 1)) "P",Assert (Atom Le (Const 0) (Var "id")) "P"] ""] "") "", ensures = Forall [Bind {bvar = "p", bsort = Int}] (Atom SetMem (Var "p") (Var "s") :=>: Atom Le (Const 0) (Select (Var "id") (Var "p")))}
-}

verify :: VCAnnot a
       => Program a
       -> IO Bool
verify p
  = do (inp, out, err, pid) <- runInteractiveProcess "z3" ["-smt2", "-in"] Nothing Nothing
       hPutStr inp vcstr
       -- putStrLn vcstr
       writeFile ".query.icet" (render (pp (prog p)))
       writeFile ".query.smt2" vcstr
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
vcGen :: VCAnnot a
      => [Binder]
      -> Stmt a
      -> Prop a
      -> Doc
vcGen g s p
  = vcat (prelude : declBinds bs ++ [checkValid vc])
  where
    γ        = tyEnv g
    bs       = fmap (uncurry Bind) . M.toList $ tenv st
    (vc, st) = runState (replaceSorts s >>= flip wlp  p)
                         (VCState { tenv = γ
                                  , constrs = M.empty
                                  , ictr = 0
                                  , invs = []
                                  , gather = False
                                  })

replaceSorts :: VCAnnot a => Stmt a -> VCGen a (Stmt a)
replaceSorts (Assign p x q e l)
  = do t <- getType (bvar x)
       return $ Assign p x { bsort = t } q e l
replaceSorts (Seq stmts l)
  = flip Seq l <$> mapM replaceSorts stmts
replaceSorts (ForEach x xs inv s l)
  = do g <- gets constrs
       case M.lookup (process l) g of
         Nothing -> 
           ForEach x xs inv <$> replaceSorts s <*> pure l
         Just ps ->
           ForEach (liftSo x ps) xs inv <$> replaceSorts (subst (bvar x) xmap s) <*> pure l
  where
    liftSo x ps = x { bsort = Map (SetIdx ps) (bsort x) }
    xmap        = Select (Var (bvar x)) (Var (process l))
replaceSorts (If p s1 s2 l)
  = If p <$> replaceSorts s1 <*> replaceSorts s2 <*> pure l
replaceSorts (Par x xs inv s l)
  = do addElem xs x
       p <- Par x xs inv <$> replaceSorts s <*> pure l
       removeElem x
       return p
replaceSorts (Atomic s l)
  = flip Atomic l <$> replaceSorts s
replaceSorts s@(Assert _ _ _)
  = return s
replaceSorts s@(Skip _)
  = return s
replaceSorts s
  = error (printf "replaceSorts: %s" (show s))

isIndex :: Sort -> Id -> VCGen a Bool
isIndex (Map (SetIdx ps) _) p
  = isElem p ps
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
wlp (Assign _ _ _ NonDetValue _) p
  = return p

wlp (Assign a x b e l) p
  = do select <- isSet b
       let v = case e of
                 Var i | select -> Select e (Var b)
                 _  -> e
       ifM (isIndex (bsort x) pr)
          (return $ subst (bvar x) (Store (Var i) (Var pr) v) p)
          (return $ subst (bvar x) v p)
  where
    i  = bvar x
    pr = process l

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

wlp (ForEach x xs (rest, i) s _) p
  = do addElem (bvar xs) (bvar x)
       i'  <- gathering $ wlp s TT
       let i'' = subst (bvar xs) erest i'
       let inv = and [i, i'']
       pre <- wlp s $ subst rest (Bin SetAdd erest ex) inv
       removeElem (bvar x)
       return $ And [ subst rest EmptySet inv
                    , Forall vs $ And [ inv
                                      , Atom SetMem ex exs 
                                      , Not $ Atom SetMem ex erest
                                      ]
                                  :=>:
                                  pre
                    , Forall vs $ subst rest (Var (bvar xs)) inv :=>: p
                    ]
  where
    ex        = Var (bvar x)
    exs       = Var (bvar xs)
    erest     = Var rest
    vs        = x : Bind rest Set : writes s

wlp (Par i is _ s _) p
  = do modify $ \s -> s { tenv = M.insert (pcName is) (Map (SetIdx is) Int) (tenv s) }
       addElem is i
       bs      <- vcBinds
       let (acts, outs) = as bs
           actsLocs     = replaceHere i is <$> acts
           exitCond     = Or [pcGuard i is x | x <- outs]
       inv     <- actionsInvariant i0 is actsLocs
       let qInv = and [ inv
                      , pcGuard i0 is (-1) :=>: p
                      ]
           init = Forall [Bind i0 Int] $ and [ Atom SetMem (Var i0) (Var is)
                                             , pcGuard i0 is 0
                                             ]
           initial = init :=>: Forall [Bind i0 Int] (subst i (Var i0) inv)
       txns    <- mapM (wlpAction i is qInv) actsLocs
       removeElem i
       return $ and ([initial] ++ txns ++ [Forall bs (qInv :=>: p)])
  where
    as bs = actions i s (CFG 0 [] ([Bind i Int]++bs) M.empty)
    i0 = i ++ "!"
    --    let inv' = subst p (Var p0) inv
    -- p0   = p ++ "!!0"
       -- return (Forall [Bind p0 Int] inv')

wlp (Assert b pre _) p
  = do g <- gets gather
       if (g && pre) || (not g && not pre) then
         return (and [b, p])
       else
         return p
wlp (If c s1 s2 _) p
  = do φ <- wlp s1 p
       ψ <- wlp s2 p
       let guard p q = case c of
                         NonDetProp -> [p, q]
                         _          -> [c :=>: p, Not c :=>: q]
       return . and $ guard φ ψ

wlp s _
  = error (printf "wlp TBD: %s" (show s))
-------------------------------------------------------------------------------
-- Build Invariant from Assertions
-------------------------------------------------------------------------------
actionsInvariant :: (Show a, Process a)
                 => Id
                 -> Id
                 -> [Action a]
                 -> VCGen a (Prop a)
actionsInvariant p ps as
  = and <$> mapM oneConj as
  where
    oneConj (Action _ _ _ _ s)
     = gathering $ wlp s TT

-------------------------------------------------------------------------------
-- Actions
-------------------------------------------------------------------------------
wlpAction :: (Process a, Show a)
          => Id
          -> Id
          -> Prop a
          -> Action a
          -> VCGen a (Prop a)
wlpAction p ps inv (Action xs pcond i outs s)
  = do inductive <- wlp s post
       return $ Forall xs (g :=>: inductive)
  where
    post    = or [ invAt o | o <- outLocs ]
    invAt l = subst (pcName ps) (Store (Var (pcName ps)) (Var p) (Const l)) inv
    outLocs = if null outs then [-1] else snd <$> outs
    g       = and [ pathGuard pcond, Atom SetMem (Var p) (Var ps), pcGuard p ps i, inv ]

pathGuard :: [Prop a] -> Prop a
pathGuard []   = TT
pathGuard [p]  = p
pathGuard ps   = and ps

pcGuard :: Id -> Id -> Int -> Prop a
pcGuard p ps i = Atom Eq (pc ps p) (Const i)


replaceHere :: t -> Id -> Action a -> Action a
replaceHere _ ps (Action xs cond i outs s)
 = Action xs cond i outs (goStmt s)
  where
    goStmt (Assert φ b l)
      = Assert (goProp φ) b l
    goStmt (Seq stmts l)
      = Seq (goStmt <$> stmts) l
    goStmt (If c s1 s2 l)
      = If c (goStmt s1) (goStmt s2) l
    goStmt (ForEach x xs inv s l)
      = ForEach x xs inv (goStmt s) l
    goStmt s
      = s

    goProp (Here e)
      = Atom Eq (Select (Var (pcName ps)) e) (Const i)
    goProp (Forall xs a)
      = Forall xs $ goProp a
    goProp (a :=>: b)
      = goProp a :=>: goProp b
    goProp (And as)
      = And (goProp <$> as)
    goProp (Or as)
      = Or (goProp <$> as)
    goProp (Not a)
      = Not $ goProp a
    goProp a
      = a
--   = Seq (replaceHere i <$> stmts) l
-- replaceHere i is (Assert p l)
--   = Assert (hereProp i p) l

-- hereProp i (Here e)
--   = pcName

  
-------------------------------------------------------------------------------
-- Monads
-------------------------------------------------------------------------------
data VCState a = VCState { tenv  :: M.Map Id Sort
                         , constrs :: M.Map Id Id
                         , ictr :: Int
                         , invs :: [(Int, [Binder], Prop a)]
                         , gather :: Bool
                         }
type VCGen a r = State (VCState a) r 

gathering :: VCGen a b -> VCGen a b  
gathering mact
  = do modify $ \s -> s { gather = True }
       r <- mact
       modify $ \s -> s { gather = False }
       return r

tyEnv :: [Binder] -> M.Map Id Sort
tyEnv bs = M.fromList [ (x,t) | Bind x t <- bs ]

vcBinds :: VCGen a [Binder]
vcBinds =  fmap (uncurry Bind) . M.toList <$> gets tenv

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

isSet :: Id -> VCGen a Bool
isSet i
  = do g <- gets constrs
       return $ M.member i g

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
