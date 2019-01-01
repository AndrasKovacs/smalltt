
module Evaluation where

import qualified SmallArray as SA
import qualified Data.Array.Dynamic as A
import Control.Monad.Except

import Common
import ElabState
import Syntax
import Values
import Pretty
import Cxt

-- import Text.Printf

-- Rule rewriting
--------------------------------------------------------------------------------

data MatchFailure = MFRigid | MFFlex Meta

-- INFELICITY: we don't use the Val parts of evaluated lhs spine at all. We
-- only have the Val-s there so that the matching function becomes
-- simpler, since it uniformly works on GV-s. If we wanted to get rid
-- of the useless Val-s, we'd need to write additional code: a) A full
-- non-local evaluator returning Val-s b) A matching function which
-- matches Val-s against GVs.
-- (TODO to rectify)

matchLHS :: Lvl -> RewriteRule -> GSpine -> VSpine -> ExceptT MatchFailure IO Glued
matchLHS topLvl (RewriteRule varNum vars lhsSp lhs rhs) gsp vsp = do

  -- lift $ printf "trying to match %s with %s\n\n"
  --   (show lhsSp) (showGlued mempty NNil (GNe (HTopRigid (Int2 0 0)) gsp vsp))


  start <- lift (A.size ruleVarStack)
  let end = start + varNum
  lift $ A.pushN ruleVarStack REUnsolved varNum

  let (gEnv, vEnv) = go start ENil ENil where
        go i gsp vsp | i == end = (gsp, vsp)
        go i gsp vsp = go (i + 1) (EDef gsp (gRuleVar i)) (EDef vsp (VRuleVar i))

  -- lift $ printf "created local envs\n"

  let match :: Glued -> GV -> ExceptT MatchFailure IO ()
      match = go topLvl where

        goSp :: Lvl -> GSpine -> GSpine -> VSpine -> ExceptT MatchFailure IO ()
        goSp l (SAppI gsp g) (SAppI gsp' g') (SAppI vsp' v') =
          goSp l gsp gsp' vsp' >> go l g (GV g' v')
        goSp l (SAppE gsp g) (SAppE gsp' g') (SAppE vsp' v') =
          goSp l gsp gsp' vsp' >> go l g (GV g' v')
        goSp d SNil SNil SNil = pure ()
        goSp _ _    _    _    = error "gvUnify.goSp: impossible"

        go :: Lvl -> Glued -> GV -> ExceptT MatchFailure IO ()
        go l g (GV g' v') = case (gForce l g, gForce l g') of
          (GNe (HRuleVar x) gsp vsp, g')    | start <= x && x < end -> solve l x gsp (GV g' v')
          (GNe h gsp vsp, GNe h' gsp' vsp') | h == h' -> goSp l gsp gsp' vsp'
          (GNe (HMeta x) gsp vsp, g')   -> throwError (MFFlex x)
          (g, GNe (HMeta x') gsp' vsp') -> throwError (MFFlex x')

          (GU, GU) -> pure ()

          (GLam (Named n i) t, GLam _ t') -> let var = gvLocal l in
            go (l + 1) (gInst l t var) (gvInst l t' var)

          (GLam (Named n i) t, t'       ) -> let var = gvLocal l in
            go (l + 1) (gInst l t var) (gvApp i l t' var)

          (t     , GLam (Named n' i') t') -> let var = gvLocal l in
            go (l + 1) (gApp i' l t var) (gvInst l t' var)

          (GPi (Named n i) (GV a _) b, GPi (Named _ i') a' b') | i == i' -> do
            let var = gvLocal l
            go l a a'
            go (l + 1) (gInst l b var) (gvInst l b' var)

          (GPi (Named n i) (GV a _) b, GFun a' b') -> do
            go l a a'
            go (l + 1) (gInst l b (gvLocal l)) b'

          (GFun (GV a _) (GV b _), GPi (Named n' i') a' b') -> do
            go l a a'
            go (l + 1) b (gvInst l b' (gvLocal l))

          (GFun (GV a _) (GV b _), GFun a' b') -> go l a a' >> go l b b'

          _ -> throwError MFRigid

        solve :: Lvl -> Lvl -> GSpine -> GV -> ExceptT MatchFailure IO ()
        solve l x gsp gv
          | l == topLvl, SNil <- gsp = lift (A.write ruleVarStack x (RESolved gv))
          | otherwise = error "match.solve: higher-order rewrite rules not yet supported"
        {-# inline solve #-}

      matchLHS :: ExceptT MatchFailure IO ()
      matchLHS = go (SA.size lhsSp - 1) gsp vsp where
        go i (SAppI gsp g) (SAppI vsp v) = go (i - 1) gsp vsp
                                        >> match (gEval varNum gEnv vEnv (SA.index lhsSp i))
                                                 (GV g v)
        go i (SAppE gsp g) (SAppE vsp v) = go (i - 1) gsp vsp
                                        >> match (gEval varNum gEnv vEnv (SA.index lhsSp i))
                                                 (GV g v)
        go i SNil          SNil          = pure ()
        go _ _             _             = error "matchLHS: impossible"

      evalRhs :: IO Glued
      evalRhs = go start ENil ENil where
        go i gs vs | i == end = do
          A.popN ruleVarStack varNum
          pure (gEval varNum gs vs rhs)
        go i gs vs = lookupRuleVarIO i >>= \case
          RESolved (GV g v) -> go (i + 1) (EDef gs g) (EDef vs v)
          REUnsolved -> error "non-deterministic rewrite rule"

  matchLHS `catchError` \e -> do
    -- lift $ printf "match failed\n\n"
    lift (A.popN ruleVarStack varNum)
    throwError e
  -- lift $ printf "matched lhs\n\n"
  lift evalRhs
{-# inline matchLHS #-}

gRewriteIO :: Lvl -> Lvl -> GSpine -> VSpine -> IO Glued
gRewriteIO l x gsp vsp = lookupTopIO x >>= \case
  TEPostulate numRules rules arity _ _ _ ->
    let overapply = spineLength gsp - arity
        gsp'      = dropSpine overapply gsp
        vsp'      = dropSpine overapply vsp
        gspRest   = takeSpine overapply gsp
        vspRest   = takeSpine overapply vsp
        go :: [RewriteRule] -> IO Glued
        go (r:rs) = do
          runExceptT (matchLHS l r gsp' vsp') >>= \case
            Left (MFFlex (Meta _ j)) -> pure (GNe (HTopBlockedOnMeta (Int2 x j)) gsp vsp)
            Left MFRigid             -> go rs
            Right g                  -> pure (gAppSpine l g gspRest vspRest)
        go []     = pure (GNe (HTopRigid (Int2 x numRules)) gsp vsp)
    in go rules
  _ -> error "gRewrite: impossible"

gRewrite :: Lvl -> Lvl -> GSpine -> VSpine -> Glued
gRewrite l x gsp vsp = runIO (gRewriteIO l x gsp vsp)

gSaturatedRewriteIO :: Lvl -> Lvl -> GSpine -> VSpine -> IO Glued
gSaturatedRewriteIO l x gsp vsp = lookupTopIO x >>= \case
  TEPostulate numRules rules arity _ _ _ -> do
    let go :: [RewriteRule] -> IO Glued
        go (r:rs) = runExceptT (matchLHS l r gsp vsp) >>= \case
          Left (MFFlex (Meta _ j)) -> pure (GNe (HTopBlockedOnMeta (Int2 x j)) gsp vsp)
          Left MFRigid             -> go rs
          Right g                  -> pure g
        go []     = pure (GNe (HTopRigid (Int2 x numRules)) gsp vsp)
    go rules
  _ -> error "gRewrite: impossible"

gSaturatedRewrite :: Lvl -> Lvl -> GSpine -> VSpine -> Glued
gSaturatedRewrite l x gsp vsp = runIO (gSaturatedRewriteIO l x gsp vsp)


-- Glued evaluation
--------------------------------------------------------------------------------

gLocal :: GEnv -> Ix -> Box Glued
gLocal = go where
  go (EDef gs g) 0 = Box g
  go (ESkip gs)  0 = let l = envLength gs in Box (GLocal l)
  go (EDef gs _) x = go gs (x - 1)
  go (ESkip gs)  x = go gs (x - 1)
  go ENil        x = error "gLocal: impossible"

gTop :: Lvl -> Box Glued
gTop x = case lookupTop x of
  TEDefinition (GV g _) _ _ _ _  -> Box g
  TEPostulate 0 _ _ _ _ _        -> Box (GNe (HTopRigid (Int2 x 0)) SNil SNil)
  TEPostulate _ _ arity _ _ _    -> Box (GNe (HTopUnderapplied (Int2 x arity)) SNil SNil)
  TERewriteRule{}                -> error "gTop: impossible"
{-# inline gTop #-}

-- | We use this to avoid allocating useless thunks for looking up variables
--   from environments.
gEvalBox :: Lvl -> GEnv -> VEnv -> Tm -> Box Glued
gEvalBox l gs vs = \case
  LocalVar x  -> gLocal gs x
  TopVar   x  -> gTop x
  MetaVar  x  -> case lookupMeta x of MESolved (GV g _) _ _ _ -> Box g; _ -> Box (GMeta x)
  t           -> Box (gEval l gs vs t)
{-# inline gEvalBox #-}

gRuleVar :: Lvl -> Glued
gRuleVar x = case lookupRuleVar x of RESolved (GV g _) -> g; _ -> GRuleVar x
{-# inline gRuleVar #-}

gMetaVar :: Meta -> Glued
gMetaVar x = case lookupMeta x of MESolved (GV g _) _ _ _ -> g; _ -> GMeta x
{-# inline gMetaVar #-}

gEval :: Lvl -> GEnv -> VEnv -> Tm -> Glued
gEval l gs vs = \case
  LocalVar x  -> let Box g = gLocal gs x in g
  TopVar   x  -> let Box g = gTop x in g
  MetaVar  x  -> gMetaVar x
  RuleVar  x  -> gRuleVar x
  AppI t u    -> let Box gu = gEvalBox l gs vs u
                 in gAppI l (gEval l gs vs t) (GV gu (vEval vs u))
  AppE t u    -> let Box gu = gEvalBox l gs vs u
                 in gAppE l (gEval l gs vs t) (GV gu (vEval vs u))
  Lam x t     -> GLam x (GCl gs vs t)
  Pi x a b    -> let Box ga = gEvalBox l gs vs a
                 in GPi x (GV ga (vEval vs a)) (GCl gs vs b)
  Fun t u     -> let Box gt = gEvalBox l gs vs t; Box gu = gEvalBox l gs vs u
                 in GFun (GV gt (vEval vs t)) (GV gu (vEval vs u))
  U           -> GU
  Let _ t u   -> let Box gt = gEvalBox l gs vs t
                 in gEval l (EDef gs gt) (EDef vs (vEval vs u)) u
  Irrelevant  -> GIrrelevant


gInst :: Lvl -> GCl -> GV -> Glued
gInst l (GCl gs vs t) (GV g v) = gEval l (EDef gs g) (EDef vs v) t
{-# inline gInst #-}

gAppI :: Lvl -> Glued -> GV -> Glued
gAppI l (GLam _ t) gv = gInst l t gv
gAppI l (GNe (HTopUnderapplied (Int2 x arity)) gsp vsp) (GV g v) =
  case arity of
    1 -> gSaturatedRewrite l x (SAppI gsp g) (SAppI vsp v)
    _ -> GNe (HTopUnderapplied (Int2 x (arity - 1))) (SAppI gsp g) (SAppI vsp v)
gAppI l (GNe h gsp vsp) (GV g v) = GNe h (SAppI gsp g) (SAppI vsp v)
gAppI _ _ _ = error "gvAppI : impossible"
{-# inline gAppI #-}

gAppE :: Lvl -> Glued -> GV -> Glued
gAppE l g gv = case (g, gv) of
  (GLam _ t, gv) -> gInst l t gv
  (GNe h@(HTopUnderapplied (Int2 x arity)) gsp vsp, GV g v) ->
    case arity of
      1 -> gSaturatedRewrite l x (SAppE gsp g) (SAppE vsp v)
      _ -> GNe (HTopUnderapplied (Int2 x (arity - 1))) (SAppE gsp g) (SAppE vsp v)
  (GNe h gsp vsp, GV g v) -> GNe h (SAppE gsp g) (SAppE vsp v)
  _ -> error "gvAppI : impossible"
{-# inline gAppE #-}

gApp :: Icit -> Lvl -> Glued -> GV -> Glued
gApp Impl = gAppI
gApp Expl = gAppE
{-# inline gApp #-}

gAppSpine :: Lvl -> Glued -> GSpine -> VSpine -> Glued
gAppSpine l g (SAppI gsp g') (SAppI vsp v) = gAppI l (gAppSpine l g gsp vsp) (GV g' v)
gAppSpine l g (SAppE gsp g') (SAppE vsp v) = gAppE l (gAppSpine l g gsp vsp) (GV g' v)
gAppSpine l g SNil           SNil          = g
gAppSpine l _ _              _             = error "gAppSpine: impossible"

gForce :: Lvl -> Glued -> Glued
gForce l g = case g of
  GNe (HMeta x) gsp vsp
    | MESolved (GV g _) _ _ _ <- lookupMeta x -> gForce l (gAppSpine l g gsp vsp)
  GNe (HTopBlockedOnMeta (Int2 x mj)) gsp vsp
    | MESolved{} <- lookupActiveMeta mj -> gForce l (gRewrite l x gsp vsp)
  GNe (HRuleVar x) gsp vsp
    | RESolved (GV g _) <- lookupRuleVar x -> gForce l (gAppSpine l g gsp vsp)
  GNe (HTopRigid (Int2 x n)) gsp vsp
    | case gsp of SNil -> False; _ -> True,
      TEPostulate n' _ _ _ _ _ <- lookupTop x, n' > n -> gForce l (gRewrite l x gsp vsp)
  g -> g

--------------------------------------------------------------------------------

topNumRulesIO :: Lvl -> IO Int
topNumRulesIO x = lookupTopIO x >>= \case
  TEPostulate num _ _ _ _ _ -> pure num
  _                         -> pure 0
{-# inline topNumRulesIO #-}

topNumRules :: Lvl -> Int
topNumRules x = runIO (topNumRulesIO x)
{-# inline topNumRules #-}

vLocal :: VEnv -> Ix -> Box Val
vLocal = go where
  go (EDef vs v) 0 = Box v
  go (ESkip vs)  0 = let l = envLength vs in Box (VLocal l)
  go (EDef vs _) x = go vs (x - 1)
  go (ESkip vs)  x = go vs (x - 1)
  go ENil        x = error "vLocal: impossible"

-- | We use this to avoid allocating useless thunks for looking up variables
--   from environments.
vEvalBox :: VEnv -> Tm -> Box Val
vEvalBox vs = \case
  LocalVar x -> vLocal vs x
  TopVar x   -> Box (VTop (Int2 x (topNumRules x)))
  MetaVar x  -> Box (VMeta x)
  t          -> Box (vEval vs t)
{-# inline vEvalBox #-}

vEval :: VEnv -> Tm -> Val
vEval vs = \case
  LocalVar x  -> let Box v = vLocal vs x in v
  TopVar x    -> VTop (Int2 x (topNumRules x))
  MetaVar x   -> case lookupMeta x of MESolved (GV _ v) True t _ -> v; _ -> VMeta x
  RuleVar x   -> VRuleVar x
  AppI t u    -> let Box vu = vEvalBox vs u in vAppI (vEval vs t) vu
  AppE t u    -> let Box vu = vEvalBox vs u in vAppE (vEval vs t) vu
  Lam x t     -> VLam x (VCl vs t)
  Pi x a b    -> let Box va = vEvalBox vs a in VPi x va (VCl vs b)
  Fun t u     -> let Box vt = vEvalBox vs t; Box vu = vEvalBox vs u
                 in VFun vt vu
  U           -> VU
  Let _   t u -> vEval (EDef vs (vEval vs t)) u
  Irrelevant  -> VIrrelevant


vInst :: VCl -> Val -> Val
vInst (VCl vs t) ~u = vEval (EDef vs u) t
{-# inline vInst #-}

vAppI :: Val -> Val -> Val
vAppI (VLam _ t) ~u = vInst t u
vAppI (VNe h vs) ~u = VNe h (SAppI vs u)
vAppI _ ~_ = error "vAppI: impossible"
{-# inline vAppI #-}

vAppE :: Val -> Val -> Val
vAppE (VLam _ t) ~u = vInst t u
vAppE (VNe h vs) ~u = VNe h (SAppE vs u)
vAppE _ ~_ = error "vAppE: impossible"
{-# inline vAppE #-}

vApp :: Icit -> Val -> Val -> Val
vApp i (VLam _ t) ~u = vInst t u
vApp i (VNe h vs) ~u = case i of Impl -> VNe h (SAppI vs u)
                                 Expl -> VNe h (SAppE vs u)
vApp _ _ _ = error "vApp: impossible"
{-# inline vApp #-}

vAppSpine :: Val -> VSpine -> Val
vAppSpine v (SAppI vs v') = vAppI (vAppSpine v vs) v'
vAppSpine v (SAppE vs v') = vAppE (vAppSpine v vs) v'
vAppSpine v SNil          = v

vForce :: Val -> Val
vForce = \case
  VNe (HMeta x) vs | MESolved (GV _ v) True _ _ <- lookupMeta x ->
    vForce (vAppSpine v vs)
  v -> v

--------------------------------------------------------------------------------

gvEval :: Lvl -> GEnv -> VEnv -> Tm -> GV
gvEval l gs vs t = GV (gEval l gs vs t) (vEval vs t)
{-# inline gvEval #-}

gvInst :: Lvl -> GCl -> GV -> GV
gvInst l (GCl gs vs t) (GV g v) =
  let vs' = EDef vs v
      gs' = EDef gs g
  in GV (gEval l gs' vs' t) (vEval vs' t)
{-# inline gvInst #-}

gvAppI :: Lvl -> Glued -> GV -> GV
gvAppI l (GLam _ t) gv = gvInst l t gv
gvAppI l (GNe (HTopUnderapplied (Int2 x arity)) gsp vsp) (GV g v) =
  let vsp' = SAppI vsp v
  in case arity of
       1 -> GV (gSaturatedRewrite l x (SAppI gsp g) vsp')
               (VNe (HTopRigid (Int2 x 0)) vsp')
       _ -> let h' = HTopUnderapplied (Int2 x (arity - 1))
            in GV (GNe h' (SAppI gsp g) vsp') (VNe h' vsp')
gvAppI l (GNe h gsp vsp) (GV g v) =
  let vsp' = SAppI vsp v
  in GV (GNe h (SAppI gsp g) vsp') (VNe h vsp')
gvAppI _ _ _ = error "gvAppI : impossible"
{-# inline gvAppI #-}

gvAppE :: Lvl -> Glued -> GV -> GV
gvAppE l (GLam _ t) gv = gvInst l t gv
gvAppE l (GNe (HTopUnderapplied (Int2 x arity)) gsp vsp) (GV g v) =
  let vsp' = SAppE vsp v
  in case arity of
       1 -> GV (gSaturatedRewrite l x (SAppE gsp g) vsp')
               (VNe (HTopRigid (Int2 x 0)) vsp')
       _ -> let h' = HTopUnderapplied (Int2 x (arity - 1))
            in GV (GNe h' (SAppE gsp g) vsp') (VNe h' vsp')
gvAppE l (GNe h gsp vsp) (GV g v) =
  let vsp' = SAppE vsp v
  in GV (GNe h (SAppE gsp g) vsp') (VNe h vsp')
gvAppE _ _ _ = error "gvAppI : impossible"
{-# inline gvAppE #-}


gvApp :: Icit -> Lvl -> Glued -> GV -> GV
gvApp Impl = gvAppI
gvApp Expl = gvAppE
{-# inline gvApp #-}

-- Quoting
--------------------------------------------------------------------------------

-- | Quote local value.
vQuote :: Lvl -> Val -> Tm
vQuote = go where
  go l v = case vForce v of
    VNe h vsp   -> goSp vsp where
                     goSp SNil = case h of
                       HMeta x                      -> MetaVar x
                       HLocal x                     -> LocalVar (l - x - 1)
                       HTopRigid (Int2 x _)         -> TopVar x
                       HTopBlockedOnMeta (Int2 x _) -> TopVar x
                       HTopUnderapplied (Int2 x _)  -> TopVar x
                       HRuleVar x                   -> RuleVar x
                     goSp (SAppI vsp t) = AppI (goSp vsp) (go l t)
                     goSp (SAppE vsp t) = AppE (goSp vsp) (go l t)
    VLam ni t   -> Lam ni (go (l + 1) (vInst t (VLocal l)))
    VPi ni a b  -> Pi ni (go l a) (go (l + 1) (vInst b (VLocal l)))
    VFun a b    -> Fun (go l a) (go l b)
    VU          -> U
    VIrrelevant -> Irrelevant

-- | Quote glued value to full normal form.
gQuote :: Lvl -> Glued -> Tm
gQuote = go where
  go l g = case gForce l g of
    GNe h gsp vsp          -> goSp gsp where
                                goSp SNil = case h of
                                  HMeta x                      -> MetaVar x
                                  HLocal x                     -> LocalVar (l - x - 1)
                                  HTopRigid (Int2 x _)         -> TopVar x
                                  HTopBlockedOnMeta (Int2 x _) -> TopVar x
                                  HTopUnderapplied (Int2 x _)  -> TopVar x
                                  HRuleVar x                   -> RuleVar x
                                goSp (SAppI vsp t) = AppI (goSp vsp) (go l t)
                                goSp (SAppE vsp t) = AppE (goSp vsp) (go l t)
    GLam ni t              -> Lam ni (go (l + 1) (gInst l t (gvLocal l)))
    GPi ni (GV a _) b      -> Pi ni (go l a) (go (l + 1) (gInst l b (gvLocal l)))
    GFun (GV a _) (GV b _) -> Fun (go l a) (go l b)
    GU                     -> U
    GIrrelevant            -> Irrelevant

-- | Quote local value while unfolding all metas.
vQuoteMetaless :: Lvl -> Val -> Tm
vQuoteMetaless = go where
  go l = \case
    VNe h vsp   -> case h of
                     HMeta x | MESolved (GV _ vt) _ _ _ <- lookupMeta x
                       -> go l (vAppSpine vt vsp)
                     HMeta x                      -> goSp l (MetaVar x) vsp
                     HLocal x                     -> goSp l (LocalVar (l - x - 1)) vsp
                     HTopRigid (Int2 x _)         -> goSp l (TopVar x) vsp
                     HTopBlockedOnMeta (Int2 x _) -> goSp l (TopVar x) vsp
                     HTopUnderapplied (Int2 x _)  -> goSp l (TopVar x) vsp
                     HRuleVar x                   -> goSp l (RuleVar x) vsp
    VLam ni t   -> Lam ni (go (l + 1) (vInst t (VLocal l)))
    VPi ni a b  -> Pi ni (go l a) (go (l + 1) (vInst b (VLocal l)))
    VFun a b    -> Fun (go l a) (go l b)
    VU          -> U
    VIrrelevant -> Irrelevant

  goSp l h SNil          = h
  goSp l h (SAppI vsp t) = AppI (goSp l h vsp) (go l t)
  goSp l h (SAppE vsp t) = AppE (goSp l h vsp) (go l t)

--------------------------------------------------------------------------------

showVal :: NameTable -> Names -> Val -> String
showVal ntbl ns = showTm ntbl ns . vQuote (namesLength ns)

showValMetaless :: NameTable -> Names -> Val -> String
showValMetaless ntbl ns = showTm ntbl ns . vQuoteMetaless (namesLength ns)

showValCxt :: Cxt -> Val -> String
showValCxt Cxt{..} = showTm _nameTable _names . vQuote _size

showValCxtMetaless :: Cxt -> Val -> String
showValCxtMetaless Cxt{..} = showValMetaless _nameTable _names

showGlued :: NameTable -> Names -> Glued -> String
showGlued ntbl ns = showTm ntbl ns . gQuote (namesLength ns)

showGluedCxt :: Cxt -> Glued -> String
showGluedCxt Cxt{..} = showGlued _nameTable _names

showGluedLvl :: Lvl -> Glued -> String
showGluedLvl l = showTm mempty NNil . gQuote l
