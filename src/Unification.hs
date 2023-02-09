
module Unification (unify, solve, unifySp) where

import qualified Data.Array.FM as AFM
import qualified Data.Ref.F as RF
import IO
import GHC.Exts

import qualified MetaCxt as MC
import qualified LvlSet as LS
import Common
import CoreTypes
import Evaluation
import Exceptions

--------------------------------------------------------------------------------

-- | Forcing depending on conversion state.
forceCS :: MetaCxt -> ConvState -> Val -> IO Val
forceCS cxt cs v = case cs of
  Full -> forceAll cxt v
  _    -> force    cxt v
{-# inline forceCS #-}


-- PARTIAL RENAMINGS
--------------------------------------------------------------------------------

data PartialRenaming = PRen {
    occ :: MetaVar          -- ^ Occurring meta to be checked.
  , dom :: Lvl              -- ^ Domain context size (context of output term)
  , cod :: Lvl              -- ^ Codomain context size (context of input value)
  , ren :: AFM.Array Lvl    -- ^ Partial mapping from cod vars to dom vars,
                            --   (-1) denotes an undefined value. Indices above the
                            --   array length are considered to be mapped to themselves.
  }

instance Show PartialRenaming where
  show (PRen occ dom cod ren) = runIO do
    ren <- AFM.unsafeFreeze ren
    pure $! show (occ, dom, cod, ren)

-- | Lift a renaming over a bound variable. The new var is mapped to itself.
lift :: PartialRenaming -> PartialRenaming
lift (PRen m dom cod ren) = PRen m (dom + 1) (cod + 1) ren
{-# inline lift #-}


-- SOLUTION QUOTATION
--------------------------------------------------------------------------------

approxOccursInSolution :: MetaCxt -> MetaVar -> MetaVar -> MetaVar -> IO UBool
approxOccursInSolution ms frz occ x
  | x < frz   = pure UTrue
  | otherwise = MC.read ms x >>= \case
      Unsolved _ | occ == x  -> pure UFalse
                 | otherwise -> pure UTrue
      Solved cache _ t _ -> do
        cached <- RF.read cache
        if cached == occ then
          pure UTrue
        else do
          res <- approxOccurs ms frz occ t
          when (res == UTrue) (RF.write cache occ)
          pure res

approxOccurs :: MetaCxt -> MetaVar -> MetaVar -> Tm -> IO UBool
approxOccurs ms frz occ t = let
  go = approxOccurs ms frz occ; {-# inline go #-}
  in case t of
    LocalVar x     -> pure UTrue
    TopVar x _     -> pure UTrue
    Let x a t u    -> (\x y z -> x &&# y &&# z) <$> go a <*> go t <*> go u
    App t u i      -> (&&#) <$> go t <*> go u
    Lam _ t        -> go t
    InsertedMeta x -> approxOccursInSolution ms frz occ x
    Meta x         -> approxOccursInSolution ms frz occ x
    Pi _ a b       -> (&&#) <$> go a <*> go b
    Irrelevant     -> pure UTrue
    U              -> pure UTrue

rigidQuoteSp :: MetaCxt -> MetaVar -> PartialRenaming -> Tm -> Spine -> IO Tm
rigidQuoteSp ms frz pren hd = \case
  SId         -> pure hd
  SApp sp t i -> App <$> rigidQuoteSp ms frz pren hd sp
                     <*> rigidQuote ms frz pren t
                     <*> pure i

rigidQuote :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> IO Tm
rigidQuote ms frz pren t = let
  go       = rigidQuote ms frz pren; {-# inline go #-}
  goSp     = rigidQuoteSp ms frz pren; {-# inline goSp #-}
  goSpFlex = flexQuoteSp ms frz pren; {-# inline goSpFlex #-}
  goBind t = rigidQuote ms frz (lift pren) (appCl' ms t (VLocalVar (cod pren) SId))
  {-# inline goBind #-}

  in force ms t >>= \case
    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        (AFM.read (ren pren) (coerce x)) >>= \case
          (-1) -> throw $ UnifyEx Conversion -- scope check
          y    -> goSp (LocalVar (lvlToIx (dom pren) y)) sp
      | otherwise ->
        -- TODO: simplify arith expr here (LocalVar (cod pren - x - 1))
        goSp (LocalVar (lvlToIx (dom pren) (x - (cod pren - dom pren)))) sp

    VFlex x sp
      | occ pren == x -> throw $ UnifyEx Conversion -- occurs check
      | otherwise     -> goSp (Meta x) sp

    topt@(VUnfold h sp t) -> do
      (t, tValid) <- case h of    -- WARNING: Core was fine here, but should be checked on ghc change
        UHTopVar x v -> do
          goSpFlex (TopVar x (coerce v) // UTrue) sp
        UHSolved x -> do
          xValid <- approxOccursInSolution ms frz (occ pren) x
          goSpFlex (Meta x // xValid) sp

      when (tValid == UFalse) $
        fullCheckRhs ms frz pren topt

      pure t

    VLam xi t   -> Lam xi <$> goBind t
    VPi xi a b  -> Pi xi <$> go a <*> goBind b
    VU          -> pure U
    VIrrelevant -> pure Irrelevant

flexQuoteSp :: MetaCxt -> MetaVar -> PartialRenaming -> (Tm, UBool) -> Spine -> IO (Tm, UBool)
flexQuoteSp ms frz pren hd@(t, !tValid) = \case
  SId         -> pure hd
  SApp sp t i -> do
    (sp, spValid) <- flexQuoteSp ms frz pren hd sp
    (t, tValid)   <- flexQuote   ms frz pren t
    pure $! (App sp t i // spValid &&# tValid)

flexQuote :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> IO (Tm, UBool)
flexQuote ms frz pren t = let
  go       = flexQuote ms frz pren; {-# inline go #-}
  goSp     = flexQuoteSp ms frz pren; {-# inline goSp #-}
  goBind t = flexQuote ms frz (lift pren) (appCl' ms t (VLocalVar (cod pren) SId))
  {-# inline goBind #-}

  in force ms t >>= \case
    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        (AFM.read (ren pren) (coerce x)) >>= \case
          (-1) -> pure (Irrelevant, UFalse)
          y    -> goSp (LocalVar (lvlToIx (dom pren) y) // UTrue) sp
      | otherwise ->
        -- TODO: simplify arith expr here (LocalVar (cod pren - x - 1))
        goSp (LocalVar (lvlToIx (dom pren) (x - (cod pren - dom pren))) // UTrue) sp

    VFlex x sp
      | occ pren == x -> pure (Irrelevant, UFalse)
      | otherwise     -> goSp (Meta x // UTrue) sp

    topt@(VUnfold h sp t) -> do
      (t, tf) <- case h of    -- WARNING: Core was fine here, but should be checked on ghc change
        UHTopVar x v -> do
          goSp (TopVar x (coerce v) // UTrue) sp
        UHSolved x -> do
          xf <- approxOccursInSolution ms frz (occ pren) x
          goSp (Meta x // xf) sp

      when (tf == UFalse) $
        fullCheckRhs ms frz pren topt

      pure $! (t // UTrue)

    VLam xi t -> do
      (!t, !tValid) <- goBind t
      pure $! (Lam xi t // tValid)

    VPi xi a b -> do
      (a, aValid) <- go a
      (b, bValid) <- goBind b
      pure $! (Pi xi a b // aValid &&# bValid)

    VU          -> pure (U // UTrue)
    VIrrelevant -> pure (Irrelevant // UTrue)

fullCheckSp :: MetaCxt -> MetaVar -> PartialRenaming -> Spine -> IO ()
fullCheckSp ms frz pren = \case
  SId         -> pure ()
  SApp sp t i -> fullCheckSp ms frz pren sp >> fullCheckRhs ms frz pren t

fullCheckRhs :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> IO ()
fullCheckRhs ms frz pren v = do
  let go       = fullCheckRhs ms frz pren;  {-# inline go #-}
      goSp     = fullCheckSp ms frz pren;   {-# inline goSp #-}
      goBind t = fullCheckRhs ms frz (lift pren)
                    (appCl' ms t (VLocalVar (cod pren) SId))
      {-# inline goBind #-}

  forceAll ms v >>= \case

    VFlex m' sp | occ pren == m' -> throw $ UnifyEx Conversion -- occurs check
                | otherwise      -> goSp sp

    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        (AFM.read (ren pren) (coerce x)) >>= \case
          (-1) -> throw $ UnifyEx Conversion -- scope check
          y    -> goSp sp
      | otherwise ->
        goSp sp

    VLam _ t    -> goBind t
    VPi _ a b   -> go a >> goBind b
    VUnfold{}   -> impossible
    VU          -> pure ()
    VIrrelevant -> pure ()


-- UNIFICATION
--------------------------------------------------------------------------------

-- | Invert a spine, producing a partial renaming. The "trim" argument is the
--   set of vars that we already dropped by eta-contracting the two sides.
invertSp :: MetaCxt -> Lvl -> MetaVar -> Spine -> LS.LvlSet -> IO PartialRenaming
invertSp ms gamma m sp trim = do
  ren <- AFM.new @Lvl (coerce gamma)
  AFM.set ren (-1)

  let go :: MetaCxt -> AFM.Array Lvl -> LS.LvlSet -> Spine -> IO Lvl
      go ms ren trim = \case
        SId         -> pure 0
        SApp sp t _ -> do
          dom <- go ms ren trim sp
          forceAll ms t >>= \case
            VLocalVar x SId -> do

              -- non-linear: variable was previously trimmed by eta-contraction
              when (LS.member x trim) (throw $ UnifyEx Conversion)

              y <- AFM.read ren (coerce x)
              case y of
                (-1) -> do
                  AFM.write ren (coerce x) dom
                  pure $! (dom + 1)

                -- non-linear: variable already mapped
                y -> throw $ UnifyEx Conversion
            _ ->
              throw $ UnifyEx Conversion -- non-var in spine

  dom <- go ms ren trim sp
  pure (PRen m dom gamma ren)

lams :: Spine -> Tm -> Tm
lams SId           acc = acc
lams (SApp sp t i) acc = lams sp (Lam (NI NX i) acc)

data SSLS = SSLS Spine Spine LS.LvlSet

-- | Try to eta contract both sides, bind trimmed lhs, rhs, and the set of
--   variables that were trimmed.
etaContract :: Spine -> Val -> (Spine -> Val -> LS.LvlSet -> IO a) -> IO a
etaContract sp rhs cont = let

  go :: Spine -> Spine -> LS.LvlSet -> IO SSLS
  go sp sp' trim = case (sp, sp') of
    (left@(SApp sp (VLocalVar x SId) i), right@(SApp sp' (VLocalVar x' SId) i')) -> do
      when (LS.member x trim) (throw $ UnifyEx Conversion) -- non-linear spine
      if x == x' then go sp sp' (LS.insert x trim)
                 else pure (SSLS left right trim)
    (sp, sp') -> pure (SSLS sp sp' trim)

  in case rhs of
    VFlex x sp'     -> go sp sp' mempty >>= \case
                         SSLS sp sp' trim -> cont sp (VFlex x sp') trim
    VLocalVar x sp' -> go sp sp' mempty >>= \case
                         SSLS sp sp' trim -> cont sp (VLocalVar x sp') trim
    VUnfold h sp' v -> go sp sp' mempty >>= \case
                         SSLS sp sp' trim -> cont sp (VUnfold h sp' v) trim
    _               -> cont sp rhs mempty
{-# inline etaContract #-}

solve :: MetaCxt -> Lvl -> MetaVar -> MetaVar -> Spine -> Val -> IO ()
solve ms l frz x ~sp ~rhs = do
  -- debug ["attempt solve", show (VFlex x sp), show rhs]
  when (x < frz) $ throw $ UnifyEx $ FrozenSolution x

  -- TURN OFF eta-contraction here

  etaContract sp rhs \sp rhs trim -> do

  -- do
  --   let trim = mempty

    pren <- invertSp ms l x sp trim
    rhs <- lams sp <$> rigidQuote ms frz pren rhs
    debug ["renamed", show rhs]
    debug ["solve", show x, show pren, show rhs]
    MC.solve ms x rhs (eval ms ENil rhs)

-- | Try to solve a meta, but fully eta-expand sides.
solveLong :: MetaCxt -> Lvl -> MetaVar -> MetaVar -> Spine -> Val -> IO ()
solveLong ms l frz x sp rhs = forceAll ms rhs >>= \case
  VLam (NI _ i) t ->
    let v = VLocalVar l SId
    in solveLong ms (l + 1) frz x (SApp sp v i) (appCl' ms t v)
  VFlex x' sp' | x == x'   -> unifySp ms l frz Full sp sp'
               | otherwise -> flexFlex ms l frz (VFlex x sp) x sp rhs x' sp'
  _ ->
    solve ms l frz x sp rhs

flexFlex :: MetaCxt -> Lvl -> MetaVar -> Val -> MetaVar -> Spine -> Val -> MetaVar -> Spine -> IO ()
flexFlex ms l frz t x ~sp t' x' ~sp' =
  solve ms l frz x sp t' `catch` \_ ->
  solve ms l frz x' sp' t

unifySp :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Spine -> Spine -> IO ()
unifySp ms l frz cs sp sp' = case (sp, sp') of
  (SId,         SId          ) -> pure ()
  (SApp sp t _, SApp sp' t' _) -> unifySp ms l frz cs sp sp' >>
                                  unify ms l frz cs (gjoin t) (gjoin t')
  _                            -> throw $ UnifyEx Conversion

unify :: MetaCxt -> Lvl -> MetaVar -> ConvState -> G -> G -> IO ()
unify ms l frz cs (G topt ftopt) (G topt' ftopt') = let
  go       = unify ms l frz cs; {-# inline go #-}
  go' t t' = go (gjoin t) (gjoin t'); {-# inline go' #-}
  err      = throw (UnifyEx Conversion); {-# inline err #-}

  goBind t t' =
    let v = VLocalVar l SId
    in unify ms (l + 1) frz cs (gjoin $! appCl' ms t v)
                               (gjoin $! appCl' ms t' v)
  {-# inline goBind #-}

  guardCS cs = when (cs == Flex) $ throw $ UnifyEx FlexSolution
  {-# inline guardCS #-}

  in do
    -- turn off speculative conversion here:

    -- t  <- forceAll ms ftopt
    -- t' <- forceAll ms ftopt'
    t  <- forceCS ms cs ftopt
    t' <- forceCS ms cs ftopt'
    case (t, t') of

      -- rigid, canonical
      (VLocalVar x sp  , VLocalVar x' sp'   ) | x == x' -> unifySp ms l frz cs sp sp'
      (VLam _ t        , VLam _ t'          )           -> goBind t t'
      (VPi (NI _ i) a b, VPi (NI _ i') a' b') | i == i' -> go' a a' >> goBind b b'
      (VU              , VU                 )           -> pure ()

      (VFlex x sp, VFlex x' sp')
        | x == x'   -> unifySp ms l frz cs sp sp'
        | otherwise -> guardCS cs >> flexFlex ms l frz topt x sp topt' x' sp'

      (VUnfold h sp t, VUnfold h' sp' t') -> case cs of
        Rigid | eqUH h h' -> unifySp ms l frz Flex sp sp'
                                `catch` \_ -> unify ms l frz Full (G topt t) (G topt' t')
              | otherwise -> unify ms l frz Rigid (G topt t) (G topt' t')
        Flex  | eqUH h h' -> unifySp ms l frz Flex sp sp'
              | otherwise -> err
        _                 -> impossible

      (VFlex x sp, t') -> do
        guardCS cs
        solve ms l frz x sp topt' `catch` \_ ->
          solveLong ms l frz x sp t'

      (t, VFlex x' sp') -> do
        guardCS cs
        solve ms l frz x' sp' topt `catch` \_ ->
          solveLong ms l frz x' sp' t

      (VUnfold h sp t, t') -> case cs of
        Rigid -> go (G topt t) (G topt' t')
        Flex  -> err
        _     -> impossible
      (t, VUnfold h' sp' t') -> case cs of
        Rigid -> go (G topt t) (G topt' t')
        Flex  -> err
        _     -> impossible

      (t, t') -> unifyCold ms l frz cs t t'


-- | Function factored out to handle `Irrelevant` values and eta-conversion
--   cases. These are quite rare, so it seems to be a good idea to remove them
--   from hot code.
unifyCold :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Val -> Val -> IO ()
unifyCold ms l frz cs ~t ~t' = case (t, t') of

  (VIrrelevant, _          ) -> pure ()
  (_          , VIrrelevant) -> pure ()

  (VLocalVar x sp, VLam (NI _ i) t')  ->
    let v = VLocalVar l SId
    in unifySpCold ms (l + 1) frz cs x (SApp sp v i) (appCl' ms t' v)
  (VLam (NI _ i) t, VLocalVar x' sp') ->
    let v = VLocalVar l SId
    in unifySpCold ms (l + 1) frz cs x' (SApp sp' v i) (appCl' ms t v)
  _ ->
    throw (UnifyEx Conversion)
{-# noinline unifyCold #-}

unifySpCold :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Lvl -> Spine -> Val -> IO ()
unifySpCold ms l frz cs x sp v = forceCS ms cs v >>= \case
  VIrrelevant ->
    pure ()
  VLam (NI _ i) t' ->
    let v = VLocalVar l SId
    in unifySpCold ms (l + 1) frz cs x (SApp sp v i) (appCl' ms t' v)
  VLocalVar x' sp' | x == x' ->
    unifySp ms l frz cs sp sp'
  _ ->
    throw (UnifyEx Conversion)
