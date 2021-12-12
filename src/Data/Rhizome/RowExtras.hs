{-# LANGUAGE ConstraintKinds #-}
module Data.Rhizome.RowExtras where
import Data.Row
import qualified Data.Row.Records as R
import Data.Kind
import Data.Proxy
import Data.Row.Records
import Data.Row.Dictionaries 
import Data.Row.Internal
import Data.Bifunctor
import Data.Functor.Const
import Control.Monad.Identity
import Data.Type.Equality
import Data.Singletons.Decide 
import Data.Singletons
import Data.Maybe
import Unsafe.Coerce
import Data.Singletons.TypeLits
import Data.Rhizome.Exists 
import Data.Row (AllUniqueLabels)

-- | This is the same as @(lazyRemove l r, r .! l)@.
lazyUncons :: KnownSymbol l => Label l -> Rec r -> (Rec (r .- l), r .! l)
lazyUncons l r = (R.lazyRemove l r, r .! l)

class ForallL (r :: Row k) (c :: Symbol -> k -> Constraint) -- (c' :: Symbol -> Constraint) 
  where
  -- | A metamorphism is an anamorphism (an unfold) followed by a catamorphism (a fold).
  -- The parameter 'p' describes the output of the unfold and the input of the fold.
  -- For records, @p = (,)@, because every entry in the row will unfold to a value paired
  -- with the rest of the record.
  -- For variants, @p = Either@, because there will either be a value or future types to
  -- explore.
  -- 'Const' can be useful when the types in the row are unnecessary.
  metamorphL :: forall (p :: Type -> Type -> Type) 
                       (f :: Row k -> Type) 
                       (g :: Row k -> Type) 
                       (h :: k -> Type)
             . Bifunctor p
            => Proxy (Proxy h, Proxy p)
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, HasType ℓ τ ρ)
               => Label ℓ -> f ρ -> p (f (ρ .- ℓ)) (h τ))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, FrontExtends ℓ τ ρ, AllUniqueLabels (Extend ℓ τ ρ))
               => Label ℓ -> p (g ρ) (h τ) -> g (Extend ℓ τ ρ))
               -- ^ The fold
            -> f r  -- ^ The input structure
            -> g r

instance ForallL (R '[]) c  where
  {-# INLINE metamorphL #-}
  metamorphL _ empty _ _ = empty

instance (KnownSymbol ℓ, c ℓ τ, ForallL ('R ρ) c, FrontExtends ℓ τ ('R ρ), AllUniqueLabels (Extend ℓ τ ('R ρ))) => ForallL ('R (ℓ :-> τ ': ρ) :: Row k) c where
  {-# INLINE metamorphL #-}
  metamorphL h empty uncons cons = case frontExtendsDict @ℓ @τ @('R ρ) of
    FrontExtendsDict Dict ->
      cons (Label @ℓ) . first (metamorphL @_ @('R ρ) @c h empty uncons cons) . uncons (Label @ℓ)

newtype RMap (f :: Type -> Type) (ρ :: Row Type) = RMap { unRMap :: Rec (R.Map f ρ) }
newtype RMap2 (f :: Type -> Type) (g :: Type -> Type) (ρ :: Row Type) = RMap2 { unRMap2 :: Rec (R.Map f (R.Map g ρ)) }

newtype RMapK  (f :: k -> Type) (ρ :: Row k) = RMapK { unRMapK :: Rec (R.Map f ρ) }
newtype RMap2K (f :: Type -> Type) (g :: k -> Type) (ρ :: Row k) = RMap2K { unRMap2K :: Rec (R.Map f (R.Map g ρ)) }

transformWithLabels :: forall k c r (f :: k -> Type) (g :: k -> Type)
                     . ForallL r c
                    => (forall l a. (KnownSymbol l) => Dict (c l a) -> f a -> g a) 
                    -> Rec (R.Map f r) 
                    -> Rec (R.Map g r)
transformWithLabels f = unRMapK . metamorphL @_ @r @c @(,) @(RMapK f) @(RMapK g) @f Proxy doNil doUncons doCons . RMapK
  where
    doNil _ = RMapK R.empty

    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, HasType ℓ τ ρ)
             => Label ℓ -> RMapK f ρ -> (RMapK f (ρ .- ℓ), f τ)
    doUncons l (RMapK r) = first RMapK $ lazyUncons l r
      \\ mapHas @f @ℓ @τ @ρ

    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ)
           => Label ℓ -> (RMapK g ρ, f τ) -> RMapK g (Extend ℓ τ ρ)
    doCons l (RMapK r, v) = RMapK (R.extend l (f (Dict :: Dict (c ℓ τ)) v) r)
      \\ mapExtendSwap @g @ℓ @τ @ρ

data Inst :: Row k -> (Symbol -> k -> Constraint) -> k -> Type where 
  Inst :: forall k (l :: Symbol) (rk :: Row k) (c :: Symbol -> k -> Constraint) (t :: k) 
          . ( KnownSymbol l 
            , HasType l t rk 
            ) => Sing l -> Dict (c l t) ->  Inst rk c t  


data MInstance :: Row k -> (Symbol -> k -> Constraint) -> k -> Type where 
  MINothing :: MInstance rk c k 
  MIJust    :: Inst rk c k -> MInstance rk c k 


instL :: forall l rx c
       . ( WellBehaved rx 
       , ForallL rx c
       , KnownSymbol l
       , HasType l (rx .! l) rx) 
      => Rec rx -> Inst rx c (rx .! l) 
instL rx = fromJust 
         . getConst 
         $ metamorphL @_ @rx @c @(,) @Rec @(Const (Maybe (Inst rx c (rx .! l)))) proxy doNil doUncons doCons rx 
  where 
    proxy :: Proxy (Proxy (Const (Maybe (Inst rx c (rx .! l)))), Proxy (,))
    proxy = Proxy 

    doNil :: Rec Empty -> Const (Maybe (Inst rx c (rx .! l))) Empty
    doNil _ = Const Nothing 

    doUncons :: forall l' t' p'
              . ( KnownSymbol l'  
                , HasType l' t' p' 
                , c l' t' 
              ) => Label l' -> Rec p' -> (Rec (p' .- l'), Const (Maybe (Inst rx c (rx .! l))) t') 
    doUncons l ry = case lazyUncons l ry of 
      (rz,e) -> case decideEquality (sing @l) (sing @l') of 
        -- this is safe. p' is a subset of rx and has unique labels. rx' .! l ~~ t. l' ~ l (in the Just branch)
        --  if p' is a subset of rx and has unique labels then 
        -- if l' ~ l, and (p' .! l' ~ t') then (rx .! l) must be inhabited and must contain a type t which is ~~ t'    
        -- (we could prove this to ghc with a stronger subset constraint, but i think we'd actually have to define that constraint in terms of this) 
        Just r@Refl -> case Inst (sing @l) (unsafeCoerce (Dict :: Dict (c l t')) :: Dict (c l (rx .! l))) :: Inst rx c (rx .! l) of 
            myInst -> (rz, Const . Just $ myInst)
        Nothing     -> (rz, Const Nothing)


    doCons :: forall l' t' p' x  
            . (KnownSymbol l', c l' t') 
          => Label l' 
          -> (Const (Maybe (Inst rx c (rx .! l))) p',
              Const (Maybe (Inst rx c (rx .! l))) t')
          -> Const (Maybe (Inst rx c (rx .! l))) x
    doCons _ (a,b) = case (getConst a, getConst b) of 
      (Nothing , Nothing) -> Const Nothing 
      (Just i  ,    _   ) -> Const (Just i)
      (_       ,  Just i) -> Const (Just i)


data HasSome' :: (k -> Constraint) -> Symbol -> Row k -> Type where 
  HasSome :: forall k (c :: k -> Constraint) (rk :: Row k) (l :: Symbol) 
          . ( WellBehaved rk 
            , KnownSymbol l 
            , HasType l (rk .! l) rk 
            , c (rk .! l)
            ) => HasSome' c l rk 

data Some :: (k -> Constraint) -> (k -> Type) -> Type where 
  Some :: forall k (c :: k -> Constraint) (f :: k -> Type) (a :: k)
        . c a => f a -> Some c f 

unSome :: Some c f -> (forall a. c a => f a -> r) -> r 
unSome (Some a) f = f a 

withSome :: forall k (c :: k -> Constraint) (l :: Symbol) (rk :: Row k) r. HasSome c l rk => (forall (x :: k). c x => r) -> r 
withSome f = case (hasSome :: HasSome' c l rk) of 
  HasSome -> f @(rk .! l)

withSome' :: forall k (c :: k -> Constraint) (l :: Symbol) (rk :: Row k) r. HasSome' c l rk -> (forall (x :: k). c x => r) -> r 
withSome' h f = case h of 
  HasSome -> f @(rk .! l)

class HasSome (c :: k -> Constraint) (l :: Symbol) (rk :: Row k)  where 
  hasSome :: HasSome' c l rk 

instance ( HasType l (rk .! l) rk
         , c (rk .! l) 
         , WellBehaved rk 
         , KnownSymbol l 
         ) => HasSome c l rk   where 
           hasSome = HasSome

getSome :: forall k (f :: k -> Type) l (c :: k -> Constraint)  (rk :: Row k) 
         . KnownSymbol l
        => HasSome' c l rk 
        -> (forall (a :: k). c a =>  f a) 
        -> Some c f 
getSome HasSome f = Some $ f @(rk .! l)
