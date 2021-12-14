{-# LANGUAGE ConstraintKinds #-}
module Data.Rhizome.OOP.Method where
  
import Data.Kind 
import Data.Rhizome.Exists (Top)
import Data.Rhizome.Types 
import Data.Row
    ( KnownSymbol, Row, Rec, type (.!), HasType, Label(Label) )
import Data.Singletons.TypeLits ( Symbol, Sing )
import Data.Singletons (KindOf, SingI (sing), Proxy (Proxy), withSingI)
import qualified Data.Row.Records as R
import Data.Row.Internal 
import Data.Bifunctor
import Data.Row.Records (lazyRemove)
import Data.Type.Equality
import Data.Rhizome.RowExtras
import Data.Constraint
import Data.Singletons.Decide
import Data.Rhizome.Prototype (apNT)
import Unsafe.Coerce
import Data.Rhizome.Eval
import Data.Row.Dictionaries (mapHas)

type Interface = Row (Type -> Type)

class t ~ t' => Is t t' where 
  _is :: t :~: t' 
  _is = Refl 

type CanApply :: Symbol -> Interface ->  Constraint 
class (KnownSymbol l, HasType l (rtt .! l) rtt, WellBehaved rtt) 
   => CanApply l rtt  where 
        runApply :: forall x. (rtt .! l) x -> Applied l rtt  x
        runApply fx = MkApplied sing fx 

instance ( KnownSymbol l
         , WellBehaved rtt
         , HasType l (rtt .! l) rtt) -- can't hurt  
    => CanApply l rtt 

data IsApp :: Interface -> Symbol -> Type -> Type where 
  IsApp :: forall rtt l t x 
              . ( KnownSymbol l 
              , t ~ (rtt .! l) x
              ) => IsApp rtt l t 

class (KnownSymbol l, CanApply l rtt) => IsApplied rtt l t  where 
  isApplied  :: IsApp rtt l t 

instance (KnownSymbol l, CanApply l rtt, f ~ (rtt .! l)) => IsApplied rtt l (f x) where 
  isApplied = IsApp 

data Applied :: Symbol -> Interface ->   Type -> Type where 
  MkApplied :: forall l rtt g x 
             . ( KnownSymbol l, 
                 WellBehaved rtt,
                 HasType l (rtt .! l) rtt
             ) => Sing l -> (rtt .! l) x -> Applied l rtt x 

data Method :: Interface -> Type -> Type where 
  MkMethod :: KnownSymbol l => Applied l rtt  x -> Method rtt x 

apMethod :: forall l x rtt rh g. HasType l (NT (rtt .! l) g) rh => Applied l rtt x -> Rec rh -> g x 
apMethod (MkApplied l fx) rh = case rh R..! (Label @l) :: (rh .! l) of 
    (NT fg) -> fg fx  

mkApplied :: forall l x rtt g
          . ( KnownSymbol l
            , WellBehaved rtt
            , HasType l (rtt .! l) rtt 
            ) => (rtt .! l) x -> Applied l rtt x
mkApplied = MkApplied sing 

type Subsumes :: Row k -> Row k -> Constraint 
class ( ForallL small (InstK small (ExistsIn big) Proxy)
      , ConjureProxy small
      , WellBehaved small 
      , WellBehaved big
      ) => Subsumes (big :: Row k) (small :: Row k) where 
  subsumes :: forall (l :: Symbol) a
            . (KnownSymbol l) => HasType l a small :- HasType l a big
  subsumes = unmapDict go
    where 
      exHas :: forall r l t. Dict (ExistsIn r l t) -> Dict (HasType l t r)
      exHas Dict = Dict  

      instances :: Rec (R.Map (InstFX small (ExistsIn big) Proxy) small )
      instances = instK @_ @small @(ExistsIn big) 

      go :: Dict (HasType l a small)
         -> Dict (HasType l a big)
      go d1@Dict = case instances R..! (Label @l) :: Map (InstFX small (ExistsIn big) Proxy) small .! l of 
        x -> case mapDict (mapHas @(InstFX small (ExistsIn big) Proxy) @l @a @small) Dict of
          di@Dict -> case x :: InstFX small (ExistsIn big) Proxy a of 
            insFX@(InstFX insF) -> conclude insF  
       where 
         conclude :: forall l1. InstF small (ExistsIn big) Proxy l1 a -> Dict (HasType l a big)
         conclude (InstF si Dict) = 
           -- This is safe in this context 
           case unsafeCoerce Refl :: l1 :~: l of 
            Refl -> Dict  

subsumeC :: forall s t c l   
          . ( KnownSymbol l  
            , Subsumes t s
            ) => c l (s .! l) :- c l (t .! l) 
subsumeC = unmapDict go where 
  go :: Dict (c l (s .! l)) -> Dict (c l (t .! l)) 
  go Dict = case mapDict (subsumes @_ @t @s @l @(s .! l)) Dict of 
    dx@Dict -> Dict 

type LTEQ :: Symbol -> k -> Symbol -> k -> Constraint 
class (l ~ l', t ~ t') => LTEQ l t l' t' where 
  lEQ :: l :~: l' 
  lEQ = Refl 

  tEQ :: t :~: t'  
  tEQ = Refl  
instance (l ~ l', t ~ t') => LTEQ l t l' t'



class (Subsumes t s, Subsumes s t) => Coextensive t s where 
  coextensive :: forall l
               . KnownSymbol l 
              => Dict ((s .! l) ~ (t .! l))


data ImplementationW :: Interface -> SlotData -> Type where 
  ImplementationW :: forall rq su cs ds slot 
             .  ( WellBehaved rq 
                , Top su 
                , Top cs 
                , Top ds
                , slot ~ Slot su cs ds (Method rq)
                ) => ImplementationW rq slot

type Implements :: Interface -> SlotData -> Constraint 
class Implements rq slot where 
  implementation :: ImplementationW rq slot 

instance ( WellBehaved rq
         , Top su
         , Top cs
         , Top ds
         ) => Implements rq (Slot su cs ds (Method rq)) where 
  implementation = ImplementationW

type MethodOf :: Interface -> Symbol -> Constraint 
class ( KnownSymbol l
      , WellBehaved rq) => MethodOf rq l where 
  mkMethod :: forall x (su :: Type) (rs :: Row SlotData) (ds :: Row SlotData) (st :: Type)
            . Label l 
           -> (rq .! l) x 
           -> Method rq x 
  mkMethod l qx  =  MkMethod $ mkApplied @l @x @rq @(RhizoM ds rs su st (Method rq) IO) qx

instance ( KnownSymbol l
         , WellBehaved rq
         , HasType l (rq .! l) rq) => MethodOf rq l

class (HasType l t r, KnownSymbol l) => ExistsIn r l t where 
  has :: Dict (HasType l t r)
  has = Dict

instance (HasType l t r, KnownSymbol l) => ExistsIn r l t 

as :: forall s t x. Subsumes s t => Method t x -> Method s x 
as (MkMethod apd) = go apd 
  where 
    go :: forall l. Applied l t x -> Method s x 
    go (MkApplied l qx) = case mapDict (subsumes @_ @s @t @l @(t .! l)) (Dict :: Dict (HasType l (t .! l) t)) of 
      dx@Dict -> withDict dx $ MkMethod (MkApplied l qx)

-- yo = x.|#add 1.|#add 2 


