{-# LANGUAGE ConstraintKinds #-}
module Data.Rhizome.RQuery where
  
import Data.Kind 
import Data.Rhizome.Exists ()
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

class t ~ t' => Is t t' where 
  _is :: t :~: t' 
  _is = Refl 

type CanApply :: Symbol -> Row (Type -> Type) ->  Constraint 
class (KnownSymbol l, HasType l (rtt .! l) rtt, WellBehaved rtt) 
   => CanApply l rtt  where 
        runApply :: forall x. (rtt .! l) x -> Applied l rtt  x
        runApply fx = MkApplied sing fx 

instance ( KnownSymbol l
         , WellBehaved rtt
         , HasType l (rtt .! l) rtt) -- can't hurt  
    => CanApply l rtt 

data IsApp :: Row (Type -> Type) -> Symbol -> Type -> Type where 
  IsApp :: forall rtt l t x 
              . ( KnownSymbol l 
              , t ~ (rtt .! l) x
              ) => IsApp rtt l t 


data IsApNT :: Row (Type -> Type) -> (Type -> Type) ->  Symbol -> Type -> Type where 
  IsApNT :: forall rtt l t x g 
              . ( KnownSymbol l 
              , t ~ NT (rtt .! l) g 
              ) => IsApNT rtt g l t 


class (KnownSymbol l, CanApply l rtt) => IsApplied rtt l t  where 
  isApplied  :: IsApp rtt l t 

instance (KnownSymbol l, CanApply l rtt, f ~ (rtt .! l)) => IsApplied rtt l (f x) where 
  isApplied = IsApp 

type IsRowQuery :: Symbol -> Row (Type -> Type) -> Row Type -> (Type -> Type) -> (Type -> Type) -> Type -> Constraint 
class ( KnownSymbol l -- i swear that ghc won't infer this sometimes if it's not an explicit superclass
      , CanApply l rtt
      , WellBehaved rtt 
      , HasType l (NT (rtt .! l) g) rh
      ) => IsRowQuery l rtt rh f g x where 
            mkRQuery :: (rtt .! l) x ->  RQuery rtt x 
            mkRQuery fx = MkRQuery $ MkApplied (sing @l) fx 

instance ( KnownSymbol l 
         , CanApply l rtt
         , WellBehaved rtt 
         , HasType l (NT (rtt .! l) g) rh
         ) => IsRowQuery l rtt rh f g x 

data Applied :: Symbol -> Row (Type -> Type) ->   Type -> Type where 
  MkApplied :: forall l rtt g x 
             . ( KnownSymbol l, 
                 WellBehaved rtt,
                 HasType l (rtt .! l) rtt
             ) => Sing l -> (rtt .! l) x -> Applied l rtt x 

data RQuery :: Row (Type -> Type) -> Type -> Type where 
  MkRQuery :: Applied l rtt  x -> RQuery rtt x 

apMethod :: forall l x rtt rh g. HasType l (NT (rtt .! l) g) rh => Applied l rtt x -> Rec rh -> g x 
apMethod (MkApplied l fx) rh = case rh R..! (Label @l) :: (rh .! l) of 
    (NT fg) -> fg fx  

mkApplied :: forall l x rtt g 
          . ( KnownSymbol l
            , WellBehaved rtt 
            , HasType l (rtt .! l) rtt 
            ) => (rtt .! l) x -> Applied l rtt x    
mkApplied = MkApplied sing 

{-
runRQuery :: forall rh rtt f g x. Rec rh -> RQuery rtt x -> g x  
runRQuery rh (MkRQuery apd) = apMethod apd rh  
-}
type ApNT :: Row (Type -> Type) -> (Type -> Type) -> Symbol -> Type -> Constraint  
class ApNT rtt g l t where 
  isApNT :: IsApNT rtt g l t 

instance (KnownSymbol l, (rtt .! l) ~ f) => ApNT rtt g l (NT f g) where
  isApNT = IsApNT   

class ( ForallL rh (ApNT rq g)
      , WellBehaved rh ) => Interface rh rq g where 
          runInterface :: forall l x
                        . Rec rh -> Applied l rq x -> g x 
          runInterface rh (MkApplied sl fx) = go rh sl fx (withSingI sl $ mkInst)
            where 
              mkInst = instL @l @rh @(ApNT rq g) rh 

              go :: Rec rh -> Sing l -> (rq .! l) x -> Inst rh (ApNT rq g) (rh .! l) -> g x
              go rh sl fx (Inst sl' dx@Dict) = go' rh sl fx dx sl' 
                where 
                  go' :: forall l1. Rec rh
                      -> Sing l 
                      -> (rq .! l) x
                      -> Dict (ApNT rq g l1 (rh .! l))
                      -> Sing l1 
                      -> g x
                  go' rx s1 qx dy@Dict s2 = case unsafeCoerce Refl :: l :~: l1 of
                    r@Refl -> case impl r dy :: Dict (ApNT rq g l (rh .! l)) of 
                      dqe@Dict -> case isApNT :: IsApNT rq g l (rh .! l) of 
                        IsApNT -> apNT (rh R..! (Label @l)) qx 
                  {- Originally had a decideEquality test but unsafeCoerce is fine here. 
                     On line 110 we create an Inst which existentially hides a singleton of 'l', 
                     and all we're doing with unsafeCoerce is telling GHC that when we immediately unwrap it, 
                     we it has the same type. I'm pretty sure we have to do it this way. (I can maybe drop the singletons?)
                  -}

                  impl :: forall l1 l2 rq rh g t. l1 :~: l2 -> Dict (ApNT rq g l1 t) -> Dict (ApNT rq g l2 t)
                  impl Refl Dict = Dict 
              
mkInterface :: forall rq rh g. Interface rh rq g => Rec rh -> (RQuery rq :~> g)
mkInterface rh = NT $ go rh 
  where 
    go :: forall a. Rec rh -> RQuery rq a -> g a
    go rh' (MkRQuery applied) = runInterface rh' applied  


mkRowSpec :: forall rq rh deps roots surface state 
           . (Interface rh rq (RhizoM deps roots surface state (RQuery rq) IO)
           ,  WellBehaved roots) 
          => Rec (  "initialState" .== state 
                .+  "methods"      .== Rec rh 
                .+  "renderer"     .== Renderer state surface) 
          -> Spec state (Slot surface roots deps (RQuery rq))
mkRowSpec rowSpec = MkSpec {
    initialState = rowSpec R..! #initialState
  , handleQuery  = Handler $ mkInterface (rowSpec R..! #methods)
  , renderer     = rowSpec R..! #renderer} 


type Implements :: Symbol -> Row (Type -> Type) -> Constraint 
class ( KnownSymbol l
      , WellBehaved rq
      , HasType l (rq .! l) rq) => Implements l rq where 
  runMethod :: forall x su rs ds (st :: Type). Label l -> (rq .! l) x -> Entity (Slot su rs ds (RQuery rq)) -> IO x 
  runMethod l qx e = run (MkRQuery $ mkApplied @l @x @rq @(RhizoM ds rs su st (RQuery rq) IO ) qx) e  