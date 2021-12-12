{-# LANGUAGE ConstraintKinds #-}
module Data.Rhizome.RQuery where
  
import Data.Kind 
import Data.Rhizome.Exists ()
import Data.Rhizome.Types ( NT(..) )
import Data.Row
    ( KnownSymbol, Row, Rec, type (.!), HasType, Label(Label) )
import Data.Singletons.TypeLits ( Symbol, Sing )
import Data.Singletons (KindOf, SingI (sing), Proxy (Proxy))
import qualified Data.Row.Records as R
import Data.Row.Internal 
import Data.Bifunctor
import Data.Row.Records (lazyRemove)
import Data.Type.Equality
import Data.Rhizome.RowExtras

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
            mkRQuery :: (rtt .! l) x ->  RQuery rtt rh g x 
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

data RQuery :: Row (Type -> Type) -> Row Type -> (Type -> Type) -> Type -> Type where 
  MkRQuery :: HasType l (NT (rtt .! l) g) rh => Applied l rtt  x -> RQuery rtt rh g x 

apMethod :: forall l x rtt rh g. HasType l (NT (rtt .! l) g) rh => Applied l rtt x -> Rec rh -> g x 
apMethod (MkApplied l fx) rh = case rh R..! (Label @l) :: (rh .! l) of 
    (NT fg) -> fg fx  

mkApplied :: forall l x rtt g 
          . ( KnownSymbol l
            , WellBehaved rtt 
            , HasType l (rtt .! l) rtt 
            ) => (rtt .! l) x -> Applied l rtt x    
mkApplied = MkApplied sing 

runRQuery :: forall rh rtt f g x. Rec rh -> RQuery rtt rh g x -> g x  
runRQuery rh (MkRQuery apd) = apMethod apd rh  

class ForallL rh (IsApplied rtt) => Interface rh rtt where 
  runMethod :: Rec rh -> RQuery rtt rh g x -> g x 





