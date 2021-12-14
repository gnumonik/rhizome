module Data.Rhizome.OOP.Interface where

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
import Data.Rhizome.OOP.Method

type Protocol rq g  = Method rq :~> g 

data IsApNT :: Interface -> (Type -> Type) ->  Symbol -> Type -> Type where 
  IsApNT :: forall rtt l t x g 
              . ( KnownSymbol l 
              , t ~ NT (rtt .! l) g 
              ) => IsApNT rtt g l t 

type ApNT :: Interface -> (Type -> Type) -> Symbol -> Type -> Constraint  
class ApNT rtt g l t where 
  isApNT :: IsApNT rtt g l t 

instance (KnownSymbol l, (rtt .! l) ~ f) => ApNT rtt g l (NT f g) where
  isApNT = IsApNT   

class ( ForallL rh (ApNT rq g)
      , WellBehaved rh ) => HasInterface rh rq g where 
          runInterface :: forall l x
                        . Rec rh -> Applied l rq x -> g x 
          runInterface rh (MkApplied sl fx) = go rh sl fx mkInst
            where 
              mkInst :: Inst rh (ApNT rq g) (rh .! l)
              mkInst = withSingI sl $ instL @l @rh @(ApNT rq g) rh 

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
                     On line 112 we create an Inst which existentially hides a singleton of 'l', 
                     and all we're doing with unsafeCoerce is telling GHC that when we immediately unwrap it, 
                     it has the same type. I'm pretty sure we have to do it this way. 

                     We need this because GHC won't infer that l1 and l in (ApNT rq g l1 (rh .! l)) are equal 
                  -}

                  impl :: forall l1 l2 rq rh g t. l1 :~: l2 -> Dict (ApNT rq g l1 t) -> Dict (ApNT rq g l2 t)
                  impl Refl Dict = Dict 

mkInterface :: forall rq rh g. HasInterface rh rq g => Rec rh -> (Method rq :~> g)
mkInterface rh = NT $ go rh 
  where 
    go :: forall a. Rec rh -> Method rq a -> g a
    go rh' (MkMethod applied) = runInterface rh' applied  