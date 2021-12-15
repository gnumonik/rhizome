module Data.Rhizome.OOP.Class where

import Data.Rhizome.OOP.Method 
import Data.Rhizome.Types
import Data.Row.Records
import Data.Rhizome.Eval
import Data.Rhizome.OOP.Interface
import Control.Comonad.Store 
import Data.Kind


-- sorta like a store comonad
data ImplX:: Interface -> Row Type -> Row Type -> Type where 
  MkImplX:: forall rq rh st  
                    . ImplBuilder st rh 
                  -> (forall ds rs su
                           . ( HasInterface rh rq (RhizoM ds rs su (Rec st) (Method rq) IO) 
                             , WellBehaved rs)
                          => ImplBuilder st rh 
                          -> Renderer (Rec st) su 
                          -> Spec (Rec st) (Impl su rs ds rq)) 
                  -> ImplX rq rh st 

mkImplementation :: forall rq rh st 
                  . ImplBuilder st rh  
                 -> ImplX rq rh st 
mkImplementation ir = MkImplX ir go 
  where 
    go :: forall ds rs su 
        . ( HasInterface rh rq (RhizoM ds rs su (Rec st) (Method rq) IO) 
          , WellBehaved rs)
      => Rec ("initialState" .== Rec st .+  "methods" .== Rec rh)
      -> Renderer (Rec st) su 
      -> Spec (Rec st) (Impl su rs ds rq)
    go irec r = MkSpec {
      initialState = irec .! #initialState 
    , handleQuery  = Handler $ mkInterface (irec .! #methods)
    , renderer     = r 
    } 

type ImplBuilder state handlers  
  =  Rec (  "initialState" .== Rec state 
        .+  "methods"      .== Rec handlers)

type Impl su rs ds rq = Slot su rs ds (Method rq)

implement :: forall rq rh deps roots surface state 
           . (HasInterface rh rq (RhizoM deps roots surface (Rec state) (Method rq) IO)
           ,  WellBehaved roots) 
          => Rec ("initialState" .== Rec state .+  "methods" .== Rec rh)
          -> Renderer (Rec state) surface   
          -> Spec (Rec state) (Impl surface roots deps rq)
implement irec rndr = case mkImplementation irec of 
  MkImplX rx f -> f rx rndr 

(.|) ::  Entity (Slot su cs ds q) -> q x -> IO x
e .| q = run q e
infixl 0 .| 