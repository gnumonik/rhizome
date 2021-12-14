module Data.Rhizome.OOP.Class where

import Data.Rhizome.OOP.Method 
import Data.Rhizome.Types
import Data.Row.Records
import Data.Rhizome.Eval
import Data.Rhizome.OOP.Interface


type Impl su rs ds rq = Slot su rs ds (Method rq)

implementation :: forall rq rh deps roots surface state 
           . (HasInterface rh rq (RhizoM deps roots surface state (Method rq) IO)
           ,  WellBehaved roots) 
          => Rec (  "initialState" .== state 
                .+  "methods"      .== Rec rh 
                .+  "renderer"     .== Renderer state surface) 
          -> Spec state (Impl surface roots deps rq)
implementation rowSpec = MkSpec {
    initialState = rowSpec .! #initialState
  , handleQuery  = Handler $ mkInterface (rowSpec .! #methods)
  , renderer     = rowSpec .! #renderer} 

(.|) ::  Entity (Slot su cs ds q) -> q x -> IO x
e .| q = run q e
infixl 0 .| 