module Data.Rhizome.Dictionary where

import Data.Rhizome.Types 
import Data.Constraint ( Dict(..), mapDict, weaken1, withDict )
import Data.Row ( HasType, type (.!) )
import qualified Data.Row.Records as R
import Data.Row.Dictionaries ( mapHas )

deriveHas :: forall f label slots slot
                . SlotKey label slots slot
               -> Dict (HasType label (f slot) (R.Map f slots))
deriveHas SlotKey 
  = withDict
    (mapDict weaken1 $ mapDict (mapHas @f @label @slot @slots) (Dict @((slots .! label) ~ slot)))
    Dict

deriveHas' :: forall f label slots slot 
            . HasType label slot slots => Dict (HasType label (f slot) (R.Map f slots))
deriveHas'  = withDict
    (mapDict weaken1 $ mapDict (mapHas @f @label @slot @slots) (Dict @((slots .! label) ~ slot)))
    Dict

