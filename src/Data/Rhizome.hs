{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}

{--

Module organization sucks but the types are too mutually dependent to 
avoid placing them all in one module. Oh well. 
--}

module Data.Rhizome (module Data.Rhizome.Types,
                     module Data.Rhizome.Eval, 
                     module Data.Rhizome.Prototype,
                     module Data.Rhizome.Activate) where

import Data.Rhizome.Types 
import Data.Rhizome.Eval 
import Data.Rhizome.Prototype 
import Data.Rhizome.Activate 