{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | This module contains Haskell variables representing globally visible names.
--   Rather than have strings floating around the system, all constant names
--   should be defined here, and the (exported) variables should be used and
--   manipulated elsewhere.

module Language.Fixpoint.Names (
  
  -- * Hardwired global names 
    dummyName
  , preludeName
  , boolConName
  , funConName
  , listConName
  , tupConName
  , propConName
  , strConName
  , vvName
  , symSepName
  , dropModuleNames 
  , takeModuleNames
) where

import FastString

import Data.List                (intercalate)
import Language.Fixpoint.Misc   (errorstar, safeLast, stripParens)

----------------------------------------------------------------------------
--------------- Global Name Definitions ------------------------------------
----------------------------------------------------------------------------

preludeName  = fsLit "Prelude"
dummyName    = fsLit "_LIQUID_dummy"
boolConName  = fsLit "Bool"
funConName   = fsLit "->"
listConName  = fsLit "[]" -- "List"
tupConName   = fsLit "()" -- "Tuple"
propConName  = fsLit "Prop"
strConName   = fsLit "Str"
vvName       = fsLit "VV"
symSepName   = '#'

-- dropModuleNames []  = []
-- dropModuleNames s  
--   | s == tupConName = tupConName 
--   | otherwise       = safeLast msg $ words $ dotWhite `fmap` stripParens s
--   where 
--     msg             = "dropModuleNames: " ++ s 
--     dotWhite '.'    = ' '
--     dotWhite c      = c

dropModuleNames          = mungeModuleNames safeLast "dropModuleNames: "
takeModuleNames          = mungeModuleNames safeInit "takeModuleNames: "

safeInit _ xs@(_:_)      = intercalate "." $ init xs
safeInit msg _           = errorstar $ "safeInit with empty list " ++ msg

mungeModuleNames _ _  [] = ""
mungeModuleNames f msg s
  | s == unpackFS tupConName
  = unpackFS tupConName
  | otherwise
  = f (msg ++ s) $ words $ dotWhite `fmap` stripParens s
  where
    dotWhite '.' = ' '
    dotWhite c   = c
