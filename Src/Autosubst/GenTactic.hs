{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.GenTactic where

import           Autosubst.Generator
import           Autosubst.ModularGenerator
import           Autosubst.Types
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS          hiding ((<>))

import           Autosubst.GenM
import qualified Data.Map                   as M
import           Data.Maybe                 as Maybe
import           Prelude                    hiding ((<$>))
import           Text.PrettyPrint.Leijen

import           Autosubst.GenAutomation
import           Autosubst.Signature
import           Autosubst.Syntax
import           Data.List                  as L

import           Autosubst.PrintScoped
import           Autosubst.PrintUnscoped


