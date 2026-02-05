{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.GenTactic where


import           Autosubst.GenM
import           Autosubst.Names
import           Autosubst.Syntax
import           Autosubst.Tactics
import           Autosubst.Types
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Lazy
import           Data.List                as L


-- Generation of as_apply tactic



genAsApply :: [TId] -> GenM [Sentence]
genAsApply xs = return $ [SentenceId "(** as_apply follows **)"]



























-- Generation of program data to see what's happening

termStr :: Term -> String

termStr (TermId s) = s

genCompp :: GenM [Sentence]

genCompp = do
  toVarT <- toVar "tmx" $ SubstSubst [TermId "sigma1", TermId "sigma2", TermId "sigma3"]
  return $ [SentenceId $ termStr toVarT]


genBottomJunk :: [TId] -> [TId] -> [TId] ->[(Binder,TId)] -> GenM [Sentence]
genBottomJunk varSorts xs substSorts upList = do
  csListList  <- mapM constructors xs
  gencmp    <- genCompp
  return $ [SentenceId "(** Some Junk below **)"] ++ (map SentenceId (map show (concat csListList))) ++ gencmp


genmString :: (Show a) =>  a -> GenM String
genmString x = return (show x)


