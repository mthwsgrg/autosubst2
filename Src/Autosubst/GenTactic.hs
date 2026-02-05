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




genRedLawsCons :: TId -> Constructor -> GenM TacticEquation
genRedLawsCons x (Constructor pms name pos) = do
  subSorts <- substOfSorts x
  argSorts <- arguments x
  if checkBinder pos then do_something
  else
    let s = genPatternNames "?s" pos in
    let sigma = genNames "?sigma" subSorts in
    let subTerms = genSubTerms (zip s argSorts) (zip sigma subSorts) in    
    return $ TacticEquation $ (TacticPatternTerm $ JustTerm $ idApp s subTerms) $ TacticId "whatever"


-- a filter function to filter from subSorts



genNames :: String -> [a] -> [String]      

genRedLaws :: [TId] -> GenM [TacticEquation]



genRedLaws varSorts = do
   csList <- something_happens
   let cons_pattern (Constructor pms name pos) =
          (if (checkBinder pos) then do_something
         else
           let s = genPatternNames "?s" pos in
           let termsTIds = zip s and tids in
           let subsTIds = zip subnames and tids) in
     
   return $ idApp name           
           

     
   
   

-- A list of pair of substitutions/renamings with corresponding sorts

type SubRenVector = [(Term, TId)]


checkBinder :: Constructor -> Bool


-- Takes a sort id, sub/ren vector and returns a subset of it that only appears in the sub/ren vector of Id 
subRenVecSort :: TId -> SubRenVector -> SubRenVector


substOfSorts :: TId -> GenM [TId]
substOfSorts = return $ substOf TId




-- Generation of program data to see what's happening

{-
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
-}

