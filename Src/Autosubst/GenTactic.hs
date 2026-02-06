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


-- I don't print implicit scopes along with the constructors (maybe add it later)

genRedLaws :: [TId] -> GenM [TacticEquation]

genRedLaws varSorts = do
  redLawsList <- mapM (\x -> genRedLawsSort x) varSorts
  return $ concat redLawsList


genRedLawsSort :: TId -> GenM [TacticEquation]
genRedLawsSort x = do
   csList  <- constructors x
   tacEqns <- mapM (\cs -> genRedLawsCons x cs) csList
   return tacEqns
   

genRedLawsCons :: TId -> Constructor -> GenM TacticEquation
genRedLawsCons x (Constructor pms name pos) =
  if checkBinder (Constructor pms name pos)
  then return $ TacticEquationTerm (TacticPattern $ JustTerm $ TermId "later") $ TacticId "later"
  else do   
    subSorts <- substOfSorts x
    argSorts <- arguments x
    let s = genNames "?s" pos
    let sigma = genNames "?sigma" subSorts
    subTerms <- genSubTerms (zip (map TermId s) argSorts) (zip (map TermId sigma) subSorts)    
    return $ TacticEquationTerm  (TacticPattern $ JustTerm $ idApp name subTerms) $ TacticId "whatever"

  {-
  if checkBinder (Constructor pms name pos) then
     return $ TacticEquation (TacticPatternTerm $ JustTerm $ TermId "later") $ TacticId "later"
  else
  -}


genSubTerms :: [(Term, TId)] -> [(Term, TId)] -> GenM [Term]
genSubTerms sTIds sigmaTIds = mapM (\x -> formArgs (fst x) (snd x) sigmaTIds) sTIds 
  
formArgs :: Term -> TId -> [(Term, TId)] -> GenM Term
formArgs s x sigmaTIds = do
  subSorts <- substOfSorts x
  let subVector = fst $ unzip $ concat $ map (\x -> filter (\y -> x == snd y) sigmaTIds) subSorts
  return $ idApp (subst_ x) $ subVector ++ [s] 

  
genNames :: String -> [a] -> [String]
genNames s xs = map (\x -> s ++ show x) (L.findIndices (const True) xs)


checkBinder :: Constructor -> Bool
checkBinder (Constructor _ _ pos) =
  let binderInPosition (Position bs args) = bs in
  or $ map (\p -> null $ binderInPosition p) pos


substOfSorts :: TId -> GenM [TId]
substOfSorts x = substOf x



-- Generation of program data to see what's happening


termStr :: Term -> String
termStr (TermId s) = s

{-
genCompp :: GenM [Sentence]
genCompp = do
  toVarT <- toVar "tmx" $ SubstSubst [TermId "sigma1", TermId "sigma2", TermId "sigma3"]
  return $ [SentenceId $ termStr toVarT]
-}

genBottomJunk :: [TId] -> [TId] -> [TId] ->[(Binder,TId)] -> GenM [Sentence]
genBottomJunk varSorts xs substSorts upList = do
  csListList  <- mapM constructors xs
  -- gencmp    <- genCompp
  return $ [SentenceId "(** Some Junk below **)"] ++ (map SentenceId (map show (concat csListList))) -- ++ gencmp


genmString :: (Show a) =>  a -> GenM String
genmString x = return (show x)


