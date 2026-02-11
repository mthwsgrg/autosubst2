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


  
-- Generation of as_apply tactic Start


genAsApply :: [TId] -> GenM [Sentence]
genAsApply xs = do
  heuristics <- genHeuristics xs
  return $ [SentenceId "(** as_apply follows **)"] ++ [SentenceTacticGeneral $ heuristics]


-- I don't print implicit scopes along with the constructors (maybe add it later)
-- I don't at the moment use SubstTy objects (maybe add it later for maintaining consistentcy with the other parts)
-- Currently I use some existing functions to talk with signature, and also I define some myself. Some of the latter maybe redundant but I will remove it later.

genHeuristics :: [TId] -> GenM Tactic
genHeuristics xs = do
  redLaws <- genRedLaws xs 
  let matchBody = TacticMatch TacticSimpleMatch (MatchTerm $ JustString "gexp") redLaws
  return $ TacticFunction "heuristics" [BinderName "gexp"] matchBody
  
                                                                    
genRedLaws :: [TId] -> GenM [TacticEquation]

genRedLaws varSorts = do
  redLawsList <- mapM (\x -> genRedLawsSort x) varSorts
  return $ concat redLawsList


genRedLawsSort :: TId -> GenM [TacticEquation]
genRedLawsSort x = do
   csList  <- constructors x
   tacEqns <- mapM (\cs -> genRedLawsCons x cs) csList
   return tacEqns
   

-- Don't start parameter name with s* because it's used in constructor arg names. (This issue exist in main code gen as well)
genRedLawsCons :: TId -> Constructor -> GenM TacticEquation
genRedLawsCons x (Constructor pms name pos) = do
  subSorts <- substOf x
  let sigmas = zip $  (map TermId (genNames "?sigma" subSorts)) pos
  let pts = zip $ (map TermId (genNames "?s" pos)) subSorts
  tms <- mapM (\pt -> genPosSubTerm pt sigmas) pts
  let pnames = map (\x -> TermId (qmark_ x)) (fst pms)
  return $ TacticEquationTerm  (TacticPattern $ JustTerm $ idApp name (pnames++tms)) $ TacticId "whatever"
  
   

-- Take a Position, Term and Substitutions and returns the Term with substitution performed
genPosSubTerm :: (Position, Term) -> [(Term, TId)] -> GenM Term
genPosSubTerm (Position bs arg, tm) subSorts = return $ tmAppExt (genSubVecArg arg bs subSorts) tm

-- Extend the application list of a term with one more term
tmAppExt :: Term -> Term -> Term
  
-- Generates substitution term for an argument  
genSubVecArg :: Argument -> [Binder] -> [(Term, TId)] -> GenM Term
genSubVecArg (Atom y) bs subSorts = do
  b <- hasSubst y
  if b then do  
    newSubSorts <- remSubSorts y subSorts
    subVectors <- mapM (\sub -> asimpledLiftGenSub bs sub) newSubSorts
    return $ idApp (subst_ y) subVectors 
  else
    return $ (TermAbs [BinderName "x"] (TermId "x"))
    
    
genSubVecArg (FunApp fname _ args) bs subSorts = do
  argSubVectors <-  mapM (\arg -> genSubVecArg arg bs subSorts) args
  return $ idApp fname argSubVectors

-- removes substitution sorts which is not relevant to a sort
remSubSorts :: TId -> [(Term,TId)] -> GenM [(Term, TId)]

-- Takes a Term and Substitution vector and returns a Term instantiated with the substitution vector  
tmSubst :: Term -> [Term] -> GenM Term

  
{-

Unlike generation of instantiation/renaming, we can't generate up_* function for lift because we match asimplified types in heuristics.
Hence We need to generate the unfolded and asimplified version of liftings.

-}


  
-- Function for asimplified lift inst and renaming construction. For each position this function is called
asimpledLiftGenSub :: [Binder] -> (Term, TId) -> GenM Term



forCompGen :: [Binder] -> (Term, TId) -> GenM [Term]

forCompGenComponent :: [Binder] -> TId -> GenM Term



forCompGenComponent bs x = foldl (\y s -> shiftComposer x y s) (TermId (var_ x)) bs  


-- forms composition with shift
 shiftComposer :: TId -> Binder -> Term -> GenM Term

-- forms variables to sconsed/sconsped
varFormer :: [Binder] -> [(Binder, Term)]


-- get variadic binder length
getVBinderLength :: Binder -> String


-- get Binder from position
binderInPos :: Position -> [Binder]

-- prefix a string with question mark
qmark_ :: String -> String


-- generates variables of a sort in 
asimpledLiftGenRen :: [Binder] -> (Term, TId) -> GenM Term



{-



  
  if checkBinder (Constructor pms name pos)
  then return $ TacticEquationTerm (TacticPattern $ JustTerm $ TermId "later") $ TacticId "later"
  else do   
    subSorts <- substOf x

    
    argConst <- arguments x
    let s = genNames "?s" pos
    let sigma = genNames "?sigma" subSorts
    subTerms <- genSubTerms (zip (map TermId s) argSorts) (zip (map TermId sigma) subSorts)    
    return $ TacticEquationTerm  (TacticPattern $ JustTerm $ idApp name subTerms) $ TacticId "whatever"



-- Returns a substitution vector of appropriate lifting by taking a list of binder, a sort under these binders, a list of substitution vector along with their sorts applicable to the main sort
genSubVector :: [Binder] -> TId -> [Term, TId] -> Gen [Term]
genSubVector bs x subs = 
  

  
             

genSubTerms :: [(Term, TId)] -> [(Term, TId)] -> GenM [Term]
genSubTerms sTIds sigmaTIds = mapM (\x -> formArgs (fst x) (snd x) sigmaTIds) sTIds 
  
formArgs :: Term -> TId -> [(Term, TId)] -> GenM Term
formArgs s x sigmaTIds = do
  subSorts <- substOfSorts x
  let subVector = fst $ unzip $ concat $ map (\x -> filter (\y -> x == snd y) sigmaTIds) subSorts
  return $ idApp (subst_ x) $ subVector ++ [s] 

  
genNames :: String -> [a] -> [String]
genNames s xs = map (\x -> s ++ show x) (L.findIndices (const True) xs)


-- Checks if a constructor is a binder
checkBinder :: Constructor -> Bool
checkBinder (Constructor _ _ pos) =
  let binderInPosition (Position bs args) = bs in
  or $ map (\p -> not $ null $ binderInPosition p) pos

genSubObjArg :: Position -> [(Term, TId)] -> Term
genSubObjArg (Position bs arg) = 

-- Returns the sorts of the arguments of a constructor
genArgConst :: Constructor -> GenM [TId]
genArgConst (Constructor pms name pos) = 

-}



-- Generation of as_apply tactic End



-- Generation of program data to see what's happening

{- This genAsApply is a dummy 

genAsApply :: [TId] -> GenM [Sentence]
genAsApply xs =  return $ [SentenceId "(** as_apply follows **)"]
-}


{-
termStr :: Term -> String
termStr (TermId s) = s

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


