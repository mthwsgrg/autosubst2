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
  let sigmas = zip subSorts (map TermId (genNames "?sigma" subSorts)) 
  let pts = zip pos (map TermId (genNames "?s" pos))
  tms <- mapM (\pt -> genPosSubTerm pt sigmas) pts -- tms will hold the instantiated positions in a list
  let pnames = map (\x -> TermId (qmark_ x)) (fst (unzip pms))
  return $ TacticEquationTerm  (TacticPattern $ JustTerm $ idApp name (pnames++tms)) $ TacticId "whatever"
  
   



-- Take a Position, Term and Substitutions and returns the Term with substitution performed
genPosSubTerm :: (Position, Term) -> [(TId, Term)] -> GenM Term
genPosSubTerm (Position bs arg, tm) subSorts = do
  tm' <-  genSubVecArg arg bs subSorts
  return $ case tm' of
              TermApp h ts -> (TermApp h $ ts++[tm]) 
              t -> TermApp t [tm] -- This case is the TermAbs case for external constructors like nat, bool etc which don't have inst/ren operations


-- Generates substitution term for an argument  
genSubVecArg :: Argument -> [Binder] -> [(TId, Term)] -> GenM Term

genSubVecArg (Atom y) bs subSorts = do
  b <- hasSubst y
  if b then do
    ySubSorts <- substOf y
    newSubSorts <- return $ foldr (\y' ys -> ys ++ (case (lookup y' subSorts) of
                                             Just t  -> [ (y',t) ]
                                             Nothing -> []
                                              )) [] ySubSorts
    subVectors <- mapM (\sub -> asimpledLiftGenSub bs sub) newSubSorts
    return $ idApp (subst_ y) subVectors 
  else
    return $ (TermAbs [BinderName "x"] (TermId "x"))
    
    
genSubVecArg (FunApp fname _ args) bs subSorts = do
  argSubVectors <-  mapM (\arg -> genSubVecArg arg bs subSorts) args
  return $ map_ fname argSubVectors

  
{-

Unlike generation of instantiation/renaming, we can't generate up_* function for lift because we match asimplified types in heuristics.
Hence We need to generate the unfolded and asimplified version of liftings.

-}


  
-- Function for asimplified lift inst and renaming construction. For each position this function is called
asimpledLiftGenSub :: [Binder] -> (TId, Term) -> GenM Term
asimpledLiftGenSub bs (srt, sigma) = do
  compTerms <- compFormer srt bs -- if compTerms are empty, then srt or the sorts srts dependent on is not in bs list
  varsList <- varsFormer srt bs
  let conser (bndr, tm) tmDef =
        case bndr of
          Single _ -> TermApp cons_ [tm, tmDef]
          BinderList p _ -> TermApp (TermId "scons_p") [TermId (qmark_ p), tm, tmDef]
  return $ if null compTerms then sigma else foldr (\bndrTm tm -> conser bndrTm tm ) (TermApp (TermConst Comp) $ [(TermApp (TermId (ren_ srt)) compTerms), sigma]) varsList



-- Perform appropriate shifting in a sort's substitution vector component with respect to a list of binders
compFormer :: TId -> [Binder] -> GenM [Term]
compFormer x bs = do
  subSorts <- substOf x
  if not (null (intersect (foldr (\bndr xs -> (binderSorts bndr) ++ xs) [] bs) subSorts))  then
     let shiftFromBinder bndr =
           case bndr of
             Single _ -> TermConst Shift
             BinderList p _ -> TermApp (TermId "shift_p") [TermId (qmark_ p)] in
     let shiftComposer x' bndr tm =
           if [x'] == binderSorts bndr then
             case tm of
               TermConst Id -> shiftFromBinder bndr
               _ -> TermApp (TermConst Comp) [tm, shiftFromBinder bndr]
           else tm in
     return $ map (\x'' -> foldr (\bndr tm -> shiftComposer x'' bndr tm) (TermConst Id) bs ) subSorts            
  else
    return $ []


-- Takes a sort and generate variables for sconsing/sconsping if the sort appear in a list of binders
varsFormer :: TId -> [Binder] -> GenM [(Binder, Term)]
varsFormer x bs =
  let varFormer bndr bs =      
        case bndr of
          Single x -> foldr (\bndr' tm -> case tm of
                                             TermApp v ts -> case bndr' of
                                                              Single _ -> TermApp v [TermApp (TermConst Shift) ts]
                                                              BinderList p _ -> TermApp v [TermApp (TermId "shift_p") $ [TermId (qmark_ p)] ++ ts])
                      (idApp (var_ x) $ [TermConst VarZero]) bs                 


          BinderList p x  -> foldr (\bndr' tm -> case tm of
                                                   TermApp c [h, z] -> case bndr' of
                                                                         Single _ -> TermApp c [TermApp (TermConst Comp) [h, TermConst Shift], z]
                                                                         BinderList p _ -> TermApp c [TermApp (TermConst Comp) [h, TermApp (TermId "shift_p") [TermId (qmark_ p)]]  ,z])
                            (TermApp (TermConst Comp) [TermId (var_ x), TermApp (TermId "zero_p") [TermId (qmark_ p)]]) bs in
                  
  let varsFormer' bs =
        case bs of
          [] -> []
          bndr: rest -> (bndr, varFormer bndr rest) : varsFormer' rest in            
  return $ varsFormer' $ filter (\bndr -> [x] == binderSorts bndr) bs


-- prefix a string with question mark
qmark_ :: String -> String
qmark_ s = ['?'] ++ s

genNames :: String -> [a] -> [String]
genNames s xs = map (\x -> s ++ show x) (L.findIndices (const True) xs)




{-
-- generates variables of a sort in 
asimpledLiftGenRen :: [Binder] -> (Term, TId) -> GenM Term
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


