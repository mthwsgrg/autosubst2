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
  redLaws <- genForEachSort xs genRedLawsSort 
  let matchBody = TacticMatch TacticSimpleMatch (MatchTerm $ JustString "gexp") redLaws
  return $ TacticFunction "heuristics" [BinderName "gexp", BinderName "hexp"] matchBody
  
    
-- Takes a list of sorts and applies tactic equation generation function on each sort

genForEachSort :: [TId] -> (TId -> GenM [TacticEquation]) -> GenM [TacticEquation]
genForeachSort xs tacEqnGenerator = do
  tacEqns <- mapM (\x -> tacEqnGenerator x) xs
  return $ concat tacEqns



genBindElimEqnsSort :: TId -> GenM [TacticEquation]
genBindElimEqnsSort x = do
  csList <- constructors x
  let binderPositions = concat $ map (\c -> case c of
                                              Constructor pms n pos -> filter (\p -> and [isPosArgAtom p, isPosBinder p]) pos) csList -- TODO: maybe a clean up function to remove repeated positions
  eqns <- mapM (\p -> genBindElimEqns p) binderPositions
  return eqns
  
genBindElimEqns :: Position -> GenM TacticEquation
genBindElimEqns (Position bs (Atom x)) = do
  srts <- substOf x
  let threeTerms srt = do
        let ss = genNames $ s++srt $ filter (\bndr -> [srt] == binderSorts bndr) bs
        consedSub <- conserWrtBinders bs (map (\s -> TermId (qmark_ s)) ss) (TermId $ "?sigma"++srt)
        liftedSub <- upSubstS srt bs [TermId $ "sigma"++srt]
        consedId <- conserWrtBinders bs (map (\s -> TermId s) ss) (var_ srt)
        return $ [consedSub, (hd liftedSub), consedId]
  
    














-- Don't start parameter name with s* because it's used in constructor arg names. (This issue exist in main code gen as well)
genRedLawsSort :: TId -> GenM [TacticEquation]
genRedLawsSort x = do
   csList  <- constructors x
   let genPosTerm (Position bs arg, tm) subSorts renOrSubLift renOrSub = do         
         tm' <-  genVecArg arg bs subSorts renOrSubLift renOrSub
         return $ case tm' of
                    TermApp h ts -> (TermApp h $ ts++[tm]) 
                    t -> TermApp t [tm] -- This case is the TermAbs case for external constructors like nat, bool etc which don't have inst/ren operations
   let genRedLawsCons x (Constructor pms name pos) renOrSubLift renOrSub = do         
         subSorts <- substOf x
         let subNames = genNames "sigma" subSorts
         let posNames = genNames "s" pos
         let pnames = fst (unzip pms)
         let sigmas = zip subSorts (map TermId (map qmark_ subNames)) 
         let pts = zip pos (map TermId (map qmark_ posNames))
         tms <- mapM (\pt -> genPosTerm pt sigmas renOrSubLift renOrSub) pts -- tms will hold the instantiated positions in a list
         let qpnames = map (\x -> TermId (qmark_ x)) pnames
         return $ TacticEquationTerm  (TacticPattern $ JustTerm $ idApp name (qpnames++tms)) $
                  let paramTerms = map TermId pnames in
                  let posTerms = map TermId posNames in
                  TacticCall "unify" [JustTerm $ TermApp (TermId $ renOrSub x) $ (map TermId subNames) ++ [idApp name $ paramTerms++posTerms], JustString "hexp"] 
   tacEqnsSub <- mapM (\cs -> genRedLawsCons x cs asimpledLiftGenSub subst_) csList
   tacEqnsRen <- mapM (\cs -> genRedLawsCons x cs asimpledLiftGenRen ren_) csList
   return $ tacEqnsSub ++ tacEqnsRen
   

-- Generates (lifted) substitution/renaming term for an Argument bound under a list of Binder. 
genVecArg ::  Argument -> [Binder] -> [(TId, Term)] -> ([Binder] -> (TId, Term) -> GenM Term) -> (TId -> String) -> GenM Term
genVecArg (Atom y) bs subSorts renOrSubLift renOrSub = do
  b <- hasSubst y
  if b then do
    ySubSorts <- substOf y
    newSubSorts <- return $ foldr (\y' ys -> ys ++ (case (lookup y' subSorts) of
                                             Just t  -> [ (y',t) ]
                                             Nothing -> []
                                              )) [] ySubSorts
    subVectors <- mapM (\sub -> renOrSubLift bs sub) newSubSorts
    return $ idApp (renOrSub y) subVectors 
  else
    return $ (TermAbs [BinderName "x"] (TermId "x"))
    
genVecArg (FunApp fname _ args) bs subSorts renOrSubLift renOrSub = do
  argSubVectors <-  mapM (\arg -> genVecArg arg bs subSorts renOrSubLift renOrSub) args
  return $ map_ fname argSubVectors  

{-

Unlike generation of instantiation/renaming, we can't generate up_* function for lift because we match asimplified types in heuristics.
Hence We need to generate the unfolded and asimplified version of liftings.

-}

  
-- Function for asimplified lift for subsitutions.
asimpledLiftGenSub :: [Binder] -> (TId, Term) -> GenM Term
asimpledLiftGenSub bs (srt, sigma) = do
  compTerms <- compFormer srt bs -- if compTerms are empty, then srt or the sorts srts dependent on is not in bs list
  varsList <- varsFormer (filter (\bndr -> [srt] == binderSorts bndr) bs) False
  let conser (bndr, tm) tmDef =
        case bndr of
          Single _ -> TermApp cons_ [tm, tmDef]
          BinderList p _ -> TermApp (TermId "scons_p") [TermId (qmark_ p), tm, tmDef]
  return $ if null compTerms then sigma else foldl' (\tm bndrTm -> conser bndrTm tm ) (TermApp (TermConst Comp) $ [(TermApp (TermId (ren_ srt)) compTerms), sigma]) varsList -- ther reversing because scoping is in the reverse order of polyadic binders in the HOAS spec


asimpledLiftGenRen :: [Binder] -> (TId, Term) -> GenM Term
asimpledLiftGenRen bs (srt, sigma) = do
  let bindersOfSrt = filter (\bndr -> [srt] == binderSorts bndr) bs
  varsList <- varsFormer bindersOfSrt True
  let compTerm = foldr (\bndr tm -> case bndr of
                                      Single _ -> TermApp (TermConst Comp) [tm, TermConst Shift]
                                      BinderList p _ -> TermApp (TermConst Comp) [tm, TermApp (TermId "shift_p") [TermId $ qmark_ p]]) sigma bindersOfSrt
  let conser (bndr, tm) tmDef =
        case bndr of
          Single _ -> TermApp cons_ [tm, tmDef]
          BinderList p _ -> TermApp (TermId "scons_p") [TermId (qmark_ p), tm, tmDef]
  return $ foldl' (\tm bndrTm -> conser bndrTm tm ) compTerm varsList
      
    
  

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
     return $ map (\x'' -> foldr (\bndr tm -> shiftComposer x'' bndr tm) (TermConst Id) bs) subSorts            
  else
    return $ []


-- Generates 0,1,p or (var 0),(var 1), (var p) with respect a list of binder for sconsing/sconsping. noVar is a bool if set won't generate var constructor
varsFormer :: [Binder] -> Bool -> GenM [(Binder, Term)]
varsFormer bs noVar =
  let finFormer bndr bs =
        case bndr of
          Single _ -> foldl' (\tm bndr' -> case bndr' of
                                             Single _ -> TermApp (TermConst Shift) [tm]
                                             BinderList p _ -> TermApp (TermId "shift_p") [TermId (qmark_ p), tm])
                      (TermConst VarZero) bs
          BinderList p _ -> let zerop = (TermApp (TermId "zero_p") [TermId (qmark_ p)]) in
                            foldr (\bndr' tm -> case tm of
                                                  TermApp c [h, z] -> case bndr' of
                                                                        Single _ -> TermApp c [TermApp (TermConst Comp) [h, TermConst Shift], z]
                                                                        BinderList p _ -> TermApp c [TermApp (TermConst Comp) [h, TermApp (TermId "shift_p") [TermId (qmark_ p)]]  ,z]
                                                  _ -> case bndr' of
                                                            Single _ -> TermApp (TermConst Comp) [TermConst Shift, zerop]
                                                            BinderList p _ -> TermApp (TermConst Comp) [TermApp (TermId "shift_p") [TermId (qmark_ p)], zerop])                                                 
                            zerop bs in
            
  let varFormer bndr bs =      
        case bndr of
          Single x -> foldl' (\tm bndr' -> case tm of
                                             TermApp v ts -> case bndr' of
                                                              Single _ -> TermApp v [TermApp (TermConst Shift) ts]
                                                              BinderList p _ -> TermApp v [TermApp (TermId "shift_p") $ [TermId (qmark_ p)] ++ ts])
                      (idApp (var_ x) $ [TermConst VarZero]) bs                 
          BinderList p x  -> foldr (\bndr' tm -> case tm of
                                                   TermApp c [h, z] -> case bndr' of
                                                                         Single _ -> TermApp c [TermApp (TermConst Comp) [h, TermConst Shift], z]
                                                                         BinderList p _ -> TermApp c [TermApp (TermConst Comp) [h, TermApp (TermId "shift_p") [TermId (qmark_ p)]]  ,z])
                             (TermApp (TermConst Comp) [TermId (var_ x), TermApp (TermId "zero_p") [TermId (qmark_ p)]]) bs in                  
  let varsFormer' bs varOrFinFormer =
        case bs of
          [] -> []
          bndr: rest -> (bndr, varOrFinFormer bndr rest) : varsFormer' rest varOrFinFormer  in            
  return $ case noVar of
             True -> varsFormer' bs finFormer
             False -> varsFormer' bs varFormer -- Note that polyadic binders appear in the same order as HOAS spec



-- prefix a string with question mark
qmark_ :: String -> String
qmark_ s = "?" ++ s

genNames :: String -> [a] -> [String]
genNames s xs = map (\x -> s ++ show x) (L.findIndices (const True) xs)

isPosBinder :: Position -> Bool
isPosBinder (Position bs arg) = if bs == [] then False else True

isPosArgAtom :: Position -> Bool
isPosArgAtom (Position bs arg) = case arg of
                                Atom _ -> True
                                _ -> False

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


