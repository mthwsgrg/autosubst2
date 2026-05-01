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


relSize :: Int
relSize = 9

premisesSize :: Int
premisesSize = 11

qvarSize :: Int
qvarSize = 16

funName :: String
funName = "heuristics"

minSigmaName :: String
minSigmaName = "sigma_min"

genAsApply :: [TId] -> GenM [Sentence]
genAsApply xs = do
  musigma <- genMuSigma xs
  heuristics <- genHeuristics xs
  matchConclGoal <- genMatchConclGoal relSize
  premToSubgoals  <- genPremToSubgoals
  qvarToEvar <- genQvarToEvar premisesSize
  asApplyLayout <- genAsApplyLayout qvarSize
  return $ [SentenceId "(** as_apply follows **)"] ++ [SentenceTacticGeneral musigma] ++ [SentenceTacticGeneral $ heuristics] ++ [SentenceTacticGeneral $ matchConclGoal]
           ++ [SentenceTacticGeneral premToSubgoals] ++ [SentenceTacticGeneral qvarToEvar] ++ [SentenceTacticGeneral asApplyLayout]   
           ++ [SentenceTacticGeneral $ TacticId "Tactic Notation \"as_apply\" open_constr(H) := as_apply' @H."]


genHeuristics :: [TId] -> GenM Tactic
genHeuristics xs = do
  xsRen <- filterM (\s -> hasRenamings s) xs --Filtering sorts that has renaming and substitutions 
  unifyCase <- genUnifyCase
  bindElimEqns <- genForEachSort xs genBindElimEqnsSort
  renamifyCases <- genForEachSort xsRen genRenamify
  substifyCases <- genForEachSort xsRen genSubstify
  mucase <- genMuSigmaCase
  congrClos <- genForEachSort xs genCongrClosureSort
  idCases <- genIdLaws xs
  let matchBody = TacticMatch TacticSimpleMatch (MatchTerm $ JustString "gexp") (renamifyCases ++ substifyCases ++ [mucase] ++ bindElimEqns ++ idCases ++ congrClos)
  return $ TacticFunction funName [BinderName "gexp", BinderName "hexp"] (TacticMatchExp matchBody)
  
    
-- Takes a list of sorts and applies tactic equation generation function on each sort

genMuSigma :: [TId] -> GenM Tactic
genMuSigma xs = do
  unifyCase <- genUnifyCase
  redLaws <- genForEachSort xs genRedCasesSort
  compLaws <- genForEachSort xs genCompCasesSort
  assocLaws <- genForEachSort xs genAssocCasesSort
  mapEnvLaws <- genForEachSort xs genMapEnvCasesSort
  congrClos <- genForEachSort xs (\x -> genCongrClosureSortGeneral x minSigmaName)
  let matchBody = TacticMatch TacticSimpleMatch (MatchTerm $ JustString "gexp") (congrClos ++ [unifyCase] ++ redLaws ++ compLaws ++ assocLaws ++ mapEnvLaws)
  return $ TacticFunction minSigmaName [BinderName "gexp", BinderName "hexp"] (TacticMatchExp matchBody)





genBindElimEqnsSort :: TId -> GenM [TacticEquation]
genBindElimEqnsSort x = do
  csList <- constructors x
  let binderPositions' = concat $ map (\c -> case c of
                                              Constructor pms n pos -> filter (\p -> and [isPosArgAtom p, isPosBinder p]) pos) csList -- TODO: maybe a clean up function to remove repeated position
  binderPositions <- filterM (\(Position bs (Atom s)) -> allDepSortsHasRenAndSub s) binderPositions'
  eqnsSub <- mapM (\p -> genBindElimEqnsSub p) binderPositions
  eqnsRen <- mapM (\p -> genBindElimEqnsRen p) binderPositions  
  return $ eqnsRen ++ eqnsSub -- Note ren should be before sub


-- TODO: Maybe try to generalise genBindElimEqnsRen/Sub into one later, but not now

genBindElimEqnsRen :: Position -> GenM TacticEquation
genBindElimEqnsRen (Position bs (Atom x)) = do
  srts <- substOf x
  let threeSubsFormer srt = do
        let filteredBs = filter (\bndr -> [srt] == binderSorts bndr) bs
        let ss = genNames ("s"++srt) $ filteredBs
        let ts = genNames ("t"++srt) $ filteredBs
        gexprSub  <- conserWrtBinders filteredBs (map (\s -> TermId (qmark_ s)) ss) (TermApp (TermConst Comp) $ [TermId $ var_ srt ,TermId $ "?sigma"++srt]) qmark_
        consedId  <- conserWrtBinders filteredBs (map (\s -> TermId s) ss) (TermId $ var_ srt) id
        hexprSub  <- conserWrtBinders filteredBs (map (\t -> TermId (qmark_ t)) ts) (TermId $ var_ srt) (\s -> (qmark_ s) ++ "_")
        return $ (gexprSub, consedId, hexprSub)
  threeSubs <- mapM (\srt -> threeSubsFormer srt) srts
  let unzippedThree = unzip3 threeSubs 
  let gexprSubs  = case unzippedThree of (a,b,c) -> a 
  let consedIds  = case unzippedThree of (a,b,c) -> b
  let hexprSubs  = case unzippedThree of (a,b,c) -> c
  liftedSubs <-  mapM (\srtTm -> asimpledLiftGenRen bs srtTm id) $ zip srts (map (\srt -> TermId $ "sigma"++srt) srts)
  let gexpr = TermApp (TermId $ subst_ x) $ gexprSubs ++ [TermId $ "?s"++x]
  let hexpr = TermApp (TermId $ subst_ x) $ hexprSubs ++ [TermId $ "?t"++x]
  let gexprToUnify = TermApp (TermId $ subst_ x) $  consedIds ++ [TermApp (TermId $ ren_ x) $ liftedSubs ++ [TermId $ "s"++x]]
  tacEqn <- unifyTacEqnFormer gexpr hexpr gexprToUnify
  return tacEqn



genBindElimEqnsSub :: Position -> GenM TacticEquation
genBindElimEqnsSub (Position bs (Atom x)) = do
  srts <- substOf x
  let threeSubsFormer srt = do
        let filteredBs = filter (\bndr -> [srt] == binderSorts bndr) bs
        let ss = genNames ("s"++srt) $ filteredBs
        let ts = genNames ("t"++srt) $ filteredBs
        gexprSub  <- conserWrtBinders filteredBs (map (\s -> TermId (qmark_ s)) ss) (TermId $ "?sigma"++srt) qmark_
        consedId  <- conserWrtBinders filteredBs (map (\s -> TermId s) ss) (TermId $ var_ srt) id
        hexprSub  <- conserWrtBinders filteredBs (map (\t -> TermId (qmark_ t)) ts) (TermId $ var_ srt) (\s -> (qmark_ s) ++ "_")
        return $ (gexprSub, consedId, hexprSub)
  threeSubs <- mapM (\srt -> threeSubsFormer srt) srts
  let unzippedThree = unzip3 threeSubs 
  let gexprSubs  = case unzippedThree of (a,b,c) -> a 
  let consedIds  = case unzippedThree of (a,b,c) -> b
  let hexprSubs  = case unzippedThree of (a,b,c) -> c
  liftedSubs <- mapM (\srtTm -> asimpledLiftGenSub bs srtTm id) $ zip srts (map (\srt -> TermId $ "sigma"++srt) srts)
  let gexpr = TermApp (TermId $ subst_ x) $ gexprSubs ++ [TermId $ "?s"++x]
  let hexpr = TermApp (TermId $ subst_ x) $ hexprSubs ++ [TermId $ "?t"++x]
  let gexprToUnify = TermApp (TermId $ subst_ x) $ consedIds ++ [TermApp (TermId $ subst_ x) $ liftedSubs ++ [TermId $ "s"++x]] 
  tacEqn <- unifyTacEqnFormer gexpr hexpr gexprToUnify
  return tacEqn





genRenamify :: TId -> GenM [TacticEquation]
genRenamify x = do
  srts <- substOf x
  let leftSubs = genNames "sigma" srts
  let rightSubs = genNames "tau" srts
  let gexprSubs = map (\(srt,sigma) -> renAsSub srt (qmark_ sigma)) $ zip srts leftSubs
  let hexprSubs = map (\tau -> TermId $ qmark_ tau) rightSubs
  let compEqn =  let gexpr = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) gexprSubs, TermId $ "?sigma"] in
                 let hexpr = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x)  hexprSubs, TermId $ "?tau"] in
                 let unifExpr = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) (map (\sigma -> TermId $ sigma ) leftSubs), TermId $ "sigma"] in
                 let tacAction = let act1 = let eqnLeft = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x)  (map (\(srt,sigma) -> renAsSub srt sigma) $ zip srts leftSubs), TermId $ "sigma"] in
                                            TacticAssert (JustTerm eqnLeft, JustTerm unifExpr)  (JustString $ "eq") $ TacticSeq [TacticId "renamify", TacticId "reflexivity"] in
                                 let act2 = TacticCall "rewrite" [JustString "eq"] in
                                 let act4 = TacticCall funName [JustTerm unifExpr, JustString "hexp"] in
                                 let act3 = TacticId "clear eq" in
                                 TacticLet (JustString "eq", JustString "fresh \"eq\"") $ TacticSeq [act1, act2, act3, act4] in
                 tacNestedMatchClause gexpr hexpr tacAction
  let substEqn = let gexpr = TermApp (TermId $ subst_ x) $ gexprSubs ++ [TermId $ "?s"] in
                 let hexpr = TermApp (TermId $ ren_ x) $ hexprSubs ++ [TermId $ "?t"] in
                 let unifExpr = TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId $ sigma ) leftSubs) ++ [TermId "s"] in
                 let tacAction = let act1 = let eqnLeft = TermApp (TermId $ subst_ x) $ (map (\(srt,sigma) -> renAsSub srt sigma) $ zip srts leftSubs)  ++ [TermId "s"]  in
                                            TacticAssert (JustTerm eqnLeft, JustTerm unifExpr)  (JustString $ "eq") $ TacticSeq [TacticId "renamify", TacticId "reflexivity"] in
                                 let act2 = TacticCall "rewrite" [JustString "eq"] in
                                 let act4 = TacticCall funName [JustTerm unifExpr, JustString "hexp"] in
                                 let act3 = TacticId "clear eq" in
                                 TacticLet (JustString "eq", JustString "fresh \"eq\"") $ TacticSeq [act1, act2, act3, act4] in
                 tacNestedMatchClause gexpr hexpr tacAction
  tacEqn1 <- compEqn
  tacEqn2 <- substEqn
  return $ [tacEqn1, tacEqn2]

genSubstify :: TId -> GenM [TacticEquation]
genSubstify x = do
  srts <- substOf x
  let leftSubs = genNames "sigma" srts
  let rightSubs = genNames "tau" srts
  let gexprSubs = map (\sigma -> TermId $ qmark_ sigma) leftSubs
  let hexprSubs = map (\tau -> TermId $ qmark_ tau) rightSubs
  let compEqn =  let gexpr = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) gexprSubs, TermId $ "?sigma"] in
                 let hexpr = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x)  hexprSubs, TermId $ "?tau"] in
                 let unifExpr = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) (map (\(srt,sigma) -> renAsSub srt sigma ) $ zip srts leftSubs), TermId $ "sigma"] in
                 let tacAction = let act1 = let eqnLeft = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x)  (map (\sigma -> TermId $ sigma) leftSubs), TermId $ "sigma"] in
                                            TacticAssert (JustTerm eqnLeft, JustTerm unifExpr)  (JustString $ "eq") $ TacticSeq [TacticId "substify", TacticId "reflexivity"] in
                                 let act2 = TacticCall "rewrite" [JustString "eq"] in
                                 let act4 = TacticCall funName [JustTerm unifExpr, JustString "hexp"] in
                                 let act3 = TacticId "clear eq" in
                                 TacticLet (JustString "eq", JustString "fresh \"eq\"") $ TacticSeq [act1, act2, act3,act4] in
                 tacNestedMatchClause gexpr hexpr tacAction
  let substEqn = let gexpr = TermApp (TermId $ ren_ x) $ gexprSubs ++ [TermId $ "?s"] in
                 let hexpr = TermApp (TermId $ subst_ x) $ hexprSubs ++ [TermId $ "?t"] in
                 let unifExpr = TermApp (TermId $ subst_ x) $ (map (\(srt,sigma) -> renAsSub srt sigma ) $ zip srts leftSubs) ++ [TermId "s"] in
                 let tacAction = let act1 = let eqnLeft = TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId $ sigma) leftSubs)  ++ [TermId "s"] in
                                            TacticAssert (JustTerm eqnLeft, JustTerm unifExpr)  (JustString $ "eq") $ TacticSeq [TacticId "substify", TacticId "reflexivity"] in
                                 let act2 = TacticCall "rewrite" [JustString "eq"] in
                                 let act4 = TacticCall funName [JustTerm unifExpr, JustString "hexp"] in
                                 let act3 = TacticId "clear eq" in
                                 TacticLet (JustString "eq", JustString "fresh \"eq\"") $ TacticSeq [act1, act2, act3, act4] in
                 tacNestedMatchClause gexpr hexpr tacAction
  tacEqn1 <- compEqn
  tacEqn2 <- substEqn
  return $ [tacEqn1, tacEqn2]




-- Don't start parameter name with s* because it's used in constructor arg names. (This issue exist in main code gen as well)
genRedCasesSort :: TId -> GenM [TacticEquation]
genRedCasesSort x = do
   csList  <- constructors x
   let genPosTerm (Position bs arg, tm) subSorts renOrSubLift renOrSub = do         
         tm' <-  genVecArg arg bs subSorts renOrSubLift renOrSub
         return $ case tm' of
                    TermApp h ts -> (TermApp h $ ts++[tm]) 
                    t -> TermApp t [tm] -- This case is the TermAbs case for external constructors like nat, bool etc which don't have inst/ren operations
   let genRedCasesCons x (Constructor pms name pos) renOrSubLift renOrSub = do         
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
                  let tacOne = TacticCall "unify" [JustTerm $ TermApp (TermId $ renOrSub x) $ (map TermId subNames) ++ [idApp name $ paramTerms++posTerms], JustString "hexp"] in
                  let tacTwo = TacticCall minSigmaName [JustTerm $ TermApp (TermId $ renOrSub x) $ (map TermId subNames) ++ [idApp name $ paramTerms++posTerms], JustString "hexp"] in 
                  TacticFirst [tacOne,tacTwo]
   let csListWithPos' = filter (\c -> case c of
                                      Constructor pms name pos -> not (pos == [])) csList
   csListWithPos <- filterM (\c -> consPosHasSrtSub x c) csListWithPos'                      
   tacEqnsSub <- mapM (\cs -> genRedCasesCons x cs asimpledLiftGenSub subst_) csListWithPos
   tacEqnsRen <- mapM (\cs -> genRedCasesCons x cs asimpledLiftGenRen ren_) csListWithPos
   return $ tacEqnsSub ++ tacEqnsRen
   

genMapEnvCasesSort :: TId -> GenM [TacticEquation]
genMapEnvCasesSort x = do
  mapSubEqn <- genMapSubCases x
  hasRen <- hasRenamings x
  if hasRen == True then do
    mapRenEqn <- genMapRenCases x  
    return [mapRenEqn, mapSubEqn]
  else
    return [mapSubEqn]
        
genMapRenCases :: TId -> GenM TacticEquation
genMapRenCases x = do
  srts <- substOf x
  let leftSubs =   genNames "sigma" srts
  let rightSubs =  genNames "tau" srts
  let gexprSubs =  map (\sigma -> TermId $ qmark_ sigma) leftSubs
  let hexprSubs = map (\tau -> TermId $ qmark_ tau) rightSubs 
  let gexpr = TermApp (TermConst Cons) [TermApp (TermId $ ren_ x) $ gexprSubs ++ [TermId "?s"],
                                        TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ gexprSubs, TermId "?thetag"]]
  let hexpr = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ hexprSubs, TermId "?thetah"]
  let gexprToUnify = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ (map (\x -> TermId x) leftSubs) ,TermApp (TermConst Cons) [TermId "s", TermId "thetag"]]
  tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
  return $ tacEqn


genMapSubCases :: TId -> GenM TacticEquation
genMapSubCases x = do
  srts <- substOf x
  let leftSubs =   genNames "sigma" srts
  let rightSubs =  genNames "tau" srts
  let gexprSubs =  map (\sigma -> TermId $ qmark_ sigma) leftSubs
  let hexprSubs = map (\tau -> TermId $ qmark_ tau) rightSubs 
  let gexpr = TermApp (TermConst Cons) [TermApp (TermId $ subst_ x) $ gexprSubs ++ [TermId "?s"],
                                        TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ gexprSubs, TermId "?thetag"]]
  let hexpr = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ hexprSubs, TermId "?thetah"]
  let gexprToUnify = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ (map (\x -> TermId x) leftSubs) ,TermApp (TermConst Cons) [TermId "s", TermId "thetag"]]
  tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
  return $ tacEqn



genCompCasesSort :: TId -> GenM [TacticEquation]
genCompCasesSort x = do
  subSubTacEqn <- genCompSubSubCases x 
  hasRen <- hasRenamings x
  if hasRen == True then do
    renRenTacEqn <- genCompRenRenCases x
    renSubTacEqn <- genCompRenSubCases x
    subRenTacEqn <- genCompSubRenCases x
    return [renRenTacEqn, renSubTacEqn, subRenTacEqn, subSubTacEqn]
  else
    return [subSubTacEqn]



genCompRenRenCases :: TId -> GenM TacticEquation
genCompRenRenCases x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs 
   let gexpr = let gexprSubs = map (\sigmaTau -> TermApp (TermConst Comp) [snd sigmaTau, fst sigmaTau]) $ zip (map (\sigma -> TermId sigma) leftSubsQ) (map (\tau -> TermId tau) rightSubsQ) in
               TermApp (TermId $ ren_ x) $ gexprSubs ++ [TermId "?s"]
   let gexprToUnify = TermApp (TermId $ ren_ x) $ (map (\tau -> TermId tau) rightSubs) ++ [TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId sigma) leftSubs) ++ [TermId "s"]]
   let hexpr = TermApp (TermId $ ren_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)) ++[TermId "?t"] 
   tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn


genCompRenSubCases :: TId -> GenM TacticEquation
genCompRenSubCases x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs 
   let gexpr = let gexprSubs = map (\sigmaTau -> TermApp (TermConst Comp) [snd sigmaTau, fst sigmaTau]) $ zip (map (\sigma -> TermId sigma) leftSubsQ) (map (\tau -> TermId tau) rightSubsQ) in
               TermApp (TermId $ subst_ x) $ gexprSubs ++ [TermId "?s"]
   let gexprToUnify = TermApp (TermId $ subst_ x) $ (map (\tau -> TermId tau) rightSubs) ++ [TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId sigma) leftSubs) ++ [TermId "s"]]
   let hexpr = TermApp (TermId $ subst_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)) ++[TermId "?t"] 
   tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn


genCompSubRenCases :: TId -> GenM TacticEquation
genCompSubRenCases x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs
   let compForSort (y,sigma) srtsNames = do
         srtsy <- substOf y
         return $  TermApp (TermConst Comp) [TermApp (TermId $ ren_ y) $ snd (unzip (filter (\srtName -> elem (fst srtName) srtsy) srtsNames)), sigma]
   gexprSubs <- mapM (\srtName -> compForSort srtName $ zip srts (map (\tau -> TermId tau) rightSubsQ)) $ zip srts (map (\sigma -> TermId sigma) leftSubsQ)
   let gexpr = TermApp (TermId $ subst_ x) $ gexprSubs ++ [TermId "?s"]
   let gexprToUnify = TermApp (TermId $ ren_ x) $ (map (\tau -> TermId tau) rightSubs) ++ [TermApp (TermId $ subst_ x) $ (map (\sigma -> TermId sigma) leftSubs) ++ [TermId "s"]]
   let hexpr = TermApp (TermId $ ren_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)) ++[TermId "?t"] 
   tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn


genCompSubSubCases :: TId -> GenM TacticEquation
genCompSubSubCases x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs
   let compForSort (y,sigma) srtsNames = do
         srtsy <- substOf y
         return $  TermApp (TermConst Comp) [TermApp (TermId $ subst_ y) $ snd (unzip (filter (\srtName -> elem (fst srtName) srtsy) srtsNames)), sigma]
   gexprSubs <- mapM (\srtName -> compForSort srtName $ zip srts (map (\tau -> TermId tau) rightSubsQ)) $ zip srts (map (\sigma -> TermId sigma) leftSubsQ) 
   let gexpr = TermApp (TermId $ subst_ x) $ gexprSubs ++ [TermId "?s"]
   let gexprToUnify = TermApp (TermId $ subst_ x) $ (map (\tau -> TermId tau) rightSubs) ++ [TermApp (TermId $ subst_ x) $ (map (\sigma -> TermId sigma) leftSubs) ++ [TermId "s"]]
   let hexpr = TermApp (TermId $ subst_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)) ++[TermId "?t"] 
   tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn




genAssocCasesSort :: TId -> GenM [TacticEquation]
genAssocCasesSort x = do
  subSubTacEqn <- genAssocSubSubCases x
  hasRen <- hasRenamings x
  if hasRen == True then do 
   renRenTacEqn <- genAssocRenRenCases x
   renSubTacEqn <- genAssocRenSubCases x
   subRenTacEqn <- genAssocSubRenCases x
   return [renRenTacEqn, renSubTacEqn, subRenTacEqn, subSubTacEqn]
  else
   return [subSubTacEqn]
   
  



genAssocRenRenCases :: TId -> GenM TacticEquation
genAssocRenRenCases x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs 
   let gexpr = let gexprSubs = map (\sigmaTau -> TermApp (TermConst Comp) [snd sigmaTau, fst sigmaTau]) $ zip (map (\sigma -> TermId sigma) leftSubsQ) (map (\tau -> TermId tau) rightSubsQ) in
               TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ gexprSubs, TermId "?sigmas"]
   let gexprToUnify = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ (map (\tau -> TermId tau) rightSubs),
                                                TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId sigma) leftSubs), TermId "sigmas"]]
   let hexpr = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)), TermId "?sigmat"] 
   tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn




genAssocRenSubCases :: TId -> GenM TacticEquation
genAssocRenSubCases x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs 
   let gexpr = let gexprSubs = map (\sigmaTau -> TermApp (TermConst Comp) [snd sigmaTau, fst sigmaTau]) $ zip (map (\sigma -> TermId sigma) leftSubsQ) (map (\tau -> TermId tau) rightSubsQ) in
               TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ gexprSubs, TermId "?sigmas"]
   let gexprToUnify = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ (map (\tau -> TermId tau) rightSubs),
                                                TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId sigma) leftSubs), TermId "sigmas"]]
   let hexpr = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)), TermId "?sigmat"] 
   tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn


genAssocSubRenCases :: TId -> GenM TacticEquation
genAssocSubRenCases x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs
   let compForSort (y,sigma) srtsNames = do
         srtsy <- substOf y
         return $  TermApp (TermConst Comp) [TermApp (TermId $ ren_ y) $ snd (unzip (filter (\srtName -> elem (fst srtName) srtsy) srtsNames)), sigma]
   gexprSubs <- mapM (\srtName -> compForSort srtName $ zip srts (map (\tau -> TermId tau) rightSubsQ)) $ zip srts (map (\sigma -> TermId sigma) leftSubsQ)
   let gexpr = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ gexprSubs, TermId "?sigmas"]
   let gexprToUnify = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ (map (\tau -> TermId tau) rightSubs),
                                                TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ (map (\sigma -> TermId sigma) leftSubs), TermId "sigmas"]]
   let hexpr = TermApp (TermConst Comp) [TermApp (TermId $ ren_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)), TermId "?sigmat"] 
   tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn


genAssocSubSubCases :: TId -> GenM TacticEquation
genAssocSubSubCases x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs
   let compForSort (y,sigma) srtsNames = do
         srtsy <- substOf y
         return $  TermApp (TermConst Comp) [TermApp (TermId $ subst_ y) $ snd (unzip (filter (\srtName -> elem (fst srtName) srtsy) srtsNames)), sigma]
   gexprSubs <- mapM (\srtName -> compForSort srtName $ zip srts (map (\tau -> TermId tau) rightSubsQ)) $ zip srts (map (\sigma -> TermId sigma) leftSubsQ)
   let gexpr = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ gexprSubs, TermId "?sigmas"]
   let gexprToUnify = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ (map (\tau -> TermId tau) rightSubs),
                                                TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ (map (\sigma -> TermId sigma) leftSubs), TermId "sigmas"]]
   let hexpr = TermApp (TermConst Comp) [TermApp (TermId $ subst_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)), TermId "?sigmat"] 
   tacEqn <- firstTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn



genCongrClosureSort :: TId -> GenM [TacticEquation]
genCongrClosureSort x = genCongrClosureSortGeneral x funName



genIdLaws :: [TId] -> GenM [TacticEquation]
genIdLaws xs = do
  idCases <- genForEachSort xs genIdLawsSort
  let idMatchExp = TacticMatch TacticSimpleMatch (MatchTerm $ JustString "hexp") idCases
  return $ [TacticEquationTerm (TacticPattern (JustTerm $ TermId $ "?s")) $ TacticMatchExp idMatchExp]
  

genIdLawsSort :: TId -> GenM [TacticEquation]
genIdLawsSort x = do
  srts <- substOf x
  hasRen <- hasRenamings x
  let rightSubs = genNames "sigma" srts
  let hexprSub = TermApp (TermId $ subst_ x) $ (map (\sigma -> TermId $ qmark_ sigma) rightSubs) ++ [TermId "?t"]
  let tacActionSub = let unifyTerm = TermApp (TermId $ subst_ x) $ (map (\srt -> TermId $ var_ srt) srts) ++ [TermId "s"] in
                     TacticCall "unify" [JustTerm  unifyTerm, JustString "hexp"]
  let tacEqnSub = TacticEquationTerm (TacticPattern (JustTerm $ hexprSub)) $ tacActionSub
  if hasRen == True then
    let hexprRen = TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId $ qmark_ sigma) rightSubs) ++ [TermId "?t"] in
    let tacActionRen = let unifyTerm = TermApp (TermId $ ren_ x) $ (map (\srt -> TermConst Id) srts) ++ [TermId "s"] in
                     TacticCall "unify" [JustTerm  unifyTerm, JustString "hexp"] in
    let tacEqnRen = TacticEquationTerm (TacticPattern (JustTerm $ hexprRen)) $ tacActionRen in
    return $ [tacEqnSub, tacEqnRen]
  else
    return $ [tacEqnSub]



-- more general functions


genForEachSort :: [TId] -> (TId -> GenM [TacticEquation]) -> GenM [TacticEquation]
genForEachSort xs tacEqnGenerator = do
  tacEqns <- mapM (\x -> tacEqnGenerator x) xs
  return $ concat tacEqns



genUnifyCase :: GenM TacticEquation
genUnifyCase = do
  let tacAction = TacticCall "unify" [JustString "gexp", JustString "hexp"]
  return $ TacticEquationTerm (TacticPattern (JustTerm $ TermId "?s")) $ tacAction

genMuSigmaCase :: GenM TacticEquation
genMuSigmaCase = do
  let tacAction = TacticCall minSigmaName [JustString "gexp", JustString "hexp"]
  return $ TacticEquationTerm (TacticPattern (JustTerm $ TermId "?s")) $ tacAction




genCongrClosureSortGeneral :: TId -> String -> GenM [TacticEquation]
genCongrClosureSortGeneral x funName = do
  csList <- constructors x
  let genSubRenCompCases x = do
        srts <- substOf x
        let leftSubs = genNames "sigma" srts
        let rightSubs = genNames "tau" srts
        let gexprSub = TermApp (TermId $ subst_ x) $ (map (\sigma -> TermId $ qmark_ sigma) leftSubs) ++ [TermId $ "?s"]
        let hexprSub = TermApp (TermId $ subst_ x) $ (map (\tau -> TermId $ qmark_ tau) rightSubs) ++ [TermId $ "?t"]
        let gexprRen = TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId $ qmark_ sigma) leftSubs) ++ [TermId $ "?s"]
        let hexprRen = TermApp (TermId $ ren_ x) $ (map (\tau -> TermId $ qmark_ tau) rightSubs) ++ [TermId $ "?t"]
        let gexprCompSub = TermApp (TermConst Comp) $ [TermApp (TermId $ subst_ x) $ map (\sigma -> TermId $ qmark_ sigma) leftSubs,  TermId "?sigma"]
        let hexprCompSub = TermApp (TermConst Comp) $ [TermApp (TermId $ subst_ x) $ map (\tau -> TermId $ qmark_ tau) rightSubs, TermId "?tau"] 
        let gexprCompRen = TermApp (TermConst Comp) $ [TermApp (TermId $ ren_ x) $ map (\sigma -> TermId $ qmark_ sigma) leftSubs, TermId "?sigma"]
        let hexprCompRen = TermApp (TermConst Comp) $ [TermApp (TermId $ ren_ x) $ map (\tau -> TermId $ qmark_ tau) rightSubs, TermId "?tau"]
        let funCallSubs = let gexprSubs = map (\sigma -> TermId sigma) leftSubs in
                              let hexprSubs = map (\tau -> TermId tau) rightSubs in
                              map (\(g,h) -> TacticCall funName [JustTerm g, JustTerm h]) $ zip gexprSubs hexprSubs  
        tacEqnSub <- tacNestedMatchClause gexprSub hexprSub $ TacticSeq $ [TacticCall funName [JustTerm $ TermId $ "s", JustTerm $ TermId $ "t"]] ++ funCallSubs
        tacEqnCompSub <-tacNestedMatchClause gexprCompSub hexprCompSub $ TacticSeq $ [TacticCall funName [JustTerm $ TermId $ "sigma", JustTerm $ TermId $ "tau"]] ++ funCallSubs
        hasRen <- hasRenamings x
        if hasRen == True then do        
          tacEqnRen <- tacNestedMatchClause gexprRen hexprRen $ TacticSeq $ [TacticCall funName [JustTerm $ TermId $ "s", JustTerm $ TermId $ "t"]] ++ funCallSubs
          tacEqnCompRen <-tacNestedMatchClause gexprCompRen hexprCompRen $ TacticSeq $ [TacticCall funName [JustTerm $ TermId $ "sigma", JustTerm $ TermId $ "tau"]] ++ funCallSubs
          return $ [tacEqnSub, tacEqnRen, tacEqnCompSub, tacEqnCompRen]
        else
          return [tacEqnSub, tacEqnCompSub]
  let genConsCase (Constructor pms name pos) = do
        let posLeft = genNames "s" pos
        let posRight = genNames "t" pos
        let gexpr = TermApp (TermId name) $ (map (\p -> TermId $ qmark_ p) $ fst (unzip pms) ) ++ (map (\s -> TermId $ qmark_ s) posLeft)
        let hexpr = TermApp (TermId name) $ (map (\p -> TermId $ (\p' -> (qmark_ p') ++ "_" ) p) $ fst (unzip pms) ) ++ (map (\s -> TermId $ qmark_ s) posRight)
        let tacAction = let gexprTerms = (map (\p -> TermId p) $ fst (unzip pms))  ++ (map (\s -> TermId s) posLeft) in
                        let hexprTerms = (map (\p -> TermId $ (\p' -> p' ++ "_" ) p) $ fst (unzip pms)) ++ (map (\s -> TermId s) posRight) in
                        TacticSeq $ map (\fstSnd -> TacticCall funName [JustTerm $ fst fstSnd, JustTerm $ snd fstSnd]) $ zip gexprTerms hexprTerms
        tacEqn <- tacNestedMatchClause gexpr hexpr tacAction
        return $ tacEqn
  let csListWithPos = filter (\c -> case c of
                                      Constructor pms name pos -> not (pos == [])) csList
  tacEqns1 <- mapM (\c -> genConsCase c) csListWithPos
  tacEqns2 <- genSubRenCompCases x
  return $ tacEqns1 ++ tacEqns2



-- Generates (lifted) substitution/renaming term for an Argument bound under a list of Binder. 
genVecArg ::  Argument -> [Binder] -> [(TId, Term)] -> ([Binder] -> (TId, Term) -> (String -> String) -> GenM Term) -> (TId -> String) -> GenM Term
genVecArg (Atom y) bs subSorts renOrSubLift renOrSub = do
  b <- hasSubst y
  if b then do
    ySubSorts <- substOf y
    newSubSorts <- return $ foldr (\y' ys -> ys ++ (case (lookup y' subSorts) of
                                             Just t  -> [ (y',t) ]
                                             Nothing -> []
                                              )) [] ySubSorts
    subVectors <- mapM (\sub -> renOrSubLift bs sub qmark_) newSubSorts
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
-- TODO : Change conser to conserWrtBinders
asimpledLiftGenSub :: [Binder] -> (TId, Term) -> (String -> String) -> GenM Term
asimpledLiftGenSub bs (srt, sigma) qmodifier = do
  compTerms <- compFormer srt bs qmodifier -- if compTerms are empty, then srt or the sorts srts dependent on is not in bs list
  varsList <- varsFormer (filter (\bndr -> [srt] == binderSorts bndr) bs) False qmodifier
  let conser (bndr, tm) tmDef =
        case bndr of
          Single _ -> TermApp cons_ [tm, tmDef]
          BinderList p _ -> TermApp (TermId "scons_p") [TermId (qmodifier p), tm, tmDef]
  return $ if null compTerms then sigma else foldl' (\tm bndrTm -> conser bndrTm tm ) (TermApp (TermConst Comp) $ [(TermApp (TermId (ren_ srt)) compTerms), sigma]) varsList -- ther reversing because scoping is in the reverse order of polyadic binders in the HOAS spec


asimpledLiftGenRen :: [Binder] -> (TId, Term) -> (String -> String) -> GenM Term
asimpledLiftGenRen bs (srt, sigma) qmodifier = do
  let bindersOfSrt = filter (\bndr -> [srt] == binderSorts bndr) bs
  varsList <- varsFormer bindersOfSrt True qmodifier
  let compTerm = case bindersOfSrt of
                   [] -> sigma
                   Single _ : rest -> let composed = foldl' (\tm bndr -> case bndr of
                                                                             Single _ -> TermApp (TermConst Comp) [tm, TermConst Shift]
                                                                             BinderList p' _ -> TermApp (TermConst Comp) [tm, TermApp (TermId "shift_p") [TermId $ qmodifier p']]) (TermConst Shift) rest
                                         in TermApp (TermConst Comp) [composed, sigma]
                   BinderList p _ : rest ->  let shiftPdef = TermApp (TermId "shift_p") [TermId $ qmodifier p] in
                                             let composed = foldl' (\tm bndr ->  case bndr of
                                                                                    Single _ -> TermApp (TermConst Shift) [tm, TermConst Shift]
                                                                                    BinderList p' _ -> TermApp (TermConst Comp) [tm, TermApp (TermId "shift_p") [TermId $ qmodifier p']]) shiftPdef rest
                                             in TermApp (TermConst Comp) [composed, sigma]
  let conser (bndr, tm) tmDef =
        case bndr of
          Single _ -> TermApp cons_ [tm, tmDef]
          BinderList p _ -> TermApp (TermId "scons_p") [TermId (qmodifier p), tm, tmDef]
  return $ foldl' (\tm bndrTm -> conser bndrTm tm ) compTerm varsList
      
    
  

-- Perform appropriate shifting in a sort's substitution vector component with respect to a list of binders
compFormer :: TId -> [Binder] -> (String -> String) -> GenM [Term]
compFormer x bs qmodifier = do
  subSorts <- substOf x
  if not (null (intersect (foldr (\bndr xs -> (binderSorts bndr) ++ xs) [] bs) subSorts))  then
     let shiftFromBinder bndr =
           case bndr of
             Single _ -> TermConst Shift
             BinderList p _ -> TermApp (TermId "shift_p") [TermId (qmodifier p)] in
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
varsFormer :: [Binder] -> Bool -> (String -> String) -> GenM [(Binder, Term)]
varsFormer bs noVar qmodifier =
  let finFormer bndr bs =
        case bndr of
          Single _ -> foldl' (\tm bndr' -> case bndr' of
                                             Single _ -> TermApp (TermConst Shift) [tm]
                                             BinderList p _ -> TermApp (TermId "shift_p") [TermId (qmodifier p), tm])
                      (TermConst VarZero) bs
          BinderList p _ -> let zerop = (TermApp (TermId "zero_p") [TermId (qmodifier p)]) in
                            foldr (\bndr' tm -> case tm of
                                                  TermApp c [h, z] -> case bndr' of
                                                                        Single _ -> TermApp c [TermApp (TermConst Comp) [h, TermConst Shift], z]
                                                                        BinderList p _ -> TermApp c [TermApp (TermConst Comp) [h, TermApp (TermId "shift_p") [TermId (qmodifier p)]]  ,z]
                                                  _ -> case bndr' of
                                                            Single _ -> TermApp (TermConst Comp) [TermConst Shift, zerop]
                                                            BinderList p _ -> TermApp (TermConst Comp) [TermApp (TermId "shift_p") [TermId (qmodifier p)], zerop])                                                 
                            zerop bs in
            
  let varFormer bndr bs =      
        case bndr of
          Single x -> foldl' (\tm bndr' -> case tm of
                                             TermApp v ts -> case bndr' of
                                                              Single _ -> TermApp v [TermApp (TermConst Shift) ts]
                                                              BinderList p _ -> TermApp v [TermApp (TermId "shift_p") $ [TermId (qmodifier p)] ++ ts])
                      (idApp (var_ x) $ [TermConst VarZero]) bs                 
          BinderList p x  -> foldr (\bndr' tm -> case tm of
                                                   TermApp c [h, z] -> case bndr' of
                                                                         Single _ -> TermApp c [TermApp (TermConst Comp) [h, TermConst Shift], z]
                                                                         BinderList p _ -> TermApp c [TermApp (TermConst Comp) [h, TermApp (TermId "shift_p") [TermId (qmodifier p)]]  ,z])
                             (TermApp (TermConst Comp) [TermId (var_ x), TermApp (TermId "zero_p") [TermId (qmodifier p)]]) bs in                  
  let varsFormer' bs varOrFinFormer =
        case bs of
          [] -> []
          bndr: rest -> (bndr, varOrFinFormer bndr rest) : varsFormer' rest varOrFinFormer  in            
  return $ case noVar of
             True -> varsFormer' bs finFormer
             False -> varsFormer' bs varFormer -- Note that polyadic binders appear in the same order as HOAS spec








-- Preprocessing steps start

genMatchConclGoal :: Int -> GenM Tactic
genMatchConclGoal n = 
  let tacCall = funName in 
  let eqnGen m = let gargs = genNames "garg" (replicate m 0) in
                 let hargs = genNames "harg" (replicate m 0) in
                 let gargsq = map (\arg -> qmark_ arg) gargs in
                 let hargsq = map (\arg -> qmark_ arg) hargs in
                 let gexpr = foldl' (\s ls -> s ++ " " ++ ls) "?Pr" gargsq in
                 let hexpr = foldl' (\s ls -> s ++ " " ++ ls) "Pr"  hargsq in
                 let tacAction = TacticSeq $ map (\(one,two) -> TacticCall tacCall [JustString one, JustString two]) (zip gargs hargs) in
                 let tacGoalPat = TacticGoalPattern [] $ TacticPattern $ JustString gexpr in
                 let tacMatchKey = TacticSimpleMatch in
                 let tacMatchItem = MatchTerm $ JustString "ty_hyp" in
                 let tacPatRight = TacticPattern $ JustString $ hexpr in
                 let tacMatchEqnRight = TacticEquationTerm tacPatRight  tacAction in
                 TacticEquationGoal tacGoalPat $ TacticMatchExp $  TacticMatch tacMatchKey tacMatchItem [tacMatchEqnRight] in
  let clausesGen n' = if  n' == 1 then [eqnGen 1] else (eqnGen n' : (clausesGen  (n'-1) )) in
  let tacMatchExp = TacticMatchExp $ TacticMatch TacticSimpleMatch MatchGoal (clausesGen n) in
  let argName = "H"  in
  return $ TacticFunction "match_concl_goal"  [BinderName argName] $ TacticLet (JustString "ty_hyp", JustString $ "type of "++ argName) tacMatchExp  
        
   
  
genPremToSubgoals :: GenM Tactic
genPremToSubgoals = return $ TacticId "Ltac premises_to_subgoals H n := \n \   
 \  match (eval compute in n) with \n \
 \  | 0 => match_concl_goal H; asimpl in H; exact H \n \
 \  | _ => let ty_hyp := type of H in \n \
 \       match ty_hyp with \n \
 \       | ?ant -> ?concl => let z := fresh \"z\" in \n \
 \                          evar (z: ant); specialize (H ?z); premises_to_subgoals H (n-1); clear z \n \
 \      end \n \                         
 \  end."

genQvarToEvar :: Int -> GenM Tactic
genQvarToEvar n =
  let zeroToN = map (\s -> "premises_to_subgoals" ++ " H' " ++ s ) (genNames "" (replicate n 0)) in
  let call_prem = tail $ foldl' (\s ls -> s ++ "| " ++ ls) "" zeroToN in  
  return $ TacticId  ("Ltac qvar_to_evar H n := \n \
  \ match (eval compute in n) with \n \
  \ | 0 => let H' := fresh \"H\" in \n \
  \      pose proof H as H'; \n \
  \      first [" ++ call_prem ++ "]; \n \
  \       clear H' \n \
  \ | _ => let ty_hyp := type of H in \n \
  \      match ty_hyp with \n \
  \      | forall (x: ?T), ?rest => let y := fresh \"y\" in \n \
  \                          evar (y: T); specialize (H ?y); qvar_to_evar H (n-1); clear y \n \                                         
  \      end \n \
  \ end.")


genAsApplyLayout :: Int -> GenM Tactic    
genAsApplyLayout n =
  let zeroToN = map (\s -> "qvar_to_evar" ++ " H " ++ s ) (genNames "" (replicate n 0)) in
  let qvar_to_evar = tail $ foldl' (\s ls -> s ++ "| " ++ ls) "" zeroToN in 
  return $ TacticId ("Ltac as_apply' H' := unshelve( \n \
  \ intros; asimpl; \n \
  \ let H := fresh \"H\" in \n \
  \ pose proof H' as H; \n \
  \ asimpl in H; \n \
  \ first [" ++ qvar_to_evar ++ "]).") 

-- Preprocessing steps end




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

renAsSub :: TId -> String -> Term
renAsSub x xi = TermApp (TermConst Comp) [TermId $ var_ x,TermId xi]

-- note this uses foldl'
conserWrtBinders :: [Binder] -> Terms -> Term -> (String -> String) -> GenM Term
conserWrtBinders bs tms defSub pModifier =
  let conser (bndr, tm) def =
        case bndr of
          Single _ -> TermApp cons_ [tm, def]
          BinderList p _ -> TermApp (TermId "scons_p") [TermId (pModifier p), tm, def] in
  return $ foldl' (\tm bndrTm -> conser bndrTm tm ) defSub (zip bs tms)


unifyTacEqnFormer :: Term -> Term -> Term -> GenM TacticEquation
unifyTacEqnFormer gexpr hexpr toUnifyExpr =
  let tacAction =  TacticCall "unify" [JustTerm toUnifyExpr, JustString "hexp"] in
  tacNestedMatchClause gexpr hexpr tacAction
  

firstTacEqnFormer :: Term -> Term -> Term -> GenM TacticEquation
firstTacEqnFormer gexpr hexpr toUnifyExpr =
  let tacOne =  TacticCall "unify" [JustTerm toUnifyExpr, JustString "hexp"] in
  let tacTwo =  TacticCall minSigmaName [JustTerm toUnifyExpr, JustString "hexp"] in  
  tacNestedMatchClause gexpr hexpr (TacticFirst [tacOne,tacTwo])

sortHasRenAndSub :: TId -> GenM Bool
sortHasRenAndSub s = do
  varSorts <- getVarSorts
  ifRenaming <- hasRenamings s
  return $ (elem s varSorts) && ifRenaming

sortHasNoRenAndSub :: TId -> GenM Bool
sortHasNoRenAndSub s = do
  varSorts <- getVarSorts
  ifRenaming <- hasRenamings s
  return $ (not (elem s varSorts)) && (not ifRenaming)

sortHasOnlySub :: TId -> GenM Bool
sortHasOnlySub s = do
  varSorts <- getVarSorts
  ifRenaming <- hasRenamings s
  return $ (elem s varSorts) && (not ifRenaming)

allDepSortsHasRenAndSub :: TId -> GenM Bool
allDepSortsHasRenAndSub x = do
  srts <- substOf x
  hasRenSrt <- foldM (\b s -> do
                         h <- hasRenamings s
                         return $ b && h) True srts
  return hasRenSrt
 

consPosHasSrtSub :: TId -> Constructor -> GenM Bool
consPosHasSrtSub srt (Constructor _ _ pos) = do
  srts <- substOf srt
  let srtCombiner prev s = do
        substSrts <- substOf s
        return $ union substSrts prev
  posSubstSorts <- foldM (\prev s -> srtCombiner prev s) []  $ foldr (\(Position _ arg) prev -> union (argSorts arg) prev) [] pos  
  return $ [] ==  (srts \\ posSubstSorts)  

-- This has to be generalized for hexp, match key and to goal pattern 
tacNestedMatchClause :: Term -> Term -> Tactic -> GenM TacticEquation
tacNestedMatchClause gexpr hexpr tacAction =
  let tacPattern = TacticPattern $ JustTerm gexpr in
  let tacMatchExp = TacticMatchExp $ TacticMatch TacticSimpleMatch (MatchTerm $ JustString "hexp") $ [TacticEquationTerm (TacticPattern $ JustTerm hexpr) $ tacAction] in  
  return $ TacticEquationTerm  tacPattern tacMatchExp



