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
-- TODO : Look for redundancy between renaming/substitution generation functions and merge whenever possible.

genHeuristics :: [TId] -> GenM Tactic
genHeuristics xs = do
  redLaws <- genForEachSort xs genRedLawsSort
  bindElimEqns <- genForEachSort xs genBindElimEqnsSort
  compLaws <- genForEachSort xs genCompLawsSort
  congrClos <- genForEachSort xs genCongrClosureSort
  renamifyCases <- genForEachSort xs genRenamify
  substifyCases <- genForEachSort xs genSubstify
  let matchBody = TacticMatch TacticSimpleMatch (MatchTerm $ JustString "gexp") (bindElimEqns ++ renamifyCases ++ substifyCases ++ redLaws ++ compLaws ++ congrClos)
  return $ TacticFunction "heuristics" [BinderName "gexp", BinderName "hexp"] matchBody
  
    
-- Takes a list of sorts and applies tactic equation generation function on each sort

genForEachSort :: [TId] -> (TId -> GenM [TacticEquation]) -> GenM [TacticEquation]
genForEachSort xs tacEqnGenerator = do
  tacEqns <- mapM (\x -> tacEqnGenerator x) xs
  return $ concat tacEqns



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
                                 let act3 = TacticCall "unify" [JustTerm unifExpr, JustString "hexp"] in
                                 let act4 = TacticId "clear eq" in
                                 TacticLet (JustString "eq", JustString "fresh \"eq\"") $ TacticSeq [act1, act2, act3, act4] in
                 tacNestedMatchClause gexpr hexpr tacAction
  let substEqn = let gexpr = TermApp (TermId $ subst_ x) $ gexprSubs ++ [TermId $ "?s"] in
                 let hexpr = TermApp (TermId $ ren_ x) $ hexprSubs ++ [TermId $ "?t"] in
                 let unifExpr = TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId $ sigma ) leftSubs) ++ [TermId "s"] in
                 let tacAction = let act1 = let eqnLeft = TermApp (TermId $ subst_ x) $ (map (\(srt,sigma) -> renAsSub srt sigma) $ zip srts leftSubs)  ++ [TermId "s"]  in
                                            TacticAssert (JustTerm eqnLeft, JustTerm unifExpr)  (JustString $ "eq") $ TacticSeq [TacticId "renamify", TacticId "reflexivity"] in
                                 let act2 = TacticCall "rewrite" [JustString "eq"] in
                                 let act3 = TacticCall "unify" [JustTerm unifExpr, JustString "hexp"] in
                                 let act4 = TacticId "clear eq" in
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
                                 let act3 = TacticCall "unify" [JustTerm unifExpr, JustString "hexp"] in
                                 let act4 = TacticId "clear eq" in
                                 TacticLet (JustString "eq", JustString "fresh \"eq\"") $ TacticSeq [act1, act2, act3,act4] in
                 tacNestedMatchClause gexpr hexpr tacAction
  let substEqn = let gexpr = TermApp (TermId $ ren_ x) $ gexprSubs ++ [TermId $ "?s"] in
                 let hexpr = TermApp (TermId $ subst_ x) $ hexprSubs ++ [TermId $ "?t"] in
                 let unifExpr = TermApp (TermId $ subst_ x) $ (map (\(srt,sigma) -> renAsSub srt sigma ) $ zip srts leftSubs) ++ [TermId "s"] in
                 let tacAction = let act1 = let eqnLeft = TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId $ sigma) leftSubs)  ++ [TermId "s"] in
                                            TacticAssert (JustTerm eqnLeft, JustTerm unifExpr)  (JustString $ "eq") $ TacticSeq [TacticId "renamify", TacticId "reflexivity"] in
                                 let act2 = TacticCall "rewrite" [JustString "eq"] in
                                 let act3 = TacticCall "unify" [JustTerm unifExpr, JustString "hexp"] in
                                 let act4 = TacticId "clear eq" in
                                 TacticLet (JustString "eq", JustString "fresh \"eq\"") $ TacticSeq [act1, act2, act3, act4] in
                 tacNestedMatchClause gexpr hexpr tacAction
  tacEqn1 <- compEqn
  tacEqn2 <- substEqn
  return $ [tacEqn1, tacEqn2]



genCongrClosureSortGeneral :: TId -> String -> GenM [TacticEquation]
genCongrClosureSortGeneral x funName = do
  csList <- constructors x
  let genSubRenCompCases x = do
        srts <- substOf x
        let leftSubs = genNames "sigma" srts
        let rightSubs = genNames "tau" srts
        let gexprSub = TermApp (TermId $ subst_ x) $ (map (\sigma -> TermId $ qmark_ sigma) leftSubs) ++ [TermId $ "?s"++x]
        let hexprSub = TermApp (TermId $ subst_ x) $ (map (\tau -> TermId $ qmark_ tau) rightSubs) ++ [TermId $ "?t"++x]
        let gexprRen = TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId $ qmark_ sigma) leftSubs) ++ [TermId $ "?s"++x]
        let hexprRen = TermApp (TermId $ ren_ x) $ (map (\tau -> TermId $ qmark_ tau) rightSubs) ++ [TermId $ "?t"++x]
        let gexprCompSub = TermApp (TermConst Comp) $ [TermApp (TermId $ subst_ x) $ map (\sigma -> TermId $ qmark_ sigma) leftSubs,  TermId "?sigma"]
        let hexprCompSub = TermApp (TermConst Comp) $ [TermApp (TermId $ subst_ x) $ map (\tau -> TermId $ qmark_ tau) rightSubs, TermId "?tau"] 
        let gexprCompRen = TermApp (TermConst Comp) $ [TermApp (TermId $ ren_ x) $ map (\sigma -> TermId $ qmark_ sigma) leftSubs, TermId "?sigma"]
        let hexprCompRen = TermApp (TermConst Comp) $ [TermApp (TermId $ ren_ x) $ map (\tau -> TermId $ qmark_ tau) rightSubs, TermId "?tau"]
        let funCallSubs = let gexprSubs = map (\sigma -> TermId sigma) leftSubs in
                              let hexprSubs = map (\tau -> TermId tau) rightSubs in
                              map (\(g,h) -> TacticCall funName [JustTerm g, JustTerm h]) $ zip gexprSubs hexprSubs  
        tacEqnSub <- tacNestedMatchClause gexprSub hexprSub $ TacticSeq $ [TacticCall funName [JustTerm $ TermId $ "s", JustTerm $ TermId $ "t"]] ++ funCallSubs
        tacEqnRen <- tacNestedMatchClause gexprRen hexprRen $ TacticSeq $ [TacticCall funName [JustTerm $ TermId $ "s", JustTerm $ TermId $ "t"]] ++ funCallSubs
        tacEqnCompSub <-tacNestedMatchClause gexprCompSub hexprCompSub $ TacticSeq $ [TacticCall funName [JustTerm $ TermId $ "sigma", JustTerm $ TermId $ "tau"]] ++ funCallSubs
        tacEqnCompRen <-tacNestedMatchClause gexprCompRen hexprCompRen $ TacticSeq $ [TacticCall funName [JustTerm $ TermId $ "sigma", JustTerm $ TermId $ "tau"]] ++ funCallSubs
        return $ [tacEqnSub, tacEqnRen, tacEqnCompSub, tacEqnCompRen]
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



genCongrClosureSort :: TId -> GenM [TacticEquation]
genCongrClosureSort x = genCongrClosureSortGeneral x "heuristics"


   
        

genCompLawsSort :: TId -> GenM [TacticEquation]
genCompLawsSort x = do
  renRenTacEqn <- genCompRenRenTacEqns x
  renSubTacEqn <- genCompRenSubTacEqns x
  subRenTacEqn <- genCompSubRenTacEqns x
  subSubTacEqn <- genCompSubSubTacEqns x 
  return [renRenTacEqn, renSubTacEqn, subRenTacEqn, subSubTacEqn]


genCompRenRenTacEqns :: TId -> GenM TacticEquation
genCompRenRenTacEqns x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs 
   let gexpr = let gexprSubs = map (\sigmaTau -> TermApp (TermConst Comp) [snd sigmaTau, fst sigmaTau]) $ zip (map (\sigma -> TermId sigma) leftSubsQ) (map (\tau -> TermId tau) rightSubsQ) in
               TermApp (TermId $ ren_ x) $ gexprSubs ++ [TermId "?s"]
   let gexprToUnify = TermApp (TermId $ ren_ x) $ (map (\tau -> TermId tau) rightSubs) ++ [TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId sigma) leftSubs) ++ [TermId "s"]]
   let hexpr = TermApp (TermId $ ren_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)) ++[TermId "?t"] 
   tacEqn <- unifyTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn


genCompRenSubTacEqns :: TId -> GenM TacticEquation
genCompRenSubTacEqns x = do
   srts <- substOf x
   let leftSubs =   genNames "sigma" srts
   let rightSubs =  genNames "tau" srts
   let leftSubsQ =  map (\sigma -> qmark_ sigma) leftSubs
   let rightSubsQ = map (\tau -> qmark_ tau) rightSubs 
   let gexpr = let gexprSubs = map (\sigmaTau -> TermApp (TermConst Comp) [snd sigmaTau, fst sigmaTau]) $ zip (map (\sigma -> TermId sigma) leftSubsQ) (map (\tau -> TermId tau) rightSubsQ) in
               TermApp (TermId $ subst_ x) $ gexprSubs ++ [TermId "?s"]
   let gexprToUnify = TermApp (TermId $ subst_ x) $ (map (\tau -> TermId tau) rightSubs) ++ [TermApp (TermId $ ren_ x) $ (map (\sigma -> TermId sigma) leftSubs) ++ [TermId "s"]]
   let hexpr = TermApp (TermId $ subst_ x) $ (map (\theta -> TermId theta) (genNames "?theta" srts)) ++[TermId "?t"] 
   tacEqn <- unifyTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn


genCompSubRenTacEqns :: TId -> GenM TacticEquation
genCompSubRenTacEqns x = do
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
   tacEqn <- unifyTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn


genCompSubSubTacEqns :: TId -> GenM TacticEquation
genCompSubSubTacEqns x = do
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
   tacEqn <- unifyTacEqnFormer gexpr hexpr gexprToUnify
   return $ tacEqn






genBindElimEqnsSort :: TId -> GenM [TacticEquation]
genBindElimEqnsSort x = do
  csList <- constructors x
  let binderPositions = concat $ map (\c -> case c of
                                              Constructor pms n pos -> filter (\p -> and [isPosArgAtom p, isPosBinder p]) pos) csList -- TODO: maybe a clean up function to remove repeated positions
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
   let csListWithPos = filter (\c -> case c of
                                      Constructor pms name pos -> not (pos == [])) csList
  
   tacEqnsSub <- mapM (\cs -> genRedLawsCons x cs asimpledLiftGenSub subst_) csListWithPos
   tacEqnsRen <- mapM (\cs -> genRedLawsCons x cs asimpledLiftGenRen ren_) csListWithPos
   return $ tacEqnsSub ++ tacEqnsRen
   

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




-- Some helper functions, and more general functions follows

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
  



tacNestedMatchClause :: Term -> Term -> Tactic -> GenM TacticEquation
tacNestedMatchClause gexpr hexpr tacAction =
  let tacPattern = TacticPattern $ JustTerm gexpr in
  let tacMatchExp = TacticMatchExp $ TacticMatch TacticSimpleMatch (MatchTerm $ JustString "hexp") $ [TacticEquationTerm (TacticPattern $ JustTerm hexpr) $ tacAction] in  
  return $ TacticEquationTerm  tacPattern tacMatchExp


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


