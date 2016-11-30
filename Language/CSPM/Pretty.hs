{- |
   Module      :  Language.CSP.Pretty
   Description :  Pretty printing for the CSP abstract syntax
   Copyright   :  Draper Laboratories
   
   The two functions in the module are used for pretty-printing the abstract CSP
   syntax.  The output is intended to be readable by FDR3.
-}

module Language.CSPM.Pretty (emitMod, emitMods) where

import Language.CSPM.Syntax
import Text.PrettyPrint
import Data.List
import Control.Monad
import qualified Data.Map as M
import qualified Data.Set as S

-- We need to keep track of which identifiers are in scope, so that we can use
-- simple names where possible.  We use a state monad (note: not a reader
-- monad, since there are globals, though we do provide reader like
-- functionality).  The state consists of three parts: 
--
-- - A map of identifiers to Doc, which says how to print anything currently
--   in scope.
--
-- - A Set, which just contains the range of the map.  When we see a new
--   identifier, we need to check that the way we want to print it doesn't
--   conflict with things already in scope.  Keeping a around is much more
--   efficient than getting the range of the map as a list and searching that.
--
-- - A list of "warnings".  If we encounter an identifier that's not in scope,
--   we have to guess about how to print it.  This may not be safe, so we note
--   the problem in the warnings.
--
-- Additionally, because CSP declarations may be mutually recursive, we do a
-- first pass to add all the global variables to the monad.  This first pass
-- also shows up where a block of local definitions may be mutually recursive,
-- as in let-within clauses.

data PPState = PPState {ppIdMap    :: !(M.Map Id String),
                        ppUsedDocs :: !(S.Set String),
                        ppWarnings :: ![String]}

emptyPPState :: PPState
emptyPPState = PPState {ppIdMap    = M.empty,
                        ppUsedDocs = S.empty,
                        ppWarnings = []}

newtype PP a = PP (PPState -> (PPState,a))

unPP :: PP a -> PPState -> (PPState,a)
unPP (PP f) = f

instance Functor PP where
  fmap f (PP g) = PP (\st -> fmap f (g st))

instance Monad PP where
  return x  = PP $ \pps -> (pps,x)
  m >>= k   = PP $ \pps -> let (pps',res) = unPP m pps in unPP (k res) pps'

instance Applicative PP where
  pure = return
  (<*>) = ap


runPP :: PPState -> PP a -> (a,[String])
runPP st (PP f) = let (st',res) = f st in (res, ppWarnings st')

getIdMap :: PP (M.Map Id String)
getIdMap = PP $ \pps -> (pps,ppIdMap pps)

warn :: String -> PP ()
warn warning = PP $ \pps -> (pps {ppWarnings = warning : ppWarnings pps},())

addGlobal :: Id -> PP Doc
addGlobal var = PP $ \pps -> 
  let ppvar = if S.member niceVersion (ppUsedDocs pps)
                then uglyVersion
                else niceVersion
  in
    (pps {ppIdMap = M.insert var ppvar (ppIdMap pps),
          ppUsedDocs = S.insert ppvar (ppUsedDocs pps)},
     text ppvar)
  where
    niceVersion :: String
    niceVersion = namePart var

    uglyVersion :: String
    uglyVersion =
      case var of
        Id (s,i) -> s ++ show i
        Fixed s  -> s

addLocal :: Id -> (Doc -> PP a) -> PP a
addLocal var action = PP $ \pps ->
  case M.lookup var (ppIdMap pps) of
    Just d -> unPP (action $ text d) pps
    Nothing -> 
      let ppvar = if S.member niceVersion (ppUsedDocs pps)
                    then uglyVersion
                    else niceVersion 
          
          (pps',result) = 
             unPP (action $ text ppvar) $
               pps {ppIdMap = M.insert var ppvar (ppIdMap pps),
                    ppUsedDocs = S.insert ppvar (ppUsedDocs pps)}
      in 
        (pps' {ppIdMap = M.delete var (ppIdMap pps'),
               ppUsedDocs = S.delete ppvar (ppUsedDocs pps')},
         result)
      where
        niceVersion :: String
        niceVersion = namePart var
    
        uglyVersion :: String
        uglyVersion =
          case var of
            Id (s,i) -> s ++ show i
            Fixed s  -> s

addLocals :: [Id] -> ([Doc] -> PP a) -> PP a
addLocals vars action =  addLocalsRec vars []
  where
    addLocalsRec []     ds = action $ reverse ds
    addLocalsRec (v:vs) ds = 
      addLocal v $ \d -> addLocalsRec vs (d:ds)

---

ppId :: Id -> PP Doc
ppId var = do 
  idmap <- getIdMap
  case M.lookup var idmap of
    Just d -> return $ text d
    Nothing -> do
      pp <- 
        case var of
          Fixed s  -> return s
          Id (s,i) -> do 
            warn $ "Identifier " ++ show var ++ " not found."
            return $ s ++ show i
      return $ text pp

-------------------------------

commas :: [Doc] -> Doc
commas es = hsep $ punctuate comma es

dots :: [Doc] -> Doc
dots es = hcat $ punctuate (char '.') es

ppFDRMod :: FDRMod -> PP Doc
ppFDRMod tops = do
  addTLGlobals tops
  ttops <- mapM ppDefinition $ topLevels tops
  return $ vcat $ punctuate (text "\n") ttops

-- This takes a pattern and does two things: tells you how it should be
-- displayed, and extends the local scope with the relevant identifiers for
-- the duration of the pretty printing.
ppPattern :: Pat -> (Doc -> PP a) -> PP a
ppPattern (PId var)         f = addLocal var f
ppPattern (PConcat p1 p2)   f = ppBinaryPattern p1 p2 (char '^') f
ppPattern (PDot p1 ps)      f = ppPatList (p1:ps) (char '.') f
ppPattern (PDouble p1 p2)   f = ppBinaryPattern p1 p2 (text "@@") f
ppPattern (PList pats)      f = 
  ppPatList pats comma $ \ppats -> f $ char '<' <> ppats <> char '>'
ppPattern (PConst c)        f = f $ ppConst c
ppPattern PEmptySet         f = f $ text "{}"
ppPattern (PSingletonSet p) f = ppPattern p $ \pp -> f $ braces pp
ppPattern (PTuple pats)     f =
  ppPatList pats comma $ \ppats -> f $ parens ppats
ppPattern PWildCard         f = f $ char '_'

-- abstract out the common case of printing a binary pattern
ppBinaryPattern :: Pat -> Pat -> Doc -> (Doc -> PP a) -> PP a
ppBinaryPattern p1 p2 pnct f = do
  ppPatParens p1 $ \pp1 -> 
    ppPatParens p2 $ \pp2 ->
      f $ pp1 <> pnct <> pp2

-- abstract out the common case of printing a list of patterns
ppPatList :: [Pat] -> Doc -> (Doc -> PP a) -> PP a
ppPatList pats pnct f = patList pats []
  where
--    patList :: [Exp] -> [Doc] -> PP a
    patList []     ds = f $ hcat $ punctuate pnct $ reverse ds
    patList (p:ps) ds = ppPatParens p $ \d -> patList ps (d:ds)


-- prints the pattern with an extra set of parens if it's not a var
ppPatParens :: Pat -> (Doc -> PP a) -> PP a
ppPatParens p@(PId _) f = ppPattern p f
ppPatParens p f = ppPattern p (\d -> f $ parens d)

-- print a datatype constructor declaration
ppConstructor :: (Id,[Exp]) -> PP Doc
ppConstructor (c,tys) = do
  tc  <- ppId c
  ttys <- mapM ppExp tys
  return $ dots (tc : map parens ttys)

ppDefinition :: Definition -> PP Doc
ppDefinition (DVar p e) = do
  -- Note that this may "double add" the variables in the pattern to the map,
  -- since they were probably added when we entered the scope of this definition
  -- as part of handling mutually recursive definitions.  This is fine, because
  -- ppPattern calls addLocal, which handles existing variables declarations
  -- gracefully.
  ppPattern p $ \pp -> do
    pe <- ppExp e
    return $ pp <+> char '=' <+> pe
ppDefinition (DFun funName funClauses) = do
  tname <- ppId funName
  vcat <$> mapM (ppFunClause tname) funClauses
  where
    ppFunClause :: Doc -> ([Pat],Exp) -> PP Doc
    ppFunClause fnm (pats,body) = ppPatList pats (char ',') $ \ppats -> do
      pbody <- ppExp body
      return $ fnm <+> parens ppats <+> char '=' $+$ (nest 2 $ pbody)
ppDefinition (DAnnot x t) = do
  px <- ppId x
  pt <- ppType t
  return $ px <+> text "::" <+> pt
ppDefinition (DDataType nm cnstrs) = do
  tnm <- ppId nm
  tcnstrs <- mapM ppConstructor cnstrs
  return $ 
    text "datatype" <+> tnm <+> char '=' 
       <+> (hcat $ punctuate (text " | ") tcnstrs)
ppDefinition (DSubType nm cnstrs) = do
  tnm <- ppId nm
  tcnstrs <- mapM ppConstructor cnstrs
  return $ 
    text "subtype" <+> tnm <+> char '=' 
       <+> (hcat $ punctuate (text " | ") tcnstrs)
ppDefinition (DChan xs []) = do 
  pxs <- commas <$> mapM ppId xs
  return $ text "channel" <+> pxs
ppDefinition (DChan xs tys) = do
  pxs <- commas <$> mapM ppId xs
  ptys <- mapM ppType tys
  return $ text "channel" <+> pxs <+> colon <+> dots ptys
ppDefinition (DInclude str) = 
  return $ text "include" <+> text (show str) --- XXXX hack for escape chars
ppDefinition (DExternal x) = do
  px <- ppId x
  return $ text "external" <+> px
ppDefinition (DTransparent x) = do
  px <- ppId x
  return $ text "transparent" <+> px
ppDefinition (DAssert a m) = do
  pa <- ppAssertion a m
  return $ text "assert" <+> pa

--just the letter part, not the brackets or [T=
modelLetter :: Model -> String
modelLetter MT  = "T"
modelLetter MF  = "F"
modelLetter MFD = "FD"

--This is [T] or [FD], etc.
ppModel :: Model -> Doc
ppModel = brackets . text . modelLetter

ppAssertion :: Assertion -> Model -> PP Doc
ppAssertion (ARefines p q) m = do
  pp <- ppExp p
  pq <- ppExp q
  return $ pp <+> text ('[' : pm ++ "=") <+> pq
  where
    pm = modelLetter m
ppAssertion (ADeadlockFree p) m = do
  pp <- ppExp p
  let pm = ppModel m
  return $ pp <+> text ":[deadlock free" <+> pm <> char ']'
ppAssertion (ADivergenceFree p) m = do
  pp <- ppExp p
  let pm = ppModel m
  return $ pp <+> text ":[divergence free" <+> pm <> char ']'
ppAssertion (ADeterministic p) m = do
  pp <- ppExp p
  let pm = ppModel m
  return $ pp <+> text ":[deterministic" <+> pm <> char ']'
ppAssertion (AHasTrace p t) m = do
  pp <- ppExp p
  pe <- ppExp t
  let pm = ppModel m
  return $ pp <+> text ":[has trace" <+> pm <> text "]:" <+> pe


ppType :: Type -> PP Doc
ppType TEvent        = return $ text "Event"
ppType TChar         = return $ text "Char"
ppType TBool         = return $ text "Bool"
ppType TInt          = return $ text "Int"
ppType TUnit         = return $ text "Unit"
ppType (TList t)     = do
  pt <- ppType t
  return $ char '<' <+> pt <+> char '>'
ppType (TSet t)      = do
  pt <- ppType t
  return $ braces pt
ppType (TMap t1 t2)  = do
  pt1 <- ppType t1
  pt2 <- ppType t2
  return $ text "(|" <+> pt1 <+> text "=>" <+> pt2 <+> text "|)"
ppType (TData x)     = ppId x
ppType (TRange a b)  = do 
  pa <- ppExpParens a
  pb <- ppExpParens b
  return $ braces $ (parens pa) <> text ".." <> (parens pb)
ppType TProc         = return $ text "Proc"

-- Printing comprehension/set statements.  Three notes:
--
-- 1) We take in a list of comprehension statements rather than each
--    individually for reasons of scope.  In particular, you can write
--    comprehensions like:
--    
--       < x+1 | x <- xs, isOdd(x) >
-- 
--    Here, the later comprehension statement "isOdd(x)" needs "x" to be in
--    scope.
-- 
-- 2) For the same reason, ppCompStmts takes in an argument indicating the
--    monadic scope of the local variables declared in the patterns (much like
--    addLocal and ppPattern).
--
-- 3) FDR3 appears to support both the "x <- a" syntax that is natural in
--    comprehensions, as in:
--
--      < x+1 | x <- xs >
-- 
--    and the "x : a" syntax that is natural in replicated operations, as in:
--
--     [] x : {0..5} @ P(x)
--
--    These mean the same thing, and it appears you can use either syntax in
--    either place.  For uniformity, we use only the "<-" syntax, since it is
--    the one mentioned on the relevant fdr page:
--
--      https://www.cs.ox.ac.uk/projects/fdr/manual/cspm/syntax.html#csp-statements
ppCompStmt :: [CompStmt] -> (Doc -> PP a) -> PP a
ppCompStmt cs f = ppCS cs []
  where
    -- ppCS :: [CompStmt] -> [Doc] -> PP a
    ppCS []                ds = 
      f $ commas $ reverse ds
    ppCS (CSGen p e : css) ds = do
      pe <- ppExp e
      ppPattern p $ \pp -> ppCS css (pp <+> text "<-" <+> pe : ds)
    ppCS (CSPred e : css)  ds = do
      pe <- ppExp e
      ppCS css (pe : ds)

-- Printing expressions
ppExp :: Exp -> PP Doc
ppExp (EId x) = ppId x
ppExp (ELambda pats e) = 
  ppPatList pats comma $ \ppats -> do
    te <- ppExp e
    return $ char '\\' <+> ppats <+> char '@' <+> te
ppExp (EApp fun es) = do
  tfun <- ppExpParens fun
  tes <- mapM ppExp es
  return $ tfun <> (parens $ commas tes)
ppExp (ELet defs e) = do
  addTLLocals (FDRMod defs) $ do
    pdefs <- mapM ppDefinition defs
    pe <- ppExp e
    return $ text "let" $$ nest 2 (vcat $ punctuate (text "\n") pdefs)
                        $$ text "within" $$ (nest 2 pe)
ppExp (EIfThenElse c e1 e2) = do
  tc <- ppExp c
  te1 <- ppExp e1
  te2 <- ppExp e2
  return $ 
     text "if" <+> tc <+> text "then" $+$ (nest 2 te1)
                       $$ text "else" $+$ (nest 2 te2)
ppExp (EUOp op e) = do
  te <- ppExpParens e
  return $ ppUOp op <+> te
ppExp (EBinOp e1 op e2) = ppBOpExp e1 (ppBinOp op) e2
ppExp (EConst c) = return $ ppConst c
ppExp (EError s) = return $ text "error" <> (parens $ text $ show s)
ppExp (EDot e es) = do 
  te <- ppExpParens e
  tes <- mapM ppExpParens es
  return $ dots (te:tes)
ppExp (EExtChoice e1 e2) = ppBOpExp e1 (text "[]") e2
ppExp (EGuarded e1 e2)   = ppBOpExp e1 (char '&') e2
ppExp (EHide e1 e2)      = ppBOpExp e1 (char '\\') e2
ppExp (EIntChoice e1 e2) = ppBOpExp e1 (text "|~|") e2
ppExp (EPrefix e1 ces e2) = do
  te1 <- ppExpParens e1
  tces_te2 <- ppCommsPrefix ces []
  return $ te1 <> tces_te2
  where
    ppCommsPrefix :: [(CommField)] -> [Doc] -> PP Doc
    ppCommsPrefix [] ds = do 
      te2 <- ppExpParens e2
      return $ hcat $ reverse $ te2 : (text " -> ") : ds
    ppCommsPrefix (comm:comms) ds =
      case ppComm comm of
        (d,Left e) -> do 
          pe <- ppExpParens e
          ppCommsPrefix comms ((d <> pe) : ds)
        (d,Right p) ->
          ppPattern p $ \pp -> 
            ppCommsPrefix comms ((d <> pp) : ds)
      where
        -- How to display the comm, and whether the thing that comes after it
        -- is a binder (as in the case of "c?x -> ...") or not (as in the case
        -- of "c!x -> ..."
        ppComm :: CommField -> (Doc,Either Exp Pat)
        ppComm (CFPlain e)   = (char '.', Left e)
        ppComm (CFInput p)   = (char '?', Right p)
        ppComm (CFOutput e)  = (char '!', Left e)
        ppComm (CFNDInput p) = (char '$', Right p)
ppExp (EProject e1 e2) = ppBOpExp e1 (text "|\\") e2
ppExp (ERename e1 nms) = do
  pe1 <- ppExpParens e1
  pnms <- mapM (\(n1,n2) -> (,) <$> ppExpParens n1 <*> ppExpParens n2) nms
  let prnms = map (\(pn1,pn2) -> pn1 <+> text "<-" <+> pn2) pnms
  return $ pe1 <+> text "[[" <+> commas prnms <+> text "]]"
ppExp (EAlphaParallel p a b q) = do
  pa <- ppExpParens a
  pb <- ppExpParens b
  ppBOpExp p (brackets $ pa <+> text "||" <+> pb) q
ppExp (EGenParallel p a q) = do
  pa <- ppExp a
  ppBOpExp p (text "[|" <+> pa <+> text "|]") q
ppExp (EInterleave e1 e2) = ppBOpExp e1 (text "|||") e2
ppExp (EException p a q)  = do
  pa <- ppExp a
  ppBOpExp p (text "[|" <+> pa <+> text "|>") q
ppExp (EInterrupt e1 e2)  = ppBOpExp e1 (text "/\\") e2
ppExp (ESeq e1 e2)        = ppBOpExp e1 (char ';') e2
ppExp (ELinkedParallel p nms q) = do
  pnms <- mapM (\(c,d) -> (,) <$> ppExpParens c <*> ppExpParens d) nms
  let ppnms = commas $ map (\(pc,pd) -> pc <+> text "<->" <+> pd) pnms
  ppBOpExp p ppnms q
ppExp (ETimeout e1 e2)    = ppBOpExp e1 (text "[>") e2
ppExp (ESyncExtChoice p a q) = do
  pa <- ppExp a
  ppBOpExp p (text "[+" <+> pa <+> text "+]") q
ppExp (ESyncInterrupt p a q) = do
  pa <- ppExp a
  ppBOpExp p (text "/+" <+> pa <+> text "+\\") q
ppExp (ERepAlphaParallel cs a p) =
  ppCompStmt cs $ \pstmts -> do
    pa <- ppExp a
    pp <- ppExpParens p
    return $ text "||" <+> pstmts <+> char '@' <+> brackets pa <+> pp
ppExp (ERepExtChoice cs p)     = ppRepExp (text "[]") cs p
ppExp (ERepGenParallel a cs p) = do
  pa <- ppExp a
  ppRepExp (text "[|" <+> pa <+> text "|]") cs p
ppExp (ERepInterleave cs p)    = ppRepExp (text "|||") cs p
ppExp (ERepIntChoice cs p)     = ppRepExp (text "|~|") cs p
ppExp (ERepLinkedParallel links cs p) = do
  plinks <- mapM (\(l,r) -> (,) <$> ppExpParens l <*> ppExpParens r) links
  let linkedLinks = map (\(pl,pr) -> pl <+> text "<->" <+> pr) plinks
  ppRepExp (brackets $ commas linkedLinks) cs p
ppExp (ERepSeq cs p)           = ppRepExp (char ';') cs p
ppExp (ERepSyncExtChoice a cs p) = do
  pa <- ppExp a
  ppRepExp (text "[+" <+> pa <+> text "+]") cs p
ppExp (EList es)          = do
  tes <- mapM ppExpParens es
  return $ char '<' <+> commas tes <+> char '>'
ppExp (EListComp es cs)   =
  ppCompStmt cs $ \pcs -> do
    pes <- mapM ppExpParens es
    return $ char '<' <+> commas pes <+> char '|' <+> pcs <+> char '>'
ppExp (EListFrom e)       = do
  pe <- ppExpParens e
  return $ char '<' <+> pe <+> text "..>"
ppExp (EListFromComp e cs) =
  ppCompStmt cs $ \pcs -> do
    pe <- ppExpParens e
    return $ char '<' <+> pe <+> text ".. |" <+> pcs <+> char '>'
ppExp (EListFromTo e1 e2) = do
  pe1 <- ppExpParens e1
  pe2 <- ppExpParens e2
  return $ char '<' <+> pe1 <+> text ".." <+> pe2 <+> char '>'
ppExp (EListFromToComp e1 e2 cs) =
  ppCompStmt cs $ \pcs -> do
    pe1 <- ppExpParens e1
    pe2 <- ppExpParens e2
    return $ char '<' <+> pe1 <+> text ".." <+> pe2
                      <+> char '|' <+> pcs <+> char '>'
ppExp (EListConcat e1 e2) = ppBOpExp e1 (char '^') e2
ppExp (EListLength e)     = do
  pe <- ppExp e
  return $ char '#' <+> pe
ppExp (ETuple es)         = parens . commas <$> mapM ppExp es
ppExp (ESet es)           = braces . commas <$> mapM ppExp es
ppExp (ESetComp es cs)    = 
  ppCompStmt cs $ \pcs -> do
    pes <- mapM ppExp es
    return $ braces $ commas pes <+> char '|' <+> pcs
ppExp (ESetFrom e)        = do
  pe <- ppExp e
  return $ braces $ pe <+> text ".."
ppExp (ESetFromComp e cs) =
  ppCompStmt cs $ \pcs -> do
    pe <- ppExp e
    return $ braces $ pe <+> text ".. |" <+> pcs
ppExp (ESetFromTo e1 e2)  = do
  pe1 <- ppExp e1
  pe2 <- ppExp e2
  return $ braces $ pe1 <+> text ".." <+> pe2
ppExp (ESetFromToComp e1 e2 cs) =
  ppCompStmt cs $ \pcs -> do
    pe1 <- ppExp e1
    pe2 <- ppExp e2
    return $ braces $ pe1 <+> text ".." <+> pe2 <+> char '|' <+> pcs
ppExp ESetInt  = return $ text "Int"
ppExp ESetBool = return $ text "Bool"
ppExp (EEnumSet es)       = do
  pes <- commas <$> mapM ppExp es
  return $ text "{|" <+> pes <+> text "|}"
ppExp (EEnumSetComp es cs) =
  ppCompStmt cs $ \pcs -> do
    pes <- commas <$> mapM ppExp es
    return $ text "{|" <+> pes <+> char '|' <+> pcs <+> text "|}"
ppExp (EMap es) = do
  tes <- mapM ppMapPair es
  return $ text "(|" <+> commas tes <+> text "|)"
  where 
    ppMapPair (e1, e2) = do te1 <- ppExpParens e1 
                            te2 <- ppExpParens e2
                            return $ te1 <+> text "=>" <+> te2


-- parens around compound things only
ppExpParens :: Exp -> PP Doc
ppExpParens e@(EId _)                 = ppExp e
ppExpParens e@(EConst _)              = ppExp e
ppExpParens e@(EList _)               = ppExp e
ppExpParens e@(EListComp _ _)         = ppExp e
ppExpParens e@(EListFrom _)           = ppExp e
ppExpParens e@(EListFromComp _ _)     = ppExp e
ppExpParens e@(EListFromTo _ _)       = ppExp e
ppExpParens e@(EListFromToComp _ _ _) = ppExp e
ppExpParens e@(ETuple _)              = ppExp e
ppExpParens e@(ESet _)                = ppExp e
ppExpParens e@(ESetComp _ _)          = ppExp e
ppExpParens e@(ESetFrom _)            = ppExp e
ppExpParens e@(ESetFromComp _ _)      = ppExp e
ppExpParens e@(ESetFromTo _ _)        = ppExp e
ppExpParens e@(ESetFromToComp _ _ _)  = ppExp e
ppExpParens e@(ESetInt)               = ppExp e
ppExpParens e@(ESetBool)              = ppExp e
ppExpParens e@(EEnumSet _)            = ppExp e
ppExpParens e@(EEnumSetComp _ _)      = ppExp e
ppExpParens e@(EMap _)                = ppExp e
ppExpParens e = parens <$> ppExp e

-- Abstract the common case of "binary" operators, which actually comes up much
-- more than just the arithmetic ones.
ppBOpExp :: Exp -> Doc -> Exp -> PP Doc
ppBOpExp e1 pop e2 = do
  pe1 <- ppExpParens e1
  pe2 <- ppExpParens e2
  return $ pe1 <+> pop <+> pe2

-- Abstract the common case of "replicated" operators
ppRepExp :: Doc -> [CompStmt] -> Exp -> PP Doc
ppRepExp op stmts e = do
  ppCompStmt stmts $ \pstmts -> do
    pe <- ppExp e
    return $ op <+> pstmts <+> char '@' <+> pe

ppConst :: Const -> Doc
ppConst CStop = text "STOP"
ppConst CSkip = text "SKIP"
ppConst (CInt n) = integer n
ppConst (CChar c) = char '\'' <> char c <> char '\''
ppConst (CBool b) = if b then text "True" else text "False"
ppConst (CString s) = text $ show s -- XXX hack.  I think this escapes things that matter?
ppConst CUnit = text "UnitVal"

ppUOp :: UOp -> Doc
ppUOp UNeg      = char '-'
ppUOp UNot      = text "not"
--ppUOp (Hide _) = error "Internal error: ppUOpApp called on hide"

ppBinOp :: BinOp -> Doc
ppBinOp BEq         = text "=="
ppBinOp BLeq        = text "<="
ppBinOp BLt         = char '<'
ppBinOp BGeq        = text ">="
ppBinOp BGt         = char '>'
ppBinOp BAnd        = text "and"
ppBinOp BOr         = text "or"
ppBinOp BNeq        = text "!="
ppBinOp BPlus       = char '+'
ppBinOp BMinus      = char '-'
ppBinOp BTimes      = char '*'
ppBinOp BDiv        = char '\\'
ppBinOp BMod        = char '%'

------------------
------------------ Top-level identifiers
------------------

topLevelIDs :: FDRMod -> [Id]
topLevelIDs m = concatMap tlIDs $ topLevels m
  where
   tlIDs :: Definition -> [Id]
   tlIDs (DFun nm _)      = [nm]
   tlIDs (DVar pat _)     = patIDs pat
   tlIDs (DAnnot _ _)     = []
   tlIDs (DDataType nm cnstrs) = nm : map fst cnstrs
   tlIDs (DSubType nm _)  = [nm]
   tlIDs (DChan x _)      = x
   tlIDs (DInclude _)     = []
   tlIDs (DExternal f)    = [f]
   tlIDs (DTransparent f) = [f]
   tlIDs (DAssert _ _)    = []

-- The IDs inside a pattern
patIDs :: Pat -> [Id]
patIDs (PId x)           = [x]
patIDs (PConcat p1 p2)   = patIDs p1 ++ patIDs p2
patIDs (PDot p1 p2)      = concatMap patIDs (p1:p2)
patIDs (PDouble p1 p2)   = patIDs p1 ++ patIDs p2
patIDs (PList ps)        = concatMap patIDs ps
patIDs (PConst _)        = []
patIDs PEmptySet         = []
patIDs (PSingletonSet p) = patIDs p
patIDs (PTuple ps)       = concatMap patIDs ps
patIDs PWildCard         = []

---- This scans a module and adds any top-level names to the monad, since they
---- may be used mutually recursively.
addTLGlobals :: FDRMod -> PP ()
addTLGlobals m = mapM_ addGlobal $ topLevelIDs m

-- The `PP a` arg here is the scope of these locals
addTLLocals :: FDRMod -> PP a -> PP a
addTLLocals m a = addLocals (topLevelIDs m) $ \_ -> a
--------------
--------------
--------------

genStyle :: Style
genStyle = Style {mode = LeftMode, lineLength = 0, ribbonsPerLine = 0}

preludeNames :: [Id]
preludeNames = []

prelude :: PPState
prelude = foldl' addName emptyPPState preludeNames
  where
    addName :: PPState -> Id -> PPState
    addName pps nm@(Fixed s) =
      pps {ppIdMap    = M.insert nm s (ppIdMap pps),
           ppUsedDocs = S.insert s (ppUsedDocs pps)}
    addName pps nm@(Id (s,_)) =
      pps {ppIdMap    = M.insert nm s (ppIdMap pps),
           ppUsedDocs = S.insert s (ppUsedDocs pps),
           ppWarnings = w : (ppWarnings pps)}
      where
        w = "Non-fixed id " ++ show nm ++ " in prelude,"

-- | Pretty-prints an FDR3 module.
-- Returns the pretty-printed module as a string, and a list of warnings.  The
-- module string should be valid FDR3 input.  The warnings will mention any
-- non-fixed identifiers that are used out of their scope.
emitMod :: FDRMod -> (String,[String])
emitMod m = let (d,ws) = runPP prelude $ ppFDRMod m in
               (renderStyle genStyle d, ws)

-- | Pretty-prints an FDR3 module.
-- Returns two lists of strings.  The strings in the first list are the
-- pretty-printed input modules, and should be valid input for FDR3.  The
-- strings in the second list are warnings, and will mention any non-fixed
-- identifiers used out of scope.  Globals with non-fixed identifiers in each
-- input module are considered in scope for subsequent modules in the list.
emitMods :: [FDRMod] -> ([String],[String])
emitMods mds =
  let (ds,ws) = runPP prelude $ mapM ppFDRMod mds in
    (map (renderStyle genStyle) ds, ws)
