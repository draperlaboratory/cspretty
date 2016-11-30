{- |
   Module      :  Language.CSP.Syntax
   Description :  Abstract syntax for CSP
   Copyright   :  Draper Laboratories
   
   Abstract syntax of machine-reable CSP.  This is intended to correspond
   with the input language of FDR3, though some features are likely missing.

-}

module Language.CSPM.Syntax where




{- | 'Id' is our type for names. -}
data Id  =
  -- | the 'Id' constructor should be used for most identifiers, like variable
  -- names.  It has two fields - a 'String' and an 'Int'.  Only the 'Int' is
  -- used to check equality of names, the 'String' is just a hint for pretty
  -- printing.  The pretty printer doesn't guarantee to use exactly this
  -- name in the case where different 'Id's use the same string part.
    Id    (String,Int)
  -- | 'Fixed' is for identifiers where the name matters outside the scope of
  -- what is currently being pretty printed (for example, to refer to the
  -- standard library).  The pretty printer will always use exactly this
  -- name, and the programmer must avoid conflicts to get sane CSPm.
  | Fixed String        
  deriving (Show)

instance Eq Id where
  (Id (_,i1)) == (Id (_,i2)) = i1 == i2
  (Fixed s1)  == (Fixed s2)  = s1 == s2
  _ == _                     = False
  
instance Ord Id where
  compare (Id (_,i1)) (Id (_,i2)) = compare i1 i2
  compare (Id _) (Fixed _)        = LT
  compare (Fixed s1) (Fixed s2)   = compare s1 s2
  compare (Fixed _)  (Id _)       = GT

-- | A helper function which gets the string part of an identifier, useful
-- for error messages
namePart :: Id -> String
namePart (Id (s,_)) = s
namePart (Fixed s)  = s

-- | Base types in FDR
data Type = TEvent | TProc
          | TChar | TBool | TInt | TUnit
          | TList Type | TSet Type | TMap Type Type
          | TData Id
          | TRange Exp Exp
            deriving (Eq, Show)

-- | Toplevel FDR modules (this corresponds to a .csp file)
data FDRMod = FDRMod { topLevels :: [Definition] }
              deriving (Eq, Show)

-- | Toplevel declarations in FDR
data Definition = 
    DVar Pat Exp
  | DFun Id [([Pat],Exp)]
  | DAnnot Id Type

   -- | Somewhat unusually, the arguments to data constructors in CSPm datatype
   -- declarations are actually expressions, not types.  In particular, the
   -- arguments must always be a set, as in:
   -- 
   -- >   datatype Foo = F.{0..5}.{True,False}
   -- 
   -- FDR provides a little syntax sugar to help with common cases, in that
   -- there are actually /expressions/ called @Int@ and @Bool@:
   --
   -- >     Int :: {Int}      Bool :: {Bool}
   -- >     Int = {0..}       Bool = {True,False}
  | DDataType Id [(Id,[Exp])]

  | DSubType Id [(Id,[Exp])]
  | DChan [Id] [Type]
  | DInclude String
  | DExternal Id
  | DTransparent Id
  | DAssert Assertion Model
    deriving (Eq, Show)

-- | The models that can be used in assertions.
data Model
  -- | Traces
  = MT
  -- | Failures
  | MF
  -- | Failures-divergences
  | MFD
  deriving (Eq,Show)

-- | FDR assertions
data Assertion = ARefines Exp Exp
               | ADeadlockFree Exp
               | ADivergenceFree Exp
               | ADeterministic Exp
               | AHasTrace Exp Exp
  deriving (Eq,Show)

-- | The types of fields one can use in a prefix.
data CommField =
  -- | .
    CFPlain Exp
  -- | ?
  | CFInput Pat
  -- | !
  | CFOutput Exp
  -- | $
  | CFNDInput Pat 
    deriving (Eq,Show)

-- | Constants
data Const = CStop | CSkip | CInt Integer | CChar Char | CUnit
           | CBool Bool | CString String
             deriving (Eq, Show)

-- | Comprehension Statements
data CompStmt =
    CSGen Pat Exp  -- CSGen p e  ==   p <- e     (or    p : e)
  | CSPred Exp
  deriving (Eq,Show)

-- | Patterns
data Pat =
    PId Id
  | PConcat Pat Pat
  | PDot Pat [Pat]
  | PDouble Pat Pat
  | PList [Pat]
  | PConst Const
  | PEmptySet
  | PSingletonSet Pat
  | PTuple [Pat]
  | PWildCard
  deriving (Eq,Show)

-- | Expressions
data Exp =
  -- FP basics
    EId Id
  | ELambda [Pat] Exp
  | EApp Exp [Exp]
  | ELet [Definition] Exp
  | EIfThenElse Exp Exp Exp
  | EUOp UOp Exp
  | EBinOp Exp BinOp Exp
  | EConst Const
  | EError String
    
  -- CSP-specific
  | EDot Exp [Exp]

  | EExtChoice Exp Exp
  | EGuarded Exp Exp
  | EHide Exp Exp
  | EIntChoice Exp Exp
  -- | In prefix we deviate a little from the strict grammar by taking an exp
  -- and its dotted arguments rather than an arbitrary expression.  This
  -- helps with pretty printing (and conceptually).
  | EPrefix Exp [CommField] Exp  
  | EProject Exp Exp  
  | ERename Exp [(Exp,Exp)]

  | EAlphaParallel Exp Exp Exp Exp
  | EGenParallel Exp Exp Exp
  | EInterleave Exp Exp

  | EException Exp Exp Exp
  | EInterrupt Exp Exp
  | ESeq Exp Exp
  | ELinkedParallel Exp [(Exp,Exp)] Exp 
  | ETimeout Exp Exp
  | ESyncExtChoice Exp Exp Exp
  | ESyncInterrupt Exp Exp Exp

  | ERepAlphaParallel [CompStmt] Exp Exp
  | ERepExtChoice [CompStmt] Exp
  | ERepGenParallel Exp [CompStmt] Exp
  | ERepInterleave [CompStmt] Exp
  | ERepIntChoice [CompStmt] Exp
  | ERepLinkedParallel [(Exp,Exp)] [CompStmt] Exp
  | ERepSeq [CompStmt] Exp
  | ERepSyncExtChoice Exp [CompStmt] Exp

  -- Lists
  | EList [Exp]
  | EListComp [Exp] [CompStmt]
  | EListFrom Exp
  | EListFromComp Exp [CompStmt]
  | EListFromTo Exp Exp
  | EListFromToComp Exp Exp [CompStmt]
  | EListConcat Exp Exp
  | EListLength Exp

  -- Tuples
  | ETuple [Exp]
         
  -- Sets
  | ESet [Exp]
  | ESetComp [Exp] [CompStmt]
  | ESetFrom Exp
  | ESetFromComp Exp [CompStmt]
  | ESetFromTo Exp Exp
  | ESetFromToComp Exp Exp [CompStmt]

  -- Built-in sets.  In the official CSPm syntax, these are just IDs provided by
  -- the standard library.  But for sanity, I'm making them explicit parts of
  -- the syntax.
  | ESetInt
  | ESetBool

  -- Enumerated Set
  | EEnumSet [Exp]
  | EEnumSetComp [Exp] [CompStmt]

  --maps
  | EMap [(Exp, Exp)]
    deriving (Eq, Show)

-- | Unary boolean and arithmetic operators
data UOp = 
    UNeg 
  | UNot
  deriving (Eq, Show)

-- | Binary boolean and arithmetic operators
data BinOp =

    BEq
  | BNeq
  | BLeq
  | BLt
  | BGeq
  | BGt

  | BPlus
  | BMinus
  | BTimes
  | BDiv
  | BMod

  | BAnd
  | BOr
  deriving (Eq, Show)
