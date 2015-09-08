-- * Module VanHaskell

-- File: VanHaskell.hs
-- Purpose: Generate C from uber cool VH language
-- Author: Benjamin Schulz
-- License: BSD3

-- ** Description

{-
To navigate this file efficiently, use a folding/outlining editor. This
file uses org-style outlining. E.g. ``-- ***" introduces a level 3 fold.

VanHaskell is a code generator/embedded language that allows generating
C99 code from two kinds of building blocks: C99 functions that follow a
special form and processes defined in the VH language.

Supported C functions take the form 
  void fun(restrictPtrToX, restrictPtrToY, ...) 

The generator handles memory allocations.
-}

-- ** Language

{-# LANGUAGE BangPatterns
           , DeriveDataTypeable
           , FlexibleContexts
           , GADTs
           , GeneralizedNewtypeDeriving
           , ScopedTypeVariables
           , TypeFamilies #-}

-- ** Exports

module Language.VanHaskell where

-- ** Imports

import Prelude hiding (foldl, mapM)               -- hiding to prevent
import Control.Applicative (pure, (<$>), (<|>))
import qualified Control.Applicative as Ap
import Control.Monad        hiding (foldM, mapM)  -- accidental use
import Control.Monad.Error  hiding (foldM, mapM)
import Data.Generics
import Data.Maybe
import Control.Monad.Reader hiding (foldM, mapM)
import Control.Monad.State  hiding (foldM, mapM)
import Data.Dynamic
import Data.Foldable (Foldable, foldl', foldlM)
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as S
import Data.Traversable (Traversable, mapM)
import Data.Tree hiding (flatten)
import System.IO (IO)
import qualified System.IO as IO

-- * The main interface

data CType = POD { ctypename :: String, cpodsize :: Int }  -- name, size in bytes
           | Struct { ctypename :: String, cstructfields :: [(String, CType)] }
           deriving (Data, Eq, Ord, Show, Typeable)

data Parameter = In_    { parname :: String, partype :: CType }
               | InOut_ { parname :: String, partype :: CType }
               | Out_   { parname :: String, partype :: CType }
               | Par_   { parname :: String, partype :: CType }
               deriving (Data, Eq, Ord, Show, Typeable)

data Function = Function { funname :: String
                         , funpars :: [Parameter]
                         , funcbody :: String }
              deriving (Data, Eq, Ord, Show, Typeable)

data Memory = Var   { memname :: String, memtype :: CType }
            | Array { memname :: String, memtype :: CType, memarrsize :: Int }
            deriving (Data, Eq, Ord, Show, Typeable)

data Argument = In    { argmem :: Memory }
              | InOut { argmem :: Memory }
              | Out   { argmem :: Memory }
              deriving (Data, Eq, Ord, Show, Typeable)

type Value = String  -- scaffolding

data Comparable = MemComp Memory | ValComp Value deriving (Data, Eq, Ord, Show, Typeable)

data CondTerm = EQ Comparable Comparable  | NEQ Comparable Comparable
              | LT Comparable Comparable  | NLT Comparable Comparable
              | GT Comparable Comparable  | NGT Comparable Comparable
              | ZR Comparable             | NZR Comparable
              | Not CondTerm | And CondTerm CondTerm | Or CondTerm CondTerm
              deriving (Data, Eq, Ord, Show, Typeable)

data Term = Call Function [Argument]
          | Shuffle [(String, String)]  -- rebind memory elements to different names
          | Store Memory Value
          | If CondTerm [Term] [Term]
          | When   CondTerm [Term]
          | Unless CondTerm [Term]  -- Assumes condition is usually false
--          | Loop   CondTerm Term [Term]
          | Parallel [Term] [[(String, String)]]
          deriving (Eq, Data, Ord, Show, Typeable)

data Process = Process { procname :: String
                       , accepts :: [Memory], returns :: [Memory]
                       , terms :: [Term] } deriving (Eq, Ord, Show)

-- The third argument provides mappings from left returns to right accepts.
link :: Process -> Process -> String -> [(String, String)] -> Process
link (Process _ asl rsl termsl) (Process _ asr rsr termsr) name arm = 
  Process name asl rsr $ termsl++[Shuffle arm]++termsr

--(>\\) p1 (p2, xm) = link p1 p2 xm

-- ** Utility functions

keep :: String -> (String, String)
keep x = (x, x)

isStruct :: CType -> Bool
isStruct (POD _ _)    = False
isStruct (Struct _ _) = True

ctypesize :: CType -> Integer
ctypesize (POD _ s) = fromIntegral s
ctypesize (Struct _ fs) = acc fs
 where acc xs = foldl' step 0 xs
       step i (_, p@(POD _ _)) = i + (ctypesize p)
       step i (_, (Struct _ subfs)) = i + (acc subfs)

extent :: Memory -> Integer
extent (Var _ t)     = ctypesize t
extent (Array _ t n) = (ctypesize t) * (fromIntegral n)

offsets :: CType -> [Integer]
offsets (Struct _ fs) = reverse $ acc fs [0]
 where acc xs ns = foldl' step ns xs
       step is (_, p@(POD _ _)) = ((head is) + (ctypesize p)):is
       step is (_, (Struct _ subfs)) = acc subfs is
offsets (POD _ _) = [0]

types :: CType -> [CType]
types (Struct _ fs) = reverse $ acc fs []
 where acc xs ts = foldl' step ts xs
       step is (_, p@(POD _ _)) = p:is
       step is (_, (Struct _ subfs)) = acc subfs is
types p@(POD _ _) = [p]

-- TODO(bas) Extract common traversal structure or use generic traversal.

makeLocal :: [Parameter] -> String
makeLocal pars = L.intercalate "\n" $ map f pars
 where f x = let pn  = parname x 
                 ctn = ctypename (partype x) in
             ctn++" "++pn++"_ = *"++pn++";"

isBranch (If _ _ _) = True
isBranch _          = False

-- ** Utilities used during evaluation

validArguments :: Function -> [Argument] -> Bool
validArguments f args = all argParAgree (zip args pars)
 where pars = funpars f
       argParAgree pa = 
         case pa of
           ((In _),    (In_ _ _))    -> True
           ((InOut _), (InOut_ _ _)) -> True
           ((Out _),   (Out_ _ _))   -> True
           _                         -> False

-- * Evaluation
-- ** The model
-- *** Shared error type

-- EvalError lets us use the Monad instance for
-- Either e and catch fail calls via the ErrorT context.

data EvalError = EvalErrNoStr | EvalErrStr String deriving (Show)

instance Error EvalError where
  noMsg  = EvalErrNoStr
  strMsg = EvalErrStr
  
type Err a = Either EvalError a

-- *** Support for annotations
-- There are two reasons for annotations: first, to keep configuration data
-- around and, second, as a way to record information about the input that's
-- learned along the way.
--
-- For example, one approach is to split passes into analyser passes that hunt
-- the input for useful information and transformer passes that can make
-- profitable use of the annotations from the analyser(s).
--
-- If we knew precisely how we will develop our stages, then we could make
-- annotations part of a data type. We, however, lack this prescience, and as
-- a result I found it helpful to use indexed Dynamics as annotations. Thanks
-- to this minor complication, we get to experiment cheaply by changing only
-- the parts that provide or consume annotations.

type Annotations = Map String Dynamic

emptyAnnotations = M.empty :: Annotations

-- Simple insert that enforces key-uniqueness at runtime.
insertU :: (Ord k) => k -> a -> Map k a -> Map k a
insertU k x ms = if isNothing (M.lookup k ms) then M.insert k x ms else undefined

annotate ms k x = insertU k x ms

-- *** Stage and Inter(mediate)

type Stage t t1 = t -> Err t1

data Inter a = Inter a Annotations deriving Show

interFrom :: a -> Inter a
interFrom x = Inter x emptyAnnotations

-- *** buildM

-- A convenience function that folds monadically over the input with a step
-- function and assembles the individual monoidal computation results into a
-- single monoidal computation output along the way. It's strict in the
-- assembled value. It's the monadic counterpart to Data.Foldable.foldMap

buildM' :: (Monoid b, Functor m, Monad m, Foldable t) => 
          (a -> m b) -> b -> t a -> m b
buildM' f out0 xs = foldlM (\ !acc x -> 
                           (\ !y -> acc `mappend` y) <$> f x) out0 xs

buildIxM' :: (Monoid b, Num n, Functor m, Monad m, Foldable t) =>
            ((a, n) -> m b) -> b -> t a -> m b
buildIxM' f out0 xs = 
  fst <$> foldlM (\ !(acc, i) x ->
                 (\ !y -> (acc `mappend` y, i+1)) <$> f (x, i)) (out0, 0) xs

buildM :: (Monoid b, Functor m, Monad m, Foldable t) => 
         (a -> m b) -> t a -> m b
buildM f xs = buildM' f mempty xs

buildIxM :: (Monoid b, Num n, Functor m, Monad m, Foldable t) =>
           ((a, n) -> m b) -> t a -> m b
buildIxM f xs = buildIxM' f mempty xs

-- ** Down to business
-- *** Internal types
-- **** Due to MemId

type MemId = Integer

data Mem' = Mem' { mem'id :: MemId, mem'type :: CType }

data Comp' = MemComp' MemId | ValComp' Value deriving (Eq, Ord, Show)

data CondTerm' = EQ' Comp' Comp' | NEQ' Comp' Comp'
               | LT' Comp' Comp' | NLT' Comp' Comp'
               | GT' Comp' Comp' | NGT' Comp' Comp'
               | ZR' Comp'       | NZR' Comp'
               | Not' CondTerm' | And' CondTerm' CondTerm' | Or' CondTerm' CondTerm'
               deriving (Eq, Ord, Show)

data Term' = Call' String [MemId]
           | Store' MemId Value
           deriving (Eq, Ord, Show)

-- **** Branch

data Branch a = RootBranch { branch :: a, branchcond :: Maybe CondTerm }
              | BoolBranch { branchbool :: Bool, branch :: a, branchcond :: Maybe CondTerm }
              | ValBranch  { branchval :: Value, branch :: a, branchcond :: Maybe CondTerm }
              deriving (Eq, Ord, Show)

isRootBranch (RootBranch _ _) = True
isRootBranch _                = False

-- *** Stage 1: Recast input in Data.Tree form
-- The branch structure defined by the recursive Term constructor If is
-- transformed into a Data.Tree Branch. (Originally, I tried SYB generics
-- on Term directly but didn't find it worth the trouble in the end.)

stage_1k :: [Term] -> Tree (Branch [Term])
stage_1k ts = unfoldTree f seed where 
  seed = (ts, RootBranch)  -- (terms, Constructor for branch)
  f (ts, b) =
    let (thisBranch, rest) = L.partition (not . isBranch) ts
        continue = not . null $ rest
        next@(If cond _ _) = head rest
        nextSeeds = if continue then extractSeeds next else []
        thisCond = if continue then Just cond else Nothing in
    (b thisBranch thisCond, nextSeeds)
  extractSeeds (If cond tb fb) = [(tb, BoolBranch True),
                                  (fb, BoolBranch False)]

stage_1 :: Inter [Term] -> Either a (Inter (Tree (Branch [Term])))
stage_1 (Inter ts a) = Right $ Inter (stage_1k ts) a

-- *** Stage 2: Memory handles and error checking
-- **** Description
-- (1) By assigning unique ids for each memory item (deshuffling if you like),
-- this stage converts the input to the internal representation. Along the way,
-- it also performs most of the error checking.
--
-- (2) As annotation, this stage provides the set of all called functions.

-- **** Stage 2 structure

type S1FunMap = Map String Function
type S1MemMap = Map String Mem'  -- Handle ~> Mem
type S1State = (S1MemMap, S1FunMap, MemId)  -- (, , last id)

emptyS1State = (M.empty, M.empty, 0)

newtype S1M a = S1M { mkS1 :: ErrorT EvalError (State S1State) a }
  deriving (Applicative, Functor, Monad, MonadError EvalError, MonadState S1State)

runS1 :: ErrorT EvalError (State S1State) a -> S1State
      -> (Either EvalError a, S1State)
runS1 k s = runState (runErrorT k) s

-- ***** S1M accessors

getS1MemMap :: (MonadState S1State m) => m S1MemMap
getS1MemMap = get >>= \(ks, _, _) -> return ks
putS1MemMap :: (MonadState S1State m) => S1MemMap -> m ()
putS1MemMap kis = get >>= \(_, fm, n) -> put (kis, fm, n)
modS1MemMap :: (MonadState S1State m) => (S1MemMap -> S1MemMap) -> m ()
modS1MemMap f = getS1MemMap >>= \kis -> putS1MemMap (f kis)
getS1FunMap :: (MonadState S1State m) => m S1FunMap
getS1FunMap = get >>= \(_, fm, _) -> return fm
putS1FunMap :: (MonadState S1State m) => S1FunMap -> m ()
putS1FunMap fm = get >>= \(ks, _, n) -> put (ks, fm, n)
modS1FunMap :: (MonadState S1State m) => (S1FunMap -> S1FunMap) -> m ()
modS1FunMap f = getS1FunMap >>= \fm -> putS1FunMap (f fm)

takeId :: (MonadState S1State m) => m MemId
takeId = get >>= \(kis, fm, n) -> put (kis, fm, n+1) >>= \_ -> return $ n+1  

-- **** Error checking

expectBoundType :: (Eq a, Monad m, Show a) => [Char] -> a -> a -> m ()
expectBoundType h t0 t =
  when (t0 /= t) (fail $ errMsgHandleTypeMismatch h t0 t)

expectBoundMem :: (MonadState S1State m) => Memory -> m ()
expectBoundMem m =
  getS1MemMap >>= \kxs ->
  let { h = memname m; nj = M.lookup h kxs } in
  if isNothing nj then (fail $ errMsgMemNotKnown h)
                  else let (Mem' _ t0) = fromJust nj in
                       expectBoundType h t0 (memtype m)

expectGoodCall :: (Monad m) => Function -> [Argument] -> m ()
expectGoodCall f@(Function n pars _) args =
 when (not $ validArguments f args) (fail $ errMsgBadFunCall f args)

-- TODO(bas) Actually, it might be nicer to just rename the aliasing fun;
--           downside is more complicated Function -> String mapping for Call'
expectIdenticalFuns name f0 f1 =
  when (f0 /= f1) (fail $ errMsgDifferentFuns name f0 f1)

-- **** Bind memory

bind :: String -> CType -> S1M MemId
bind h t = 
  takeId >>= \id ->
  modS1MemMap (\kxs -> M.insert h (Mem' id t) kxs) >>
  return id

bind_ :: String -> CType -> S1M ()
bind_ h t = bind h t >> return ()

-- If the memory is bound, return id; if it isn't, bind it and return id.
findOrBind :: Memory -> S1M MemId
findOrBind m =
  getS1MemMap >>= \s -> 
  let { h = memname m; t = memtype m; nj = M.lookup h s } in
  case nj of
    Just (Mem' id0 t0) -> expectBoundType h t0 t >> return id0
    Nothing -> bind h t

findOrBind_ :: Memory -> S1M ()
findOrBind_ m = findOrBind m >> return ()

-- **** Process terms
-- ***** Process Call

prepAndCheckBeforeCall :: [Argument] -> S1M ()
prepAndCheckBeforeCall args = forM_ args f
  where f x = case x of
                (In m) -> expectBoundMem m
                arg    -> findOrBind_ $ argmem arg

rememberFun :: (MonadState S1State m) => Function -> m ()
rememberFun f =
  getS1FunMap >>= \fs ->
  let { fn = funname f;
        nj = M.lookup fn fs; known = isJust nj; f0 = fromJust nj } in
  if known then expectIdenticalFuns fn f0 f
           else modS1FunMap (\kxs -> M.insert fn f kxs)

s1ProcCall :: Function -> [Argument] -> S1M Term'
s1ProcCall f@(Function fn pars _) args =
  expectGoodCall f args >> prepAndCheckBeforeCall args >> rememberFun f >>
  getS1MemMap >>= \kxs ->
  return $ Call' fn  -- pACBC ensures that the fromJust below is safe
    (map (\x -> mem'id . fromJust $ (M.lookup (memname . argmem $ x) kxs))
         args)

-- ***** Process Store

s1ProcStore :: Memory -> Value -> S1M Term'
s1ProcStore m x = findOrBind m >>= \ix -> return $ Store' ix x

-- ***** Traverse input

s1Step :: Term -> S1M [Term']
s1Step x =  -- TODO(bas) Add context to error messages
  pure <$> case x of
             Call  f args -> s1ProcCall f args
             Store m x    -> s1ProcStore m x
             -- TODO(bas) Handle other terms

s1Trav :: (Traversable t, Foldable t1)
 =>      t (Branch (t1  Term))
 -> S1M (t (Branch [Term']))
s1Trav = mapM
  (\x -> let ts = branch x in
         buildM s1Step ts >>= \ts1 ->
         return x { branch = ts1 }) 

-- ***** Run it

-- Extract Either from first part of pair
either1st :: (Either a t, b) -> Either a (t, b)
either1st p = case fst p of { Right x -> Right (x, snd p); Left e -> Left e }

mapValsToSet :: (Ord b) => Map a b -> Set b
mapValsToSet m = S.fromList (snd <$> M.toList m)

s1transf :: (Traversable t, Foldable t1)
 => t (Branch (t1 Term))
 -> Either EvalError (t (Branch [Term']), Set Function)
s1transf ts = either1st (ei, fs)
 where (ei, (_, fm, _)) = runS1 (mkS1 $ s1Trav ts) emptyS1State
       fs = mapValsToSet fm

-- **** stage_2

stage_2 :: (Traversable t, Foldable t1)
 =>      Inter (t (Branch (t1 Term)))
 -> Err (Inter (t (Branch [Term'])))
stage_2 (Inter xs a) = f <$> (s1transf xs)
 where f (xs', fs) = Inter xs' (if S.null fs then a
                                else annotate a "function-set" $ toDyn fs)

extractFunctionSet :: Annotations -> Set Function
extractFunctionSet a = 
  let nj = M.lookup "function-set" a in
  if isJust nj then fromJust . fromDynamic . fromJust $ nj
               else S.empty

-- **** Error messages

errMsgBadFunCall (Function name pars _) args =
  "Bad function call when calling function \""++name++"\":"++
  "Expected parameters: \""++(show pars)++"\"\n"++
  "But called with:     \""++(show args)++"\"\n"

errMsgDifferentFuns n f0 f1 =
  "Function redefinition: the name \""++n++"\" was used to refer to different"++
  "functions.\n"++
  "Original function: \""++(show f0)++"\"\n"++
  "Aliasing function: \""++(show f1)++"\""

errMsgHandleTypeMismatch h t0 t1 = 
  "Memory type mismatch: The handle \""++h++"\" was used to refer to different types.\n"++
  "Original type: \""++(show t0)++"\"\n"++
  "Aliasing type: \""++(show t1)++"\""

errMsgMemNotKnown h = 
  "Unknown memory: The memory referred to by \""++h++"\" has not been claimed.\n"++
  "Possible solutions: Use memory as an Out parameter or\n"++
  "                    use a Store Term to initialize it."

errMsgDuplicateClaim h =
  "Bad memory claim: the memory referred to by \""++h++"\" is already claimed.\n"++
  "Possible solution: use a unique name as handle."

-- *** Stage 3: From memory handles to actual memory

-- *** Stage 4: From Tree to linear blocks
-- **** Types

data Block where
      BLT :: (Foldable t, Show (t Term')) => t Term' -> Block
      BLC :: CondTerm -> Block
      Label :: Value -> Block
      Open :: Block
      Close :: Block
--TODO(bas) This definition of Block allows generic storage of Term', but
--that means we can't use deriving :( Probably better to use a type variable
--(Block a)

instance Show Block where
  show (BLT xs)  = "BLT " ++ (show xs)
  show (BLC c)   = "BLC " ++ (show c)
  show (Label v) = "Label " ++ (show v)
  show Open = "Open"
  show Close = "Close"

-- **** Recursive conversion

-- These functions define a non-tail-recursive conversion of the tree.
-- If tail-recursion is desired, we could either investigate adding block-
-- closing markers to the tree as last element of each subtree or folding
-- over the tree (depth-first) while maintaining a state consisting of 
-- `([num children], [seen children])`.

boolLabel True = "1"
boolLabel False = "0"

treeToBlocks :: (Foldable t, Show (t Term'))
             => Tree (Branch (t Term')) -> [Block]
treeToBlocks node =
  let x = rootLabel node
      cs = subForest node
      cond c = if isJust c then [BLC (fromJust c)] else []
      cbs = if not . null $ cs
            then (cond $ branchcond x) ++
                 (Open : 
                   (concatMap treeToBlocks cs) ++
                 [Close])
            else [] in
  case x of
    BoolBranch x ts _  -> (Label $ boolLabel x) :
                           Open : 
                             (BLT ts) :
                             cbs ++ 
                          [Close]
    RootBranch ts _    -> (BLT ts) : cbs

-- **** stage_4

stage_4 :: (Foldable t, Show (t Term'))
 => Inter (Tree (Branch (t Term')))
 -> Either a (Inter [Block])
stage_4 (Inter xs a) = Right (Inter (treeToBlocks xs) a)

-- *** Stage 5: Output C99
-- **** Structure

data Location = Offset Integer  -- in bytes
              deriving (Show)

data MemAlloc = MemAlloc { maloc :: Location, matype :: CType }
              deriving (Show)

type StructSet = Set CType

data S2State = S2State { bindings :: Map MemId MemAlloc
                       , memuse   :: Set (Integer, Integer) }
                       deriving (Show)

emptyS2State = S2State { bindings = M.empty, memuse = S.empty }

type MemState = (Map MemId MemAlloc, Set (Integer, Integer))

type S2M a = State S2State a

-- **** Convert terms

termsStr :: (Foldable t) => t Term' -> S2M String
termsStr ts = return "TERMS BE HERE;\n"  -- TODO(bas) Migrate term generation

-- **** Convert branches
-- ***** Building blocks

-- Convention: Items add their own newline at the end but not beginning.

switchStr :: String -> String
switchStr s = "switch ("++s++")\n"

compStr :: Comparable -> String
compStr (ValComp x) = x

condStr :: CondTerm -> String
condStr (ZR c) = switchStr ("0 == "++(compStr c))

caseStr :: String -> String
caseStr s = "case "++s++":\n"

branchCaseStr :: (Branch a) -> String
branchCaseStr (BoolBranch v _ _) = 
  case v of
    True  -> caseStr "1"
    False -> caseStr "0"

branchCaseEndStr :: String
branchCaseEndStr = "\n} break;\n"

branchCondStr :: Maybe CondTerm -> String
branchCondStr (Just c) = condStr c
branchCondStr Nothing  = "{\n"

-- ***** Conversion

blocksToString :: (Foldable t) 
 => t Block -> S2M String
blocksToString xs =
  let f acc (BLT ts)  = termsStr ts >>= \str -> return (acc ++ str)
      f acc (BLC c)   = return (acc ++ (condStr c))
      f acc (Label v) = return (acc ++ (caseStr v))
      f acc Open      = return (acc ++ "{\n")
      f acc Close     = return (acc ++ "break;\n}\n")
      -- adds harmless extra breaks
      in
  foldlM f "" xs

-- **** stage_5

stage_5k :: (Foldable t) => t Block -> String
stage_5k xs = evalState (blocksToString xs) emptyS2State

stage_5 :: (Foldable t) => Inter (t Block) -> Either a String
stage_5 (Inter xs a) = Right (stage_5k xs)

-- ** Putting it all together

runStages :: Inter [Term] -> Either EvalError String
runStages = stage_1 >=> stage_2 >=> 
            stage_4 >=> stage_5

vhCompile :: Process -> Either EvalError String
vhCompile x = runStages (interFrom $ terms x)

showError :: EvalError -> String
showError (EvalErrStr s) = s ++ "\n"
showError _ = "An unspecified error occured during compilation.\n"

-- This is a helper for testing.
compileToString :: Process -> String
compileToString x = either showError id (vhCompile x)

compileToFile :: Process -> IO ()
compileToFile x = 
  let n  = procname x in
  case vhCompile x of
    Right str -> IO.openFile (n++".c") IO.WriteMode >>= \file ->
                 IO.hPutStr file str >>
                 IO.hClose file
    Left err  -> IO.hPutStr IO.stderr (showError err)

