-- | "Text.Regex.TDFA.TDFA" converts the QNFA from TNFA into the DFA.
-- A DFA state corresponds to a Set of QNFA states, repesented as list
-- of Index which are used to lookup the DFA state in a lazy Trie
-- which holds all possible subsets of QNFA states.
module Text.Regex.TDFA.TDFA(patternToRegex,DFA(..),DT(..)
                            ,examineDFA,nfaToDFA,dfaMap) where

--import Control.Arrow((***))
import Data.Monoid as Mon(Monoid(..))
import Control.Monad.State(State,MonadState(..),execState)
import Data.Array.IArray(Array,(!),bounds,{-assocs-})
import Data.IntMap(IntMap)
import qualified Data.IntMap as IMap(empty,keys,delete,null,lookup,fromDistinctAscList
                                    ,member,unionWith,singleton,union
                                    ,toAscList,Key,elems,toList,insert
                                    ,insertWith,insertWithKey)
import Data.IntMap.CharMap2(CharMap(..))
import qualified Data.IntMap.CharMap2 as Map(empty)
--import Data.IntSet(IntSet)
import qualified Data.IntSet as ISet(empty,singleton,null)
import Data.List(foldl')
import qualified Data.Map (Map,empty,member,insert,elems)
import Data.Sequence as S((|>),{-viewl,ViewL(..)-})

import Text.Regex.TDFA.Common {- all -}
import Text.Regex.TDFA.IntArrTrieSet(TrieSet)
import qualified Text.Regex.TDFA.IntArrTrieSet as Trie(lookupAsc,fromSinglesMerge)
import Text.Regex.TDFA.Pattern(Pattern)
--import Text.Regex.TDFA.RunMutState(toInstructions)
import Text.Regex.TDFA.TNFA(patternToNFA)
--import Debug.Trace

{- By Chris Kuklewicz, 2007. BSD License, see the LICENSE file. -}

err :: String -> a
err s = common_error "Text.Regex.TDFA.TDFA"  s

dlose :: DFA
dlose = DFA { d_id = ISet.empty
            , d_dt = Simple' { dt_win = IMap.empty
                             , dt_trans = Map.empty
                             , dt_other = Transition dlose dlose mempty } }

-- dumb smart constructor for tracing construction (I wanted to monitor laziness)
{-# INLINE makeDFA #-}
makeDFA :: SetIndex -> DT -> DFA
makeDFA i dt = DFA i dt

-- Note that no CompOption or ExecOption parameter is needed.
nfaToDFA :: ((Index,Array Index QNFA),Array Tag OP,Array GroupIndex [GroupInfo])
         -> CompOption -> ExecOption
         -> Regex
nfaToDFA ((startIndex,aQNFA),aTagOp,aGroupInfo) co eo = Regex dfa startIndex indexBounds tagBounds trie aTagOp aGroupInfo ifa co eo where
  dfa = indexesToDFA [startIndex]
  indexBounds = bounds aQNFA
  tagBounds = bounds aTagOp
  ifa = isDFAFrontAnchored (multiline co) dfa

  indexesToDFA = {-# SCC "nfaToDFA.indexesToDFA" #-} Trie.lookupAsc trie  -- Lookup in cache

  trie :: TrieSet DFA
  trie = Trie.fromSinglesMerge dlose mergeDFA (bounds aQNFA) indexToDFA

  newTransition :: DTrans -> Transition
  newTransition dtrans = Transition { trans_many = indexesToDFA (IMap.keys dtransWithSpawn)
                                    , trans_single = indexesToDFA (IMap.keys dtrans)
                                    , trans_how = dtransWithSpawn }
    where dtransWithSpawn = addSpawn dtrans

  makeTransition :: DTrans -> Transition
  makeTransition dtrans | hasSpawn  = Transition { trans_many = indexesToDFA (IMap.keys dtrans)
                                                 , trans_single = indexesToDFA (IMap.keys (IMap.delete startIndex dtrans))
                                                 , trans_how = dtrans }
                        | otherwise = Transition { trans_many = indexesToDFA (IMap.keys dtrans)
                                                 , trans_single = indexesToDFA (IMap.keys dtrans)
                                                 , trans_how = dtrans }
    where hasSpawn = maybe False IMap.null (IMap.lookup startIndex dtrans)

  -- coming from (-1) means spawn a new starting item
  addSpawn :: DTrans -> DTrans
  addSpawn dtrans | IMap.member startIndex dtrans = dtrans
                  | otherwise = IMap.insert startIndex mempty dtrans

  indexToDFA :: Index -> DFA  -- used to seed the Trie from the NFA
  indexToDFA i = {-# SCC "nfaToDFA.indexToDFA" #-} makeDFA (ISet.singleton source) (qtToDT qtIn)
    where
      (QNFA {q_id = source,q_qt = qtIn}) = aQNFA!i
      qtToDT :: QT -> DT
      qtToDT (Testing {qt_test=wt, qt_dopas=dopas, qt_a=a, qt_b=b}) =
          Testing' { dt_test = wt
                   , dt_dopas = dopas
                   , dt_a = qtToDT a
                   , dt_b = qtToDT b }
      qtToDT (Simple {qt_win=w, qt_trans=t, qt_other=o}) =
        Simple' { dt_win = makeWinner
                , dt_trans = fmap qtransToDFA t
--                , dt_other = if IMap.null o then Just (newTransition $ IMap.singleton startIndex mempty) else Just (qtransToDFA o)}
                , dt_other = qtransToDFA o}
        where
          makeWinner :: IntMap {- Index -} Instructions --  (RunState ())
          makeWinner | noWin w = IMap.empty
                     | otherwise = IMap.singleton source (cleanWin w)

          qtransToDFA :: QTrans -> Transition
          qtransToDFA qtrans = {-# SCC "nfaToDFA.indexToDFA.qtransToDFA" #-}
                               newTransition dtrans
            where
              dtrans :: DTrans
              dtrans =IMap.fromDistinctAscList . mapSnd (IMap.singleton source) $ best
              best :: [(Index {- Destination -} ,(DoPa,Instructions))]
              best = pickQTrans aTagOp $ qtrans

  -- The DFA states are built up by merging the singleton ones converted from the NFA.
  -- Thus the "source" indices in the DTrans should not collide.
  mergeDFA :: DFA -> DFA -> DFA
  mergeDFA d1 d2 = {-# SCC "nfaToDFA.mergeDFA" #-} makeDFA i dt
    where
      i = d_id d1 `mappend` d_id d2
      dt = d_dt d1 `mergeDT` d_dt d2
      mergeDT,nestDT :: DT -> DT -> DT
      mergeDT (Simple' w1 t1 o1) (Simple' w2 t2 o2) = Simple' w t o
        where
          w = w1 `mappend` w2
          t = fuseDTrans -- t1 o1 t2 o2
          o = mergeDTrans o1 o2
          -- This is very much like mergeQTrans
          mergeDTrans :: Transition -> Transition -> Transition
          mergeDTrans (Transition {trans_how=dt1}) (Transition {trans_how=dt2}) = makeTransition dtrans
            where dtrans = IMap.unionWith IMap.union dt1 dt2
          -- This is very much like fuseQTrans
          fuseDTrans :: CharMap Transition
          fuseDTrans = CharMap (IMap.fromDistinctAscList (fuse l1 l2))
            where
              l1 = IMap.toAscList (unCharMap t1)
              l2 = IMap.toAscList (unCharMap t2)
              fuse :: [(IMap.Key, Transition)]
                   -> [(IMap.Key, Transition)]
                   -> [(IMap.Key, Transition)]
              fuse [] y = fmap (fmap (mergeDTrans o1)) y
              fuse x [] = fmap (fmap (mergeDTrans o2)) x
              fuse x@((xc,xa):xs) y@((yc,ya):ys) = 
                case compare xc yc of
                  LT -> (xc,mergeDTrans o2 xa) : fuse xs y
                  EQ -> (xc,mergeDTrans xa ya) : fuse xs ys
                  GT -> (yc,mergeDTrans o1 ya) : fuse x ys
      mergeDT dt1@(Testing' wt1 dopas1 a1 b1) dt2@(Testing' wt2 dopas2 a2 b2) =
        case compare wt1 wt2 of
          LT -> nestDT dt1 dt2
          EQ -> Testing' { dt_test = wt1
                         , dt_dopas = dopas1 `mappend` dopas2
                         , dt_a = mergeDT a1 a2
                         , dt_b = mergeDT b1 b2 }
          GT -> nestDT dt2 dt1
      mergeDT dt1@(Testing' {}) dt2 = nestDT dt1 dt2
      mergeDT dt1 dt2@(Testing' {}) = nestDT dt2 dt1
      nestDT dt1@(Testing' {dt_a=a,dt_b=b}) dt2 = dt1 { dt_a = mergeDT a dt2, dt_b = mergeDT b dt2 }
      nestDT _ _ = err "nestDT called on Simple -- cannot happen"

patternToRegex :: (Pattern,(GroupIndex, DoPa)) -> CompOption -> ExecOption -> Regex
patternToRegex pattern compOpt execOpt = nfaToDFA (patternToNFA compOpt pattern) compOpt execOpt

dfaMap :: DFA -> Data.Map.Map SetIndex DFA
dfaMap = seen (Data.Map.empty) where
  seen old d@(DFA {d_id=i,d_dt=dt}) =
    if i `Data.Map.member` old
      then old
      else let new = Data.Map.insert i d old
           in foldl' seen new (flattenDT dt)

-- Get all trans_many states
flattenDT :: DT -> [DFA]
flattenDT (Simple' {dt_trans=(CharMap mt),dt_other=o}) = concatMap (\d -> [trans_many d {-,trans_single d-}]) . (:) o . IMap.elems $ mt
flattenDT (Testing' {dt_a=a,dt_b=b}) = flattenDT a ++ flattenDT b

examineDFA :: Regex -> String
examineDFA (Regex {regex_dfa=dfa}) = unlines . (:) ("Number of reachable DFA states: "++show (length dfas)) . map show $ dfas
  where dfas = Data.Map.elems $ dfaMap dfa

{-

fillMap :: Tag -> IntMap (Position,Bool)
fillMap tag = IMap.fromDistinctAscList [(t,(-1,True)) | t <- [0..tag] ]

diffMap :: IntMap (Position,Bool) -> IntMap (Position,Bool) -> [(Index,(Position,Bool))]
diffMap old new = IMap.toList (IMap.differenceWith (\a b -> if a==b then Nothing else Just b) old new)

examineDFA :: (DFA,Index,Array Tag OP,Array GroupIndex [GroupInfo]) -> String
examineDFA (dfa,_,aTags,_) = unlines $ map (examineDFA' (snd . bounds $ aTags)) (Map.elems $ dfaMap dfa)

examineDFA' :: Tag -> DFA -> String
examineDFA' maxTag = showDFA (fillMap maxTag)

{-
instance Show DFA where
  show (DFA {d_id=i,d_dt=dt}) = "DFA {d_id = "++show (ISet.toList i)
                            ++"\n    ,d_dt = "++ show dt
                            ++"\n}"
-}
-- instance Show DT where show = showDT

showDFA :: IntMap (Position,Bool) -> DFA -> String
showDFA m (DFA {d_id=i,d_dt=dt}) = "DFA {d_id = "++show (ISet.toList i)
                               ++"\n    ,d_dt = "++ showDT m dt
                               ++"\n}"
-}



-- pick QTrans can be told the unique source and knows all the
-- destinations (hmm...along with qt_win)!  So if in ascending destination order the last source
-- is free to mutatate the old state.  If the QTrans has only one
-- entry then all we need to do is mutate that entry when making a
-- transition.
-- 
pickQTrans :: Array Tag OP -> QTrans -> [({-Destination-}Index,(DoPa,Instructions))]
pickQTrans op tr = mapSnd (bestTrans op) . IMap.toList $ tr

cleanWin :: WinTags -> Instructions
cleanWin = toInstructions

bestTrans :: Array Tag OP -> [TagCommand] -> (DoPa,Instructions)
bestTrans _ [] = err "bestTrans : There were no transition choose from!"
bestTrans aTagOP (f:fs) | null fs = canonical f
                        | otherwise = answer -- if null toDisplay then answer else trace toDisplay answer
 where
  answer = foldl' pick (canonical f) fs
  {- toDisplay | null fs = ""
               | otherwise = unlines $ "bestTrans" : show (answer) : "from among" : concatMap (\x -> [show x, show (toInstructions (snd x))]) (f:fs) -}
  canonical :: TagCommand -> (DoPa,Instructions)
  canonical (dopa,spec) = (dopa, toInstructions spec)
  pick :: (DoPa,Instructions) -> TagCommand -> (DoPa,Instructions)
  pick win@(dopa1,winI) (dopa2,spec) =
    let nextI = toInstructions spec
--    in case compareWith choose winPos nextPos of -- XXX 2009: add in enterOrbit information
    in case compareWith choose (toListing winI) (toListing nextI) of
         GT -> win
         LT -> (dopa2,nextI)
         EQ -> if dopa1 >= dopa2 then win else (dopa2,nextI) -- no deep reason not to just pick win

  toListing :: Instructions -> [(Tag,Action)]
  toListing (Instructions {newPos = nextPos}) = filter notReset nextPos
    where notReset (_,SetVal (-1)) = False
          notReset _ = True
{-
  toListing (Instructions {newPos = nextPos}) = mergeTagOrbit nextPos (filter snd nextFlags)

  mergeTagOrbit xx [] = xx
  mergeTagOrbit [] yy = yy
  mergeTagOrbit xx@(x:xs) yy@(y:ys) = 
    case compare (fst x) (fst y) of
      GT -> y : mergeTagOrbit xx ys
      LT -> x : mergeTagOrbit xs yy
      EQ -> x : mergeTagOrbit xs ys -- keep tag setting over orbit setting.
-}

  {-# INLINE choose #-}
  choose :: Maybe (Tag,Action) -> Maybe (Tag,Action) -> Ordering
  choose Nothing Nothing = EQ
  choose Nothing x = flipOrder (choose x Nothing)
  choose (Just (tag,_post)) Nothing =
    case aTagOP!tag of
      Maximize -> GT
      Minimize -> LT -- needed to choose best path inside nested * operators,
                    -- this needs a leading Minimize tag inside at least the parent * operator
      Ignore -> GT -- XXX this is a guess in analogy with Maximize for the end bit of a group
      Orbit -> LT -- trace ("choose LT! Just "++show tag++" < Nothing") LT -- 2009 XXX : comment out next line and use the Orbit instead
--      Orbit -> err $ "bestTrans.choose : Very Unexpeted Orbit in Just Nothing: "++show (tag,post,aTagOP,f:fs)
  choose (Just (tag,post1)) (Just (_,post2)) =
    case aTagOP!tag of
      Maximize -> order
      Minimize -> flipOrder order
      Ignore -> EQ
      Orbit -> EQ
--      Orbit -> err $ "bestTrans.choose : Very Unexpeted Orbit in Just Just: "++show (tag,(post1,post2),aTagOP,f:fs)
   where order = case (post1,post2) of
                   (SetPre,SetPre) -> EQ
                   (SetPost,SetPost) -> EQ
                   (SetPre,SetPost) -> LT
                   (SetPost,SetPre) -> GT
                   (SetVal v1,SetVal v2) -> compare v1 v2
                   _ -> err $ "bestTrans.compareWith.choose sees incomparable "++show (tag,post1,post2)


  {-# INLINE compareWith #-}
  compareWith :: (Ord x,Monoid a) => (Maybe (x,b) -> Maybe (x,c) -> a) -> [(x,b)] -> [(x,c)] -> a
  compareWith comp = cw where
    cw [] [] = comp Nothing Nothing
    cw xx@(x:xs) yy@(y:ys) =
      case compare (fst x) (fst y) of
        GT -> comp Nothing  (Just y) `mappend` cw xx ys
        EQ -> comp (Just x) (Just y) `mappend` cw xs ys
        LT -> comp (Just x) Nothing  `mappend` cw xs yy
    cw xx [] = foldr (\x rest -> comp (Just x) Nothing  `mappend` rest) mempty xx
    cw [] yy = foldr (\y rest -> comp Nothing  (Just y) `mappend` rest) mempty yy

                   
isDFAFrontAnchored :: Bool -> DFA -> Bool
isDFAFrontAnchored isMultiline = isDTFrontAnchored . d_dt
 where
  isDTFrontAnchored :: DT -> Bool
  isDTFrontAnchored (Simple' {}) = False
  isDTFrontAnchored (Testing' {dt_test=wt,dt_a=a,dt_b=b}) | isAnchorTest = isDTLosing b
                                                          | otherwise = isDTFrontAnchored a && isDTFrontAnchored b
   where
    -- Which tests are an anchor depends on if we are in multline mode or not. If not,
    -- both ^ and \` are anchors, if we are, then only \` is an anchor
    isAnchorTest
      | isMultiline = wt == Test_BOB
      | otherwise = wt == Test_BOB || wt == Test_BOL
    -- can DT never win or accept a character (when following trans_single)?
    isDTLosing :: DT -> Bool
    isDTLosing (Testing' {dt_a=a',dt_b=b'}) = isDTLosing a' && isDTLosing b'
    isDTLosing (Simple' {dt_win=w}) | not (IMap.null w) = False -- can win with 0 characters
    isDTLosing (Simple' {dt_trans=CharMap mt,dt_other=o}) =
      let ts = o : IMap.elems mt
      in all transLoses ts
     where
      transLoses :: Transition -> Bool
      transLoses (Transition {trans_single=dfa,trans_how=dtrans}) = isDTLose dfa || onlySpawns dtrans
       where
        isDTLose :: DFA -> Bool
        isDTLose dfa' = ISet.null (d_id dfa')
        onlySpawns :: DTrans -> Bool
        onlySpawns t = case IMap.elems t of
                         [m] -> IMap.null m
                         _ -> False

{- toInstructions -}

toInstructions :: TagList -> Instructions
toInstructions spec =
  let (p,o) = execState (assemble spec) (mempty,mempty)
  in Instructions { newPos = IMap.toList p
                  , newOrbits = if IMap.null o then Nothing
                                  else Just $ alterOrbits (IMap.toList o)
                  }

type CompileInstructions a = State
  ( IntMap Action -- 2009: change to SetPre | SetPost enum
  , IntMap AlterOrbit
  ) a

data AlterOrbit = AlterReset                        -- removing the Orbits record from the OrbitLog
                | AlterLeave                        -- set inOrbit to False
                | AlterModify { newInOrbit :: Bool   -- set inOrbit to the newInOrbit value
                              , freshOrbit :: Bool}  -- freshOrbit of True means to set getOrbits to mempty
                  deriving (Show)                   -- freshOrbit of False means try appending position or else Seq.empty

assemble :: TagList -> CompileInstructions ()
assemble = mapM_ oneInstruction where
  oneInstruction (tag,command) =
    case command of
      PreUpdate TagTask -> setPreTag tag
      PreUpdate ResetGroupStopTask -> resetGroupTag tag
      PreUpdate SetGroupStopTask -> setGroupTag tag
      PreUpdate ResetOrbitTask -> resetOrbit tag
      PreUpdate EnterOrbitTask -> enterOrbit tag
      PreUpdate LeaveOrbitTask -> leaveOrbit tag
      PostUpdate TagTask -> setPostTag tag
      PostUpdate ResetGroupStopTask -> resetGroupTag tag
      PostUpdate SetGroupStopTask -> setGroupTag tag
      _ -> err ("assemble : Weird orbit command: "++show (tag,command))

setPreTag :: Tag -> CompileInstructions ()
setPreTag = modifyPos SetPre

setPostTag :: Tag -> CompileInstructions ()
setPostTag = modifyPos SetPost

resetGroupTag :: Tag -> CompileInstructions ()
resetGroupTag = modifyPos (SetVal (-1))

setGroupTag :: Tag -> CompileInstructions ()
setGroupTag = modifyPos (SetVal 0)

-- The following is ten times more complicated than it ought to be.  Sorry, I was too new, and now
-- too busy to clean this up.

resetOrbit :: Tag -> CompileInstructions ()
resetOrbit tag = modifyPos (SetVal (-1)) tag >> modifyOrbit (IMap.insert tag AlterReset)

enterOrbit :: Tag -> CompileInstructions ()
enterOrbit tag = modifyPos (SetVal 0) tag >> modifyOrbit changeOrbit where
  changeOrbit = IMap.insertWith overwriteOrbit tag appendNewOrbit

  appendNewOrbit = AlterModify {newInOrbit = True, freshOrbit = False} -- try to append
  startNewOrbit  = AlterModify {newInOrbit = True, freshOrbit = True}  -- will start a new series

  overwriteOrbit _ AlterReset = startNewOrbit
  overwriteOrbit _ AlterLeave = startNewOrbit
  overwriteOrbit _ (AlterModify {newInOrbit = False}) = startNewOrbit
  overwriteOrbit _ (AlterModify {newInOrbit = True}) =
    err $ "enterOrbit: Cannot enterOrbit twice in a row: " ++ show tag

leaveOrbit :: Tag -> CompileInstructions ()
leaveOrbit tag = modifyOrbit escapeOrbit where
  escapeOrbit = IMap.insertWith setInOrbitFalse tag AlterLeave where
    setInOrbitFalse _ x@(AlterModify {}) = x {newInOrbit = False}
    setInOrbitFalse _ x = x

modifyPos :: Action -> Tag -> CompileInstructions ()
modifyPos todo tag = do
  (a,c) <- get
  let a' = IMap.insert tag todo a
  seq a' $ put (a',c)

modifyOrbit :: (IntMap AlterOrbit -> IntMap AlterOrbit) -> CompileInstructions ()
modifyOrbit f = do
  (a,c) <- get
  let c' = f c
  seq c' $ put (a,c')

----

alterOrbits :: [(Tag,AlterOrbit)] -> (Position -> OrbitTransformer)
alterOrbits x = let items = map alterOrbit x
                in (\ pos m -> foldl (flip ($)) m (map ($ pos) items))

alterOrbit :: (Tag,AlterOrbit) -> (Position -> OrbitTransformer)

alterOrbit (tag,AlterModify {newInOrbit = inOrbit',freshOrbit = True}) =
  (\ pos m -> IMap.insert tag (Orbits { inOrbit = inOrbit'
                                     , basePos = pos
                                     , ordinal = Nothing
                                     , getOrbits = mempty}) m)

alterOrbit (tag,AlterModify {newInOrbit = inOrbit',freshOrbit = False}) =
  (\ pos m -> IMap.insertWithKey (updateOrbit pos) tag (newOrbit pos) m) where
  newOrbit pos = Orbits { inOrbit = inOrbit'
                        , basePos = pos
                        , ordinal = Nothing
                        , getOrbits = Mon.mempty}
  updateOrbit pos _tag new old | inOrbit old = old { inOrbit = inOrbit'
                                                   , getOrbits = getOrbits old |> pos }
                               | otherwise = new

alterOrbit (tag,AlterReset) = (\ _ m -> IMap.delete tag m)

alterOrbit (tag,AlterLeave) = (\ _ m -> case IMap.lookup tag m of
                                         Nothing -> m
                                         Just x -> IMap.insert tag (x {inOrbit=False}) m)
