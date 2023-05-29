{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}
module Propositional where

import Data.List
import Control.Monad
import Test.QuickCheck
import System.IO.Unsafe
import Data.Maybe (fromJust)
import Utils
import qualified Data.Set as Set

type PropName = String

fresh :: [PropName] -> PropName
fresh vars = head $ filter (not . (`elem` vars)) $ map (("p"++) . show) [0..]

data Formula =
      T
    | F
    | Prop PropName
    | Not Formula
    | And Formula Formula
    | Or Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    deriving (Eq, Show)

p, q, r, s, t :: Formula

p = Prop "p"
q = Prop "q"
r = Prop "r"
s = Prop "s"
t = Prop "t"

infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, ==>
(\/) = Or
(∨) = Or -- input with "\or"
(==>) = Implies

infixr 4 <==>, ⇔
(<==>) = Iff
(⇔) = Iff -- input with "\lr"

instance Arbitrary Formula where
    arbitrary = sized f where

      f 0 = oneof $ map return $ [p, q, r, s, t] ++ [T, F]

      f size = frequency [
        (1, liftM Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]

    shrink (Not φ) = [φ]
    shrink (Or φ ψ) = [φ, ψ]
    shrink (And φ ψ) = [φ, ψ]
    shrink (Implies φ ψ) = [φ, ψ]
    shrink (Iff φ ψ) = [φ, ψ]
    shrink _ = []

type Valuation = PropName -> Bool

eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Prop p) ρ = ρ p
eval (Not φ) ρ = not (eval φ ρ)
eval (And φ ψ) ρ = (eval φ ρ) && (eval ψ ρ)
eval (Or φ ψ) ρ = (eval φ ρ) || (eval ψ ρ)
eval (Implies φ ψ) ρ = not (eval φ ρ) || (eval ψ ρ)
eval (Iff φ ψ) ρ = (eval φ ρ == eval ψ ρ)

variables :: Formula -> [PropName]
variables = nub . go where
  go T = []
  go F = []
  go (Prop p) = [p]
  go (Not φ) = go φ
  go (And φ ψ) = go φ ++ go ψ
  go (Or φ ψ) = go φ ++ go ψ
  go (Implies φ ψ) = go φ ++ go ψ
  go (Iff φ ψ) = go φ ++ go ψ

valuations :: [PropName] -> [Valuation]
valuations [] = [undefined]
valuations (x : xs) = concat [[update ϱ x True, update ϱ x False] | ϱ <- valuations xs]

type SATSolver = Formula -> Bool

satisfiable :: SATSolver
satisfiable φ = or [eval φ ϱ | ϱ <- valuations (variables φ)]

tautology :: Formula -> Bool
tautology φ = and [eval φ ρ | ρ <- valuations (variables φ)]

nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf r@(Prop p) = r
nnf (Not phi) = case nnf phi of
  T -> F
  F -> T
  Not phi' -> phi'
  Or phi' psi' -> And (nnf (Not phi')) (nnf (Not psi'))
  And phi' psi' -> Or (nnf (Not phi')) (nnf (Not psi'))
  phi' -> Not phi'
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = Or (nnf (Not phi)) (nnf psi)
nnf (Iff phi psi) = Or (nnf (And phi psi)) (nnf (And (Not phi) (Not psi)))

data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

type CNFClause = [Literal]
type CNF = [CNFClause]

cnf2formula :: CNF -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
  go [] = F
  go ls = foldr1 Or (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)

positive_literals :: CNFClause -> [PropName]
positive_literals ls = nub [p | Pos p <- ls]

negative_literals :: CNFClause -> [PropName]
negative_literals ls = nub [p | Neg p <- ls]

literals :: [Literal] -> [PropName]
literals ls = nub $ positive_literals ls ++ negative_literals ls

cnf :: Formula -> CNF
cnf = go . nnf where
  go T = []
  go F = [[]]
  go (Prop p) = [[Pos p]]
  go (Not (Prop p)) = [[Neg p]]
  go (φ `And` ψ) = go φ ++ go ψ
  go (φ `Or` ψ) = [as ++ bs | as <- go φ, bs <- go ψ]

test_cnf :: Formula -> Bool
test_cnf φ = tautology $ φ ⇔ (cnf2formula (cnf φ))

-- >>> quickCheckWith (stdArgs {maxSize = 18}) test_cnf

equi_satisfiable :: Formula -> Formula -> Bool
equi_satisfiable φ ψ = satisfiable φ == satisfiable ψ

ecnf :: Formula -> CNF
ecnf φ = let (cnf1, rep, _) = ecnfGo φ [] in (cnf rep ++ cnf1)

ecnfGo :: Formula -> [PropName] -> (CNF, Formula, [PropName])
ecnfGo T props = ([], T, props)
ecnfGo F props = ([], F, props)
ecnfGo (And φ ψ) props = ecnfGoCon And φ ψ props
ecnfGo (Or φ ψ) props = ecnfGoCon Or φ ψ props
ecnfGo (Implies φ ψ) props = ecnfGoCon Implies φ ψ props
ecnfGo (Iff φ ψ) props = ecnfGoCon Iff φ ψ props
ecnfGo (Prop p) props = ([], Prop p, p : props)
ecnfGo (Not φ) props =
  let (cnf1, rep1, props1) = ecnfGo φ props in
    (cnf1, Not rep1, props1)

ecnfGoCon :: (Formula -> Formula -> Formula)
     -> Formula -> Formula -> [PropName] -> ([CNFClause], Formula, [PropName])
ecnfGoCon con φ ψ props =
  let (cnf1, rep1, props1) = ecnfGo φ props in
  let (cnf2, rep2, props2) = ecnfGo ψ props1 in
  let freshProp = fresh props2 in
    (cnf1 ++ cnf2 ++ cnf ((Prop freshProp) `Iff` (con rep1 rep2)),
     Prop freshProp,
     freshProp : props2)

prop_ecnf :: Formula -> Property
prop_ecnf phi =
  within 10000000 $
  counterexample ("Formula: " ++ show phi) $
  equi_satisfiable phi (cnf2formula $ ecnf phi)

checkEcnf = quickCheckWith (stdArgs {maxSize = 10}) prop_ecnf

isPos (Pos _) = True
isPos (Neg _) = False

getLiteral (Pos x) = x
getLiteral (Neg x) = x

removeTautologies :: CNF -> CNF
removeTautologies = filter (\y -> not (any (\(a, b) -> isPos a /= isPos b && getLiteral a == getLiteral b) $ [(a1, a2) | a1 <- y, a2 <- y]))

oneLiteral :: CNF -> CNF
oneLiteral cnf =
  case anyOneLiteral cnf of
    Just p -> let result = map (`mapL` p) cnf in
                if Nothing `elem` result
                  then [[]]
                  else oneLiteral $ filter (not . null) $ map fromJust result
    Nothing -> cnf
  where
    mapL :: [Literal] -> Literal -> Maybe [Literal]
    mapL [] _ = Just []
    mapL elems y
      | y `elem` elems = Just []
      | otherwise = let filteredElems = filtered elems y in
        if null filteredElems
          then Nothing
          else Just filteredElems

    filtered :: [Literal] -> Literal -> [Literal]
    filtered elems y = filter (\x -> isPos x == isPos y || getLiteral x /= getLiteral y) elems

anyOneLiteral :: CNF -> Maybe Literal
anyOneLiteral cnf = fmap head (find (\x -> case x of {[_] -> True; _ -> False}) cnf)

prop_one_literal :: Bool
prop_one_literal =
  oneLiteral
    [[Pos "p"], [Pos "p", Pos "q", Pos "p", Pos "r"], [Neg "q", Pos "r", Neg "p", Neg "r", Neg "p"], [Neg "q", Neg "p"], [Pos "q", Pos "r", Pos "s"], [Neg "p", Pos "p"]] ==
    [[Pos "r",Pos "s"]] &&
  oneLiteral
    [[Pos "p"],[Pos "p1"],[Neg "p",Pos "q"],[Pos "p1",Pos "p0"],[Pos "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "q0",Neg "p"],[Neg "s",Neg "p",Pos "p0"]] ==
    [[Neg "p0",Pos "s"],[Neg "s",Pos "p0"]] &&
  oneLiteral
    [[Pos "q"],[Pos "p0"],[Neg "p0",Pos "s"],[Neg "p0"]] ==
    [[]]

-- >>> quickCheck prop_one_literal

affirmativeNegative :: CNF -> CNF
affirmativeNegative cnf = let result = filter (not . any (\x -> getLiteral x `elem` holdingProps)) cnf in if finished then result else affirmativeNegative result
  where
  flattened = concat cnf
  allLiterals = Set.fromList flattened
  allProps = Set.map getLiteral allLiterals
  notHoldingProps = Set.map (\(x, _) -> getLiteral x)
                    $ Set.filter (\(x, y) -> getLiteral x == getLiteral y && isPos x /= isPos y)
                    $ Set.cartesianProduct allLiterals allLiterals
  holdingProps = Set.difference allProps notHoldingProps
  finished = null holdingProps


prop_affirmative_negative :: Bool
prop_affirmative_negative =
  affirmativeNegative
    [[Neg "p2",Pos "p"],[Neg "p2",Pos "p1"],[Neg "p",Neg "p1",Neg "p2"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
    [[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] &&
  affirmativeNegative
    [[Pos "p", Pos "q"], [Pos "p", Neg "q"]] ==
    []

check_prop_affirmative_negative = quickCheck prop_affirmative_negative

resolution :: CNF -> CNF
resolution [] = []
resolution [[]] = [[]]
resolution cnf = [nub $ x ++ y | x <- clausesWithPositiveMapped, y <- clausesWithNegativeMapped] ++ remainingClauses
  where
    propToConsider = getLiteral $ head $ head cnf
    clausesWithPositive = filter (any (\y -> isPos y && getLiteral y == propToConsider)) cnf
    clausesWithPositiveMapped = map (filter (\y -> getLiteral y /= propToConsider)) clausesWithPositive
    clausesWithNegative = filter (any (\y -> not (isPos y) && getLiteral y == propToConsider)) cnf
    clausesWithNegativeMapped = map (filter (\y -> getLiteral y /= propToConsider)) clausesWithNegative
    remainingClauses = (cnf \\ clausesWithPositive) \\ clausesWithNegative

prop_resolution :: Bool
prop_resolution = resolution [[Pos "p", Pos "q"],[Neg "p", Neg "q"]] == [[Pos "q", Neg "q"]]

dp :: CNF -> Bool
dp [] = True
dp [[]] = False
dp cnf 
  | [] `elem` cnf = False
  | otherwise = dp resolutionApplied
    where
      simplified = nub . map nub $ cnf
      tautologiesRemoved = removeTautologies simplified
      oneLiteralApplied = oneLiteral tautologiesRemoved
      affirmativeNegativeApplied = affirmativeNegative oneLiteralApplied
      resolutionApplied = resolution affirmativeNegativeApplied

sat_DP :: SATSolver
sat_DP form = dp cnf where
  cnf = ecnf form

prop_DP :: Formula -> Bool
prop_DP φ = sat_DP φ == satisfiable φ

checkPropDp = quickCheckWith (stdArgs {maxSize = 20}) prop_DP
