{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ImportQualifiedPost #-}

module FirstOrder where

import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe (fromJust, isNothing)
import Test.QuickCheck hiding (Fun, (===))
import Utils
import qualified Propositional as Prop

type VarName = String

type FunName = String

type RelName = String

data GenTerm a = Var a | Fun FunName [GenTerm a] deriving (Eq, Show)

type Term = GenTerm VarName

variables :: Term -> [VarName]
variables (Var x) = [x]
variables (Fun _ ts) = nub $ concatMap variables ts

type FunInt a = FunName -> [a] -> a

type Env a = VarName -> a

evalTerm :: FunInt a -> Env a -> Term -> a
evalTerm _ rho (Var x) = rho x
evalTerm int rho (Fun f ts) = int f $ map (evalTerm int rho) ts

data Formula
  = F
  | T
  | Rel RelName [Term]
  | Not Formula
  | Or Formula Formula
  | And Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | Exists VarName Formula
  | Forall VarName Formula
  deriving (Eq, Show)

-- type Formula = GenFormula VarName

infixr 8 /\, ∧

(/\) = And

(∧) = And

infixr 5 \/, ∨, -->

(\/) = Or

(∨) = Or

(-->) = Implies

infixr 4 <-->

(<-->) = Iff

infix 9 ===, =/=

(===), (=/=) :: Term -> Term -> Formula
u === v = Rel "=" [u, v]
u =/= v = Not (u === v)

type Substitution = Env Term

-- apply a substitution on all free variables
apply :: Substitution -> Formula -> Formula
apply _ F = F
apply _ T = T
apply f (Rel r ts) = Rel r $ map (evalTerm Fun f) ts
apply f (Not phi) = Not (apply f phi)
apply f (Or phi psi) = Or (apply f phi) (apply f psi)
apply f (And phi psi) = And (apply f phi) (apply f psi)
apply f (Implies phi psi) = Implies (apply f phi) (apply f psi)
apply f (Iff phi psi) = Iff (apply f phi) (apply f psi)
apply f (Exists x phi) = Exists x (apply (update f x (Var x)) phi)
apply f (Forall x phi) = Forall x (apply (update f x (Var x)) phi)

instance {-# OVERLAPPING #-} Arbitrary VarName where
  arbitrary = elements ["x", "y", "z", "t"]

instance Arbitrary Term where
  arbitrary = resize 8 $ sized f
    where
      f size
        | size == 0 || size == 1 = do
            x <- arbitrary
            return $ Var x
        | otherwise = frequency [(1, go sizes) | sizes <- catalan size]
        where
          go sizes = do
            ts <- sequence $ map f sizes
            return $ Fun "f" ts

instance Arbitrary Formula where
  arbitrary = resize 30 $ sized f
    where
      f 0 = do
        ts <- arbitrary
        return $ Rel "R" ts
      f size =
        frequency
          [ (1, liftM Not (f (size - 1))),
            ( 4,
              do
                size' <- choose (0, size - 1)
                conn <- oneof $ map return [And, Or, Implies, Iff]
                left <- f $ size'
                right <- f $ size - size' - 1
                return $ conn left right
            ),
            ( 5,
              do
                conn <- oneof $ map return [Exists, Forall]
                phi <- f $ size - 1
                x <- arbitrary
                return $ conn x phi
            )
          ]

  shrink (Not varphi) = [varphi]
  shrink (Or varphi psi) = [varphi, psi]
  shrink (And varphi psi) = [varphi, psi]
  shrink (Implies varphi psi) = [varphi, psi]
  shrink (Iff varphi psi) = [varphi, psi]
  shrink (Exists _ varphi) = [varphi]
  shrink (Forall _ varphi) = [varphi]
  shrink _ = []

type SATSolver = Formula -> Bool

type FOProver = Formula -> Bool

-- find all free variables
fv :: Formula -> [VarName]
fv T = []
fv F = []
fv (Rel _ ts) = variables (Fun "dummy" ts)
fv (Not phi) = fv phi
fv (And phi psi) = nub $ fv phi ++ fv psi
fv (Or phi psi) = nub $ fv phi ++ fv psi
fv (Implies phi psi) = nub $ fv phi ++ fv psi
fv (Iff phi psi) = nub $ fv phi ++ fv psi
fv (Exists x phi) = delete x $ fv phi
fv (Forall x phi) = delete x $ fv phi

vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = variables (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = nub $ vars phi ++ vars psi
vars (Or phi psi) = nub $ vars phi ++ vars psi
vars (Implies phi psi) = nub $ vars phi ++ vars psi
vars (Iff phi psi) = nub $ vars phi ++ vars psi
vars (Exists x phi) = nub $ x : vars phi
vars (Forall x phi) = nub $ x : vars phi

variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0 ..]]

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = x `notElem` vars phi

freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [y | y <- variants x, y `freshIn` phi]

renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z
renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename _ _ T = T
rename _ _ F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where
    go [] = phi
    go (x : xs) = Forall x $ go xs

specify :: Formula -> Formula
specify (Forall _ x) = specify x
specify x = x

prop_generalise = generalise (Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])) == Forall "y" (Forall "z" (Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])))

checkGeneralise = quickCheck prop_generalise

fresh :: Formula -> Formula
fresh phi = evalState (go phi) $ fv phi
  where
    go :: Formula -> State [VarName] Formula
    go T = return T
    go F = return F
    go phi@(Rel _ _) = return phi
    go (Not phi) = fmap Not (go phi)
    go (And phi psi) = liftM2 And (go phi) (go psi)
    go (Or phi psi) = liftM2 Or (go phi) (go psi)
    go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
    go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
    go (Forall x phi) = go2 Forall x phi
    go (Exists x phi) = go2 Exists x phi

    go2 quantifier x phi =
      do
        xs <- get
        let y = head [y | y <- variants x, y `notElem` xs]
        let psi = rename x y phi
        put $ y : xs
        quantifier y <$> go psi

isNnf :: Formula -> Bool
isNnf T = True
isNnf F = True
isNnf (Rel _ _) = True
isNnf (Not (Rel _ _)) = True
isNnf (And phi psi) = isNnf phi && isNnf psi
isNnf (Or phi psi) = isNnf phi && isNnf psi
isNnf (Implies phi psi) = False
isNnf (Iff phi psi) = False
isNnf (Not _) = False
isNnf (Exists _ phi) = isNnf phi
isNnf (Forall _ phi) = isNnf phi

nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf r@(Rel _ _) = r
nnf (Not φ) = case nnf φ of
  T -> F
  F -> T
  Not φ' -> φ'
  Or φ' ψ' -> And (nnf (Not φ')) (nnf (Not ψ'))
  And φ' ψ' -> Or (nnf (Not φ')) (nnf (Not ψ'))
  Exists x φ' -> Forall x (nnf (Not φ'))
  Forall x φ' -> Exists x (nnf (Not φ'))
  φ' -> Not φ'
nnf (And φ ψ) = And (nnf φ) (nnf ψ)
nnf (Or φ ψ) = Or (nnf φ) (nnf ψ)
nnf (Implies φ ψ) = Or (nnf (Not φ)) (nnf ψ)
nnf (Iff φ ψ) = Or (nnf (And φ ψ)) (nnf (And (Not φ) (Not ψ)))
nnf (Exists x φ) = Exists x (nnf φ)
nnf (Forall x φ) = Forall x (nnf φ)

nnfProp :: Formula -> Bool
nnfProp phi = isNnf (nnf phi)

checkNnf = quickCheck nnfProp

isPnf :: Formula -> Bool
isPnf (Forall _ phi) = isPnf phi
isPnf (Exists _ phi) = isPnf phi
isPnf phi = qf phi

qf :: Formula -> Bool
qf (Rel _ _) = True
qf (Not phi) = qf phi
qf (And phi psi) = qf phi && qf psi
qf (Or phi psi) = qf phi && qf psi
qf (Implies phi psi) = qf phi && qf psi
qf (Iff phi psi) = qf phi && qf psi
qf _ = False

pnf :: Formula -> Formula
pnf = go . nnf
  where
    go T = T
    go F = F
    go r@(Rel _ _) = r
    go n@(Not _) = n
    go (Exists x φ) = Exists x (go φ)
    go (Forall x φ) = Forall x (go φ)
    go (And (Forall x φ) (Forall y ψ)) = go $ buildFreshAndForall φ x ψ y
    go (And (Forall x φ) (Exists y ψ)) = let (formula, left, right) = buildFreshFormula And φ x ψ (Just y) in Forall left (Exists (fromJust right) (go formula))
    go (And (Exists x φ) (Forall y ψ)) = let (formula, left, right) = buildFreshFormula And φ x ψ (Just y) in Exists left (Forall (fromJust right) (go formula))
    go (And (Exists x φ) (Exists y ψ)) = let (formula, left, right) = buildFreshFormula And φ x ψ (Just y) in Exists left (Exists (fromJust right) (go formula))
    go (And (Exists x φ) ψ) = let (formula, left, _) = buildFreshFormula And φ x ψ Nothing in Exists left (go formula)
    go (And (Forall x φ) ψ) = let (formula, left, _) = buildFreshFormula And φ x ψ Nothing in Forall left (go formula)
    go (And φ (Exists y ψ)) = let (formula, left, _) = buildFreshFormula And ψ y φ Nothing in Exists left (go formula)
    go (And φ (Forall y ψ)) = let (formula, left, _) = buildFreshFormula And ψ y φ Nothing in Forall left (go formula)
    go (And φ ψ) = let (left, right) = (go φ, go ψ) in if isQuantifier left || isQuantifier right then go $ And left right else And left right
    go (Or (Exists x φ) (Exists y ψ)) = go $ buildFreshOrExists φ x ψ y
    go (Or (Forall x φ) (Exists y ψ)) = let (formula, left, right) = buildFreshFormula Or φ x ψ (Just y) in Forall left (Exists (fromJust right) (go formula))
    go (Or (Exists x φ) (Forall y ψ)) = let (formula, left, right) = buildFreshFormula Or φ x ψ (Just y) in Exists left (Forall (fromJust right) (go formula))
    go (Or (Forall x φ) (Forall y ψ)) = let (formula, left, right) = buildFreshFormula Or φ x ψ (Just y) in Forall left (Forall (fromJust right) (go formula))
    go (Or (Exists x φ) ψ) = let (formula, left, _) = buildFreshFormula Or φ x ψ Nothing in Exists left (go formula)
    go (Or (Forall x φ) ψ) = let (formula, left, _) = buildFreshFormula Or φ x ψ Nothing in Forall left (go formula)
    go (Or φ (Exists y ψ)) = let (formula, left, _) = buildFreshFormula Or ψ y φ Nothing in Exists left (go formula)
    go (Or φ (Forall y ψ)) = let (formula, left, _) = buildFreshFormula Or ψ y φ Nothing in Forall left (go formula)
    go (Or φ ψ) = let (left, right) = (go φ, go ψ) in if isQuantifier left || isQuantifier right then go $ Or left right else Or left right

isQuantifier :: Formula -> Bool
isQuantifier (Exists _ _) = True
isQuantifier (Forall _ _) = True
isQuantifier _ = False

buildFreshAndForall :: Formula -> VarName -> Formula -> VarName -> Formula
buildFreshAndForall φ x ψ y = Forall freshVariantInBoth (And (rename x freshVariantInBoth φ) (rename y freshVariantInBoth ψ))
  where
    freshVariantInBoth = freshVariant x (And φ ψ)

buildFreshOrExists :: Formula -> VarName -> Formula -> VarName -> Formula
buildFreshOrExists φ x ψ y = Exists freshVariantInBoth (Or (rename x freshVariantInBoth φ) (rename y freshVariantInBoth ψ))
  where
    freshVariantInBoth = freshVariant x (And φ ψ)

buildFreshFormula con φ x ψ y = (con left right, freshLeft, freshRight)
  where
    xFree = freshIn x (And φ ψ)
    freshLeft = if xFree then x else freshVariant x (And φ ψ)
    left = if xFree then φ else rename x freshLeft φ
    yFree = isNothing y || freshIn (fromJust y) (And left ψ)
    freshRight = if yFree then y else Just $ freshVariant (fromJust y) (And left ψ)
    right = if yFree then ψ else rename (fromJust y) (fromJust freshRight) ψ

pnfProp = isPnf . pnf
checkPnf = quickCheck pnfProp

skolemiseInner :: Formula -> [VarName] -> Formula
skolemiseInner (And p q) boundVars = And (skolemiseInner p boundVars) (skolemiseInner q boundVars)
skolemiseInner (Or p q) boundVars = Or (skolemiseInner p boundVars) (skolemiseInner q boundVars)
skolemiseInner (Forall x p) boundVars = Forall x (skolemiseInner p (boundVars ++ [x]))
skolemiseInner (Exists x p) boundVars = skolemiseInner (apply (\y -> if y == x then Fun x (map Var boundVars) else Var y) p) boundVars
skolemiseInner f _ = f

skolemise :: Formula -> Formula
skolemise = pnf . flip skolemiseInner [] . fresh . nnf . generalise

prop_skolemise = skolemise (Forall "x" $ Exists "y" $ Rel "P" [Var "x", Var "y"] /\ Rel "Q" [Var "y"]) == Forall "x" (And (Rel "P" [Var "x", Fun "y" [Var "x"]]) (Rel "Q" [Fun "y" [Var "x"]]))

type Arity = Int
type Signature = [(FunName, Arity)]

sigT :: Term -> Signature
sigT (Var _) = []
sigT (Fun f ts) = nub $ (f, length ts) : concatMap sigT ts

sig :: Formula -> Signature
sig T = []
sig F = []
sig (Rel r ts) = concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = nub $ sig phi ++ sig psi
sig (Or phi psi) = nub $ sig phi ++ sig psi
sig (Implies phi psi) = nub $ sig phi ++ sig psi
sig (Iff phi psi) = nub $ sig phi ++ sig psi
sig (Exists _ phi) = sig phi
sig (Forall _ phi) = sig phi

groundTerms :: Signature -> [Term]
groundTerms s = go 0 [] [] []
  where
    constants = let result = filter (\x -> snd x == 0) s in if null result then [("c", 0)] else result
    functions = filter (\x -> snd x > 0) s
    go :: Int -> [Term] -> [Term] -> [Term] -> [Term]
    go 0 [] [] [] = let new = groundTermsInner 0 [] [] [] in if null functions then new else new ++ go 1 new new []
    go n tillNow current previous = let new = groundTermsInner n tillNow current previous in new ++ go (n + 1) (tillNow ++ new) new current
    groundTermsInner :: Int -> [Term] -> [Term] -> [Term] -> [Term]
    groundTermsInner n tillNow current previous
      | n == 0 = map (\(name, _) -> Fun name []) constants
      | otherwise = concatMap (\(name, arity) -> map (Fun name) (buildFnArguments arity tillNow current previous)) functions
    buildFnArguments :: Int -> [Term] -> [Term] -> [Term] -> [[Term]]
    buildFnArguments 0 _ _ _ = []
    buildFnArguments n tillNow current previous = goBuild n
      where
        goBuild k
          | k == n = [x ++ [y] | x <- replicateM (n - 1) previous, y <- current]  ++ goBuild (k - 1)
          | k == 0 = []
          | otherwise = [x ++ y:z | x <- replicateM (k - 1) previous, y <- current, z <- replicateM (n - k) tillNow]  ++ goBuild (k - 1)

groundFormulas :: Formula -> [Formula]
groundFormulas f = map (`apply` f) fns
  where
    signature = sig f
    terms = groundTerms signature
    freeVariables = fv f
    fns = functions freeVariables terms

satisfiable :: Formula -> Bool
satisfiable f = all Prop.dp $ scanl (\acc x -> acc ++ Prop.ecnf (mapFormula x)) [] (groundFormulas f)

mapFormula :: Formula -> Prop.Formula
mapFormula F = Prop.F
mapFormula T = Prop.T
mapFormula (Rel name lTerms) = Prop.Prop (name ++ "_" ++ show lTerms)
mapFormula (Not f) = Prop.Not (mapFormula f)
mapFormula (Or l r) = Prop.Or (mapFormula l) (mapFormula r)
mapFormula (And l r) = Prop.And (mapFormula l) (mapFormula r)

tautology :: Formula -> Bool
tautology = not . satisfiable . specify . skolemise . Not