{-# LANGUAGE PatternGuards #-}

module Main where

-- This is a revision exercise for the "Models of Computation" course at Imperial College London.

-- It implements β-reduction, Church numerals and addition in Lambda Calculus.

-- You will recognize from the lecture:

--   * data Lamba -- the λ-term definition
--   * fw         -- free variables
--   * substitute -- variable substitution
--   * nf         -- calculating the β-Normal Form
--   * num / nat  -- converting numbers to Church numerals and back
--   * add        -- A lambda expression for computing the sum of two Church numerals

-- If you run this program ("runhaskell lambdanumbers.hs" or "main" from ghci),
-- you will see a simple adding calculator that asks you for numbers
-- and shows the lambda evaluation steps.

-- Niklas Hambüchen


-- License: MIT (you can modify and redistribute this as you wish).

import Prelude hiding ((.), (^^))
import Data.Char
import Data.List
import System.IO
import Debug.Trace


-- Change . to $ so that we can use it in lambda terms, use `compose` instead
infixr 9 `compose`
infixr 0 .
compose f g x = f (g x)
a . b         = a $ b


-- Variables we can use in lambda terms
data Var = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
           deriving (Eq, Show, Enum)

-- THE definition
data Lambda = Var Var | Def Var Lambda | App Lambda Lambda
              deriving (Show, Eq)

-- USAGE:
--   * In lambda abstractions, use CAPITAL letters
--   * In lambda bodies, use lowercase letters
--   * You can use the dot as expected
--   * Example: λ X . x


-- Variable shortcuts
[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z] = map Var [A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z]

-- Definition and application shortcuts
def2 x y   t = Def x (Def y t)
def3 x y z t = Def x (Def y (Def z t))
app  x y   = App x y
infixl 7 `app`                  -- Application is left-associative
app2 x y z = x `app` y `app` z  -- app2 x y z = App (App x y) z

-- Lambda shortcuts
λ = Def; λ2 = def2; λ3 = def3


-- Lambda pretty-printing, showing only necessary brackets
showVar x = [toLower (head (show x))]

pretty (Def x l) = "λ" ++ showVar x ++ "." ++ prettyRec l  -- no brackets for outermost lambda
pretty l         = prettyRec l

prettyRec l = case l of
    Var x               -> showVar x
    Def x l'            -> "(λ" ++ showVar x ++ "." ++ prettyRec l' ++ ")"
    App l1 l2@(App _ _) -> prettyRec l1 ++ "(" ++ prettyRec l2 ++ ")"      -- brackets as application is right-associative
    App l1 l2           -> prettyRec l1 ++ " " ++ prettyRec l2


-- Finding free variables
fw :: Lambda -> [Var]
fw l = case l of
    Var x   -> [x]
    Def _ m -> fw m
    App m n -> fw m ++ fw n

-- Choosing unused variables
varNotIn :: [Var] -> Var
varNotIn vars = case [(A)..Z] \\ vars of
    []    -> error "ran out of free variables"
    (a:_) -> a


-- Returns the contents of Left x or Right x, no matter what it is.
whatever :: Either c c -> c
whatever = either id id


-- N[M/x]: replaces all occurrences of variable x in n by m
substitute :: Lambda -> Lambda -> Var -> Lambda
substitute n m x = debug "substitute" (n,m,x) $ case n of
    Var y | x == y    -> m
    Var y             -> Var y
    Def y n' | x == y -> Def y n'  -- "bind protection"
                         -- TODO check slide 10: forces variable y to be replaced when it doesn't need to
                         --                      z ∈ FV (M) ∪ FV (N')       ∪ {x}
                         -- should probably be:  z ∈ FV (M) ∪ FV (N' - {y}) ∪ {x}
    Def y n'          -> let z = if y `notElem` fw m then y
                                                     else varNotIn (fw n' ++ fw m ++ [x])
                          in Def z (substitute (substitute n' (Var z) y) m x)
    App n1 n2         -> App (substitute n1 m x) (substitute n2 m x)


-- Normal form β-reduction
nf :: Lambda -> Lambda
nf l = whatever $ reduceAsFarAsPossible l
    where
        -- Applies reduction step until the normal form is reached (nontermination if there is none)
        reduceAsFarAsPossible l = nf1 l >>= reduceAsFarAsPossible

-- Performs one β-reduction step
nf1 :: Lambda -> Either Lambda Lambda
nf1 l = debug "nf1" l $ case l of
    Var x                       -> Left $ Var x              -- TODO check missing in slides?
    App (Def x m) n             -> Right $ substitute m n x  -- outermost
    App m n | Right m' <- nf1 m -> Right $ App m' n          -- leftmost
    App m n | Right n' <- nf1 n -> Right $ App m n'
    Def x m | Right m' <- nf1 m -> Right $ Def x m'
    x                           -> Left x                    -- No reduction possible


-- Numbers to Church numerals
num :: Int -> Lambda
num 0 = λ2 F X . x
num 1 = λ2 F X . App f x
num 2 = λ2 F X . App f (App f x)
num n = λ2 F X . (f ^^ n) x
    where
        f ^^ n = foldl1 compose (replicate n (App f))

-- Church numerals back to numbers
nat :: Lambda -> Int
nat (Def f (Def x chain)) = count 0 f x chain
    where
        count n _ x (Var base)                | x == base    = n
                                              | otherwise    = error $ "Invalid Church numeral: innermost var is not the zero variable given in the second outermost lamdba"
        count n f x (App (Var succVar) chain) | f == succVar = count (n+1) f x chain
                                              | otherwise    = error $ "Invalid Church numeral: successor function variable the one given in the outermost lambda"
        count _ _ _ l                                        = error $ "Invalid Church numeral: " ++ show l ++ " should only contain applications of " ++ show f ++ " and " ++ show x ++ " as a zero variable"
nat l = error $ "Invalid Church numeral: " ++ show l ++ " should start with a lambda abstraction describing successor function and zero variable"


-- Addition of Church numerals in Lambda Calculus. Usage: "add `app` num1 `app` num2"
add :: Lambda
add = λ2 A B . λ2 F X . (app a f) `app` (app2 b f x)


-- Simple example adding program using lambda calculus
runCalculator :: (Lambda -> String) -> IO ()
runCalculator showLambda = do

    firstNum  <- askSummand "first"
    secondNum <- askSummand "second"

    let churchSum = add `app` firstNum `app` secondNum

    _ <- putStrLn "Press enter to show beta reduction steps:" >> getLine
    printEvalTrace churchSum

    putStrLn $ "as natural number: " ++ show (nat (nf churchSum))

    where
        askSummand desc = do
            putStr $ "Enter the " ++ desc ++ " summand: "
            int <- read `fmap` getLine
            printChurch int
            return (num int)
        printChurch n = putStrLn $ " -> " ++ showLambda (num n) ++ "\n"
        printEvalTrace l = case nf1 l of
            Left  _       -> putStrLn "    beta-reduced.\n"
            Right reduced -> putStrLn (" -> " ++ showLambda reduced) >> printEvalTrace reduced


-- Starts the calculator
main = do hSetBuffering stdout NoBuffering
          askStyle >>= runCalculator
    where
        askStyle = do
            putStr "Want to see lambdas or Haskell datatypes? [L/d] "
            style <- getLine
            putStrLn ""
            return $ case map toLower style of
                'd':_ -> show
                _     -> pretty


-- From slide "Examples of β-Reduction"

ex1 = (λ2 X Y . x) `app` y  -- (λxy. x)y =α (λxz. x)y → λz. y
ex2 = (λ2 Y Z . z) `app` u  -- (λyz.z)u → λz. z
                            -- (λy(λz.z))u
                            -- (λz.z)[u/y] -- here we have to "prefer" z so that it is not renamed to a
ex3 = (λ X . x `app` y) `app` (λ X . x)               -- (λx. xy)(λx.x) → (λx. x)y → y
ex4 = (λ X . x `app` y) `app` ((λ2 X Z . z) `app` u)  -- (λx. xy)((λyz. z)u) → ((λyz. z)u)y → (λz. z)y → y

-- Example 5 is ex4 and we have fixed the evaluation strategy, so there is nothing to do.


-- "and tests" collapses all tests to a single Bool
tests = [ add == Def A (Def B (Def F (Def X (App (App (Var A) (Var F)) (App (App (Var B) (Var F)) (Var X))))))
        , nf ex1 == (λ A . y)
        , nf ex2 == (λ Z . z)
        , nf ex3 == y
        , nf ex4 == y
        , all (\i -> nat (num i) == i) [0..100]
        ]


-- Debugging helpers

_DEBUG = False

-- To print the name, arguments and result at the beginning of a function
debug :: (Show a, Show b) => [Char] -> a -> b -> b
debug name input res | _DEBUG = trace (name ++ ":  " ++ show input ++ " ->  " ++ show res) res
debug _    _     res          = res

-- Performs one β reduction step and elimitates the information whether the term could be simplified
nfstep l = whatever $ nf1 l


-- Either monad (in Control.Monad.Instances) in GHC >= 7.0
instance Monad (Either e) where
    return = Right
    Left  l >>= _ = Left l
    Right r >>= k = k r
