-- | Concrete testing data.
module Test.Concrete where

import qualified Data.Set as Set

import Logic

-- | Term free variables helper.
fv :: Term String String -> [String]
fv = Set.toList . freeVarsT

-- | Formula free variables helper.
fvf :: Formula String String String -> [String]
fvf = Set.toList . freeVars

-- | Constructs an empty relation.
r :: String -> Formula String String String
r x = Relation x []

-- | Skolemize a formula and get rid of 'Either'.
sk :: Formula String String String -> Formula String String String
sk = fmapF id (either id id) id . skolemize . prenex

-- * Testing data.

-- Testing data for term free variables and pretty printing.
term1, term2, term3 :: Term String String
term1 = Function "f" [Var "a", Function "g" [Var "b", Var "c"], Var "c"]
term2 = Function "f" [Function "g" [], Function "h" []]
term3 = Var "a"

-- Testing data for formula free variables.
formula1, formula2, formula3, formula4 :: Formula String String String
formula1 = Relation "R" [Var "x"]
formula2 = Forall "x" $ Relation "R" [Var "x", Var "y"]
formula3 = Or (And formula2 (Relation "Q" [Var "x"])) formula2
formula4 = Exists "y" formula2

-- Testing data for formula pretty printing.
formula5, formula6 :: Formula String String String
formula5 = And (Implies (Implies (r "P") (r "Q")) (r "R"))
    (Relation "S" [Var "x", Var "y"])
formula6 = Not (Forall "x" (And (Or (r "A") (r "B")) (r "C")))

-- Testing data for prenex and Skolem normal form.
formula7, formula8 :: Formula String String String
formula7 = Not (Implies (Exists "x" (Relation "R" [Var "x", Var "y"]))
    (And (Relation "Q" [Var "x"]) (Exists "y"
    (Relation "S" [Var "y", Var "z"]))))
formula8 = Not (Implies (Implies (Exists "x" (Relation "R" [Var "x"]))
    (Relation "Q" [Var "y"])) (Forall "y" (Exists "z" (Relation "S"
    [Var "x", Var "y", Var "z"]))))

-- Testing data for CNF.
formula9, formula10 :: Formula String String String
formula9  = Forall "x" (Implies (Not (r "P")) (r "Q"))
formula10 = Implies (Or (r "A") (Not (Implies (Or (r "B") (r "C"))
    (And (Not (r "D")) (r "E"))))) (And (Not (r "F")) (Not (r "G")))

-- * Tests.

-- 'Term' free variables.
freeVarsT1, freeVarsT2, freeVarsT3 :: [String]
[freeVarsT1, freeVarsT2, freeVarsT3] = map fv [term1, term2, term3]

-- 'Term' pretty printing.
showT1, showT2, showT3 :: String
[showT1, showT2, showT3] = map showTerm [term1, term2, term3]

-- 'Formula' free variables.
freeVarsFT1, freeVarsFT2, freeVarsFT3, freeVarsFT4  :: [String]
[freeVarsFT1, freeVarsFT2, freeVarsFT3, freeVarsFT4]
    = map fvf [formula1, formula2, formula3, formula4]

-- 'Formula' pretty printing.
showFT1, showFT2 :: String
[showFT1, showFT2] = map showFormula [formula5, formula6]

-- 'prenex'.
prenexT1, prenexT2 :: String
[prenexT1, prenexT2] = map (showFormula . prenex) [formula7, formula8]

-- 'skolemize'.
skolemT1, skolemT2 :: String
[skolemT1, skolemT2] = map (showFormula . sk) [formula7, formula8]

-- 'cnf'.
cnfT1, cnfT2 :: String
[cnfT1, cnfT2] = map (showFormula . cnf) [formula9, formula10]

-- * Results.

-- 'Term' free variables.
freeVarsR1, freeVarsR2, freeVarsR3 :: [String]
[freeVarsR1, freeVarsR2, freeVarsR3] =
    [ ["a", "b", "c"]
    , []
    , ["a"]
    ]

-- 'Term' pretty printing.
showR1, showR2, showR3 :: String
[showR1, showR2, showR3] =
    [ "f(a,g(b,c),c)"
    , "f(g(),h())"
    , "a"
    ]

-- 'Formula' free variables.
freeVarsFR1, freeVarsFR2, freeVarsFR3, freeVarsFR4  :: [String]
[freeVarsFR1, freeVarsFR2, freeVarsFR3, freeVarsFR4] =
    [ ["x"]
    , ["y"]
    , ["x", "y"]
    , []
    ]

-- 'Formula' pretty printing.
showFR1, showFR2 :: String
[showFR1, showFR2] =
    [ "((P[] -> Q[]) -> R[]) & S[x,y]"
    , "~(Vx)((A[] v B[]) & C[])"
    ]

-- 'prenex'.
prenexR1, prenexR2 :: String
[prenexR1, prenexR2] =
    [ "(Ed)(Ve)~(R[d,b] -> Q[a] & S[e,c])"
    , "(Vc)(Ed)(Ve)~((R[c] -> Q[b]) -> S[a,d,e])"
    ]

-- 'skolemize'.
skolemR1, skolemR2 :: String
[skolemR1, skolemR2] =
    [ "~(R[a(),b] -> Q[a] & S[e,c])"
    , "~((R[c] -> Q[b]) -> S[a,a(c),e])"
    ]

-- 'cnf'.
cnfR1, cnfR2 :: String
[cnfR1, cnfR2] =
    [ "(Vx)(P[] v Q[])"
    , "(~A[] v ~F[]) & (~A[] v ~G[]) & (~B[] v ~D[] v ~F[]) & (~B[]\
      \ v ~D[] v ~G[]) & (~B[] v E[] v ~F[]) & (~B[] v E[] v ~G[]) \
      \& (~C[] v ~D[] v ~F[]) & (~C[] v ~D[] v ~G[]) & (~C[] v E[] \
      \v ~F[]) & (~C[] v E[] v ~G[])"
    ]
