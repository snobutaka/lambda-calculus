{----------------How to use---------------------
You can define lambda-term with constructors Var, Abs, App (each means Variable, lambda-Abstraction, Application)
For example, lambda x.xy can be defined as
 (Abs (Var "x") (App (Var "x") (Var "y"))).

There are some important operations and predicates.
- alpha_equiv: takes 2 terms as arguments. If 2 terms are aplha-equivalent, alpha_equiv returns true; otherwise false.
  e.g. alpha_equiv (Abs (Var "x") (Var "x")) (Abs (Var "y") (Var "y")) == True
       alpha_equiv (Abs (Var "x") (Var "x")) (Abs (Var "x") (Var "y")) == False

- beta_reduction: takes a term as argument, then returns the term that is obtained by reducing the left-most redex of the arguments.

- many_reduction: takes a term as argument, then returns the term that is obtained by reducing the argument untill it becomes normal-foam.
  If the argument doesn't have normal-form, this function falls into endless-loop.

- beta_equiv: takes 2 terms as arguments: If 2 terms are beta-equivalent, i.e. they have same normal-form, returns True; otherwise False.
  If one of the arguments doesn't have normal-form, this function falls into endless-loop.

- church_numeral: take an Int number n, then returns the church_numeral that represents n.

- add: the term behaves addition operator for church_numerals.

- term2int: takes a church-numeral term as argument, then returns the Int value represented by the term.

------------------------------------------------}
lambda_symbol                                                   :: String
lambda_symbol                                                   =  "\x03BB"

data Term                                                       =  Var String | Abs Term Term | App Term Term
     deriving (Eq)
instance Show Term where
         show (Var var)                                         =  var
         show (Abs left right)                                  =  "(" ++ lambda_symbol ++ show left ++ "." ++ show right ++ ")"
         show (App left right)                                  =  "(" ++ show left ++ " " ++ show right ++ ")"

data Form                                                       =  Variable | Abstraction | Application | Mal_formed
     deriving (Eq,Show)

well_formed                                                     :: Term -> Bool
well_formed (Abs (Var var) term)                                =  well_formed term
well_formed (Abs term1 term2)                                   =  False
well_formed (App term1 term2)                                   =  well_formed term1 && well_formed term2
well_formed (Var var)                                           =  True

form_of                                                         :: Term -> Form
form_of (Var var)                                               =  Variable
form_of (Abs left right)                                        =  if well_formed (Abs left right) then Abstraction else Mal_formed
form_of (App left right)                                        =  if well_formed (App left right) then Application else Mal_formed

remove                                                          :: Eq a => [a] -> a -> [a]
remove [] _                                                     =  []
remove (x:xs) target
       |x == target                                             =  remove xs target
       |otherwise                                               =  x:(remove xs target)

-- remove duplication in list
rmdups                                                          :: Eq a => [a] -> [a]
rmdups []                                                       = []
rmdups (x:xs)                                                   = x:rmdups (filter (/= x) xs)

var_occurence                                                   :: Term -> [Term]
var_occurence (Var x)                                           =  [Var x]
var_occurence (App left right)                                  =  var_occurence left ++ var_occurence right
var_occurence (Abs _ term)                                      =  var_occurence term

vars                                                            :: Term -> [Term]
vars term                                                       =  rmdups (var_occurence term)

free_vars                                                       :: Term -> [Term]
free_vars (Var x)                                               =  [(Var x)]
free_vars (App left right)                                      =  free_vars left ++ free_vars right
free_vars (Abs (Var x) term)                                    =  remove (free_vars term) (Var x)
free_vars (Abs _ term)                                          =  []

free_var                                                        :: Term -> [Term]
free_var term                                                   =  rmdups (free_vars term)

same_stracture                                                  :: Term -> Term -> Bool
same_stracture (Var x) (Var y)                                  =  True
same_stracture (App left1 right1) (App left2 right2)            =  same_stracture left1 left2 && same_stracture right1 right2
same_stracture (Abs var1 term1) (Abs var2 term2)                =  same_stracture var1 var2 && same_stracture term1 term2
same_stracture _ _                                              =  False

alpha_equiv                                                     :: Term -> Term -> Bool
alpha_equiv (Var x) (Var y)                                     =  x == y
alpha_equiv (App left1 right1) (App left2 right2)               =  alpha_equiv left1 left2 && alpha_equiv right1 right2
alpha_equiv (Abs (Var x) term1) (Abs (Var y) term2)
            |x == y                                             =  alpha_equiv term1 term2
            |otherwise                                          =  alpha_equiv term1 (substitute term2 (Var y) (Var x))
alpha_equiv (Abs _ _) (Abs _ _)                                 =  False
alpha_equiv _ _                                                 =  False

is_beta_redex                                                   :: Term -> Bool
is_beta_redex (App left _)                                      =  if form_of left == Abstraction then True else False
is_beta_redex _                                                 =  False

has_beta_redex                                                  ::  Term -> Bool
has_beta_redex (Var _)                                          =  False
has_beta_redex (Abs left right)                                 =  has_beta_redex left || has_beta_redex right
has_beta_redex (App left right)                                 =  is_beta_redex (App left right) || has_beta_redex left || has_beta_redex right

gen_new_var                                                     :: Term -> [Term] -> [Term] -> Term
gen_new_var (Var x) xs ys                                       =  if elem (Var x) xs || elem (Var x) ys then gen_new_var (Var (x++"'")) xs ys else (Var x)
gen_new_var _ _ _                                               =  (Var "something wrong")

substitute                                                      :: Term -> Term -> Term -> Term
substitute (Var var1) (Var var2) term                           =  if var1 == var2 then term else (Var var1)
substitute (App left right) (Var var) term                      =  (substitute left (Var var) term) `App` (substitute right (Var var) term)
substitute (Abs (Var var1) term1) (Var var2) term2
           |var1 == var2                                        =  Abs (Var var1) term1 
           |otherwise                                           =  if elem (Var var1) (free_var term2)
                                                                      then substitute (Abs var1' (substitute term1 (Var var1) var1')) (Var var2) term2
                                                                      else Abs (Var var1) (substitute term1 (Var var2) term2)
                                                                           where
                                                                            var1' = gen_new_var (Var var1) (vars term1) (vars term2)
substitute _ _ _                                                =  (Var "error:substituted term is not a variable!")

beta_reduction                                                  :: Term -> Term
beta_reduction (Var var)                                        =  (Var var)
beta_reduction (App (Abs (Var x) left) right)                   =  substitute left (Var x) right
beta_reduction (App left right)                                 =  if has_beta_redex left 
                                                                      then (beta_reduction left) `App` right 
                                                                      else left `App` (beta_reduction right)
beta_reduction (Abs left right)                                 = (Abs left (beta_reduction right))

many_reduction                                                  :: Term -> Term
many_reduction term
               | has_beta_redex term                            =  many_reduction (beta_reduction term)
               | otherwise                                      =  term

beta_equiv                                                      :: Term -> Term -> Bool
beta_equiv term1 term2                                          =  alpha_equiv (many_reduction term1) (many_reduction term2)

term2int                                                        :: Term -> Int
term2int term                                                   =  if alpha_equiv (church_numeral size) term then size else -1
                                                                      where size = length (var_occurence term) -1


{- define important terms -}
id_term                                                         :: Term
id_term                                                         =  Abs x x
                                                                       where x = (Var "x")

true                                                            :: Term
true                                                            =  k_combinator

false                                                           :: Term
false                                                           =  Abs x (Abs y y)
                                                                       where
                                                                        x = Var "x"
                                                                        y = Var "y"

if_then_else                                                    :: Term -> Term -> Term -> Term
if_then_else bool term1 term2                                   =  ((bool `App` term1) `App` term2)

s_combinator                                                    :: Term
s_combinator                                                    =  Abs x (Abs y (Abs z ((x `App` z) `App` (y `App` z) )))
                                                                       where
                                                                        x = Var "x"
                                                                        y = Var "y"
                                                                        z = Var "z"

k_combinator                                                    :: Term
k_combinator                                                    =  Abs x (Abs y x)
                                                                       where
                                                                        x = Var "x"
                                                                        y = Var "y"

-- add (church_numeral m) (church_numeral n) ->> church_numeral (m+n)
add                                                             :: Term
add                                                             =  Abs x (Abs y (Abs u (Abs v
                                                                            ((x `App` u) `App` ( (y `App` u) `App` v) ))))
                                                                       where
                                                                        x = Var "x"
                                                                        y = Var "y"
                                                                        u = Var "u"
                                                                        v = Var "v"

-- iterator n = f (f (..f(f x)..)), f occurs n times
iterator                                                        :: Int -> Term
iterator 0                                                      =  (Var "x")
iterator n                                                      =  (Var "f") `App` (iterator (n-1))

church_numeral                                                  :: Int -> Term
church_numeral n                                                =  Abs (Var "f") (Abs (Var "x") (iterator n))
