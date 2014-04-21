-- This is a program for combinatory logic.
-- You can define CL-termm and reduce terms.
-- You can construct CL-term by the function 'abstraction', wihch returns a term that has lambda-abstraction like behavior.

data Term                       = Variable String | S | K | App Term Term
instance Show Term where
      show (Variable var)                               =  var
      show S                                            =  "S"
      show K                                            =  "K"
      show (App left right)                             =  "(" ++ show left ++ " " ++ show right ++ ")"

{- get free varialbes of a Term-}
free_vars                                               :: Term -> [Term]
free_vars (Variable var)                                =  [Variable var]
free_vars S                                             =  []
free_vars K                                             =  []
free_vars (App left right)                              =  (free_vars left) ++ (free_vars right)

{- check the form of term -}
what_form                                               :: Term -> String
what_form (App left right)                              =  "application"
what_form _                                             =  "variable"

{- get subexpression of term in application form -}
get_left                                                :: Term -> Term
get_left (App left right)                               =  left
get_right                                               :: Term -> Term
get_right (App left right)                              =  right

{- define K reduction rule -}
--if term can be reduced with K-rule, k_reductionable == True
k_reductionable                                         :: Term -> Bool
k_reductionable term                                    =  if what_form term == "application" 
                                                              then if what_form (get_left term) == "application"
                                                                      then if show (get_left (get_left term)) == "K"
                                                                              then True
                                                                              else False
                                                                      else False
                                                              else False

--reduction a term with K-rule
k_reduction                                             :: Term -> Term
k_reduction term
            |k_reductionable term                       =  get_right (get_left term)
            |otherwise                                  =  term

{- define S reductioin rule -}
s_reductionable                                         :: Term -> Bool
s_reductionable term                                    =  if what_form term == "application"
                                                              then if what_form (get_left term) == "application"
                                                                      then if what_form (get_left (get_left term)) == "application"
                                                                              then if show (get_left (get_left (get_left term))) == "S"
                                                                                      then True
                                                                                      else False
                                                                              else False
                                                                      else False
                                                              else False

s_reduction                                             :: Term -> Term
s_reduction term
            |s_reductionable term                       = App (App x z) (App y z)
            |otherwise                                  = term
              where
                x = get_right (get_left (get_left term))
                y = get_right (get_left term)
                z = get_right term

-- if a term is S or K reductionable, reductionable == True
reductionable                                           :: Term -> Bool
reductionable (App left right)
              |k_reductionable (App left right)         =  True
              |s_reductionable (App left right)         =  True
              |otherwise                                =  reductionable left || reductionable right
reductionable _                                         =  False

-- reduce a term onece with S or K rule, at first found subexpression that is reductionable
reduction                                               :: Term -> Term
reduction term
          |s_reductionable term                         =  s_reduction term
          |k_reductionable term                         =  k_reduction term
          |reductionable (get_left term)                =  (reduction (get_left term)) `App` (get_right term)
          |reductionable (get_right term)               =  (get_left term) `App` (reduction (get_right term))
          |otherwise                                    =  term

-- reduce a term until it turns into normal form
many_reduction                                          :: Term -> Term
many_reduction term
               |reductionable term                      =  many_reduction (reduction term)
               |otherwise                               =  term

--reduce a term for inuput times
reduction_times                                         :: Int -> Term -> Term
reduction_times 0 term                                  =  term
reduction_times n term                                  =  reduction (reduction_times (n-1) term)

-- abstract a term
abstraction                                             :: Term -> Term -> Term
abstraction (Variable var1) (Variable var2)             =  if var1 == var2 
                                                              then id_term
                                                              else App K (Variable var2) 
abstraction (Variable var) (left `App` right)             =  if not (elem var (map show (free_vars (left `App` right)))) 
                                                              then App K (left `App` right)
                                                              else (S `App` (abstraction (Variable var) left)) `App` (abstraction (Variable var) right)
abstraction (Variable var) S                            = K `App` S
abstraction (Variable var) K                            = K `App` K

{-------------------------------------------------------------------------------------------------------
        **this versioin of abstraction contains eta-reduction like rule**
abstraction                                             :: Term -> Term -> Term
abstraction (Variable var1) (Variable var2)             =  if  var1 == var2
                                                              then id_term
                                                              else App K (Variable var2)
abstraction (Variable var) (App left right)             =  if not (elem var (map to_string (free_vars (App left right)))) 
                                                              then (App left right)
                                                              else if to_string right == var && not (elem var (map to_string (free_vars left)))
                                                                      then left
                                                                      else App (App S (abstraction (Variable var) left)) (abstraction (Variable var) right)
 ------------------------------------------------------------------------------------------------------}

{- defining some terms -}
x                                                       :: Term
x                                                       =  Variable "x"

-- I = S K K
id_term                                                 :: Term
id_term                                                 =  (S `App` K) `App` K

-- K x y
k_example                                               :: Term
k_example                                               =  (K `App` (Variable "x")) `App` (Variable "y")

-- S x y z
s_example                                               :: Term
s_example                                               =  ((S `App` (Variable "x")) `App` (Variable "y")) `App` (Variable "z")

-- define term1 s.t. [term1 x y ->> x y]
term1                                                   :: Term
term1                                                   =  abstraction (Variable "x") (abstraction (Variable "y") ((Variable "x") `App` (Variable "y")))
-- term1 x y
term1_applicated                                        :: Term
term1_applicated                                        =  (term1 `App` (Variable "x")) `App` (Variable "y")

-- define term2 s.t. [term2 x y z ->> x y z]
term2                                                   :: Term
term2                                                   =  abstraction (Variable "x") (abstraction (Variable "y") 
                                                                       (abstraction (Variable "z") (((Variable "x") `App` (Variable "y")) `App` (Variable "z"))))
-- term2 x y z
term2_applicated                                        :: Term
term2_applicated                                        =  ((term2 `App` (Variable "x")) `App` (Variable "y")) `App` (Variable "z")

-- define term3 s.t. [term3 x y z w ->> x y z w]
term3                                                   :: Term
term3                                                   =  abstraction (Variable "x") (abstraction (Variable "y") (abstraction (Variable "z") (abstraction (Variable "w")
                                                                       (( ((Variable "x") `App` (Variable "y")) `App` (Variable "z") ) `App` (Variable "w")))))
-- term3 x y z w
term3_applicated                                        :: Term
term3_applicated                                        =  (((term3 `App` (Variable "x")) `App` (Variable "y")) `App` (Variable "z")) `App` (Variable "w")

-- define term4 s.t. [term4 x y ->> y x]
term4                                                   :: Term
term4                                                   =  abstraction (Variable "x") (abstraction (Variable "y") 
                                                                       ((Variable "y") `App` (Variable "x")))
-- term4 x y
term4_applicated                                        :: Term
term4_applicated                                        =  (term4 `App` (Variable "x")) `App` (Variable "y")

-- define term5 s.t. [term5 x y ->> x y y]
term5                                                   :: Term
term5                                                   =  abstraction (Variable "x") (abstraction (Variable "y")
                                                                       ((((Variable "x") `App` (Variable "y")) `App` (Variable "y"))))
-- term5 x y
term5_applicated                                        :: Term
term5_applicated                                        =  (term5 `App` (Variable "x")) `App` (Variable "y")

