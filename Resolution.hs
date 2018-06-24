module Resolution(sat, tau, valid, V, F(..), Statement, L(..), C, CSet, Clash) where
  import Data.List
  -----------------------------------------
  -- Tipos de datos
  -----------------------------------------
  type V = String
  data F = Atom V
         | Neg  F
         | Conj F F                  
         | Disy F F     
         | Imp  F F
         deriving(Eq)     
  
  type Statement = ([F],F)
  
  data L = LP V | LN V
           deriving (Eq)
  type C    = [L]
  type CSet = [C]
  type Clash = (C,L,C,L)
  
  -----------------------------------------
  -- Funciones principales
  -----------------------------------------
  -- Pos: retorna True si la formula es SAT, o False si es UNSAT
  sat :: F -> Bool
  sat f = not (hasEmtpyCSet (resolveCSet (f2CSet f))) --contiene el vacio es unsat, retorno false
  
  -- Pos: retorna True si la formula es Tautología, o False en caso contrario
  tau :: F -> Bool
  tau f = not (sat f)
  
  -- Pos: retorna True si el razonamiento es válido, o False en caso contrario
  valid :: Statement -> Bool
  valid ([],conclusion) = not (sat conclusion)
  valid ((premisa:premisas),conclusion) = sat premisa && valid (premisas, conclusion)
  
  -----------------------------------------
  -- Formulas y Clausulas
  -----------------------------------------
  -- Pos: convierte una formula a un conjunto de clausulas
  f2CSet :: F -> CSet
  f2CSet f = cnf2CSet (f2cnf f)
  
  -- Pre: recibe una formula en FNC
  -- Pos: convierte la FNC a un conjunto de clausulas
  cnf2CSet :: F -> CSet
  cnf2CSet (Atom v)     = [[LP v]]
  cnf2CSet (Neg (Atom v)) = [[LN v]]
  cnf2CSet (a `Conj` b) = (cnf2CSet a) ++ (cnf2CSet b)
  cnf2CSet (a `Disy` b) = [removeDupes ((f2ArrayL a) ++ (f2ArrayL b))]
  
  f2ArrayL :: F -> [L]
  f2ArrayL (Atom v) = [LP v]
  f2ArrayL (Neg (Atom v)) = [LN v]
  f2ArrayL (a `Disy` b) = (f2ArrayL a) ++ (f2ArrayL b)
  
  removeDupes :: (Eq a) => [a] -> [a]
  removeDupes (x:xs) = x : removeDupes (filter (/= x) xs)
  removeDupes [] = [] 
  
  --  ((Atom "p") `Disy` ((Atom "q") `Disy` (Atom "r")))
  -- Pos: convierte una formula a FNC
  f2cnf :: F -> F
  f2cnf = distr . pushNeg . sustImp
  
  sustImp :: F -> F
  sustImp (Atom v)     = (Atom v)
  sustImp (Neg a)      = Neg (sustImp a)
  sustImp (a `Conj` b) = (sustImp a) `Conj` (sustImp b)
  sustImp (a `Disy` b) = (sustImp a) `Disy` (sustImp b)
  sustImp (a `Imp`  b) = (Neg (sustImp a)) `Disy` (sustImp b) 
  
  pushNeg :: F -> F
  pushNeg (Atom v)           = (Atom v)
  pushNeg (Neg (a `Disy` b)) = (pushNeg (Neg a)) `Conj` (pushNeg (Neg b))
  pushNeg (Neg (a `Conj` b)) = (pushNeg (Neg a)) `Disy` (pushNeg (Neg b))
  pushNeg (Neg (Neg a))      = pushNeg a
  pushNeg (Neg a)            = Neg (pushNeg a)
  pushNeg (a `Conj` b)       = (pushNeg a) `Conj` (pushNeg b)
  pushNeg (a `Disy` b)       = (pushNeg a) `Disy` (pushNeg b)
  
  distr :: F -> F
  distr (a `Disy` b) = distr' ((distr a) `Disy` (distr b))
    where 
    distr' (a `Disy` (b `Conj` c)) = (distr' (a `Disy` b)) `Conj` (distr' (a `Disy` c))
    distr' ((a `Conj` b) `Disy` c) = (distr' (a `Disy` c)) `Conj` (distr' (b `Disy` c))
    distr' a                       = a
  distr (a `Conj` b) = (distr a) `Conj` (distr b)
  distr a            = a  
  
  
  -----------------------------------------
  -- Procedimiento de Resolución
  -----------------------------------------
  -- Pre: recibe un conjunto de clausulas
  -- Pos: si es SAT,   retorna el conjunto de clausulas saturado
  --      si es UNSAT, retorna un conjunto de clausulas incluyendo la clausula vacía
  resolveCSet :: CSet -> CSet
  resolveCSet [] = []
  resolveCSet [c] = [c]
  resolveCSet (c1:c2:cs) = (resolveCSet (c2:cs)) ++ (c2CSet c1 (c2:cs))
  --case (hasClash c1 c2) of { LP "" -> (resolveCSet (c1:cs)) ; False -> a}
  
  hasClash :: C -> C -> L
  hasClash [] ls = LP ""
  hasClash (l1:l1s) (l2:l2s) = case (or ( map (== (opuesto l1)) (l2:l2s))) of { True -> l1 ;    
                                                                                False -> hasClash (l1s) (l2:l2s)}

  opuesto :: L -> L 
  opuesto (LP v) = LN v
  opuesto (LN v) = LP v
  
  c2CSet :: C -> CSet -> CSet
  c2CSet c [] = []
  -- c2CSet c [a] = [resolveClash(c , (hasClash c a) , a , (opuesto (hasClash c a)))]
  c2CSet c (x:xs) = (resolveClash (c , (hasClash c x) , x , (opuesto (hasClash c x)))) : (c2CSet c xs)
  --case (litToClash c x) of { LP "" -> (c2CSet c xs) ; alfa -> (resolveClash (c , alfa ,  x, (opuesto alfa)) ) : (c2CSet c xs) }

  -- Pos: retorna la resolvente de un conflicto
  resolveClash :: Clash -> C
  resolveClash (c1, l1, c2, l2) = removeDupes ((delete l1 c1) ++ (delete l2 c2))
  
  -- resolveClash ([LP "p" , LP "q"] , (LP "p") , [LP "q" , LN "p"] , (LN "p") )

  hasEmtpyCSet :: CSet -> Bool
  hasEmtpyCSet [] = False
  hasEmtpyCSet (x:xs) = (hasEmtpyC x) || (hasEmtpyCSet xs)

  hasEmtpyC :: C -> Bool
  hasEmtpyC [] = False
  hasEmtpyC (l:ls) = (l == (LP "")) || (hasEmtpyC ls)
  ----------------------------------------------------------------------------------
  -- Pretty Printing
  instance Show F where
    show (Atom v)       = v
    show (Neg (Neg a))  = "~" ++ show (Neg a)
    show (Neg (Atom v)) = "~ " ++ show (Atom v)
    show (Neg a)        = "~ (" ++ show a ++ ")"
    show (a `Conj` b)   = "(" ++ show a ++ ") /\\ (" ++ show b ++ ")"
    show (a `Disy` b)   = "(" ++ show a ++ ") \\/ (" ++ show b ++ ")"
    show (a `Imp` b)    = "(" ++ show a ++ ") --> (" ++ show b ++ ")"
    
  instance Show L where  
    show (LP v)  = v
    show (LN v)  = "~" ++ v