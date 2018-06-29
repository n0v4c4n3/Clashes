-- Gabriel Martinez (188532)
-- Mauricio Guala (196087)
module Test where

import Resolution
import Test.HUnit  -- Acerca de HUnit: https://hackage.haskell.org/package/HUnit

tau1_sat_should_be_true  = TestCase (assertEqual "sat tau1" True  (sat tau1))
tau2_sat_should_be_true  = TestCase (assertEqual "sat tau2" True  (sat tau2))
tau3_sat_should_be_true  = TestCase (assertEqual "sat tau3" True  (sat tau3))
ind1_sat_should_be_true  = TestCase (assertEqual "sat ind1" True  (sat ind1))
ind2_sat_should_be_true  = TestCase (assertEqual "sat ind2" True  (sat ind2))
ind3_sat_should_be_true  = TestCase (assertEqual "sat ind3" True  (sat ind3))
con1_sat_should_be_false = TestCase (assertEqual "sat con1" False (sat con1))
con2_sat_should_be_false = TestCase (assertEqual "sat con2" False (sat con2))
con3_sat_should_be_false = TestCase (assertEqual "sat con3" False (sat con3))

tau1_tau_should_be_true  = TestCase (assertEqual "tau tau1" True  (tau tau1))
tau2_tau_should_be_true  = TestCase (assertEqual "tau tau2" True  (tau tau2))
tau3_tau_should_be_true  = TestCase (assertEqual "tau tau3" True  (tau tau3))
ind1_tau_should_be_false = TestCase (assertEqual "tau ind1" False (tau ind1))
ind2_tau_should_be_false = TestCase (assertEqual "tau ind2" False (tau ind2))
ind3_tau_should_be_false = TestCase (assertEqual "tau ind3" False (tau ind3))
con1_tau_should_be_false = TestCase (assertEqual "tau con1" False (tau con1))
con2_tau_should_be_false = TestCase (assertEqual "tau con2" False (tau con2))
con3_tau_should_be_false = TestCase (assertEqual "tau con3" False (tau con3))

val1_val_should_be_true  = TestCase (assertEqual "valid val1" True (valid val1))
val2_val_should_be_true  = TestCase (assertEqual "valid val2" True (valid val2))
val3_val_should_be_true  = TestCase (assertEqual "valid val3" True (valid val3))
inv1_val_should_be_false = TestCase (assertEqual "valid inv1" False (valid inv1))
inv2_val_should_be_false = TestCase (assertEqual "valid inv2" False (valid inv2))
inv3_val_should_be_false = TestCase (assertEqual "valid inv3" False (valid inv3))


satTests = [TestLabel "Tautologia 1"    tau1_sat_should_be_true, 
            TestLabel "Tautologia 2"    tau2_sat_should_be_true,
            TestLabel "Tautologia 3"    tau3_sat_should_be_true,
            TestLabel "Contingencia 1"  ind1_sat_should_be_true, 
            TestLabel "Contingencia 2"  ind2_sat_should_be_true,
            TestLabel "Contingencia 3"  ind3_sat_should_be_true,
            TestLabel "Contradiccion 1" con1_sat_should_be_false, 
            TestLabel "Contradiccion 2" con2_sat_should_be_false,
            TestLabel "Contradiccion 3" con3_sat_should_be_false]
                     
tauTests = [TestLabel "Tautologia 1"    tau1_tau_should_be_true, 
            TestLabel "Tautologia 2"    tau2_tau_should_be_true,
            TestLabel "Tautologia 3"    tau3_tau_should_be_true,
            TestLabel "Contingencia 1"  ind1_tau_should_be_false, 
            TestLabel "Contingencia 2"  ind2_tau_should_be_false,
            TestLabel "Contingencia 3"  ind3_tau_should_be_false,
            TestLabel "Contradiccion 1" con1_tau_should_be_false, 
            TestLabel "Contradiccion 2" con2_tau_should_be_false,
            TestLabel "Contradiccion 3" con3_tau_should_be_false]                     
       
valTests = [TestLabel "Razonamiento valido 1" val1_val_should_be_true, 
            TestLabel "Razonamiento valido 2" val2_val_should_be_true,
            TestLabel "Razonamiento valido 3" val3_val_should_be_true,
            TestLabel "Razonamiento invalido 1" inv1_val_should_be_false, 
            TestLabel "Razonamiento invalido 2" inv2_val_should_be_false,
            TestLabel "Razonamiento invalido 3" inv3_val_should_be_false]

allTests = TestList $ satTests ++ tauTests ++ valTests                    


-- razonamiento valido    
val1 = ([], (Atom "q") `Imp` (Atom "q"))
val2 = ([((Atom "q") `Conj` (Atom "r")) `Imp` (Atom "p"), (Neg (Atom "q")) `Disy` (Atom "r"), Atom "q"],  (Atom "p") `Conj` (Atom "q"))
val3 = ([(Neg (Atom "p")) `Disy` (Neg (Atom "q")) `Disy` (Atom "r"), Atom "p", Atom "q"],  Atom "r")
  
-- razonamiento invalido  
inv1 = ([ ((Atom "p") `Conj` (Atom "q")) `Imp` (Atom "r"), Atom "p", Atom "q"], Neg (Atom "r") )
inv2 = ([ (Atom "p") `Imp` ((Atom "q") `Conj` (Atom "r")), Neg (Atom "p")], Neg (Atom "q") `Conj` Neg (Atom "r"))  -- no tiene resolventes
inv3 = ([ (Neg (Atom "p")) `Disy` ((Atom "q") `Disy` (Atom "r")), (Neg (Atom "p")) `Disy` (Atom "r"), (Atom "p") `Disy` (Neg (Atom "q")) ], Neg (Atom "q") `Conj` Neg (Atom "r"))  
  
-- tautologias
tau1 = true
tau2 = (Atom "p") `Imp` (Atom "p")
tau3 = (((Atom "p") `Imp` (Atom "q")) `Imp` (Atom "p")) `Imp` (Atom "p")

-- contingencias
ind1 = (Atom "p") `Imp` (Atom "q")
ind2 = ((Neg (Atom "p")) `Imp` (Neg (Atom "q"))) `Imp` ((Atom "p") `Imp` (Atom "q"))
ind3 = (((Atom "s") `Imp` (Atom "r")) `Disy` ((Atom "q") `Imp` (Neg (Atom "r")))) `Conj` (Atom "p")
           
-- contradicciones
con1 = false
con2 = true `Imp` false
con3 = false `Conj` ((Atom "q") `Disy` (Neg (Atom "q")))


-- Bottom y Top definidas como abreviaciones sintacticas en el lenguaje L
false = (Atom "p") `Conj` (Neg (Atom "p"))
true  = false `Imp` false