import ProofSystems.propositional_logic.definitions

------------------ SATISFIABILITY ------------------
def getPropVar {Var : Type} [DecidableEq Var] : Formula Var → List Var
  | .varf x => {x}
  | .truef => ∅
  | .falsef => ∅
  | .negf f => getPropVar f
  | .andf f g => (getPropVar f) ∪ (getPropVar g)
  | .orf f g => (getPropVar f) ∪ (getPropVar g)

def gen_domain (n : Nat) : List (List Bool) :=
  if n <= 0 then []
  else [false, true] :: gen_domain (n-1)

def gen_table_left (n : Nat) : List (List Bool) := cp (gen_domain n)

set_option linter.style.longLine false
def find_assignment {t : Type} [DecidableEq t] (propvars : List t) (img : List Bool) (v : t) : Bool :=
  match propvars with
    | (p :: ps) => if p == v && img.length>0 then img.head!
                  else find_assignment ps img.tail v
    | [] => false

def gen_assignment {t : Type} [DecidableEq t] (propvar : List t) (img : List Bool) : Valuation t Bool :=
  fun v : t => find_assignment propvar img v

def genTruthTable {Var : Type} [DecidableEq Var] (F : Formula Var) : List (Prod (List Bool) Bool) :=
  let propvars : List Var := getPropVar F
  let n := propvars.length
  let ttable := gen_table_left n
  let assignments := List.map (gen_assignment propvars) ttable
  let tvalues := List.map (fun a => eval a F) assignments
  let fulltable : List (Prod (List Bool) Bool) := myZip ttable tvalues
  fulltable

#eval (genTruthTable (("p" and "q") or "r" : Formula String))

def SAT [DecidableEq t] (F : Formula t) : Bool :=
  let ttable := genTruthTable F
  myFoldr (fun row : Prod (List Bool) Bool => fun tval : Bool => row.2 || tval) false ttable

-- TAUTOLOGY
def ISTAUT [DecidableEq t] (F : Formula t) : Bool :=
  ! (SAT (not F))

-- ENTAILMENT
def ENTAILS [DecidableEq t] (F G : Formula t) : Bool :=
  ! (SAT (F and (not G)))

-- LOGICALLY EQUIVALENT
def EQUIV [DecidableEq t] (F G : Formula t) : Bool :=
  (ENTAILS F G) && (ENTAILS G F)

------------------ EXAMPLES ------------------
def eg1 : Formula String := "p" and "q"
#eval SAT eg1

def eg2 : Formula String := "p" and (not "p")
#eval SAT eg2

#eval ENTAILS ("p") ("q" impl "p" : Formula String)

def deMorgL : Formula String := not ("p" and "q")
def deMorgR : Formula String := not "p" or not "q"

#eval EQUIV deMorgL deMorgR

#eval EQUIV ("p" impl "q" : Formula String) (not "p" impl not "q" : Formula String)

-- MINIMAL LOGIC AXIOMS
namespace Axioms
def PL1 : Formula String := "A" impl ("A" and "A")
#eval ISTAUT PL1

def PL2 : Formula String := ("A" and "B") impl ("B" and "A")
#eval ISTAUT PL2

def PL3 : Formula String := ("A" impl "B") impl (("A" and "C") impl ("B" and "C"))
#eval ISTAUT PL3

def PL4 : Formula String := (("A" impl "B") and ("B" impl "C")) impl ("A" impl "C")
#eval ISTAUT PL4

def PL5 : Formula String := "B" impl ("A" impl "B")
#eval ISTAUT PL5

def PL6 : Formula String := ("A" and ("A" impl "B")) impl "B"
#eval ISTAUT PL6

def PL7 : Formula String := "A" impl ("A" or "B")
#eval ISTAUT PL7

def PL8 : Formula String := ("A" or "B") impl ("B" or "A")
#eval ISTAUT PL8

def PL9 : Formula String := (("A" impl "C") and ("B" impl "C")) impl (("A" or "B") impl "C")
#eval ISTAUT PL9

def PL10 : Formula String := (("A" impl "B") and ("A" impl (not "B"))) impl (not "A")
#eval ISTAUT PL10

-- INTUITIONISTIC LOGIC
def PL11 : Formula String := (not "A") impl ("A" impl "B")
#eval ISTAUT PL11

-- CLASSICAL LOGIC
def PL12 : Formula String := (not (not "A")) impl "A"
#eval ISTAUT PL12
end Axioms


------- DNF -------
def findDNF {Var : Type} [DecidableEq Var] (F : Formula Var) : List (List Bool) :=
  let propvars : List Var := getPropVar F
  let n := propvars.length
  let ttable := gen_table_left n
  let assignments := List.map (gen_assignment propvars) ttable
  let tvalues := List.map (fun a => eval a F) assignments
  let fulltable : List (Prod (List Bool) Bool) := myZip ttable tvalues
  let p := fun pair : Prod (List Bool) Bool => pair.2
  List.map (fun x : Prod (List Bool) Bool => x.1) (fulltable.filter (p))

def findCNF {Var : Type} [DecidableEq Var] (F : Formula Var) : List (List Bool) :=
  let propvars : List Var := getPropVar F
  let n := propvars.length
  let ttable := gen_table_left n
  let assignments := List.map (gen_assignment propvars) ttable
  let tvalues := List.map (fun a => eval a F) assignments
  let fulltable : List (Prod (List Bool) Bool) := myZip ttable tvalues
  let p := fun pair : Prod (List Bool) Bool => !pair.2
  List.map (fun x : Prod (List Bool) Bool => List.map (! ·) x.1) (fulltable.filter (p))

def tmpf : Formula String := ("x" or "y") impl "z"
#eval findCNF tmpf
