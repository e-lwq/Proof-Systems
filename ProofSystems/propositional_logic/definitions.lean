import Mathlib.Data.Set.Defs
import Mathlib.Data.Finset.Basic

set_option linter.style.longLine false

inductive Formula (Var : Type) : Type
| truef  : Formula Var
| falsef  : Formula Var
| varf  : Var → Formula Var
| negf  : Formula Var → Formula Var
| andf  : Formula Var → Formula Var → Formula Var
| orf   : Formula Var → Formula Var → Formula Var
deriving DecidableEq, Repr

--- Logical abbreviations
def impl {Var} (F G : Formula Var) : Formula Var :=
  Formula.orf (Formula.negf F) G
def iff {Var} (F G : Formula Var) : Formula Var :=
  Formula.andf (impl F G) (impl G F)
def xor {Var} (F G : Formula Var) : Formula Var :=
  Formula.orf (Formula.andf F (Formula.negf G)) (Formula.andf (Formula.negf F) G)

open Formula

instance {Var : Type} [Inhabited Var] : Inhabited (Formula Var) where
  default := truef

--- Pretty writing
instance : Coe String (Formula String) where
  coe := Formula.varf
prefix:75 "not " => negf
infixr:70 " and " => andf
infixr:65 " or " => orf
infixr:60 " impl " => impl
infixr:55 " iff " => iff
infixr:65 " xor " => xor
---

--- Examples of formulas
def ex_formula_1 : Formula String :=
    "p" impl "q" impl "p"
---

--- Type definitions of valuations and evaluations
def Valuation (Var : Type) (Domain : Type):= Var → Domain
def Evaluation (Var : Type) (Domain : Type) :=
  Valuation Var Domain → Formula Var → Domain
---

--- Examples of valuations and evaluations
---- A standard and a non-standard valuation
def ex_valuation_bool : Valuation String Bool :=
    fun x => if x = "p" then true else if x = "q" then false else false
def ex_valuation_string : Valuation String String :=
    fun x => if x = "p" then "♡" else if x = "q" then "♧" else "unknown"
----

---- Generic evaluation function for propositional logic
set_option linter.unusedVariables false
def eval {Var} : Evaluation Var Bool
| v, Formula.truef      => true
| v, Formula.falsef     => false
| v, Formula.varf x     => v x
| v, Formula.negf F     => !(eval v F)
| v, Formula.andf F G   => (eval v F) && (eval v G)
| v, Formula.orf  F G   => (eval v F) || (eval v G)

#eval eval ex_valuation_bool ex_formula_1
----

---- Nonstandard evaluation function that maps formulas to funny strings
def eval_string {Var} : Evaluation Var String
| v, Formula.truef      => "𓅪"
| v, Formula.falsef     => "⌂"
| v, Formula.varf x     => v x
| v, Formula.negf F     => "☺" ++ (eval_string v F)
| v, Formula.andf F G   => (eval_string v F) ++ (eval_string v G)
| v, Formula.orf  F G   => (eval_string v G) ++ (eval_string v F)

#eval eval_string ex_valuation_string ex_formula_1
----
-- DEF
def isTaut {Var : Type} [DecidableEq Var] (F : Formula Var) : Prop :=
  ∀ valuation : Valuation Var Bool, eval valuation F = true

def entails {Var : Type} [DecidableEq Var] (F G : Formula Var) : Prop :=
  ∀ valuation : Valuation Var Bool, eval valuation F = true → eval valuation G = true

def logicEquiv {Var : Type} [DecidableEq Var] (F G : Formula Var) : Prop :=
  ∀ valuation : Valuation Var Bool, eval valuation F = eval valuation G

def unsat {Var : Type} [DecidableEq Var] (F : Formula Var) : Prop :=
  ∀ valuation : Valuation Var Bool, eval valuation F = false

theorem taut_unsat {Var : Type} [DecidableEq Var] (f : Formula Var) : isTaut f ↔ unsat (not f) := by
  unfold isTaut at *
  unfold unsat at *
  apply Iff.intro
  · intro istautf val
    have ftrue := istautf val
    calc
      eval val (not f) = ! eval val f := rfl
      _ = ! true := by rw [ftrue]
      _ = false := rfl
  · intro unsatnotf val
    have hnotf := unsatnotf val
    simp? [eval] at hnotf
    exact hnotf

-- LOGICAL EQUIVALENCE IS AN EQUIVALENCE RELATION
namespace logicEquiv
theorem reflexive {Var : Type} [DecidableEq Var] {F : Formula Var} : logicEquiv F F := by
  rw [logicEquiv]
  intro val
  rfl

theorem symmetric {Var : Type} [DecidableEq Var] {F G : Formula Var} : logicEquiv F G → logicEquiv G F := by
  intro feqg
  rw [logicEquiv] at *
  intro val
  have geqf := feqg val
  apply Eq.symm
  exact geqf

theorem transitive {Var : Type} [DecidableEq Var] {F G H : Formula Var} : logicEquiv F G → logicEquiv G H → logicEquiv F H := by
  intro feqg geqh
  rw [logicEquiv] at *
  intro val
  rw [feqg val, geqh val]
end logicEquiv

instance {Var : Type} [DecidableEq Var] : Trans (logicEquiv (Var := Var)) (logicEquiv (Var := Var)) (logicEquiv (Var := Var)) where
  trans := logicEquiv.transitive

-- HELPER FUNCTIONS
def cp {p : Type} : (List (List p)) → List (List p)
  | [] => [[]]
  | xs :: xss => do
    let x ← xs
    let ys ← cp xss
    pure (x :: ys)

def myZip {p q : Type} : List p → List q → List (Prod p q)
  | (x::xs), (y::ys) => (x,y) :: myZip xs ys
  | _, _ => []

def myFoldr {a b : Type} (cons : a → b → b) (nil : b) : List a → b
  | [] => nil
  | x::xs => cons x (myFoldr cons nil xs)

---- SUBSTITUTION
set_option linter.unusedVariables false
-- In formula F, substitute all occurrences of sub-formula G with H
def substitute {Var : Type} [DecidableEq Var] (F G H : Formula Var) : Formula Var :=
  if F=G then H
  else match F with
    | Formula.truef => F
    | Formula.falsef => F
    | Formula.varf f => F
    | Formula.negf f => Formula.negf (substitute f G H)
    | Formula.andf f1 f2 => Formula.andf (substitute f1 G H) (substitute f2 G H)
    | Formula.orf f1 f2 => Formula.orf (substitute f1 G H) (substitute f2 G H)

#eval substitute ("p" and "q" : Formula String) ("p":Formula String) ("r" : Formula String)

def structEquiv {Var : Type} [DecidableEq Var] (F G : Formula Var) : Prop :=
  F = G

#check Formula.recOn

theorem eqstruct_equiv {Var : Type} [DecidableEq Var] (F G : Formula Var) : structEquiv F G → ∀ val : Valuation Var Bool, eval val F = eval val G := by
  unfold structEquiv
  intro seq val
  rw [seq]

theorem substitution_thm {Var : Type} [DecidableEq Var] (F G H : Formula Var) : logicEquiv G H → logicEquiv F (substitute F G H) := by
  intro pgeqh
  unfold logicEquiv at *
  intro val
  have geqh := pgeqh val
  induction F with
  | truef =>
    unfold substitute
    split
    · rename_i h
      rw [h, geqh]
    · rw []
  | falsef =>
    unfold substitute
    split
    · rename_i h
      rw [h, geqh]
    · rw []
  | varf f =>
    unfold substitute
    split
    · rename_i h
      rw [h,geqh]
    · rw []
  | negf f ih =>
    unfold substitute
    split
    · rename_i h
      rw [h, geqh]
    · simp?
      apply Eq.symm
      exact calc
        eval val (not substitute f G H) = ! eval val (substitute f G H) := rfl
        _ = ! eval val f := by rw [← ih]
        _ = eval val (not f) := rfl
  | andf f1 f2 ih1 ih2 =>
    unfold substitute
    split
    · rename_i h
      rw [h, geqh]
    · simp?
      apply Eq.symm
      calc
        (eval val ((substitute f1 G H) and (substitute f2 G H))) = (eval val (substitute f1 G H) && eval val (substitute f2 G H)) := rfl
        _ = ((eval val f1) && (eval val f2)) := by rw [ih1, ih2]
        _ = eval val (f1 and f2) := rfl
  | orf f1 f2 ih1 ih2 =>
    unfold substitute
    split
    · rename_i h
      rw [h, geqh]
    · simp?
      apply Eq.symm
      calc
        (eval val (substitute f1 G H or substitute f2 G H)) = (eval val (substitute f1 G H) || eval val (substitute f2 G H)) := rfl
        _ = (eval val f1 || eval val f2) := by rw [ih1,ih2]
        _ = eval val (f1 or f2) := rfl
