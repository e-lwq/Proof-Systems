import Mathlib.Data.Finset.Basic
import ProofSystems.propositional_logic.definitions

open Formula

inductive Literal (α : Type) where
  | pl : α → Literal α
  | nl : α → Literal α
deriving DecidableEq, Repr
open Literal

def notl (l : Literal t) : Literal t :=
  match l with
  | pl v => nl v
  | nl v => pl v

abbrev Clause (t : Type) := List (Literal t)
abbrev Setc (t : Type) := List (Clause t)

def varAssignType (α β : Type) [DecidableEq α] : Type := α → β
def litAssignType (α β : Type) [DecidableEq α] : Type := varAssignType α β → Literal α → β
def clauseAssignType (α β : Type) [DecidableEq α] : Type := varAssignType α β → Clause α → β
def setcAssignType (α β : Type) [DecidableEq α] : Type := varAssignType α β → Setc α → β

def varAssignment : varAssignType String Bool :=
  fun p =>
    match p with
    | "x" => true
    | "y" => false
    | _ => false

def evalLit {α : Type} [DecidableEq α] : litAssignType α Bool :=
  fun varassign => fun literal =>
    match literal with
    | pl v => varassign v
    | nl v => ! varassign v

def evalClause {α : Type} [DecidableEq α] : clauseAssignType α Bool :=
  fun varassign => fun clause =>
    List.any clause (evalLit varassign)

def evalSetc {α : Type} [DecidableEq α] : setcAssignType α Bool :=
  fun varassign => fun setc =>
    List.all setc (evalClause varassign)

set_option linter.style.longLine false
def satClause {α : Type} [DecidableEq α] (varassign : varAssignType α Bool) (clause : Clause α) : Prop :=
  evalClause varassign clause = true

def satSet {α : Type} [DecidableEq α] (varassign : varAssignType α Bool) (sc : Setc α) : Prop :=
  evalSetc varassign sc = true

def SetcLogicEquiv {α : Type} [DecidableEq α] (F G : Setc α) : Prop :=
  ∀ (varassign : varAssignType α Bool), evalSetc varassign F = evalSetc varassign G

------------------ RESOLUTION ------------------
-- resolve C1, C2 where p ∈ C1, ¬p ∈ C2
def resolve [DecidableEq α] (C1 C2 : Clause α) (p : Literal α) : Option (Clause α) :=
  if List.contains C1 p && List.contains C2 (notl p) then
    some (List.union (List.filter (fun x => x≠p) C1) (List.filter (fun x => x≠notl p) C2))
  else none

--theorem resolution_lemma {Var : Type} [DecidableEq Var] (F : setc Var) ()

/-
Algorithm with graphs

Construct graph by:
1. each node = 1 clause
2. edge connects 2 nodes if the 2 clauses can be resolved

Simplify graph by:
1. if more than 1 edge connects 2 nodes, delete all those multi-edges
2. if a node has degree 0, delete the node

Repeat:
- choose 1 unused edge to resolve
- mark that edge as used
- new node is formed, add edges accordingly
- simplify again
until no more unused edges

If □ ∈ Res*(F), then F = unsat
else, F = sat
-/
