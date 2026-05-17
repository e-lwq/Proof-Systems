import ProofSystems.propositional_logic.definitions

open Formula
open List

namespace BoolAxioms
def flip (x : α × β) : β × α := (x.2,x.1)

variable {Var : Type} [DecidableEq Var]
variable (A : Formula Var) (B : Formula Var) (C : Formula Var)
def idem1L := (A and A, A)
def idem1R := flip (idem1L A)
def idem2L := ((A or A), A)
def idem2R := flip (idem2L A)
def comm1L := (A and B, B and A)
def comm1R := flip (comm1L A B)
def comm2L := (A or B, B or A)
def comm2R := flip (comm2L A B)
def assoc1L := ((A and B) and C, A and (B and C))
def assoc1R := flip (assoc1L A B C)
def assoc2L := ((A or B) or C, A or (B or C))
def assoc2R := flip (assoc2L A B C)
def absorb1L := ((A and (A or B)), A)
def absorb1R := flip (absorb1L A B)
def absorb2L := (A or (A and B), A)
def absorb2R := flip (absorb2L A B)
def distrib1L := (A and (B or C), (A and B) or (A and C))
def distrib1R := flip (distrib1L A B C)
def distrib2L := (A or (B and C), (A or B) and (A or C))
def distrib2R := flip (distrib2L A B C)
def doubnegL := (not not A, A)
def doubnegR := flip (doubnegL A)
def demorg1L := (not (A and B), not A or not B)
def demorg1R := flip (demorg1L A B)
def demorg2L := (not (A or B), not A and not B)
def demorg2R := flip (demorg2L A B)
def comp1L := (A or not A, truef (Var := Var))
def comp1R := flip (comp1L A)
def comp2L := (A and not A, falsef (Var := Var))
def comp2R := flip (comp2L A)
def zero1L := (A or truef (Var := Var), truef (Var := Var))
def zero1R := flip (zero1L A)
def zero2L := (A and falsef (Var := Var), falsef (Var := Var))
def zero2R := flip (zero2L A)
def id1L := (A or falsef (Var := Var), A)
def id1R := flip (id1L A)
def id2L := (A and truef (Var := Var), A)
def id2R := flip (id2L A)
end BoolAxioms

inductive Rule {Var : Type} [DecidableEq Var]
  | idem1L : Formula Var → Rule
  | idem1R : Formula Var → Rule
  | idem2L : Formula Var → Rule
  | idem2R : Formula Var → Rule
  | comm1L : Formula Var → Formula Var → Rule
  | comm1R : Formula Var → Formula Var → Rule
  | comm2L : Formula Var → Formula Var → Rule
  | comm2R : Formula Var → Formula Var → Rule
  | assoc1L : Formula Var → Formula Var → Formula Var → Rule
  | assoc1R : Formula Var → Formula Var → Formula Var → Rule
  | assoc2L : Formula Var → Formula Var → Formula Var → Rule
  | assoc2R : Formula Var → Formula Var → Formula Var → Rule
  | absorb1L : Formula Var → Formula Var → Rule
  | absorb1R : Formula Var → Formula Var → Rule
  | absorb2L : Formula Var → Formula Var → Rule
  | absorb2R : Formula Var → Formula Var → Rule
  | distrib1L : Formula Var → Formula Var → Formula Var → Rule
  | distrib1R : Formula Var → Formula Var → Formula Var → Rule
  | distrib2L : Formula Var → Formula Var → Formula Var → Rule
  | distrib2R : Formula Var → Formula Var → Formula Var → Rule
  | doubnegL : Formula Var → Rule
  | doubnegR : Formula Var → Rule
  | demorg1L : Formula Var → Formula Var → Rule
  | demorg1R : Formula Var → Formula Var → Rule
  | demorg2L : Formula Var → Formula Var → Rule
  | demorg2R : Formula Var → Formula Var → Rule
  | comp1L : Formula Var → Rule
  | comp1R : Formula Var → Rule
  | comp2L : Formula Var → Rule
  | comp2R : Formula Var → Rule
  | zero1L : Formula Var → Rule
  | zero1R : Formula Var → Rule
  | zero2L : Formula Var → Rule
  | zero2R : Formula Var → Rule
  | id1L : Formula Var → Rule
  | id1R : Formula Var → Rule
  | id2L : Formula Var → Rule
  | id2R : Formula Var → Rule
open Rule

def genPair {Var : Type} [DecidableEq Var] (rule : Rule (Var := Var)) : Formula Var × Formula Var :=
  match rule with
  | idem1L A => BoolAxioms.idem1L A
  | idem1R A => BoolAxioms.idem1R A
  | idem2L A => BoolAxioms.idem2L A
  | idem2R A => BoolAxioms.idem2R A
  | comm1L A B => BoolAxioms.comm1L A B
  | comm1R A B => BoolAxioms.comm1R A B
  | comm2L A B => BoolAxioms.comm2L A B
  | comm2R A B => BoolAxioms.comm2R A B
  | assoc1L A B C => BoolAxioms.assoc1L A B C
  | assoc1R A B C => BoolAxioms.assoc1R A B C
  | assoc2L A B C => BoolAxioms.assoc2L A B C
  | assoc2R A B C => BoolAxioms.assoc2R A B C
  | absorb1L A B => BoolAxioms.absorb1L A B
  | absorb1R A B => BoolAxioms.absorb1R A B
  | absorb2L A B => BoolAxioms.absorb2L A B
  | absorb2R A B => BoolAxioms.absorb2R A B
  | distrib1L A B C => BoolAxioms.distrib1L A B C
  | distrib1R A B C => BoolAxioms.distrib1R A B C
  | distrib2L A B C => BoolAxioms.distrib2L A B C
  | distrib2R A B C => BoolAxioms.distrib2R A B C
  | doubnegL A => BoolAxioms.doubnegL A
  | doubnegR A => BoolAxioms.doubnegR A
  | demorg1L A B => BoolAxioms.demorg1L A B
  | demorg1R A B => BoolAxioms.demorg1R A B
  | demorg2L A B => BoolAxioms.demorg2L A B
  | demorg2R A B => BoolAxioms.demorg2R A B
  | comp1L A => BoolAxioms.comp1L A
  | comp1R A => BoolAxioms.comp1R A
  | comp2L A => BoolAxioms.comp2L A
  | comp2R A => BoolAxioms.comp2R A
  | zero1L A => BoolAxioms.zero1L A
  | zero1R A => BoolAxioms.zero1R A
  | zero2L A => BoolAxioms.zero2L A
  | zero2R A => BoolAxioms.zero2R A
  | id1L A => BoolAxioms.id1L A
  | id1R A => BoolAxioms.id1R A
  | id2L A => BoolAxioms.id2L A
  | id2R A => BoolAxioms.id2R A

set_option linter.style.longLine false
def correct_deriv_type {Var : Type} [DecidableEq Var] (LHS RHS : Formula Var) (rule : Rule (Var := Var)) : Prop :=
  have pair := genPair rule
  substitute LHS pair.1 pair.2 = RHS

structure dstep {Var : Type} [DecidableEq Var] where
  LHS : Formula Var
  RHS : Formula Var
  rule : Rule (Var:=Var)
  correct_deriv : correct_deriv_type LHS RHS rule

def pairfun {Var : Type} [DecidableEq Var] := fun step_pair : dstep (Var := Var) × dstep => step_pair.1.RHS = step_pair.2.LHS

def hchain_type {Var : Type} [DecidableEq Var] (p : dstep (Var := Var) × dstep (Var := Var) → Prop) (steps : List (dstep (Var := Var))) : Prop :=
  have ll := myZip steps steps.tail
  Forall p ll

structure derivation {Var : Type} [DecidableEq Var] where
  steps : List (dstep (Var := Var))
  hchain : hchain_type pairfun steps
  notnull : steps ≠ []
