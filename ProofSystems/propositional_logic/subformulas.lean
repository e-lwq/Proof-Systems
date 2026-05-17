import ProofSystems.propositional_logic.definitions

---- Subformulas
def subformulas {Var : Type} [DecidableEq Var] : Formula Var → Set (Formula Var)
  | .truef => {Formula.truef}
  | .falsef => {Formula.falsef}
  | .varf v => {Formula.varf v}
  | .negf F => subformulas F ∪ {Formula.negf F}
  | .andf F G => subformulas F ∪ subformulas G ∪ {Formula.andf F G}
  | .orf F G => subformulas F ∪ subformulas G ∪ {Formula.orf F G}

set_option linter.style.cdot false
theorem subformulas_self {Var} [DecidableEq Var] : ∀ F : Formula Var, F ∈ subformulas F := by
    intro f
    unfold subformulas
    split
    . rfl
    . rfl
    . rfl
    . apply Or.inr; rfl
    . apply Or.inr; rfl
    . apply Or.inr; rfl
