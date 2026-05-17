import Mathlib.Data.Set.Basic

abbrev Var : Type := String

inductive LambdaTerm
  | var : Var → LambdaTerm
  | app : LambdaTerm → LambdaTerm → LambdaTerm
  | abs : Var → LambdaTerm → LambdaTerm
deriving DecidableEq, Repr

open LambdaTerm
#check LambdaTerm.recOn

instance : Coe String LambdaTerm where
  coe := LambdaTerm.var

def SyntaxEquiv (M N : LambdaTerm) : Prop :=
  M = N
local infixl:50 " ≅ " => SyntaxEquiv
namespace Subterm
def Sub (term : LambdaTerm) : Set LambdaTerm :=
  match term with
  | var v => {var v}
  | app M N => {app M N} ∪ Sub M ∪ Sub N
  | abs u M => {abs u M} ∪ Sub M

def isSubterm (M N : LambdaTerm) : Prop :=
  M ∈ Sub N

def isProperSubterm (M N : LambdaTerm) : Prop :=
  isSubterm M N ∧ ¬(SyntaxEquiv M N)

theorem reflexive : ∀ term : LambdaTerm, isSubterm term term := by
  intro term
  rw [isSubterm]
  unfold Sub
  cases term with
  | var v => simp; rfl
  | app M N => simp?; apply Or.inl; apply Or.inl; rfl
  | abs u M => simp?; apply Or.inl; rfl

theorem transitive : ∀ L M N : LambdaTerm, isSubterm L M ∧ isSubterm M N → isSubterm L N := by
  intro L M N cond
  induction N generalizing L M with
  | var n =>
    unfold isSubterm at *
    have : M = var n := cond.right
    rw [← this]
    exact cond.left
  | app n1 n2 ih1 ih2 =>
    unfold isSubterm at *
    cases cond.right with
    | inl c1 =>
      cases c1 with
      | inl c11 =>
        simp? at *
        have : M = n1.app n2 := c11
        rw [← this]
        have cl := cond.left
        exact cond.left
      | inr c12 =>
        simp? at *
        have := ih1 L M cond.left c12
        unfold Sub
        apply Or.inl
        apply Or.inr
        exact this
    | inr c2 =>
      simp? at *
      have := ih2 L M cond.left c2
      unfold Sub
      apply Or.inr
      exact this
  | abs v n ih =>
    simp? at *
    have cr := cond.right
    unfold isSubterm at cr
    unfold Sub at cr
    cases cr with
    | inl cr1 =>
      have : M = abs v n := cr1
      rw [← this]
      exact cond.left
    | inr cr2 =>
      have : isSubterm M n := cr2
      have := ih L M cond.left this
      unfold isSubterm
      unfold Sub
      apply Or.inr
      exact this

end Subterm

def FV (M : LambdaTerm) : Set Var :=
  match M with
  | var m => {m}
  | app m n => FV m ∪ FV n
  | abs x m => FV m \ {x}

def AllVar (M : LambdaTerm) : Set Var :=
  match M with
  | var m => {m}
  | app m n => AllVar m ∪ AllVar n
  | abs x m => {x} ∪ AllVar m

theorem AllVar.notInApp (y : Var) (m1 m2 : LambdaTerm) (hp : ¬(y ∈ AllVar (app m1 m2))) :
  ¬(y ∈ AllVar m1) ∧ ¬(y ∈ AllVar m2) := by
  unfold AllVar at hp
  simp? at hp
  exact hp

theorem AllVar.notInAbs (y : Var) (x : Var) (m : LambdaTerm) (hp : ¬(y ∈ AllVar (abs x m))) :
  ¬(y ∈ AllVar m) := by
  unfold AllVar at hp
  simp? at hp
  exact hp.right


def isClosed (M : LambdaTerm) : Prop :=
  FV M = ∅
abbrev isCombinator := isClosed

def Λ₀ : Type := {M : LambdaTerm // isClosed M}

def rename (M : LambdaTerm) (x y : Var) (hp : ¬(y ∈ AllVar M)) : LambdaTerm :=
  match M with
  | var v =>
    if v == x then var y
    else var v
  | app m1 m2 =>
    have := AllVar.notInApp y m1 m2 hp
    app (rename m1 x y this.left) (rename m2 x y this.right)
  | abs v m =>
    if x == v then abs v m
    else
      have := AllVar.notInAbs y v m hp
      abs v (rename m x y this)

set_option linter.style.longLine false
inductive α_equiv : LambdaTerm → LambdaTerm → Prop
  | rfl {M : LambdaTerm} : α_equiv M M
  | symm {N M : LambdaTerm} : (α_equiv N M) → α_equiv M N
  | trans {M N L : LambdaTerm} : (α_equiv M L) → (α_equiv L N) → α_equiv M N
  | rename {x : Var} {M : LambdaTerm} {y : Var} {N : LambdaTerm} : (hp : ¬(y ∈ AllVar M)) → (N = rename M x y hp) → α_equiv (abs x M) (abs y N)
  | compat_appL {L M N : LambdaTerm} : (α_equiv M N) → α_equiv (app L M) (app L N)
  | compat_appR {M N L : LambdaTerm} : (α_equiv M N) → α_equiv (app M L) (app N L)
  | compat_abs {z : Var} {M N : LambdaTerm} : (α_equiv M N) → α_equiv (abs z M) (abs z N)

local infixl:50 " =α " => α_equiv
abbrev α_convertible := α_equiv
abbrev α_variant := α_equiv

-- Assume bounded variables of M are not in N
def substitution (M : LambdaTerm) (x : Var) (N : LambdaTerm) : LambdaTerm :=
  match M with
  | var v =>
    if v == x then N
    else var v
  | app m1 m2 => app (substitution m1 x N) (substitution m2 x N)
  | abs v m =>
    if x == v then abs v m
    else abs v (substitution m x N)

theorem sub_lemma {M N L : LambdaTerm} {x y : Var} : (hxy : x≠y) → (hxL : ¬(x ∈ FV L))
  → substitution (substitution M x N) y L = substitution (substitution M y L) x (substitution N y L)
  := by sorry

def β_reduction (M N : LambdaTerm) : LambdaTerm :=
  match M with
  | var _ => M
  | app _ _ => M
  | abs x m => substitution m x N
