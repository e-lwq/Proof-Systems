open Classical
variable (A B C : Prop)

------------ HILBERT STYLE AXIOMS ------------
theorem pl1 : A → (A ∧ A) := by
  intro a
  constructor; repeat assumption


theorem pl2 : A∧B → (B∧A) := by
  intro ⟨pa,pb⟩
  constructor; repeat assumption


theorem pl3 : (A→B) → ((A∧C) → (B∧C)) := by
  intro pab ⟨pa,pc⟩
  constructor; exact pab pa; exact pc

theorem pl4 : ((A→B) ∧ (B→C)) → (A→C) := by
  intro ⟨pab,pbc⟩ pa
  have pb := pab pa
  exact pbc pb

theorem pl5 : B → (A→B) := by
  intro pb pa
  assumption

theorem pl6 : (A∧(A→B)) → B := by
  intro ⟨pa,pab⟩
  exact pab pa

theorem pl7 : A → (A∨B) := by
  intro pa
  apply Or.inl; assumption

theorem pl8 : (A∨B) → (B∨A) := by
  intro pab
  cases pab
  . case inl pa => exact Or.inr pa
  . case inr pb => exact Or.inl pb

theorem pl9 : ((A→C)∧(B→C)) → ((A∨B)→C) := by
  intro ⟨pac,pbc⟩ pab
  cases pab with
  | inl pa => exact pac pa
  | inr pb => exact pbc pb

theorem pl10 : ((A→B)∧(A→(¬B))) → (¬A) := by
  intro ⟨pab,panb⟩ pa
  have pb := pab pa
  have pnb := panb pa
  contradiction

theorem pl11 : ¬A → (A→B) := by
  intro pna pa
  contradiction
-- used intuitionistic logic

theorem pl12 : ¬¬A → A := by
  intro pnna
  apply byContradiction
  intro pna
  contradiction
-- used classical logic

------------ BOOLEAN ALGEBRA AXIOMS ------------
theorem idem1 : A∧A ↔ A := by
  apply Iff.intro
  . intro ⟨pa1,pa2⟩; assumption
  . intro pa; constructor; repeat assumption

theorem idem2 : A∨A ↔ A := by
    apply Iff.intro
    . intro paa
      cases paa <;> assumption
    . intro pa; exact Or.inl pa

theorem comm1 : A∧B ↔ B∧A := by
  apply Iff.intro
  repeat (intro ⟨pa,pb⟩; constructor <;> assumption)

theorem comm2 : A∨B ↔ B∨A := by
  apply Iff.intro
  repeat (intro pxy; cases pxy <;> first | apply Or.inl; assumption | apply Or.inr; assumption)

theorem assoc1 : (A∧B)∧C ↔ (A∧(B∧C)) := by
  apply Iff.intro
  . intro ⟨⟨pa,pb⟩,pc⟩
    constructor <;> first | assumption | constructor; repeat assumption
  . intro ⟨pa,⟨pb,pc⟩⟩
    constructor <;> first | assumption | constructor; repeat assumption

theorem assoc2 : (A∨B)∨C ↔ A∨(B∨C) := by
  apply Iff.intro
  . intro pabc
    cases pabc with
    | inl pab =>
      cases pab <;> first | apply Or.inl; assumption | apply Or.inr; apply Or.inl; assumption
    | inr pc => apply Or.inr; apply Or.inr; exact pc
  . intro pabc
    cases pabc with
    | inl pa => apply Or.inl; apply Or.inl; exact pa
    | inr pbc =>
      cases pbc <;> first | apply Or.inr; assumption | apply Or.inl; apply Or.inr; assumption

theorem absorption1 : A∧(A∨B) ↔ A := by
  apply Iff.intro
  . intro ⟨pa,pab⟩; assumption
  . intro pa; constructor; exact pa; apply Or.inl pa;

theorem absorption2 : A∨(A∧B) ↔ A := by
  apply Iff.intro
  . intro paab
    cases paab with
    | inl pa => exact pa
    | inr pab => exact pab.left
  . intro pa; apply Or.inl pa

theorem dist1 : A∧(B∨C) ↔ (A∧B)∨(A∧C) := by
  apply Iff.intro
  . intro ⟨pa,pbc⟩
    cases pbc with
    | inl pb => apply Or.inl; constructor; repeat assumption
    | inr pc => apply Or.inr; constructor; repeat assumption
  . intro pabac
    cases pabac with
    | inl pab => constructor; exact pab.left; exact (Or.inl pab.right)
    | inr pac => constructor; exact pac.left; exact (Or.inr pac.right)

theorem dist2 : A∨(B∧C) ↔ (A∨B)∧(A∨C) := by
  apply Iff.intro
  . intro pabc
    cases pabc with
    | inl pa => constructor <;> first | apply Or.inl pa | apply Or.inr pa
    | inr pbc => constructor <;> (first | apply Or.inr pbc.left | apply Or.inr pbc.right)
  . intro ⟨pab,pac⟩
    cases pab with
    | inl pa => apply Or.inl pa
    | inr pb =>
      cases pac with
      | inl pa => apply Or.inl pa
      | inr pc => apply Or.inr; constructor; repeat assumption

theorem doubleneg : ¬¬A ↔ A := by
  apply Iff.intro
  . intro pnna
    apply byContradiction
    intro pna
    exact pnna pna
  . intro pa
    intro paf
    exact paf pa
-- used classical logic

theorem demorg1 : ¬(A∧B) ↔ (¬A ∨ ¬B) := by
  apply Iff.intro
  . intro pnab
    have pa := em A
    cases pa with
    | inr pna => apply Or.inl; assumption
    | inl ta =>
      apply Or.inr;
      intro pb
      exact pnab ⟨ta,pb⟩
  . intro pnanb
    cases pnanb <;> intro ⟨pa,pb⟩ <;> contradiction
-- used classical logic

theorem demorg2 : ¬(A∨B) ↔ (¬A∧¬B) := by
  apply Iff.intro
  . intro pab
    constructor <;> intro p <;> (first | exact (pab (Or.inl p)) | exact (pab (Or.inr p)))
  . intro ⟨pna,pnb⟩
    intro pab
    cases pab <;> contradiction

theorem comp1 : A∨¬A ↔ True := by
  apply Iff.intro
  . intros; apply True.intro
  . intros; exact em A
-- used classical logic

theorem comp2 : A∧¬A ↔ False := by
  apply Iff.intro
  . intro ⟨pa,pna⟩; contradiction
  . intros; apply False.elim; assumption;
-- used intuitionistic logic

theorem zero1 : A ∨ True ↔ True := by
  apply Iff.intro
  . intros; exact True.intro
  . intros; exact (Or.inr True.intro)

theorem zero2 : A ∧ False ↔ False := by
  apply Iff.intro
  . intro ⟨pa,pf⟩; assumption
  . intros; apply False.elim; assumption
-- used intuitionistic logic

theorem id1 : A ∨ False ↔ A := by
  apply Iff.intro
  . intro paf
    cases paf <;> (first | assumption | apply False.elim; assumption)
  . intro pa
    exact (Or.inl pa)
-- used intuitionistic logic

theorem id2 : A ∧ True ↔ A := by
  apply Iff.intro
  . intro ⟨pa,pt⟩; assumption
  . intro pa; constructor; assumption; exact True.intro
