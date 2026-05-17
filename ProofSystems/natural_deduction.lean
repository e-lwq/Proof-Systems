open Classical
variable (A B C : Prop)

------------ HILBERT STYLE AXIOMS ------------
theorem pl1 : A → (A ∧ A) :=
  fun pa : A => show A∧A from And.intro pa pa

theorem pl2 : A∧B → (B∧A) :=
  fun pab : A∧B =>
    have pa := pab.left
    have pb := pab.right
    show B∧A from And.intro pb pa

theorem pl3 : (A→B) → ((A∧C) → (B∧C)) :=
  fun pab : A→B => fun pac : A∧C =>
    have pa := pac.left
    have pc := pac.right
    have pb := pab pa
    show B∧C from And.intro pb pc

theorem pl4 : ((A→B) ∧ (B→C)) → (A→C) :=
  fun pabc : (A→B) ∧ (B→C) => fun pa : A =>
    have pab := pabc.left
    have pbc := pabc.right
    have pb := pab pa
    show C from pbc pb

theorem pl5 : B → (A→B) :=
  fun pb : B => fun _ : A =>
    show B from pb

theorem pl6 : (A∧(A→B)) → B :=
  fun paab : A∧(A→B) =>
    have pa := paab.left
    have pab := paab.right
    show B from pab pa

theorem pl7 : A → (A∨B) :=
  fun pa : A =>
    show A∨B from Or.inl pa

theorem pl8 : (A∨B) → (B∨A) :=
  fun pab : A∨B =>
    show B∨A from Or.elim pab
      (fun pa : A => show B∨A from Or.inr pa)
      (fun pb : B => show B∨A from Or.inl pb)

theorem pl9 : ((A→C)∧(B→C)) → ((A∨B)→C) :=
  fun pacbc : (A→C)∧(B→C) => fun pab : A∨B =>
    have pac := pacbc.left
    have pbc := pacbc.right
    show C from Or.elim pab
      (fun pa : A => show C from pac pa)
      (fun pb : B => show C from pbc pb)

theorem pl10 : ((A→B)∧(A→(¬B))) → (¬A) :=
  fun pabab : (A→B)∧(A→(¬B)) => fun pa : A =>
    have pab := pabab.left
    have panb := pabab.right
    have pb := pab pa
    have pnb := panb pa
    show False from pnb pb

theorem pl11 : ¬A → (A→B) :=
  fun pna : ¬A => fun pa : A => show B from False.elim (pna pa)
-- used intuitionistic logic

theorem pl12 : ¬¬A → A :=
  fun pnna : ¬¬A =>
    byContradiction
      fun pna : ¬A => show False from pnna pna
-- used classical logic

------------ BOOLEAN ALGEBRA AXIOMS ------------
theorem idem1 : A∧A ↔ A :=
  Iff.intro
    (fun paa : A∧A =>
      have pa := paa.left
      show A from pa)
    (fun pa : A => show A∧A from And.intro pa pa)

theorem idem2 : A∨A ↔ A :=
  Iff.intro
    (fun paa : A∨A =>
      Or.elim paa
        (fun pa : A => pa)
        (fun pa : A => pa))
    (fun pa : A => show A∨A from Or.inl pa)

theorem comm1 : A∧B ↔ B∧A :=
  Iff.intro
  (fun pab : A∧B =>
    have pa := pab.left
    have pb := pab.right
    show B∧A from And.intro pb pa)
  (fun pba : B∧A =>
    have pa := pba.right
    have pb := pba.left
    show A∧B from And.intro pa pb)

theorem comm2 : A∨B ↔ B∨A :=
  Iff.intro
    (fun pab : A∨B =>
      Or.elim pab
        (fun pa : A => show B∨A from Or.inr pa)
        (fun pb : B => show B∨A from Or.inl pb))
    (fun pba : B∨A =>
      (Or.elim pba
        (fun pb : B => show A∨B from Or.inr pb)
        (fun pa : A => show A∨B from Or.inl pa)))

theorem assoc1 : (A∧B)∧C ↔ (A∧(B∧C)) :=
  Iff.intro
    (fun pabc : (A∧B)∧C =>
      have pab := pabc.left
      have pa := pab.left
      have pb := pab.right
      have pc := pabc.right
      show A∧(B∧C) from And.intro pa (And.intro pb pc))
    (fun pabc : A∧(B∧C) =>
      have pa := pabc.left
      have pbc := pabc.right
      have pb := pbc.left
      have pc := pbc.right
      show (A∧B)∧C from And.intro (And.intro pa pb) pc)

theorem assoc2 : (A∨B)∨C ↔ A∨(B∨C) :=
  Iff.intro
    (fun pabc : (A∨B)∨C =>
      Or.elim pabc
        (fun pab : A∨B =>
          Or.elim pab
            (fun pa : A => show A∨(B∨C) from Or.inl pa)
            (fun pb : B => show A∨(B∨C) from Or.inr (Or.inl pb))
        )
        (fun pc : C => show A∨(B∨C) from Or.inr (Or.inr pc)))
    (fun pabc : (A∨(B∨C)) =>
      Or.elim pabc
        (fun pa : A => show (A∨B)∨C from Or.inl (Or.inl pa))
        (fun pbc : B∨C =>
          Or.elim pbc
            (fun pb : B => show (A∨B)∨C from Or.inl (Or.inr pb))
            (fun pc : C => show (A∨B)∨C from Or.inr pc)))

theorem absorption1 : A∧(A∨B) ↔ A :=
  Iff.intro
    (fun paab : A∧(A∨B) =>
      have pa := paab.left
      pa)
    (fun pa : A => show A∧(A∨B) from And.intro pa (Or.inl pa))

theorem absorption2 : A∨(A∧B) ↔ A :=
  Iff.intro
    (fun paab : A∨(A∧B) =>
      Or.elim paab
        (fun pa : A => pa)
        (fun pab : A∧B =>
          have pa := pab.left
          show A from pa))
    (fun pa : A => show A∨(A∧B) from Or.inl pa)

theorem dist1 : A∧(B∨C) ↔ (A∧B)∨(A∧C) :=
  Iff.intro
    (fun pabc : A∧(B∨C) =>
      have pa := pabc.left
      have pbc := pabc.right
      Or.elim pbc
        (fun pb : B => show (A∧B)∨(A∧C) from Or.inl (And.intro pa pb))
        (fun pc : C => show (A∧B)∨(A∧C) from Or.inr (And.intro pa pc)))
    (fun pabac : (A∧B)∨(A∧C) =>
      Or.elim pabac
        (fun pab : A∧B =>
          have pa := pab.left
          have pb := pab.right
          show A∧(B∨C) from And.intro pa (Or.inl pb))
        (fun pac : A∧C =>
          have pa := pac.left
          have pc := pac.right
          show A∧(B∨C) from  And.intro pa (Or.inr pc)))

theorem dist2 : A∨(B∧C) ↔ (A∨B)∧(A∨C) :=
  Iff.intro
    (fun pabc : A∨(B∧C) =>
      Or.elim pabc
        (fun pa : A =>
          show (A∨B)∧(A∨C) from And.intro (Or.inl pa) (Or.inl pa))
        (fun pbc : B∧C =>
          have pb := pbc.left
          have pc := pbc.right
          show (A∨B)∧(A∨C) from And.intro (Or.inr pb) (Or.inr pc)))
    (fun pabac : (A∨B)∧(A∨C) =>
      have pab := pabac.left
      have pac := pabac.right
      Or.elim pab
        (fun pa : A => show A∨(B∧C) from Or.inl pa)
        (fun pb : B =>
          Or.elim pac
            (fun pa : A => show A∨(B∧C) from Or.inl pa)
            (fun pc : C => show A∨(B∧C) from Or.inr (And.intro pb pc))))

theorem doubleneg : ¬¬A ↔ A :=
  Iff.intro
    (fun pnna : ¬¬A =>
      byContradiction (fun pna : ¬A => show False from pnna pna))
    (fun pa : A => fun pna : ¬A => show False from pna pa)
-- used intuitionistic logic

theorem demorg1 : ¬(A∧B) ↔ (¬A ∨ ¬B) :=
  Iff.intro
    (fun pnab : ¬(A∧B) =>
      Or.elim (em A)
        (fun pa : A => show (¬A∨¬B) from Or.inr (fun pb : B => pnab (And.intro pa pb)))
        (fun pna : ¬A => show (¬A∨¬B) from Or.inl pna))
    (fun pnanb : ¬A ∨ ¬B =>
      Or.elim pnanb
        (fun pna : ¬A => (fun pab : A∧B =>
          have pa := pab.left
          show False from pna pa))
        (fun pnb : ¬B => (fun pab : A∧B =>
          have pb := pab.right
          show False from pnb pb)))
-- used classical logic

theorem demorg2 : ¬(A∨B) ↔ (¬A∧¬B) :=
  Iff.intro
    (fun pnab : ¬(A∨B) => And.intro
      (fun pa : A => show False from pnab (Or.inl pa))
      (fun pb : B => show False from pnab (Or.inr pb)))
    (fun pnanb : ¬A∧¬B =>
      have pna := pnanb.left
      have pnb := pnanb.right
      fun pab : A∨B =>
        Or.elim pab
          (fun pa : A => show False from pna pa)
          (fun pb : B => show False from pnb pb))

theorem comp1 : A∨¬A ↔ True :=
  Iff.intro
    (fun _ : A∨¬A => True.intro)
    (fun _ : True => show A∨¬A from em A)
-- used classical logic

theorem comp2 : A∧¬A ↔ False :=
  Iff.intro
    (fun paa: A∧¬A => show False from paa.right paa.left)
    (fun pfalse : False => show A∧¬A from False.elim pfalse)
-- used intuitionistic logic

theorem zero1 : A ∨ True ↔ True :=
  Iff.intro
    (fun _ : A∨True => True.intro)
    (fun ptrue : True => show A∨True from Or.inr ptrue)

theorem zero2 : A ∧ False ↔ False :=
  Iff.intro
    (fun paf : A∧False => show False from paf.right)
    (fun pfalse : False => show A∧False from False.elim pfalse)
-- used intuitionistic logic

theorem id1 : A ∨ False ↔ A :=
  Iff.intro
    (fun paf : A∨False =>
      Or.elim paf
        (fun pa : A => pa)
        (fun pfalse : False => show A from False.elim pfalse))
    (fun pa : A => show A∨False from Or.inl pa)
-- used intuitionistic logic

theorem id2 : A ∧ True ↔ A :=
  Iff.intro
    (fun pat : A∧True => show A from pat.left)
    (fun pa : A => show A∧True from And.intro pa True.intro)
