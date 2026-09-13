/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Witt decomposition

Over a field in which `2` is invertible, every regular quadratic form on a finite-dimensional
space is isometric to an orthogonal sum of hyperbolic planes and an anisotropic form, and both
the number of planes and the anisotropic summand are determined by the isometry class. The number
of planes is the *Witt index* and the last summand is the *anisotropic part*.

The material rests on two earlier results of this library: the hyperbolic splitting theorem
`TauCeti.exists_hyperbolicPlane_prod_equivalent` gives the existence of the decomposition, and
Witt cancellation, in the form of the `IsCancelAdd (TauCeti.RegularFormClass K)` instance, gives
its uniqueness.

Both statements are phrased on `TauCeti.RegularFormClass K`, the isometry classes of regular
forms, whose addition is orthogonal sum. `m` hyperbolic planes are then `m • hyperbolicClass K`,
so the decomposition reads `c = m • hyperbolicClass K + a`, and the invariance of the Witt index
and of the anisotropic part under isometry is automatic. `TauCeti.hyperbolicPresentation` names
the diagonal presentation `⟨1, -1, …, 1, -1⟩` realising `m • hyperbolicClass K`, which is what
turns the statement back into an isometry of quadratic forms in
`QuadraticForm.exists_equivalent_hyperbolicPresentation_prod`.

This file treats the regular case, which is the case the Witt ring needs. A form with a nonzero
radical is the orthogonal sum of the zero form on its radical and a regular form, and its Witt
decomposition follows from the regular one.

## Main definitions

* `TauCeti.hyperbolicClass`: the isometry class of the hyperbolic plane.
* `TauCeti.hyperbolicPresentation`: the diagonal presentation of `m` hyperbolic planes.
* `TauCeti.RegularFormClass.Anisotropic`: anisotropy of an isometry class.
* `TauCeti.RegularFormClass.wittIndex`: the number of hyperbolic planes in a class.
* `TauCeti.RegularFormClass.anisotropicPart`: the anisotropic summand of a class.

## Main results

* `TauCeti.exists_nsmul_hyperbolicClass_add`: **Witt decomposition** (Lam I.4.1), existence.
* `TauCeti.eq_of_nsmul_hyperbolicClass_add_eq`: **Witt decomposition**, uniqueness of both the
  number of hyperbolic planes and the anisotropic summand.
* `TauCeti.RegularFormClass.wittDecomposition`: the decomposition of a class by its own Witt
  index and anisotropic part.
* `TauCeti.RegularFormClass.rank_eq_two_mul_wittIndex_add`: the rank formula
  `rank c = 2 * wittIndex c + rank (anisotropicPart c)`.
* `QuadraticForm.exists_equivalent_hyperbolicPresentation_prod`: the decomposition read as an
  isometry of quadratic forms.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §4.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v

variable {K : Type u} [Field K]

/-! ### Hyperbolic presentations and hyperbolic classes -/

section Hyperbolic

variable [Invertible (2 : K)]

/-- The diagonal presentation `⟨1, -1⟩` presents the hyperbolic plane. -/
theorem presentedForm_one_neg_one :
    presentedForm (⟨2, ![1, -1]⟩ : RegularFormPresentation K) = hyperbolicPlane K := by
  ext x
  rw [presentedForm_apply, hyperbolicPlane_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, Units.val_neg, one_mul,
    neg_mul]
  ring

/-- The isometry class of the hyperbolic plane `⟨1, -1⟩`.

As with `TauCeti.hyperbolicPlane`, the invertibility hypothesis is not used by the formula; it
confines the definition to characteristic not two, where `⟨1, -1⟩` is the hyperbolic plane. -/
def hyperbolicClass (K : Type u) [Field K] [_i2 : Invertible (2 : K)] : RegularFormClass K :=
  Quotient.mk (regularFormSetoid K) ⟨2, ![1, -1]⟩

/-- The hyperbolic class is the class of the presentation `⟨1, -1⟩`. -/
theorem hyperbolicClass_def :
    hyperbolicClass K = Quotient.mk (regularFormSetoid K) ⟨2, ![1, -1]⟩ := by
  rw [hyperbolicClass]

/-- The hyperbolic class has rank two. -/
@[simp]
theorem rank_hyperbolicClass : RegularFormClass.rank (hyperbolicClass K) = 2 := by
  rw [hyperbolicClass_def, RegularFormClass.rank_mk]

/-- The class of the hyperbolic plane, as a form, is the hyperbolic class. -/
@[simp]
theorem formClass_hyperbolicPlane :
    formClass (hyperbolicPlane K) nondegenerate_hyperbolicPlane = hyperbolicClass K := by
  rw [hyperbolicClass_def]
  refine formClass_mk _ _ _ ?_
  rw [presentedForm_one_neg_one]
  exact QuadraticMap.Equivalent.refl _

/-- The diagonal presentation `⟨1, -1, …, 1, -1⟩` of `m` hyperbolic planes. -/
def hyperbolicPresentation (K : Type u) [Field K] [_i2 : Invertible (2 : K)] :
    ℕ → RegularFormPresentation K
  | 0 => ⟨0, Fin.elim0⟩
  | m + 1 => RegularFormPresentation.append ⟨2, ![1, -1]⟩ (hyperbolicPresentation K m)

/-- `m` hyperbolic planes are presented by `2 * m` weights. -/
@[simp]
theorem fst_hyperbolicPresentation (m : ℕ) : (hyperbolicPresentation K m).1 = 2 * m := by
  induction m with
  | zero => rw [hyperbolicPresentation]
  | succ m ih =>
    rw [hyperbolicPresentation, RegularFormPresentation.fst_append, ih]
    ring

/-- The presentation of `m` hyperbolic planes presents the `m`-fold sum of the hyperbolic
class. -/
@[simp]
theorem mk_hyperbolicPresentation (m : ℕ) :
    Quotient.mk (regularFormSetoid K) (hyperbolicPresentation K m) = m • hyperbolicClass K := by
  induction m with
  | zero => rw [hyperbolicPresentation, zero_nsmul, RegularFormClass.zero_def]
  | succ m ih =>
    rw [hyperbolicPresentation, ← RegularFormClass.mk_add_mk, ih, succ_nsmul',
      hyperbolicClass_def]

end Hyperbolic

/-! ### Anisotropic classes -/

/-- An isometry class is anisotropic when the forms in it are: being anisotropic is an isometry
invariant, by `QuadraticMap.Equivalent.anisotropic_iff`, so it descends to the classes. -/
def RegularFormClass.Anisotropic (c : RegularFormClass K) : Prop :=
  Quotient.liftOn c (fun p => (presentedForm p).Anisotropic) fun _ _ h =>
    propext h.anisotropic_iff

/-- A class is anisotropic exactly when one, equivalently every, presented form in it is. -/
@[simp]
theorem RegularFormClass.anisotropic_mk (p : RegularFormPresentation K) :
    RegularFormClass.Anisotropic (Quotient.mk (regularFormSetoid K) p) ↔
      (presentedForm p).Anisotropic := by
  rw [RegularFormClass.Anisotropic, Quotient.liftOn_mk]

/-- The rank-zero class is anisotropic: its space has no nonzero vector. -/
@[simp]
theorem RegularFormClass.anisotropic_zero :
    RegularFormClass.Anisotropic (0 : RegularFormClass K) := by
  rw [RegularFormClass.zero_def, RegularFormClass.anisotropic_mk]
  intro x _
  exact Subsingleton.elim x 0

section Hyperbolic

variable [Invertible (2 : K)]

/-- A hyperbolic plane is isotropic, so an orthogonal sum with one is never anisotropic. -/
theorem _root_.QuadraticForm.not_anisotropic_hyperbolicPlane_prod {W : Type v} [AddCommGroup W]
    [Module K W] (R : QuadraticForm K W) : ¬ ((hyperbolicPlane K).prod R).Anisotropic := by
  rw [QuadraticMap.not_anisotropic_iff_exists]
  refine ⟨(![1, 1], 0), fun hzero => ?_, ?_⟩
  · have h := congrFun (congrArg Prod.fst hzero) 0
    simp at h
  · simp [QuadraticMap.prod_apply]

/-- A class with a hyperbolic summand is not anisotropic. -/
theorem not_anisotropic_hyperbolicClass_add (c : RegularFormClass K) :
    ¬ RegularFormClass.Anisotropic (hyperbolicClass K + c) := by
  induction c using Quotient.inductionOn with
  | _ p =>
    rw [hyperbolicClass_def, RegularFormClass.mk_add_mk, RegularFormClass.anisotropic_mk]
    intro hani
    refine QuadraticForm.not_anisotropic_hyperbolicPlane_prod (presentedForm p) ?_
    rw [← presentedForm_one_neg_one]
    exact (equivalent_presentedForm_append_prod _ p).anisotropic_iff.mp hani

/-- A class with at least one hyperbolic plane split off is not anisotropic. -/
theorem not_anisotropic_succ_nsmul_hyperbolicClass_add (m : ℕ) (c : RegularFormClass K) :
    ¬ RegularFormClass.Anisotropic ((m + 1) • hyperbolicClass K + c) := by
  rw [succ_nsmul', add_assoc]
  exact not_anisotropic_hyperbolicClass_add _

end Hyperbolic

/-! ### The decomposition -/

section Decomposition

variable [Invertible (2 : K)]

-- Existence of a Witt decomposition, by strong induction on the rank: an isotropic class splits
-- off a hyperbolic plane and drops its rank by two.
private theorem exists_nsmul_hyperbolicClass_add_aux (n : ℕ) :
    ∀ c : RegularFormClass K, RegularFormClass.rank c = n →
      ∃ (m : ℕ) (a : RegularFormClass K),
        RegularFormClass.Anisotropic a ∧ c = m • hyperbolicClass K + a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc
    induction c using Quotient.inductionOn with
    | _ p =>
      by_cases hani : (presentedForm p).Anisotropic
      · exact ⟨0, Quotient.mk (regularFormSetoid K) p,
          (RegularFormClass.anisotropic_mk p).mpr hani, by rw [zero_nsmul, zero_add]⟩
      · obtain ⟨q, hq⟩ := exists_hyperbolicPlane_prod_equivalent (presentedForm p)
          (nondegenerate_presentedForm p) hani
        have hsplit : (Quotient.mk (regularFormSetoid K) p : RegularFormClass K) =
            hyperbolicClass K + Quotient.mk (regularFormSetoid K) q := by
          rw [hyperbolicClass_def, RegularFormClass.mk_add_mk, RegularFormClass.mk_eq_mk_iff]
          refine hq.trans ?_
          rw [← presentedForm_one_neg_one]
          exact (equivalent_presentedForm_append_prod _ q).symm
        have hrank : RegularFormClass.rank (Quotient.mk (regularFormSetoid K) q) < n := by
          have := congrArg RegularFormClass.rank hsplit
          rw [hc, RegularFormClass.rank_add, rank_hyperbolicClass] at this
          omega
        obtain ⟨m, a, ha, heq⟩ := ih _ hrank _ rfl
        exact ⟨m + 1, a, ha, by rw [hsplit, heq, succ_nsmul', add_assoc]⟩

/-- **Witt decomposition** (Lam I.4.1), existence: every isometry class of regular forms is the
orthogonal sum of a number of hyperbolic planes and an anisotropic class. -/
theorem exists_nsmul_hyperbolicClass_add (c : RegularFormClass K) :
    ∃ (m : ℕ) (a : RegularFormClass K),
      RegularFormClass.Anisotropic a ∧ c = m • hyperbolicClass K + a :=
  exists_nsmul_hyperbolicClass_add_aux _ c rfl

-- Uniqueness of a Witt decomposition when the number of planes on the left is the smaller one.
-- The statement is symmetric in the two decompositions, so this is the whole content.
private theorem eq_of_nsmul_hyperbolicClass_add_eq_aux {m m' : ℕ} {a a' : RegularFormClass K}
    (hmm : m ≤ m') (ha : RegularFormClass.Anisotropic a)
    (h : m • hyperbolicClass K + a = m' • hyperbolicClass K + a') : m = m' ∧ a = a' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmm
  rw [add_nsmul, add_assoc] at h
  have hk : a = k • hyperbolicClass K + a' := add_left_cancel h
  match k with
  | 0 => exact ⟨by omega, by rwa [zero_nsmul, zero_add] at hk⟩
  | j + 1 => exact absurd (hk ▸ ha) (not_anisotropic_succ_nsmul_hyperbolicClass_add j a')

/-- **Witt decomposition** (Lam I.4.1), uniqueness: the number of hyperbolic planes and the
anisotropic summand are determined by the class. -/
theorem eq_of_nsmul_hyperbolicClass_add_eq {m m' : ℕ} {a a' : RegularFormClass K}
    (ha : RegularFormClass.Anisotropic a) (ha' : RegularFormClass.Anisotropic a')
    (h : m • hyperbolicClass K + a = m' • hyperbolicClass K + a') : m = m' ∧ a = a' := by
  rcases le_total m m' with hmm | hmm
  · exact eq_of_nsmul_hyperbolicClass_add_eq_aux hmm ha h
  · obtain ⟨h₁, h₂⟩ := eq_of_nsmul_hyperbolicClass_add_eq_aux hmm ha' h.symm
    exact ⟨h₁.symm, h₂.symm⟩

/-- The **Witt index** of an isometry class of regular forms: the number of hyperbolic planes in
its Witt decomposition. -/
noncomputable def RegularFormClass.wittIndex (c : RegularFormClass K) : ℕ :=
  (exists_nsmul_hyperbolicClass_add c).choose

/-- The **anisotropic part** of an isometry class of regular forms: the anisotropic summand of
its Witt decomposition. -/
noncomputable def RegularFormClass.anisotropicPart (c : RegularFormClass K) :
    RegularFormClass K :=
  (exists_nsmul_hyperbolicClass_add c).choose_spec.choose

/-- The anisotropic part of a class is anisotropic. -/
theorem RegularFormClass.anisotropic_anisotropicPart (c : RegularFormClass K) :
    RegularFormClass.Anisotropic (RegularFormClass.anisotropicPart c) :=
  (exists_nsmul_hyperbolicClass_add c).choose_spec.choose_spec.1

/-- **Witt decomposition**: a class is its Witt index worth of hyperbolic planes plus its
anisotropic part. -/
theorem RegularFormClass.wittDecomposition (c : RegularFormClass K) :
    c = RegularFormClass.wittIndex c • hyperbolicClass K +
      RegularFormClass.anisotropicPart c :=
  (exists_nsmul_hyperbolicClass_add c).choose_spec.choose_spec.2

/-- Any Witt decomposition of a class computes its Witt index. -/
theorem RegularFormClass.wittIndex_eq {c a : RegularFormClass K} {m : ℕ}
    (ha : RegularFormClass.Anisotropic a) (h : c = m • hyperbolicClass K + a) :
    RegularFormClass.wittIndex c = m :=
  (eq_of_nsmul_hyperbolicClass_add_eq (RegularFormClass.anisotropic_anisotropicPart c) ha
    ((RegularFormClass.wittDecomposition c).symm.trans h)).1

/-- Any Witt decomposition of a class computes its anisotropic part. -/
theorem RegularFormClass.anisotropicPart_eq {c a : RegularFormClass K} {m : ℕ}
    (ha : RegularFormClass.Anisotropic a) (h : c = m • hyperbolicClass K + a) :
    RegularFormClass.anisotropicPart c = a :=
  (eq_of_nsmul_hyperbolicClass_add_eq (RegularFormClass.anisotropic_anisotropicPart c) ha
    ((RegularFormClass.wittDecomposition c).symm.trans h)).2

-- The Witt decomposition of `c` with `m` further hyperbolic planes adjoined.
private theorem nsmul_hyperbolicClass_add_wittDecomposition (m : ℕ) (c : RegularFormClass K) :
    m • hyperbolicClass K + c =
      (m + RegularFormClass.wittIndex c) • hyperbolicClass K +
        RegularFormClass.anisotropicPart c := by
  conv_lhs => rw [RegularFormClass.wittDecomposition c]
  rw [← add_assoc, ← add_nsmul]

/-- Adjoining `m` hyperbolic planes raises the Witt index by `m`. -/
@[simp]
theorem RegularFormClass.wittIndex_nsmul_hyperbolicClass_add (m : ℕ) (c : RegularFormClass K) :
    RegularFormClass.wittIndex (m • hyperbolicClass K + c) =
      m + RegularFormClass.wittIndex c :=
  RegularFormClass.wittIndex_eq (RegularFormClass.anisotropic_anisotropicPart c)
    (nsmul_hyperbolicClass_add_wittDecomposition m c)

/-- Adjoining hyperbolic planes leaves the anisotropic part unchanged. -/
@[simp]
theorem RegularFormClass.anisotropicPart_nsmul_hyperbolicClass_add (m : ℕ)
    (c : RegularFormClass K) :
    RegularFormClass.anisotropicPart (m • hyperbolicClass K + c) =
      RegularFormClass.anisotropicPart c :=
  RegularFormClass.anisotropicPart_eq (RegularFormClass.anisotropic_anisotropicPart c)
    (nsmul_hyperbolicClass_add_wittDecomposition m c)

/-- The rank-zero class has Witt index zero. -/
@[simp]
theorem RegularFormClass.wittIndex_zero :
    RegularFormClass.wittIndex (0 : RegularFormClass K) = 0 :=
  RegularFormClass.wittIndex_eq (m := 0) RegularFormClass.anisotropic_zero
    (by rw [zero_nsmul, add_zero])

/-- The anisotropic part of the rank-zero class is itself. -/
@[simp]
theorem RegularFormClass.anisotropicPart_zero :
    RegularFormClass.anisotropicPart (0 : RegularFormClass K) = 0 :=
  RegularFormClass.anisotropicPart_eq (m := 0) RegularFormClass.anisotropic_zero
    (by rw [zero_nsmul, add_zero])

/-- An anisotropic class has Witt index zero, and conversely. -/
@[simp]
theorem RegularFormClass.wittIndex_eq_zero_iff {c : RegularFormClass K} :
    RegularFormClass.wittIndex c = 0 ↔ RegularFormClass.Anisotropic c := by
  refine ⟨fun h => ?_, fun h => RegularFormClass.wittIndex_eq h (by rw [zero_nsmul, zero_add])⟩
  have hc := RegularFormClass.wittDecomposition c
  rw [h, zero_nsmul, zero_add] at hc
  exact hc ▸ RegularFormClass.anisotropic_anisotropicPart c

/-- An anisotropic class is its own anisotropic part. -/
theorem RegularFormClass.anisotropicPart_eq_self {c : RegularFormClass K}
    (hc : RegularFormClass.Anisotropic c) : RegularFormClass.anisotropicPart c = c :=
  RegularFormClass.anisotropicPart_eq hc (by rw [zero_nsmul, zero_add])

/-- The hyperbolic plane has Witt index one. -/
@[simp]
theorem RegularFormClass.wittIndex_hyperbolicClass :
    RegularFormClass.wittIndex (hyperbolicClass K) = 1 :=
  RegularFormClass.wittIndex_eq RegularFormClass.anisotropic_zero (by rw [one_nsmul, add_zero])

/-- The hyperbolic plane has no anisotropic part. -/
@[simp]
theorem RegularFormClass.anisotropicPart_hyperbolicClass :
    RegularFormClass.anisotropicPart (hyperbolicClass K) = 0 :=
  RegularFormClass.anisotropicPart_eq RegularFormClass.anisotropic_zero
    (by rw [one_nsmul, add_zero])

/-- The rank of a class splits as twice its Witt index plus the rank of its anisotropic part. -/
theorem RegularFormClass.rank_eq_two_mul_wittIndex_add (c : RegularFormClass K) :
    RegularFormClass.rank c =
      2 * RegularFormClass.wittIndex c +
        RegularFormClass.rank (RegularFormClass.anisotropicPart c) := by
  conv_lhs => rw [RegularFormClass.wittDecomposition c]
  rw [RegularFormClass.rank_add, ← mk_hyperbolicPresentation, RegularFormClass.rank_mk,
    fst_hyperbolicPresentation]

/-- Twice the Witt index is at most the rank. -/
theorem RegularFormClass.two_mul_wittIndex_le_rank (c : RegularFormClass K) :
    2 * RegularFormClass.wittIndex c ≤ RegularFormClass.rank c := by
  rw [RegularFormClass.rank_eq_two_mul_wittIndex_add c]
  exact Nat.le_add_right _ _

end Decomposition

/-! ### The decomposition of a form -/

section Form

variable [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A regular form is anisotropic exactly when its isometry class is. -/
@[simp]
theorem _root_.QuadraticForm.anisotropic_formClass (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) :
    RegularFormClass.Anisotropic (formClass Q hQ) ↔ Q.Anisotropic := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.anisotropic_mk]
  exact hp.anisotropic_iff.symm

/-- **Witt decomposition** for a regular form: a nondegenerate quadratic form on a
finite-dimensional space is isometric to the orthogonal sum of `m` hyperbolic planes and an
anisotropic diagonal form, and `m` is the Witt index of its class. -/
theorem _root_.QuadraticForm.exists_equivalent_hyperbolicPresentation_prod (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) :
    ∃ p : RegularFormPresentation K, (presentedForm p).Anisotropic ∧
      Module.finrank K V = 2 * RegularFormClass.wittIndex (formClass Q hQ) + p.1 ∧
      Q.Equivalent ((presentedForm
        (hyperbolicPresentation K (RegularFormClass.wittIndex (formClass Q hQ)))).prod
          (presentedForm p)) := by
  set m := RegularFormClass.wittIndex (formClass Q hQ) with hm
  obtain ⟨p, hp⟩ := Quotient.exists_rep (RegularFormClass.anisotropicPart (formClass Q hQ))
  have hani : (presentedForm p).Anisotropic := by
    rw [← RegularFormClass.anisotropic_mk, hp]
    exact RegularFormClass.anisotropic_anisotropicPart _
  refine ⟨p, hani, ?_, ?_⟩
  · have hrank := RegularFormClass.rank_eq_two_mul_wittIndex_add (formClass Q hQ)
    rw [rank_formClass, ← hp, RegularFormClass.rank_mk] at hrank
    exact hrank
  · have hclass : formClass Q hQ = Quotient.mk (regularFormSetoid K)
        (RegularFormPresentation.append (hyperbolicPresentation K m) p) := by
      rw [← RegularFormClass.mk_add_mk, mk_hyperbolicPresentation, hp, hm]
      exact RegularFormClass.wittDecomposition _
    obtain ⟨r, hr⟩ := exists_presentedForm_equivalent Q hQ
    rw [formClass_mk Q hQ r hr, RegularFormClass.mk_eq_mk_iff] at hclass
    exact (hr.trans hclass).trans (equivalent_presentedForm_append_prod _ p)

end Form

/-! ### Worked examples -/

/-- **Worked example.** The binary form `⟨1, 1⟩` over `ℚ` is anisotropic, because a sum of two
rational squares vanishes only at the origin. -/
theorem anisotropic_presentedForm_one_one :
    (presentedForm (⟨2, ![1, 1]⟩ : RegularFormPresentation ℚ)).Anisotropic := by
  intro x hx
  rw [presentedForm_apply, Fin.sum_univ_two] at hx
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, one_mul] at hx
  have h0 : x 0 = 0 := by nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1)]
  have h1 : x 1 = 0 := by nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1)]
  funext i
  fin_cases i <;> simp [h0, h1]

/-- **Worked example.** The positive definite form `⟨1, 1⟩` over `ℚ` has Witt index `0`, while
the hyperbolic plane has Witt index `1`: both values occur in rank two. -/
example :
    RegularFormClass.wittIndex
        (Quotient.mk (regularFormSetoid ℚ) ⟨2, ![1, 1]⟩) = 0 ∧
      RegularFormClass.wittIndex (hyperbolicClass ℚ) = 1 :=
  ⟨RegularFormClass.wittIndex_eq_zero_iff.mpr
    ((RegularFormClass.anisotropic_mk _).mpr anisotropic_presentedForm_one_one),
    RegularFormClass.wittIndex_hyperbolicClass⟩

end TauCeti
