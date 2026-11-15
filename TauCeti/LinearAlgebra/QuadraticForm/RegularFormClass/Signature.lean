/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
import TauCeti.Algebra.Group.Units.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Semiring

/-!
# Signature of regular quadratic forms over ordered fields

The integer signature is the positive index minus the negative index of inertia. It descends to
isometry classes over any ordered field, is additive under orthogonal sum, and is multiplicative
under tensor product. It therefore defines a semiring homomorphism to `ℤ` and vanishes on the
hyperbolic plane.

Over an ordered real closed field, every positive coefficient is a square. Positive lines are
therefore isometric to `⟨1⟩`, and negative lines to `⟨-1⟩`. These reductions are used to identify
the Witt ring with `ℤ` by signature.

## Main results

* `TauCeti.RegularFormClass.sigPos` and `TauCeti.RegularFormClass.sigNeg`: the positive and
  negative indices of inertia on regular-form classes.
* `TauCeti.RegularFormClass.signatureHom`: the integer signature as a semiring homomorphism.
* `TauCeti.signature_formClass`: computes signature from the inertia indices of a regular form.
* `TauCeti.RegularFormClass.mk_rankOne_eq_one_of_pos`: positive lines over real closed fields
  are isometric to the unit line.
* `TauCeti.RegularFormClass.mk_rankOne_eq_mk_neg_one_of_neg`: negative lines over real closed
  fields are isometric to the negative unit line.
* `TauCeti.RegularFormClass.eq_sigPos_nsmul_add_sigNeg_nsmul`: normal-form decomposition into
  positive and negative unit lines over ordered real closed fields.
* `TauCeti.RegularFormClass.discr_eq_sigNeg_nsmul`: the determinant-sign formula for the
  discriminant over ordered real closed fields.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §3.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The positive index of inertia of a regular-form class over an ordered field. -/
noncomputable def RegularFormClass.sigPos : RegularFormClass K → ℕ :=
  Quotient.lift (fun p => _root_.sigPos (presentedForm p))
    (fun _ _ h => h.sigPos_eq)

/-- The negative index of inertia of a regular-form class over an ordered field. -/
noncomputable def RegularFormClass.sigNeg : RegularFormClass K → ℕ :=
  Quotient.lift (fun p => _root_.sigNeg (presentedForm p))
    (fun _ _ h => h.sigNeg_eq)

/-- The integer signature of a regular-form class: its positive index minus its negative
index. -/
noncomputable def RegularFormClass.signature : RegularFormClass K → ℤ :=
  Quotient.lift (fun p => (_root_.sigPos (presentedForm p) : ℤ) - _root_.sigNeg (presentedForm p))
    (fun _ _ h => by rw [h.sigPos_eq, h.sigNeg_eq])

omit [IsStrictOrderedRing K] in
/-- The positive index of inertia of a diagonal presentation agrees with that of its presented
form. -/
@[simp]
theorem RegularFormClass.sigPos_mk (p : RegularFormPresentation K) :
    RegularFormClass.sigPos (Quotient.mk (regularFormSetoid K) p) =
      _root_.sigPos (presentedForm p) := (rfl)

omit [IsStrictOrderedRing K] in
/-- The negative index of inertia of a diagonal presentation agrees with that of its presented
form. -/
@[simp]
theorem RegularFormClass.sigNeg_mk (p : RegularFormPresentation K) :
    RegularFormClass.sigNeg (Quotient.mk (regularFormSetoid K) p) =
      _root_.sigNeg (presentedForm p) := (rfl)

omit [IsStrictOrderedRing K] in
/-- The signature of a diagonal presentation is the difference of its inertia indices. -/
@[simp]
theorem RegularFormClass.signature_mk (p : RegularFormPresentation K) :
    signature (Quotient.mk (regularFormSetoid K) p) =
      (_root_.sigPos (presentedForm p) : ℤ) - _root_.sigNeg (presentedForm p) := (rfl)

omit [IsStrictOrderedRing K] in
/-- The positive index on isometry classes agrees with that of any regular form. -/
@[simp]
theorem sigPos_formClass [Invertible (2 : K)] (Q : QuadraticForm K M) (hQ : Q.Nondegenerate) :
    RegularFormClass.sigPos (formClass Q hQ) = _root_.sigPos Q := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.sigPos_mk, hp.sigPos_eq]

omit [IsStrictOrderedRing K] in
/-- The negative index on isometry classes agrees with that of any regular form. -/
@[simp]
theorem sigNeg_formClass [Invertible (2 : K)] (Q : QuadraticForm K M) (hQ : Q.Nondegenerate) :
    RegularFormClass.sigNeg (formClass Q hQ) = _root_.sigNeg Q := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.sigNeg_mk, hp.sigNeg_eq]

omit [IsStrictOrderedRing K] in
/-- The signature on isometry classes agrees with the inertia indices of any regular form. -/
@[simp]
theorem signature_formClass [Invertible (2 : K)] (Q : QuadraticForm K M) (hQ : Q.Nondegenerate) :
    RegularFormClass.signature (formClass Q hQ) = (_root_.sigPos Q : ℤ) - _root_.sigNeg Q := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.signature_mk, hp.sigPos_eq, hp.sigNeg_eq]

namespace RegularFormClass

omit [IsStrictOrderedRing K] in
/-- The integer signature of a class is its positive index minus its negative index. -/
theorem signature_eq_sigPos_sub_sigNeg (x : RegularFormClass K) :
    signature x = (x.sigPos : ℤ) - x.sigNeg :=
  Quotient.inductionOn x fun _ => rfl

/-- The zero-dimensional form has positive index zero. -/
@[simp]
theorem sigPos_zero : sigPos (0 : RegularFormClass K) = 0 := by
  rw [zero_def, sigPos_mk, presentedForm_eq_weightedSumSquares_coe]
  simp [sigPos_weightedSumSquares, Set.eq_empty_of_isEmpty]

/-- The zero-dimensional form has negative index zero. -/
@[simp]
theorem sigNeg_zero : sigNeg (0 : RegularFormClass K) = 0 := by
  rw [zero_def, sigNeg_mk, presentedForm_eq_weightedSumSquares_coe]
  simp [sigNeg_weightedSumSquares, Set.eq_empty_of_isEmpty]

/-- The zero-dimensional form has signature zero. -/
@[simp]
theorem signature_zero : signature (0 : RegularFormClass K) = 0 := by
  rw [signature_eq_sigPos_sub_sigNeg, sigPos_zero, sigNeg_zero, sub_self]

/-- The positive index of inertia is additive under orthogonal sum. -/
@[simp]
theorem sigPos_add (x y : RegularFormClass K) :
    sigPos (x + y) = sigPos x + sigPos y :=
  Quotient.inductionOn₂ x y fun p q => by
    have h := equivalent_presentedForm_append_prod p q
    rw [mk_add_mk, sigPos_mk, sigPos_mk, sigPos_mk, h.sigPos_eq, sigPos_prod]

/-- The negative index of inertia is additive under orthogonal sum. -/
@[simp]
theorem sigNeg_add (x y : RegularFormClass K) :
    sigNeg (x + y) = sigNeg x + sigNeg y :=
  Quotient.inductionOn₂ x y fun p q => by
    have h := equivalent_presentedForm_append_prod p q
    rw [mk_add_mk, sigNeg_mk, sigNeg_mk, sigNeg_mk, h.sigNeg_eq, sigNeg_prod]

/-- Signature is additive under orthogonal sum. -/
@[simp]
theorem signature_add (x y : RegularFormClass K) :
    signature (x + y) = signature x + signature y := by
  simp only [signature_eq_sigPos_sub_sigNeg, sigPos_add, sigNeg_add, Nat.cast_add]
  ring

/-- A line has positive index `1` when its coefficient is positive and `0` otherwise. -/
@[simp 1100]
theorem sigPos_mk_rankOne (a : Kˣ) :
    sigPos (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) =
      if 0 < (a : K) then 1 else 0 := by
  rw [sigPos_mk, presentedForm_eq_weightedSumSquares_coe, sigPos_weightedSumSquares]
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha
  · simp [ha.not_gt]
  · simp [ha]

/-- A line has negative index `1` when its coefficient is negative and `0` otherwise. -/
@[simp 1100]
theorem sigNeg_mk_rankOne (a : Kˣ) :
    sigNeg (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) =
      if (a : K) < 0 then 1 else 0 := by
  rw [sigNeg_mk, presentedForm_eq_weightedSumSquares_coe, sigNeg_weightedSumSquares]
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha
  · simp [ha]
  · simp [not_lt_of_gt ha]

/-- A line has signature `1` or `-1`, according to the sign of its coefficient. -/
@[simp 1100]
theorem signature_mk_rankOne (a : Kˣ) :
    signature (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) =
      if 0 < (a : K) then 1 else -1 := by
  rw [signature_eq_sigPos_sub_sigNeg, sigPos_mk_rankOne, sigNeg_mk_rankOne]
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha
  · simp [ha, ha.not_gt]
  · simp [ha, not_lt_of_gt ha]

/-- The positive unit line has positive index one. -/
@[simp]
theorem sigPos_one : sigPos (1 : RegularFormClass K) = 1 := by
  rw [← mk_rankOne_one, sigPos_mk_rankOne]
  norm_num

/-- The positive unit line has negative index zero. -/
@[simp]
theorem sigNeg_one : sigNeg (1 : RegularFormClass K) = 0 := by
  rw [← mk_rankOne_one, sigNeg_mk_rankOne]
  norm_num

/-- The positive unit line has signature one. -/
@[simp]
theorem signature_one : signature (1 : RegularFormClass K) = 1 := by
  rw [signature_eq_sigPos_sub_sigNeg, sigPos_one, sigNeg_one]
  norm_num

/-- For any regular-form class over an ordered field, its positive and negative indices of inertia
sum to its rank. -/
theorem sigPos_add_sigNeg_eq_rank (x : RegularFormClass K) :
    x.sigPos + x.sigNeg = x.rank := by
  induction x using induction_on_rankOne with
  | zero => simp
  | add_rankOne x a ih =>
    rw [sigPos_add, sigNeg_add, rank_add, rank_mk, sigPos_mk_rankOne, sigNeg_mk_rankOne]
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha
    · simp only [ha.not_gt, ↓reduceIte, ha]
      omega
    · simp only [ha, ↓reduceIte, not_lt_of_gt ha]
      omega

variable [Invertible (2 : K)]

/-- The hyperbolic plane has signature zero. -/
@[simp]
theorem signature_hyperbolicClass : signature (hyperbolicClass K) = 0 := by
  have ht : (fun i : Fin 1 => (![1, -1] i.succ : Kˣ)) = fun _ => -1 := by
    simp
  rw [hyperbolicClass_def, mk_succ_eq_mk_rankOne_add, signature_add,
    signature_mk_rankOne, ht, signature_mk_rankOne]
  norm_num

/-- Signature is multiplicative under tensor product. -/
@[simp]
theorem signature_mul (x y : RegularFormClass K) :
    signature (x * y) = signature x * signature y := by
  have hscale (a : Kˣ) (z : RegularFormClass K) :
      signature (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ * z) =
        signature (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) * signature z := by
    induction z using Quotient.inductionOn with
    | h p =>
      have hs := formClass_smul a (presentedForm p) (nondegenerate_presentedForm p)
      rw [formClass_presentedForm] at hs
      rw [← hs, signature_formClass, signature_mk_rankOne, signature_mk]
      rcases lt_or_gt_of_ne a.ne_zero with ha | ha
      · rw [QuadraticForm.sigPos_smul_of_neg _ ha, QuadraticForm.sigNeg_smul_of_neg _ ha,
          ite_eq_right ha.not_gt]
        ring
      · rw [QuadraticForm.sigPos_smul_of_pos _ ha, QuadraticForm.sigNeg_smul_of_pos _ ha,
          ite_eq_left ha, one_mul]
  induction x using induction_on_rankOne with
  | zero => simp
  | add_rankOne x a ih =>
    rw [add_mul, signature_add, signature_add, ih, hscale, add_mul]

/-- The integer signature as a semiring homomorphism on regular-form classes. -/
noncomputable def signatureHom : RegularFormClass K →+* ℤ where
  toFun := signature
  map_zero' := signature_zero
  map_one' := signature_one
  map_add' := signature_add
  map_mul' := signature_mul

@[simp]
theorem signatureHom_apply (x : RegularFormClass K) : signatureHom x = signature x := (rfl)

-- Not `@[simp]`: `nsmul_eq_mul` rewrites the left-hand side in the semiring
-- `RegularFormClass K`, so this declaration would fail `simpNF`.
/-- The signature of the orthogonal sum of `n` copies of a class is `n` times its signature. -/
theorem signature_nsmul (n : ℕ) (x : RegularFormClass K) :
    signature (n • x) = n • signature x :=
  map_nsmul signatureHom n x

variable [IsRealClosed K]

/-- A positive line over a real closed field is isometric to the unit line. -/
theorem mk_rankOne_eq_one_of_pos {a : Kˣ} (ha : 0 < (a : K)) :
    Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ = 1 :=
  eq_one_of_rank_eq_one_of_discr_eq_zero (rank_mk _) (by
    rw [discr_mk, Fin.prod_univ_one, squareClass_eq_zero_iff, ← Units.isSquare_coe_iff]
    exact IsSquare.of_nonneg ha.le)

/-- A negative line over a real closed field is isometric to the line with coefficient `-1`. -/
theorem mk_rankOne_eq_mk_neg_one_of_neg {a : Kˣ} (ha : (a : K) < 0) :
    Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ =
      Quotient.mk (regularFormSetoid K) ⟨1, fun _ => (-1 : Kˣ)⟩ := by
  have hpos : 0 < ((-a : Kˣ) : K) := by simpa using neg_pos.mpr ha
  have h := mk_rankOne_eq_one_of_pos hpos
  have hm := congrArg (fun x : RegularFormClass K =>
    Quotient.mk (regularFormSetoid K) ⟨1, fun _ => (-1 : Kˣ)⟩ * x) h
  simpa only [mk_rankOne_mul_mk_rankOne, neg_mul, one_mul, neg_neg, mul_one] using hm

/-- **Normal-form decomposition over an ordered real closed field.** Every regular-form class is
the orthogonal sum of `sigPos x` positive unit lines and `sigNeg x` negative unit lines. -/
theorem eq_sigPos_nsmul_add_sigNeg_nsmul (x : RegularFormClass K) :
    x = x.sigPos • (1 : RegularFormClass K) +
      x.sigNeg • Quotient.mk (regularFormSetoid K) ⟨1, fun _ => (-1 : Kˣ)⟩ := by
  induction x using induction_on_rankOne with
  | zero => simp
  | add_rankOne x a ih =>
    rw [sigPos_add, sigNeg_add, sigPos_mk_rankOne, sigNeg_mk_rankOne]
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha
    · simp only [ha.not_gt, ↓reduceIte, ha, add_zero, add_nsmul, one_nsmul]
      conv_lhs => rw [ih, mk_rankOne_eq_mk_neg_one_of_neg ha]
      abel
    · simp only [ha, ↓reduceIte, not_lt_of_gt ha, add_zero, add_nsmul, one_nsmul]
      conv_lhs => rw [ih, mk_rankOne_eq_one_of_pos ha]
      abel

/-- **The determinant-sign formula over an ordered real closed field.** The discriminant of a
regular-form class is `sigNeg x • [-1]`. -/
theorem discr_eq_sigNeg_nsmul (x : RegularFormClass K) :
    discr x = x.sigNeg • squareClass (-1 : Kˣ) := by
  conv_lhs => rw [eq_sigPos_nsmul_add_sigNeg_nsmul x]
  rw [discr_add, discr_nsmul, discr_one, smul_zero, zero_add (M := SquareClassGroup K),
    discr_nsmul, discr_mk, Fin.prod_univ_one]

end RegularFormClass

end TauCeti
