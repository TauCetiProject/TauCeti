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

* `TauCeti.RegularFormClass.signatureHom`: the integer signature as a semiring homomorphism.
* `TauCeti.signature_formClass`: computes signature from the inertia indices of a regular form.
* `TauCeti.RegularFormClass.mk_rankOne_eq_one_of_pos`: positive lines over real closed fields
  are isometric to the unit line.
* `TauCeti.RegularFormClass.mk_rankOne_eq_mk_neg_one_of_neg`: negative lines over real closed
  fields are isometric to the negative unit line.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §3.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The integer signature of a regular-form class: its positive index minus its negative
index. -/
noncomputable def RegularFormClass.signature : RegularFormClass K → ℤ :=
  Quotient.lift (fun p => (sigPos (presentedForm p) : ℤ) - sigNeg (presentedForm p))
    (fun _ _ h => by rw [h.sigPos_eq, h.sigNeg_eq])

omit [IsStrictOrderedRing K] in
/-- The signature of a diagonal presentation is the difference of its inertia indices. -/
@[simp]
theorem RegularFormClass.signature_mk (p : RegularFormPresentation K) :
    signature (Quotient.mk (regularFormSetoid K) p) =
      (sigPos (presentedForm p) : ℤ) - sigNeg (presentedForm p) := (rfl)

omit [IsStrictOrderedRing K] in
/-- The signature on isometry classes agrees with the inertia indices of any regular form. -/
@[simp]
theorem signature_formClass [Invertible (2 : K)] (Q : QuadraticForm K M) (hQ : Q.Nondegenerate) :
    RegularFormClass.signature (formClass Q hQ) = (sigPos Q : ℤ) - sigNeg Q := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.signature_mk, hp.sigPos_eq, hp.sigNeg_eq]

namespace RegularFormClass

/-- The zero-dimensional form has signature zero. -/
@[simp]
theorem signature_zero : signature (0 : RegularFormClass K) = 0 := by
  rw [zero_def, signature_mk, presentedForm_eq_weightedSumSquares_coe]
  simp [sigPos_weightedSumSquares, sigNeg_weightedSumSquares, Set.eq_empty_of_isEmpty]

/-- Signature is additive under orthogonal sum. -/
@[simp]
theorem signature_add (x y : RegularFormClass K) :
    signature (x + y) = signature x + signature y := by
  refine Quotient.inductionOn₂ x y fun p q => ?_
  have h := equivalent_presentedForm_append_prod p q
  rw [mk_add_mk, signature_mk, signature_mk, signature_mk, h.sigPos_eq, h.sigNeg_eq,
    sigPos_prod, sigNeg_prod]
  push_cast
  ring

/-- A line has signature `1` or `-1`, according to the sign of its coefficient. -/
@[simp 1100]
theorem signature_mk_rankOne (a : Kˣ) :
    signature (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) =
      if 0 < (a : K) then 1 else -1 := by
  rw [signature_mk, presentedForm_eq_weightedSumSquares_coe,
    sigPos_weightedSumSquares, sigNeg_weightedSumSquares]
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha
  · simp [ha, ha.not_gt]
  · simp [ha, not_lt_of_gt ha]

/-- The positive unit line has signature one. -/
@[simp]
theorem signature_one : signature (1 : RegularFormClass K) = 1 := by
  rw [← mk_rankOne_one, signature_mk_rankOne]
  norm_num

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
      · rw [sigPos_smul_of_neg _ ha, sigNeg_smul_of_neg _ ha, ite_eq_right ha.not_gt]
        ring
      · rw [sigPos_smul_of_pos _ ha, sigNeg_smul_of_pos _ ha, ite_eq_left ha, one_mul]
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

variable [IsRealClosed K]

/-- A positive line over a real closed field is isometric to the unit line. -/
theorem mk_rankOne_eq_one_of_pos {a : Kˣ} (ha : 0 < (a : K)) :
    Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ = 1 :=
  eq_one_of_rank_eq_one_of_discr_eq_zero (rank_mk _) (by
    rw [discr_mk, Fin.prod_univ_one, squareClass_eq_zero_iff, ← isSquare_units_val_iff]
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

end RegularFormClass

end TauCeti
