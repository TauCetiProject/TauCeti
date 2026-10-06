/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Real
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Semiring

/-!
# Signature and discriminant of regular real quadratic forms

Over `ℝ` the square class of a nonzero number is its sign, so the discriminant of a regular form
only records the sign of the product of the weights of a diagonalization.  By Sylvester's law of
inertia that sign is `(-1)^q`, where `q = sigNeg Q` is the negative index of inertia.  This is the
determinant-sign formula `sign (det Q) = (-1)^q`, stated in the square-class group.

In particular the discriminant of a regular real form is determined by its signature, and it is
trivial exactly when the negative index is even.

The integer signature, the positive index minus the negative index, descends to isometry classes.
It is additive under orthogonal sum and multiplicative under tensor product, so it defines a
semiring homomorphism to `ℤ`. It vanishes on the hyperbolic plane and therefore induces the
signature of a Witt class.

## Main results

* `QuadraticForm.discr_formClass_eq_sigNeg_nsmul`: the discriminant of a regular real form is
  `sigNeg Q • [-1]`.
* `QuadraticForm.discr_formClass_eq_zero_iff_even_sigNeg`: it is trivial exactly when `sigNeg Q`
  is even.
* `TauCeti.discr_formClass_realSignatureForm`: the normal form of signature `(p, q)` has
  discriminant `q • [-1]`.
* `TauCeti.RegularFormClass.signatureHom`: the integer signature as a semiring homomorphism.
* `TauCeti.signature_formClass`: computes signature from the inertia indices of a regular form.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §3.
-/

public section

open QuadraticMap QuadraticForm TauCeti

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]

namespace QuadraticForm

/-- **The determinant-sign formula.** The discriminant of a regular real quadratic form is the
class of `(-1)^q`, where `q` is its negative index of inertia. -/
theorem discr_formClass_eq_sigNeg_nsmul (Q : _root_.QuadraticForm ℝ M) (hQ : Q.Nondegenerate) :
    RegularFormClass.discr (formClass Q hQ) = sigNeg Q • squareClass (-1 : ℝˣ) := by
  obtain ⟨⟨n, w⟩, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [discr_formClass Q hQ ⟨n, w⟩ hp, squareClass_prod, sum_squareClass_eq_ncard_nsmul,
    sigNeg_of_equiv_weightedSumSquares (by rwa [← presentedForm_eq_weightedSumSquares_coe])]

/-- The discriminant of a regular real quadratic form is trivial exactly when its negative index
of inertia is even. -/
@[simp]
theorem discr_formClass_eq_zero_iff_even_sigNeg (Q : _root_.QuadraticForm ℝ M)
    (hQ : Q.Nondegenerate) :
    RegularFormClass.discr (formClass Q hQ) = 0 ↔ Even (sigNeg Q) := by
  rw [discr_formClass_eq_sigNeg_nsmul, nsmul_squareClass_neg_one_eq_zero_iff_even]

end QuadraticForm

namespace TauCeti

/-- The normal form `p⟨1⟩ ⊥ q⟨-1⟩` of signature `(p, q)` has discriminant `q • [-1]`. -/
@[simp]
theorem discr_formClass_realSignatureForm (p q : ℕ) :
    RegularFormClass.discr
        (formClass (realSignatureForm p q) (nondegenerate_realSignatureForm p q)) =
      q • squareClass (-1 : ℝˣ) := by
  rw [discr_formClass_eq_sigNeg_nsmul, sigNeg_realSignatureForm]

/-- The integer signature of a real regular-form class: its positive index minus its negative
index. -/
noncomputable def RegularFormClass.signature : RegularFormClass ℝ → ℤ :=
  Quotient.lift (fun p => (sigPos (presentedForm p) : ℤ) - sigNeg (presentedForm p))
    (fun _ _ h => by rw [h.sigPos_eq, h.sigNeg_eq])

/-- The signature of a diagonal presentation is the difference of its inertia indices. -/
@[simp]
theorem RegularFormClass.signature_mk (p : RegularFormPresentation ℝ) :
    signature (Quotient.mk (regularFormSetoid ℝ) p) =
      (sigPos (presentedForm p) : ℤ) - sigNeg (presentedForm p) := (rfl)

/-- The signature on isometry classes agrees with the inertia indices of any regular form. -/
@[simp]
theorem signature_formClass (Q : QuadraticForm ℝ M) (hQ : Q.Nondegenerate) :
    RegularFormClass.signature (formClass Q hQ) = (sigPos Q : ℤ) - sigNeg Q := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.signature_mk, hp.sigPos_eq, hp.sigNeg_eq]

namespace RegularFormClass

/-- The zero-dimensional form has signature zero. -/
@[simp]
theorem signature_zero : signature (0 : RegularFormClass ℝ) = 0 := by
  rw [zero_def, signature_mk, presentedForm_eq_weightedSumSquares_coe]
  simp [sigPos_weightedSumSquares, sigNeg_weightedSumSquares, Set.eq_empty_of_isEmpty]

/-- Signature is additive under orthogonal sum. -/
@[simp]
theorem signature_add (x y : RegularFormClass ℝ) :
    signature (x + y) = signature x + signature y := by
  refine Quotient.inductionOn₂ x y fun p q => ?_
  have h := equivalent_presentedForm_append_prod p q
  rw [mk_add_mk, signature_mk, signature_mk, signature_mk, h.sigPos_eq, h.sigNeg_eq,
    sigPos_prod, sigNeg_prod]
  push_cast
  ring

/-- A real line has signature `1` or `-1`, according to the sign of its coefficient. -/
@[simp 1100]
theorem signature_mk_rankOne (a : ℝˣ) :
    signature (Quotient.mk (regularFormSetoid ℝ) ⟨1, fun _ => a⟩) =
      if 0 < (a : ℝ) then 1 else -1 := by
  rw [signature_mk, presentedForm_eq_weightedSumSquares_coe,
    sigPos_weightedSumSquares, sigNeg_weightedSumSquares]
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha
  · simp [ha, ha.not_gt]
  · simp [ha, not_lt_of_gt ha]

/-- The positive unit line has signature one. -/
@[simp]
theorem signature_one : signature (1 : RegularFormClass ℝ) = 1 := by
  rw [← mk_rankOne_one, signature_mk_rankOne]
  norm_num

/-- A positive real line is isometric to the unit line. -/
theorem mk_rankOne_eq_one_of_pos {a : ℝˣ} (ha : 0 < (a : ℝ)) :
    Quotient.mk (regularFormSetoid ℝ) ⟨1, fun _ => a⟩ = 1 :=
  eq_one_of_rank_eq_one_of_discr_eq_zero (rank_mk _) (by
    rw [discr_mk, Fin.prod_univ_one]
    exact (Units.squareClass_eq_zero_iff_pos a).mpr ha)

/-- A negative real line is isometric to the line with coefficient `-1`. -/
theorem mk_rankOne_eq_mk_neg_one_of_neg {a : ℝˣ} (ha : (a : ℝ) < 0) :
    Quotient.mk (regularFormSetoid ℝ) ⟨1, fun _ => a⟩ =
      Quotient.mk (regularFormSetoid ℝ) ⟨1, fun _ => (-1 : ℝˣ)⟩ := by
  have hpos : 0 < ((-a : ℝˣ) : ℝ) := by simpa using neg_pos.mpr ha
  have h := mk_rankOne_eq_one_of_pos hpos
  have hm := congrArg (fun x : RegularFormClass ℝ =>
    Quotient.mk (regularFormSetoid ℝ) ⟨1, fun _ => (-1 : ℝˣ)⟩ * x) h
  simpa only [mk_rankOne_mul_mk_rankOne, neg_mul, one_mul, neg_neg, mul_one] using hm

/-- The hyperbolic plane has signature zero. -/
@[simp]
theorem signature_hyperbolicClass : signature (hyperbolicClass ℝ) = 0 := by
  have ht : (fun i : Fin 1 => (![1, -1] i.succ : ℝˣ)) = fun _ => -1 := by
    simp
  rw [hyperbolicClass_def, mk_succ_eq_mk_rankOne_add, signature_add,
    signature_mk_rankOne, ht, signature_mk_rankOne]
  norm_num

/-- Signature is multiplicative under tensor product. -/
@[simp]
theorem signature_mul (x y : RegularFormClass ℝ) :
    signature (x * y) = signature x * signature y := by
  have hneg (z : RegularFormClass ℝ) :
      signature (Quotient.mk (regularFormSetoid ℝ) ⟨1, fun _ => (-1 : ℝˣ)⟩ * z) =
        -signature z := by
    induction z using Quotient.inductionOn with
    | h p =>
      have hs := formClass_smul (-1 : ℝˣ) (presentedForm p) (nondegenerate_presentedForm p)
      rw [formClass_presentedForm] at hs
      rw [← hs, signature_formClass, signature_mk,
        sigPos_smul_of_neg _ (by norm_num : ((-1 : ℝˣ) : ℝ) < 0),
        sigNeg_smul_of_neg _ (by norm_num : ((-1 : ℝˣ) : ℝ) < 0)]
      ring
  induction x using induction_on_rankOne with
  | zero => simp
  | add_rankOne x a ih =>
    rw [add_mul, signature_add, signature_add, ih]
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha
    · rw [mk_rankOne_eq_mk_neg_one_of_neg ha, hneg, signature_mk_rankOne]
      norm_num
      ring
    · rw [mk_rankOne_eq_one_of_pos ha, one_mul, signature_one]
      ring

/-- The integer signature as a semiring homomorphism on real regular-form classes. -/
noncomputable def signatureHom : RegularFormClass ℝ →+* ℤ where
  toFun := signature
  map_zero' := signature_zero
  map_one' := signature_one
  map_add' := signature_add
  map_mul' := signature_mul

@[simp]
theorem signatureHom_apply (x : RegularFormClass ℝ) : signatureHom x = signature x := (rfl)

end RegularFormClass

end TauCeti
