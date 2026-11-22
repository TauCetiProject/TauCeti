/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.ContinuousBilinearForm
public import TauCeti.Analysis.Matrix.HermitianSignature.Crossing
public import TauCeti.LinearAlgebra.Matrix.Signature
import TauCeti.Analysis.Matrix.HermitianSignature.RegularCrossings
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# Crossing forms of matrices

The *crossing form* of a matrix `A` and a matrix `A'` (`Matrix.crossingForm`) is the quadratic
form `x ↦ x ⬝ᵥ A' *ᵥ x` restricted to the kernel of `A`. For a real symmetric `A` it is isometric
to the crossing form `ContinuousLinearMap.crossingForm` of the corresponding continuous bilinear
forms `Matrix.toContinuousLinearMap₂'` (`Matrix.crossingFormIsometryEquiv`), so that the
signature theory of paths of continuous bilinear forms at their crossings applies to paths of
matrices. In particular, along a path of real symmetric matrices whose crossings, the parameters
where the matrix is singular, are regular, the change of the signature is the sum of the
signatures of the crossing forms, counted twice at the interior crossings and once at the
endpoints (`Matrix.signature_sub_signature_eq_crossingForm_add_two_mul_finsum`).

## Main definitions

* `Matrix.crossingForm`: the quadratic form of `A'` on the kernel of `A`.
* `Matrix.crossingFormIsometryEquiv`: for real symmetric `A`, the crossing form of the bilinear
  forms of `A` and `A'` is isometric to the crossing form of `A` and `A'`.

## Main results

* `Matrix.signature_sub_signature_eq_crossingForm_add_two_mul_finsum`: the change of the signature
  along a path of real symmetric matrices with regular crossings.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Section 2 (crossing forms and regular crossings).
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Crossing forms of matrices -/

/-- The **crossing form** of a square matrix `A` and a matrix `A'`: the quadratic form
`x ↦ x ⬝ᵥ A' *ᵥ x` restricted to the kernel of `A`. For a path of symmetric matrices `A` with
derivative `A'` at a parameter where `A` is singular, it is the crossing form of Robbin and Salamon
of the path of graphs `{x + i A x}` relative to `ℝⁿ`. -/
noncomputable def crossingForm {R : Type*} [CommRing R] (A A' : Matrix n n R) :
    QuadraticForm R (LinearMap.ker A.mulVecLin) :=
  A'.toQuadraticForm'.restrict (LinearMap.ker A.mulVecLin)

@[simp]
theorem crossingForm_apply {R : Type*} [CommRing R] (A A' : Matrix n n R)
    (x : LinearMap.ker A.mulVecLin) : crossingForm A A' x = (x : n → R) ⬝ᵥ A' *ᵥ x := by
  simp [crossingForm, toQuadraticForm', toLinearMap₂'_apply']

/-- For a real symmetric matrix `A`, the crossing form of the bilinear forms of `A` and `A'` is
the crossing form of `A` and `A'`, read on the same kernel. -/
noncomputable def crossingFormIsometryEquiv {A : Matrix n n ℝ} (hA : A.IsSymm)
    (A' : Matrix n n ℝ) :
    (ContinuousLinearMap.crossingForm A.toContinuousLinearMap₂'
      A'.toContinuousLinearMap₂').IsometryEquiv (crossingForm A A') :=
  ⟨LinearEquiv.ofEq _ _ (by rw [ker_toContinuousLinearMap₂', hA.eq]), fun v ↦ by simp⟩

open Set in
/-- **The signature along a path of symmetric matrices with regular crossings.** Let `t ↦ A t`
be a path of real symmetric matrices, continuous on `[a, b]`. Suppose that at every crossing
`t ∈ [a, b]`, where `A t` is singular, `A` has entrywise derivative `A' t` within `[a, b]` and the
crossing form `Matrix.crossingForm (A t) (A' t)` is nondegenerate. Then the signature of `A b`
minus that of `A a` is the sum of the signatures of the crossing forms, counted twice at the
interior crossings and once at the endpoints. Parameters where `A t` is invertible contribute
zero. -/
theorem signature_sub_signature_eq_crossingForm_add_two_mul_finsum {a b : ℝ} (hab : a < b)
    {A A' : ℝ → Matrix n n ℝ} (hAc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Icc a b, (A t).IsSymm)
    (hd : ∀ t ∈ Icc a b, (A t).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ A r i j) (A' t i j) (Icc a b) t)
    (hreg : ∀ t ∈ Icc a b, (A t).det = 0 → (crossingForm (A t) (A' t)).Nondegenerate) :
    signature (A b) - signature (A a) =
      (sigPos (crossingForm (A a) (A' a)) : ℤ) - sigNeg (crossingForm (A a) (A' a)) +
        2 * ∑ᶠ t ∈ Ioo a b,
          ((sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t))) +
        ((sigPos (crossingForm (A b) (A' b)) : ℤ) - sigNeg (crossingForm (A b) (A' b))) := by
  have hdet (t : ℝ) (hnt : ¬((A t).toContinuousLinearMap₂').toBilinForm.Nondegenerate) :
      (A t).det = 0 :=
    not_not.1 fun h ↦
      hnt ((nondegenerate_toBilinForm_toContinuousLinearMap₂'_iff_det_ne_zero _).2 h)
  have hsig :=
    ContinuousLinearMap.sigPos_sub_sigNeg_sub_sigPos_sub_sigNeg_eq_crossingForm_add_two_mul_finsum
    (V := fun t ↦ (A t).toContinuousLinearMap₂') (V' := fun t ↦ (A' t).toContinuousLinearMap₂')
    hab (continuousOn_toContinuousLinearMap₂' hAc)
    (fun t ht ↦ isSymm_toBilinForm_toContinuousLinearMap₂' (hA t ht))
    (fun t ht hnt ↦ hasDerivWithinAt_toContinuousLinearMap₂' (hd t ht (hdet t hnt)))
    (fun t ht hnt ↦ (crossingFormIsometryEquiv (hA t ht) (A' t)).nondegenerate_iff.2
      (hreg t ht (hdet t hnt)))
  -- The crossing forms of the bilinear forms are those of the matrices.
  have hΓ (t : ℝ) (ht : t ∈ Icc a b) :
      (sigPos (ContinuousLinearMap.crossingForm (A t).toContinuousLinearMap₂'
          (A' t).toContinuousLinearMap₂') : ℤ) -
          sigNeg (ContinuousLinearMap.crossingForm (A t).toContinuousLinearMap₂'
            (A' t).toContinuousLinearMap₂') =
        (sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t)) := by
    have h : QuadraticMap.Equivalent _ _ := ⟨crossingFormIsometryEquiv (hA t ht) (A' t)⟩
    rw [h.sigPos_eq, h.sigNeg_eq]
  have hsum : ∑ᶠ t ∈ Ioo a b,
        ((sigPos (ContinuousLinearMap.crossingForm (A t).toContinuousLinearMap₂'
            (A' t).toContinuousLinearMap₂') : ℤ) -
          sigNeg (ContinuousLinearMap.crossingForm (A t).toContinuousLinearMap₂'
            (A' t).toContinuousLinearMap₂')) =
      ∑ᶠ t ∈ Ioo a b,
        ((sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t))) :=
    finsum_mem_congr rfl fun t ht ↦ hΓ t (Ioo_subset_Icc_self ht)
  simp only [toQuadraticMap_toBilinForm_toContinuousLinearMap₂', hΓ a (left_mem_Icc.2 hab.le),
    hΓ b (right_mem_Icc.2 hab.le), hsum] at hsig
  rw [signature_def, signature_def, hsig]

end Matrix
