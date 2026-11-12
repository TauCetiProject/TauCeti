/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.RegularCrossings
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# The crossing form formula for the Maslov index of a path of graphs

Let `t ↦ A t` be a path of real symmetric matrices on `[0, 1]`, and `γ` a path of unitary frames
of the Lagrangian graphs `Λ t = {x + i A t x}`, so that the Souriau maps `γ t γ tᵀ` are the Cayley
transforms of `A t`. The graph `Λ t` meets the fixed Lagrangian `ℝⁿ` in the kernel of `A t`, so
the *crossings* of the path relative to `ℝⁿ` are the parameters at which `A t` is singular. At a
crossing `t` the *crossing form* of Robbin and Salamon is the quadratic form `x ↦ x ⬝ᵥ A' t *ᵥ x`
of the derivative of `A`, restricted to the kernel of `A t` (`Matrix.crossingForm`): for `x` in
that kernel, `x + i (A s - A t) x` is the point of `Λ s` above `x`, and the symplectic form
`Im ⟪·, ·⟫` pairs `x` with its displacement to `x ⬝ᵥ (A s - A t) *ᵥ x`. A crossing is *regular*
when its crossing form is nondegenerate.

If every crossing is regular, the Maslov index of `γ` is the sum of the signatures of the
crossing forms, the crossings at the endpoints `0` and `1` counting one half
(`Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley`):

`μ(γ) = (sign Γ(0) + sign Γ(1)) / 2 + ∑ᶠ t ∈ (0, 1), sign Γ(t)`.

This compares the definition of the Maslov index for paths by crossing forms (Robbin–Salamon,
§2) with the spectral definition `Matrix.UnitaryGroup.maslovIndex`, for the paths of Lagrangians
transverse to `iℝⁿ`, which are exactly the graphs `{x + i A x}` of symmetric matrices. The proof
combines the localization axiom
`Matrix.UnitaryGroup.maslovIndex_eq_signature_sub_of_souriau_eq_cayley`, which gives the index as
half the change of the signature of `A`, with the regular-crossing formula for the signature of a
path of symmetric forms,
`ContinuousLinearMap.sigPos_sub_sigNeg_sub_sigPos_sub_sigNeg_eq_crossingForm_add_two_mul_finsum`,
applied to the bilinear forms `(x, y) ↦ x ⬝ᵥ A t *ᵥ y`.

Matrices carry no preferred norm, so the derivative of `A` at a crossing is asked for entry by
entry.

## Main definitions

* `Matrix.crossingForm`: the quadratic form of `A'` on the kernel of `A`.

## Main results

* `Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley`: the crossing
  form formula for the Maslov index of a path of graphs with regular crossings.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Section 2 (crossing forms, and the Maslov index of a path with regular crossings as the sum of
  their signatures, with half weights at the endpoints).
-/

public section

open Set
open scoped unitInterval

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

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

/-! ### Matrices as continuous bilinear forms -/

/-- The continuous bilinear form `(x, y) ↦ x ⬝ᵥ M *ᵥ y` of a real matrix. -/
private noncomputable def bilin (M : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) →L[ℝ] ℝ :=
  (toLinearMap₂' ℝ M).toContinuousBilinearMap

private theorem bilin_apply (M : Matrix n n ℝ) (x y : n → ℝ) : bilin M x y = x ⬝ᵥ M *ᵥ y := by
  simp [bilin, toLinearMap₂'_apply']

private theorem toBilinForm_bilin (M : Matrix n n ℝ) :
    (bilin M).toBilinForm = toLinearMap₂' ℝ M :=
  LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap _

private theorem toQuadraticMap_bilin (M : Matrix n n ℝ) :
    (bilin M).toBilinForm.toQuadraticMap = M.toQuadraticForm' := by
  rw [toBilinForm_bilin]
  -- `Matrix.toQuadraticForm'` is by definition the quadratic map of `Matrix.toLinearMap₂'`.
  rfl

private theorem nondegenerate_bilin_iff (M : Matrix n n ℝ) :
    (bilin M).toBilinForm.Nondegenerate ↔ M.det ≠ 0 := by
  rw [toBilinForm_bilin]
  exact LinearMap.nondegenerate_toLinearMap₂'_iff_det_ne_zero

private theorem isSymm_bilin {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    (bilin M).toBilinForm.IsSymm := by
  have hT : Mᵀ = M := by rw [← conjTranspose_eq_transpose_of_trivial, hM.eq]
  refine ⟨fun x y ↦ ?_⟩
  simp only [ContinuousLinearMap.toBilinForm_apply, bilin_apply]
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

/-- The kernel of the bilinear form of a symmetric matrix is the kernel of the matrix. -/
private theorem ker_bilin {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    (bilin M).ker = LinearMap.ker M.mulVecLin := by
  have hT : Mᵀ = M := by rw [← conjTranspose_eq_transpose_of_trivial, hM.eq]
  have hxy (x y : n → ℝ) : bilin M x y = (M *ᵥ x) ⬝ᵥ y := by
    rw [bilin_apply, dotProduct_mulVec, ← mulVec_transpose, hT]
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, mulVecLin_apply, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    funext i
    have hi : bilin M x (Pi.single i 1) = 0 := by simp [h]
    rwa [hxy, dotProduct_single, mul_one] at hi
  · intro h
    ext y
    simp [hxy, h]

/-- The crossing form of the bilinear forms of `A` and `A'` is the crossing form of `A` and `A'`,
read on the same kernel. -/
private noncomputable def crossingFormBilinIsometryEquiv {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (A' : Matrix n n ℝ) :
    (ContinuousLinearMap.crossingForm (bilin A) (bilin A')).IsometryEquiv (crossingForm A A') :=
  ⟨LinearEquiv.ofEq _ _ (ker_bilin hA), fun v ↦ by simp [bilin_apply]⟩

/-- The bilinear forms of matrices, as a continuous linear map on the entries. -/
private noncomputable def bilinCLM : (n → n → ℝ) →L[ℝ] (n → ℝ) →L[ℝ] (n → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun M := bilin (of M)
      map_add' M N := by
        ext x y
        simp [bilin_apply, ← of_add_of, add_mulVec, dotProduct_add]
      map_smul' c M := by
        ext x y
        simp [bilin_apply, ← smul_of, smul_mulVec, dotProduct_smul] }

/-- Entrywise derivatives of a path of matrices give the derivative of its bilinear forms. -/
private theorem hasDerivWithinAt_bilin {A : ℝ → Matrix n n ℝ} {A' : Matrix n n ℝ} {s : Set ℝ}
    {t : ℝ} (h : ∀ i j, HasDerivWithinAt (fun r ↦ A r i j) (A' i j) s t) :
    HasDerivWithinAt (fun r ↦ bilin (A r)) (bilin A') s t := by
  have hA : HasDerivWithinAt (fun r ↦ of.symm (A r)) (of.symm A') s t :=
    hasDerivWithinAt_pi.2 fun i ↦ hasDerivWithinAt_pi.2 fun j ↦ h i j
  have hΦ := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := n → n → ℝ)
    (F := (n → ℝ) →L[ℝ] (n → ℝ) →L[ℝ] ℝ) (f := bilinCLM) (x := of.symm (A t))
  exact HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ) (F := n → n → ℝ)
    (E := (n → ℝ) →L[ℝ] (n → ℝ) →L[ℝ] ℝ) t hΦ hA

private theorem continuousOn_bilin {A : ℝ → Matrix n n ℝ} {s : Set ℝ} (hA : ContinuousOn A s) :
    ContinuousOn (fun r ↦ bilin (A r)) s := by
  have h : ContinuousOn (fun r ↦ of.symm (A r)) s :=
    continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦
      (continuous_id.matrix_elem i j).comp_continuousOn hA
  exact bilinCLM.continuous.comp_continuousOn h

namespace UnitaryGroup

/-- **The crossing form formula for the Maslov index of a path of graphs.** Let `t ↦ A t` be a
path of real symmetric matrices, continuous on `[0, 1]`, and `γ` a path of unitary frames of their
graphs `{x + i A t x}`, that is, with Souriau maps `γ t γ tᵀ` the Cayley transforms of `A t`.
Suppose that at every crossing `t ∈ [0, 1]`, where `A t` is singular, `A` has entrywise derivative
`A' t` within `[0, 1]` and the crossing form `Matrix.crossingForm (A t) (A' t)` is nondegenerate.
Then the Maslov index of `γ` relative to `ℝⁿ` is the sum of the signatures of the crossing forms,
the crossings at the endpoints counting one half. Parameters where `A t` is invertible contribute
zero. -/
theorem maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley {U V : unitaryGroup n ℂ}
    (γ : Path U V) {A A' : ℝ → Matrix n n ℝ} (hAc : ContinuousOn A (Icc 0 1))
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, (A t).IsHermitian)
    (hγ : ∀ t : I, (souriau (γ t) : Matrix n n ℂ) = cayley ((A t).map ((↑) : ℝ → ℂ)))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (A t).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ A r i j) (A' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (A t).det = 0 → (crossingForm (A t) (A' t)).Nondegenerate) :
    maslovIndex γ =
      (((sigPos (crossingForm (A 0) (A' 0)) : ℤ) - sigNeg (crossingForm (A 0) (A' 0)) +
        ((sigPos (crossingForm (A 1) (A' 1)) : ℤ) - sigNeg (crossingForm (A 1) (A' 1))) : ℤ) :
          ℝ) / 2 +
      ((∑ᶠ t ∈ Ioo (0 : ℝ) 1,
        ((sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t))) : ℤ) :
          ℝ) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  -- The localization axiom: the index is half the change of the signature of `A`.
  have hloc := maslovIndex_eq_signature_sub_of_souriau_eq_cayley γ (A := fun t : I ↦ A t)
    (hAc.comp_continuous continuous_subtype_val fun t ↦ t.2) (fun t ↦ hA t t.2) hγ
  simp only [Icc.coe_one, Icc.coe_zero] at hloc
  -- The signature formula for the bilinear forms of `A`.
  have hsig :=
    ContinuousLinearMap.sigPos_sub_sigNeg_sub_sigPos_sub_sigNeg_eq_crossingForm_add_two_mul_finsum
    (V := fun t ↦ bilin (A t)) (V' := fun t ↦ bilin (A' t)) zero_lt_one (continuousOn_bilin hAc)
    (fun t ht ↦ isSymm_bilin (hA t ht))
    (fun t ht hnt ↦ hasDerivWithinAt_bilin
      (hd t ht (not_not.1 fun h ↦ hnt ((nondegenerate_bilin_iff _).2 h))))
    (fun t ht hnt ↦ (crossingFormBilinIsometryEquiv (hA t ht) (A' t)).nondegenerate_iff.2
      (hreg t ht (not_not.1 fun h ↦ hnt ((nondegenerate_bilin_iff _).2 h))))
  have hΓ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (sigPos (ContinuousLinearMap.crossingForm (bilin (A t)) (bilin (A' t))) : ℤ) -
          sigNeg (ContinuousLinearMap.crossingForm (bilin (A t)) (bilin (A' t))) =
        (sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t)) := by
    have h : QuadraticMap.Equivalent _ _ := ⟨crossingFormBilinIsometryEquiv (hA t ht) (A' t)⟩
    rw [h.sigPos_eq, h.sigNeg_eq]
  have hsum : ∑ᶠ t ∈ Ioo (0 : ℝ) 1,
        ((sigPos (ContinuousLinearMap.crossingForm (bilin (A t)) (bilin (A' t))) : ℤ) -
          sigNeg (ContinuousLinearMap.crossingForm (bilin (A t)) (bilin (A' t)))) =
      ∑ᶠ t ∈ Ioo (0 : ℝ) 1,
        ((sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t))) :=
    finsum_mem_congr rfl fun t ht ↦ hΓ t (Ioo_subset_Icc_self ht)
  simp only [toQuadraticMap_bilin, hΓ 0 h0, hΓ 1 h1, hsum] at hsig
  rw [hloc, signature_def, signature_def, ← Int.cast_sub, hsig]
  push_cast
  ring

end UnitaryGroup

end Matrix
