/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
public import TauCeti.Analysis.SpecialFunctions.Sigmoid

/-!
# Conjugating parabolic operators by a spatial weight

Let `w = exp φ` be a positive time-independent weight on `E` whose logarithm `φ` has a bounded
`α`-Hölder gradient `ℓ = Dφ` and Hessian `M = D²φ`; `φ` itself need not be bounded. For the
parabolic operator `P u = ∂ₜu - A·D_x²u - B·D_xu - C·u` with coefficient fields in `C_b^{α,α/2}`
(`ParabolicC2HolderSpace.parabolicOperatorL`), this file proves the conjugation identity

`w⁻¹ P (w v) = P_w v`,

where `P_w` has the same second-order coefficient `A` and the lower-order coefficients

* `B_w H = B H + A (ℓ ⊗ H + H ⊗ ℓ)`, with `(ℓ ⊗ H)(h, k) = ℓ h • H k`;
* `C_w y = C y + A ((M + ℓ ⊗ ℓ) ⊗ y) + B (ℓ ⊗ y)`.

In coordinates, for a symmetric matrix `a`, these are `b_w^i = b^i + 2 a^{ij} ∂ⱼφ` and
`c_w = c + a^{ij} (∂ᵢⱼφ + ∂ᵢφ ∂ⱼφ) + b^i ∂ᵢφ`. The new coefficients are again bounded parabolic
Hölder fields (`weightFirstOrderCoeff`, `weightZerothOrderCoeff`), with norms controlled by those
of `A`, `B`, `C`, `ℓ` and `M`. Thus a function `u = w v` that may grow like `w` is a classical
solution of `P u = f` exactly when `v ∈ C_b^{2+α,1+α/2}` solves `P_w v = f / w`, an equation with
bounded coefficients to which the bounded theory applies.

The basic example is `w(x) = 1 + exp x` on `ℝ`, the growth of an option price in the log-spot
variable. Here `φ = log (1 + exp x)` is unbounded, while `φ' = sigmoid` and
`φ'' = sigmoid (1 - sigmoid)` are bounded and Hölder (`Real.memHolder_iteratedDeriv_sigmoid`).

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.weightFirstOrderCoeff` and
  `TauCeti.ParabolicC2HolderSpace.weightZerothOrderCoeff`: the conjugated coefficients `B_w` and
  `C_w`, with their pointwise formulas and the bounds `norm_weightFirstOrderCoeff_le` and
  `norm_weightZerothOrderCoeff_le`.
* `TauCeti.ParabolicC2HolderSpace.hasFDerivAt_exp_smul_slice` and
  `TauCeti.ParabolicC2HolderSpace.hasFDerivAt_fderiv_exp_smul_slice`: the spatial gradient and
  Hessian of `w v`.
* `TauCeti.ParabolicC2HolderSpace.exp_smul_parabolicOperatorL_weightCoeff`: the conjugation
  identity `w P_w v = P (w v)`, with `P (w v)` computed from the classical derivatives of `w v`.
* `TauCeti.ParabolicC2HolderSpace.parabolicOperatorL_weightCoeff_eq_iff`: `P_w v = g` if and only
  if `P (w v) = w g`.
* `TauCeti.logOneAddExpGrad`, `TauCeti.logOneAddExpHess` and
  `TauCeti.ParabolicC2HolderSpace.one_add_exp_smul_parabolicOperatorL_weightCoeff`: the weight
  `1 + exp x` on `ℝ`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4 (the
  transformation `u = w v` of a parabolic equation).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime ContinuousLinearMap
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- A local shortcut for the norm on Hessians, needed for the operator norm on the coefficient
space `(E →L[ℝ] E →L[ℝ] F) →L[ℝ] F` for the reason explained in
`TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
local instance weightNormedAddCommGroupHessian :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians. -/
local instance weightNormedSpaceHessian : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-! ### The pointwise algebra of the conjugation -/

section Bilinear

/-- A local shortcut for the norm on gradients. -/
local instance weightNormedAddCommGroupGradient : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on gradients. -/
local instance weightNormedSpaceGradient : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- A local shortcut for the norm on covectors. -/
local instance weightNormedAddCommGroupCovector : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for scalar operations on covectors. -/
local instance weightNormedSpaceCovector : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for the norm on bilinear forms. -/
local instance weightNormedAddCommGroupForm :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for scalar operations on bilinear forms. -/
local instance weightNormedSpaceForm : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for the norm on second-order coefficients. -/
local instance weightNormedAddCommGroupSecondCoeff :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on second-order coefficients. -/
local instance weightNormedSpaceSecondCoeff :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) := inferInstance
/-- A local shortcut for the norm on first-order coefficients. -/
local instance weightNormedAddCommGroupFirstCoeff :
    NormedAddCommGroup ((E →L[ℝ] F) →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on first-order coefficients. -/
local instance weightNormedSpaceFirstCoeff : NormedSpace ℝ ((E →L[ℝ] F) →L[ℝ] F) := inferInstance
/-- A local shortcut for the norm on zeroth-order coefficients. -/
local instance weightNormedAddCommGroupZerothCoeff : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on zeroth-order coefficients. -/
local instance weightNormedSpaceZerothCoeff : NormedSpace ℝ (F →L[ℝ] F) := inferInstance


/-- The bilinear map `(A, ℓ) ↦ (H ↦ A (ℓ ⊗ H + H ⊗ ℓ))` giving the correction to `B`. -/
private def firstOrderCorrL :
    ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ((E →L[ℝ] F) →L[ℝ] F) :=
  ((compL ℝ (E →L[ℝ] F) (E →L[ℝ] E →L[ℝ] F) F).flip ∘L
    (smulRightL ℝ E (E →L[ℝ] F) + compL ℝ E F (E →L[ℝ] F) ∘L smulRightL ℝ E F)).flip

private theorem firstOrderCorrL_apply (A : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) (ℓ : E →L[ℝ] ℝ)
    (H : E →L[ℝ] F) : firstOrderCorrL A ℓ H = A (ℓ.smulRight H + (ℓ.smulRight H).flip) := by
  simp only [firstOrderCorrL, flip_apply, comp_apply, compL_apply]
  exact congrArg A (by ext h k; simp)

private theorem norm_firstOrderCorrL_le : ‖firstOrderCorrL (E := E) (F := F)‖ ≤ 2 := by
  have hS : ‖smulRightL ℝ E (E →L[ℝ] F) + compL ℝ E F (E →L[ℝ] F) ∘L smulRightL ℝ E F‖ ≤ 2 := by
    refine opNorm_le_bound₂ _ zero_le_two fun ℓ H ↦ ?_
    have hS : (smulRightL ℝ E (E →L[ℝ] F) + compL ℝ E F (E →L[ℝ] F) ∘L smulRightL ℝ E F) ℓ H =
        ℓ.smulRight H + (ℓ.smulRight H).flip := by
      ext h k
      simp
    rw [hS]
    calc _ ≤ ‖ℓ.smulRight H‖ + ‖(ℓ.smulRight H).flip‖ := norm_add_le _ _
      _ = 2 * ‖ℓ‖ * ‖H‖ := by rw [opNorm_flip, norm_smulRight_apply]; ring
  rw [firstOrderCorrL, opNorm_flip]
  refine (opNorm_comp_le _ _).trans ?_
  rw [opNorm_flip]
  nlinarith [norm_compL_le ℝ (E →L[ℝ] F) (E →L[ℝ] E →L[ℝ] F) F,
    norm_nonneg (smulRightL ℝ E (E →L[ℝ] F) + compL ℝ E F (E →L[ℝ] F) ∘L smulRightL ℝ E F)]

/-- The bilinear map `(A, Q) ↦ (y ↦ A (Q ⊗ y))` giving the second-order part of the correction
to `C`. -/
private def zerothOrderCorrL :
    ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] F) :=
  ((compL ℝ F (E →L[ℝ] E →L[ℝ] F) F).flip ∘L precompL E (smulRightL ℝ E F)).flip

private theorem zerothOrderCorrL_apply (A : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (y : F) :
    zerothOrderCorrL A Q y = A (precompL E (smulRightL ℝ E F) Q y) := by
  simp [zerothOrderCorrL]

private theorem norm_zerothOrderCorrL_le : ‖zerothOrderCorrL (E := E) (F := F)‖ ≤ 1 := by
  rw [zerothOrderCorrL, opNorm_flip]
  refine (opNorm_comp_le _ _).trans ?_
  rw [opNorm_flip]
  nlinarith [norm_compL_le ℝ F (E →L[ℝ] E →L[ℝ] F) F,
    (norm_precompL_le E (smulRightL ℝ E F)).trans norm_smulRightL_le,
    norm_nonneg (precompL E (smulRightL ℝ E F))]

/-- The bilinear map `(B, ℓ) ↦ (y ↦ B (ℓ ⊗ y))` giving the first-order part of the correction
to `C`. -/
private def gradCorrL : ((E →L[ℝ] F) →L[ℝ] F) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] F) :=
  ((compL ℝ F (E →L[ℝ] F) F).flip ∘L smulRightL ℝ E F).flip

private theorem gradCorrL_apply (B : (E →L[ℝ] F) →L[ℝ] F) (ℓ : E →L[ℝ] ℝ) (y : F) :
    gradCorrL B ℓ y = B (ℓ.smulRight y) := by
  simp [gradCorrL]

private theorem norm_gradCorrL_le : ‖gradCorrL (E := E) (F := F)‖ ≤ 1 := by
  rw [gradCorrL, opNorm_flip]
  refine (opNorm_comp_le _ _).trans ?_
  rw [opNorm_flip]
  nlinarith [norm_compL_le ℝ F (E →L[ℝ] F) F, norm_smulRightL_le (𝕜 := ℝ) (E := E) (Fₗ := F),
    norm_nonneg (smulRightL ℝ E F)]

/-! ### The conjugated coefficients -/

section Coefficients

variable (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
  (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F))
  (C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F))
  (ℓ : HolderSpace α E (E →L[ℝ] ℝ)) (M : HolderSpace α E (E →L[ℝ] E →L[ℝ] ℝ))

/-- The first-order coefficient `B_w H = B H + A (ℓ ⊗ H + H ⊗ ℓ)` of the operator conjugated by
the weight `exp φ` with gradient `ℓ = Dφ`, as a field in `C_b^{α,α/2}`. -/
def weightFirstOrderCoeff : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F) :=
  B + firstOrderCorrL.compHolder₂ A (HolderSpace.compLipschitzL _ lipschitzWith_slab_space ℓ)

/-- The zeroth-order coefficient `C_w y = C y + A ((M + ℓ ⊗ ℓ) ⊗ y) + B (ℓ ⊗ y)` of the operator
conjugated by the weight `exp φ` with gradient `ℓ = Dφ` and Hessian `M = D²φ`, as a field in
`C_b^{α,α/2}`. -/
def weightZerothOrderCoeff : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F) :=
  C + zerothOrderCorrL.compHolder₂ A (HolderSpace.compLipschitzL _ lipschitzWith_slab_space
      (M + (smulRightL ℝ E (E →L[ℝ] ℝ)).compHolder₂ ℓ ℓ)) +
    gradCorrL.compHolder₂ B (HolderSpace.compLipschitzL _ lipschitzWith_slab_space ℓ)

@[simp]
theorem weightFirstOrderCoeff_apply (p : slab (E := E) t₀ t₁) (H : E →L[ℝ] F) :
    weightFirstOrderCoeff A B ℓ p H = B p H +
      A p ((ℓ (p : ParabolicSpaceTime E).space).smulRight H +
        ((ℓ (p : ParabolicSpaceTime E).space).smulRight H).flip) := by
  simp [weightFirstOrderCoeff, firstOrderCorrL_apply]

/-- The zeroth-order coefficient, evaluated: the bilinear form `M + ℓ ⊗ ℓ` is tensored with `y`
through `Q ↦ ((smulRightL ℝ E F).flip y).comp Q`, that is `(h, k) ↦ Q h k • y`. -/
@[simp]
theorem weightZerothOrderCoeff_apply (p : slab (E := E) t₀ t₁) (y : F) :
    weightZerothOrderCoeff A B C ℓ M p y = C p y +
      A p (((smulRightL ℝ E F).flip y).comp (M (p : ParabolicSpaceTime E).space +
        (ℓ (p : ParabolicSpaceTime E).space).smulRight (ℓ (p : ParabolicSpaceTime E).space))) +
      B p ((ℓ (p : ParabolicSpaceTime E).space).smulRight y) := by
  have hQ (Q : E →L[ℝ] E →L[ℝ] ℝ) :
      precompL E (smulRightL ℝ E F) Q y = ((smulRightL ℝ E F).flip y).comp Q := by
    ext h k
    simp
  simp [weightZerothOrderCoeff, zerothOrderCorrL_apply, gradCorrL_apply, hQ]

/-- **Bound on the conjugated first-order coefficient.** `‖B_w‖ ≤ ‖B‖ + 2 ‖A‖ ‖ℓ‖`. -/
theorem norm_weightFirstOrderCoeff_le :
    ‖weightFirstOrderCoeff A B ℓ‖ ≤ ‖B‖ + 2 * ‖A‖ * ‖ℓ‖ := by
  refine (norm_add_le _ _).trans ?_
  gcongr
  refine (norm_compHolder₂_apply_le _ _ _).trans ?_
  gcongr
  · exact norm_firstOrderCorrL_le
  · exact ((HolderSpace.compLipschitzL _ _).le_of_opNorm_le
      (HolderSpace.norm_compLipschitzL_le_one _) _).trans_eq (one_mul _)

/-- **Bound on the conjugated zeroth-order coefficient.**
`‖C_w‖ ≤ ‖C‖ + ‖A‖ (‖M‖ + ‖ℓ‖²) + ‖B‖ ‖ℓ‖`. -/
theorem norm_weightZerothOrderCoeff_le :
    ‖weightZerothOrderCoeff A B C ℓ M‖ ≤ ‖C‖ + ‖A‖ * (‖M‖ + ‖ℓ‖ * ‖ℓ‖) + ‖B‖ * ‖ℓ‖ := by
  have hQ : ‖M + (smulRightL ℝ E (E →L[ℝ] ℝ)).compHolder₂ ℓ ℓ‖ ≤ ‖M‖ + ‖ℓ‖ * ‖ℓ‖ := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_compHolder₂_apply_le _ _ _).trans ?_
    nlinarith [norm_smulRightL_le (𝕜 := ℝ) (E := E) (Fₗ := E →L[ℝ] ℝ), norm_nonneg ℓ]
  have h₁ : ‖zerothOrderCorrL.compHolder₂ A (HolderSpace.compLipschitzL _
      (lipschitzWith_slab_space (a := t₀) (b := t₁))
        (M + (smulRightL ℝ E (E →L[ℝ] ℝ)).compHolder₂ ℓ ℓ))‖ ≤ ‖A‖ * (‖M‖ + ‖ℓ‖ * ‖ℓ‖) := by
    refine (norm_compHolder₂_apply_le _ _ _).trans ?_
    calc _ ≤ 1 * ‖A‖ * (‖M‖ + ‖ℓ‖ * ‖ℓ‖) := by
          gcongr
          · exact norm_zerothOrderCorrL_le
          · exact (((HolderSpace.compLipschitzL _ _).le_of_opNorm_le
              (HolderSpace.norm_compLipschitzL_le_one _) _).trans_eq (one_mul _)).trans hQ
      _ = _ := by ring
  have h₂ : ‖gradCorrL.compHolder₂ B (HolderSpace.compLipschitzL _
      (lipschitzWith_slab_space (a := t₀) (b := t₁)) ℓ)‖ ≤ ‖B‖ * ‖ℓ‖ := by
    refine (norm_compHolder₂_apply_le _ _ _).trans ?_
    calc _ ≤ 1 * ‖B‖ * ‖ℓ‖ := by
          gcongr
          · exact norm_gradCorrL_le
          · exact ((HolderSpace.compLipschitzL _ _).le_of_opNorm_le
      (HolderSpace.norm_compLipschitzL_le_one _) _).trans_eq (one_mul _)
      _ = _ := by ring
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) h₂)
  gcongr

end Coefficients

end Bilinear

/-! ### The conjugation identity -/

section Conjugation

variable {A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)}
  {B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F)}
  {C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)}
  {ℓ : HolderSpace α E (E →L[ℝ] ℝ)} {M : HolderSpace α E (E →L[ℝ] E →L[ℝ] ℝ)} {φ : E → ℝ}

/-- **The gradient of a weighted slice.** For `v ∈ C_b^{2+α,1+α/2}` and `ℓ = Dφ`, the slice
`y ↦ exp (φ y) • v (y, t)` has gradient `exp (φ x) • (D_x v + ℓ ⊗ v)` at `x`. -/
theorem hasFDerivAt_exp_smul_slice (hφ : ∀ x, HasFDerivAt φ (ℓ x) x)
    (v : ParabolicC2HolderSpace α E F ht) (t : Icc t₀ t₁) (x : E) :
    HasFDerivAt (fun y ↦ Real.exp (φ y) • v (slabMk y t))
      (Real.exp (φ x) • (spatialFDerivL v (slabMk x t) + (ℓ x).smulRight (v (slabMk x t)))) x := by
  refine (((hφ x).exp).smul (v.hasSpatialFDerivAt t x)).congr_fderiv ?_
  ext h
  simp [smul_add, smul_smul]

/-- **The Hessian of a weighted slice.** For `v ∈ C_b^{2+α,1+α/2}`, `ℓ = Dφ` and `M = D²φ`, the
gradient of `y ↦ exp (φ y) • v (y, t)` has derivative
`exp (φ x) • (D_x²v + ℓ ⊗ D_xv + (ℓ ⊗ D_xv)ᵀ + (M + ℓ ⊗ ℓ) ⊗ v)` at `x`, where `Q ⊗ y` is
`(h, k) ↦ Q h k • y`. -/
theorem hasFDerivAt_fderiv_exp_smul_slice (hφ : ∀ x, HasFDerivAt φ (ℓ x) x)
    (hℓ : ∀ x, HasFDerivAt (fun y ↦ ℓ y) (M x) x) (v : ParabolicC2HolderSpace α E F ht)
    (t : Icc t₀ t₁) (x : E) :
    HasFDerivAt (fderiv ℝ fun y ↦ Real.exp (φ y) • v (slabMk y t))
      (Real.exp (φ x) • (spatialSecondFDerivL v (slabMk x t) +
        ((ℓ x).smulRight (spatialFDerivL v (slabMk x t)) +
          ((ℓ x).smulRight (spatialFDerivL v (slabMk x t))).flip) +
        ((smulRightL ℝ E F).flip (v (slabMk x t))).comp (M x + (ℓ x).smulRight (ℓ x)))) x := by
  rw [funext fun y ↦ (hasFDerivAt_exp_smul_slice hφ v t y).fderiv]
  have hK := (v.hasSpatialSecondFDerivAt t x).add
    ((smulRightL ℝ E F).hasFDerivAt_of_bilinear (hℓ x) (v.hasSpatialFDerivAt t x))
  refine (((hφ x).exp).smul hK).congr_fderiv ?_
  ext h k
  simp [mul_smul]
  module

variable (hα : α ≤ 1)

/-- **The conjugation identity** `w P_w v = P (w v)` for the weight `w = exp φ`. Let `ℓ` and `M`
be the gradient and Hessian of `φ`, and let `u = w v` with `v ∈ C_b^{2+α,1+α/2}`. Then at every
point of the slab, `w` times the conjugated operator applied to `v` is the operator
`P u = ∂ₜu - A·D_x²u - B·D_xu - C·u`, computed from the classical derivatives of `u`. The
function `u` need not be bounded. -/
theorem exp_smul_parabolicOperatorL_weightCoeff (hφ : ∀ x, HasFDerivAt φ (ℓ x) x)
    (hℓ : ∀ x, HasFDerivAt (fun y ↦ ℓ y) (M x) x) (v : ParabolicC2HolderSpace α E F ht)
    {u : slab (E := E) t₀ t₁ → F}
    (hu : ∀ p, u p = Real.exp (φ (p : ParabolicSpaceTime E).space) • v p) (x : E)
    (t : Icc t₀ t₁) :
    Real.exp (φ x) • parabolicOperatorL hα A (weightFirstOrderCoeff A B ℓ)
        (weightZerothOrderCoeff A B C ℓ M) v (slabMk x t) =
      derivWithin (timeExtension ht.le u x) (Icc t₀ t₁) t -
        (A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
          B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) +
            C (slabMk x t) (u (slabMk x t))) := by
  have hslice : (fun y ↦ u (slabMk y t)) = fun y ↦ Real.exp (φ y) • v (slabMk y t) :=
    funext fun y ↦ by rw [hu, space_slabMk]
  have htime : timeExtension ht.le u x = Real.exp (φ x) • timeExtension ht.le v x :=
    funext fun s ↦ by simp [timeExtension_def, hu]
  rw [hslice, (hasFDerivAt_fderiv_exp_smul_slice hφ hℓ v t x).fderiv,
    (hasFDerivAt_exp_smul_slice hφ v t x).fderiv, htime,
    ((v.hasTimeDerivWithinAt x t).const_smul (Real.exp (φ x))).derivWithin
      (uniqueDiffOn_Icc ht t t.2), hu]
  simp only [parabolicOperatorL_apply, weightFirstOrderCoeff_apply,
    weightZerothOrderCoeff_apply, space_slabMk, map_smul, map_add, smul_sub, smul_add]
  abel

/-- **Weighted solutions.** `v ∈ C_b^{2+α,1+α/2}` solves the conjugated equation `P_w v = g` if
and only if `u = exp φ • v` is a classical solution of `P u = exp φ • g`: forcing terms transform
by division by the weight. -/
theorem parabolicOperatorL_weightCoeff_eq_iff (hφ : ∀ x, HasFDerivAt φ (ℓ x) x)
    (hℓ : ∀ x, HasFDerivAt (fun y ↦ ℓ y) (M x) x) (v : ParabolicC2HolderSpace α E F ht)
    {u : slab (E := E) t₀ t₁ → F}
    (hu : ∀ p, u p = Real.exp (φ (p : ParabolicSpaceTime E).space) • v p)
    (g : HolderSpace α (slab (E := E) t₀ t₁) F) :
    parabolicOperatorL hα A (weightFirstOrderCoeff A B ℓ) (weightZerothOrderCoeff A B C ℓ M) v =
        g ↔
      ∀ (x : E) (t : Icc t₀ t₁), derivWithin (timeExtension ht.le u x) (Icc t₀ t₁) t -
        (A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
          B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) +
            C (slabMk x t) (u (slabMk x t))) =
        Real.exp (φ x) • g (slabMk x t) := by
  constructor
  · intro h x t
    rw [← exp_smul_parabolicOperatorL_weightCoeff hα hφ hℓ v hu x t, h]
  · intro h
    refine HolderSpace.ext fun p ↦ ?_
    rw [← slabMk_space_slabTime p]
    have hp := h (p : ParabolicSpaceTime E).space (slabTime p)
    rw [← exp_smul_parabolicOperatorL_weightCoeff hα hφ hℓ v hu] at hp
    exact smul_right_injective F (Real.exp_pos _).ne' hp

end Conjugation

end TauCeti.ParabolicC2HolderSpace

/-! ### The weight `1 + exp x` on the line -/

namespace TauCeti

open Set ParabolicSpaceTime ContinuousLinearMap Real
open scoped NNReal

variable {α : ℝ≥0} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ}
  {ht : t₀ < t₁} (hα : α ≤ 1)

/-- A local shortcut for the norm on Hessians on the line, needed for the operator norm on the
coefficient space `(ℝ →L[ℝ] ℝ →L[ℝ] F) →L[ℝ] F`. -/
local instance lineNormedAddCommGroupHessian :
    NormedAddCommGroup (ℝ →L[ℝ] ℝ →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians on the line. -/
local instance lineNormedSpaceHessian : NormedSpace ℝ (ℝ →L[ℝ] ℝ →L[ℝ] F) := inferInstance

/-- The gradient `x ↦ sigmoid x` of `log (1 + exp x)`, as a bounded `α`-Hölder field of covectors
on `ℝ`. -/
def logOneAddExpGrad : HolderSpace α ℝ (ℝ →L[ℝ] ℝ) :=
  (smulRightL ℝ ℝ ℝ).compHolder₂ (HolderSpace.const 1) <| HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup sigmoid continuous_sigmoid 1 fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sigmoid_nonneg x)]
      exact sigmoid_le_one x)
    (by simpa using memHolder_iteratedDeriv_sigmoid 0 hα)

/-- The Hessian `x ↦ sigmoid x (1 - sigmoid x)` of `log (1 + exp x)`, as a bounded `α`-Hölder
field of bilinear forms on `ℝ`. -/
def logOneAddExpHess : HolderSpace α ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) :=
  (smulRightL ℝ ℝ (ℝ →L[ℝ] ℝ)).compHolder₂ (HolderSpace.const 1) <|
    (smulRightL ℝ ℝ ℝ).compHolder₂ (HolderSpace.const 1) <| HolderSpace.ofBoundedContinuousFunction
      (BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ sigmoid x * (1 - sigmoid x))
        (by fun_prop) 1 fun x ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sigmoid_nonneg x)
            (sub_nonneg.2 (sigmoid_le_one x)))]
          nlinarith [sigmoid_nonneg x, sigmoid_le_one x])
      (by simpa [deriv_sigmoid] using memHolder_iteratedDeriv_sigmoid 1 hα)

@[simp]
theorem logOneAddExpGrad_apply (x : ℝ) :
    logOneAddExpGrad hα x = toSpanSingleton ℝ (sigmoid x) := by
  ext
  simp [logOneAddExpGrad]

@[simp]
theorem logOneAddExpHess_apply (x : ℝ) :
    logOneAddExpHess hα x =
      toSpanSingleton ℝ (toSpanSingleton ℝ (sigmoid x * (1 - sigmoid x))) := by
  ext
  simp [logOneAddExpHess]

/-- `logOneAddExpGrad` is the gradient of `x ↦ log (1 + exp x)`. -/
theorem hasFDerivAt_log_one_add_exp (x : ℝ) :
    HasFDerivAt (fun x ↦ log (1 + exp x)) (logOneAddExpGrad hα x) x := by
  simpa using (hasDerivAt_log_one_add_exp x).hasFDerivAt

/-- `logOneAddExpHess` is the derivative of `logOneAddExpGrad`. -/
theorem hasFDerivAt_logOneAddExpGrad (x : ℝ) :
    HasFDerivAt (fun y ↦ logOneAddExpGrad hα y) (logOneAddExpHess hα x) x := by
  have h := ((toSpanSingletonLIE (𝕜 := ℝ) (E := ℝ)).toContinuousLinearEquiv.hasFDerivAt
    ).comp_hasDerivAt x (hasDerivAt_sigmoid x)
  simp only [logOneAddExpGrad_apply, logOneAddExpHess_apply]
  exact h.hasFDerivAt

/-- **The conjugation identity for the weight `1 + exp x` on `ℝ`.** For `u = (1 + exp x) • v`
with `v ∈ C_b^{2+α,1+α/2}`, the operator `P u` computed from the classical derivatives of `u` is
`(1 + exp x)` times the conjugated operator, whose coefficients are bounded parabolic Hölder fields
built from `sigmoid` and its derivative. -/
theorem ParabolicC2HolderSpace.one_add_exp_smul_parabolicOperatorL_weightCoeff
    {A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] F) →L[ℝ] F)}
    {B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] F) →L[ℝ] F)}
    {C : HolderSpace α (slab (E := ℝ) t₀ t₁) (F →L[ℝ] F)}
    (v : ParabolicC2HolderSpace α ℝ F ht) {u : slab (E := ℝ) t₀ t₁ → F}
    (hu : ∀ p, u p = (1 + exp (p : ParabolicSpaceTime ℝ).space) • v p) (x : ℝ)
    (t : Icc t₀ t₁) :
    (1 + exp x) • parabolicOperatorL hα A (weightFirstOrderCoeff A B (logOneAddExpGrad hα))
        (weightZerothOrderCoeff A B C (logOneAddExpGrad hα) (logOneAddExpHess hα)) v
        (slabMk x t) =
      derivWithin (timeExtension ht.le u x) (Icc t₀ t₁) t -
        (A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
          B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) +
            C (slabMk x t) (u (slabMk x t))) := by
  have hexp (y : ℝ) : exp (log (1 + exp y)) = 1 + exp y := exp_log (by positivity)
  simpa only [hexp] using exp_smul_parabolicOperatorL_weightCoeff hα
    (hasFDerivAt_log_one_add_exp hα) (hasFDerivAt_logOneAddExpGrad hα) v
    (fun p ↦ by rw [hu, hexp]) x t

end TauCeti
