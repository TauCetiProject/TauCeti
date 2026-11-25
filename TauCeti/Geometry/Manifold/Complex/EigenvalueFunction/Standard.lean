/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.EigenvalueFunction
public import TauCeti.Analysis.Complex.LeviForm.Laplacian

/-!
# The standard Hermitian metric and the flat complex Laplacian

On a complex inner product space `V`, regarded as a complex manifold modelled on itself, the
**standard Hermitian metric** `TauCeti.standardHermitianMetric V` is the constant real two-form
`ω(u, v) = Im ⟪u, v⟫`; on `ℂⁿ` it is `Σ_j dx_j ∧ dy_j`. Its Hermitian form is the inner product
(`TauCeti.twoFormHermitianForm_standardHermitianMetric`), and it is a Hermitian metric: it is
compatible with multiplication by `i` (`TauCeti.compatible_standardHermitianMetric`).

Relative to it, the eigenvalue function of `i ∂∂bar φ` is the relative eigenvalue vector of
`2 L_φ(x)` for the inner product, and the complex Laplacian is half the Euclidean Laplacian,
`Δ_ω φ = Δ φ / 2` (`TauCeti.complexLaplacian_standardHermitianMetric`), where `Δ` is the Laplacian
for the real inner product `Re ⟪·, ·⟫`; on `ℂⁿ` this is
`Δ_ω φ = (1/2)·Σ_j (∂²φ/∂x_j² + ∂²φ/∂y_j²)`.

## Main definitions

* `TauCeti.standardHermitianMetric V`: the constant two-form `ω(u, v) = Im ⟪u, v⟫`.

## Main results

* `TauCeti.twoFormHermitianForm_standardHermitianMetric`: `H_ω = ⟪·, ·⟫`.
* `TauCeti.compatible_standardHermitianMetric`: `ω` is a Hermitian metric.
* `TauCeti.relEigenvalueFunction_standardHermitianMetric`: `λ_ω[i ∂∂bar φ](x)` is the relative
  eigenvalue vector of `2 L_φ(x)` for the inner product.
* `TauCeti.complexLaplacian_standardHermitianMetric`: `Δ_ω φ = Δ φ / 2` for `φ` of class `C²`.
-/

public section

open Complex Module
open scoped ContDiff Manifold InnerProductSpace Laplacian

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable (V) in
/-- The real bilinear form `(u, v) ↦ Im ⟪u, v⟫` of a complex inner product space. -/
def imInnerBilin : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun u v ↦ (⟪u, v⟫_ℂ).im)
      (fun u u' v ↦ by simp [inner_add_left])
      (fun r u v ↦ by simp [← Complex.coe_smul, inner_smul_left])
      (fun u v v' ↦ by simp [inner_add_right])
      (fun r u v ↦ by simp [← Complex.coe_smul, inner_smul_right]))
    1 fun u v ↦ by
      simpa using (abs_im_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) u v)

/-- `imInnerBilin V u v = Im ⟪u, v⟫`. -/
@[simp]
theorem imInnerBilin_apply (u v : V) : imInnerBilin V u v = (⟪u, v⟫_ℂ).im :=
  (rfl)

variable (V) in
/-- The **standard Hermitian metric** `ω(u, v) = Im ⟪u, v⟫` of a complex inner product space `V`,
as a constant smooth two-form on `V`. On `ℂⁿ` it is `Σ_j dx_j ∧ dy_j`, so that `ω(1, i) = 1` on
`ℂ`. Its Hermitian form is the inner product. -/
def standardHermitianMetric : SmoothTwoForm 𝓘(ℝ, V) V :=
  SmoothTwoForm.const (imInnerBilin V)

/-- The standard Hermitian metric evaluates as `ω(u, v) = Im ⟪u, v⟫`. -/
theorem standardHermitianMetric_apply (x : V) (v : Fin 2 → V) :
    (standardHermitianMetric V).val x v = (⟪v 0, v 1⟫_ℂ).im := by
  rw [standardHermitianMetric, SmoothTwoForm.const_eq]
  erw [SmoothForm.const_apply]
  simp only [ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.alternatizeBilinCLM_apply, imInnerBilin_apply, smul_eq_mul]
  change 2⁻¹ * ((⟪v 0, v 1⟫_ℂ).im - (⟪v 1, v 0⟫_ℂ).im) = _
  rw [← inner_conj_symm (v 1), conj_im]
  ring

/-- **The Hermitian form of the standard metric is the inner product**:
`H_ω(u, v) = ω(u, i v) + i·ω(u, v) = ⟪u, v⟫`. -/
@[simp]
theorem twoFormHermitianForm_standardHermitianMetric (x u v : V) :
    twoFormHermitianForm V (standardHermitianMetric V).val x u v = ⟪u, v⟫_ℂ := by
  rw [twoFormHermitianForm_def]
  erw [standardHermitianMetric_apply, standardHermitianMetric_apply]
  apply Complex.ext <;> simp [inner_smul_right]

/-- **The standard metric is a Hermitian metric**: it is invariant under, and tames,
multiplication by `i`. -/
theorem compatible_standardHermitianMetric :
    (standardHermitianMetric V).Compatible
      (SmoothAlmostComplexStructure.ofComplexManifold V V) := by
  have hJ (x u : V) :
      (SmoothAlmostComplexStructure.ofComplexManifold V V).toEndomorphism x u = I • u :=
    SmoothAlmostComplexStructure.ofComplexManifold_apply x u
  have hinv (v w : V) : (⟪I • v, I • w⟫_ℂ).im = (⟪v, w⟫_ℂ).im := by
    simp [inner_smul_left, inner_smul_right]
  have htame (v : V) (hv : v ≠ 0) : 0 < (⟪v, I • v⟫_ℂ).im := by
    simpa [inner_smul_right, inner_self_eq_norm_sq_to_K, ← ofReal_pow] using
      pow_pos (norm_pos_iff.2 hv) 2
  refine ⟨SmoothTwoForm.invariant_iff.2 fun x v w ↦ ?_, SmoothTwoForm.tames_iff.2 fun x v hv ↦ ?_⟩
  · rw [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply]
    beta_reduce
    erw [hJ, hJ, standardHermitianMetric_apply, standardHermitianMetric_apply]
    exact hinv v w
  · rw [SmoothBundleForm.eval₂_apply]
    beta_reduce
    erw [hJ, standardHermitianMetric_apply]
    exact htame v hv

variable [FiniteDimensional ℂ V] {φ : V → ℝ} {x : V}

/-- **The eigenvalue function of `i ∂∂bar φ` relative to the standard metric** is the relative
eigenvalue vector of `2 L_φ(x)` for the inner product. -/
theorem relEigenvalueFunction_standardHermitianMetric (h : ((2 : ℂ) • leviForm φ x).IsSymm) :
    relEigenvalueFunction V (standardHermitianMetric V) 0 φ x = h.relEigenvalues rfl := by
  refine compatible_standardHermitianMetric.relEigenvalueFunction_eq_of_isRelEigenvalueVector
    (fun _ _ ↦ by simp) ?_ (h.relEigenvalues_antitone rfl)
  have hH : twoFormHermitianForm V (standardHermitianMetric V).val x =
      fun u v ↦ innerₛₗ ℂ u v := by
    ext u v
    simp
  have hD : ddbarHermitianForm V 0 φ x = fun u v ↦ ((2 : ℂ) • leviForm φ x) u v := by
    ext u v
    simp [manifoldLeviForm_eq_leviForm]
  rw [hH, hD]
  exact h.isRelEigenvalueVector_relEigenvalues

section Laplacian

attribute [local instance] InnerProductSpace.complexToReal

/-- **The complex Laplacian of the standard metric is half the Laplacian**: for `φ` of class `C²`
at `x`, `Δ_ω φ(x) = Δ φ(x) / 2`, where `Δ` is the Laplacian for the real inner product
`Re ⟪·, ·⟫`. On `ℂⁿ` this is `Δ_ω φ = (1/2)·Σ_j (∂²φ/∂x_j² + ∂²φ/∂y_j²)`. -/
theorem complexLaplacian_standardHermitianMetric (hφ : ContDiffAt ℝ 2 φ x) :
    complexLaplacian V (standardHermitianMetric V) φ x = Δ φ x / 2 := by
  rw [compatible_standardHermitianMetric.complexLaplacian_eq_two_mul_sum
    (contMDiffAt_iff_contDiffAt.2 hφ) (stdOrthonormalBasis ℂ V) fun i j ↦ by
      simp [orthonormal_iff_ite.1 (stdOrthonormalBasis ℂ V).orthonormal]]
  simp only [manifoldLeviForm_eq_leviForm]
  rw [sum_re_leviForm_apply_self (stdOrthonormalBasis ℂ V)]
  ring

end Laplacian

end TauCeti
