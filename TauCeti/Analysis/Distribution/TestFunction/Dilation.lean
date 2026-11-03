/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Divergence
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Dilation of test functions

Dilating the support of a test function by a nonzero real scalar amounts to precomposing with
its inverse. The derivative, gradient and divergence acquire the inverse scalar. These formulas
transport the test-field pairings that define distributional variation and perimeter under
dilations, and the homogeneous Sobolev norms of test functions.
Combining dilation with translation rescales a test vector field around a point `x`
(`TestFunction.exists_eq_comp`); for small ratios the rescaled support stays inside any
open neighbourhood of `x` (`TauCeti.eventually_forall_tsupport_add_smul_mem`).
-/

public section

noncomputable section

namespace TauCeti

open Set Filter Metric TestFunction TopologicalSpace
open scoped Distributions Gradient Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω V : Opens E} {r : ℝ}

/-- Dilate the support of a test function by `r`, regarding it as a test function on any open
set containing the dilated original domain. -/
def dilateTestFunction (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω) (φ : 𝓓(V, F)) :
    𝓓(Ω, F) :=
  ⟨fun y => φ (r⁻¹ • y), φ.contDiff.comp (contDiff_const.smul contDiff_id),
    by
      simpa only [Homeomorph.smulOfNeZero_apply, Function.comp_def] using
        φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)),
    by
      intro y hy
      have hy' : r⁻¹ • y ∈ tsupport (φ : E → F) := by
        -- Composition with this homeomorphism is definitionally the lambda defining the dilation.
        have hycomp : y ∈ tsupport
            ((φ : E → F) ∘ Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)) := hy
        rw [tsupport_comp_eq_preimage] at hycomp
        exact hycomp
      simpa only [smul_inv_smul₀ hr] using hVO (φ.tsupport_subset hy')⟩

/-- Evaluation of a test function whose support has been dilated. -/
@[simp]
theorem dilateTestFunction_apply (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (φ : 𝓓(V, F)) (y : E) : dilateTestFunction hr hVO φ y = φ (r⁻¹ • y) :=
  (rfl)

/-- The derivative of a dilated test function acquires the inverse dilation factor. -/
@[simp]
theorem fderiv_dilateTestFunction (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (φ : 𝓓(V, F)) (y : E) :
    fderiv ℝ (dilateTestFunction hr hVO φ : E → F) y =
      r⁻¹ • fderiv ℝ (φ : E → F) (r⁻¹ • y) :=
  fderiv_comp_smul _

/-- The directional derivative of a dilated test function acquires the inverse dilation factor. -/
@[simp]
theorem lineDeriv_dilateTestFunction (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (φ : 𝓓(V, F)) (y w : E) :
    lineDeriv ℝ (dilateTestFunction hr hVO φ : E → F) y w =
      r⁻¹ • lineDeriv ℝ (φ : E → F) (r⁻¹ • y) w := by
  have hd := (dilateTestFunction hr hVO φ).contDiff.differentiable (by simp)
  rw [(hd y).lineDeriv_eq_fderiv,
    (φ.contDiff.differentiable (by simp) (r⁻¹ • y)).lineDeriv_eq_fderiv,
    fderiv_dilateTestFunction]
  simp only [smul_apply]

/-- The divergence of a dilated test vector field acquires the inverse dilation factor. -/
@[simp]
theorem divergenceCLM_dilateTestFunction [FiniteDimensional ℝ E]
    (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω) (φ : 𝓓(V, E)) :
    divergenceCLM (dilateTestFunction hr hVO φ) =
      r⁻¹ • dilateTestFunction hr hVO (divergenceCLM φ) := by
  ext y
  simp

/-- The gradient of a dilated real test function acquires the inverse dilation factor. -/
@[simp]
theorem gradient_dilateTestFunction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Ω V : Opens H} (hr : r ≠ 0) (hVO : MapsTo (fun x : H => r • x) V Ω)
    (φ : 𝓓(V, ℝ)) (y : H) :
    ∇ (dilateTestFunction hr hVO φ : H → ℝ) y = r⁻¹ • ∇ (φ : H → ℝ) (r⁻¹ • y) := by
  apply (InnerProductSpace.toDual ℝ H).injective
  simp [toDual_gradient]

/-- For small `r > 0` the support of a test function on `E`, rescaled by `r` around `x ∈ Ω`, lies
in `Ω`. -/
theorem eventually_forall_tsupport_add_smul_mem {x : E} (hx : x ∈ Ω) (φ : 𝓓((⊤ : Opens E), F)) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ y ∈ tsupport φ, x + r • y ∈ Ω := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  obtain ⟨ε, hε, hεΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds hx)
  have hR1 : 0 < max R 1 := lt_max_of_lt_right one_pos
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε hR1)] with r hr y hy
  refine hεΩ ?_
  have hy' : ‖y‖ ≤ max R 1 := (mem_closedBall_zero_iff.1 (hR hy)).trans (le_max_left _ _)
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.1.le]
  calc r * ‖y‖ ≤ r * max R 1 := mul_le_mul_of_nonneg_left hy' hr.1.le
    _ ≤ ε := ((lt_div_iff₀ hR1).1 hr.2).le

end TauCeti

namespace TestFunction

open Set TauCeti TopologicalSpace
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

/-- Rescaling a test vector field on `E` around `x` by a ratio `r ≠ 0` gives a test vector field
on `Ω`, provided the rescaled support lies in `Ω`. -/
theorem exists_eq_comp [FiniteDimensional ℝ E] {x : E} (φ : 𝓓((⊤ : Opens E), E))
    {r : ℝ} (hr : r ≠ 0) (hΩ : ∀ y ∈ tsupport φ, x + r • y ∈ Ω) :
    ∃ ψ : 𝓓(Ω, E), (∀ y, ψ y = φ (r⁻¹ • (y - x))) ∧
      ∀ y, divergenceCLM ψ y = r⁻¹ * divergenceCLM φ (r⁻¹ • (y - x)) := by
  have htop {f : E → E} : MapsTo f (⊤ : Opens E) (⊤ : Opens E) := by
    rw [Opens.coe_top]
    exact mapsTo_univ _ _
  let ψ' : 𝓓((⊤ : Opens E), E) :=
    translateTestFunction (h := x) htop (dilateTestFunction hr htop φ)
  have hψ' (y : E) : ψ' y = φ (r⁻¹ • (y - x)) := by
    rw [translateTestFunction_apply, dilateTestFunction_apply]
  -- The support of `ψ'` lies in the image of the support of `φ` under `z ↦ x + r • z`.
  have hsub : Function.support (ψ' : E → E) ⊆ (fun z => x + r • z) '' tsupport φ := fun y hy =>
    ⟨r⁻¹ • (y - x), subset_tsupport _ (by rwa [Function.mem_support, ← hψ']),
      by simp [smul_inv_smul₀ hr]⟩
  have hsupp : tsupport (ψ' : E → E) ⊆ Ω := by
    refine (closure_minimal hsub
      (φ.hasCompactSupport.isCompact.image (by fun_prop)).isClosed).trans ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hΩ y hy
  refine ⟨⟨ψ', ψ'.contDiff, ψ'.hasCompactSupport, hsupp⟩, fun y => by rw [coe_mk, hψ'],
    fun y => ?_⟩
  rw [divergenceCLM_apply, coe_mk, ← divergenceCLM_apply, divergenceCLM_translateTestFunction,
    translateTestFunction_apply, divergenceCLM_dilateTestFunction]
  simp only [IsSMulApply.smul_apply, dilateTestFunction_apply, smul_eq_mul]

end TestFunction
