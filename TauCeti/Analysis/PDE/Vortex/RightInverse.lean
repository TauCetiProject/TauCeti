/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.InnerProductSpace.AdjointRightInverse
public import TauCeti.Analysis.PDE.Vortex.SpectralGap

/-!
# The `L²` right inverse of the gauge-fixed vortex operator

In the coordinates of `TauCeti.Vortex.equation`, the gauge-fixed operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) of a field `x` has the formal adjoint
`L_x*` (`TauCeti.Vortex.gaugeFixedAdjoint`). A field `u ∈ L²` solves `L_x u = f` weakly when

`∫ ⟪u, L_x* η⟫ = ∫ ⟪f, η⟫`

for every compactly supported `C²` test field `η ∈ 𝓓²(ℂ)`. By integration by parts
(`TauCeti.Vortex.integral_inner_gaugeFixedOperator`) every compactly supported `C¹` solution is a
weak solution.

At an actual vortex with `|α| → 1`, the spectral gap `c ∫ |η|² ≤ ∫ |L_x* η|²`
(`TauCeti.Vortex.exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint`)
says that `L_x*` is bounded below on test fields. Hence the weak `L²` realization of `L_x` is
onto: `TauCeti.Vortex.gaugeFixedRightInverse μ x` is a bounded operator on `L²` with
`L_x (R f) = f` weakly for every `f`
(`TauCeti.Vortex.integral_inner_gaugeFixedRightInverse_of_equation_eq_zero`). This is the
cokernel vanishing of the vortex deformation operator, in its weak `L²` form. Under a gap
constant `c` the operator has norm at most `c^(-1/2)`
(`TauCeti.Vortex.norm_gaugeFixedRightInverse_le`), and `R f` is the unique weak solution of
least norm (`TauCeti.Vortex.gaugeFixedRightInverse_apply_eq_iff`); formally, this is the
minimal-norm right inverse `L_x* (L_x L_x*)⁻¹`. It is constructed by
`LinearMap.adjointRightInverse` from the lower bound alone. No decay of the connection or of
derivatives is assumed.

The regularity of `R f`, the `H¹ → L²` Fredholm property and the identification of the kernel
of `L_x` are separate.

## Main results

* `TauCeti.Vortex.gaugeFixedRightInverse`: the minimal-norm `L²` right inverse of `L_x`.
* `TauCeti.Vortex.integral_inner_gaugeFixedRightInverse`: it solves `L_x u = f` weakly,
  whenever `L_x*` has a spectral gap.
* `TauCeti.Vortex.integral_inner_gaugeFixedRightInverse_of_equation_eq_zero`: the same at an
  actual vortex with unit-modulus end.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011, Theorem 2.20.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter TopologicalSpace
open scoped Distributions RealInnerProductSpace Topology

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- A test field has square-integrable `L_x*` when the field `x` is continuous. -/
private theorem memLp_gaugeFixedAdjoint (hx : Continuous x)
    (η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4))) :
    MemLp (gaugeFixedAdjoint x η) 2 μ :=
  (continuous_gaugeFixedAdjoint hx (η.contDiff.of_le (by norm_num))).memLp_of_hasCompactSupport
    (hasCompactSupport_gaugeFixedAdjoint η.hasCompactSupport)

/-- Test fields as elements of `L²`. -/
private def testToLp : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)) →ₗ[ℝ]
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun η := (η.continuous.memLp_of_hasCompactSupport η.hasCompactSupport).toLp η
  map_add' η ν := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_eq (by ext; simp))
  map_smul' t η := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_eq (by ext; simp))

/-- The formal adjoint `L_x*` on test fields, with values in `L²`. -/
private def adjointToLp (hx : Continuous x) :
    𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)) →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun η := (memLp_gaugeFixedAdjoint μ hx η).toLp _
  map_add' η ν := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ ?_)
    have h₂ := (η.contDiff.differentiable (by norm_num)).differentiableAt (x := z)
    have h₂' := (ν.contDiff.differentiable (by norm_num)).differentiableAt (x := z)
    exact gaugeFixedAdjoint_add x h₂ h₂'
  map_smul' t η := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ gaugeFixedAdjoint_smul x η t z)

variable {μ}

private theorem inner_testToLp (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
    (η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4))) :
    ⟪u, testToLp μ η⟫ = ∫ z, ⟪u z, η z⟫ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (η.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2)
    η.hasCompactSupport)] with z hz
  simp only [testToLp, LinearMap.coe_mk, AddHom.coe_mk, hz]

private theorem inner_adjointToLp (hx : Continuous x) (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
    (η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4))) :
    ⟪u, adjointToLp μ hx η⟫ = ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_gaugeFixedAdjoint μ hx η)] with z hz
  simp only [adjointToLp, LinearMap.coe_mk, AddHom.coe_mk, hz]

omit [μ.IsAddHaarMeasure] in
/-- The squared `L²` norm, as the integral of the pointwise squared norm. -/
private theorem norm_sq_eq_integral (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    ‖u‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- A spectral gap for `L_x*` bounds test fields by their image, in `L²`. -/
private theorem norm_testToLp_le (hx : Continuous x) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)),
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    (η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4))) :
    ‖testToLp μ η‖ ≤ (√c)⁻¹ * ‖adjointToLp μ hx η‖ := by
  have hη : ‖testToLp μ η‖ ^ 2 = ∫ z, ‖η z‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, inner_testToLp]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (η.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2)
      η.hasCompactSupport)] with z hz
    simp only [testToLp, LinearMap.coe_mk, AddHom.coe_mk, hz, real_inner_self_eq_norm_sq]
  have hL : ‖adjointToLp μ hx η‖ ^ 2 = ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := by
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_gaugeFixedAdjoint μ hx η)] with z hz
    simp only [adjointToLp, LinearMap.coe_mk, AddHom.coe_mk, hz]
  have hsq : (√c * ‖testToLp μ η‖) ^ 2 ≤ ‖adjointToLp μ hx η‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le, hη, hL]
    exact hgap η
  have hle := (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq
  rw [inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.mpr hc), mul_comm]
  exact hle

variable (μ x)

/-- **The `L²` right inverse of the gauge-fixed vortex operator.** For a continuous field `x`
whose formal adjoint `L_x*` has a spectral gap `c ∫ |η|² ≤ ∫ |L_x* η|²` on test fields, this is
the bounded operator on `L²` sending `f` to the weak solution of `L_x u = f` of least norm
(`TauCeti.Vortex.integral_inner_gaugeFixedRightInverse`,
`TauCeti.Vortex.gaugeFixedRightInverse_apply_eq_iff`). Formally, it is the minimal-norm right
inverse `L_x* (L_x L_x*)⁻¹`. For a discontinuous field it is `0`. -/
def gaugeFixedRightInverse :
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ :=
  open scoped Classical in
  if hx : Continuous x then (adjointToLp μ hx).adjointRightInverse (testToLp μ) else 0

variable {μ x}

private theorem gaugeFixedRightInverse_eq (hx : Continuous x) :
    gaugeFixedRightInverse μ x = (adjointToLp μ hx).adjointRightInverse (testToLp μ) := by
  simp [gaugeFixedRightInverse, hx]

private theorem exists_norm_testToLp_le (hx : Continuous x)
    (hgap : ∃ c > 0, ∀ η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)),
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) :
    ∃ C, ∀ η, ‖testToLp μ η‖ ≤ C * ‖adjointToLp μ hx η‖ :=
  let ⟨_, hc, hgap⟩ := hgap
  ⟨_, norm_testToLp_le hx hc hgap⟩

/-- **`L_x` is onto `L²` in the weak sense.** If `L_x*` has a spectral gap on test fields, then
`u = gaugeFixedRightInverse μ x f` solves `L_x u = f` weakly:
`∫ ⟪u, L_x* η⟫ = ∫ ⟪f, η⟫` for every test field `η`. -/
theorem integral_inner_gaugeFixedRightInverse (hx : Continuous x)
    (hgap : ∃ c > 0, ∀ η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)),
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
    (η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ⟪gaugeFixedRightInverse μ x f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ := by
  rw [← inner_adjointToLp hx, ← inner_testToLp, gaugeFixedRightInverse_eq hx]
  exact LinearMap.inner_adjointRightInverse_apply (exists_norm_testToLp_le hx hgap) f η

/-- **The norm bound.** A spectral gap `c ∫ |η|² ≤ ∫ |L_x* η|²` bounds the right inverse by
`c^(-1/2)`. -/
theorem norm_gaugeFixedRightInverse_le (hx : Continuous x) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)),
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) :
    ‖gaugeFixedRightInverse μ x‖ ≤ (√c)⁻¹ := by
  rw [gaugeFixedRightInverse_eq hx]
  exact LinearMap.norm_adjointRightInverse_le (by positivity) (norm_testToLp_le hx hc hgap)

/-- **Characterization by least norm.** If `L_x*` has a spectral gap on test fields, then
`gaugeFixedRightInverse μ x f` is the unique weak solution of `L_x u = f` of least `L²` norm. -/
theorem gaugeFixedRightInverse_apply_eq_iff (hx : Continuous x)
    (hgap : ∃ c > 0, ∀ η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)),
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    gaugeFixedRightInverse μ x f = u ↔
      (∀ η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)),
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) ∧
      ∀ v : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)),
          ∫ z, ⟪v z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) → ‖u‖ ≤ ‖v‖ := by
  simp only [← inner_adjointToLp hx, ← inner_testToLp]
  rw [gaugeFixedRightInverse_eq hx]
  exact LinearMap.adjointRightInverse_apply_eq_iff (exists_norm_testToLp_le hx hgap)

/-- The spectral gap at an actual vortex with unit-modulus end, on test fields. -/
private theorem exists_gap_of_equation_eq_zero (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ c > 0, ∀ η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4)),
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ :=
  let ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hlim
  ⟨c, hc, fun η ↦ hgap η (by exact_mod_cast η.contDiff) η.hasCompactSupport⟩

/-- **Cokernel vanishing at a vortex.** At a `C¹` vortex with `|α| → 1`, the operator
`gaugeFixedRightInverse μ x` is a bounded right inverse of the weak `L²` realization of `L_x`:
`u = gaugeFixedRightInverse μ x f` satisfies `∫ ⟪u, L_x* η⟫ = ∫ ⟪f, η⟫` for every test field
`η`. -/
theorem integral_inner_gaugeFixedRightInverse_of_equation_eq_zero (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
    (η : 𝓓^{2}((⊤ : Opens ℂ), EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ⟪gaugeFixedRightInverse μ x f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ :=
  integral_inner_gaugeFixedRightInverse hx.continuous
    (exists_gap_of_equation_eq_zero hx hsol hlim) f η

end TauCeti.Vortex
