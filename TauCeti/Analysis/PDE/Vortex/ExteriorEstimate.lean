/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral

/-!
# Exterior coercivity of the plane-vortex adjoint

For an actual plane vortex with `|α| → 1`, the formal adjoint of the gauge-fixed operator has
an exterior `L²` lower bound at every mass strictly below `1/2`. The radius depends on the
vortex and the chosen mass, but not on the compactly supported test field. No decay of the
connection, choice of winding gauge, or derivative decay is assumed.

The proof uses the Weitzenböck formula at a vortex
(`gaugeFixedOperator_gaugeFixedAdjoint_of_equation_eq_zero`). The magnetic first-order terms
complete to covariant-gradient squares, while the two potentials are
`P = |α|²/4` and `1/8 + P/2`. Integrating the squared-norm Bochner identity eliminates the
Laplacian. These are classical test-field estimates; they do not assert a completed Fredholm
realization or a uniform inverse over the noncompact vortex moduli space.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Chapter III.
-/

public section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter
open scoped Laplacian Topology RealInnerProductSpace

variable {x η : ℂ → EuclideanSpace ℝ (Fin 4)}

private theorem mass_mul_norm_sq_le_inner_add_laplacian {z : ℂ} {a : ℝ}
    (hx : DifferentiableAt ℝ x z) (hη : ContDiffAt ℝ 2 η z)
    (hsol : equation x z = 0) (ha : a ≤ 1 / 4)
    (hP : a ≤ x z 2 ^ 2 + x z 3 ^ 2) :
    a * ‖η z‖ ^ 2 ≤
      ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ +
        Δ (fun w ↦ ‖η w‖ ^ 2) z / 2 := by
  have hdi (i : Fin 4) : fderiv ℝ (fun w ↦ η w i) z =
      (EuclideanSpace.proj i) ∘L fderiv ℝ η z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z
      (hη.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hΔi (i : Fin 4) : Δ (fun w ↦ η w i) z = (Δ η z) i :=
    hη.laplacian_CLM_comp_left (l := EuclideanSpace.proj (𝕜 := ℝ) i)
  rw [gaugeFixedOperator_gaugeFixedAdjoint_of_equation_eq_zero hx hη hsol,
    hη.laplacian_norm_sq orthonormalBasisOneI]
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, Fin.isValue, hΔi, one_div, hdi,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    coe_orthonormalBasisOneI, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two,
    Matrix.cons_val_fin_one, ge_iff_le]
  -- Complete the section derivatives to covariant-gradient squares. The remaining
  -- zeroth-order terms have coefficients P - a and 1/8 + P/2 - a, both nonnegative.
  have hp : 0 ≤ x z 2 ^ 2 + x z 3 ^ 2 - a := by linarith
  have hq : 0 ≤ 1 / 8 + (x z 2 ^ 2 + x z 3 ^ 2) / 2 - a := by linarith
  nlinarith only [
    sq_nonneg (fderiv ℝ η z 1 0), sq_nonneg (fderiv ℝ η z I 0),
    sq_nonneg (fderiv ℝ η z 1 1), sq_nonneg (fderiv ℝ η z I 1),
    sq_nonneg (fderiv ℝ η z 1 2 - x z 0 * η z 3),
    sq_nonneg (fderiv ℝ η z I 2 - x z 1 * η z 3),
    sq_nonneg (fderiv ℝ η z 1 3 + x z 0 * η z 2),
    sq_nonneg (fderiv ℝ η z I 3 + x z 1 * η z 2),
    mul_nonneg hp (sq_nonneg (η z 0)), mul_nonneg hp (sq_nonneg (η z 1)),
    mul_nonneg hq (sq_nonneg (η z 2)), mul_nonneg hq (sq_nonneg (η z 3))]

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure]

/-- The vortex adjoint has squared `L²` lower bound `a ≤ 1/4` on any compactly supported
`C²` test field supported where the vortex equation holds and `|α|²/4 ≥ a`.
This is a support-local estimate, not a global spectral gap for all vortices. -/
theorem mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η)
    (hsol : ∀ z, η z ≠ 0 → equation x z = 0) {a : ℝ} (ha : a ≤ 1 / 4)
    (hP : ∀ z, η z ≠ 0 → a ≤ x z 2 ^ 2 + x z 3 ^ 2) :
    a * (∫ z, ‖η z‖ ^ 2 ∂μ) ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := by
  have hη₁ : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hA := contDiff_gaugeFixedAdjoint hx hη
  have hAc := hasCompactSupport_gaugeFixedAdjoint (x := x) hc
  have hLc := continuous_gaugeFixedOperator hx.continuous hA
  have hi : Integrable (fun z ↦ ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫) μ :=
    (hLc.inner hη.continuous).integrable_of_hasCompactSupport
      (hc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have hnc : HasCompactSupport (fun z ↦ ‖η z‖ ^ 2) :=
    hc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp)
  have hΔ : Integrable (fun z ↦ Δ (fun w ↦ ‖η w‖ ^ 2) z / 2) μ :=
    ((hη.norm_sq ℝ).continuous_laplacian.div_const 2).integrable_of_hasCompactSupport
      (hnc.laplacian.comp_left (g := fun t : ℝ ↦ t / 2) (by simp))
  have hn : Integrable (fun z ↦ a * ‖η z‖ ^ 2) μ :=
    ((hη.continuous.norm.pow 2).const_mul a).integrable_of_hasCompactSupport
      hnc.mul_left
  have hbound (z : ℂ) : a * ‖η z‖ ^ 2 ≤
      ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ +
        Δ (fun w ↦ ‖η w‖ ^ 2) z / 2 := by
    by_cases hz : η z = 0
    · rw [hη.contDiffAt.laplacian_norm_sq orthonormalBasisOneI]
      have hs : 0 ≤ (2 * ∑ i : Fin 2, ‖fderiv ℝ η z (orthonormalBasisOneI i)‖ ^ 2) / 2 :=
        by positivity
      simpa [hz] using hs
    · exact mass_mul_norm_sq_le_inner_add_laplacian
        (hx.differentiable one_ne_zero z) hη.contDiffAt (hsol z hz) ha (hP z hz)
  have hb := integral_mono hn (hi.add hΔ) hbound
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add hi hΔ, integral_div,
    integral_laplacian_eq_zero_of_hasCompactSupport (hη.norm_sq ℝ) hnc,
    zero_div, add_zero, integral_inner_gaugeFixedOperator hx.continuous hA hAc hη₁] at hb
  simpa only [real_inner_self_eq_norm_sq] using hb

/-- For an actual vortex with unit-modulus end and `0 < c < 1/2`, there is a radius `R > 0`,
depending only on the vortex and `c`, such that `c² ∫|η|² ≤ ∫|L_x* η|²` for every compactly
supported `C²` field `η` vanishing on the closed disc of radius `R` about the origin. -/
theorem exists_exterior_integral_norm_sq_gaugeFixedAdjoint_ge
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : 0 < c) (hc' : c < 1 / 2) :
    ∃ R > 0, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η →
      HasCompactSupport η → (∀ z, ‖z‖ ≤ R → η z = 0) →
      c ^ 2 * (∫ z, ‖η z‖ ^ 2 ∂μ) ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := by
  have hmass : 4 * c ^ 2 < 1 := by nlinarith
  have he := hlim.eventually (lt_mem_nhds hmass)
  rw [← Metric.cobounded_eq_cocompact] at he
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp he
  refine ⟨max R 1, by positivity, fun η hη hηc hzero ↦
    mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint hx hη hηc (fun z _ ↦ hsol z)
      (by nlinarith) ?_⟩
  intro z hz
  have hnorm : max R 1 < ‖z‖ := lt_of_not_ge fun h ↦ hz (hzero z h)
  have hval : 4 * c ^ 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    hR (le_trans (le_max_left R 1) hnorm.le)
  linarith

end TauCeti.Vortex
