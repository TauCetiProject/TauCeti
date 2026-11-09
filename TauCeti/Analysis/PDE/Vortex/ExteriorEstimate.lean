/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral

/-!
# Exterior coercivity of the plane-vortex operator and its adjoint

For an actual plane vortex with `|α| → 1`, the formal adjoint of the gauge-fixed operator has
an exterior `L²` lower bound at every mass strictly below `1/2`. The radius depends on the
vortex and the chosen mass, but not on the compactly supported test field. No decay of the
connection, choice of winding gauge, or derivative decay is assumed.

The proof uses the Weitzenböck formula at a vortex
(`gaugeFixedOperator_gaugeFixedAdjoint_of_equation_eq_zero`). The magnetic first-order terms
complete to covariant-gradient squares, while the two potentials are
`P = |α|²/4` and `1/8 + P/2`. Integrating the squared-norm Bochner identity eliminates the
Laplacian.

The gauge-fixed operator `L_x` itself satisfies the same kind of exterior bound, at every mass
below `1/2`, once the covariant derivative `∇₁ α` also tends to zero at infinity. Its
Weitzenböck formula (`gaugeFixedAdjoint_gaugeFixedOperator_of_equation_eq_zero`) has the
potentials `P` and `3 P / 2 - 1 / 8`, both tending to `1/4`, and a zeroth-order coupling of the
connection and section parts through `∇₁ α`, which has no sign. Integrating the Bochner
identity gives the energy identity
`‖L_x y‖₂² = ‖∇ξ‖₂² + ‖∇_a ζ‖₂² + ∫ P |ξ|² + ∫ (3 P / 2 - 1 / 8) |ζ|² + 2 ∫ ⟪ξ, K ζ⟫`
(`integral_norm_sq_gaugeFixedOperator_of_equation_eq_zero`), which reduces to
`‖L₀ y‖₂² = ‖∇y‖₂² + ‖y‖₂² / 4` at the vacuum. Where `|K| = |∇₁ α|` is small the coupling is
absorbed by the potentials (`exists_exterior_integral_norm_sq_gaugeFixedOperator_ge`).
Together, the exterior bounds for `L_x` and `L_x*` are the estimates at infinity behind the
Fredholm property of `L_x` at a vortex.

These are classical test-field estimates; they do not assert a completed Fredholm
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

/-- At a unit-modulus end, the squared mass eventually exceeds every `a < 1/4`,
with a positive radius independent of any test field. -/
theorem exists_exterior_lt_mass
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {a : ℝ} (ha : a < 1 / 4) :
    ∃ R > 0, ∀ z, R < ‖z‖ → a < x z 2 ^ 2 + x z 3 ^ 2 := by
  have he := hlim.eventually (lt_mem_nhds (by linarith : 4 * a < 1))
  rw [← Metric.cobounded_eq_cocompact] at he
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp he
  refine ⟨max R 1, by positivity, fun z hz ↦ ?_⟩
  have hv : 4 * a < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    hR (le_trans (le_max_left R 1) hz.le)
  linarith

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
  have hmass : c ^ 2 < 1 / 4 := by nlinarith
  obtain ⟨R, hR₀, hR⟩ := exists_exterior_lt_mass hlim hmass
  refine ⟨R, hR₀, fun η hη hηc hzero ↦
    mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint hx hη hηc (fun z _ ↦ hsol z)
      hmass.le ?_⟩
  intro z hz
  exact (hR z (lt_of_not_ge fun h ↦ hz (hzero z h))).le

/-! ### The gauge-fixed operator -/

section Operator

variable {y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The pointwise Bochner identity for `L_x` at a point where `y` vanishes or the vortex equation
holds: `⟪L_x* L_x y, y⟫ + Δ |y|² / 2` is the sum of the squared gradient of the connection part,
the squared covariant gradient of the section part, the two potentials and the coupling through
`∇₁ α`. -/
private theorem inner_gaugeFixedAdjoint_gaugeFixedOperator_add_laplacian {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hy : ContDiffAt ℝ 2 y z) (hsol : y z ≠ 0 → equation x z = 0) :
    ⟪gaugeFixedAdjoint x (gaugeFixedOperator x y) z, y z⟫ + Δ (fun w ↦ ‖y w‖ ^ 2) z / 2 =
      fderiv ℝ (fun w ↦ y w 0) z 1 ^ 2 + fderiv ℝ (fun w ↦ y w 0) z I ^ 2 +
        fderiv ℝ (fun w ↦ y w 1) z 1 ^ 2 + fderiv ℝ (fun w ↦ y w 1) z I ^ 2 +
        (fderiv ℝ (fun w ↦ y w 2) z 1 - x z 0 * y z 3) ^ 2 +
        (fderiv ℝ (fun w ↦ y w 2) z I - x z 1 * y z 3) ^ 2 +
        (fderiv ℝ (fun w ↦ y w 3) z 1 + x z 0 * y z 2) ^ 2 +
        (fderiv ℝ (fun w ↦ y w 3) z I + x z 1 * y z 2) ^ 2 +
        (x z 2 ^ 2 + x z 3 ^ 2) * (y z 0 ^ 2 + y z 1 ^ 2) +
        (3 * (x z 2 ^ 2 + x z 3 ^ 2) / 2 - 1 / 8) * (y z 2 ^ 2 + y z 3 ^ 2) +
        2 * ((covariantDerivative x z 1).im * (y z 0 * y z 2 + y z 1 * y z 3) +
          (covariantDerivative x z 1).re * (y z 1 * y z 2 - y z 0 * y z 3)) := by
  have hdi (i : Fin 4) : fderiv ℝ (fun w ↦ y w i) z =
      (EuclideanSpace.proj i) ∘L fderiv ℝ y z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z
      (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hΔi (i : Fin 4) : Δ (fun w ↦ y w i) z = (Δ y z) i :=
    hy.laplacian_CLM_comp_left (l := EuclideanSpace.proj (𝕜 := ℝ) i)
  rw [hy.laplacian_norm_sq orthonormalBasisOneI]
  by_cases hz : y z = 0
  · rw [hz, inner_zero_right]
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, Fin.isValue, hdi,
      ContinuousLinearMap.comp_apply, PiLp.proj_apply, PiLp.zero_apply, coe_orthonormalBasisOneI,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      inner_zero_left]
    ring
  rw [gaugeFixedAdjoint_gaugeFixedOperator_of_equation_eq_zero hx hy (hsol hz)]
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, Fin.isValue, hΔi, hdi,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    coe_orthonormalBasisOneI, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two,
    Matrix.cons_val_fin_one]
  ring

/-- Integrating the Bochner identity: for a `C¹` field and a compactly supported `C²` variation,
`⟪L_x* L_x y, y⟫ + Δ |y|² / 2` is integrable with integral `‖L_x y‖₂²`. -/
private theorem integral_inner_gaugeFixedAdjoint_gaugeFixedOperator_add_laplacian
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 2 y) (hc : HasCompactSupport y) :
    Integrable (fun z ↦ ⟪gaugeFixedAdjoint x (gaugeFixedOperator x y) z, y z⟫ +
        Δ (fun w ↦ ‖y w‖ ^ 2) z / 2) μ ∧
      ∫ z, (⟪gaugeFixedAdjoint x (gaugeFixedOperator x y) z, y z⟫ +
        Δ (fun w ↦ ‖y w‖ ^ 2) z / 2) ∂μ = ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ := by
  have hL : ContDiff ℝ 1 (gaugeFixedOperator x y) := contDiff_gaugeFixedOperator hx hy
  have hi : Integrable (fun z ↦ ⟪gaugeFixedAdjoint x (gaugeFixedOperator x y) z, y z⟫) μ :=
    ((continuous_gaugeFixedAdjoint hx.continuous hL).inner
      hy.continuous).integrable_of_hasCompactSupport
      (hc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have hnc : HasCompactSupport (fun z ↦ ‖y z‖ ^ 2) :=
    hc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp)
  have hΔ : Integrable (fun z ↦ Δ (fun w ↦ ‖y w‖ ^ 2) z / 2) μ :=
    ((hy.norm_sq ℝ).continuous_laplacian.div_const 2).integrable_of_hasCompactSupport
      (hnc.laplacian.comp_left (g := fun t : ℝ ↦ t / 2) (by simp))
  refine ⟨hi.add hΔ, ?_⟩
  have hsym : ∫ z, ⟪gaugeFixedAdjoint x (gaugeFixedOperator x y) z, y z⟫ ∂μ =
      ∫ z, ⟪y z, gaugeFixedAdjoint x (gaugeFixedOperator x y) z⟫ ∂μ :=
    integral_congr_ae (.of_forall fun z ↦ real_inner_comm _ _)
  rw [integral_add hi hΔ, integral_div,
    integral_laplacian_eq_zero_of_hasCompactSupport (hy.norm_sq ℝ) hnc, zero_div, add_zero, hsym,
    ← integral_inner_gaugeFixedOperator hx.continuous (hy.of_le (by norm_num)) hc hL]
  simp_rw [real_inner_self_eq_norm_sq]

/-- **The energy identity for `L_x` at a vortex.** For a compactly supported `C²` variation
`y = (ξ, ζ)`, with `P = p² + q² = |α|² / 4`,
`‖L_x y‖₂² = ‖∇ξ‖₂² + ‖∇_a ζ‖₂² + ∫ P |ξ|² + ∫ (3 P / 2 - 1 / 8) |ζ|² + 2 ∫ ⟪ξ, K ζ⟫`,
where `K` is multiplication by `i conj (∇₁ α)`, written in real coordinates. At the vacuum it is
the identity `‖L₀ y‖₂² = ‖∇y‖₂² + ‖y‖₂² / 4`. -/
theorem integral_norm_sq_gaugeFixedOperator_of_equation_eq_zero
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 2 y) (hc : HasCompactSupport y)
    (hsol : ∀ z, y z ≠ 0 → equation x z = 0) :
    ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ =
      ∫ z, (fderiv ℝ (fun w ↦ y w 0) z 1 ^ 2 + fderiv ℝ (fun w ↦ y w 0) z I ^ 2 +
        fderiv ℝ (fun w ↦ y w 1) z 1 ^ 2 + fderiv ℝ (fun w ↦ y w 1) z I ^ 2 +
        (fderiv ℝ (fun w ↦ y w 2) z 1 - x z 0 * y z 3) ^ 2 +
        (fderiv ℝ (fun w ↦ y w 2) z I - x z 1 * y z 3) ^ 2 +
        (fderiv ℝ (fun w ↦ y w 3) z 1 + x z 0 * y z 2) ^ 2 +
        (fderiv ℝ (fun w ↦ y w 3) z I + x z 1 * y z 2) ^ 2 +
        (x z 2 ^ 2 + x z 3 ^ 2) * (y z 0 ^ 2 + y z 1 ^ 2) +
        (3 * (x z 2 ^ 2 + x z 3 ^ 2) / 2 - 1 / 8) * (y z 2 ^ 2 + y z 3 ^ 2) +
        2 * ((covariantDerivative x z 1).im * (y z 0 * y z 2 + y z 1 * y z 3) +
          (covariantDerivative x z 1).re * (y z 1 * y z 2 - y z 0 * y z 3))) ∂μ := by
  rw [← (integral_inner_gaugeFixedAdjoint_gaugeFixedOperator_add_laplacian hx hy hc).2]
  exact integral_congr_ae (.of_forall fun z ↦
    inner_gaugeFixedAdjoint_gaugeFixedOperator_add_laplacian (hx.differentiable one_ne_zero z)
      hy.contDiffAt (hsol z))

private theorem mul_norm_sq_le_inner_gaugeFixedAdjoint_gaugeFixedOperator_add_laplacian {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hy : ContDiffAt ℝ 2 y z) (hsol : y z ≠ 0 → equation x z = 0)
    {a δ : ℝ} (hδ : 0 < δ) (ha : a + δ ≤ 1 / 4)
    (hP : a + δ ≤ 3 * (x z 2 ^ 2 + x z 3 ^ 2) / 2 - 1 / 8)
    (hcov : ‖covariantDerivative x z 1‖ ≤ δ) :
    a * ‖y z‖ ^ 2 ≤
      ⟪gaugeFixedAdjoint x (gaugeFixedOperator x y) z, y z⟫ + Δ (fun w ↦ ‖y w‖ ^ 2) z / 2 := by
  rw [inner_gaugeFixedAdjoint_gaugeFixedOperator_add_laplacian hx hy hsol,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  have hcd : (covariantDerivative x z 1).im ^ 2 + (covariantDerivative x z 1).re ^ 2 ≤ δ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hcov 2
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    linarith
  -- The coupling `2 ⟪ξ, K ζ⟫`, with `|K| = |∇₁ α| ≤ δ`, is at least `-δ (|ξ|² + |ζ|²)`.
  set c := (covariantDerivative x z 1).im
  set d := (covariantDerivative x z 1).re
  have hcpl : -(δ * (y z 0 ^ 2 + y z 1 ^ 2 + y z 2 ^ 2 + y z 3 ^ 2)) ≤
      2 * (c * (y z 0 * y z 2 + y z 1 * y z 3) + d * (y z 1 * y z 2 - y z 0 * y z 3)) := by
    refine le_of_mul_le_mul_left ?_ hδ
    nlinarith [sq_nonneg (δ * y z 0 + (c * y z 2 - d * y z 3)),
      sq_nonneg (δ * y z 1 + (d * y z 2 + c * y z 3)),
      mul_le_mul_of_nonneg_right hcd (add_nonneg (sq_nonneg (y z 2)) (sq_nonneg (y z 3)))]
  have hP' : a + δ ≤ x z 2 ^ 2 + x z 3 ^ 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hP' (add_nonneg (sq_nonneg (y z 0)) (sq_nonneg (y z 1))),
    mul_le_mul_of_nonneg_right hP (add_nonneg (sq_nonneg (y z 2)) (sq_nonneg (y z 3))),
    sq_nonneg (fderiv ℝ (fun w ↦ y w 0) z 1), sq_nonneg (fderiv ℝ (fun w ↦ y w 0) z I),
    sq_nonneg (fderiv ℝ (fun w ↦ y w 1) z 1), sq_nonneg (fderiv ℝ (fun w ↦ y w 1) z I),
    sq_nonneg (fderiv ℝ (fun w ↦ y w 2) z 1 - x z 0 * y z 3),
    sq_nonneg (fderiv ℝ (fun w ↦ y w 2) z I - x z 1 * y z 3),
    sq_nonneg (fderiv ℝ (fun w ↦ y w 3) z 1 + x z 0 * y z 2),
    sq_nonneg (fderiv ℝ (fun w ↦ y w 3) z I + x z 1 * y z 2)]

/-- The gauge-fixed vortex operator has squared `L²` lower bound `a` on any compactly supported `C²`
variation supported where the vortex equation holds, the section potential satisfies
`3 |α|² / 8 - 1 / 8 ≥ a + δ` and `|∇₁ α| ≤ δ`, for some `δ > 0` with `a + δ ≤ 1 / 4`. This is
a support-local estimate, not a global spectral gap for all vortices. -/
theorem mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 2 y) (hc : HasCompactSupport y)
    (hsol : ∀ z, y z ≠ 0 → equation x z = 0) {a δ : ℝ} (hδ : 0 < δ) (ha : a + δ ≤ 1 / 4)
    (hP : ∀ z, y z ≠ 0 → a + δ ≤ 3 * (x z 2 ^ 2 + x z 3 ^ 2) / 2 - 1 / 8)
    (hcov : ∀ z, y z ≠ 0 → ‖covariantDerivative x z 1‖ ≤ δ) :
    a * (∫ z, ‖y z‖ ^ 2 ∂μ) ≤ ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ := by
  have hint := integral_inner_gaugeFixedAdjoint_gaugeFixedOperator_add_laplacian (μ := μ) hx hy hc
  have hn : Integrable (fun z ↦ a * ‖y z‖ ^ 2) μ :=
    ((hy.continuous.norm.pow 2).const_mul a).integrable_of_hasCompactSupport
      (hc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp)).mul_left
  rw [← hint.2, ← integral_const_mul]
  refine integral_mono hn hint.1 fun z ↦ ?_
  by_cases hz : y z = 0
  · rw [hy.contDiffAt.laplacian_norm_sq orthonormalBasisOneI]
    have hs : 0 ≤ (2 * ∑ i : Fin 2, ‖fderiv ℝ y z (orthonormalBasisOneI i)‖ ^ 2) / 2 :=
      by positivity
    simpa [hz] using hs
  · exact mul_norm_sq_le_inner_gaugeFixedAdjoint_gaugeFixedOperator_add_laplacian
      (hx.differentiable one_ne_zero z) hy.contDiffAt (fun _ ↦ hsol z hz) hδ ha (hP z hz)
      (hcov z hz)

/-- **Exterior coercivity of the gauge-fixed vortex operator.** For an actual vortex with
`|α| → 1` and `∇₁ α → 0` at infinity, and `0 < c < 1/2`, there is a radius `R > 0`, depending
only on the vortex and `c`, such that `c² ∫|y|² ≤ ∫|L_x y|²` for every compactly supported `C²`
variation `y` vanishing on the closed disc of radius `R` about the origin. -/
theorem exists_exterior_integral_norm_sq_gaugeFixedOperator_ge
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    {c : ℝ} (hc : 0 < c) (hc' : c < 1 / 2) :
    ∃ R > 0, ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 y →
      HasCompactSupport y → (∀ z, ‖z‖ ≤ R → y z = 0) →
      c ^ 2 * (∫ z, ‖y z‖ ^ 2 ∂μ) ≤ ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ := by
  set δ : ℝ := (1 / 4 - c ^ 2) / 2 with hδdef
  have hc2 : c ^ 2 < 1 / 4 := by nlinarith
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hpot : Tendsto (fun z ↦ 3 * (x z 2 ^ 2 + x z 3 ^ 2) / 2 - 1 / 8) (cocompact ℂ)
      (𝓝 (1 / 4)) := by
    have := (hlim.const_mul (3 / 8)).sub_const (1 / 8)
    norm_num at this
    refine this.congr fun z ↦ ?_
    ring
  have he : ∀ᶠ z in cocompact ℂ, c ^ 2 + δ < 3 * (x z 2 ^ 2 + x z 3 ^ 2) / 2 - 1 / 8 ∧
      ‖covariantDerivative x z 1‖ < δ :=
    (hpot.eventually (lt_mem_nhds (by rw [hδdef]; linarith))).and
      (hcov.norm.eventually (gt_mem_nhds (by simpa using hδ)))
  rw [← Metric.cobounded_eq_cocompact] at he
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp he
  refine ⟨max R 1, by positivity, fun y hy hyc hzero ↦
    mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedOperator hx hy hyc (fun z _ ↦ hsol z) hδ
      (by rw [hδdef]; linarith) (fun z hz ↦ ?_) (fun z hz ↦ ?_)⟩
  · have hzR : max R 1 < ‖z‖ := lt_of_not_ge fun h ↦ hz (hzero z h)
    exact (hR (le_trans (le_max_left R 1) hzR.le)).1.le
  · have hzR : max R 1 < ‖z‖ := lt_of_not_ge fun h ↦ hz (hzero z h)
    exact (hR (le_trans (le_max_left R 1) hzR.le)).2.le

end Operator

end TauCeti.Vortex
