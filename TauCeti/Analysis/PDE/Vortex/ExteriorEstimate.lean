/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Garding
public import TauCeti.Analysis.PDE.Vortex.UniformDerivativeDecay
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
Laplacian. At a continuous field with `|α| → 1`, the squared mass `P` and the section coordinates
are bounded (`exists_forall_sq_add_sq_le`, `memLp_top_sq_add_sq`,
`memLp_top_apply_of_eq_two_or_eq_three`), and `P` exceeds every `a < 1/4` outside a disc
(`exists_exterior_lt_mass`); together these are the hypotheses of the stationary Schrödinger
theory for `-Δ + P` (`exists_memLp_top_sq_add_sq_and_le`).

The gauge-fixed operator `L_x` itself satisfies the same kind of exterior bound, at every mass
below `1/2`, once the covariant derivative `∇₁ α` also tends to zero at infinity. At a vortex the
potential of its Weitzenböck formula (`integral_norm_sq_gaugeFixedOperator`) is
`P |ξ|² + (3 P / 2 - 1 / 8) |ζ|²`, with both coefficients tending to `1/4`, plus a zeroth-order
coupling of the connection and section parts through `∇₁ α`, which has no sign. This gives the
energy identity
`‖L_x y‖₂² = ‖∇ξ‖₂² + ‖∇_a ζ‖₂² + ∫ P |ξ|² + ∫ (3 P / 2 - 1 / 8) |ζ|² + 2 ∫ ⟪ξ, K ζ⟫`
(`integral_norm_sq_gaugeFixedOperator_of_equation_eq_zero`), which reduces to
`‖L₀ y‖₂² = ‖∇y‖₂² + ‖y‖₂² / 4` at the vacuum. Where `|K| = |∇₁ α|` is small the coupling is
absorbed by the potentials; the exterior bound
(`exists_exterior_integral_norm_sq_gaugeFixedOperator_ge`) is the Gårding inequality
`exists_integral_gaugeFixedGradientDensity_add_mul_integral_norm_sq_le` for variations vanishing
on its disc.

The radius of that bound depends on the vortex only through how fast `|α|² → 1` and `∇₁ α → 0`
at infinity. Both rates are uniform over the smooth framed vortices of degree `m` whose zeros lie in
a fixed disc (`exists_forall_lt_normSq_of_forall_mem_norm_le`,
`exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub`), so the lower bound
`vortexMass` of the potential exceeds any `a < 1/4` outside a common radius
(`exists_forall_lt_vortexMass_of_forall_mem_norm_le`). Since the potential is at least
`vortexMass` times `|y|²`
(`mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedOperator_of_le_vortexMass`), the exterior
bound for `L_x` holds with one radius for all these vortices, collisions of zeros included
(`exists_forall_exterior_integral_norm_sq_gaugeFixedOperator_ge_of_forall_mem_norm_le`). Every
compact window of divisors lies in such a disc.

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
open scoped Laplacian Topology RealInnerProductSpace ContDiff

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

/-- At a continuous field, the squared mass `P = |α|² / 4 = x₂² + x₃²` is continuous. -/
theorem continuous_sq_add_sq (hx : Continuous x) :
    Continuous fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 := by
  have _ : Continuous fun z ↦ x z 2 := by fun_prop
  have _ : Continuous fun z ↦ x z 3 := by fun_prop
  fun_prop

/-- At a continuous field with a unit-modulus end, the squared mass `P = |α|² / 4 = x₂² + x₃²` is
bounded above. -/
theorem exists_forall_sq_add_sq_le (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ M, ∀ z, x z 2 ^ 2 + x z 3 ^ 2 ≤ M := by
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.1 (hlim.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_sq_add_sq hx).continuousOn
  refine ⟨max M 1, fun z ↦ ?_⟩
  by_cases hz : z ∈ K
  · exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM z hz).trans (le_max_left _ _))
  · have h2 : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 2 := hKc hz
    linarith [le_max_right M 1]

/-- At a continuous field with a unit-modulus end, the squared mass `P = |α|² / 4 = x₂² + x₃²` is
essentially bounded. -/
theorem memLp_top_sq_add_sq (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    MemLp (fun z ↦ x z 2 ^ 2 + x z 3 ^ 2) ⊤ (volume : Measure ℂ) := by
  obtain ⟨M, hM⟩ := exists_forall_sq_add_sq_le hx hlim
  refine memLp_top_of_bound (continuous_sq_add_sq hx).aestronglyMeasurable M
    (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact hM z

/-- The section coordinates of a continuous field whose section has unit modulus at infinity are
bounded. -/
theorem memLp_top_apply_of_eq_two_or_eq_three (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {i : Fin 4}
    (hi : i = 2 ∨ i = 3) : MemLp (fun z ↦ x z i) ⊤ volume := by
  obtain ⟨M, hM⟩ := exists_forall_sq_add_sq_le hx hlim
  have hxi : Continuous fun z ↦ x z i := by fun_prop
  refine memLp_top_of_bound hxi.aestronglyMeasurable (M + 1) (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_eq_abs]
  have hz := hM z
  rcases hi with rfl | rfl
  · nlinarith [sq_nonneg (|x z 2| - 1), sq_abs (x z 2), sq_nonneg (x z 3), abs_nonneg (x z 2)]
  · nlinarith [sq_nonneg (|x z 3| - 1), sq_abs (x z 3), sq_nonneg (x z 2), abs_nonneg (x z 3)]

/-- At a continuous field with a unit-modulus end, the squared mass `P = |α|² / 4 = x₂² + x₃²`
satisfies the hypotheses of the stationary Schrödinger theory for `-Δ + P`: it is essentially
bounded, nonnegative, and at least `1 / 8` outside some disc. -/
theorem exists_memLp_top_sq_add_sq_and_le (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ R : ℝ, MemLp (fun z ↦ x z 2 ^ 2 + x z 3 ^ 2) ⊤ (volume : Measure ℂ) ∧
      (∀ᵐ z ∂volume, 0 ≤ x z 2 ^ 2 + x z 3 ^ 2) ∧
      ∀ᵐ z ∂(volume : Measure ℂ), R < ‖z‖ → 1 / 8 ≤ x z 2 ^ 2 + x z 3 ^ 2 := by
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  exact ⟨R, memLp_top_sq_add_sq hx hlim, ae_of_all _ fun z ↦ by positivity,
    ae_of_all _ fun z hz ↦ (hR z hz).le⟩

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
    zero_div, add_zero, integral_inner_gaugeFixedOperator hA hη₁ (.inl hAc)] at hb
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

/-- **The energy identity for `L_x` at a vortex.** For a compactly supported `C²` variation
`y = (ξ, ζ)` supported where the vortex equation holds, with `P = p² + q² = |α|² / 4`,
`‖L_x y‖₂² = ‖∇ξ‖₂² + ‖∇_a ζ‖₂² + ∫ P |ξ|² + ∫ (3 P / 2 - 1 / 8) |ζ|² + 2 ∫ ⟪ξ, K ζ⟫`,
where `K` is multiplication by `i conj (∇₁ α)`, written in real coordinates. It is the
Weitzenböck formula `integral_norm_sq_gaugeFixedOperator` with the potential simplified by
`gaugeFixedPotential_eq_of_equation_eq_zero`. At the vacuum it is the identity
`‖L₀ y‖₂² = ‖∇y‖₂² + ‖y‖₂² / 4`. -/
theorem integral_norm_sq_gaugeFixedOperator_of_equation_eq_zero
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 2 y) (hc : HasCompactSupport y)
    (hsol : ∀ z, y z ≠ 0 → equation x z = 0) :
    ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ =
      (∫ z, gaugeFixedGradientDensity x y z ∂μ) +
        ∫ z, ((x z 2 ^ 2 + x z 3 ^ 2) * (y z 0 ^ 2 + y z 1 ^ 2) +
          (3 * (x z 2 ^ 2 + x z 3 ^ 2) / 2 - 1 / 8) * (y z 2 ^ 2 + y z 3 ^ 2) +
          2 * ((covariantDerivative x z 1).im * (y z 0 * y z 2 + y z 1 * y z 3) +
            (covariantDerivative x z 1).re * (y z 1 * y z 2 - y z 0 * y z 3))) ∂μ := by
  rw [integral_norm_sq_gaugeFixedOperator hx hy hc]
  congr 1
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  by_cases hz : y z = 0
  · simp [gaugeFixedPotential_def, hz]
  · exact gaugeFixedPotential_eq_of_equation_eq_zero (hx.differentiable one_ne_zero z)
      (hsol z hz) (y z)

/-- **Exterior coercivity of the gauge-fixed vortex operator.** For an actual vortex with
`|α| → 1` and `∇₁ α → 0` at infinity, and `0 < c < 1/2`, there is a radius `R > 0`, depending
only on the vortex and `c`, such that `c² ∫|y|² ≤ ∫|L_x y|²` for every compactly supported `C²`
variation `y` vanishing on the closed disc of radius `R` about the origin. This is the Gårding
inequality `exists_integral_gaugeFixedGradientDensity_add_mul_integral_norm_sq_le` at mass `c²`,
whose compact remainder vanishes for such variations. -/
theorem exists_exterior_integral_norm_sq_gaugeFixedOperator_ge
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    {c : ℝ} (hc : 0 < c) (hc' : c < 1 / 2) :
    ∃ R > 0, ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 y →
      HasCompactSupport y → (∀ z, ‖z‖ ≤ R → y z = 0) →
      c ^ 2 * (∫ z, ‖y z‖ ^ 2 ∂μ) ≤ ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ := by
  have hc2 : c ^ 2 < 1 / 4 := by nlinarith
  obtain ⟨R, hR, K, hK⟩ :=
    exists_integral_gaugeFixedGradientDensity_add_mul_integral_norm_sq_le (μ := μ) hx hsol hlim
      hcov hc2
  refine ⟨R, hR, fun y hy hyc hzero ↦ ?_⟩
  have hB : ∫ z in Metric.closedBall 0 R, ‖y z‖ ^ 2 ∂μ = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ by
      simp [hzero z (by simpa using Metric.mem_closedBall.mp hz)]
  have hG : 0 ≤ ∫ z, gaugeFixedGradientDensity x y z ∂μ :=
    integral_nonneg (gaugeFixedGradientDensity_nonneg x y)
  have h := hK y hy hyc
  rw [hB, mul_zero, add_zero] at h
  linarith

/-- **Coercivity from a lower bound on the vortex mass.** Let `x` be a `C¹` field and `y` a
compactly supported `C²` variation such that, wherever `y z ≠ 0`, the vortex equation holds at `z`
and `a ≤ vortexMass x z`. Then `a ∫ |y|² ≤ ∫ |L_x y|²`. -/
theorem mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedOperator_of_le_vortexMass
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 2 y) (hyc : HasCompactSupport y)
    (hsol : ∀ z, y z ≠ 0 → equation x z = 0) {a : ℝ}
    (ha : ∀ z, y z ≠ 0 → a ≤ vortexMass x z) :
    a * ∫ z, ‖y z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ := by
  have hn : Integrable (fun z ↦ ‖y z‖ ^ 2) μ :=
    Continuous.integrable_of_hasCompactSupport (f := fun z ↦ ‖y z‖ ^ 2)
      (hy.continuous.norm.pow 2) (hyc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp))
  -- Pointwise the potential is at least `a |y|²`, by the lower bound `vortexMass |y|²`.
  have hpt (z : ℂ) : a * ‖y z‖ ^ 2 ≤ gaugeFixedPotential x z (y z) := by
    by_cases hz : y z = 0
    · simp [gaugeFixedPotential_def, hz]
    · exact (mul_le_mul_of_nonneg_right (ha z hz) (sq_nonneg _)).trans
        (vortexMass_mul_norm_sq_le_gaugeFixedPotential (hx.differentiable one_ne_zero z)
          (hsol z hz) (y z))
  have hlow := integral_mono (hn.const_mul a)
    (integrable_gaugeFixedPotential hx hy.continuous hyc) hpt
  rw [integral_const_mul] at hlow
  have hG : 0 ≤ ∫ z, gaugeFixedGradientDensity x y z ∂μ :=
    integral_nonneg (gaugeFixedGradientDensity_nonneg x y)
  rw [integral_norm_sq_gaugeFixedOperator hx hy hyc]
  linarith

/-- **A common lower bound on the vortex mass over a window of divisors.** For every degree `m`,
radius `R₀` and `a < 1 / 4` there is a radius `R` such that every smooth plane vortex with the
degree-`m` end framing whose zeros lie in the closed disc of radius `R₀` satisfies
`a < vortexMass x z` for every `z` with `‖z‖ > R`. -/
theorem exists_forall_lt_vortexMass_of_forall_mem_norm_le (m : ℕ) (R₀ : ℝ) {a : ℝ}
    (ha : a < 1 / 4) :
    ∃ R, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ z, R < ‖z‖ → a < vortexMass x z := by
  obtain ⟨δ, hδ, rfl⟩ : ∃ δ, 0 < δ ∧ a = 1 / 4 - 2 * δ := ⟨(1 / 4 - a) / 2, by linarith, by ring⟩
  -- Far out, `|α|² > 1 - 2 δ`, so both entries of the minimum in `vortexMass` exceed `1/4 - δ`.
  obtain ⟨R₁, hR₁⟩ := exists_forall_lt_normSq_of_forall_mem_norm_le m R₀ (θ := 1 - 2 * δ)
    (by linarith)
  -- At distance `ρ₀` from every zero, `|∇₁ α| ≤ K exp (-ρ₀ / 4) ≤ δ`.
  obtain ⟨K, R₂, hK, hcov⟩ := exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub m
    (c := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨ρ₀, hρ₀R, hρ₀⟩ : ∃ ρ₀, R₂ ≤ ρ₀ ∧ 4 * Real.log ((K + 1) / δ) ≤ ρ₀ :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hexp : K * Real.exp (-(1 / 4 * ρ₀)) ≤ δ := by
    have h₁ : Real.exp (-(1 / 4 * ρ₀)) ≤ ((K + 1) / δ)⁻¹ := by
      rw [← Real.exp_log (show 0 < (K + 1) / δ by positivity), ← Real.exp_neg]
      exact Real.exp_le_exp.2 (by linarith)
    calc K * Real.exp (-(1 / 4 * ρ₀)) ≤ K * ((K + 1) / δ)⁻¹ := mul_le_mul_of_nonneg_left h₁ hK
      _ = δ * (K / (K + 1)) := by rw [inv_div]; ring
      _ ≤ δ * 1 := by gcongr; exact (div_le_one (by positivity)).2 (by linarith)
      _ = δ := mul_one δ
  refine ⟨max R₁ (R₀ + ρ₀), fun x D hx hsol hframe hD hD₀ z hz ↦ ?_⟩
  have hzR := (le_max_right R₁ (R₀ + ρ₀)).trans_lt hz
  have hs := hR₁ x D hx hsol hframe hD hD₀ z ((le_max_left _ _).trans_lt hz)
  have hc := hcov x D hx hsol hframe hD z ρ₀ hρ₀R (fun b hb ↦ by
    linarith [norm_sub_norm_le z b, hD₀ b hb]) 1
  rw [norm_one, mul_one] at hc
  have hmin : 1 / 4 - δ <
      min (x z 2 ^ 2 + x z 3 ^ 2) ((12 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8) :=
    lt_min (by linarith) (by linarith)
  rw [vortexMass_def]
  linarith

/-- **Exterior coercivity of the gauge-fixed vortex operator, uniformly over a window of
divisors.** For every degree `m`, radius `R₀` and `|c| < 1/2` there is a radius `R > 0` with
the following property. For every smooth plane vortex `x` with the degree-`m` end framing whose
zeros lie in the closed disc of radius `R₀`, every compactly supported `C²` variation `y`
vanishing on the closed disc of radius `R` satisfies `c² ∫ |y|² ≤ ∫ |L_x y|²`. The radius depends
only on `m`, `R₀` and `c`; this is the uniform version of
`exists_exterior_integral_norm_sq_gaugeFixedOperator_ge`. -/
theorem exists_forall_exterior_integral_norm_sq_gaugeFixedOperator_ge_of_forall_mem_norm_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ R > 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 y → HasCompactSupport y →
        (∀ z, ‖z‖ ≤ R → y z = 0) →
        c ^ 2 * (∫ z, ‖y z‖ ^ 2 ∂μ) ≤ ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ := by
  obtain ⟨R, hR⟩ := exists_forall_lt_vortexMass_of_forall_mem_norm_le m R₀ (a := c ^ 2)
    (by nlinarith [sq_abs c, abs_nonneg c])
  refine ⟨max R 1, lt_max_of_lt_right one_pos, fun x D hx hsol hframe hD hD₀ y hy hyc hzero ↦
    mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedOperator_of_le_vortexMass
      (hx.of_le (by simp)) hy hyc (fun z _ ↦ hsol z)
      fun z hz ↦ (hR x D hx hsol hframe hD hD₀ z ?_).le⟩
  exact (le_max_left R 1).trans_lt (lt_of_not_ge fun h ↦ hz (hzero z h))

end Operator

end TauCeti.Vortex
