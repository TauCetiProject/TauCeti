/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic
import TauCeti.Probability.Distributions.Cauchy.ApproximateIdentity
import TauCeti.Topology.Instances.NNReal

/-!
# The boundary measure as a vague limit

Let `u = c Im + P[ν]` on the upper half-plane `ℂ₊`, with `c ∈ ℝ` and `ν` a Poisson-finite measure
on `ℝ`, where `P[ν]` is the Poisson integral `TauCeti.upperHalfPlanePoissonIntegral`. Then `ν` is
the vague limit of the measures `u(x + iy) dx` as `y → 0⁺`: for every continuous compactly
supported `φ : ℝ → ℝ`,

`∫ φ(x) u(x + iy) dx → ∫ φ dν`

(`TauCeti.tendsto_integral_mul_of_eq_mul_im_add_upperHalfPlanePoissonIntegral`).

The proof follows the route of Garnett, Chapter I, §3. By Fubini,
`∫ φ(x) P[ν](x + iy) dx = ∫ g_y dν` with `g_y(t) = ∫ P(x + iy, t) φ(x) dx`, which is the Poisson
integral of `φ` at `t + iy` (`TauCeti.integral_mul_upperHalfPlanePoissonIntegral_add_mul_I`).
The Poisson kernel at height `y` is the Cauchy density of scale `y`, an approximate identity, so
`g_y(t) → φ(t)` (`TauCeti.tendsto_integral_upperHalfPlanePoissonKernel_add_mul_I_mul`). For
`y ≤ 1`, `(1 + t ^ 2) P(x + iy, t) ≤ 2 (1 + x ^ 2) (P(x + iy, t) + 1 / π)`, so
`|g_y(t)| ≤ C_φ / (1 + t ^ 2)`
(`TauCeti.abs_integral_upperHalfPlanePoissonKernel_add_mul_I_mul_le`), which is
`ν`-integrable, and dominated convergence gives the limit. The term `c y ∫ φ` tends to `0`.

Fubini applies because a Poisson-finite measure is finite on compact sets
(`TauCeti.IsPoissonFinite.isFiniteMeasureOnCompacts`), hence σ-finite.

## Main results

* `TauCeti.tendsto_integral_mul_upperHalfPlanePoissonIntegral_add_mul_I`:
  `∫ φ(x) P[ν](x + iy) dx → ∫ φ dν` as `y → 0⁺`.
* `TauCeti.tendsto_integral_mul_of_eq_mul_im_add_upperHalfPlanePoissonIntegral`: the same limit
  for `u = c Im + P[ν]`.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §3.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Set Topology
open UpperHalfPlane (upperHalfPlaneSet)
open scoped Real NNReal ENNReal

namespace TauCeti

/-! ### The Poisson kernel at height `y` -/

/-- For `0 < y ≤ 1`, `(1 + t ^ 2) P(x + iy, t) ≤ 2 (1 + x ^ 2) (P(x + iy, t) + 1 / π)`. This
is the pointwise bound behind the decay `C_φ / (1 + t ^ 2)` of the Poisson integrals of a
compactly supported test function. -/
theorem one_add_sq_mul_upperHalfPlanePoissonKernel_add_mul_I_le {y : ℝ} (hy₀ : 0 < y)
    (hy₁ : y ≤ 1) (x t : ℝ) :
    (1 + t ^ 2) * upperHalfPlanePoissonKernel (x + y * I) t ≤
      2 * (1 + x ^ 2) * (upperHalfPlanePoissonKernel (x + y * I) t + π⁻¹) := by
  rw [upperHalfPlanePoissonKernel_add_mul_I_eq]
  set d := t - x
  have ht : t = x + d := by ring
  have h1 : 1 + t ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + d ^ 2) := by
    rw [ht]; nlinarith [sq_nonneg (x - d), sq_nonneg (x * d)]
  have h2 : y * (1 + d ^ 2) ≤ y + (d ^ 2 + y ^ 2) := by nlinarith [sq_nonneg d, sq_nonneg y]
  have key : 2 * (1 + x ^ 2) * (y / (π * (d ^ 2 + y ^ 2)) + π⁻¹) =
      2 * (1 + x ^ 2) * (y + (d ^ 2 + y ^ 2)) / (π * (d ^ 2 + y ^ 2)) := by
    field_simp
  rw [key, mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * (1 + x ^ 2)),
    mul_le_mul_of_nonneg_left h1 hy₀.le]

/-! ### Poisson integrals of a test function -/

section TestFunction

variable {φ : ℝ → ℝ}

/-- **The Poisson integrals of a bounded uniformly continuous function converge to it.** For `φ`
bounded and uniformly continuous, for instance continuous with compact support,
`∫ P(x + iy, t) φ(x) dx → φ(t)` as `y → 0⁺`: the Poisson kernel at height `y` is the Cauchy
density of scale `y`, an approximate identity. -/
theorem tendsto_integral_upperHalfPlanePoissonKernel_add_mul_I_mul (hφ : UniformContinuous φ)
    {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (t : ℝ) :
    Tendsto (fun y : ℝ ↦ ∫ x : ℝ, upperHalfPlanePoissonKernel (x + y * I) t * φ x) (𝓝[>] 0)
      (𝓝 (φ t)) := by
  have hU := Probability.tendstoUniformly_integral_mul_cauchyPDFReal_smul hφ hM
    continuous_const (H := 1) (fun _ ↦ by simp) rfl
  refine ((hU.tendsto_at t).comp Real.tendsto_toNNReal_nhdsGT_zero_nhdsNE).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Function.comp_apply, one_mul, smul_eq_mul]
  rw [← integral_sub_left_eq_self _ volume t]
  simp_rw [upperHalfPlanePoissonKernel_add_mul_I_eq_cauchyPDFReal (le_of_lt hy), sub_sub_cancel]

/-- **Decay of the Poisson integrals of a test function.** For `0 < y ≤ 1`, `φ` measurable with
`ψ(x) = |φ(x)| (1 + x ^ 2)` integrable and bounded by `M`,
`|∫ P(x + iy, t) φ(x) dx| ≤ 2 (M + ∫ ψ) / (1 + t ^ 2)`. -/
theorem abs_integral_upperHalfPlanePoissonKernel_add_mul_I_mul_le
    (hφ : AEStronglyMeasurable φ) (hψ : Integrable fun x ↦ |φ x| * (1 + x ^ 2)) {M : ℝ}
    (hM : ∀ x, |φ x| * (1 + x ^ 2) ≤ M) {y : ℝ} (hy₀ : 0 < y) (hy₁ : y ≤ 1) (t : ℝ) :
    |∫ x : ℝ, upperHalfPlanePoissonKernel (x + y * I) t * φ x| ≤
      2 * (M + ∫ x, |φ x| * (1 + x ^ 2)) / (1 + t ^ 2) := by
  set ψ : ℝ → ℝ := fun x ↦ |φ x| * (1 + x ^ 2)
  have hP (x : ℝ) : 0 ≤ upperHalfPlanePoissonKernel (x + y * I) t :=
    upperHalfPlanePoissonKernel_nonneg (by simpa using hy₀.le) t
  have hPint := integrable_upperHalfPlanePoissonKernel_add_mul_I y t
  have hP1 := integral_upperHalfPlanePoissonKernel_add_mul_I hy₀ t
  have hψP : Integrable fun x ↦ ψ x * upperHalfPlanePoissonKernel (x + y * I) t :=
    hPint.bdd_mul hψ.aestronglyMeasurable
      (.of_forall fun x ↦ by rw [Real.norm_of_nonneg (by positivity)]; exact hM x)
  have hφP : Integrable fun x : ℝ ↦ upperHalfPlanePoissonKernel (x + y * I) t * φ x := by
    have hφM (x : ℝ) : ‖φ x‖ ≤ M :=
      (le_mul_of_one_le_right (abs_nonneg _) (by nlinarith [sq_nonneg x])).trans (hM x)
    exact hPint.mul_bdd hφ (.of_forall hφM)
  have ht : 0 < 1 + t ^ 2 := by positivity
  rw [le_div_iff₀ ht, mul_comm _ (1 + t ^ 2), ← abs_of_pos ht, ← abs_mul, ← integral_const_mul]
  calc |∫ x : ℝ, (1 + t ^ 2) * (upperHalfPlanePoissonKernel (x + y * I) t * φ x)|
      ≤ ∫ x : ℝ, |(1 + t ^ 2) * (upperHalfPlanePoissonKernel (x + y * I) t * φ x)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, (2 * (ψ x * upperHalfPlanePoissonKernel (x + y * I) t) + 2 * π⁻¹ * ψ x) := by
        refine integral_mono (hφP.const_mul _).abs ((hψP.const_mul 2).add (hψ.const_mul _))
          fun x ↦ ?_
        have h := one_add_sq_mul_upperHalfPlanePoissonKernel_add_mul_I_le hy₀ hy₁ x t
        rw [abs_mul, abs_mul, abs_of_pos ht, abs_of_nonneg (hP x)]
        have := mul_le_mul_of_nonneg_right h (abs_nonneg (φ x))
        simp only [ψ]
        nlinarith
    _ = 2 * (∫ x, ψ x * upperHalfPlanePoissonKernel (x + y * I) t) + 2 * π⁻¹ * ∫ x, ψ x := by
        rw [integral_add (hψP.const_mul 2) (hψ.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * M + 2 * ∫ x, ψ x := by
        have h1 : ∫ x, ψ x * upperHalfPlanePoissonKernel (x + y * I) t ≤ M := by
          calc ∫ x, ψ x * upperHalfPlanePoissonKernel (x + y * I) t
              ≤ ∫ x : ℝ, M * upperHalfPlanePoissonKernel (x + y * I) t :=
                integral_mono hψP (hPint.const_mul M) fun x ↦
                  mul_le_mul_of_nonneg_right (hM x) (hP x)
            _ = M := by rw [integral_const_mul, hP1, mul_one]
        have h2 : 0 ≤ ∫ x, ψ x := integral_nonneg fun x ↦ by positivity
        have h3 : π⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])
        nlinarith
    _ = 2 * (M + ∫ x, |φ x| * (1 + x ^ 2)) := by ring

end TestFunction

/-! ### The vague limit -/

section VagueLimit

variable {ν : Measure ℝ} {φ : ℝ → ℝ}

/-- The weight `|φ(x)| (1 + x ^ 2)` of a compactly supported `φ` has compact support. -/
private theorem hasCompactSupport_abs_mul_one_add_sq (hφc : HasCompactSupport φ) :
    HasCompactSupport fun x ↦ |φ x| * (1 + x ^ 2) :=
  (hφc.comp_left abs_zero).mul_right

/-- The weight `|φ(x)| (1 + x ^ 2)` of a continuous compactly supported `φ` is integrable. -/
private theorem integrable_abs_mul_one_add_sq (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable fun x ↦ |φ x| * (1 + x ^ 2) :=
  (by fun_prop : Continuous fun x ↦ |φ x| * (1 + x ^ 2)).integrable_of_hasCompactSupport
    (hasCompactSupport_abs_mul_one_add_sq hφc)

/-- At every height `y`, `(x, t) ↦ P(x + iy, t)` is jointly measurable. -/
private theorem measurable_upperHalfPlanePoissonKernel_add_mul_I (y : ℝ) :
    Measurable fun p : ℝ × ℝ ↦ upperHalfPlanePoissonKernel (p.1 + y * I) p.2 :=
  measurable_uncurry_upperHalfPlanePoissonKernel.comp
    (by fun_prop : Measurable fun p : ℝ × ℝ ↦ ((p.1 + y * I : ℂ), p.2))

/-- For `y > 0`, `(x, t) ↦ P(x + iy, t) φ(x)` is integrable for Lebesgue measure times a
Poisson-finite `ν`, when `φ` is a.e. strongly measurable and `|φ(x)| (1 + x ^ 2)` is integrable. -/
private theorem integrable_upperHalfPlanePoissonKernel_add_mul_I_mul_prod (hν : IsPoissonFinite ν)
    (hφ : AEStronglyMeasurable φ) (hψ : Integrable fun x ↦ |φ x| * (1 + x ^ 2)) {y : ℝ}
    (hy : 0 < y) :
    Integrable (fun p : ℝ × ℝ ↦ upperHalfPlanePoissonKernel (p.1 + y * I) p.2 * φ p.1)
      (volume.prod ν) := by
  have := hν.isFiniteMeasureOnCompacts
  set ψ : ℝ → ℝ := fun x ↦ |φ x| * (1 + x ^ 2)
  set K := 2 * max y y⁻¹ / π
  refine ((hψ.mul_const K).mul_prod ((isPoissonFinite_iff ν).1 hν)).mono' ?_
    (.of_forall fun p ↦ ?_)
  · exact (measurable_upperHalfPlanePoissonKernel_add_mul_I y).aestronglyMeasurable.mul
      hφ.comp_fst
  · have h := upperHalfPlanePoissonKernel_le (z := p.1 + y * I) (by simpa using hy.le) p.2
    have hP := upperHalfPlanePoissonKernel_nonneg (z := p.1 + y * I) (by simpa using hy.le) p.2
    have hre : ((p.1 : ℂ) + y * I).re = p.1 := by simp
    have him : ((p.1 : ℂ) + y * I).im = y := by simp
    rw [hre, him] at h
    rw [norm_mul, Real.norm_of_nonneg hP, Real.norm_eq_abs]
    calc upperHalfPlanePoissonKernel (p.1 + y * I) p.2 * |φ p.1|
        ≤ 2 * (1 + p.1 ^ 2) * max y y⁻¹ / π / (1 + p.2 ^ 2) * |φ p.1| :=
          mul_le_mul_of_nonneg_right h (abs_nonneg _)
      _ = ψ p.1 * K * (1 + p.2 ^ 2)⁻¹ := by simp only [ψ, K]; ring

/-- **Fubini for the Poisson integral against a test function.** For `y > 0`, `φ` a.e. strongly
measurable and `|φ(x)| (1 + x ^ 2)` integrable,
`∫ φ(x) P[ν](x + iy) dx = ∫ (∫ P(x + iy, t) φ(x) dx) dν(t)`. -/
theorem integral_mul_upperHalfPlanePoissonIntegral_add_mul_I (hν : IsPoissonFinite ν)
    (hφ : AEStronglyMeasurable φ) (hψ : Integrable fun x ↦ |φ x| * (1 + x ^ 2)) {y : ℝ}
    (hy : 0 < y) :
    ∫ x, φ x * upperHalfPlanePoissonIntegral ν (x + y * I) =
      ∫ t, (∫ x : ℝ, upperHalfPlanePoissonKernel (x + y * I) t * φ x) ∂ν := by
  have := hν.isFiniteMeasureOnCompacts
  rw [← integral_integral_swap
    (integrable_upperHalfPlanePoissonKernel_add_mul_I_mul_prod hν hφ hψ hy)]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [upperHalfPlanePoissonIntegral_def, integral_mul_const]
  exact mul_comm _ _

/-- For `y > 0`, `φ` a.e. strongly measurable and `|φ(x)| (1 + x ^ 2)` integrable,
`x ↦ φ(x) P[ν](x + iy)` is Lebesgue integrable. -/
theorem integrable_mul_upperHalfPlanePoissonIntegral_add_mul_I (hν : IsPoissonFinite ν)
    (hφ : AEStronglyMeasurable φ) (hψ : Integrable fun x ↦ |φ x| * (1 + x ^ 2)) {y : ℝ}
    (hy : 0 < y) :
    Integrable fun x ↦ φ x * upperHalfPlanePoissonIntegral ν (x + y * I) := by
  have := hν.isFiniteMeasureOnCompacts
  refine (integrable_upperHalfPlanePoissonKernel_add_mul_I_mul_prod hν hφ hψ hy)
    |>.integral_prod_left |>.congr (.of_forall fun x ↦ ?_)
  simp only [upperHalfPlanePoissonIntegral_def, integral_mul_const]
  exact mul_comm _ _

/-- **The boundary measure is the vague limit of the Poisson integral.** For a Poisson-finite `ν`
and `φ` continuous with compact support, `∫ φ(x) P[ν](x + iy) dx → ∫ φ dν` as `y → 0⁺`. -/
theorem tendsto_integral_mul_upperHalfPlanePoissonIntegral_add_mul_I (hν : IsPoissonFinite ν)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun y : ℝ ↦ ∫ x, φ x * upperHalfPlanePoissonIntegral ν (x + y * I)) (𝓝[>] 0)
      (𝓝 (∫ t, φ t ∂ν)) := by
  have := hν.isFiniteMeasureOnCompacts
  have hψ := integrable_abs_mul_one_add_sq hφ hφc
  obtain ⟨M, hM⟩ := (by fun_prop : Continuous fun x ↦ |φ x| * (1 + x ^ 2))
    |>.bounded_above_of_compact_support (hasCompactSupport_abs_mul_one_add_sq hφc)
  obtain ⟨B, hB⟩ := hφ.bounded_above_of_compact_support hφc
  set C := 2 * (M + ∫ x, |φ x| * (1 + x ^ 2))
  have hM' (x : ℝ) : |φ x| * (1 + x ^ 2) ≤ M := (Real.le_norm_self _).trans (hM x)
  refine (tendsto_integral_filter_of_dominated_convergence (fun t ↦ C * (1 + t ^ 2)⁻¹)
    ?_ ?_ (((isPoissonFinite_iff ν).1 hν).const_mul C)
    (.of_forall (tendsto_integral_upperHalfPlanePoissonKernel_add_mul_I_mul
      (hφc.uniformContinuous_of_continuous hφ) hB))).congr' ?_
  · refine .of_forall fun y ↦ ?_
    exact ((((measurable_upperHalfPlanePoissonKernel_add_mul_I y).mul
      (hφ.measurable.comp measurable_fst)).comp measurable_swap).stronglyMeasurable
        |>.integral_prod_right' (ν := volume)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with y hy
    refine .of_forall fun t ↦ ?_
    rw [Real.norm_eq_abs, ← div_eq_mul_inv]
    exact abs_integral_upperHalfPlanePoissonKernel_add_mul_I_mul_le hφ.aestronglyMeasurable
      hψ hM' hy.1 hy.2 t
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (integral_mul_upperHalfPlanePoissonIntegral_add_mul_I hν hφ.aestronglyMeasurable hψ
      hy).symm

/-- **The boundary measure of `c Im + P[ν]` as a vague limit.** If `u = c Im + P[ν]` on the upper
half-plane, with `c ∈ ℝ` arbitrary and `ν` Poisson-finite, then for `φ` continuous with compact
support, `∫ φ(x) u(x + iy) dx → ∫ φ dν` as `y → 0⁺`: `ν` is the vague limit of the
measures `u(x + iy) dx`. -/
theorem tendsto_integral_mul_of_eq_mul_im_add_upperHalfPlanePoissonIntegral {u : ℂ → ℝ} {c : ℝ}
    (hν : IsPoissonFinite ν)
    (hrep : ∀ z ∈ upperHalfPlaneSet, u z = c * z.im + upperHalfPlanePoissonIntegral ν z)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun y : ℝ ↦ ∫ x, φ x * u (x + y * I)) (𝓝[>] 0) (𝓝 (∫ t, φ t ∂ν)) := by
  have h0 : Tendsto (fun y : ℝ ↦ c * y * ∫ x, φ x) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun y : ℝ ↦ c * y * ∫ x, φ x := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := h0.add (tendsto_integral_mul_upperHalfPlanePoissonIntegral_add_mul_I hν hφ hφc)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hint := integrable_mul_upperHalfPlanePoissonIntegral_add_mul_I hν
    hφ.aestronglyMeasurable (integrable_abs_mul_one_add_sq hφ hφc) hy
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hu (x : ℝ) : φ x * u (x + y * I) =
      c * y * φ x + φ x * upperHalfPlanePoissonIntegral ν (x + y * I) := by
    have him : ((x : ℂ) + y * I).im = y := by simp
    rw [hrep _ (by simpa using hy), him]
    ring
  simp_rw [hu]
  rw [integral_add (hφi.const_mul _) hint, integral_const_mul]

end VagueLimit

end TauCeti
