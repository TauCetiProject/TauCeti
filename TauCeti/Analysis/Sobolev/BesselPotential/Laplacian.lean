/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Elliptic regularity for classical solutions on the Bessel-potential scale

Let `E` be a finite-dimensional real inner product space, let `1 < p < ∞`, and write
`Lᵖ ∩ H^{s,p}` for the real functions `realSobolevFunctions E s p`; this is all of `H^{s,p}` when
`s ≥ 0`. For every real `c`, a real `C²` function `v ∈ Lᵖ(E)` whose classical Laplacian satisfies
`c v - Δv ∈ Lᵖ ∩ H^{s,p}` lies in `Lᵖ ∩ H^{s+2,p}`
(`TemperedDistribution.mem_realSobolevFunctions_add_two_of_sub_laplacian`). Indeed, Green's second
identity against test functions (`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`)
identifies the distributional Laplacian of `v` with its classical Laplacian, with no decay of `v`
or of its derivatives assumed. The Bessel potential of order two is `1 - (2π)⁻² Δ`
(`TemperedDistribution.besselPotential_two_eq_sub_laplacian`). Substituting
`Δv = c v - (c v - Δv)`, it maps `v ∈ H^{t,p}` into `H^{min t s, p}`, so `v` gains two derivatives
at each step until it reaches `H^{s+2,p}`.

The second result bootstraps this for the semilinear equation

`Δv = c (exp v - 1) + g`

when `E` has dimension at most three. If `v` is a `C²` function in `L²` bounded above and
`g ∈ L² ∩ H^s`, then `v ∈ L² ∩ H^{s+2}`
(`TemperedDistribution.mem_realSobolevFunctions_add_two_of_laplacian_eq_mul_exp_sub_one_add`).
The upper bound on `v` makes `exp v - 1` square integrable, which gives `v ∈ H²`. From then on
`H^t(E)`, `t ≥ 2`, is closed under `w ↦ exp w - 1`
(`TemperedDistribution.exp_sub_one_mem_realSobolevFunctions`), so `v - Δv` gains regularity up to
that of `g`, and `v` gains two derivatives at each step. On the plane this equation is the scalar
equation `Δ log |α|² = (|α|² - 1) / 4` satisfied by the logarithmic modulus of a vortex section
away from its zeros, with `c = 1 / 4`.

## Main results

* `TemperedDistribution.memSobolev_add_two_of_neg_laplacian_add_smul`: for `1 < p < ∞`, a tempered
  distribution of some Sobolev order with `-Δ T + c T ∈ H^{s,p}` lies in `H^{s+2,p}`.
* `TemperedDistribution.laplacian_toTemperedDistribution_apply_postcompCLM_of_ae_eq`: the
  distributional Laplacian of a `C²` function `v ∈ Lᵖ` is its classical Laplacian on compactly
  supported test functions; for real `v`,
  `laplacian_toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM_of_ae_eq` is the same
  identity as a real integral.
* `TemperedDistribution.mem_realSobolevFunctions_add_two_of_sub_laplacian`: for `1 < p < ∞`,
  `c v - Δv ∈ Lᵖ ∩ H^{s,p}` implies `v ∈ Lᵖ ∩ H^{s+2,p}` for a `C²` function `v ∈ Lᵖ`.
* `TemperedDistribution.mem_realSobolevFunctions_add_two_of_laplacian_eq_mul_exp_sub_one_add`:
  `L²` solutions of `Δv = c (exp v - 1) + g` bounded above, with `g ∈ L² ∩ H^s`, lie in
  `L² ∩ H^{s+2}`, in dimension at most three.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (Sobolev spaces on `ℝⁿ`).
* M. E. Taylor, *Partial Differential Equations III*, 2nd ed., Springer, 2011, Chapter 13
  (composition estimates in `H^s`) and Chapter 14 (regularity for nonlinear elliptic equations).
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory Module
open scoped SchwartzMap Laplacian Distributions ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Elliptic bootstrap on the Bessel-potential scale.** For `1 < p < ∞` and any real `c`, a
tempered distribution `T` of some Sobolev order `t` with `-Δ T + c T ∈ H^{s,p}` lies in
`H^{s+2,p}`. The Bessel potential of order two is `1 - (2π)⁻² Δ`, and
`Δ T = c T - (-Δ T + c T)`, so the order of `T` gains two at each step until it reaches `s + 2`.
For `c > 0` and `p = 2` this is one direction of
`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`, which needs no a priori
order `t`. -/
theorem memSobolev_add_two_of_neg_laplacian_add_smul {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ ∞) {c s t : ℝ} {T : 𝓢'(E, F)} (hT : MemSobolev t p T)
    (h : MemSobolev s p (-Δ T + c • T)) : MemSobolev (s + 2) p T := by
  have hstep {r : ℝ} (hr : MemSobolev r p T) : MemSobolev (2 + min r s) p T := by
    have hJ : besselPotential E F 2 T = T - ((2 * Real.pi) ^ 2)⁻¹ • (c • T - (-Δ T + c • T)) := by
      rw [besselPotential_two_eq_sub_laplacian]
      congr 2
      abel
    rw [← memSobolev_besselPotential_iff, hJ]
    have hr' := hr.mono_of_one_lt hp hp_top (min_le_left r s)
    exact hr'.sub (((hr'.smul_of_tower c).sub
      (h.mono_of_one_lt hp hp_top (min_le_right r s))).smul_of_tower _)
  have hall (n : ℕ) : MemSobolev (min (s + 2) (t + 2 * n)) p T := by
    induction n with
    | zero => exact hT.mono_of_one_lt hp hp_top (by simp)
    | succ n ih =>
      refine (hstep ih).mono_of_one_lt hp hp_top ?_
      push_cast
      rw [← min_add_add_left, ← min_add_add_left]
      simp only [le_min_iff, min_le_iff]
      exact ⟨⟨Or.inl (by linarith), Or.inr (by linarith)⟩, Or.inl (by linarith)⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ((s + 2 - t) / 2)
  have h := hall n
  rwa [min_eq_left (by linarith)] at h

end inner

/-- On a compactly supported real test function `φ`, the distributional Laplacian of a `C²`
function `v ∈ Lᵖ(μ)`, given by any almost-everywhere representative `u`, is integration against its
classical Laplacian `Δv`, for any additive Haar measure `μ`. This is Green's second identity; no
decay of `v` or of its derivatives at infinity is assumed. -/
theorem laplacian_toTemperedDistribution_apply_postcompCLM_of_ae_eq {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {μ : Measure E}
    [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : Lp F p μ} {v : E → F}
    (hv : ContDiff ℝ 2 v) (hu : u =ᵐ[μ] v) {φ : 𝓢(E, ℝ)} (hφ : HasCompactSupport φ) :
    Δ (Lp.toTemperedDistribution u) (φ.postcompCLM Complex.ofRealCLM) =
      ∫ x, φ x • Δ v x ∂μ := by
  let φ' : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) :=
    ⟨φ, φ.smooth ⊤, hφ, by simp only [TopologicalSpace.Opens.coe_top, Set.subset_univ]⟩
  have hgreen := ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian (μ := μ)
    (hv.contDiffOn (s := (⊤ : TopologicalSpace.Opens E))) φ'
  simp only [φ', TestFunction.coe_mk] at hgreen
  rw [laplacian_apply_apply, TauCeti.laplacian_postcompCLM, Lp.toTemperedDistribution_apply,
    ← hgreen]
  refine integral_congr_ae (hu.mono fun x hx ↦ ?_)
  simp only [hx, SchwartzMap.postcompCLM_apply, SchwartzMap.laplacian_apply,
    Complex.ofRealCLM_apply, Complex.coe_smul]

/-- On a compactly supported real test function `φ`, the complex distributional Laplacian of a real
`C²` function `v ∈ Lᵖ(μ)`, given by any almost-everywhere representative `u`, is the real integral
of `φ Δv`. -/
theorem laplacian_toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM_of_ae_eq
    {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : Lp ℝ p μ} {v : E → ℝ}
    (hv : ContDiff ℝ 2 v) (hu : u =ᵐ[μ] v) {φ : 𝓢(E, ℝ)} (hφ : HasCompactSupport φ) :
    Δ (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) (φ.postcompCLM Complex.ofRealCLM) =
      ((∫ x, φ x * Δ v x ∂μ : ℝ) : ℂ) := by
  rw [laplacian_toTemperedDistribution_apply_postcompCLM_of_ae_eq
    (Complex.ofRealCLM.contDiff.comp hv)
    (((Complex.ofRealCLM.coeFn_compLp u).and hu).mono fun x hx ↦ by simp [hx.1, hx.2]) hφ,
    ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [hv.contDiffAt.laplacian_CLM_comp_left, Function.comp_apply, Complex.ofRealCLM_apply,
    Complex.real_smul, Complex.ofReal_mul]

/-- **Elliptic regularity for classical functions.** For `1 < p < ∞` and any real `c`, a real `C²`
function `v ∈ Lᵖ(E)` with `c v - Δv ∈ Lᵖ ∩ H^{s,p}` lies in `Lᵖ ∩ H^{s+2,p}` (these are `H^{s,p}`
and `H^{s+2,p}` when `s ≥ 0`). Here `Δv` is the classical Laplacian; no decay of `v` or of its
derivatives at infinity is assumed. -/
theorem mem_realSobolevFunctions_add_two_of_sub_laplacian {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ ∞) {c s : ℝ} {v : E → ℝ} (hv : ContDiff ℝ 2 v) (hvp : MemLp v p volume)
    (h : (fun x ↦ c * v x - Δ v x) ∈ realSobolevFunctions E s p) :
    v ∈ realSobolevFunctions E (s + 2) p := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 h
  set T : 𝓢'(E, ℂ) := Lp.toTemperedDistribution (Complex.ofRealCLM.compLp (hvp.toLp v))
  -- The distributional equation `-Δ T + c T = c v - Δv`, tested on compactly supported functions.
  have hT : -Δ T + c • T = Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u) := by
    refine ext_real fun φ hφ ↦ ?_
    have hφv : Integrable (fun x ↦ φ x * v x) :=
      (φ.continuous.mul hv.continuous).integrable_of_hasCompactSupport hφ.mul_right
    have hΔv : Continuous (Δ v) := (hv.laplacian (m := 0) (by simp)).continuous
    have hφΔ : Integrable (fun x ↦ φ x * Δ v x) :=
      (φ.continuous.mul hΔv).integrable_of_hasCompactSupport hφ.mul_right
    rw [add_apply, neg_apply, smul_apply,
      laplacian_toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM_of_ae_eq hv
        hvp.coeFn_toLp hφ,
      Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM_of_ae_eq hvp.coeFn_toLp,
      Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM_of_ae_eq huf]
    simp_rw [mul_sub, mul_left_comm (φ _) c]
    rw [integral_sub (hφv.const_mul c) hφΔ, integral_const_mul, Complex.real_smul]
    push_cast
    ring
  exact mem_realSobolevFunctions.2 ⟨hvp.toLp v, hvp.coeFn_toLp,
    memSobolev_add_two_of_neg_laplacian_add_smul hp hp_top (memSobolev_zero_iff.2 ⟨_, rfl⟩)
      (hT ▸ hu)⟩

/-- **Regularity for `Δv = c (exp v - 1) + g`.** In dimension at most three, a real `C²` function
`v ∈ L²(E)` bounded above and solving `Δv = c (exp v - 1) + g` classically, with
`g ∈ L² ∩ H^s`, lies in `L² ∩ H^{s+2}`. -/
theorem mem_realSobolevFunctions_add_two_of_laplacian_eq_mul_exp_sub_one_add
    (hE : finrank ℝ E < 4) {s : ℝ} {v g : E → ℝ} {c C : ℝ} (hv : ContDiff ℝ 2 v)
    (hv2 : MemLp v 2 volume) (hvC : ∀ x, v x ≤ C) (hg : g ∈ realSobolevFunctions E s 2)
    (heq : ∀ x, Δ v x = c * (Real.exp (v x) - 1) + g x) :
    v ∈ realSobolevFunctions E (s + 2) 2 := by
  have hsub : (fun x ↦ 1 * v x - Δ v x) =
      v - c • (fun x ↦ Real.exp (v x) - 1) - g := by
    ext x
    simp only [heq x, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hmono {t t' : ℝ} (h : t' ≤ t) := realSobolevFunctions_mono (E := E) (p := 2)
    (by norm_num) (by norm_num) h
  -- The base case `v ∈ H²`: since `v` is bounded above, `exp v - 1 ∈ L²`.
  have hbase : v ∈ realSobolevFunctions E 2 2 := by
    have hexp : MemLp (fun x ↦ Real.exp (v x) - 1) 2 volume :=
      (hv2.const_mul (Real.exp (max C 0))).of_le
        ((Real.continuous_exp.comp hv.continuous).sub continuous_const).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
          refine (TauCeti.abs_exp_sub_one_le_mul_exp_max (v x)).trans ?_
          gcongr
          exact hvC x)
    have h := mem_realSobolevFunctions_add_two_of_sub_laplacian (c := 1) (s := 0) (by norm_num)
      (by norm_num) hv hv2 (by
      rw [hsub, mem_realSobolevFunctions_zero_iff]
      exact (hv2.sub (hexp.const_smul c)).sub (memLp_of_mem_realSobolevFunctions hg))
    rwa [zero_add] at h
  have hE' : (finrank ℝ E : ℝ) < 4 := by exact_mod_cast hE
  rcases le_or_gt s 0 with hs | hs
  · exact hmono (by linarith) hbase
  -- For `s > 0`, each step gains two derivatives up to the regularity of `g`:
  -- `v ∈ H^{min s (2n) + 2}` for every `n`.
  have hall (n : ℕ) : v ∈ realSobolevFunctions E (min s (2 * n) + 2) 2 := by
    induction n with
    | zero => exact hmono (by simp) hbase
    | succ n ih =>
      have ht : (finrank ℝ E : ℝ) < 2 * (min s (2 * n) + 2) := by
        have : (0 : ℝ) ≤ min s (2 * n) := le_min hs.le (by positivity)
        linarith
      have hr : min s (2 * ((n + 1 : ℕ) : ℝ)) ≤ min s (2 * n) + 2 := by
        rw [← min_add_add_right]
        exact le_min ((min_le_left _ _).trans (by linarith))
          ((min_le_right _ _).trans (by push_cast; linarith))
      have hexp := exp_sub_one_mem_realSobolevFunctions ht ih
      refine mem_realSobolevFunctions_add_two_of_sub_laplacian (c := 1) (by norm_num) (by norm_num)
        hv hv2 ?_
      rw [hsub]
      exact sub_mem (sub_mem (hmono hr ih) (Submodule.smul_mem _ c (hmono hr hexp)))
        (hmono (min_le_left _ _) hg)
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  have h := hall n
  rwa [min_eq_left (by linarith)] at h

end TemperedDistribution
