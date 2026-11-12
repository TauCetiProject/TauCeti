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
  set U : 𝓢'(E, ℂ) := Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)
  have hΔv : Continuous (Δ v) := (hv.laplacian (m := 0) (by simp)).continuous
  -- The distributional equation `-Δ T + c T = c v - Δv`, tested on compactly supported functions.
  have hT : -Δ T + c • T = U := by
    refine ext_real fun φ hφ ↦ ?_
    let φ' : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) :=
      ⟨φ, φ.smooth ⊤, hφ, by simp only [TopologicalSpace.Opens.coe_top, Set.subset_univ]⟩
    have hgreen := ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian (μ := volume)
      (hv.contDiffOn (s := (⊤ : TopologicalSpace.Opens E))) φ'
    simp only [φ', TestFunction.coe_mk, smul_eq_mul] at hgreen
    have hT' (ψ : 𝓢(E, ℝ)) : T (ψ.postcompCLM Complex.ofRealCLM) = ((∫ x, ψ x * v x : ℝ) : ℂ) := by
      rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
        integral_congr_ae (hvp.coeFn_toLp.mono fun x hx ↦ by rw [hx])]
    have hu' : U (φ.postcompCLM Complex.ofRealCLM) =
        ((∫ x, φ x * (c * v x - Δ v x) : ℝ) : ℂ) := by
      rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
        integral_congr_ae (huf.mono fun x hx ↦ by rw [hx])]
    have hsplit : ∫ x, φ x * (c * v x - Δ v x) = c * (∫ x, φ x * v x) - ∫ x, φ x * Δ v x := by
      have hcv : Integrable (fun x ↦ c * (φ x * v x)) :=
        ((φ.continuous.mul hv.continuous).integrable_of_hasCompactSupport hφ.mul_right).const_mul c
      have hΔ : Integrable (fun x ↦ φ x * Δ v x) :=
        (φ.continuous.mul hΔv).integrable_of_hasCompactSupport hφ.mul_right
      rw [← integral_const_mul, ← integral_sub hcv hΔ]
      congr 1
      ext x
      ring
    have hΔφ : ∫ x, (Δ φ : 𝓢(E, ℝ)) x * v x = ∫ x, φ x * Δ v x := by
      simp only [SchwartzMap.laplacian_apply]
      exact hgreen
    rw [add_apply, neg_apply, smul_apply, laplacian_apply_apply, TauCeti.laplacian_postcompCLM,
      hT', hT', hu', hsplit, hΔφ, Complex.real_smul]
    push_cast
    ring
  -- Writing the Bessel potential `J² T = T - (2π)⁻² Δ T` with `Δ T = c T - U`, each step gains
  -- two derivatives up to the regularity of `U`: `T ∈ H^{min (s + 2) (2n), p}` for every `n`.
  have hstep {t : ℝ} (ht : MemSobolev t p T) : MemSobolev (2 + min t s) p T := by
    have hJ : besselPotential E ℂ 2 T = T - (((2 * Real.pi) ^ 2)⁻¹ : ℂ) • (c • T - U) := by
      rw [besselPotential_two_eq_sub_laplacian, ← hT, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simp
    rw [← memSobolev_besselPotential_iff, hJ]
    have hT' := ht.mono_of_one_lt hp hp_top (min_le_left t s)
    exact hT'.sub (((hT'.smul (c : ℂ)).sub (hu.mono_of_one_lt hp hp_top (min_le_right t s))).smul _)
  have hall (n : ℕ) : MemSobolev (min (s + 2) (2 * n)) p T := by
    induction n with
    | zero =>
      refine (memSobolev_zero_iff.2 ⟨_, rfl⟩).mono_of_one_lt hp hp_top ?_
      simp
    | succ n ih =>
      refine (hstep ih).mono_of_one_lt hp hp_top ?_
      push_cast
      rw [← min_add_add_left, ← min_add_add_left]
      simp only [le_min_iff, min_le_iff]
      exact ⟨⟨Or.inl (by linarith), Or.inr (by linarith)⟩, Or.inl (by linarith)⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ((s + 2) / 2)
  have hT2 := hall n
  rw [min_eq_left (by linarith)] at hT2
  exact mem_realSobolevFunctions.2 ⟨hvp.toLp v, hvp.coeFn_toLp, hT2⟩

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
