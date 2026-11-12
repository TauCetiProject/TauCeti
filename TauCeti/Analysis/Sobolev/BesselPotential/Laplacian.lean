/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Elliptic regularity for classical solutions on the Bessel-potential scale

Let `E` be a finite-dimensional real inner product space, and write `L² ∩ H^s` for the real
functions `realSobolevFunctions E s 2`; this is all of `H^s` when `s ≥ 0`. For `c > 0`, a real
`C²` function `v ∈ L²(E)` whose classical Laplacian satisfies `c v - Δv ∈ L² ∩ H^s` lies in
`L² ∩ H^{s+2}` (`TemperedDistribution.mem_realSobolevFunctions_add_two_of_sub_laplacian`).
Indeed, Green's second identity against test functions
(`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`) identifies the distributional
Laplacian of `v` with its classical Laplacian, with no decay of `v` or of its derivatives
assumed, and the resolvent of the Laplacian gains two derivatives
(`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`).

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

* `TemperedDistribution.mem_realSobolevFunctions_add_two_of_sub_laplacian`: for `c > 0`,
  `c v - Δv ∈ L² ∩ H^s` implies `v ∈ L² ∩ H^{s+2}` for a `C²` function `v ∈ L²`.
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
open scoped SchwartzMap Laplacian Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Elliptic regularity for classical functions.** For `c > 0`, a real `C²` function
`v ∈ L²(E)` with `c v - Δv ∈ L² ∩ H^s` lies in `L² ∩ H^{s+2}` (these are `H^s` and `H^{s+2}` when
`s ≥ 0`). Here `Δv` is the classical Laplacian; no decay of `v` or of its derivatives at infinity
is assumed. -/
theorem mem_realSobolevFunctions_add_two_of_sub_laplacian {c s : ℝ} (hc : 0 < c) {v : E → ℝ}
    (hv : ContDiff ℝ 2 v) (hv2 : MemLp v 2 volume)
    (h : (fun x ↦ c * v x - Δ v x) ∈ realSobolevFunctions E s 2) :
    v ∈ realSobolevFunctions E (s + 2) 2 := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 h
  set T : 𝓢'(E, ℂ) := Lp.toTemperedDistribution (Complex.ofRealCLM.compLp (hv2.toLp v))
  have hR : MemLp (fun x ↦ c * v x - Δ v x) 2 volume := memLp_of_mem_realSobolevFunctions h
  -- The distributional equation `-Δ T + c T = c v - Δv`, tested on compactly supported functions.
  have hT : -Δ T + c • T = Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u) := by
    refine ext_real fun φ hφ ↦ ?_
    have hφ2 := φ.memLp 2 (μ := volume)
    let φ' : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) :=
      ⟨φ, φ.smooth ⊤, hφ, by simp only [TopologicalSpace.Opens.coe_top, Set.subset_univ]⟩
    have hgreen := ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian (μ := volume)
      (hv.contDiffOn (s := (⊤ : TopologicalSpace.Opens E))) φ'
    simp only [smul_eq_mul, show (φ' : E → ℝ) = φ from TestFunction.coe_mk] at hgreen
    have hT' (ψ : 𝓢(E, ℝ)) : T (ψ.postcompCLM Complex.ofRealCLM) = ((∫ x, ψ x * v x : ℝ) : ℂ) := by
      rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
        integral_congr_ae (hv2.coeFn_toLp.mono fun x hx ↦ by rw [hx])]
    have hu' : Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)
        (φ.postcompCLM Complex.ofRealCLM) = ((∫ x, φ x * (c * v x - Δ v x) : ℝ) : ℂ) := by
      rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
        integral_congr_ae (huf.mono fun x hx ↦ by rw [hx])]
    have hsplit : ∫ x, φ x * (c * v x - Δ v x) = c * (∫ x, φ x * v x) - ∫ x, φ x * Δ v x := by
      have hcv : Integrable (fun x ↦ c * (φ x * v x)) := (hφ2.integrable_mul hv2).const_mul c
      have hΔv : Integrable (fun x ↦ φ x * Δ v x) := (hcv.sub (hφ2.integrable_mul hR)).congr
        (Filter.Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply, Pi.mul_apply]; ring)
      rw [← integral_const_mul, ← integral_sub hcv hΔv]
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
  have hT2 : MemSobolev (s + 2) 2 T :=
    (memSobolev_add_two_iff_neg_laplacian_add_smul hc).2 (by rw [hT]; exact hu)
  exact mem_realSobolevFunctions.2 ⟨hv2.toLp v, hv2.coeFn_toLp, hT2⟩

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
    have h := mem_realSobolevFunctions_add_two_of_sub_laplacian (s := 0) one_pos hv hv2 (by
      rw [hsub, mem_realSobolevFunctions_zero_iff]
      exact (hv2.sub (hexp.const_smul c)).sub (memLp_of_mem_realSobolevFunctions hg))
    rwa [zero_add] at h
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
        linarith [show (finrank ℝ E : ℝ) < 4 by exact_mod_cast hE]
      have hr : min s (2 * ((n + 1 : ℕ) : ℝ)) ≤ min s (2 * n) + 2 := by
        rw [← min_add_add_right]
        exact le_min ((min_le_left _ _).trans (by linarith))
          ((min_le_right _ _).trans (by push_cast; linarith))
      have hexp := exp_sub_one_mem_realSobolevFunctions ht ih
      refine mem_realSobolevFunctions_add_two_of_sub_laplacian one_pos hv hv2 ?_
      rw [hsub]
      exact sub_mem (sub_mem (hmono hr ih) (Submodule.smul_mem _ c (hmono hr hexp)))
        (hmono (min_le_left _ _) hg)
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  have h := hall n
  rwa [min_eq_left (by linarith)] at h

end TemperedDistribution
