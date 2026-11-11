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

Let `E` be a finite-dimensional real inner product space. A real `C²` function `v ∈ L²(E)` whose
classical Laplacian satisfies `v - Δv ∈ H^s` lies in `H^{s+2}`
(`TemperedDistribution.mem_realSobolevFunctions_add_two_of_sub_laplacian`). Indeed, Green's
second identity against test functions
(`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`) identifies the distributional
Laplacian of `v` with its classical Laplacian, with no decay of `v` or of its derivatives
assumed, and the resolvent of the Laplacian gains two derivatives
(`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`).

The second result bootstraps this for the semilinear equation

`Δv = c (exp v - 1) + g`

when `E` has dimension at most three. If `v` is a bounded `C²` function in `L²` and `g` lies in
every `H^s`, then so does `v`
(`TemperedDistribution.mem_realSobolevFunctions_of_laplacian_eq_mul_exp_sub_one_add`). The
boundedness of `v` makes `exp v - 1` square integrable, which gives `v ∈ H²`. From then on
`H^s(E)` is an algebra and is closed under `w ↦ exp w - 1`
(`TemperedDistribution.exp_mul_sub_one_mem_realSobolevFunctions`), so `v - Δv ∈ H^s` and
`v ∈ H^{s+2}`. On the plane this equation is the scalar equation `Δ log |α|² = (|α|² - 1) / 4`
satisfied by the logarithmic modulus of a vortex section away from its zeros, with `c = 1 / 4`.

## Main results

* `TemperedDistribution.mem_realSobolevFunctions_add_two_of_sub_laplacian`: `v - Δv ∈ H^s`
  implies `v ∈ H^{s+2}` for a `C²` function `v ∈ L²`.
* `TemperedDistribution.mem_realSobolevFunctions_of_laplacian_eq_mul_exp_sub_one_add`: bounded
  `L²` solutions of `Δv = c (exp v - 1) + g` with `g` in every `H^s` lie in every `H^s`, in
  dimension at most three.

## References

* L. C. Evans, *Partial Differential Equations*, Section 6.3 (interior regularity) and Section 8
  for semilinear bootstraps.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory Module
open scoped SchwartzMap Laplacian Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Elliptic regularity for classical functions.** A real `C²` function `v ∈ L²(E)` with
`v - Δv ∈ H^s` lies in `H^{s+2}`. Here `Δv` is the classical Laplacian; no decay of `v` or of its
derivatives at infinity is assumed. -/
theorem mem_realSobolevFunctions_add_two_of_sub_laplacian {s : ℝ} {v : E → ℝ}
    (hv : ContDiff ℝ 2 v) (hv2 : MemLp v 2 volume)
    (h : (fun x ↦ v x - Δ v x) ∈ realSobolevFunctions E s 2) :
    v ∈ realSobolevFunctions E (s + 2) 2 := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 h
  set T : 𝓢'(E, ℂ) := Lp.toTemperedDistribution (Complex.ofRealCLM.compLp (hv2.toLp v))
  have hR : MemLp (fun x ↦ v x - Δ v x) 2 volume := memLp_of_mem_realSobolevFunctions h
  -- The distributional equation `-Δ T + T = v - Δv`, tested on compactly supported functions.
  have hT : -Δ T + (1 : ℝ) • T = Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u) := by
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
        (φ.postcompCLM Complex.ofRealCLM) = ((∫ x, φ x * (v x - Δ v x) : ℝ) : ℂ) := by
      rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
        integral_congr_ae (huf.mono fun x hx ↦ by rw [hx])]
    have hsplit : ∫ x, φ x * (v x - Δ v x) = (∫ x, φ x * v x) - ∫ x, φ x * Δ v x := by
      simp_rw [mul_sub]
      refine integral_sub (hφ2.integrable_mul hv2) (((hφ2.integrable_mul hv2).sub
        (hφ2.integrable_mul hR)).congr (Filter.Eventually.of_forall fun x ↦ ?_))
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring
    have hΔφ : ∫ x, (Δ φ : 𝓢(E, ℝ)) x * v x = ∫ x, φ x * Δ v x := by
      simp only [SchwartzMap.laplacian_apply]
      exact hgreen
    rw [add_apply, neg_apply, smul_apply, laplacian_apply_apply, TauCeti.laplacian_postcompCLM,
      hT', hT', hu', hsplit, hΔφ, one_smul]
    push_cast
    ring
  have hT2 : MemSobolev (s + 2) 2 T :=
    (memSobolev_add_two_iff_neg_laplacian_add_smul one_pos).2 (by rw [hT]; exact hu)
  exact mem_realSobolevFunctions.2 ⟨hv2.toLp v, hv2.coeFn_toLp, hT2⟩

/-- **Regularity for `Δv = c (exp v - 1) + g`.** In dimension at most three, a bounded real `C²`
function `v ∈ L²(E)` solving `Δv = c (exp v - 1) + g` classically, with `g` in every
Bessel-potential space `H^s`, lies in every `H^s`. -/
theorem mem_realSobolevFunctions_of_laplacian_eq_mul_exp_sub_one_add (hE : finrank ℝ E < 4)
    {v g : E → ℝ} {c C : ℝ} (hv : ContDiff ℝ 2 v) (hv2 : MemLp v 2 volume)
    (hvC : ∀ x, |v x| ≤ C) (hg : ∀ s, g ∈ realSobolevFunctions E s 2)
    (heq : ∀ x, Δ v x = c * (Real.exp (v x) - 1) + g x) (s : ℝ) :
    v ∈ realSobolevFunctions E s 2 := by
  have hsub : (fun x ↦ v x - Δ v x) =
      v - c • (fun x ↦ Real.exp (v x) - 1) - g := by
    ext x
    simp only [heq x, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- From `v ∈ H^s`, `s > n / 2`, to `v ∈ H^{s+2}`.
  have hstep {s : ℝ} (hs : finrank ℝ E < 2 * s) (h : v ∈ realSobolevFunctions E s 2) :
      v ∈ realSobolevFunctions E (s + 2) 2 := by
    have hexp : (fun x ↦ Real.exp (v x) - 1) ∈ realSobolevFunctions E s 2 := by
      simpa only [one_mul] using exp_mul_sub_one_mem_realSobolevFunctions hs h 1
    refine mem_realSobolevFunctions_add_two_of_sub_laplacian hv hv2 ?_
    rw [hsub]
    exact sub_mem (sub_mem h (Submodule.smul_mem _ c hexp)) (hg s)
  -- The base case `v ∈ H²`: since `v` is bounded, `exp v - 1 ∈ L²`.
  have hbase : v ∈ realSobolevFunctions E 2 2 := by
    have hexp : MemLp (fun x ↦ Real.exp (v x) - 1) 2 volume :=
      (hv2.const_mul (Real.exp C)).of_le
        ((Real.continuous_exp.comp hv.continuous).sub continuous_const).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos C), mul_comm]
          exact (TauCeti.abs_exp_sub_one_le_mul_exp_abs (v x)).trans
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hvC x)) (abs_nonneg _)))
    have h := mem_realSobolevFunctions_add_two_of_sub_laplacian (s := 0) hv hv2 (by
      rw [hsub, mem_realSobolevFunctions_zero_iff]
      exact (hv2.sub (hexp.const_smul c)).sub (memLp_of_mem_realSobolevFunctions (hg 0)))
    rwa [zero_add] at h
  have hall (n : ℕ) : v ∈ realSobolevFunctions E (2 + 2 * n) 2 := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      have h := hstep (by linarith [show (finrank ℝ E : ℝ) < 4 by exact_mod_cast hE,
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) ih
      rwa [show (2 : ℝ) + 2 * n + 2 = 2 + 2 * ((n + 1 : ℕ) : ℝ) by push_cast; ring] at h
  obtain ⟨n, hn⟩ := exists_nat_ge s
  exact realSobolevFunctions_mono (by norm_num) (by norm_num) (by linarith) (hall n)

end TemperedDistribution
