/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Multiplication by smooth functions with bounded derivatives on `H^{k,p}`

Let `E` be a finite-dimensional real inner product space, `k` a natural number and `1 < p < ∞`.
If `g : E → ℂ` is smooth, of temperate growth, and its derivatives of order at most `k` are
bounded, then multiplication by `g` maps the Bessel-potential space `H^{k,p}(E, F)` (Mathlib's
`TemperedDistribution.MemSobolev k p`) to itself
(`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`). Unlike multiplication
by a Schwartz function (`TemperedDistribution.MemSobolev.smulLeftCLM`), no decay of `g` is
required: `g` may be a non-vanishing phase such as `(z / |z|) ^ m` outside a disc, or a
coefficient decaying only like `1 / |z|`. Such multipliers are the coefficients of the nonlinear
field equations on affine Sobolev spaces centered at a reference field with a nontrivial tail.

The proof is by induction on `k`. For `k = 0`, `H^{0,p} = Lᵖ` and `g` is bounded
(`TemperedDistribution.MemSobolev.smulLeftCLM_of_memLp_top`). For the
inductive step, `u ∈ H^{k+1,p}` exactly when `u ∈ Lᵖ` and every `∂_v u ∈ H^{k,p}`
(`TemperedDistribution.memSobolev_natCast_add_one_iff`), and the Leibniz rule
`∂_v (g u) = (∂_v g) u + g ∂_v u` (`TemperedDistribution.lineDerivOp_smulLeftCLM`) expresses
`∂_v (g u)` through multiplications by `g` and by `∂_v g`, whose derivatives of order at most `k`
are bounded.

The same holds for real functions and real `Lᵖ` functions whose complexification lies in
`H^{k,p}`
(`TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul_of_norm_iteratedFDeriv_le`).

## Main results

* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`: `g u ∈ H^{k,p}` for
  `u ∈ H^{k,p}`.
* `TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul_of_norm_iteratedFDeriv_le`:
  the real form.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press, 2003, §3.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap LineDeriv ENNReal

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The order-`0` case of the standing hypothesis that the derivatives of order at most `k` of a
continuous function are bounded puts the function in `L^∞`. -/
private theorem memLp_top_of_norm_iteratedFDeriv_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : E → G} (hg : Continuous g) {k : ℕ}
    (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) : MemLp g ∞ volume := by
  obtain ⟨C, hC⟩ := hbd 0 (Nat.zero_le k)
  exact memLp_top_of_bound hg.aestronglyMeasurable C (.of_forall fun x ↦ by simpa using hC x)

/-- Multiplication by an essentially bounded function of temperate growth maps `Lᵖ = H^{0,p}` to
itself. -/
theorem MemSobolev.smulLeftCLM_of_memLp_top {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hgm : MemLp g ∞ volume) {u : 𝓢'(E, F)} (hu : MemSobolev 0 p u) :
    MemSobolev 0 p (smulLeftCLM F g u) := by
  obtain ⟨f, rfl⟩ := memSobolev_zero_iff.1 hu
  exact memSobolev_zero_iff.2
    ⟨(hgm.toLp g • f : Lp F p volume), (Lp.toTemperedDistribution_smul_eq (r := p) hg hgm f).symm⟩

/-- **Multiplication by a smooth function with bounded derivatives on `H^{k,p}`.** For a natural
number `k` and `1 < p < ∞`, multiplication by a function `g` of temperate growth whose
derivatives of order at most `k` are bounded maps `H^{k,p}` to itself. -/
theorem MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) {u : 𝓢'(E, F)}
    (hu : MemSobolev k p u) : MemSobolev k p (smulLeftCLM F g u) := by
  have hgm := memLp_top_of_norm_iteratedFDeriv_le hg.1.continuous hbd
  induction k generalizing g u with
  | zero => simpa using MemSobolev.smulLeftCLM_of_memLp_top hg hgm (by simpa using hu)
  | succ k ih =>
    have hk : MemSobolev k p u := hu.mono_of_one_lt hp hp_top (by simp)
    rw [Nat.cast_succ, memSobolev_natCast_add_one_iff hp hp_top] at hu ⊢
    refine ⟨MemSobolev.smulLeftCLM_of_memLp_top hg hgm hu.1, fun v ↦ ?_⟩
    -- `∂_v (g u) = (∂_v g) u + g ∂_v u`, and `∂_v g` has bounded derivatives of order `≤ k`.
    rw [lineDerivOp_smulLeftCLM hg]
    have hbd' : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (fun x ↦ fderiv ℝ g x v) x‖ ≤ C :=
      (ContinuousLinearMap.apply ℝ ℂ v).exists_norm_iteratedFDeriv_comp_left_le
        (hg.fderiv.1.of_le (mod_cast le_top)) fun n hn ↦ by
          simpa only [norm_iteratedFDeriv_fderiv] using hbd (n + 1) (Nat.succ_le_succ hn)
    have hbdk : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C :=
      fun n hn ↦ hbd n (hn.trans k.le_succ)
    exact MemSobolev.add (ih (hg.fderiv_apply v) hbd' hk
      (memLp_top_of_norm_iteratedFDeriv_le (hg.fderiv_apply v).1.continuous hbd'))
      (ih hg hbdk (hu.2 v) hgm)

/-- **Multiplication by a real smooth function with bounded derivatives on real `H^{k,p}`
functions.** For `1 < p < ∞`, the product of a real `Lᵖ` function whose complexification lies in
`H^{k,p}` with a real function `c` of temperate growth whose derivatives of order at most `k` are
bounded is again such a function. -/
theorem exists_mem_realSobolevSubmodule_ae_eq_mul_of_norm_iteratedFDeriv_le (hp : 1 < p)
    (hp_top : p ≠ ∞) {k : ℕ} {c : E → ℝ} (hc : c.HasTemperateGrowth)
    (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n c x‖ ≤ C)
    {u : Lp ℝ p (volume : Measure E)} (hu : u ∈ realSobolevSubmodule E k p) :
    ∃ v ∈ realSobolevSubmodule E k p, v =ᵐ[volume] fun x ↦ c x * u x := by
  have hcm := memLp_top_of_norm_iteratedFDeriv_le hc.1.continuous hbd
  have hm : MemLp (fun x ↦ c x * u x) p volume := hcm.mul (Lp.memLp u)
  have hc' : (fun x ↦ (c x : ℂ)).HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp hc
  -- The complexification of `c u` is the product of `c` with the complexification of `u`.
  have heq : Lp.toTemperedDistribution (Complex.ofRealCLM.compLp (hm.toLp _)) =
      smulLeftCLM ℂ (fun x ↦ (c x : ℂ))
        (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) := by
    ext φ
    rw [Lp.smulLeftCLM_toTemperedDistribution_apply hc', Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) (hm.toLp _),
      Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) u, hm.coeFn_toLp] with x h₁ h₂ h₃
    simp only [h₁, h₂, h₃, Complex.ofRealCLM_apply, Complex.ofReal_mul, smul_eq_mul]
  refine ⟨hm.toLp _, ?_, hm.coeFn_toLp⟩
  rw [mem_realSobolevSubmodule, heq]
  exact (mem_realSobolevSubmodule.1 hu).smulLeftCLM_of_norm_iteratedFDeriv_le hp hp_top hc'
    (Complex.ofRealCLM.exists_norm_iteratedFDeriv_comp_left_le (hc.1.of_le (mod_cast le_top)) hbd)

end TemperedDistribution
