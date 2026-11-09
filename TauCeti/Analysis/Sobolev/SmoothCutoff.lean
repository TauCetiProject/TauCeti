/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import TauCeti.Analysis.Calculus.ContDiff.Scaling
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Compactly supported approximation of smooth Sobolev functions

A smooth function whose classical derivatives through order `k` belong to `Lᵖ` can be
approximated by smooth compactly supported functions, simultaneously in the `Lᵖ` seminorm
of every derivative through order `k`, for every finite `p`. The domain is a finite-dimensional
real normed space, the codomain is a real normed space, and the measure is arbitrary.

The approximations are `χ ((n + 1)⁻¹ • x) • f x`, with a fixed smooth compactly supported
cutoff `χ` equal to one near zero. The Leibniz estimate gives an integrable envelope consisting
of a finite sum of norms of derivatives of `f`. At each point the approximation eventually
agrees with `f` on a neighborhood, so all its derivatives eventually agree there as well.
This is the cutoff step used after smoothing in whole-space Sobolev density arguments.
The approximation holds for functions of finite smoothness `m ≥ k`, with approximants of the same
smoothness; for `C¹` integrable functions with integrable derivative it gives compactly supported
`C¹` approximants converging in `L¹`, with `L¹` norms of the derivatives bounded by `‖Du‖₁`
plus a sequence tending to zero
(`TauCeti.exists_contDiff_hasCompactSupport_tendsto_eLpNorm_fderiv`).
The statements here concern classical derivatives; no identification with a bundled weak
Sobolev space is asserted.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.1. The derivative estimate uses Mathlib's
`norm_iteratedFDeriv_smul_le` and `iteratedFDeriv_comp_const_smul`.

The expanding-cutoff construction and the compactly supported bump's derivative bounds are
adapted from `SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop` in
`TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean`. Its positive-order derivative scaling
estimate is shared via `TauCeti.norm_iteratedFDeriv_comp_inv_smul_sub_const_le`.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory
open scoped ContDiff ENNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Expanding cutoffs approximate the `k`-th classical derivative of a `Cᵏ` function in `Lᵖ`.
Only the derivatives up to the requested order need to be integrable; the measure need not
be translation invariant. -/
theorem tendsto_eLpNorm_iteratedFDeriv_cutoff_sub
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    {μ : Measure E} {p : ENNReal} (hp : p ≠ ⊤)
    {χ : E → ℝ} {f : E → F} {k : ℕ} (hχ : ContDiff ℝ k χ)
    (hχ1 : χ =ᶠ[𝓝 0] 1) {B : ℕ → ℝ}
    (hB : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B i)
    (hf : ContDiff ℝ k f) (hmem : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) p μ) :
    Tendsto (fun n : ℕ ↦ eLpNorm
      (iteratedFDeriv ℝ k (fun x ↦ χ (((n : ℝ) + 1)⁻¹ • x) • f x) -
        iteratedFDeriv ℝ k f) p μ) atTop (𝓝 0) := by
  let error (n : ℕ) : E → F := fun x ↦ (χ (((n : ℝ) + 1)⁻¹ • x) - 1) • f x
  have hsmooth (n : ℕ) : ContDiff ℝ k (error n) :=
    ((hχ.comp (contDiff_const_smul _)).sub contDiff_const).smul hf
  have herr (n : ℕ) :
      iteratedFDeriv ℝ k (error n) =
        iteratedFDeriv ℝ k (fun x ↦ χ (((n : ℝ) + 1)⁻¹ • x) • f x) -
          iteratedFDeriv ℝ k f := by
    funext x
    simp only [error, sub_smul, one_smul]
    exact fun_iteratedFDeriv_sub_apply
      ((hχ.comp (contDiff_const_smul _)).smul hf).contDiffAt hf.contDiffAt
  -- The Leibniz estimate is dominated by a finite sum of integrable derivative norms.
  let bound : E → ℝ := fun x ↦ ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * (1 + B i) * ‖iteratedFDeriv ℝ (k - i) f x‖
  have hbmem : MemLp bound p μ := by
    apply memLp_finsetSum
    intro i _
    exact (hmem (k - i) (Nat.sub_le _ _)).norm.const_smul
      ((k.choose i : ℝ) * (1 + B i))
  have hb (n : ℕ) (x : E) : ‖iteratedFDeriv ℝ k (error n) x‖ ≤ ‖bound x‖ := by
    refine (norm_iteratedFDeriv_smul_le
      ((hχ.comp (contDiff_const_smul _)).sub contDiff_const) hf x le_rfl).trans ?_
    refine (Finset.sum_le_sum fun i hi ↦ ?_).trans (le_abs_self _)
    have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hd := norm_iteratedFDeriv_comp_inv_smul_sub_const_le_add_norm (hB i hi')
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ) ≤ (n : ℝ) + 1) 1 x
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa [add_comm] using hd)
        (Nat.cast_nonneg _)) (norm_nonneg _)
  -- The expanding region where the cutoff is one gives eventual local agreement.
  have hlim (x : E) : ∀ᶠ n : ℕ in atTop, iteratedFDeriv ℝ k (error n) x = 0 := by
    have ht : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
      simpa only [one_div, zero_smul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x
    filter_upwards [ht.eventually (eventually_eventually_nhds.2 hχ1)] with n hn
    have heq : error n =ᶠ[𝓝 x] 0 := by
      have hnear := (continuous_const_smul ((n : ℝ) + 1)⁻¹).continuousAt.eventually hn
      filter_upwards [hnear] with y hy
      simp only [error, hy, Pi.one_apply, sub_self, zero_smul, Pi.zero_apply]
    simpa only [iteratedFDeriv_zero, Pi.zero_apply] using
      (heq.iteratedFDeriv ℝ k).eq_of_nhds
  -- Dominated convergence applies to the full derivative error, including order zero.
  have ht := tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (g := 0) hp
    (Eventually.of_forall fun n ↦ (hsmooth n).continuous_iteratedFDeriv le_rfl
      |>.aestronglyMeasurable)
    hbmem
    (Eventually.of_forall fun n ↦ Eventually.of_forall fun x ↦ by
      simpa only [ofReal_norm, Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul] using
        ENNReal.ofReal_le_ofReal (hb n x))
    (Eventually.of_forall fun x ↦ (tendsto_congr' (hlim x)).mpr tendsto_const_nhds)
  simpa only [sub_zero, herr] using ht

/-- Multiplication by a `Cᵏ` scalar function with bounded derivatives preserves `Lᵖ`
integrability of the `k`-th classical derivative, provided every derivative of the second
factor through order `k` belongs to `Lᵖ`. -/
theorem memLp_iteratedFDeriv_smul_of_bounded
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    {μ : Measure E} {p : ENNReal} {χ : E → ℝ} {f : E → F} {k : ℕ}
    (hχ : ContDiff ℝ k χ) {B : ℕ → ℝ}
    (hB : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B i)
    (hf : ContDiff ℝ k f) (hmem : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) p μ) :
    MemLp (iteratedFDeriv ℝ k (fun x ↦ χ x • f x)) p μ := by
  have hbmem : MemLp (fun x ↦ ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * B i * ‖iteratedFDeriv ℝ (k - i) f x‖) p μ := by
    apply memLp_finsetSum
    intro i _
    exact (hmem (k - i) (Nat.sub_le _ _)).norm.const_smul ((k.choose i : ℝ) * B i)
  refine hbmem.mono' ((hχ.smul hf).continuous_iteratedFDeriv le_rfl
    |>.aestronglyMeasurable) (Eventually.of_forall fun x ↦ ?_)
  exact (norm_iteratedFDeriv_smul_le hχ hf x le_rfl).trans
    (Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hB i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) x)
        (Nat.cast_nonneg _)) (norm_nonneg _))

/-- A `Cᵐ` function with `Lᵖ` classical derivatives through order `k ≤ m` admits `Cᵐ`
compactly supported approximations converging in the `Lᵖ` seminorm of every such derivative.
The same approximation sequence works for all orders through `k`. -/
theorem exists_contDiff_hasCompactSupport_approximation
    [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure E} {p : ENNReal} (hp : p ≠ ⊤)
    {m : ℕ∞} {f : E → F} (hf : ContDiff ℝ m f) (k : ℕ) (hk : (k : ℕ∞) ≤ m)
    (hmem : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) p μ) :
    ∃ g : ℕ → E → F,
      (∀ n, ContDiff ℝ m (g n) ∧ HasCompactSupport (g n)) ∧
      (∀ n i, i ≤ k → MemLp (iteratedFDeriv ℝ i (g n)) p μ) ∧
      ∀ i ≤ k, Tendsto (fun n ↦
        eLpNorm (iteratedFDeriv ℝ i (g n) - iteratedFDeriv ℝ i f) p μ) atTop (𝓝 0) := by
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbdd (i : ℕ) : ∃ B, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B :=
    (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (χ.hasCompactSupport.iteratedFDeriv i)
  choose B hB using hbdd
  have hscaled (n i : ℕ) (x : E) :
      ‖iteratedFDeriv ℝ i (fun y ↦ χ (((n : ℝ) + 1)⁻¹ • y)) x‖ ≤ B i := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [iteratedFDeriv_comp_const_smul _ (χ.contDiff.of_le (mod_cast le_top)),
      norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg hn.le]
    have hpow : (((n : ℝ) + 1)⁻¹) ^ i ≤ 1 :=
      pow_le_one₀ (by positivity)
        (inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    simpa only [one_mul] using mul_le_mul hpow (hB i _) (norm_nonneg _) zero_le_one
  have hfk (i : ℕ) (hi : i ≤ k) : ContDiff ℝ i f :=
    hf.of_le (by exact_mod_cast (Nat.cast_le.2 hi).trans hk)
  refine ⟨fun n x ↦ χ (((n : ℝ) + 1)⁻¹ • x) • f x, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(χ.contDiff.comp (contDiff_const_smul _)).smul hf,
      (χ.hasCompactSupport.comp_smul (by positivity : ((n : ℝ) + 1)⁻¹ ≠ 0)).smul_right⟩
  · intro n i hi
    exact memLp_iteratedFDeriv_smul_of_bounded
      ((χ.contDiff.comp (contDiff_const_smul _)).of_le (mod_cast le_top))
      (fun j _ x ↦ hscaled n j x) (hfk i hi)
      (fun j hj ↦ hmem j (hj.trans hi))
  · intro i hi
    exact tendsto_eLpNorm_iteratedFDeriv_cutoff_sub hp
      (χ.contDiff.of_le (mod_cast le_top)) χ.eventuallyEq_one
      (fun j _ x ↦ hB j x) (hfk i hi)
      (fun j hj ↦ hmem j (hj.trans hi))

/-- A `C¹` integrable function with integrable derivative has compactly supported `C¹`
approximations `g n` that converge to it in `L¹`, with `L¹` norms of the derivatives at most
`‖Du‖₁ + ε n` for a sequence `ε n → 0`. -/
theorem exists_contDiff_hasCompactSupport_tendsto_eLpNorm_fderiv
    [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}
    {u : E → F} (hu : ContDiff ℝ 1 u) (hi : Integrable u μ)
    (htop : eLpNorm (fderiv ℝ u) 1 μ ≠ ⊤) :
    ∃ (g : ℕ → E → F) (ε : ℕ → ℝ≥0∞), (∀ n, ContDiff ℝ 1 (g n)) ∧
      (∀ n, HasCompactSupport (g n)) ∧ Tendsto (fun n => eLpNorm (g n - u) 1 μ) atTop (𝓝 0) ∧
      Tendsto ε atTop (𝓝 0) ∧
      ∀ n, eLpNorm (fderiv ℝ (g n)) 1 μ ≤ eLpNorm (fderiv ℝ u) 1 μ + ε n := by
  have hdu : AEStronglyMeasurable (fderiv ℝ u) μ :=
    (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable
  have hmem : ∀ i ≤ 1, MemLp (iteratedFDeriv ℝ i u) 1 μ := fun i hi1 => by
    interval_cases i
    · exact (memLp_one_iff_integrable.2 hi).congr_norm
        (hu.continuous_iteratedFDeriv (by simp) |>.aestronglyMeasurable)
        (.of_forall fun x => norm_iteratedFDeriv_zero.symm)
    · have hdi : Integrable (fderiv ℝ u) μ := ⟨hdu, by
        rwa [HasFiniteIntegral, ← eLpNorm_one_eq_lintegral_enorm hdu, lt_top_iff_ne_top]⟩
      exact (memLp_one_iff_integrable.2 hdi).congr_norm
        (hu.continuous_iteratedFDeriv le_rfl |>.aestronglyMeasurable)
        (.of_forall fun x => (norm_iteratedFDeriv_one u).symm)
  obtain ⟨g, hg, -, hlim⟩ := exists_contDiff_hasCompactSupport_approximation (μ := μ)
    ENNReal.one_ne_top (m := 1) hu 1 le_rfl hmem
  have hval : Tendsto (fun n => eLpNorm (g n - u) 1 μ) atTop (𝓝 0) :=
    (hlim 0 zero_le_one).congr fun n => eLpNorm_congr_norm_ae
      (((hg n).1.continuous_iteratedFDeriv (by simp)).sub
        (hu.continuous_iteratedFDeriv (by simp))).aestronglyMeasurable
      ((hg n).1.continuous.sub hu.continuous).aestronglyMeasurable
      (.of_forall fun x => by
        simp only [iteratedFDeriv_zero_eq_comp, Pi.sub_apply, Function.comp_apply, ← map_sub,
          LinearIsometryEquiv.norm_map])
  set ε := fun n => eLpNorm (iteratedFDeriv ℝ 1 (g n) - iteratedFDeriv ℝ 1 u) 1 μ
  have hderiv (n : ℕ) : eLpNorm (fderiv ℝ (g n)) 1 μ ≤ eLpNorm (fderiv ℝ u) 1 μ + ε n := by
    rw [eLpNorm_congr_norm_ae ((hg n).1.continuous_fderiv one_ne_zero).aestronglyMeasurable
        ((hg n).1.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
        (.of_forall fun x => (norm_iteratedFDeriv_one _).symm),
      eLpNorm_congr_norm_ae hdu (hu.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
        (.of_forall fun x => (norm_iteratedFDeriv_one _).symm), add_comm]
    simpa using eLpNorm_add_le (μ := μ)
      (f := iteratedFDeriv ℝ 1 (g n) - iteratedFDeriv ℝ 1 u) (g := iteratedFDeriv ℝ 1 u) le_rfl
  exact ⟨g, ε, fun n => (hg n).1, fun n => (hg n).2, hval, hlim 1 le_rfl, hderiv⟩

end TauCeti
