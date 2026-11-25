/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Analysis.Asymptotics.ExpGrowth

/-!
# The Lipschitz bound for topological entropy

Let `T` be a `K`-Lipschitz map of a pseudo-emetric space `X` whose covering numbers satisfy
`N(ε) ≤ C ε^(-D)` for `ε ∈ (0, 1]` (Mathlib's `Metric.coveringNumber`). Then
`coverEntropy T univ ≤ D * max 0 (log K)` (`TauCeti.coverEntropy_le_of_lipschitzWith`); in
particular the entropy is finite.

With `L = max 1 K`, two points at distance at most `ε / L^n` stay within `ε` of each other for `n`
steps of `T`, so an `ε / L^n`-cover of `X` is a dynamical cover at scale `ε` and time `n`. It has
at most `C (L^n / ε)^D = C ε^(-D) (L^D)^n` points, whose exponential growth rate is `D log L`.

## Main results

* `TauCeti.coverEntropy_le_mul_log_of_lipschitzWith`: the bound `D * log (max 1 K)`.
* `TauCeti.coverEntropy_le_of_lipschitzWith`: the bound `D * max 0 (log K)`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth Metric
open scoped Uniformity ENNReal NNReal

variable {X : Type*} [PseudoEMetricSpace X] {T : X → X} {K C : ℝ≥0} {D : ℝ}

/-- At scale `ε ∈ (0, 1]` and time `n`, the minimal dynamical covers of a `K`-Lipschitz map are
bounded by `C ε^(-D) (max 1 K ^ D)^n`. -/
private lemma coverMincard_le_of_lipschitzWith (hT : LipschitzWith K T)
    (hN : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε (univ : Set X) : ℝ≥0∞) ≤ ((C * ε⁻¹ ^ D : ℝ≥0) : ℝ≥0∞))
    {ε : ℝ≥0} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) :
    (coverMincard T univ {p | edist p.1 p.2 ≤ ε} n : ℝ≥0∞) ≤
      ((C * ε⁻¹ ^ D : ℝ≥0) : ℝ≥0∞) * (((max 1 K ^ D : ℝ≥0)) : ℝ≥0∞) ^ n := by
  classical
  set L : ℝ≥0 := max 1 K
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLn : 0 < L ^ n := pow_pos (zero_lt_one.trans_le hL1) n
  set ε' : ℝ≥0 := ε / L ^ n
  have hε'0 : 0 < ε' := div_pos hε0 hLn
  have hε'1 : ε' ≤ 1 := (div_le_self (by positivity) (one_le_pow₀ hL1)).trans hε1
  have hbound := hN ε' hε'0 hε'1
  have hfin : coveringNumber ε' (univ : Set X) ≠ ⊤ := by
    intro h
    have := ne_top_of_le_ne_top ENNReal.coe_ne_top hbound
    simp [h] at this
  obtain ⟨S, -, hSfin, hScov, hScard⟩ := exists_set_encard_eq_coveringNumber hfin
  have hdyn : IsDynCoverOf T univ {p | edist p.1 p.2 ≤ ε} n hSfin.toFinset := by
    intro x _
    obtain ⟨y, hy, hxy⟩ := hScov (mem_univ x)
    refine ⟨y, by simpa using hy, mem_dynEntourage.2 fun k hk ↦ ?_⟩
    calc edist (T^[k] x) (T^[k] y) ≤ (K ^ k : ℝ≥0) * edist x y := (hT.iterate k).edist_le_mul x y
      _ ≤ (L ^ n : ℝ≥0) * ε' := by
          have hKL : K ^ k ≤ L ^ n := (pow_le_pow_left₀ (by positivity) (le_max_right 1 K) k).trans
            (pow_le_pow_right₀ hL1 hk.le)
          exact mul_le_mul' (by exact_mod_cast hKL) hxy
      _ = ε := by
          rw [← ENNReal.coe_mul]
          exact congrArg _ (mul_div_cancel₀ ε hLn.ne')
  have hε' : ε'⁻¹ ^ D = ε⁻¹ ^ D * (L ^ D) ^ n := by
    rw [inv_div, div_eq_mul_inv, NNReal.mul_rpow, mul_comm, ← NNReal.rpow_natCast,
      ← NNReal.rpow_mul, mul_comm (n : ℝ) D, NNReal.rpow_mul, NNReal.rpow_natCast]
  calc (coverMincard T univ {p | edist p.1 p.2 ≤ ε} n : ℝ≥0∞)
      ≤ (hSfin.toFinset.card : ℝ≥0∞) := ENat.toENNReal_le.2 hdyn.coverMincard_le_card
    _ = (coveringNumber ε' (univ : Set X) : ℝ≥0∞) := by
        rw [← hScard, hSfin.encard_eq_coe_toFinset_card]; simp
    _ ≤ _ := hbound
    _ = _ := by rw [hε']; push_cast; ring

/-- The entourage-level form of the Lipschitz bound. -/
private lemma coverEntropyEntourage_le_of_lipschitzWith (hT : LipschitzWith K T)
    (hN : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε (univ : Set X) : ℝ≥0∞) ≤ ((C * ε⁻¹ ^ D : ℝ≥0) : ℝ≥0∞))
    {ε : ℝ≥0} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    coverEntropyEntourage T univ {p | edist p.1 p.2 ≤ ε} ≤
      ENNReal.log ((max 1 K ^ D : ℝ≥0) : ℝ≥0∞) :=
  (expGrowthSup_le_of_eventually_le ENNReal.coe_ne_top
    (Eventually.of_forall (coverMincard_le_of_lipschitzWith hT hN hε0 hε1))).trans_eq
    expGrowthSup_pow

/-- **Lipschitz bound.** If `T` is `K`-Lipschitz and the covering numbers of the space satisfy
`N(ε) ≤ C ε^(-D)` for `ε ∈ (0, 1]`, then the topological entropy of `T` is at most
`D * log (max 1 K)`. -/
theorem coverEntropy_le_mul_log_of_lipschitzWith (hT : LipschitzWith K T)
    (hN : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε (univ : Set X) : ℝ≥0∞) ≤ ((C * ε⁻¹ ^ D : ℝ≥0) : ℝ≥0∞)) :
    coverEntropy T univ ≤ ((D * Real.log (max 1 K) : ℝ) : EReal) := by
  have hL : (0 : ℝ) < (max 1 K : ℝ≥0) := zero_lt_one.trans_le (by exact_mod_cast le_max_left 1 K)
  have hlog : ENNReal.log ((max 1 K ^ D : ℝ≥0) : ℝ≥0∞) =
      ((D * Real.log (max 1 K) : ℝ) : EReal) := by
    rw [ENNReal.log_pos_real (by simp) ENNReal.coe_ne_top]
    simp only [ENNReal.coe_toReal, NNReal.coe_rpow]
    rw [Real.log_rpow hL, NNReal.coe_max, NNReal.coe_one]
  refine iSup₂_le fun U hU ↦ ?_
  obtain ⟨r, hr, hrU⟩ := mem_uniformity_edist.1 hU
  obtain ⟨ε, hε0, hεr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr
  set ε₁ := min ε 1
  have hε₁ : 0 < ε₁ := lt_min (by exact_mod_cast hε0) zero_lt_one
  have hsub : {p : X × X | edist p.1 p.2 ≤ ε₁} ⊆ U := fun p hp ↦
    hrU (hp.trans_lt ((ENNReal.coe_le_coe.2 (min_le_left _ _)).trans_lt hεr))
  exact (coverEntropyEntourage_antitone T univ hsub).trans <|
    (coverEntropyEntourage_le_of_lipschitzWith hT hN hε₁ (min_le_right _ _)).trans_eq hlog

/-- `log (max 1 K) = max 0 (log K)` for `K ≥ 0`. -/
private lemma log_max_one (K : ℝ≥0) : Real.log (max 1 (K : ℝ)) = max 0 (Real.log K) := by
  rcases le_total (K : ℝ) 1 with h | h
  · rw [max_eq_left h, Real.log_one]
    exact (max_eq_left (Real.log_nonpos K.coe_nonneg h)).symm
  · rw [max_eq_right h, max_eq_right (Real.log_nonneg h)]

/-- **Lipschitz bound.** If `T` is `K`-Lipschitz and the covering numbers of the space satisfy
`N(ε) ≤ C ε^(-D)` for `ε ∈ (0, 1]`, then `coverEntropy T univ ≤ D * max 0 (log K)`; in particular
the topological entropy is finite. -/
theorem coverEntropy_le_of_lipschitzWith (hT : LipschitzWith K T)
    (hN : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε (univ : Set X) : ℝ≥0∞) ≤ ((C * ε⁻¹ ^ D : ℝ≥0) : ℝ≥0∞)) :
    coverEntropy T univ ≤ ((D * max 0 (Real.log K) : ℝ) : EReal) := by
  rw [← log_max_one]
  exact coverEntropy_le_mul_log_of_lipschitzWith hT hN

end TauCeti
