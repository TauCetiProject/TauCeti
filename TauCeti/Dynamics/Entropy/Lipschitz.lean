/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Analysis.Asymptotics.ExpGrowth

/-!
# The Lipschitz bound for topological entropy

Let `T` be a self-map of a pseudo-emetric space `X`, and `F ⊆ X` a forward-invariant set on
which `T` is `K`-Lipschitz and whose covering numbers satisfy `N(ε) ≤ C ε^(-D)` for `ε ∈ (0, 1]`
(Mathlib's `Metric.coveringNumber`). Then `coverEntropy T F ≤ D * log⁺ K = D * max 0 (log K)`
(`TauCeti.coverEntropy_le_of_lipschitzOnWith`); in particular the entropy is not `⊤`.

With `L = max 1 K`, two points at distance at most `ε / L^n` stay within `ε` of each other for `n`
steps of `T`, so an `ε / L^n`-cover of `F` is a dynamical cover at scale `ε` and time `n`. It has
at most `C (L^n / ε)^D = C ε^(-D) (L^D)^n` points, whose exponential growth rate is
`D log L = D log⁺ K`.

## Main results

* `TauCeti.coverEntropy_le_of_lipschitzOnWith`: the bound `D * log⁺ K`.

## References

* A. Katok and B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Encyclopedia of Mathematics and its Applications 54, Cambridge University Press, 1995, §3.2
  (topological entropy; the bound for Lipschitz maps in terms of box dimension).
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth Metric
open scoped Uniformity ENNReal NNReal Real

variable {X : Type*} [PseudoEMetricSpace X] {T : X → X} {F : Set X} {K C : ℝ≥0} {D : ℝ}

/-- At scale `ε ∈ (0, 1]` and time `n`, the minimal dynamical covers of a forward-invariant set
`F` on which `T` is `K`-Lipschitz are bounded by `C ε^(-D) (max 1 K ^ D)^n`. -/
private lemma coverMincard_le_of_lipschitzOnWith (hT : LipschitzOnWith K T F) (hF : MapsTo T F F)
    (hN : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε F : ℝ≥0∞) ≤ ((C * ε⁻¹ ^ D : ℝ≥0) : ℝ≥0∞))
    {ε : ℝ≥0} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) :
    (coverMincard T F {p | edist p.1 p.2 ≤ ε} n : ℝ≥0∞) ≤
      ((C * ε⁻¹ ^ D : ℝ≥0) : ℝ≥0∞) * (((max 1 K ^ D : ℝ≥0)) : ℝ≥0∞) ^ n := by
  classical
  set L : ℝ≥0 := max 1 K
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLn : 0 < L ^ n := pow_pos (zero_lt_one.trans_le hL1) n
  set ε' : ℝ≥0 := ε / L ^ n
  have hε'0 : 0 < ε' := div_pos hε0 hLn
  have hε'1 : ε' ≤ 1 := (div_le_self (by positivity) (one_le_pow₀ hL1)).trans hε1
  have hbound := hN ε' hε'0 hε'1
  have hfin : coveringNumber ε' F ≠ ⊤ := by
    intro h
    have := ne_top_of_le_ne_top ENNReal.coe_ne_top hbound
    simp [h] at this
  obtain ⟨S, hSF, hSfin, hScov, hScard⟩ := exists_set_encard_eq_coveringNumber hfin
  have hdyn : IsDynCoverOf T F {p | edist p.1 p.2 ≤ ε} n hSfin.toFinset := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hScov hx
    refine ⟨y, by simpa using hy, mem_dynEntourage.2 fun k hk ↦ ?_⟩
    calc edist (T^[k] x) (T^[k] y) ≤ (K ^ k : ℝ≥0) * edist x y := by
          simpa only [Subtype.edist_eq, hF.coe_iterate_restrict] using
            ((hT.mapsToRestrict hF).iterate k).edist_le_mul ⟨x, hx⟩ ⟨y, hSF hy⟩
      _ ≤ (L ^ n : ℝ≥0) * ε' := by
          have hKL : K ^ k ≤ L ^ n := (pow_le_pow_left₀ (by positivity) (le_max_right 1 K) k).trans
            (pow_le_pow_right₀ hL1 hk.le)
          exact mul_le_mul' (by exact_mod_cast hKL) hxy
      _ = ε := by
          rw [← ENNReal.coe_mul]
          exact congrArg _ (mul_div_cancel₀ ε hLn.ne')
  have hε' : ε'⁻¹ ^ D = ε⁻¹ ^ D * (L ^ D) ^ n := by
    rw [inv_div, div_eq_inv_mul, NNReal.mul_rpow, ← NNReal.rpow_natCast_mul, mul_comm (n : ℝ) D,
      NNReal.rpow_mul_natCast]
  calc (coverMincard T F {p | edist p.1 p.2 ≤ ε} n : ℝ≥0∞)
      ≤ (hSfin.toFinset.card : ℝ≥0∞) := ENat.toENNReal_le.2 hdyn.coverMincard_le_card
    _ = (coveringNumber ε' F : ℝ≥0∞) := by
        rw [← hScard, hSfin.encard_eq_coe_toFinset_card]; simp
    _ ≤ _ := hbound
    _ = _ := by rw [hε']; push_cast; ring

/-- The entourage-level form of the Lipschitz bound. -/
private lemma coverEntropyEntourage_le_of_lipschitzOnWith (hT : LipschitzOnWith K T F)
    (hF : MapsTo T F F)
    (hN : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε F : ℝ≥0∞) ≤ ((C * ε⁻¹ ^ D : ℝ≥0) : ℝ≥0∞))
    {ε : ℝ≥0} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    coverEntropyEntourage T F {p | edist p.1 p.2 ≤ ε} ≤
      ENNReal.log ((max 1 K ^ D : ℝ≥0) : ℝ≥0∞) :=
  (expGrowthSup_le_of_eventually_le ENNReal.coe_ne_top
    (Eventually.of_forall (coverMincard_le_of_lipschitzOnWith hT hF hN hε0 hε1))).trans_eq
    expGrowthSup_pow

/-- **Lipschitz bound.** If `F` is forward-invariant under `T`, `T` is `K`-Lipschitz on `F`, and
the covering numbers of `F` satisfy `N(ε) ≤ C ε^(-D)` for `ε ∈ (0, 1]`, then
`coverEntropy T F ≤ D * log⁺ K`, where `log⁺ K = max 0 (log K)`; in particular the topological
entropy of `T` on `F` is not `⊤`. For a globally `K`-Lipschitz `T` and `F = univ`, use
`hT.lipschitzOnWith` and `mapsTo_univ`. -/
theorem coverEntropy_le_of_lipschitzOnWith (hT : LipschitzOnWith K T F) (hF : MapsTo T F F)
    (hN : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε F : ℝ≥0∞) ≤ ((C * ε⁻¹ ^ D : ℝ≥0) : ℝ≥0∞)) :
    coverEntropy T F ≤ ((D * log⁺ K : ℝ) : EReal) := by
  have hL : (0 : ℝ) < (max 1 K : ℝ≥0) := zero_lt_one.trans_le (by exact_mod_cast le_max_left 1 K)
  have hlog : ENNReal.log ((max 1 K ^ D : ℝ≥0) : ℝ≥0∞) = ((D * log⁺ K : ℝ) : EReal) := by
    rw [ENNReal.log_pos_real (by simp) ENNReal.coe_ne_top]
    simp only [ENNReal.coe_toReal, NNReal.coe_rpow]
    rw [Real.log_rpow hL, NNReal.coe_max, NNReal.coe_one, Real.posLog_eq_log_max_one K.coe_nonneg]
  refine iSup₂_le fun U hU ↦ ?_
  obtain ⟨r, hr, hrU⟩ := mem_uniformity_edist.1 hU
  obtain ⟨ε, hε0, hεr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr
  set ε₁ := min ε 1
  have hε₁ : 0 < ε₁ := lt_min (by exact_mod_cast hε0) zero_lt_one
  have hsub : {p : X × X | edist p.1 p.2 ≤ ε₁} ⊆ U := fun p hp ↦
    hrU (hp.trans_lt ((ENNReal.coe_le_coe.2 (min_le_left _ _)).trans_lt hεr))
  exact (coverEntropyEntourage_antitone T F hsub).trans <|
    (coverEntropyEntourage_le_of_lipschitzOnWith hT hF hN hε₁ (min_le_right _ _)).trans_eq hlog

end TauCeti
