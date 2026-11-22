/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LowPass
public import TauCeti.MeasureTheory.Function.Lp.One
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The constant function `1` in Besov spaces

The constant function `1` belongs to `B^s_{∞,q}` for every `s : ℝ` and `1 ≤ q ≤ ∞`, with
underlying tempered distribution `(volume : Measure E).toTemperedDistribution`
(`TemperedDistribution.memBesov_toTemperedDistribution_volume`), zeroth Littlewood–Paley block
`1 ∈ L^∞`, vanishing higher blocks (`TauCeti.BesovSpace.block_eq_ite_of_toDistr_eq_volume`), and
Besov norm `1` (`NormOneClass (TauCeti.BesovSpace ℂ φ s ∞ q)`). This module collects the `One` and
`NormOneClass` instances along with their compatibility lemmas for `lowPass`, `inclusion`,
`inclusionOfLT`, `bumpEquiv`, `ofLpCLM`, and `toLpCLM`.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {q : ℝ≥0∞}

/-- The constant function `1` as an element of `B^s_{∞,q}`: its tempered distribution is Lebesgue
measure, its zeroth Littlewood–Paley block is `1 ∈ L∞`, and every higher block vanishes. -/
instance : One (BesovSpace ℂ φ s ∞ q) where
  one := ⟨(volume : Measure E).toTemperedDistribution, lp.single q 0 1, fun j ↦ by
    rcases j with _ | j
    · simp
    · rw [lp.single_apply_ne _ _ _ (Nat.succ_ne_zero j)]
      simp⟩

@[simp] theorem toDistr_one :
    (1 : BesovSpace ℂ φ s ∞ q).toDistr = (volume : Measure E).toTemperedDistribution := rfl

@[simp] theorem weightedBlocks_one :
    (1 : BesovSpace ℂ φ s ∞ q).weightedBlocks = lp.single q 0 1 := rfl

/-- **The constant `1` lies in every Hölder–Zygmund space.** As a tempered distribution, `1` is
the volume, which lies in `B^s_{∞,q}` for every `s` and `q`. -/
theorem _root_.TemperedDistribution.memBesov_toTemperedDistribution_volume (s : ℝ)
    (q : ℝ≥0∞) : (volume : Measure E).toTemperedDistribution.MemBesov φ s ∞ q :=
  memBesov_of_littlewoodPaleyBlock_eq_ite (m := 0) (p := ∞)
    (f := 1) (fun k ↦ by
      rw [littlewoodPaleyBlock_toTemperedDistribution_volume, Lp.toTemperedDistribution_one])

/-- **The blocks of the constant `1`.** If the tempered distribution of `u ∈ B^s_{∞,q}` is the
constant function `1`, then `Δ₀ u = 1` and `Δⱼ u = 0` for `j ≥ 1`. -/
theorem block_eq_ite_of_toDistr_eq_volume {u : BesovSpace ℂ φ s ∞ q}
    (hu : u.toDistr = (volume : Measure E).toTemperedDistribution) (k : ℕ) :
    u.block k = if k = 0 then 1 else 0 :=
  Lp.toTemperedDistribution_injective <| by
    simp only [coe_block, hu, littlewoodPaleyBlock_toTemperedDistribution_volume]
    split_ifs
    · rw [Lp.toTemperedDistribution_one]
    · simp

/-- The `j`-th Littlewood–Paley block of `1 ∈ B^s_{∞,q}` is `1` at `j = 0` and `0` for `j ≥ 1`. -/
theorem block_one (j : ℕ) : (1 : BesovSpace ℂ φ s ∞ q).block j = if j = 0 then 1 else 0 :=
  block_eq_ite_of_toDistr_eq_volume toDistr_one j

@[simp] theorem block_one_zero : (1 : BesovSpace ℂ φ s ∞ q).block 0 = 1 := by simp [block_one]

@[simp] theorem block_one_succ (j : ℕ) : (1 : BesovSpace ℂ φ s ∞ q).block (j + 1) = 0 := by
  simp [block_one]

/-- For every `m ≥ 1`, the low-frequency cut-off `S_m 1` of `1 ∈ B^s_{∞,q}` equals `1 ∈ L^∞`. -/
@[simp] theorem lowPass_one_succ (m : ℕ) : (1 : BesovSpace ℂ φ s ∞ q).lowPass (m + 1) = 1 := by
  induction m with
  | zero => rw [lowPass_succ, lowPass_zero_right, block_one_zero, zero_add]
  | succ m ih => rw [lowPass_succ, ih, block_one_succ, add_zero]

/-- The low-frequency cut-off `S_m 1` of `1 ∈ B^s_{∞,q}` is `0` at `m = 0` and `1` for `m ≥ 1`. -/
theorem lowPass_one (m : ℕ) : (1 : BesovSpace ℂ φ s ∞ q).lowPass m = if m = 0 then 0 else 1 := by
  rcases m with _ | m <;> simp

/-- The Besov norm of `1 ∈ B^s_{∞,q}` is `1`. -/
instance [Fact (1 ≤ q)] : NormOneClass (BesovSpace ℂ φ s ∞ q) where
  norm_one := by
    rw [← norm_weightedBlocks, weightedBlocks_one, lp.norm_single (zero_lt_one.trans_le Fact.out),
      Lp.norm_one_of_ne_zero (NeZero.ne (volume : Measure E)), norm_one]

@[simp] theorem inclusion_one {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ q')]
    (hs : s' ≤ s) (hq : q ≤ q') : inclusion ℂ φ ∞ hs hq 1 = 1 := ext (by simp)

@[simp] theorem inclusionOfLT_one {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ q')]
    (hs : s' < s) : inclusionOfLT ℂ φ ∞ q q' hs 1 = 1 := ext (by simp)

@[simp] theorem bumpEquiv_one [Fact (1 ≤ q)] (φ' : ContDiffBump (0 : E)) :
    bumpEquiv ℂ φ φ' s ∞ q 1 = 1 := ext (by simp)

@[simp] theorem ofLpCLM_one : ofLpCLM ℂ φ ∞ 1 = 1 := ext (by simp)

@[simp] theorem toLpCLM_one [Fact (1 ≤ q)] (hs : 0 < s) : toLpCLM ℂ φ ∞ q hs 1 = 1 :=
  Lp.toTemperedDistribution_injective (by simp)

end TauCeti.BesovSpace
