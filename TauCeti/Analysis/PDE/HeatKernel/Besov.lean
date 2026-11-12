/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
public import TauCeti.Analysis.PDE.HeatKernel.TemperedDistribution
import TauCeti.Analysis.PDE.HeatKernel.FrequencyLocalized
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# The heat semigroup on Besov spaces

Let `B^s_{p,q}` be the inhomogeneous Besov space built from the Littlewood–Paley blocks `Δⱼ` of a
bump function `φ` (`TauCeti.BesovSpace`), and let `e^{tΔ}` be the heat semigroup on tempered
distributions (`TemperedDistribution.heatSemigroup`). This file proves that `e^{tΔ}` acts on every
`B^s_{p,q}`, `1 ≤ p, q ≤ ∞`, by contractions, and that for `t > 0` it gains any amount of
smoothness: for `σ ≥ 0` there is a constant `C`, depending only on `φ`, `σ` and the dimension,
such that

`‖e^{tΔ} u‖_{B^{s + 2σ}_{p,q}} ≤ C t^{-σ} ‖u‖_{B^s_{p,q}}` for `0 < t ≤ 1`

(`TauCeti.BesovSpace.exists_toDistr_eq_heatSemigroup_and_norm_le_rpow_neg`). For `p = q = ∞` this
is the smoothing estimate `‖e^{tΔ} u‖_{𝒞^{s + 2σ}} ≤ C t^{-σ} ‖u‖_{𝒞^s}` on the Hölder–Zygmund
scale. For `σ > 0` the restriction `t ≤ 1` cannot be dropped: the constant `1` lies in every
`𝒞^s` and is fixed by `e^{tΔ}`, so its norm does not tend to `0` as `t → ∞`, while `t^{-σ}` does.
For all `t > 0` the bound holds
with `max 1 (t^{-σ})` in place of `t^{-σ}`
(`TauCeti.BesovSpace.exists_toDistr_eq_heatSemigroup_and_norm_le`).

## The argument

The heat semigroup commutes with the blocks, so `Δⱼ e^{tΔ} u = e^{tΔ} Δⱼ u`, and the block `Δⱼ u` of
an element of `B^s_{p,q}` is an `Lᵖ` function. On `Lᵖ` the heat semigroup is a contraction
(`TemperedDistribution.exists_heatSemigroup_eq_and_norm_le`), which gives the contraction on
`B^s_{p,q}`. For `j ≥ 1` the frequencies of `Δⱼ u` lie in an annulus of size `2^j`, so `e^{tΔ}`
agrees on it with the multiplier by the Schwartz symbol `χ (2^{1-j} ξ) exp(-4π² t ‖ξ‖²)`,
where `χ` is a cutoff equal to one on that annulus at unit scale and
vanishing near the origin. The kernel of that multiplier has `L¹` norm `O(exp(-c 4^j t))`
(`TauCeti.exists_integral_norm_fourierInv_mul_exp_le`), so by Young's inequality
`‖Δⱼ e^{tΔ} u‖_p ≤ C exp(-c 4^j t) ‖Δⱼ u‖_p`
(`TauCeti.exists_heatSemigroup_littlewoodPaleyBlock_succ_eq_and_norm_le`). Finally
`2^{2σj} exp(-c 4^j t) = t^{-σ} x^σ exp(-c x)` with `x = 4^j t`, and `x^σ exp(-c x)` is bounded on
`x ≥ 0` (`TauCeti.exists_rpow_mul_exp_neg_mul_le`).

## Main declarations

* `TauCeti.BesovSpace.heatSemigroup`: `e^{tΔ}` as a contraction of `B^s_{p,q}`, with
  `TauCeti.BesovSpace.heatSemigroup_zero` and the semigroup law
  `TauCeti.BesovSpace.heatSemigroup_heatSemigroup_apply`.
* `TauCeti.BesovSpace.exists_toDistr_eq_heatSemigroup_and_norm_le_rpow_neg`: the smoothing
  estimate `B^s_{p,q} → B^{s + 2σ}_{p,q}` with norm `O(t^{-σ})` for `0 < t ≤ 1`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.4 (the heat flow on frequency-localized functions) and Section 2.7.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory Metric Real Set Filter FourierTransform
open scoped ContDiff ENNReal NNReal SchwartzMap Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TauCeti

open TemperedDistribution

/-- **The gain of the heat flow on the weights.** For `σ ≥ 0` and `c > 0` there is `A` with
`(4^j)^σ exp(-c (4^j - 1) t) ≤ A max 1 (t^{-σ})` for every `j` and every `t > 0`. -/
private theorem exists_rpow_mul_exp_le {σ c : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c) :
    ∃ A, 0 ≤ A ∧ ∀ (j : ℕ) {t : ℝ}, 0 < t →
      ((4 : ℝ) ^ j) ^ σ * rexp (-(c * ((4 ^ j - 1) * t))) ≤ A * max 1 (t ^ (-σ)) := by
  obtain ⟨M, hM0, hM⟩ := exists_rpow_mul_exp_neg_mul_le hσ hc
  refine ⟨rexp c * M, by positivity, fun j t ht ↦ ?_⟩
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  rcases le_total t 1 with h1 | h1
  · -- For `t ≤ 1`, write `(4^j)^σ = (4^j t)^σ t^{-σ}` and use the bound at `x = 4^j t`.
    have hx : ((4 : ℝ) ^ j) ^ σ = (4 ^ j * t) ^ σ * t ^ (-σ) := by
      rw [mul_rpow (by positivity) ht.le, mul_assoc, ← rpow_add ht, add_neg_cancel, rpow_zero,
        mul_one]
    have he : -(c * ((4 ^ j - 1) * t)) = c * t + -(c * (4 ^ j * t)) := by ring
    calc ((4 : ℝ) ^ j) ^ σ * rexp (-(c * ((4 ^ j - 1) * t)))
        = rexp (c * t) * ((4 ^ j * t) ^ σ * rexp (-(c * (4 ^ j * t)))) * t ^ (-σ) := by
          rw [hx, he, exp_add]
          ring
      _ ≤ rexp c * M * t ^ (-σ) := by
          have hct : rexp (c * t) ≤ rexp c := exp_le_exp.2 (by nlinarith)
          have hMx := hM (4 ^ j * t) (by positivity)
          gcongr
      _ ≤ rexp c * M * max 1 (t ^ (-σ)) := by gcongr; exact le_max_right _ _
  · -- For `t ≥ 1` the exponential only decreases in `t`, so use the bound at `x = 4^j`.
    have he : -(c * ((4 ^ j - 1) * 1)) = c + -(c * 4 ^ j) := by ring
    calc ((4 : ℝ) ^ j) ^ σ * rexp (-(c * ((4 ^ j - 1) * t)))
        ≤ ((4 : ℝ) ^ j) ^ σ * rexp (-(c * ((4 ^ j - 1) * 1))) := by
          gcongr
      _ = rexp c * (((4 : ℝ) ^ j) ^ σ * rexp (-(c * 4 ^ j))) := by
          rw [he, exp_add]
          ring
      _ ≤ rexp c * M := by gcongr; exact hM _ (by positivity)
      _ ≤ rexp c * M * max 1 (t ^ (-σ)) := le_mul_of_one_le_right (by positivity)
          (le_max_left _ _)

namespace BesovSpace

variable [CompleteSpace F] {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The heat flow of an element `u` of `B^s_{p,q}`: if `C`, `c` are the constants of
`exists_littlewoodPaleyBlock_heatSemigroup_eq_and_norm_le` and the weights `w j ≥ 0` satisfy
`w j * C exp(-c (4^j - 1) t) ≤ B 2^{js}`, then `e^{tΔ} u` has `Lᵖ` blocks with weighted norms
`w j ‖Δⱼ e^{tΔ} u‖_p ≤ B 2^{js} ‖Δⱼ u‖_p`. -/
private theorem exists_block_heatSemigroup {C c : ℝ}
    (hCc : ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (t : ℝ≥0) (u : 𝓢'(E, F))
      (f : Lp F p (volume : Measure E)), littlewoodPaleyBlock F φ j u = f →
      ∃ g : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (TemperedDistribution.heatSemigroup E F t u) = g ∧
          ‖g‖ ≤ C * rexp (-(c * ((4 ^ j - 1) * t))) * ‖f‖)
    (t : ℝ≥0) {w : ℕ → ℝ} {B : ℝ} (hw : ∀ j, 0 ≤ w j)
    (hwB : ∀ j, w j * (C * rexp (-(c * ((4 ^ j - 1) * t)))) ≤ B * 2 ^ (s * j))
    (u : BesovSpace F φ s p q) :
    ∃ g : ℕ → Lp F p (volume : Measure E),
      (∀ j, littlewoodPaleyBlock F φ j (TemperedDistribution.heatSemigroup E F t u.toDistr) =
        g j) ∧
        ∀ j, w j * ‖g j‖ ≤ B * (2 ^ (s * j) * ‖u.block j‖) := by
  choose g hg hgn using fun j ↦ hCc j t u.toDistr (u.block j) (coe_block u j).symm
  refine ⟨g, hg, fun j ↦ ?_⟩
  calc w j * ‖g j‖ ≤ w j * (C * rexp (-(c * ((4 ^ j - 1) * t))) * ‖u.block j‖) :=
        mul_le_mul_of_nonneg_left (hgn j) (hw j)
    _ = w j * (C * rexp (-(c * ((4 ^ j - 1) * t)))) * ‖u.block j‖ := by ring
    _ ≤ B * 2 ^ (s * j) * ‖u.block j‖ := mul_le_mul_of_nonneg_right (hwB j) (norm_nonneg _)
    _ = B * (2 ^ (s * j) * ‖u.block j‖) := by ring

/-- The heat flow of an element of `B^s_{p,q}` lies in `B^{s'}_{p,q}` with norm at most `B ‖u‖`,
once the weights satisfy `2^{js'} ‖Δⱼ e^{tΔ} u‖_p ≤ B 2^{js} ‖Δⱼ u‖_p`. -/
private theorem exists_toDistr_eq_heatSemigroup_of_block [Fact (1 ≤ q)] {s' B : ℝ} (hB : 0 ≤ B)
    (t : ℝ≥0) (u : BesovSpace F φ s p q) (g : ℕ → Lp F p (volume : Measure E))
    (hg : ∀ j,
      littlewoodPaleyBlock F φ j (TemperedDistribution.heatSemigroup E F t u.toDistr) = g j)
    (hgn : ∀ j : ℕ, 2 ^ (s' * j) * ‖g j‖ ≤ B * (2 ^ (s * j) * ‖u.block j‖)) :
    ∃ v : BesovSpace F φ s' p q,
      v.toDistr = TemperedDistribution.heatSemigroup E F t u.toDistr ∧ ‖v‖ ≤ B * ‖u‖ := by
  have hmem : (TemperedDistribution.heatSemigroup E F t u.toDistr).MemBesov φ s' p q := by
    obtain ⟨f, hf, hfm⟩ := memBesov_iff.1 u.memBesov_toDistr
    have hfu : ∀ j, f j = u.block j := fun j ↦ LinearMap.ker_eq_bot.1
      Lp.ker_toTemperedDistributionCLM_eq_bot (by simp [← hf j])
    refine memBesov_iff.2 ⟨g, hg, (hfm.const_mul B).mono fun j ↦ ?_⟩
    rw [Real.norm_of_nonneg (by positivity), hfu]
    exact hgn j
  refine ⟨hmem.toBesovSpace, hmem.toDistr_toBesovSpace, ?_⟩
  have hj (j : ℕ) : hmem.toBesovSpace.block j = g j := LinearMap.ker_eq_bot.1
    Lp.ker_toTemperedDistributionCLM_eq_bot (by simp [hg j])
  rw [← norm_weightedBlocks, ← norm_weightedBlocks]
  calc ‖hmem.toBesovSpace.weightedBlocks‖ ≤ ‖(B : ℂ) • u.weightedBlocks‖ :=
        lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ by
          rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_of_nonneg hB,
            norm_weightedBlocks_apply, norm_weightedBlocks_apply, hj]
          exact hgn j
    _ = B * ‖u.weightedBlocks‖ := by rw [norm_smul, Complex.norm_of_nonneg hB]

/-- **The heat semigroup on a Besov space gains smoothness.** For `σ ≥ 0` there is a constant
`C`, depending only on `φ`, `σ` and `E`, such that for every `1 ≤ p, q ≤ ∞`, every `s`, every
`t > 0` and every `u ∈ B^s_{p,q}`, the heat flow `e^{tΔ} u` lies in `B^{s + 2σ}_{p,q}` with

`‖e^{tΔ} u‖_{B^{s + 2σ}_{p,q}} ≤ C max 1 (t^{-σ}) ‖u‖_{B^s_{p,q}}`. -/
theorem exists_toDistr_eq_heatSemigroup_and_norm_le {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C, 0 ≤ C ∧ ∀ {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (t : ℝ≥0), t ≠ 0 →
      ∀ u : BesovSpace F φ s p q, ∃ v : BesovSpace F φ (s + 2 * σ) p q,
        v.toDistr = TemperedDistribution.heatSemigroup E F t u.toDistr ∧
          ‖v‖ ≤ C * max 1 ((t : ℝ) ^ (-σ)) * ‖u‖ := by
  obtain ⟨C, c, hC1, hc, hCc⟩ :=
    exists_littlewoodPaleyBlock_heatSemigroup_eq_and_norm_le (F := F) φ
  obtain ⟨A, hA0, hA⟩ := exists_rpow_mul_exp_le hσ hc
  refine ⟨C * A, mul_nonneg (zero_le_one.trans hC1) hA0, fun {s p q} _ _ t ht u ↦ ?_⟩
  have ht' : (0 : ℝ) < t := by positivity
  have hwB (j : ℕ) : 2 ^ ((s + 2 * σ) * j) * (C * rexp (-(c * ((4 ^ j - 1) * t)))) ≤
      C * A * max 1 ((t : ℝ) ^ (-σ)) * 2 ^ (s * j) := by
    -- Raising the order from `s` to `s + 2σ` multiplies the weight `2^{js}` by `(4^j)^σ`.
    have h4 : (4 : ℝ) ^ j = 2 ^ (2 * j : ℝ) := by
      rw [rpow_mul zero_le_two, rpow_natCast, rpow_two]
      norm_num
    have hw : (2 : ℝ) ^ ((s + 2 * σ) * j) = ((4 : ℝ) ^ j) ^ σ * 2 ^ (s * j) := by
      rw [h4, ← rpow_mul zero_le_two, ← rpow_add two_pos]
      ring_nf
    rw [hw]
    calc ((4 : ℝ) ^ j) ^ σ * 2 ^ (s * j) * (C * rexp (-(c * ((4 ^ j - 1) * t))))
        = C * (((4 : ℝ) ^ j) ^ σ * rexp (-(c * ((4 ^ j - 1) * t)))) * 2 ^ (s * j) := by ring
      _ ≤ C * (A * max 1 ((t : ℝ) ^ (-σ))) * 2 ^ (s * j) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hA j ht') (zero_le_one.trans hC1)) (by positivity)
      _ = C * A * max 1 ((t : ℝ) ^ (-σ)) * 2 ^ (s * j) := by ring
  obtain ⟨g, hg, hgn⟩ := exists_block_heatSemigroup hCc t (fun j ↦ by positivity) hwB u
  exact exists_toDistr_eq_heatSemigroup_of_block (by positivity) t u g hg hgn

/-- **The smoothing estimate of the heat semigroup on Besov spaces.** For `σ ≥ 0` there is a
constant `C`, depending only on `φ`, `σ` and `E`, such that for every `1 ≤ p, q ≤ ∞`, every `s`,
every `0 < t ≤ 1` and every `u ∈ B^s_{p,q}`,

`‖e^{tΔ} u‖_{B^{s + 2σ}_{p,q}} ≤ C t^{-σ} ‖u‖_{B^s_{p,q}}`.

For `p = q = ∞` this is the smoothing estimate of the heat semigroup on the Hölder–Zygmund scale
`𝒞^s = B^s_{∞,∞}`. -/
theorem exists_toDistr_eq_heatSemigroup_and_norm_le_rpow_neg {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C, 0 ≤ C ∧ ∀ {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (t : ℝ≥0), t ≠ 0 →
      t ≤ 1 → ∀ u : BesovSpace F φ s p q, ∃ v : BesovSpace F φ (s + 2 * σ) p q,
        v.toDistr = TemperedDistribution.heatSemigroup E F t u.toDistr ∧
          ‖v‖ ≤ C * (t : ℝ) ^ (-σ) * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_toDistr_eq_heatSemigroup_and_norm_le (F := F) (φ := φ) hσ
  refine ⟨C, hC0, fun {s p q} _ _ t ht ht1 u ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := hC t ht u
  refine ⟨v, hv, hvn.trans_eq ?_⟩
  rw [max_eq_right (one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity)
    (by exact_mod_cast ht1) (neg_nonpos.2 hσ))]

variable [Fact (1 ≤ q)]

/-- The heat flow of an element of `B^s_{p,q}` lies in `B^s_{p,q}`, with norm at most `‖u‖`:
each block is contracted. -/
private theorem exists_toDistr_eq_heatSemigroup_and_norm_le_self (t : ℝ≥0)
    (u : BesovSpace F φ s p q) :
    ∃ v : BesovSpace F φ s p q,
      v.toDistr = TemperedDistribution.heatSemigroup E F t u.toDistr ∧ ‖v‖ ≤ ‖u‖ := by
  choose g hg hgn using fun j ↦ exists_heatSemigroup_eq_and_norm_le t (u.block j)
  obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_heatSemigroup_of_block (s' := s) zero_le_one t u g
    (fun j ↦ by rw [littlewoodPaleyBlock_heatSemigroup_comm, ← coe_block, hg j])
    (fun j ↦ by rw [one_mul]; exact mul_le_mul_of_nonneg_left (hgn j) (by positivity))
  exact ⟨v, hv, hvn.trans_eq (one_mul _)⟩

variable (F φ s p q) in
/-- **The heat semigroup on a Besov space.** For `t ≥ 0`, `e^{tΔ}` maps `B^s_{p,q}` to itself with
norm at most `1`. -/
def heatSemigroup (t : ℝ≥0) : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s p q :=
  LinearMap.mkContinuous
    { toFun u := (exists_toDistr_eq_heatSemigroup_and_norm_le_self t u).choose
      map_add' u v := ext <| by
        have h (w : BesovSpace F φ s p q) :=
          (exists_toDistr_eq_heatSemigroup_and_norm_le_self t w).choose_spec.1
        exact (h (u + v)).trans (by simp only [h, toDistr_add, map_add])
      map_smul' c u := ext <| by
        have h (w : BesovSpace F φ s p q) :=
          (exists_toDistr_eq_heatSemigroup_and_norm_le_self t w).choose_spec.1
        exact (h (c • u)).trans (by simp only [h, toDistr_smul, map_smul, RingHom.id_apply]) }
    1 fun u ↦ ((exists_toDistr_eq_heatSemigroup_and_norm_le_self t u).choose_spec.2).trans_eq
      (one_mul _).symm

@[simp]
theorem toDistr_heatSemigroup (t : ℝ≥0) (u : BesovSpace F φ s p q) :
    (heatSemigroup F φ s p q t u).toDistr =
      TemperedDistribution.heatSemigroup E F t u.toDistr :=
  (exists_toDistr_eq_heatSemigroup_and_norm_le_self t u).choose_spec.1

/-- The blocks of the heat flow of `u` are the heat flows of the blocks of `u`. -/
theorem coe_block_heatSemigroup (t : ℝ≥0) (u : BesovSpace F φ s p q) (j : ℕ) :
    ((heatSemigroup F φ s p q t u).block j : 𝓢'(E, F)) =
      TemperedDistribution.heatSemigroup E F t (u.block j) := by
  rw [coe_block, coe_block, toDistr_heatSemigroup, littlewoodPaleyBlock_heatSemigroup_comm]

/-- The heat semigroup is a contraction of `B^s_{p,q}`. -/
theorem norm_heatSemigroup_le (t : ℝ≥0) (u : BesovSpace F φ s p q) :
    ‖heatSemigroup F φ s p q t u‖ ≤ ‖u‖ :=
  (exists_toDistr_eq_heatSemigroup_and_norm_le_self t u).choose_spec.2

variable (F φ s p q) in
/-- At time `0` the heat semigroup on `B^s_{p,q}` is the identity. -/
@[simp]
theorem heatSemigroup_zero :
    heatSemigroup F φ s p q 0 = ContinuousLinearMap.id ℂ _ := by
  ext1 u
  exact ext (by simp)

/-- **The semigroup law** `e^{tΔ} e^{sΔ} = e^{(s+t)Δ}` on `B^s_{p,q}`. -/
@[simp]
theorem heatSemigroup_heatSemigroup_apply (t₁ t₂ : ℝ≥0) (u : BesovSpace F φ s p q) :
    heatSemigroup F φ s p q t₂ (heatSemigroup F φ s p q t₁ u) =
      heatSemigroup F φ s p q (t₁ + t₂) u :=
  ext (by simp)

/-- The semigroup law `e^{tΔ} ∘ e^{sΔ} = e^{(s+t)Δ}` on `B^s_{p,q}` as an identity of
operators. -/
theorem heatSemigroup_compL_heatSemigroup (t₁ t₂ : ℝ≥0) :
    heatSemigroup F φ s p q t₂ ∘L heatSemigroup F φ s p q t₁ =
      heatSemigroup F φ s p q (t₁ + t₂) := by
  ext1 u
  exact heatSemigroup_heatSemigroup_apply t₁ t₂ u

end BesovSpace

end TauCeti
