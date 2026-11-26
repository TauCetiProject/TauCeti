/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Delta
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little
public import TauCeti.Analysis.Semigroups.Basic
public import TauCeti.Analysis.PDE.HeatKernel.TemperedDistribution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Group.Tannery
import TauCeti.Analysis.PDE.HeatKernel.FrequencyLocalized

/-!
# The heat semigroup on Besov spaces

Let `B^s_{p,q}` be the inhomogeneous Besov space built from the Littlewood–Paley blocks `Δⱼ` of a
bump function `φ` (`TauCeti.BesovSpace`), and let `e^{tΔ}` be the heat semigroup on tempered
distributions (`TemperedDistribution.heatSemigroup`). This file proves that `e^{tΔ}` acts on every
`B^s_{p,q}`, `1 ≤ p, q ≤ ∞`, by contractions, and that for `t > 0` it gains any amount of
smoothness: `e^{tΔ}` is a continuous linear map `B^s_{p,q} → B^{s'}_{p,q}` for every `s'`
(`TauCeti.BesovSpace.heatSemigroupOfNeZero`), and for `σ ≥ 0` there is a constant `C`, depending
only on `φ`, `σ`, `E` and `F`, such that

`‖e^{tΔ} u‖_{B^{s + 2σ}_{p,q}} ≤ C t^{-σ} ‖u‖_{B^s_{p,q}}` for `0 < t ≤ 1`

(`TauCeti.BesovSpace.exists_norm_heatSemigroupOfNeZero_le_rpow_neg`). For `p = q = ∞` this
is the smoothing estimate `‖e^{tΔ} u‖_{𝒞^{s + 2σ}} ≤ C t^{-σ} ‖u‖_{𝒞^s}` on the Hölder–Zygmund
scale. For `σ > 0` the restriction `t ≤ 1` cannot be dropped: the constant `1` lies in every
`𝒞^s` and is fixed by `e^{tΔ}`, so its norm does not tend to `0` as `t → ∞`, while `t^{-σ}` does.
For all `t > 0` the bound holds
with `max 1 (t^{-σ})` in place of `t^{-σ}`
(`TauCeti.BesovSpace.exists_norm_heatSemigroupOfNeZero_le`).

The heat semigroup is **strongly continuous** on `B^s_{p,q}` for `q < ∞`: `e^{tΔ} u → u` as
`t → 0` for every `u`, and every `1 ≤ p ≤ ∞` (`TauCeti.BesovSpace.tendsto_heatSemigroup`), so it
is a strongly continuous contraction semigroup there
(`TauCeti.BesovSpace.heatContractionSemigroup`). On `B^s_{p,∞}` it is strongly continuous at `u`
exactly when the weighted blocks vanish at high frequency, `2^{js} ‖Δⱼ u‖_p → 0`
(`TauCeti.BesovSpace.tendsto_heatSemigroup_iff`). This holds on the little Besov space
`b^s_{p,∞}`, the closure of the Schwartz functions, and for `p < ∞` it characterizes it; at
`p = ∞` this is the little Hölder–Zygmund space `c^s`, on which the heat semigroup is strongly
continuous although it is not on `𝒞^s`. For instance `e^{tΔ} δ₀` does not tend to `δ₀` in
`B^{-n/p'}_{p,∞}`, which is `𝒞^{-n}` at `p = ∞`
(`TauCeti.BesovSpace.not_tendsto_heatSemigroup_delta_zero`).

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

For strong continuity, the block `Δⱼ u` has frequencies in the ball of radius `2^j φ.rOut`, where
`e^{tΔ} - 1` is the multiplier by a Schwartz symbol whose kernel tends to `0` in `L¹`, so
`‖Δⱼ (e^{tΔ} u - u)‖_p ≤ cⱼ(t) ‖Δⱼ u‖_p` with `cⱼ(t) → 0`
(`TauCeti.exists_heatSemigroup_sub_eq_and_norm_le_of_isVanishingOn_fourier`). Each weighted
block of `e^{tΔ} u - u` is also at most twice that of `u`. For `q < ∞` dominated convergence in
the sum `∑ⱼ (2^{js} ‖Δⱼ (e^{tΔ} u - u)‖_p)^q` gives the convergence; for `q = ∞` the decay of the
weighted blocks of `u` controls the high blocks uniformly in `t`. Conversely, for `t > 0` the
heat flow `e^{tΔ} u` lies in `B^{s+1}_{p,∞} ⊆ B^s_{p,1}`, so its weighted blocks in
`B^s_{p,∞}` vanish at high frequency. Since this is a closed condition
(`TauCeti.BesovSpace.isClosed_setOf_tendsto_rpow_mul_norm_block`), it passes to the limit `u`.

## Main declarations

* `TauCeti.BesovSpace.heatSemigroup`: `e^{tΔ}` as a contraction of `B^s_{p,q}`, with
  `TauCeti.BesovSpace.heatSemigroup_zero` and the semigroup law
  `TauCeti.BesovSpace.heatSemigroup_heatSemigroup_apply`.
* `TemperedDistribution.MemBesov.heatSemigroup` and
  `TemperedDistribution.MemBesov.heatSemigroup_of_ne_zero`: `e^{tΔ}` preserves `B^s_{p,q}` and, for
  `t > 0`, maps it into every `B^{s'}_{p,q}`.
* `TauCeti.BesovSpace.heatSemigroupOfNeZero`: for `t > 0`, `e^{tΔ}` as a continuous linear map
  `B^s_{p,q} → B^{s'}_{p,q}`, with the uniform bounds
  `TauCeti.BesovSpace.exists_norm_heatSemigroupOfNeZero_le` and
  `TauCeti.BesovSpace.exists_norm_heatSemigroupOfNeZero_le_rpow_neg`, the smoothing estimate
  `B^s_{p,q} → B^{s + 2σ}_{p,q}` with norm `O(t^{-σ})` for `0 < t ≤ 1`.
* `TauCeti.BesovSpace.tendsto_heatSemigroup` and `TauCeti.BesovSpace.heatContractionSemigroup`:
  strong continuity on `B^s_{p,q}` for `q < ∞`.
* `TauCeti.BesovSpace.tendsto_heatSemigroup_iff`: strong continuity at `u ∈ B^s_{p,∞}` exactly
  when `2^{js} ‖Δⱼ u‖_p → 0`, with `TauCeti.BesovSpace.tendsto_heatSemigroup_of_mem_littleBesov`
  and, for `p < ∞`, `TauCeti.BesovSpace.tendsto_heatSemigroup_iff_mem_littleBesov`.
* `TauCeti.BesovSpace.not_tendsto_heatSemigroup_delta_zero`: no strong continuity at `δ₀` in
  `B^{-n/p'}_{p,∞}`.

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

namespace BesovSpace

variable [CompleteSpace F] {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The weighted heat flow on a block.** For `σ ≥ 0` there is `C ≥ 0`, depending only on `φ`,
`σ`, `E` and `F`, such that for `s' ≤ s + 2σ` and `t > 0`: if the block `Δⱼ u` of a tempered
distribution is an `Lᵖ` function `f`, then `Δⱼ e^{tΔ} u` is an `Lᵖ` function `g` with
`2^{js'} ‖g‖_p ≤ C max 1 (t^{-σ}) 2^{js} ‖f‖_p`. -/
private theorem exists_littlewoodPaleyBlock_heatSemigroup_eq_and_rpow_mul_norm_le {σ : ℝ}
    (hσ : 0 ≤ σ) (φ : ContDiffBump (0 : E)) :
    ∃ C, 0 ≤ C ∧ ∀ {s s' : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)], s' ≤ s + 2 * σ → ∀ t : ℝ≥0, t ≠ 0 →
      ∀ (j : ℕ) (u : 𝓢'(E, F)) (f : Lp F p (volume : Measure E)),
        littlewoodPaleyBlock F φ j u = f → ∃ g : Lp F p (volume : Measure E),
          littlewoodPaleyBlock F φ j (TemperedDistribution.heatSemigroup E F t u) = g ∧
            2 ^ (s' * j) * ‖g‖ ≤ C * max 1 ((t : ℝ) ^ (-σ)) * (2 ^ (s * j) * ‖f‖) := by
  obtain ⟨C, c, hC1, hc, hCc⟩ :=
    exists_littlewoodPaleyBlock_heatSemigroup_eq_and_norm_le (F := F) φ
  obtain ⟨A, hA0, hA⟩ := exists_two_rpow_mul_exp_neg_le hσ hc
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  refine ⟨C * A, mul_nonneg hC0 hA0, fun {s s' p} _ hs' t ht j u f hf ↦ ?_⟩
  obtain ⟨g, hg, hgn⟩ := hCc j t u f hf
  refine ⟨g, hg, ?_⟩
  calc 2 ^ (s' * j) * ‖g‖
      ≤ 2 ^ (s' * j) * (C * rexp (-(c * ((4 ^ j - 1) * t))) * ‖f‖) := by gcongr
    _ = C * (2 ^ (s' * j) * rexp (-(c * ((4 ^ j - 1) * t)))) * ‖f‖ := by ring
    _ ≤ C * (A * max 1 ((t : ℝ) ^ (-σ)) * 2 ^ (s * j)) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hA hs' j (NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht))) hC0) (norm_nonneg _)
    _ = C * A * max 1 ((t : ℝ) ^ (-σ)) * (2 ^ (s * j) * ‖f‖) := by ring

/-- **The heat flow preserves Besov membership.** If `u ∈ B^s_{p,q}`, then `e^{tΔ} u ∈ B^s_{p,q}`
for every `t ≥ 0`: each block is contracted. -/
theorem _root_.TemperedDistribution.MemBesov.heatSemigroup {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ s p q) (t : ℝ≥0) :
    (TemperedDistribution.heatSemigroup E F t u).MemBesov φ s p q := by
  obtain ⟨f, hf, hfm⟩ := memBesov_iff.1 hu
  choose g hg hgn using fun j ↦ exists_heatSemigroup_eq_and_norm_le t (f j)
  refine memBesov_iff.2 ⟨g, fun j ↦ by rw [littlewoodPaleyBlock_heatSemigroup_comm, hf j, hg j],
    hfm.mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hgn j) (by positivity)

/-- **The heat flow gains every amount of smoothness.** If `u ∈ B^s_{p,q}` and `t > 0`, then
`e^{tΔ} u ∈ B^{s'}_{p,q}` for every `s'`. -/
theorem _root_.TemperedDistribution.MemBesov.heatSemigroup_of_ne_zero {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ s p q) {t : ℝ≥0} (ht : t ≠ 0) (s' : ℝ) :
    (TemperedDistribution.heatSemigroup E F t u).MemBesov φ s' p q := by
  obtain ⟨C, -, hC⟩ := exists_littlewoodPaleyBlock_heatSemigroup_eq_and_rpow_mul_norm_le
    (F := F) (le_max_left 0 ((s' - s) / 2)) φ
  have hs' : s' ≤ s + 2 * max 0 ((s' - s) / 2) := by linarith [le_max_right 0 ((s' - s) / 2)]
  obtain ⟨f, hf, hfm⟩ := memBesov_iff.1 hu
  choose g hg hgn using fun j ↦ hC hs' t ht j u (f j) (hf j)
  refine memBesov_iff.2 ⟨g, hg,
    (hfm.const_mul (C * max 1 ((t : ℝ) ^ (-max 0 ((s' - s) / 2))))).mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact hgn j

/-- The heat flow at a time `t > 0` of an element `u` of `B^s_{p,q}`, as an element of
`B^{s'}_{p,q}` for `s' ≤ s + 2σ`, with norm at most `C max 1 (t^{-σ}) ‖u‖`, where `C` depends only
on `φ`, `σ`, `E` and `F`. -/
private theorem exists_toDistr_eq_heatSemigroup_and_norm_le {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C, 0 ≤ C ∧ ∀ {s s' : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], s' ≤ s + 2 * σ →
      ∀ t : ℝ≥0, t ≠ 0 → ∀ u : BesovSpace F φ s p q, ∃ v : BesovSpace F φ s' p q,
        v.toDistr = TemperedDistribution.heatSemigroup E F t u.toDistr ∧
          ‖v‖ ≤ C * max 1 ((t : ℝ) ^ (-σ)) * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_littlewoodPaleyBlock_heatSemigroup_eq_and_rpow_mul_norm_le (F := F) hσ φ
  refine ⟨C, hC0, fun {s s' p q} _ _ hs' t ht u ↦ ?_⟩
  choose g hg hgn using fun j ↦ hC hs' t ht j u.toDistr (u.block j) (coe_block u j).symm
  exact exists_toDistr_eq_and_norm_le_of_block (by positivity) u g hg hgn

variable [Fact (1 ≤ q)]

/-- The heat flow of an element of `B^s_{p,q}` lies in `B^s_{p,q}`, with norm at most `‖u‖`:
each block is contracted. -/
private theorem exists_toDistr_eq_heatSemigroup_and_norm_le_self (t : ℝ≥0)
    (u : BesovSpace F φ s p q) :
    ∃ v : BesovSpace F φ s p q,
      v.toDistr = TemperedDistribution.heatSemigroup E F t u.toDistr ∧ ‖v‖ ≤ ‖u‖ := by
  choose g hg hgn using fun j ↦ exists_heatSemigroup_eq_and_norm_le t (u.block j)
  obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_and_norm_le_of_block (s' := s)
    (w := TemperedDistribution.heatSemigroup E F t u.toDistr) zero_le_one u g
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

/-- **The semigroup law** `e^{t₂Δ} e^{t₁Δ} = e^{(t₁+t₂)Δ}` on `B^s_{p,q}`. -/
@[simp]
theorem heatSemigroup_heatSemigroup_apply (t₁ t₂ : ℝ≥0) (u : BesovSpace F φ s p q) :
    heatSemigroup F φ s p q t₂ (heatSemigroup F φ s p q t₁ u) =
      heatSemigroup F φ s p q (t₁ + t₂) u :=
  ext (by simp)

/-- The semigroup law `e^{t₂Δ} ∘ e^{t₁Δ} = e^{(t₁+t₂)Δ}` on `B^s_{p,q}` as an identity of
operators. -/
theorem heatSemigroup_compL_heatSemigroup (t₁ t₂ : ℝ≥0) :
    heatSemigroup F φ s p q t₂ ∘L heatSemigroup F φ s p q t₁ =
      heatSemigroup F φ s p q (t₁ + t₂) := by
  ext1 u
  exact heatSemigroup_heatSemigroup_apply t₁ t₂ u

section Smoothing

variable (F φ s p q) in
/-- **The smoothing heat semigroup on the Besov scale.** For `t > 0`, `e^{tΔ}` maps `B^s_{p,q}`
continuously into `B^{s'}_{p,q}` for every `s'`
(`TemperedDistribution.MemBesov.heatSemigroup_of_ne_zero`). For `σ ≥ 0` and `s' ≤ s + 2σ` its
norm is `O(max 1 (t^{-σ}))`, uniformly in `s`, `s'`, `p`, `q` and `t`
(`TauCeti.BesovSpace.exists_norm_heatSemigroupOfNeZero_le`). -/
def heatSemigroupOfNeZero (s' : ℝ) {t : ℝ≥0} (ht : t ≠ 0) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s' p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := (u.memBesov_toDistr.heatSemigroup_of_ne_zero ht s').toBesovSpace
      map_add' u v := ext (by simp)
      map_smul' c u := ext (by simp) } <| by
    obtain ⟨C, -, hC⟩ := exists_toDistr_eq_heatSemigroup_and_norm_le (F := F) (φ := φ)
      (le_max_left 0 ((s' - s) / 2))
    refine ⟨C * max 1 ((t : ℝ) ^ (-max 0 ((s' - s) / 2))), fun u ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ :=
      hC (s := s) (s' := s') (by linarith [le_max_right 0 ((s' - s) / 2)]) t ht u
    convert hvn using 2
    exact ext (by simp [hv])

@[simp]
theorem toDistr_heatSemigroupOfNeZero (s' : ℝ) {t : ℝ≥0} (ht : t ≠ 0)
    (u : BesovSpace F φ s p q) :
    (heatSemigroupOfNeZero F φ s p q s' ht u).toDistr =
      TemperedDistribution.heatSemigroup E F t u.toDistr := by
  simp [heatSemigroupOfNeZero]

/-- At the order `s' = s` the smoothing heat semigroup is the heat semigroup on `B^s_{p,q}`. -/
theorem heatSemigroupOfNeZero_self {t : ℝ≥0} (ht : t ≠ 0) :
    heatSemigroupOfNeZero F φ s p q s ht = heatSemigroup F φ s p q t := by
  ext1 u
  exact ext (by simp)

variable (F φ) in
/-- **The heat semigroup on a Besov space gains smoothness.** For `σ ≥ 0` there is a constant
`C`, depending only on `φ`, `σ`, `E` and `F`, such that for every `1 ≤ p, q ≤ ∞`, every `s`, every
`s' ≤ s + 2σ`, every `t > 0` and every `u ∈ B^s_{p,q}`,

`‖e^{tΔ} u‖_{B^{s'}_{p,q}} ≤ C max 1 (t^{-σ}) ‖u‖_{B^s_{p,q}}`. -/
theorem exists_norm_heatSemigroupOfNeZero_le {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C, 0 ≤ C ∧ ∀ {s s' : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], s' ≤ s + 2 * σ →
      ∀ {t : ℝ≥0} (ht : t ≠ 0) (u : BesovSpace F φ s p q),
        ‖heatSemigroupOfNeZero F φ s p q s' ht u‖ ≤ C * max 1 ((t : ℝ) ^ (-σ)) * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_toDistr_eq_heatSemigroup_and_norm_le (F := F) (φ := φ) hσ
  refine ⟨C, hC0, fun {s s' p q} _ _ hs' t ht u ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := hC hs' t ht u
  convert hvn using 2
  exact ext (by simp [hv])

variable (F φ) in
/-- **The smoothing estimate of the heat semigroup on Besov spaces.** For `σ ≥ 0` there is a
constant `C`, depending only on `φ`, `σ`, `E` and `F`, such that for every `1 ≤ p, q ≤ ∞`, every
`s`, every `s' ≤ s + 2σ`, every `0 < t ≤ 1` and every `u ∈ B^s_{p,q}`,

`‖e^{tΔ} u‖_{B^{s'}_{p,q}} ≤ C t^{-σ} ‖u‖_{B^s_{p,q}}`.

For `p = q = ∞` and `s' = s + 2σ` this is the smoothing estimate of the heat semigroup on the
Hölder–Zygmund scale `𝒞^s = B^s_{∞,∞}`. -/
theorem exists_norm_heatSemigroupOfNeZero_le_rpow_neg {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C, 0 ≤ C ∧ ∀ {s s' : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], s' ≤ s + 2 * σ →
      ∀ {t : ℝ≥0} (ht : t ≠ 0), t ≤ 1 → ∀ u : BesovSpace F φ s p q,
        ‖heatSemigroupOfNeZero F φ s p q s' ht u‖ ≤ C * (t : ℝ) ^ (-σ) * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_heatSemigroupOfNeZero_le F φ hσ
  refine ⟨C, hC0, fun {s s' p q} _ _ hs' t ht ht1 u ↦ (hC hs' ht u).trans_eq ?_⟩
  rw [max_eq_right (one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity)
    (by exact_mod_cast ht1) (neg_nonpos.2 hσ))]

end Smoothing

section StrongContinuity

/-- **The heat semigroup contracts every block:** `‖Δⱼ e^{tΔ} u‖_p ≤ ‖Δⱼ u‖_p`. -/
theorem norm_block_heatSemigroup_le (t : ℝ≥0) (u : BesovSpace F φ s p q) (j : ℕ) :
    ‖(heatSemigroup F φ s p q t u).block j‖ ≤ ‖u.block j‖ := by
  obtain ⟨g, hg, hgn⟩ := exists_heatSemigroup_eq_and_norm_le t (u.block j)
  rwa [← Lp.toTemperedDistribution_injective ((coe_block_heatSemigroup t u j).trans hg)] at hgn

variable (F φ) in
/-- **The heat flow of a single block tends to the block**, at a rate depending on the block
index `j` (and on `φ`) but uniform in `s`, `p`, `q` and `u`: for every `j` there is a function `c`
of time with `c t → 0` as `t → 0` and `‖Δⱼ (e^{tΔ} u - u)‖_p ≤ c t ‖Δⱼ u‖_p` for every `u` in
every Besov space `B^s_{p,q}`. The block `Δⱼ u` has frequencies in the ball of radius
`2^j φ.rOut`, on which the heat flow tends to the identity uniformly. -/
theorem exists_tendsto_and_norm_block_heatSemigroup_sub_le (j : ℕ) :
    ∃ c : ℝ≥0 → ℝ, Tendsto c (𝓝 0) (𝓝 0) ∧ ∀ {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]
      [Fact (1 ≤ q)] (t : ℝ≥0) (u : BesovSpace F φ s p q),
        ‖(heatSemigroup F φ s p q t u - u).block j‖ ≤ c t * ‖u.block j‖ := by
  obtain ⟨c, hc, hcf⟩ := exists_heatSemigroup_sub_eq_and_norm_le_of_isVanishingOn_fourier
    (E := E) (F := F) (2 ^ j * φ.rOut)
  refine ⟨c, hc, fun {s p q} _ _ t u ↦ ?_⟩
  have hv := isVanishingOn_fourier_littlewoodPaleyBlock φ j u.toDistr
  rw [← coe_block] at hv
  obtain ⟨g, hg, hgn⟩ := hcf t (u.block j) hv
  have hb : (heatSemigroup F φ s p q t u - u).block j = g := by
    refine Lp.toTemperedDistribution_injective ?_
    dsimp only
    rw [← hg, coe_block, toDistr_sub, toDistr_heatSemigroup, map_sub,
      littlewoodPaleyBlock_heatSemigroup_comm, ← coe_block]
  rwa [hb]

/-- The weighted blocks of `e^{tΔ} u - u` are at most twice those of `u`. -/
private theorem rpow_mul_norm_block_heatSemigroup_sub_le (t : ℝ≥0) (u : BesovSpace F φ s p q)
    (j : ℕ) :
    2 ^ (s * j) * ‖(heatSemigroup F φ s p q t u - u).block j‖ ≤
      2 * (2 ^ (s * j) * ‖u.block j‖) := by
  rw [block_sub, mul_left_comm, two_mul (‖u.block j‖)]
  gcongr
  exact (norm_sub_le _ _).trans (by gcongr; exact norm_block_heatSemigroup_le t u j)

/-- Each weighted block of `e^{tΔ} u - u` tends to `0` as `t → 0`. -/
private theorem tendsto_rpow_mul_norm_block_heatSemigroup_sub (u : BesovSpace F φ s p q)
    (j : ℕ) :
    Tendsto (fun t ↦ 2 ^ (s * j) * ‖(heatSemigroup F φ s p q t u - u).block j‖) (𝓝 0)
      (𝓝 0) := by
  obtain ⟨c, hc, hcu⟩ := exists_tendsto_and_norm_block_heatSemigroup_sub_le F φ j
  refine squeeze_zero (fun t ↦ by positivity)
    (fun t ↦ mul_le_mul_of_nonneg_left (hcu t u) (by positivity)) ?_
  simpa using (hc.mul_const ‖u.block j‖).const_mul (2 ^ (s * j))

/-- **Strong continuity of the heat semigroup on `B^s_{p,q}`, `q < ∞`.** For every
`u ∈ B^s_{p,q}` with `q < ∞`, `e^{tΔ} u → u` in `B^s_{p,q}` as `t → 0`. This holds for every
`1 ≤ p ≤ ∞`, including the case `p = ∞`, where the heat semigroup is not strongly continuous on
`L^∞`. -/
theorem tendsto_heatSemigroup (hq : q ≠ ⊤) (u : BesovSpace F φ s p q) :
    Tendsto (fun t ↦ heatSemigroup F φ s p q t u) (𝓝 0) (𝓝 u) := by
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [norm_eq_tsum_rpow hq]
  refine TauCeti.tendsto_tsum_rpow_rpow_of_dominated hq0 (fun t j ↦ by positivity)
    (fun t j ↦ rpow_mul_norm_block_heatSemigroup_sub_le t u j)
    (tendsto_rpow_mul_norm_block_heatSemigroup_sub u)
    (((hasSum_norm hq u).summable.mul_left (2 ^ q.toReal)).congr fun j ↦ ?_)
  rw [Real.mul_rpow zero_le_two (by positivity)]

/-- If the heat flow of `u ∈ B^s_{p,∞}` tends to `u`, the weighted blocks of `u` vanish at high
frequency, because those of `e^{tΔ} u`, `t > 0`, do and this is a closed condition. -/
private theorem tendsto_rpow_mul_norm_block_of_tendsto_heatSemigroup {u : BesovSpace F φ s p ∞}
    (hu : Tendsto (fun t ↦ heatSemigroup F φ s p ∞ t u) (𝓝 0) (𝓝 u)) :
    Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) := by
  refine isClosed_setOf_tendsto_rpow_mul_norm_block.mem_of_tendsto
    (hu.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_)
  -- At `t > 0`, `e^{tΔ} u` lies in `B^{s+1}_{p,∞} ⊆ B^s_{p,1}`, with the same blocks.
  set w := heatSemigroupOfNeZero F φ s p ∞ (s + 1) (ne_of_gt ht) u
  have h := tendsto_rpow_mul_norm_block ENNReal.one_ne_top
    (inclusionOfLT F φ p ∞ 1 (lt_add_one s) w)
  simp only [block_inclusionOfLT] at h
  exact h.congr fun j ↦ by
    rw [block_eq_of_toDistr_eq (u := heatSemigroup F φ s p ∞ t u) (v := w) (by simp [w]) j]

/-- If the weighted blocks of `u ∈ B^s_{p,∞}` vanish at high frequency, the heat flow of `u`
tends to `u`: the high blocks are small uniformly in time, and each low block converges. -/
private theorem tendsto_heatSemigroup_of_tendsto_rpow_mul_norm_block {u : BesovSpace F φ s p ∞}
    (ha : Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0)) :
    Tendsto (fun t ↦ heatSemigroup F φ s p ∞ t u) (𝓝 0) (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [norm_eq_ciSup]
  exact TauCeti.tendsto_iSup_of_dominated (fun t j ↦ by positivity)
    (fun t j ↦ rpow_mul_norm_block_heatSemigroup_sub_le t u j)
    (tendsto_rpow_mul_norm_block_heatSemigroup_sub u) (by simpa using ha.const_mul 2)

/-- **Strong continuity of the heat semigroup on `B^s_{p,∞}`.** For `u ∈ B^s_{p,∞}`,
`e^{tΔ} u → u` in `B^s_{p,∞}` as `t → 0` exactly when the weighted blocks of `u` vanish at high
frequency, `2^{js} ‖Δⱼ u‖_p → 0`. At `p = ∞` this describes the elements of the Hölder–Zygmund
space `𝒞^s` at which the heat semigroup is strongly continuous. -/
theorem tendsto_heatSemigroup_iff (u : BesovSpace F φ s p ∞) :
    Tendsto (fun t ↦ heatSemigroup F φ s p ∞ t u) (𝓝 0) (𝓝 u) ↔
      Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) :=
  ⟨tendsto_rpow_mul_norm_block_of_tendsto_heatSemigroup,
    tendsto_heatSemigroup_of_tendsto_rpow_mul_norm_block⟩

/-- **Strong continuity of the heat semigroup on the little Besov spaces.** For `u` in the little
Besov space `b^s_{p,∞}`, in particular in the little Hölder–Zygmund space `c^s` (`p = ∞`),
`e^{tΔ} u → u` in `B^s_{p,∞}` as `t → 0`. -/
theorem tendsto_heatSemigroup_of_mem_littleBesov {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) :
    Tendsto (fun t ↦ heatSemigroup F φ s p ∞ t u) (𝓝 0) (𝓝 u) :=
  (tendsto_heatSemigroup_iff u).2 (tendsto_rpow_mul_norm_block_of_mem_littleBesov hu)

/-- For `p < ∞` the heat semigroup on `B^s_{p,∞}` is strongly continuous exactly on the little
Besov space: `e^{tΔ} u → u` as `t → 0` if and only if `u ∈ b^s_{p,∞}`. -/
theorem tendsto_heatSemigroup_iff_mem_littleBesov (hp : p ≠ ⊤) (u : BesovSpace F φ s p ∞) :
    Tendsto (fun t ↦ heatSemigroup F φ s p ∞ t u) (𝓝 0) (𝓝 u) ↔ u ∈ littleBesov F φ s p := by
  rw [tendsto_heatSemigroup_iff, mem_littleBesov_iff_tendsto hp]

variable (φ p) in
/-- **The heat semigroup is not strongly continuous on `B^{-n/p'}_{p,∞}`.** On a real inner
product space of dimension `n ≥ 1`, for `1 ≤ p ≤ ∞`, `e^{tΔ} δ₀` does not tend to the Dirac mass
`δ₀` in `B^{-n/p'}_{p,∞}` as `t → 0`; at `p = ∞` this space is the Hölder–Zygmund space `𝒞^{-n}`.
So the restriction to `q < ∞` in `TauCeti.BesovSpace.tendsto_heatSemigroup` cannot be dropped. -/
theorem not_tendsto_heatSemigroup_delta_zero [Nontrivial E] :
    ¬Tendsto (fun t ↦ heatSemigroup ℂ φ _ p ∞ t (memBesov_delta_zero φ p).toBesovSpace) (𝓝 0)
      (𝓝 (memBesov_delta_zero φ p).toBesovSpace) := by
  rw [tendsto_heatSemigroup_iff]
  exact not_tendsto_rpow_mul_norm_block_delta_zero φ p

variable (F φ s p q) in
/-- **The heat semigroup on `B^s_{p,q}`, `q < ∞`, as a strongly continuous contraction
semigroup**, for every `1 ≤ p ≤ ∞`. Its operators are those of
`TauCeti.BesovSpace.heatSemigroup`, viewed as real-linear maps. -/
def heatContractionSemigroup (hq : q ≠ ⊤) :
    Semigroups.ContractionSemigroup (BesovSpace F φ s p q) where
  toFun t := (heatSemigroup F φ s p q t).restrictScalars ℝ
  map_zero' := by ext1 u; simp
  map_add' t₁ t₂ := by ext1 u; simp [add_comm t₁ t₂]
  continuousAt_zero' u := by
    simpa [ContinuousAt] using tendsto_heatSemigroup hq u
  contracting t := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
      rw [one_mul]; exact norm_heatSemigroup_le t u

@[simp]
theorem heatContractionSemigroup_apply (hq : q ≠ ⊤) (t : ℝ≥0) (u : BesovSpace F φ s p q) :
    heatContractionSemigroup F φ s p q hq t u = heatSemigroup F φ s p q t u :=
  (rfl)

end StrongContinuity

end BesovSpace

end TauCeti
