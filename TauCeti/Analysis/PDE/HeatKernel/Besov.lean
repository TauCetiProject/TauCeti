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
* `TemperedDistribution.MemBesov.heatSemigroup` and
  `TemperedDistribution.MemBesov.heatSemigroup_of_ne_zero`: `e^{tΔ}` preserves `B^s_{p,q}` and, for
  `t > 0`, maps it into every `B^{s'}_{p,q}`.
* `TauCeti.BesovSpace.heatSemigroupOfNeZero`: for `t > 0`, `e^{tΔ}` as a continuous linear map
  `B^s_{p,q} → B^{s'}_{p,q}`, with the uniform bounds
  `TauCeti.BesovSpace.exists_norm_heatSemigroupOfNeZero_le` and
  `TauCeti.BesovSpace.exists_norm_heatSemigroupOfNeZero_le_rpow_neg`, the smoothing estimate
  `B^s_{p,q} → B^{s + 2σ}_{p,q}` with norm `O(t^{-σ})` for `0 < t ≤ 1`.

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
  obtain ⟨A, hA0, hA⟩ := exists_rpow_mul_exp_le hσ hc
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  refine ⟨C * A, mul_nonneg hC0 hA0, fun {s s' p} _ hs' t ht j u f hf ↦ ?_⟩
  obtain ⟨g, hg, hgn⟩ := hCc j t u f hf
  refine ⟨g, hg, ?_⟩
  -- Raising the order from `s` to `s + 2σ` multiplies the weight `2^{js}` by `(4^j)^σ`.
  have h4 : (4 : ℝ) ^ j = 2 ^ (2 * j : ℝ) := by
    rw [rpow_mul zero_le_two, rpow_natCast, rpow_two]
    norm_num
  have hw : (2 : ℝ) ^ ((s + 2 * σ) * j) = ((4 : ℝ) ^ j) ^ σ * 2 ^ (s * j) := by
    rw [h4, ← rpow_mul zero_le_two, ← rpow_add two_pos]
    ring_nf
  have hs'j : (2 : ℝ) ^ (s' * j) ≤ ((4 : ℝ) ^ j) ^ σ * 2 ^ (s * j) :=
    (rpow_le_rpow_of_exponent_le one_le_two
      (mul_le_mul_of_nonneg_right hs' j.cast_nonneg)).trans_eq hw
  calc 2 ^ (s' * j) * ‖g‖
      ≤ ((4 : ℝ) ^ j) ^ σ * 2 ^ (s * j) * (C * rexp (-(c * ((4 ^ j - 1) * t))) * ‖f‖) :=
        mul_le_mul hs'j hgn (norm_nonneg _) (by positivity)
    _ = C * (((4 : ℝ) ^ j) ^ σ * rexp (-(c * ((4 ^ j - 1) * t)))) * (2 ^ (s * j) * ‖f‖) := by
        ring
    _ ≤ C * (A * max 1 ((t : ℝ) ^ (-σ))) * (2 ^ (s * j) * ‖f‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hA j (by positivity)) hC0) (by positivity)
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
    { toFun u := (u.memBesov_toDistr.heatSemigroup t).toBesovSpace
      map_add' _ _ := ext (by simp)
      map_smul' _ _ := ext (by simp) }
    1 fun u ↦ by
      obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_heatSemigroup_and_norm_le_self t u
      rw [one_mul]
      convert hvn using 2
      exact ext (by simp [hv])

@[simp]
theorem toDistr_heatSemigroup (t : ℝ≥0) (u : BesovSpace F φ s p q) :
    (heatSemigroup F φ s p q t u).toDistr =
      TemperedDistribution.heatSemigroup E F t u.toDistr := by
  simp [heatSemigroup]

/-- The blocks of the heat flow of `u` are the heat flows of the blocks of `u`. -/
theorem coe_block_heatSemigroup (t : ℝ≥0) (u : BesovSpace F φ s p q) (j : ℕ) :
    ((heatSemigroup F φ s p q t u).block j : 𝓢'(E, F)) =
      TemperedDistribution.heatSemigroup E F t (u.block j) := by
  rw [coe_block, coe_block, toDistr_heatSemigroup, littlewoodPaleyBlock_heatSemigroup_comm]

/-- The heat semigroup is a contraction of `B^s_{p,q}`. -/
theorem norm_heatSemigroup_le (t : ℝ≥0) (u : BesovSpace F φ s p q) :
    ‖heatSemigroup F φ s p q t u‖ ≤ ‖u‖ :=
  ((heatSemigroup F φ s p q t).le_of_opNorm_le
    (LinearMap.mkContinuous_norm_le _ zero_le_one _) u).trans_eq (one_mul _)

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

end BesovSpace

end TauCeti
