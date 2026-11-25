/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Cover
public import TauCeti.Analysis.InnerProductSpace.Compressible
public import TauCeti.Analysis.InnerProductSpace.Euclidean.IntegerPoints
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Topology.MetricSpace.CoveringNumbers

/-!
# The essential least common denominator of a real vector

For tolerances `α γ : ℝ`, the essential least common denominator `LCD_{α,γ}(a)` of a vector
`a ∈ ℝⁿ` is the infimum of the dilations `θ > 0` for which `θ • a` lies within distance
`min (γ ‖θ • a‖) α` of an integer point `TauCeti.latticePoint p`. The relative tolerance
`γ ‖θ • a‖` only admits integer points in a cone around the direction of `a`. For `γ < 1`, a small
LCD means that a moderate multiple of `a` is close to a nonzero integer vector, so that the
coordinates of `a` have a strong arithmetic structure. The small-ball probability of a weighted
sum `∑ aₖ ξₖ` of independent random variables is controlled by the reciprocal of the LCD of the
weights. This is how the LCD enters the lower bounds for the least singular value of square random
matrices. The LCD is `⊤` when no dilation qualifies, as for `a = 0`.

This file proves three deterministic facts about the LCD.

* An incompressible unit vector, in the sense of `TauCeti.IsIncompressibleVector k ρ`, has LCD at
  least `√(k + 1) / 2` whenever `γ ≤ ρ`. For `ρ ≥ 0`, its coordinates of norm at most
  `1 / √(k + 1)` carry squared mass more than `ρ²`, and they stay within `1 / 2` of `0` under
  dilations by at most `√(k + 1) / 2`. For `ρ < 0` the relative tolerance is negative, so no
  dilation qualifies.
* If the LCD of `a ≠ 0` is at least `L > 0`, `γ > 0` and `2t < α`, the recurrence set of the
  dilations `θ ∈ [-T, T]` bringing `θ • a` within `t` of an integer point has measure at most
  `(4T / L + 1) * (2t / (γ ‖a‖))`. This is the estimate through which the LCD controls the
  integral of a characteristic function in the small-ball inequality.
* A set of unit vectors whose LCDs lie in `[D, 2D)` has a `4α/D`-net inside the set with at most
  `(e (1 + √π (2D + α) / √n))ⁿ` points. Each such vector is within `2α/D` of a normalized integer
  point of norm at most `2D + α`.

## Main definitions

* `TauCeti.leastCommonDenominator`: the essential least common denominator `LCD_{α,γ}`.

## Main results

* `TauCeti.IsIncompressibleVector.ofReal_sqrt_div_two_le_leastCommonDenominator`: the lower bound
  for incompressible vectors.
* `TauCeti.volume_setOf_mem_Icc_exists_norm_smul_sub_le_le`: the measure of recurrence sets.
* `TauCeti.exists_finset_isCover_of_forall_leastCommonDenominator_mem_Ico`: nets of the level sets
  of the LCD.

## References

* M. Rudelson and R. Vershynin, *Smallest singular value of a random rectangular matrix*,
  Comm. Pure Appl. Math. 62 (2009), §3 (the definition of the LCD, Lemmas 3.5 and 3.6) and
  Lemma 4.7. Their Lemma 3.5 bounds recurrence sets for the `m`-dimensional LCD; the
  one-dimensional case is proved here, for dilations in an arbitrary interval `[-T, T]`. Their
  Lemma 3.6 assumes `γ < ρ² √δ / 2`, where `δ n` plays the role of `k`; here `γ ≤ ρ` suffices.
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Real

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The **essential least common denominator** `LCD_{α,γ}(a)` of a real vector `a`: the infimum
of the dilations `θ > 0` for which `θ • a` lies within distance `min (γ * ‖θ • a‖) α` of an integer
point. It is `⊤` when no dilation qualifies. -/
def leastCommonDenominator (α γ : ℝ) (a : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ⨅ (θ : ℝ) (_ : 0 < θ ∧ ∃ p : ι → ℤ,
    ‖θ • a - latticePoint p‖ < min (γ * ‖θ • a‖) α), ENNReal.ofReal θ

variable {α γ : ℝ} {a : EuclideanSpace ℝ ι}

/-- The LCD is less than `D` exactly when some dilation `0 < θ < D` brings `θ • a` within
`min (γ * ‖θ • a‖) α` of an integer point. -/
theorem leastCommonDenominator_lt_ofReal_iff {D : ℝ} :
    leastCommonDenominator α γ a < ENNReal.ofReal D ↔ ∃ θ, 0 < θ ∧ θ < D ∧ ∃ p : ι → ℤ,
      ‖θ • a - latticePoint p‖ < min (γ * ‖θ • a‖) α := by
  simp only [leastCommonDenominator, iInf_lt_iff, exists_prop]
  constructor
  · rintro ⟨θ, ⟨hθ, hp⟩, hlt⟩
    exact ⟨θ, hθ, (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1, hp⟩
  · rintro ⟨θ, hθ, hθD, hp⟩
    exact ⟨θ, ⟨hθ, hp⟩, ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hθD, hθ.trans hθD⟩⟩

/-- The LCD is at least `D` exactly when no dilation `0 < θ < D` brings `θ • a` within
`min (γ * ‖θ • a‖) α` of an integer point. -/
theorem ofReal_le_leastCommonDenominator_iff {D : ℝ} :
    ENNReal.ofReal D ≤ leastCommonDenominator α γ a ↔ ∀ θ, 0 < θ → θ < D → ∀ p : ι → ℤ,
      min (γ * ‖θ • a‖) α ≤ ‖θ • a - latticePoint p‖ := by
  rw [← not_lt, leastCommonDenominator_lt_ofReal_iff]
  simp only [not_exists, not_and, not_lt]

/-- A dilation `θ > 0` that brings `θ • a` within `min (γ * ‖θ • a‖) α` of an integer point bounds
the LCD. -/
theorem leastCommonDenominator_le_ofReal {θ : ℝ} (hθ : 0 < θ) (p : ι → ℤ)
    (hp : ‖θ • a - latticePoint p‖ < min (γ * ‖θ • a‖) α) :
    leastCommonDenominator α γ a ≤ ENNReal.ofReal θ :=
  iInf₂_le θ ⟨hθ, p, hp⟩

/-- No dilation of the zero vector qualifies, so its LCD is `⊤`. -/
@[simp]
theorem leastCommonDenominator_zero (α γ : ℝ) :
    leastCommonDenominator α γ (0 : EuclideanSpace ℝ ι) = ⊤ := by
  refine iInf₂_eq_top.2 fun _ ⟨_, p, hp⟩ ↦ absurd hp (not_lt.2 ?_)
  rw [smul_zero, norm_zero, mul_zero]
  exact (min_le_left _ _).trans (norm_nonneg _)

/-- Larger tolerances `α` and `γ` admit more dilations, so they give a smaller LCD. -/
theorem leastCommonDenominator_anti {α' γ' : ℝ} (hα : α ≤ α') (hγ : γ ≤ γ') :
    leastCommonDenominator α' γ' a ≤ leastCommonDenominator α γ a :=
  le_iInf₂ fun _ ⟨hθ, p, hp⟩ ↦ leastCommonDenominator_le_ofReal hθ p <|
    hp.trans_le (min_le_min (mul_le_mul_of_nonneg_right hγ (norm_nonneg _)) hα)

/-- A dilation `θ • x` of an incompressible unit vector, with `0 < θ ≤ √(k + 1) / 2`, is farther
than `ρ * θ` from every integer point. -/
theorem IsIncompressibleVector.mul_lt_norm_smul_sub {k : ℕ} {ρ θ : ℝ}
    {x : EuclideanSpace ℝ ι} (hx : IsIncompressibleVector k ρ x) (hθ : 0 < θ)
    (hθk : θ ≤ √(k + 1) / 2) (p : ι → ℤ) :
    ρ * θ < ‖θ • x - latticePoint p‖ := by
  classical
  rcases lt_or_ge ρ 0 with hρ | hρ
  · exact (mul_neg_of_neg_of_pos hρ hθ).trans_le (norm_nonneg _)
  -- The coordinates of norm at most `1 / √(k + 1)` carry squared mass more than `ρ ^ 2`.
  let s := Finset.univ.filter fun i ↦ 1 / √(k + 1) < ‖x i‖
  have hs : s.card ≤ k := PiLp.card_filter_lt_norm_le (by positivity) (by
    rw [hx.norm_eq_one, div_pow, one_pow, Real.sq_sqrt (by positivity)]
    exact (mul_one_div_cancel (ne_of_gt (by positivity))).ge)
  have hmass := ((isIncompressibleVector_iff_sum_compl_gt hρ).1 hx).2 s hs
  -- After the dilation these coordinates stay within `1 / 2` of `0`, so no integer beats `0`.
  have hcoord : ∀ i ∈ sᶜ, (θ * x i) ^ 2 ≤ (θ * x i - p i) ^ 2 := by
    intro i hi
    have hxi : ‖x i‖ ≤ 1 / √(k + 1) := by simpa [s] using hi
    have ht : |θ * x i| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hθ, ← Real.norm_eq_abs]
      calc
        θ * ‖x i‖ ≤ √(k + 1) / 2 * (1 / √(k + 1)) :=
          mul_le_mul hθk hxi (norm_nonneg _) (by positivity)
        _ = 1 / 2 := by field_simp
    refine sq_le_sq.2 ?_
    rcases eq_or_ne (p i) 0 with hp | hp
    · simp [hp]
    · have hq : (1 : ℝ) ≤ |(p i : ℝ)| := by exact_mod_cast Int.one_le_abs hp
      have := abs_sub_abs_le_abs_sub (p i : ℝ) (θ * x i)
      rw [abs_sub_comm] at this
      linarith
  have hsq : (ρ * θ) ^ 2 < ‖θ • x - latticePoint p‖ ^ 2 := calc
    (ρ * θ) ^ 2 = θ ^ 2 * ρ ^ 2 := by ring
    _ < θ ^ 2 * ∑ i ∈ sᶜ, ‖x i‖ ^ 2 := mul_lt_mul_of_pos_left hmass (by positivity)
    _ = ∑ i ∈ sᶜ, (θ * x i) ^ 2 := by
      rw [Finset.mul_sum]
      simp_rw [Real.norm_eq_abs, sq_abs, mul_pow]
    _ ≤ ∑ i ∈ sᶜ, (θ * x i - p i) ^ 2 := Finset.sum_le_sum hcoord
    _ ≤ ∑ i, (θ * x i - p i) ^ 2 := Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
    _ = _ := by simp [EuclideanSpace.real_norm_sq_eq]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

/-- **The LCD of incompressible vectors.** An incompressible unit vector with sparsity parameter
`k` and radius `ρ` has LCD at least `√(k + 1) / 2` for every `γ ≤ ρ` and every `α`. -/
theorem IsIncompressibleVector.ofReal_sqrt_div_two_le_leastCommonDenominator {k : ℕ} {ρ : ℝ}
    {x : EuclideanSpace ℝ ι} (hx : IsIncompressibleVector k ρ x) (hγ : γ ≤ ρ) :
    ENNReal.ofReal (√(k + 1) / 2) ≤ leastCommonDenominator α γ x := by
  refine ofReal_le_leastCommonDenominator_iff.2 fun θ hθ hθk p ↦ ?_
  have hnorm : ‖θ • x‖ = θ := by
    rw [norm_smul, hx.norm_eq_one, mul_one, Real.norm_of_nonneg hθ.le]
  calc
    min (γ * ‖θ • x‖) α ≤ γ * θ := (min_le_left _ _).trans_eq (by rw [hnorm])
    _ ≤ ρ * θ := mul_le_mul_of_nonneg_right hγ hθ.le
    _ ≤ _ := (hx.mul_lt_norm_smul_sub hθ hθk.le p).le

/-- Two dilations that are closer than a lower bound `L` of the LCD, and that each bring `a`
within `t` of an integer point with `2t < α`, are within `2t / (γ ‖a‖)` of each other. -/
private theorem abs_sub_le_of_ofReal_le_leastCommonDenominator {L t θ₁ θ₂ : ℝ}
    (hLa : ENNReal.ofReal L ≤ leastCommonDenominator α γ a) (htα : 2 * t < α)
    (hγa : 0 < γ * ‖a‖) {p₁ p₂ : ι → ℤ}
    (h₁ : ‖θ₁ • a - latticePoint p₁‖ ≤ t)
    (h₂ : ‖θ₂ • a - latticePoint p₂‖ ≤ t) (hL : |θ₁ - θ₂| < L) :
    |θ₁ - θ₂| ≤ 2 * t / (γ * ‖a‖) := by
  wlog h₂₁ : θ₂ ≤ θ₁ generalizing θ₁ θ₂ p₁ p₂
  · rw [abs_sub_comm] at hL ⊢
    exact this h₂ h₁ hL (le_of_not_ge h₂₁)
  rw [abs_of_nonneg (sub_nonneg.2 h₂₁)] at hL ⊢
  rcases h₂₁.eq_or_lt with rfl | h₂₁
  · rw [sub_self]
    exact div_nonneg (by linarith [(norm_nonneg _).trans h₁]) hγa.le
  have hτ : 0 < θ₁ - θ₂ := sub_pos.2 h₂₁
  -- The difference of the two dilations is within `2t` of the difference of the integer points.
  have hdiff : ‖(θ₁ - θ₂) • a - latticePoint (p₁ - p₂)‖ ≤ 2 * t := by
    have heq : (θ₁ - θ₂) • a - latticePoint (p₁ - p₂) =
        (θ₁ • a - latticePoint p₁) - (θ₂ • a - latticePoint p₂) := by
      rw [latticePoint_sub, sub_smul]
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith)
  -- Since `2t < α`, the LCD bound forces `γ (θ₁ - θ₂) ‖a‖ ≤ 2t`.
  have hmin := ofReal_le_leastCommonDenominator_iff.1 hLa _ hτ hL (p₁ - p₂)
  rw [norm_smul, Real.norm_of_nonneg hτ.le] at hmin
  rw [le_div_iff₀ hγa]
  linarith [(min_le_iff.1 (hmin.trans hdiff)).resolve_right (by linarith)]

/-- **Recurrence sets and the LCD.** Let `L > 0` be at most the LCD of a vector `a ≠ 0`, with
`γ > 0` and `2t < α`. Then the dilations `θ ∈ [-T, T]` that bring `θ • a` within `t` of an integer
point form a set of measure at most `(4T / L + 1) * (2t / (γ ‖a‖))`. -/
theorem volume_setOf_mem_Icc_exists_norm_smul_sub_le_le {L T t : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    (ha : a ≠ 0) (htα : 2 * t < α) (hLa : ENNReal.ofReal L ≤ leastCommonDenominator α γ a) :
    volume {θ ∈ Icc (-T) T | ∃ p : ι → ℤ, ‖θ • a - latticePoint p‖ ≤ t} ≤
      ENNReal.ofReal ((4 * T / L + 1) * (2 * t / (γ * ‖a‖))) := by
  set I := {θ ∈ Icc (-T) T | ∃ p : ι → ℤ, ‖θ • a - latticePoint p‖ ≤ t}
  have hγa : 0 < γ * ‖a‖ := mul_pos hγ (norm_pos_iff.2 ha)
  rcases lt_or_ge t 0 with ht | ht
  · have hI : I = ∅ := eq_empty_of_forall_notMem fun _ ⟨_, _, hp⟩ ↦
      (norm_nonneg _).not_gt (hp.trans_lt ht)
    simp [hI]
  rcases lt_or_ge T 0 with hT | hT
  · have hI : I = ∅ := eq_empty_of_forall_notMem fun _ ⟨hθ, _⟩ ↦ by linarith [hθ.1, hθ.2]
    simp [hI]
  have hr : 0 ≤ 2 * t / (γ * ‖a‖) := by positivity
  -- Cover `[-T, T]` by `⌊4T / L⌋₊ + 1` intervals of length `L / 2`.
  let K : ℕ → Set ℝ := fun j ↦ Icc (-T + j * (L / 2)) (-T + (j + 1) * (L / 2))
  have hcover : I ⊆ ⋃ j ∈ Finset.range (⌊4 * T / L⌋₊ + 1), I ∩ K j := by
    intro θ hθ
    have hθT := hθ.1
    have hj0 : 0 ≤ (θ + T) / (L / 2) := div_nonneg (by linarith [hθT.1]) (by positivity)
    have hfl := Nat.floor_le hj0
    have hlt := Nat.lt_floor_add_one ((θ + T) / (L / 2))
    rw [le_div_iff₀ (by positivity)] at hfl
    rw [div_lt_iff₀ (by positivity)] at hlt
    refine mem_iUnion₂.2 ⟨⌊(θ + T) / (L / 2)⌋₊, Finset.mem_range.2 (Nat.lt_succ_of_le
      (Nat.floor_le_floor ?_)), hθ, by linarith, by linarith⟩
    rw [div_le_div_iff₀ (by positivity) hL]
    nlinarith [hθT.2]
  have hpiece : ∀ j, volume (I ∩ K j) ≤ ENNReal.ofReal (2 * t / (γ * ‖a‖)) := by
    intro j
    refine (Real.volume_le_diam _).trans (Metric.ediam_le fun x hx y hy ↦ ?_)
    rw [edist_dist, Real.dist_eq]
    obtain ⟨⟨-, p₁, h₁⟩, hx₁, hx₂⟩ := hx
    obtain ⟨⟨-, p₂, h₂⟩, hy₁, hy₂⟩ := hy
    refine ENNReal.ofReal_le_ofReal
      (abs_sub_le_of_ofReal_le_leastCommonDenominator hLa htα hγa h₁ h₂ ?_)
    rw [abs_lt]
    constructor <;> nlinarith
  calc
    volume I ≤ volume (⋃ j ∈ Finset.range (⌊4 * T / L⌋₊ + 1), I ∩ K j) := measure_mono hcover
    _ ≤ ∑ j ∈ Finset.range (⌊4 * T / L⌋₊ + 1), volume (I ∩ K j) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (⌊4 * T / L⌋₊ + 1), ENNReal.ofReal (2 * t / (γ * ‖a‖)) :=
      Finset.sum_le_sum fun j _ ↦ hpiece j
    _ = ENNReal.ofReal ((⌊4 * T / L⌋₊ + 1 : ℕ) * (2 * t / (γ * ‖a‖))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast]
    _ ≤ _ := by
      have hTL : 0 ≤ 4 * T / L := by positivity
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hr)
      push_cast
      linarith [Nat.floor_le hTL]

/-- **Nets of the level sets of the LCD.** A set `S` of unit vectors whose LCDs lie in `[D, 2D)`
has a `4α/D`-net contained in `S` with at most `(e (1 + √π (2D + α) / √n))ⁿ` points, where `n` is
the cardinality of `ι`. -/
theorem exists_finset_isCover_of_forall_leastCommonDenominator_mem_Ico {α D : ℝ≥0} {γ : ℝ}
    {S : Set (EuclideanSpace ℝ ι)}
    (hS : ∀ x ∈ S, ‖x‖ = 1 ∧ leastCommonDenominator α γ x ∈ Ico (D : ℝ≥0∞) (2 * D)) :
    ∃ N : Finset (EuclideanSpace ℝ ι), (N : Set (EuclideanSpace ℝ ι)) ⊆ S ∧
      IsCover (4 * α / D) S N ∧
      (N.card : ℝ) ≤
        (Real.exp 1 * (1 + √π * (2 * D + α) / √(Fintype.card ι))) ^ Fintype.card ι := by
  classical
  have hfin := finite_setOf_norm_latticePoint_le (ι := ι) (2 * D + α)
  let N₀ : Finset (EuclideanSpace ℝ ι) := hfin.toFinset.image fun p ↦
    NormedSpace.normalize (latticePoint p)
  -- Every point of `S` is within `2α/D` of a normalized integer point of norm at most `2D + α`.
  have hN₀ : IsCover (2 * α / D) S N₀ := by
    intro x hx
    obtain ⟨hx1, hDx, hx2D⟩ := hS x hx
    rw [← ENNReal.ofReal_coe_nnreal] at hDx
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul zero_le_two] at hx2D
    obtain ⟨θ, hθ, hθ2D, p, hp⟩ := leastCommonDenominator_lt_ofReal_iff.1 hx2D
    have hDθ : (D : ℝ) ≤ θ := by
      by_contra! h
      exact (ofReal_le_leastCommonDenominator_iff.1 hDx θ hθ h p).not_gt hp
    set v : EuclideanSpace ℝ ι := latticePoint p
    have hpα : ‖θ • x - v‖ < α := hp.trans_le (min_le_right _ _)
    have hnorm : ‖θ • x‖ = θ := by rw [norm_smul, hx1, mul_one, Real.norm_of_nonneg hθ.le]
    have hvR : ‖v‖ ≤ 2 * D + α := by
      have h := norm_sub_le (θ • x) (θ • x - v)
      rw [sub_sub_cancel] at h
      linarith
    refine ⟨_, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hvR), edist_le_coe.mpr ?_⟩
    have hsub : x - θ⁻¹ • v = θ⁻¹ • (θ • x - v) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hθ.ne', one_smul]
    have hdist : dist x (θ⁻¹ • v) = ‖θ • x - v‖ / θ := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hθ.le), inv_mul_eq_div]
    calc
      dist x (NormedSpace.normalize v) = dist x (NormedSpace.normalize (θ⁻¹ • v)) := by
        rw [NormedSpace.normalize_smul_of_pos (inv_pos.2 hθ)]
      _ ≤ 2 * dist x (θ⁻¹ • v) := NormedSpace.dist_normalize_le_two_mul_dist hx1 _
      _ ≤ 2 * (α / D) := by
        rw [hdist]
        exact mul_le_mul_of_nonneg_left
          (div_le_div₀ α.coe_nonneg hpα.le (by linarith) hDθ) zero_le_two
      _ = ((2 * α / D : ℝ≥0) : ℝ) := by push_cast; ring
  obtain ⟨N, hNS, hN, hcard⟩ := hN₀.exists_finset_subset_isCover_two_mul
  refine ⟨N, hNS, by convert hN using 2; ring, ?_⟩
  calc
    (N.card : ℝ) ≤ N₀.card := by exact_mod_cast hcard
    _ ≤ hfin.toFinset.card := by exact_mod_cast Finset.card_image_le
    _ ≤ _ := card_le_of_forall_norm_latticePoint_le (by positivity)
      fun p hp ↦ hfin.mem_toFinset.1 hp

end TauCeti
