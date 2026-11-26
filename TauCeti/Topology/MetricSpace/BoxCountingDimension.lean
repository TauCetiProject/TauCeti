/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Data.ENNReal.Inv
import TauCeti.Topology.Algebra.Order.Field

/-!
# Upper and lower box-counting dimensions

For a subset `A` of a pseudo-emetric space, write `N(ε, A)` for Mathlib's covering number
`Metric.coveringNumber ε A`: the least cardinality, in `ℕ∞`, of a subset of `A` such that every
point of `A` lies at distance at most `ε` from one of its points. The *upper box-counting
dimension* of `A` is the infimum of the exponents `d ≥ 0` such that `N(ε, A) ≤ ε ^ (-d)` for all
sufficiently small `ε > 0`, and the *lower box-counting dimension* is the infimum of the exponents
`d ≥ 0` such that `N(ε, A) ≤ ε ^ (-d)` for arbitrarily small `ε > 0`. Both take values in `ℝ≥0∞`,
an infimum over no exponent being `∞`. These are the upper and lower Minkowski dimensions.

The box-counting dimensions measure a set by covers at a single scale, so they bound the
Hausdorff dimension from above: a cover of `A` by `N(ε, A)` closed balls of radius `ε` has
`∑ (diam)^t ≤ 2 ^ t ε ^ (t - d)` when `N(ε, A) ≤ ε ^ (-d)`, which tends to `0` for `t > d`.

## Main definitions

* `TauCeti.upperBoxDim A`: the upper box-counting dimension of `A`.
* `TauCeti.lowerBoxDim A`: the lower box-counting dimension of `A`.

## Main results

* `TauCeti.upperBoxDim_le_iff` and `TauCeti.lowerBoxDim_le_iff`: the dimension is at most `D`
  exactly when, for every exponent `d > D`, the covering numbers are eventually (respectively
  frequently) at most `ε ^ (-d)`.
* `TauCeti.lowerBoxDim_le_upperBoxDim`.
* `Set.Finite.upperBoxDim_eq_zero` and `Set.Finite.lowerBoxDim_eq_zero`: finite sets have both
  dimensions zero, although for two points at positive distance the exponent `0` itself does not
  satisfy the defining inequality.
* `TauCeti.upperBoxDim_eq_top_of_not_totallyBounded` and
  `TauCeti.lowerBoxDim_eq_top_of_not_totallyBounded`: a set that is not totally bounded has both
  dimensions infinite.
* `TauCeti.upperBoxDim_mono` and `TauCeti.lowerBoxDim_mono`: both dimensions are monotone in the
  set, although the covering number itself is not.
* `TauCeti.hausdorffMeasure_eq_zero_of_frequently_coveringNumber_le`: if `N(ε, A) ≤ ε ^ (-d)` for
  arbitrarily small `ε`, then `μH[t] A = 0` for every `t > d`.
* `TauCeti.dimH_le_lowerBoxDim`: the Hausdorff dimension is at most the lower box-counting
  dimension, in every extended metric space.

## References

* C. J. Bishop and Y. Peres, *Fractals in Probability and Analysis*, Section 1.1 (the
  definitions) and inequality (1.2.3) (the comparison with the Hausdorff dimension).
-/

public section

open Filter Metric MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {A B : Set X}

/-- The **upper box-counting dimension** (upper Minkowski dimension) of a set `A`: the infimum of
the exponents `d ≥ 0` such that the covering number of `A` at radius `ε` is at most `ε ^ (-d)` for
all sufficiently small `ε > 0`. It is `∞` when no exponent qualifies. -/
noncomputable def upperBoxDim (A : Set X) : ℝ≥0∞ :=
  ⨅ (d : ℝ≥0) (_ : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ)), (d : ℝ≥0∞)

/-- The **lower box-counting dimension** (lower Minkowski dimension) of a set `A`: the infimum of
the exponents `d ≥ 0` such that the covering number of `A` at radius `ε` is at most `ε ^ (-d)` for
arbitrarily small `ε > 0`. It is `∞` when no exponent qualifies. -/
noncomputable def lowerBoxDim (A : Set X) : ℝ≥0∞ :=
  ⨅ (d : ℝ≥0) (_ : ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ)), (d : ℝ≥0∞)

/-- An exponent at which the covering numbers are eventually bounded bounds the upper box-counting
dimension. -/
theorem upperBoxDim_le_of_eventually {d : ℝ≥0}
    (h : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ)) :
    upperBoxDim A ≤ d :=
  iInf₂_le d h

/-- An exponent at which the covering numbers are frequently bounded bounds the lower box-counting
dimension. -/
theorem lowerBoxDim_le_of_frequently {d : ℝ≥0}
    (h : ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0, (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ)) :
    lowerBoxDim A ≤ d :=
  iInf₂_le d h

/-- Above the upper box-counting dimension, the covering numbers are eventually bounded:
if `upperBoxDim A < d`, then `N(ε, A) ≤ ε ^ (-d)` for all small `ε > 0`. -/
theorem eventually_coveringNumber_le_of_upperBoxDim_lt {d : ℝ≥0} (h : upperBoxDim A < d) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ) := by
  simp only [upperBoxDim, iInf_lt_iff, exists_prop] at h
  obtain ⟨d₀, hd₀, hlt⟩ := h
  filter_upwards [hd₀, ENNReal.eventually_mul_inv_rpow_le ENNReal.one_ne_top
    (NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hlt))] with ε h₁ h₂
  exact h₁.trans (by simpa using h₂)

/-- Above the lower box-counting dimension, the covering numbers are frequently bounded:
if `lowerBoxDim A < d`, then `N(ε, A) ≤ ε ^ (-d)` for arbitrarily small `ε > 0`. -/
theorem frequently_coveringNumber_le_of_lowerBoxDim_lt {d : ℝ≥0} (h : lowerBoxDim A < d) :
    ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0, (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ) := by
  simp only [lowerBoxDim, iInf_lt_iff, exists_prop] at h
  obtain ⟨d₀, hd₀, hlt⟩ := h
  refine hd₀.mp ?_
  filter_upwards [ENNReal.eventually_mul_inv_rpow_le ENNReal.one_ne_top
    (NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hlt))] with ε h₂ h₁
  exact h₁.trans (by simpa using h₂)

/-- The upper box-counting dimension of `A` is at most `D` exactly when, for every exponent
`d > D`, the covering number of `A` at radius `ε` is at most `ε ^ (-d)` for all small `ε > 0`. -/
theorem upperBoxDim_le_iff {D : ℝ≥0∞} :
    upperBoxDim A ≤ D ↔ ∀ d : ℝ≥0, D < d →
      ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ) :=
  ⟨fun h _ hd => eventually_coveringNumber_le_of_upperBoxDim_lt (h.trans_lt hd),
    fun h => ENNReal.le_of_forall_nnreal_gt fun d hd => upperBoxDim_le_of_eventually (h d hd)⟩

/-- The lower box-counting dimension of `A` is at most `D` exactly when, for every exponent
`d > D`, the covering number of `A` at radius `ε` is at most `ε ^ (-d)` for arbitrarily small
`ε > 0`. -/
theorem lowerBoxDim_le_iff {D : ℝ≥0∞} :
    lowerBoxDim A ≤ D ↔ ∀ d : ℝ≥0, D < d →
      ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0, (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ) :=
  ⟨fun h _ hd => frequently_coveringNumber_le_of_lowerBoxDim_lt (h.trans_lt hd),
    fun h => ENNReal.le_of_forall_nnreal_gt fun d hd => lowerBoxDim_le_of_frequently (h d hd)⟩

/-- The lower box-counting dimension is at most the upper one. -/
theorem lowerBoxDim_le_upperBoxDim : lowerBoxDim A ≤ upperBoxDim A :=
  le_iInf₂ fun _ hd => lowerBoxDim_le_of_frequently hd.frequently

/-- A finite set has upper box-counting dimension zero: its covering numbers are bounded, by its
cardinality, so every positive exponent qualifies. The infimum is not attained when `A` consists
of two points at positive distance, since then `N(ε, A) = 2 > ε ^ 0` for small `ε`. -/
theorem _root_.Set.Finite.upperBoxDim_eq_zero (hA : A.Finite) : upperBoxDim A = 0 := by
  refine le_antisymm
    (ENNReal.le_of_forall_nnreal_gt fun d hd => upperBoxDim_le_of_eventually ?_) bot_le
  have hcard : (A.encard : ℝ≥0∞) ≠ ∞ := ENat.toENNReal_ne_top.2 hA.encard_lt_top.ne
  filter_upwards [ENNReal.eventually_mul_inv_rpow_le hcard (d := 0) (d' := d)
    (NNReal.coe_pos.2 (ENNReal.coe_pos.1 hd))] with ε hε
  calc (coveringNumber ε A : ℝ≥0∞) ≤ A.encard :=
        ENat.toENNReal_le.2 (coveringNumber_le_encard_self A)
    _ ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ) := by simpa using hε

/-- A finite set has lower box-counting dimension zero. -/
theorem _root_.Set.Finite.lowerBoxDim_eq_zero (hA : A.Finite) : lowerBoxDim A = 0 :=
  le_antisymm (lowerBoxDim_le_upperBoxDim.trans_eq hA.upperBoxDim_eq_zero) bot_le

@[simp]
theorem upperBoxDim_empty : upperBoxDim (∅ : Set X) = 0 :=
  finite_empty.upperBoxDim_eq_zero

@[simp]
theorem lowerBoxDim_empty : lowerBoxDim (∅ : Set X) = 0 :=
  finite_empty.lowerBoxDim_eq_zero

@[simp]
theorem upperBoxDim_singleton (x : X) : upperBoxDim ({x} : Set X) = 0 :=
  (finite_singleton x).upperBoxDim_eq_zero

@[simp]
theorem lowerBoxDim_singleton (x : X) : lowerBoxDim ({x} : Set X) = 0 :=
  (finite_singleton x).lowerBoxDim_eq_zero

/-- A bound `N(ε, A) ≤ ε ^ (-d)` at a radius `ε > 0` forces the covering number to be finite. -/
private theorem coveringNumber_ne_top_of_le_inv_rpow {ε d : ℝ≥0} (hε : 0 < ε)
    (h : (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ)) : coveringNumber ε A ≠ ⊤ :=
  fun hN => by
    rw [hN, ENat.toENNReal_top, top_le_iff] at h
    exact ENNReal.rpow_ne_top_of_nonneg d.coe_nonneg
      (ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hε.ne')) h

/-- A set that is not totally bounded has infinite lower box-counting dimension: its covering
numbers are infinite at every small radius. -/
theorem lowerBoxDim_eq_top_of_not_totallyBounded (hA : ¬TotallyBounded A) :
    lowerBoxDim A = ∞ := by
  -- Some radius `ε₀ > 0` admits no finite cover of `A`.
  obtain ⟨ε₀, hε₀, hN⟩ : ∃ ε₀ : ℝ≥0, 0 < ε₀ ∧ coveringNumber ε₀ A = ⊤ := by
    by_contra! h
    refine hA (EMetric.totallyBounded_iff.2 fun r hr => ?_)
    obtain ⟨ε₀, hε₀, hε₀r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr
    obtain ⟨C, -, hCfin, hC, -⟩ :=
      exists_set_encard_eq_coveringNumber (h ε₀ (ENNReal.coe_pos.1 hε₀))
    refine ⟨C, hCfin, (isCover_iff_subset_iUnion_closedEBall.1 hC).trans ?_⟩
    exact iUnion₂_mono fun y _ z hz =>
      mem_eball.2 ((mem_closedEBall.1 hz).trans_lt hε₀r)
  simp only [lowerBoxDim, iInf_eq_top, ENNReal.coe_ne_top, imp_false]
  intro d hd
  obtain ⟨ε, hle, hε⟩ := (hd.and_eventually (Ioo_mem_nhdsGT hε₀)).exists
  exact coveringNumber_ne_top_of_le_inv_rpow hε.1 hle
    (top_unique (hN ▸ coveringNumber_anti hε.2.le))

/-- A set that is not totally bounded has infinite upper box-counting dimension. -/
theorem upperBoxDim_eq_top_of_not_totallyBounded (hA : ¬TotallyBounded A) :
    upperBoxDim A = ∞ :=
  top_unique ((lowerBoxDim_eq_top_of_not_totallyBounded hA).symm.trans_le
    lowerBoxDim_le_upperBoxDim)

/-- For `A ⊆ B` and `d₀ < d`, a bound `N(ε / 2, B) ≤ (ε / 2) ^ (-d₀)` gives
`N(ε, A) ≤ ε ^ (-d)` for all small `ε > 0`. -/
private theorem eventually_coveringNumber_le_of_subset (hAB : A ⊆ B) {d₀ d : ℝ≥0} (hd : d₀ < d) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (coveringNumber (ε / 2) B : ℝ≥0∞) ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ (d₀ : ℝ) →
        (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ) := by
  have h2 : (2 : ℝ≥0∞) ^ (d₀ : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg d₀.coe_nonneg ENNReal.ofNat_ne_top
  filter_upwards [ENNReal.eventually_mul_inv_rpow_le h2 (NNReal.coe_lt_coe.2 hd)] with ε hε hB
  calc (coveringNumber ε A : ℝ≥0∞) ≤ coveringNumber (ε / 2) B :=
        ENat.toENNReal_le.2 (coveringNumber_subset_le hAB)
    _ ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ (d₀ : ℝ) := hB
    _ = 2 ^ (d₀ : ℝ) * (ε : ℝ≥0∞)⁻¹ ^ (d₀ : ℝ) := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ d₀.coe_nonneg]
      simp [ENNReal.coe_div, ENNReal.div_eq_inv_mul, ENNReal.mul_inv]
    _ ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ) := hε

/-- The upper box-counting dimension is monotone in the set. The covering number itself is not,
because the centres of a cover must lie in the set. -/
@[gcongr]
theorem upperBoxDim_mono (hAB : A ⊆ B) : upperBoxDim A ≤ upperBoxDim B := by
  refine upperBoxDim_le_iff.2 fun d hd => ?_
  obtain ⟨d₀, hBd₀, hd₀d⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hd
  have h2 : Tendsto (fun ε : ℝ≥0 => ε / 2) (𝓝[>] 0) (𝓝[>] 0) :=
    (tendsto_const_mul_nhdsGT_zero (inv_pos.2 two_pos)).congr fun ε => inv_mul_eq_div 2 ε
  exact (h2.eventually
    (eventually_coveringNumber_le_of_upperBoxDim_lt hBd₀)).mp
    (eventually_coveringNumber_le_of_subset hAB (ENNReal.coe_lt_coe.1 hd₀d))

/-- The lower box-counting dimension is monotone in the set. -/
@[gcongr]
theorem lowerBoxDim_mono (hAB : A ⊆ B) : lowerBoxDim A ≤ lowerBoxDim B := by
  refine lowerBoxDim_le_iff.2 fun d hd => ?_
  obtain ⟨d₀, hBd₀, hd₀d⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hd
  -- Substituting `ε = 2 ε'` turns the frequent bound for `B` at `ε'` into one at `ε / 2`.
  have hB : ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (coveringNumber (ε / 2) B : ℝ≥0∞) ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ (d₀ : ℝ) :=
    (tendsto_const_mul_nhdsGT_zero two_pos).frequently (p := fun ε : ℝ≥0 =>
      (coveringNumber (ε / 2) B : ℝ≥0∞) ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ (d₀ : ℝ))
      (by simpa using frequently_coveringNumber_le_of_lowerBoxDim_lt hBd₀)
  exact hB.mp (eventually_coveringNumber_le_of_subset hAB (ENNReal.coe_lt_coe.1 hd₀d))

end PseudoEMetricSpace

section EMetricSpace

variable {X : Type*} [EMetricSpace X]

/-- If `N(ε, A) ≤ ε ^ (-d)` at a radius `ε > 0`, then the closed balls of radius `ε` around the
points of a minimal cover of `A` have `∑ (diam)^t ≤ 2 ^ t ε ^ (t - d)` for every `t ≥ 0`. -/
private theorem tsum_ediam_closedEBall_minimalCover_le {A : Set X} {ε d : ℝ≥0} {t : ℝ}
    (ht : 0 ≤ t) (hε : 0 < ε) (h : (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ)) :
    ∑' i : minimalCover ε A, ediam (closedEBall (i : X) ε) ^ t ≤
      2 ^ t * (ε : ℝ≥0∞) ^ (t - d) := by
  have h0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
  calc ∑' i : minimalCover ε A, ediam (closedEBall (i : X) ε) ^ t
      ≤ ∑' _ : minimalCover ε A, (2 * (ε : ℝ≥0∞)) ^ t :=
        tsum_le_tsum fun _ => ENNReal.rpow_le_rpow ediam_closedEBall_le ht
    _ = coveringNumber ε A * (2 * (ε : ℝ≥0∞)) ^ t := by
        rw [ENNReal.tsum_const, ENat.card_coe_set_eq,
          encard_minimalCover (coveringNumber_ne_top_of_le_inv_rpow hε h)]
    _ ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ) * (2 * (ε : ℝ≥0∞)) ^ t := by gcongr
    _ = 2 ^ t * (ε : ℝ≥0∞) ^ (t - d) := by
        rw [ENNReal.rpow_sub _ _ h0 ENNReal.coe_ne_top, ENNReal.mul_rpow_of_nonneg _ _ ht,
          ENNReal.inv_rpow, div_eq_mul_inv]
        ring

/-- The covers behind the box-counting dimensions control the Hausdorff measure: if
`N(ε, A) ≤ ε ^ (-d)` for arbitrarily small `ε > 0`, then `μH[t] A = 0` for every `t > d`. -/
theorem hausdorffMeasure_eq_zero_of_frequently_coveringNumber_le [MeasurableSpace X]
    [BorelSpace X] {A : Set X} {d : ℝ≥0} {t : ℝ}
    (h : ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0, (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ))
    (hdt : (d : ℝ) < t) : μH[t] A = 0 := by
  have ht : 0 < t := d.coe_nonneg.trans_lt hdt
  -- `l`: the radii `ε → 0⁺` at which the covering number is bounded by `ε ^ (-d)`.
  set l := 𝓝[>] (0 : ℝ≥0) ⊓ 𝓟 {ε | (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ)}
  have : l.NeBot := frequently_iff_neBot.1 h
  have hpos : ∀ᶠ ε in l, 0 < ε := mem_inf_of_left self_mem_nhdsWithin
  have hgood : ∀ᶠ ε in l, 0 < ε ∧ (coveringNumber ε A : ℝ≥0∞) ≤ (ε : ℝ≥0∞)⁻¹ ^ (d : ℝ) :=
    hpos.and (mem_inf_of_right (mem_principal_self _))
  have hcoe : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞)) l (𝓝 0) :=
    (ENNReal.continuous_coe.tendsto' 0 0 ENNReal.coe_zero).mono_left
      (inf_le_left.trans nhdsWithin_le_nhds)
  have : ∀ ε : ℝ≥0, Countable (minimalCover ε A) := fun _ =>
    finite_minimalCover.countable.to_subtype
  -- The bounds `2 ^ t ε ^ (t - d)` on the sums over the covers tend to `0`.
  have hlim : Tendsto (fun ε : ℝ≥0 => 2 ^ t * (ε : ℝ≥0∞) ^ (t - d)) l (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul
      ((ENNReal.continuous_rpow_const (y := t - d)).tendsto 0 |>.comp hcoe)
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg ht.le ENNReal.ofNat_ne_top)) (a := 2 ^ t)
    rwa [ENNReal.zero_rpow_of_pos (sub_pos.2 hdt), mul_zero] at h
  refine le_antisymm ?_ bot_le
  calc μH[t] A
      ≤ liminf (fun ε : ℝ≥0 => ∑' i : minimalCover ε A, ediam (closedEBall (i : X) ε) ^ t) l :=
        Measure.hausdorffMeasure_le_liminf_tsum t A (fun ε : ℝ≥0 => 2 * (ε : ℝ≥0∞))
          (by simpa using ENNReal.Tendsto.const_mul hcoe (Or.inr ENNReal.ofNat_ne_top) (a := 2))
          (fun ε (i : minimalCover ε A) => closedEBall (i : X) ε)
          (Eventually.of_forall fun _ _ => ediam_closedEBall_le)
          (hgood.mono fun ε hε => by
            simpa only [iUnion_coe_set] using isCover_iff_subset_iUnion_closedEBall.1
              (isCover_minimalCover (coveringNumber_ne_top_of_le_inv_rpow hε.1 hε.2)))
    _ ≤ liminf (fun ε : ℝ≥0 => 2 ^ t * (ε : ℝ≥0∞) ^ (t - d)) l :=
        liminf_le_liminf (hgood.mono fun _ hε =>
          tsum_ediam_closedEBall_minimalCover_le ht.le hε.1 hε.2)
    _ = 0 := hlim.liminf_eq

/-- **The Hausdorff dimension is at most the lower box-counting dimension**, in every extended
metric space (Bishop and Peres, inequality (1.2.3)). -/
theorem dimH_le_lowerBoxDim (A : Set X) : dimH A ≤ lowerBoxDim A := by
  borelize X
  refine dimH_le fun t ht => le_of_not_gt fun hlt => ?_
  obtain ⟨d, hAd, hdt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have h0 := hausdorffMeasure_eq_zero_of_frequently_coveringNumber_le
    (frequently_coveringNumber_le_of_lowerBoxDim_lt hAd)
    (NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hdt))
  rw [h0] at ht
  exact ENNReal.zero_ne_top ht

/-- The Hausdorff dimension is at most the upper box-counting dimension. -/
theorem dimH_le_upperBoxDim (A : Set X) : dimH A ≤ upperBoxDim A :=
  (dimH_le_lowerBoxDim A).trans lowerBoxDim_le_upperBoxDim

end EMetricSpace

end TauCeti
