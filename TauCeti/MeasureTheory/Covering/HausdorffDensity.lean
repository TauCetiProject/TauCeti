/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Covering.Vitali
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.MeasureTheory.Measure.Hausdorff

/-!
# Upper densities and Hausdorff measure

Let `μ` be a measure on a metric space `X` and `d ≥ 0`. If at every point `x` of a set `A` the
measure of arbitrarily small closed balls satisfies `μ (closedBall x r) ≥ c (2 r) ^ d`, that is, if
the `d`-dimensional upper density of `μ` is at least `c` on `A`, then `μ` dominates `c` times the
`d`-dimensional Hausdorff measure on `A`:

`c * μH[d] A ≤ μ U` for every open `U ⊇ A`, hence `c * μH[d] A ≤ μ A` if `μ` is outer regular.

Neither `A` nor `μ` needs any further regularity, and `c` is not required to be finite. The
constant is sharp: no covering constant is lost.

Conversely, if at every point `x` of `A` all small closed balls satisfy
`μ (closedBall x r) ≤ c (2 r) ^ d` with `c ≠ 0, ∞`, then `μ A ≤ 2 ^ d c μH[d] A`. A set of
diameter `ρ` meeting `A` at `x` lies in `closedBall x ρ`, so here a factor `2 ^ d` is lost. In
particular `μ` vanishes on the `μH[d]`-null subsets of `A`.

As a consequence, a null-measurable set `A` of finite `d`-dimensional Hausdorff measure has upper
density zero at almost every point outside it:
`μH[d] (A ∩ closedBall x r) / (2 r) ^ d → 0` as `r → 0⁺` for `μH[d]`-almost every `x ∉ A`.

These comparisons between densities and Hausdorff measure are the measure-theoretic input of the
density theorem for rectifiable sets and of the identification of the perimeter measure with the
Hausdorff measure of the reduced boundary. Their Euclidean normalizations, with `ω_k r ^ k` in
place of `(2 r) ^ k`, are in `TauCeti.Geometry.Euclidean.Volume.Measure`.

## Main results

* `MeasureTheory.Measure.mul_hausdorffMeasure_le_measure_of_isOpen` and
  `MeasureTheory.Measure.mul_hausdorffMeasure_le_measure`: a measure whose upper density is at
  least `c` on `A` dominates `c • μH[d]` on `A`.
* `MeasureTheory.Measure.measure_le_mul_hausdorffMeasure`: a measure with
  `μ (closedBall x r) ≤ c (2 r) ^ d` for all small `r` at every point `x` of `A`, where
  `c ≠ 0, ∞`, is at most `2 ^ d c • μH[d]` on `A`.
* `TauCeti.ae_tendsto_hausdorffMeasure_inter_closedBall_div`: zero density outside a
  null-measurable set of finite Hausdorff measure.

## Implementation notes

The domination is proved with the Vitali covering lemma
`Vitali.exists_disjoint_subfamily_covering_enlargement`, applied to the closed balls inside `U` on
which `μ` is large. The selected disjoint balls are countable because they have positive measure
inside a set of finite measure, and the sum of `(2 r) ^ d` over them is at most `μ U / c`. Finitely
many of them, together with the threefold enlargements of the others, cover `A`, and the sum over
the enlargements tends to zero. The reverse comparison needs no covering lemma: on the part of `A`
where the bound holds below a fixed radius, `μ` is bounded on small sets by `2 ^ d c diam ^ d`,
which is compared with the Hausdorff measure by `OuterMeasure.le_mkMetric`.

## References

* H. Federer, *Geometric Measure Theory*, 2.10.19 (densities and Hausdorff measures).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorems 6.2 and 6.9.
-/

public section

open Filter Metric MeasureTheory Measure Set
open scoped ENNReal NNReal Topology

universe u

namespace TauCeti

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A disjoint family `u` of closed balls `closedBall p.1 p.2` of positive radii inside a set `U` of
finite measure, each with `c (2 r) ^ d ≤ μ (closedBall x r)` for some `c ≠ 0`, is countable, and
`∑ (2 r) ^ d ≤ μ U / c` over it. -/
private lemma countable_and_tsum_le_of_pairwiseDisjoint (μ : Measure X) {d : ℝ}
    {c : ℝ≥0∞} (hc0 : c ≠ 0) {U : Set X} (hUtop : μ U ≠ ∞) {u : Set (X × ℝ)}
    (hud : u.PairwiseDisjoint fun p => closedBall p.1 p.2)
    (hu : ∀ p ∈ u, 0 < p.2 ∧ closedBall p.1 p.2 ⊆ U ∧
      c * ENNReal.ofReal (2 * p.2) ^ d ≤ μ (closedBall p.1 p.2)) :
    u.Countable ∧ ∑' p : u, ENNReal.ofReal (2 * p.1.2) ^ d ≤ μ U / c := by
  -- Disjoint balls of positive measure inside `U` are countable.
  have hcount : u.Countable := by
    have := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top μ
      (As := fun p : u => closedBall p.1.1 p.1.2) (fun _ => measurableSet_closedBall)
      (fun p q hpq => hud p.2 q.2 (Subtype.coe_ne_coe.2 hpq))
      (ne_top_of_le_ne_top hUtop (measure_mono (iUnion_subset fun p => (hu _ p.2).2.1)))
    have hall : {p : u | 0 < μ (closedBall p.1.1 p.1.2)} = univ :=
      eq_univ_of_forall fun p => (ENNReal.mul_pos hc0 (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.2 (by linarith [(hu _ p.2).1])) ENNReal.ofReal_ne_top).ne').trans_le
          (hu _ p.2).2.2
    rw [hall] at this
    exact Set.countable_coe_iff.1 (countable_univ_iff.1 this)
  refine ⟨hcount, ?_⟩
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inr hUtop), ← ENNReal.tsum_mul_right]
  calc ∑' p : u, ENNReal.ofReal (2 * p.1.2) ^ d * c ≤ ∑' p : u, μ (closedBall p.1.1 p.1.2) :=
        tsum_le_tsum fun p => by rw [mul_comm]; exact (hu _ p.2).2.2
    _ = μ (⋃ p ∈ u, closedBall p.1 p.2) :=
        (measure_biUnion hcount hud fun _ _ => measurableSet_closedBall).symm
    _ ≤ μ U := measure_mono (iUnion₂_subset fun p hp => (hu p hp).2.1)

/-- Tripling the radii `ρ i` outside a finite set `F` multiplies their terms of
`∑ (2 ρ i) ^ d` by `3 ^ d`, so the new sum is at most `∑ (2 ρ i) ^ d + 3 ^ d ∑_{i ∉ F} (2 ρ i) ^ d`.
-/
private lemma tsum_ofReal_two_mul_ite_le {ι : Type*} [DecidableEq ι] (F : Finset ι) (ρ : ι → ℝ)
    (d : ℝ) :
    ∑' i, ENNReal.ofReal (2 * if i ∈ F then ρ i else 3 * ρ i) ^ d ≤
      ∑' i, ENNReal.ofReal (2 * ρ i) ^ d +
        3 ^ d * ∑' i : {i // i ∉ F}, ENNReal.ofReal (2 * ρ i) ^ d := by
  have h3 (i : ι) : ENNReal.ofReal (2 * (3 * ρ i)) ^ d = 3 ^ d * ENNReal.ofReal (2 * ρ i) ^ d := by
    rw [mul_left_comm, ENNReal.ofReal_mul_rpow zero_le_three, ENNReal.ofReal_ofNat]
  calc _ ≤ ∑' i, (ENNReal.ofReal (2 * ρ i) ^ d +
        {i | i ∉ F}.indicator (fun i => 3 ^ d * ENNReal.ofReal (2 * ρ i) ^ d) i) :=
        tsum_le_tsum fun i => by
          by_cases hi : i ∈ F
          · simp [hi]
          · rw [ite_eq_right hi, h3, indicator_of_mem (by exact hi)]
            exact le_add_self
    _ = _ := by
        rw [tsum_add, ← tsum_subtype, ENNReal.tsum_mul_left]
        -- `↥{i | i ∉ F}` is notation for the subtype `{i // i ∉ F}`.
        rfl

/-- If `μ (closedBall x ρ) ≤ c (2 ρ) ^ d` for every `x ∈ B` and every radius `ρ ∈ [0, ε)`, where
`c ≠ 0, ∞`, then `μ B ≤ 2 ^ d * c * μH[d] B`: a set of diameter `ρ` meeting `B` at `x` lies in
`closedBall x ρ`. -/
private lemma measure_le_mul_hausdorffMeasure_of_forall_closedBall_le (μ : Measure X) {d : ℝ}
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) {B : Set X} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x ∈ B, ∀ ρ : ℝ, 0 ≤ ρ → ρ < ε →
      μ (closedBall x ρ) ≤ c * ENNReal.ofReal (2 * ρ) ^ d) :
    μ B ≤ 2 ^ d * c * μH[d] B := by
  have h2 : (2 : ℝ≥0∞) ^ d * c ≠ 0 :=
    mul_ne_zero (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne' hc0
  have h2top : (2 : ℝ≥0∞) ^ d * c ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero two_ne_zero ENNReal.ofNat_ne_top) hc
  -- Every set of diameter at most `ε / 2` meets `B` in measure at most `2 ^ d c diam ^ d`.
  have hle : μ.toOuterMeasure.restrict B ≤ OuterMeasure.mkMetric fun r => 2 ^ d * c * r ^ d := by
    refine OuterMeasure.le_mkMetric _ _ (ENNReal.ofReal (ε / 2)) (by simpa using hε) fun s hs => ?_
    rw [OuterMeasure.restrict_apply]
    rcases (s ∩ B).eq_empty_or_nonempty with he | ⟨x, hxs, hxB⟩
    · simp [he]
    have hstop : ediam s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
    have hsub : s ⊆ closedBall x (ediam s).toReal := fun y hy => by
      rw [mem_closedBall, dist_edist]
      exact ENNReal.toReal_mono hstop (edist_le_ediam_of_mem hy hxs)
    have hρε : (ediam s).toReal < ε :=
      (ENNReal.toReal_le_of_le_ofReal (by positivity) hs).trans_lt (half_lt_self hε)
    calc μ (s ∩ B) ≤ μ (closedBall x (ediam s).toReal) :=
          measure_mono (inter_subset_left.trans hsub)
      _ ≤ c * ENNReal.ofReal (2 * (ediam s).toReal) ^ d := h x hxB _ ENNReal.toReal_nonneg hρε
      _ = 2 ^ d * c * ediam s ^ d := by
        rw [ENNReal.ofReal_mul_rpow zero_le_two, ENNReal.ofReal_toReal hstop, ENNReal.ofReal_ofNat]
        ring
  calc μ B = μ.toOuterMeasure.restrict B B := by
        rw [OuterMeasure.restrict_apply, inter_self, toOuterMeasure_apply]
    _ ≤ OuterMeasure.mkMetric (fun r => 2 ^ d * c * r ^ d) B := hle _
    _ = Measure.mkMetric (fun r => 2 ^ d * c * r ^ d) B := by
        rw [← Measure.mkMetric_toOuterMeasure, toOuterMeasure_apply]
    _ ≤ ((2 ^ d * c) • μH[d]) B :=
        Measure.mkMetric_mono_smul h2top h2 (Eventually.of_forall fun _ => le_rfl) _
    _ = 2 ^ d * c * μH[d] B := by rw [smul_apply, smul_eq_mul]

end TauCeti

namespace MeasureTheory.Measure

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Density comparison for Hausdorff measure**, open-set form. If at every point `x` of `A`
there are arbitrarily small radii `r > 0` with `c (2 r) ^ d ≤ μ (closedBall x r)`, then
`c * μH[d] A ≤ μ U` for every open set `U` containing `A`. -/
theorem mul_hausdorffMeasure_le_measure_of_isOpen (μ : Measure X) {d : ℝ} (hd : 0 ≤ d)
    {c : ℝ≥0∞} {A U : Set X} (hU : IsOpen U) (hAU : A ⊆ U)
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0, c * ENNReal.ofReal (2 * r) ^ d ≤ μ (closedBall x r)) :
    c * μH[d] A ≤ μ U := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  rcases eq_or_ne (μ U) ∞ with hUtop | hUtop
  · simp [hUtop]
  refine le_trans ?_ (ENNReal.mul_div_le (a := c) (b := μ U))
  gcongr
  refine TauCeti.hausdorffMeasure_le_of_forall_exists_closedBall_cover hd fun δ hδ ε hε => ?_
  -- The admissible balls: centred in `A`, of radius at most `δ / 3`, inside `U`, and large for `μ`.
  set T : Set (X × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ p.2 ≤ δ / 3 ∧ closedBall p.1 p.2 ⊆ U ∧
    c * ENNReal.ofReal (2 * p.2) ^ d ≤ μ (closedBall p.1 p.2)}
  have fine : ∀ x ∈ A, ∀ V ∈ 𝓝 x, ∃ r, (x, r) ∈ T ∧ closedBall x r ⊆ V := by
    intro x hx V hV
    obtain ⟨r, hr, hrV, hrδ⟩ := ((h x hx).and_eventually
      ((eventually_nhdsWithin_of_eventually_nhds (eventually_closedBall_subset
        (inter_mem hV (hU.mem_nhds (hAU hx))))).and
          (Ioo_mem_nhdsGT (by positivity : 0 < δ / 3)))).exists
    exact ⟨r, ⟨hx, hrδ.1, hrδ.2.le, hrV.trans inter_subset_right, hr⟩, hrV.trans inter_subset_left⟩
  obtain ⟨u, huT, hud, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun p : X × ℝ => closedBall p.1 p.2) T (fun p => p.2) 2 one_lt_two
    (fun p hp => hp.2.1.le) (δ / 3) (fun p hp => hp.2.2.1)
    (fun p hp => nonempty_closedBall.2 hp.2.1.le)
  obtain ⟨hu, hsum⟩ := TauCeti.countable_and_tsum_le_of_pairwiseDisjoint μ hc0 hUtop hud
    fun p hp => ⟨(huT hp).2.1, (huT hp).2.2.2.1, (huT hp).2.2.2.2⟩
  have : Countable u := hu.to_subtype
  have h3 : (3 : ℝ≥0∞) ^ d ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hd (by simp)
  -- Choose a finite subfamily `F` whose complement has a small sum.
  obtain ⟨F, hF⟩ := ((ENNReal.tendsto_nhds_zero.1 (ENNReal.tendsto_tsum_compl_atTop_zero
    (ne_top_of_le_ne_top (ENNReal.div_lt_top hUtop hc0).ne hsum)) _
    (ENNReal.div_pos hε.ne' h3)).exists)
  -- Cover by the balls in `F` and the threefold enlargements of the other selected balls.
  classical
  refine ⟨u, inferInstance, fun p => p.1.1, fun p => if p ∈ F then p.1.2 else 3 * p.1.2,
    fun p => ?_, fun x hx => ?_, ?_⟩
  · have := (huT p.2).2.2.1
    dsimp only
    split_ifs <;> linarith [(huT p.2).2.1]
  · by_cases hxF : x ∈ ⋃ p ∈ F, closedBall p.1.1 p.1.2
    · obtain ⟨p, hpF, hxp⟩ := mem_iUnion₂.1 hxF
      exact mem_iUnion.2 ⟨p, by simpa [hpF] using hxp⟩
    obtain ⟨r, hrT, hrF⟩ := fine x hx _ ((isClosed_biUnion_finset fun p _ =>
      isClosed_closedBall).isOpen_compl.mem_nhds hxF)
    obtain ⟨b, hbu, ⟨y, hyx, hyb⟩, hrb⟩ := hucov (x, r) hrT
    have hbF : (⟨b, hbu⟩ : u) ∉ F := fun hbF => hrF hyx (mem_iUnion₂.2 ⟨_, hbF, hyb⟩)
    refine mem_iUnion.2 ⟨⟨b, hbu⟩, ?_⟩
    simp only [hbF, ↓reduceIte, mem_closedBall]
    linarith [dist_triangle x y b.1, mem_closedBall'.1 hyx, mem_closedBall.1 hyb]
  · calc _ ≤ _ := TauCeti.tsum_ofReal_two_mul_ite_le F (fun p : u => p.1.2) d
      _ ≤ μ U / c + 3 ^ d * (ε / 3 ^ d) := by gcongr
      _ ≤ μ U / c + ε := by gcongr; exact ENNReal.mul_div_le

/-- **Density comparison for Hausdorff measure**, outer regular form. If `μ` is outer regular
and at every point `x` of `A` there are arbitrarily small radii `r > 0` with
`c (2 r) ^ d ≤ μ (closedBall x r)`, then `c * μH[d] A ≤ μ A`. -/
theorem mul_hausdorffMeasure_le_measure (μ : Measure X) [μ.OuterRegular] {d : ℝ} (hd : 0 ≤ d)
    {c : ℝ≥0∞} {A : Set X}
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0, c * ENNReal.ofReal (2 * r) ^ d ≤ μ (closedBall x r)) :
    c * μH[d] A ≤ μ A := by
  refine le_of_forall_gt fun b hb => ?_
  obtain ⟨U, hAU, hU, hUb⟩ := A.exists_isOpen_lt_of_lt b hb
  exact (mul_hausdorffMeasure_le_measure_of_isOpen μ hd hU hAU h).trans_lt hUb

/-- **Upper density comparison for Hausdorff measure.** If at every point `x` of `A` all small
closed balls satisfy `μ (closedBall x r) ≤ c (2 r) ^ d`, where `c ≠ 0, ∞`, then
`μ A ≤ 2 ^ d * c * μH[d] A`. -/
theorem measure_le_mul_hausdorffMeasure (μ : Measure X) {d : ℝ} {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) {A : Set X}
    (h : ∀ x ∈ A, ∀ᶠ r in 𝓝[>] 0, μ (closedBall x r) ≤ c * ENNReal.ofReal (2 * r) ^ d) :
    μ A ≤ 2 ^ d * c * μH[d] A := by
  -- `B j`: the points of `A` at which the bound holds for every radius in `(0, 1 / (j + 1))`.
  set B : ℕ → Set X := fun j => {x | x ∈ A ∧ ∀ r ∈ Ioo (0 : ℝ) (1 / (j + 1)),
    μ (closedBall x r) ≤ c * ENNReal.ofReal (2 * r) ^ d}
  have hBmono : Monotone B := fun i j hij x hx => ⟨hx.1, fun r hr => hx.2 r
    ⟨hr.1, hr.2.trans_le (one_div_le_one_div_of_le (by positivity) (by gcongr))⟩⟩
  have hAB : A ⊆ ⋃ j, B j := fun x hx => by
    obtain ⟨ε, hε, hεA⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' one_pos).1 (h x hx)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    exact mem_iUnion.2 ⟨j, hx, fun r hr => hεA ⟨hr.1, hr.2.trans hj⟩⟩
  refine (measure_mono hAB).trans ((hBmono.measure_iUnion (μ := μ)).trans_le (iSup_le fun j => ?_))
  -- The bound extends from radii in `(0, 1 / (j + 1))` to radii in `[0, 1 / (j + 1))`.
  have hcont : Continuous fun r : ℝ => c * ENNReal.ofReal (2 * r) ^ d :=
    (ENNReal.continuous_const_mul hc).comp (ENNReal.continuous_rpow_const.comp
      (ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  refine (TauCeti.measure_le_mul_hausdorffMeasure_of_forall_closedBall_le μ hc0 hc
    (B := B j) (ε := 1 / (j + 1)) (by positivity) fun x hx ρ hρ hρε =>
      measure_closedBall_le_of_frequently_le μ hcont.continuousWithinAt
        (eventually_of_mem (Ioo_mem_nhdsGT hρε) fun r hr =>
          hx.2 r ⟨hρ.trans_lt hr.1, hr.2⟩).frequently).trans ?_
  gcongr
  exact fun x hx => hx.1

end MeasureTheory.Measure

namespace TauCeti

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A measurable set of finite `μH[d]` measure has upper `d`-density less than `c` at
`μH[d]`-almost every point outside it, for each `c ≠ 0`. -/
private lemma hausdorffMeasure_setOf_frequently_le_eq_zero {d : ℝ} (hd : 0 ≤ d) {A : Set X}
    (hA : MeasurableSet A) (hAfin : μH[d] A ≠ ∞) {c : ℝ≥0∞} (hc : c ≠ 0) :
    μH[d] {x | x ∉ A ∧ ∃ᶠ r in 𝓝[>] 0,
      c * ENNReal.ofReal (2 * r) ^ d ≤ μH[d] (A ∩ closedBall x r)} = 0 := by
  set B := {x | x ∉ A ∧ ∃ᶠ r in 𝓝[>] 0,
    c * ENNReal.ofReal (2 * r) ^ d ≤ μH[d] (A ∩ closedBall x r)}
  suffices c * μH[d] B = 0 by simpa [hc] using this
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  -- Approximate `A` from inside by a closed set `F`, using the finite measure `μH[d]|_A`.
  have : IsFiniteMeasure (μH[d].restrict A) :=
    ⟨by rw [restrict_apply_univ]; exact hAfin.lt_top⟩
  obtain ⟨F, hFA, hF, hAF⟩ := hA.exists_isClosed_sdiff_lt (μ := μH[d].restrict A)
    (by rwa [restrict_apply_self]) (ENNReal.coe_ne_zero.2 hε.ne')
  rw [Measure.restrict_apply (hA.diff hF.measurableSet), inter_eq_left.2 sdiff_subset] at hAF
  -- Near a point outside `F`, the part of `A` in a small ball lies in `A \ F`.
  have key := mul_hausdorffMeasure_le_measure_of_isOpen (μH[d].restrict (A \ F)) hd
    hF.isOpen_compl (c := c) (A := B) (fun x hx => fun hxF => hx.1 (hFA hxF)) fun x hx =>
      hx.2.mp ((eventually_nhdsWithin_of_eventually_nhds (eventually_closedBall_subset
        (hF.isOpen_compl.mem_nhds fun hxF => hx.1 (hFA hxF)))).mono fun r hr hle => ?_)
  · rw [Measure.restrict_apply hF.isOpen_compl.measurableSet,
      show Fᶜ ∩ (A \ F) = A \ F by grind] at key
    simpa using key.trans hAF.le
  · rwa [Measure.restrict_apply measurableSet_closedBall,
      show closedBall x r ∩ (A \ F) = A ∩ closedBall x r by grind]

/-- **Zero density outside a set.** A null-measurable set `A` of finite `d`-dimensional Hausdorff
measure has upper `d`-density zero at almost every point outside it:
`μH[d] (A ∩ closedBall x r) / (2 r) ^ d → 0` as `r → 0⁺` for `μH[d]`-almost every `x ∉ A`. -/
theorem ae_tendsto_hausdorffMeasure_inter_closedBall_div {d : ℝ} (hd : 0 ≤ d) {A : Set X}
    (hA : NullMeasurableSet A μH[d]) (hAfin : μH[d] A ≠ ∞) :
    ∀ᵐ x ∂μH[d], x ∉ A → Tendsto (fun r => μH[d] (A ∩ closedBall x r) /
      ENNReal.ofReal (2 * r) ^ d) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨A₀, hA₀A, hA₀, hA₀ae⟩ := hA.exists_measurable_subset_ae_eq
  have hball (x : X) (r : ℝ) : μH[d] (A ∩ closedBall x r) = μH[d] (A₀ ∩ closedBall x r) :=
    measure_congr (hA₀ae.symm.inter (ae_eq_refl _))
  have hnull := fun n : ℕ => hausdorffMeasure_setOf_frequently_le_eq_zero hd hA₀
    (ne_top_of_le_ne_top hAfin (measure_mono hA₀A)) (c := (n : ℝ≥0∞)⁻¹) (by simp)
  filter_upwards [ae_all_iff.2 fun n => measure_eq_zero_iff_ae_notMem.1 (hnull n)]
    with x hx hxA
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  have := hx n
  simp only [not_and, not_frequently, not_le] at this
  filter_upwards [this fun hxA₀ => hxA (hA₀A hxA₀)] with r hr
  rw [hball]
  exact ENNReal.div_le_of_le_mul (hr.le.trans (by gcongr))

end TauCeti
