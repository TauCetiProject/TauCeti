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

Let `μ` be a measure on a metric space `X` and `d : ℝ`. If at every point `x` of a set `A` the
measure of arbitrarily small closed balls satisfies `μ (closedBall x r) ≥ c (2 r) ^ d`, that is, if
the `d`-dimensional upper density of `μ` is at least `c` on `A`, then `μ` dominates `c` times the
`d`-dimensional Hausdorff measure on `A`:

`c * μH[d] A ≤ μ U` for every open `U ⊇ A`, hence `c * μH[d] A ≤ μ A` if `μ` is outer regular.

Neither `A` nor `μ` needs any further regularity, and `c` is not required to be finite. The
constant is sharp: no covering constant is lost.

Applied on small open sets of finite `μ`-measure, this gives local finiteness: if `μ` is locally
finite and every point has a neighbourhood on whose part of `A` the density is at least a fixed
`c ≠ 0`, then `μH[d]` restricted to `A` is locally finite.

Conversely, if at every point `x` of `A` all small closed balls satisfy
`μ (closedBall x r) ≤ c (2 r) ^ d` with `c ≠ 0, ∞`, then `μ A ≤ 2 ^ d c μH[d] A`. A set of
diameter `ρ` meeting `A` at `x` lies in `closedBall x ρ`, so here a factor `2 ^ d` is lost. In
particular `μ` vanishes on the `μH[d]`-null subsets of `A`. No constant is lost when the bound is
known for all small sets rather than for balls: if every set `t ∋ x` of small diameter satisfies
`μ t ≤ c * ediam t ^ d` at every `x ∈ A`, then `μ A ≤ c μH[d] A`; this small-set comparison
holds in any extended metric space.

As a consequence, an outer regular measure `μ` has `d`-density zero at `μH[d]`-almost every point
of any `μ`-null set (`MeasureTheory.Measure.ae_tendsto_measure_closedBall_div_of_measure_eq_zero`),
and a null-measurable set `A` of finite `d`-dimensional Hausdorff measure has upper density zero at
almost every point outside it:
`μH[d] (A ∩ closedBall x r) / (2 r) ^ d → 0` as `r → 0⁺` for `μH[d]`-almost every `x ∉ A`.

These comparisons between densities and Hausdorff measure are the measure-theoretic input of the
density theorem for rectifiable sets and of the identification of the perimeter measure with the
Hausdorff measure of the reduced boundary. Their Euclidean normalizations, with `ω_k r ^ k` in
place of `(2 r) ^ k`, are in `TauCeti.Geometry.Euclidean.Volume.Measure`.

## Main results

* `MeasureTheory.Measure.mul_hausdorffMeasure_le_measure_of_isOpen` and
  `MeasureTheory.Measure.mul_hausdorffMeasure_le_measure`: a measure whose upper density is at
  least `c` on `A` dominates `c • μH[d]` on `A`.
* `MeasureTheory.Measure.frequently_ofReal_div_mul_rpow_le_measure_closedBall`: a lower bound
  `c ρ ^ d ≤ μ (closedBall y ρ)` for all radii `0 < ρ ≤ ρ₀` gives the density bound
  `(c / 2 ^ d) (2 r) ^ d ≤ μ (closedBall y r)` for arbitrarily small `r`.
* `MeasureTheory.Measure.isLocallyFiniteMeasure_restrict_hausdorffMeasure` and
  `MeasureTheory.Measure.isLocallyFiniteMeasure_restrict_hausdorffMeasure_of_ofReal_mul_pow_le`:
  if a locally finite measure has upper density bounded below on `A`, locally uniformly, then `A`
  has locally finite Hausdorff measure.
* `MeasureTheory.Measure.measure_le_mul_hausdorffMeasure`: a measure with
  `μ (closedBall x r) ≤ c (2 r) ^ d` for all small `r` at every point `x` of `A`, where
  `c ≠ 0, ∞`, is at most `2 ^ d c • μH[d]` on `A`.
* `MeasureTheory.Measure.measure_le_mul_hausdorffMeasure_of_le_mul_ediam_rpow`: a measure with
  `μ t ≤ c * ediam t ^ d` for all small sets `t` containing a point of `A`, where `c ≠ 0, ∞`, is at
  most `c • μH[d]` on `A`.
* `MeasureTheory.Measure.ae_tendsto_measure_closedBall_div_of_measure_eq_zero`: an outer regular
  measure has `d`-density zero at `μH[d]`-almost every point of a null set.
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
which is compared with the Hausdorff measure by `OuterMeasure.le_mkMetric`. The same comparison
proves the version for small sets, from which the version for balls follows.

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
    u.Countable ∧ ∑' p : u, ENNReal.ofReal (2 * p.val.2) ^ d ≤ μ U / c := by
  -- Disjoint balls of positive measure inside `U` are countable.
  have hcount : u.Countable := by
    have := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top μ
      (As := fun p : u => closedBall p.val.1 p.val.2) (fun _ => measurableSet_closedBall)
      (fun p q hpq => hud p.property q.property (Subtype.coe_ne_coe.2 hpq))
      (ne_top_of_le_ne_top hUtop (measure_mono (iUnion_subset fun p => (hu _ p.property).2.1)))
    have hall : {p : u | 0 < μ (closedBall p.val.1 p.val.2)} = univ :=
      eq_univ_of_forall fun p => (ENNReal.mul_pos hc0 (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.2 (by linarith
            [(hu _ p.property).1])) ENNReal.ofReal_ne_top).ne').trans_le
          (hu _ p.property).2.2
    rw [hall] at this
    exact Set.countable_coe_iff.1 (countable_univ_iff.1 this)
  refine ⟨hcount, ?_⟩
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inr hUtop), ← ENNReal.tsum_mul_right]
  calc ∑' p : u, ENNReal.ofReal (2 * p.val.2) ^ d * c ≤ ∑' p : u, μ (closedBall p.val.1 p.val.2) :=
        tsum_le_tsum fun p => by rw [mul_comm]; exact (hu _ p.property).2.2
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

end TauCeti

namespace MeasureTheory.Measure

section EMetricSpace

variable {X : Type u} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Upper comparison with Hausdorff measure from small sets.** If every point `x` of `A` has a
scale `ε > 0` such that every set `t` containing `x` with `ediam t < ε` satisfies
`μ t ≤ c * ediam t ^ d`, where `c ≠ 0, ∞`, then `μ A ≤ c * μH[d] A`. The sets in a cover of `A`
that meet `A` are themselves estimated, so no covering constant is lost. -/
theorem measure_le_mul_hausdorffMeasure_of_le_mul_ediam_rpow (μ : Measure X) {d : ℝ}
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) {A : Set X}
    (h : ∀ x ∈ A, ∃ ε : ℝ≥0∞, 0 < ε ∧
      ∀ t : Set X, x ∈ t → ediam t < ε → μ t ≤ c * ediam t ^ d) :
    μ A ≤ c * μH[d] A := by
  choose! ε hε hεA using h
  -- `B j`: the points of `A` whose scale exceeds `1 / (j + 1)`.
  set B : ℕ → Set X := fun j => {x | x ∈ A ∧ ((j : ℝ≥0∞) + 1)⁻¹ < ε x}
  have hBmono : Monotone B := fun i j hij x hx =>
    ⟨hx.1, lt_of_le_of_lt (ENNReal.inv_le_inv.2 (by gcongr)) hx.2⟩
  have hAB : A ⊆ ⋃ j, B j := fun x hx => by
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt (hε x hx).ne'
    exact mem_iUnion.2 ⟨j, hx, lt_of_le_of_lt (ENNReal.inv_le_inv.2 le_self_add) hj⟩
  refine (measure_mono hAB).trans ((hBmono.measure_iUnion (μ := μ)).trans_le (iSup_le fun j => ?_))
  -- Every set of diameter at most `1 / (j + 1)` meets `B j` in measure at most `c diam ^ d`.
  have hle : μ.toOuterMeasure.restrict (B j) ≤ OuterMeasure.mkMetric fun r => c * r ^ d := by
    refine OuterMeasure.le_mkMetric _ _ ((j : ℝ≥0∞) + 1)⁻¹ (by simp) fun s hs => ?_
    rw [OuterMeasure.restrict_apply]
    rcases (s ∩ B j).eq_empty_or_nonempty with he | ⟨x, hxs, hxB⟩
    · simp [he]
    exact (measure_mono inter_subset_left).trans (hεA x hxB.1 s hxs (hs.trans_lt hxB.2))
  calc μ (B j) = μ.toOuterMeasure.restrict (B j) (B j) := by
        rw [OuterMeasure.restrict_apply, inter_self, toOuterMeasure_apply]
    _ ≤ OuterMeasure.mkMetric (fun r => c * r ^ d) (B j) := hle _
    _ = Measure.mkMetric (fun r => c * r ^ d) (B j) := by
        rw [← Measure.mkMetric_toOuterMeasure, toOuterMeasure_apply]
    _ ≤ (c • μH[d]) (B j) :=
        Measure.mkMetric_mono_smul hc hc0 (Eventually.of_forall fun _ => le_rfl) _
    _ ≤ c * μH[d] A := by
        rw [smul_apply, smul_eq_mul]
        gcongr
        exact fun x hx => hx.1

end EMetricSpace

section MetricSpace

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Density comparison for Hausdorff measure**, open-set form. If at every point `x` of `A`
there are arbitrarily small radii `r > 0` with `c (2 r) ^ d ≤ μ (closedBall x r)`, then
`c * μH[d] A ≤ μ U` for every open set `U` containing `A`. -/
theorem mul_hausdorffMeasure_le_measure_of_isOpen (μ : Measure X) {d : ℝ}
    {c : ℝ≥0∞} {A U : Set X} (hU : IsOpen U) (hAU : A ⊆ U)
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0, c * ENNReal.ofReal (2 * r) ^ d ≤ μ (closedBall x r)) :
    c * μH[d] A ≤ μ U := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  rcases eq_or_ne (μ U) ∞ with hUtop | hUtop
  · simp [hUtop]
  refine le_trans ?_ (ENNReal.mul_div_le (a := c) (b := μ U))
  gcongr
  refine TauCeti.hausdorffMeasure_le_of_forall_exists_closedBall_cover fun δ hδ ε hε => ?_
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
  have h3 : (3 : ℝ≥0∞) ^ d ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero (by simp) (by simp)
  -- Choose a finite subfamily `F` whose complement has a small sum.
  obtain ⟨F, hF⟩ := ((ENNReal.tendsto_nhds_zero.1 (ENNReal.tendsto_tsum_compl_atTop_zero
    (ne_top_of_le_ne_top (ENNReal.div_lt_top hUtop hc0).ne hsum)) _
    (ENNReal.div_pos hε.ne' h3)).exists)
  -- Cover by the balls in `F` and the threefold enlargements of the other selected balls.
  classical
  refine ⟨u, inferInstance, fun p => p.val.1, fun p => if p ∈ F then p.val.2 else 3 * p.val.2,
    fun p => ?_, fun x hx => ?_, ?_⟩
  · have := (huT p.property).2.2.1
    dsimp only
    split_ifs <;> linarith [(huT p.property).2.1]
  · by_cases hxF : x ∈ ⋃ p ∈ F, closedBall p.val.1 p.val.2
    · obtain ⟨p, hpF, hxp⟩ := mem_iUnion₂.1 hxF
      exact mem_iUnion.2 ⟨p, by simpa [hpF] using hxp⟩
    obtain ⟨r, hrT, hrF⟩ := fine x hx _ ((isClosed_biUnion_finset fun p _ =>
      isClosed_closedBall).isOpen_compl.mem_nhds hxF)
    obtain ⟨b, hbu, ⟨y, hyx, hyb⟩, hrb⟩ := hucov (x, r) hrT
    have hbF : (⟨b, hbu⟩ : u) ∉ F := fun hbF => hrF hyx (mem_iUnion₂.2 ⟨_, hbF, hyb⟩)
    refine mem_iUnion.2 ⟨⟨b, hbu⟩, ?_⟩
    simp only [hbF, ↓reduceIte, mem_closedBall]
    linarith [dist_triangle x y b.1, mem_closedBall'.1 hyx, mem_closedBall.1 hyb]
  · calc _ ≤ _ := TauCeti.tsum_ofReal_two_mul_ite_le F (fun p : u => p.val.2) d
      _ ≤ μ U / c + 3 ^ d * (ε / 3 ^ d) := by gcongr
      _ ≤ μ U / c + ε := by gcongr; exact ENNReal.mul_div_le

/-- **Density comparison for Hausdorff measure**, outer regular form. If `μ` is outer regular
and at every point `x` of `A` there are arbitrarily small radii `r > 0` with
`c (2 r) ^ d ≤ μ (closedBall x r)`, then `c * μH[d] A ≤ μ A`. -/
theorem mul_hausdorffMeasure_le_measure (μ : Measure X) [μ.OuterRegular] {d : ℝ}
    {c : ℝ≥0∞} {A : Set X}
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0, c * ENNReal.ofReal (2 * r) ^ d ≤ μ (closedBall x r)) :
    c * μH[d] A ≤ μ A := by
  refine le_of_forall_gt fun b hb => ?_
  obtain ⟨U, hAU, hU, hUb⟩ := A.exists_isOpen_lt_of_lt b hb
  exact (mul_hausdorffMeasure_le_measure_of_isOpen μ hU hAU h).trans_lt hUb

omit [BorelSpace X] in
/-- **Rescaling a lower bound on the measures of balls.** If `c ρ ^ d ≤ μ (closedBall y ρ)` for
every radius `0 < ρ ≤ ρ₀`, then arbitrarily small radii `r > 0` have
`(c / 2 ^ d) (2 r) ^ d ≤ μ (closedBall y r)`, the form of a lower density bound used in
`MeasureTheory.Measure.mul_hausdorffMeasure_le_measure_of_isOpen`. -/
theorem frequently_ofReal_div_mul_rpow_le_measure_closedBall {μ : Measure X} {y : X} {c ρ₀ : ℝ}
    {d : ℕ} (hρ₀ : 0 < ρ₀)
    (h : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ENNReal.ofReal (c * ρ ^ d) ≤ μ (closedBall y ρ)) :
    ∃ᶠ r in 𝓝[>] 0,
      ENNReal.ofReal (c / 2 ^ d) * ENNReal.ofReal (2 * r) ^ (d : ℝ) ≤ μ (closedBall y r) := by
  refine Eventually.frequently ?_
  filter_upwards [Ioc_mem_nhdsGT hρ₀] with ρ hρ
  have h2ρ : 0 ≤ 2 * ρ := by linarith [hρ.1]
  have hscale : c / 2 ^ d * (2 * ρ) ^ d = c * ρ ^ d := by
    rw [mul_pow]
    field_simp
  rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow h2ρ, ← ENNReal.ofReal_mul' (pow_nonneg h2ρ d),
    hscale]
  exact h ρ hρ.1 hρ.2

/-- **Locally finite Hausdorff measure from a local density bound.** Let `μ` be locally finite.
If every point has a neighbourhood `V` and a constant `c ≠ 0` such that at every point `y` of
`A ∩ V` arbitrarily small radii `r > 0` have `c (2 r) ^ d ≤ μ (closedBall y r)`, then `A` has
locally finite `d`-dimensional Hausdorff measure. -/
theorem isLocallyFiniteMeasure_restrict_hausdorffMeasure (μ : Measure X)
    [IsLocallyFiniteMeasure μ] {d : ℝ} {A : Set X}
    (h : ∀ x, ∃ V ∈ 𝓝 x, ∃ c ≠ 0, ∀ y ∈ A ∩ V,
      ∃ᶠ r in 𝓝[>] 0, c * ENNReal.ofReal (2 * r) ^ d ≤ μ (closedBall y r)) :
    IsLocallyFiniteMeasure (μH[d].restrict A) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨V, hV, c, hc, hdens⟩ := h x
  obtain ⟨W, hxW, hW, hWfin⟩ := μ.exists_isOpen_measure_lt_top x
  -- On the open neighbourhood `U = W ∩ interior V` of `x`, the density bound controls `μH[d]`.
  have hU : IsOpen (W ∩ interior V) := hW.inter isOpen_interior
  refine ⟨W ∩ interior V, hU.mem_nhds ⟨hxW, mem_interior_iff_mem_nhds.2 hV⟩, ?_⟩
  rw [Measure.restrict_apply hU.measurableSet]
  have hle := mul_hausdorffMeasure_le_measure_of_isOpen μ hU (inter_subset_left (t := A))
    fun y hy => hdens y ⟨hy.2, interior_subset hy.1.2⟩
  exact ENNReal.lt_top_of_mul_ne_top_right
    ((hle.trans_lt ((measure_mono inter_subset_left).trans_lt hWfin)).ne) hc

/-- **Locally finite Hausdorff measure from a local lower density bound.** Let `μ` be locally
finite. If every point has a neighbourhood `U` and constants `c > 0`, `ρ₀ > 0` with
`c ρ ^ d ≤ μ (closedBall y ρ)` for every `y ∈ A ∩ U` and every radius `0 < ρ ≤ ρ₀`, then `A` has
locally finite `d`-dimensional Hausdorff measure. -/
theorem isLocallyFiniteMeasure_restrict_hausdorffMeasure_of_ofReal_mul_pow_le (μ : Measure X)
    [IsLocallyFiniteMeasure μ] {d : ℕ} {A : Set X}
    (h : ∀ x, ∃ U ∈ 𝓝 x, ∃ c > 0, ∃ ρ₀ > 0, ∀ y ∈ A ∩ U, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
      ENNReal.ofReal (c * ρ ^ d) ≤ μ (closedBall y ρ)) :
    IsLocallyFiniteMeasure (μH[d].restrict A) := by
  refine isLocallyFiniteMeasure_restrict_hausdorffMeasure μ fun x ↦ ?_
  obtain ⟨U, hU, c, hc, ρ₀, hρ₀, hdens⟩ := h x
  exact ⟨U, hU, ENNReal.ofReal (c / 2 ^ d), (ENNReal.ofReal_pos.2 (by positivity)).ne',
    fun y hy ↦ frequently_ofReal_div_mul_rpow_le_measure_closedBall hρ₀ (hdens y hy)⟩

/-- **Upper density comparison for Hausdorff measure.** If at every point `x` of `A` all small
closed balls satisfy `μ (closedBall x r) ≤ c (2 r) ^ d`, where `c ≠ 0, ∞`, then
`μ A ≤ 2 ^ d * c * μH[d] A`. A set of diameter `ρ` meeting `A` at `x` lies in
`closedBall x ρ`, which is where the factor `2 ^ d` is lost. -/
theorem measure_le_mul_hausdorffMeasure (μ : Measure X) {d : ℝ} {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) {A : Set X}
    (h : ∀ x ∈ A, ∀ᶠ r in 𝓝[>] 0, μ (closedBall x r) ≤ c * ENNReal.ofReal (2 * r) ^ d) :
    μ A ≤ 2 ^ d * c * μH[d] A := by
  have h2 : (2 : ℝ≥0∞) ^ d * c ≠ 0 :=
    mul_ne_zero (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne' hc0
  have h2top : (2 : ℝ≥0∞) ^ d * c ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero two_ne_zero ENNReal.ofNat_ne_top) hc
  have hcont : Continuous fun r : ℝ => c * ENNReal.ofReal (2 * r) ^ d :=
    (ENNReal.continuous_const_mul hc).comp (ENNReal.continuous_rpow_const.comp
      (ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  refine measure_le_mul_hausdorffMeasure_of_le_mul_ediam_rpow μ h2 h2top fun x hx => ?_
  obtain ⟨ε, hε, hεA⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' one_pos).1 (h x hx)
  refine ⟨ENNReal.ofReal ε, ENNReal.ofReal_pos.2 hε, fun t hxt ht => ?_⟩
  have hstop : ediam t ≠ ∞ := (ht.trans ENNReal.ofReal_lt_top).ne
  have hsub : t ⊆ closedBall x (ediam t).toReal := fun y hy => by
    rw [mem_closedBall, dist_edist]
    exact ENNReal.toReal_mono hstop (edist_le_ediam_of_mem hy hxt)
  have hρε : (ediam t).toReal < ε := ENNReal.toReal_lt_of_lt_ofReal ht
  -- The bound extends from radii in `(0, ε)` to the radius `diam t ∈ [0, ε)`.
  calc μ t ≤ μ (closedBall x (ediam t).toReal) := measure_mono hsub
    _ ≤ c * ENNReal.ofReal (2 * (ediam t).toReal) ^ d :=
        measure_closedBall_le_of_frequently_le μ hcont.continuousWithinAt
          (eventually_of_mem (Ioo_mem_nhdsGT hρε) fun r hr =>
            hεA ⟨ENNReal.toReal_nonneg.trans_lt hr.1, hr.2⟩).frequently
    _ = 2 ^ d * c * ediam t ^ d := by
        rw [ENNReal.ofReal_mul_rpow zero_le_two, ENNReal.ofReal_toReal hstop, ENNReal.ofReal_ofNat]
        ring

/-- **Zero density on a null set.** An outer regular measure `μ` has `d`-density zero at
`μH[d]`-almost every point of any `μ`-null set `A` (no measurability of `A` is needed):
`μ (closedBall x r) / (2 r) ^ d → 0` as `r → 0⁺` for `μH[d]`-almost every `x ∈ A`. -/
theorem ae_tendsto_measure_closedBall_div_of_measure_eq_zero (μ : Measure X) [μ.OuterRegular]
    {d : ℝ} {A : Set X} (hA : μ A = 0) :
    ∀ᵐ x ∂μH[d], x ∈ A → Tendsto (fun r => μ (closedBall x r) /
      ENNReal.ofReal (2 * r) ^ d) (𝓝[>] 0) (𝓝 0) := by
  have hnull (n : ℕ) : μH[d] {x | x ∈ A ∧ ∃ᶠ r in 𝓝[>] 0,
      (n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (2 * r) ^ d ≤ μ (closedBall x r)} = 0 := by
    set B := {x | x ∈ A ∧ ∃ᶠ r in 𝓝[>] 0,
      (n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (2 * r) ^ d ≤ μ (closedBall x r)}
    have hc : (n : ℝ≥0∞)⁻¹ ≠ 0 := by simp
    have hle := (μ.mul_hausdorffMeasure_le_measure (A := B) fun _ hx => hx.2).trans
      (measure_mono_null (s := B) (fun _ hx => hx.1) hA).le
    simpa [hc] using nonpos_iff_eq_zero.1 hle
  filter_upwards [ae_all_iff.2 fun n => measure_eq_zero_iff_ae_notMem.1 (hnull n)] with x hx hxA
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  have hxn := hx n
  simp only [hxA, true_and, not_frequently, not_le] at hxn
  filter_upwards [hxn] with r hr
  exact ENNReal.div_le_of_le_mul (hr.le.trans (by gcongr))

end MetricSpace

end MeasureTheory.Measure

namespace TauCeti

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Zero density outside a set.** A null-measurable set `A` of finite `d`-dimensional Hausdorff
measure has upper `d`-density zero at almost every point outside it:
`μH[d] (A ∩ closedBall x r) / (2 r) ^ d → 0` as `r → 0⁺` for `μH[d]`-almost every `x ∉ A`. -/
theorem ae_tendsto_hausdorffMeasure_inter_closedBall_div {d : ℝ} {A : Set X}
    (hA : NullMeasurableSet A μH[d]) (hAfin : μH[d] A ≠ ∞) :
    ∀ᵐ x ∂μH[d], x ∉ A → Tendsto (fun r => μH[d] (A ∩ closedBall x r) /
      ENNReal.ofReal (2 * r) ^ d) (𝓝[>] 0) (𝓝 0) := by
  have : IsFiniteMeasure (μH[d].restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAfin.lt_top⟩
  have hnull : (μH[d].restrict A) Aᶜ = 0 := ae_iff.1 (ae_restrict_mem₀ hA)
  simpa [Measure.restrict_apply measurableSet_closedBall, inter_comm A] using
    (μH[d].restrict A).ae_tendsto_measure_closedBall_div_of_measure_eq_zero hnull

end TauCeti
