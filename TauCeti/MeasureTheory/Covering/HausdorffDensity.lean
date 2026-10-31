/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Covering.Vitali
import TauCeti.MeasureTheory.Measure.Lebesgue.Isodiametric

/-!
# Upper densities and Hausdorff measure

Let `μ` be a measure on a metric space `X` and `d ≥ 0`. If at every point `x` of a set `A` the
measure of arbitrarily small closed balls satisfies `μ (closedBall x r) ≥ c (2 r) ^ d`, that is, if
the `d`-dimensional upper density of `μ` is at least `c` on `A`, then `μ` dominates `c` times the
`d`-dimensional Hausdorff measure on `A`:

`c * μH[d] A ≤ μ U` for every open `U ⊇ A`, hence `c * μH[d] A ≤ μ A` if `μ` is outer regular.

Neither `A` nor `μ` needs any further regularity, and `c` is not required to be finite. The
constant is sharp: no covering constant is lost. Combined with the isodiametric inequality, this
identifies the normalizing constant of Mathlib's Euclidean Hausdorff measure:
`μHE[k] = (ω_k / 2 ^ k) • μH[k]` on every extended metric space, where `ω_k` is the volume of the
unit ball of `EuclideanSpace ℝ (Fin k)`. In this normalization the density comparison reads
`c * μHE[k] A ≤ μ U` whenever `μ (closedBall x r) ≥ c ω_k r ^ k` along arbitrarily small radii at
every `x ∈ A`.

As a consequence, a set `A` of finite `d`-dimensional Hausdorff measure has upper density zero
at almost every point outside it:
`μH[d] (A ∩ closedBall x r) / (2 r) ^ d → 0` as `r → 0⁺` for `μH[d]`-almost every `x ∉ A`, and
likewise `μHE[k] (A ∩ closedBall x r) / (ω_k r ^ k) → 0`.

These comparisons between densities and Hausdorff measure are the measure-theoretic input of the
density theorem for rectifiable sets and of the identification of the perimeter measure with the
Hausdorff measure of the reduced boundary.

## Main results

* `TauCeti.mul_hausdorffMeasure_le_measure_of_isOpen` and `TauCeti.mul_hausdorffMeasure_le_measure`:
  a measure whose upper density is at least `c` on `A` dominates `c • μH[d]` on `A`.
* `TauCeti.euclideanHausdorffMeasure_eq_smul_hausdorffMeasure`: `μHE[k] = (ω_k / 2 ^ k) • μH[k]`.
* `TauCeti.mul_euclideanHausdorffMeasure_le_measure_of_isOpen` and
  `TauCeti.mul_euclideanHausdorffMeasure_le_measure`: the same domination in the Euclidean
  normalization.
* `TauCeti.ae_tendsto_hausdorffMeasure_inter_closedBall_div` and
  `TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`: zero density outside a set
  of finite Hausdorff measure.

## Implementation notes

The domination is proved with the Vitali covering lemma
`Vitali.exists_disjoint_subfamily_covering_enlargement`, applied to the closed balls inside `U` on
which `μ` is large. The selected disjoint balls are countable because they have positive measure
inside a set of finite measure, and the sum of `(2 r) ^ d` over them is at most `μ U / c`. Finitely
many of them, together with the threefold enlargements of the others, cover `A`, and the sum over
the enlargements tends to zero.

## References

* H. Federer, *Geometric Measure Theory*, 2.10.19 (densities and Hausdorff measures).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 6.2.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  Theorem 2.10 and Theorem 2.4 (the normalization of Hausdorff measure).
-/

public section

open Filter Metric MeasureTheory Measure Set Module
open scoped ENNReal NNReal Topology

universe u

namespace TauCeti

section MetricSpace

variable {X : Type u} [MetricSpace X]

/-- A closed ball of radius `r` has extended diameter at most `2 r`. -/
private lemma ediam_closedBall_le_ofReal (x : X) (r : ℝ) :
    ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
  ediam_le_of_forall_dist_le fun y hy z hz => (dist_triangle_right y z x).trans <| by
    linarith [mem_closedBall.1 hy, mem_closedBall.1 hz]

/-- Every neighbourhood of `x` contains the closed balls around `x` of all small positive radii. -/
private lemma eventually_closedBall_subset {x : X} {V : Set X} (hV : V ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ closedBall x r ⊆ V := by
  obtain ⟨ε, hε, hεV⟩ := nhds_basis_closedBall.mem_iff.1 hV
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  exact ⟨hr.1, (closedBall_subset_closedBall hr.2.le).trans hεV⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- If for every `δ > 0` and `ε > 0` the set `A` is covered by countably many closed balls of
radii at most `δ` with `∑ (2 rᵢ) ^ d ≤ M + ε`, then `μH[d] A ≤ M`. This is
`hausdorffMeasure_le_liminf_tsum` for covers by closed balls. -/
private lemma hausdorffMeasure_le_of_forall_exists_closedBall_cover {d : ℝ} (hd : 0 ≤ d) {A : Set X}
    {M : ℝ≥0∞} (h : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (ι : Type u) (_ : Countable ι) (x : ι → X) (r : ι → ℝ), (∀ i, r i ≤ δ) ∧
        A ⊆ ⋃ i, closedBall (x i) (r i) ∧ ∑' i, ENNReal.ofReal (2 * r i) ^ d ≤ M + ε) :
    μH[d] A ≤ M := by
  choose ι hι x r hrδ hA hsum using fun n : ℕ =>
    h (1 / (n + 1)) Nat.one_div_pos_of_nat (n : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (by simp))
  have hlim : Tendsto (fun n : ℕ => M + (n : ℝ≥0∞)⁻¹) atTop (𝓝 M) := by
    simpa using tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
  have hδ : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (1 / (n + 1)))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2)
  have := hι
  calc μH[d] A ≤ liminf (fun n => ∑' i, ediam (closedBall (x n i) (r n i)) ^ d) atTop :=
        hausdorffMeasure_le_liminf_tsum d A _ hδ _
          (Eventually.of_forall fun n i => (ediam_closedBall_le_ofReal _ _).trans
            (ENNReal.ofReal_le_ofReal (by linarith [hrδ n i])))
          (Eventually.of_forall hA)
    _ ≤ liminf (fun n : ℕ => M + (n : ℝ≥0∞)⁻¹) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => (ENNReal.tsum_le_tsum fun i =>
          ENNReal.rpow_le_rpow (ediam_closedBall_le_ofReal _ _) hd).trans (hsum n))
    _ = M := hlim.liminf_eq

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
        ENNReal.tsum_le_tsum fun p => by rw [mul_comm]; exact (hu _ p.2).2.2
    _ = μ (⋃ p ∈ u, closedBall p.1 p.2) :=
        (measure_biUnion hcount hud fun _ _ => measurableSet_closedBall).symm
    _ ≤ μ U := measure_mono (iUnion₂_subset fun p hp => (hu p hp).2.1)

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
  refine hausdorffMeasure_le_of_forall_exists_closedBall_cover hd fun δ hδ ε hε => ?_
  -- The admissible balls: centred in `A`, of radius at most `δ / 3`, inside `U`, and large for `μ`.
  set T : Set (X × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ p.2 ≤ δ / 3 ∧ closedBall p.1 p.2 ⊆ U ∧
    c * ENNReal.ofReal (2 * p.2) ^ d ≤ μ (closedBall p.1 p.2)}
  have fine : ∀ x ∈ A, ∀ V ∈ 𝓝 x, ∃ r, (x, r) ∈ T ∧ closedBall x r ⊆ V := by
    intro x hx V hV
    obtain ⟨r, hr, ⟨hr0, hrV⟩, hrδ⟩ := ((h x hx).and_eventually
      ((eventually_closedBall_subset (inter_mem hV (hU.mem_nhds (hAU hx)))).and
        (Ioo_mem_nhdsGT (by positivity : 0 < δ / 3)))).exists
    exact ⟨r, ⟨hx, hr0, hrδ.2.le, hrV.trans inter_subset_right, hr⟩, hrV.trans inter_subset_left⟩
  obtain ⟨u, huT, hud, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun p : X × ℝ => closedBall p.1 p.2) T (fun p => p.2) 2 one_lt_two
    (fun p hp => hp.2.1.le) (δ / 3) (fun p hp => hp.2.2.1)
    (fun p hp => nonempty_closedBall.2 hp.2.1.le)
  obtain ⟨hu, hsum⟩ := countable_and_tsum_le_of_pairwiseDisjoint μ hc0 hUtop hud
    fun p hp => ⟨(huT hp).2.1, (huT hp).2.2.2.1, (huT hp).2.2.2.2⟩
  have : Countable u := hu.to_subtype
  set a : u → ℝ≥0∞ := fun p => ENNReal.ofReal (2 * p.1.2) ^ d with ha
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
  · calc ∑' p : u, ENNReal.ofReal (2 * if p ∈ F then p.1.2 else 3 * p.1.2) ^ d
        ≤ ∑' p : u, (a p + {p | p ∉ F}.indicator (fun p => 3 ^ d * a p) p) :=
          ENNReal.tsum_le_tsum fun p => by
            by_cases hp : p ∈ F
            · simp [hp, ha]
            · simp only [hp, ↓reduceIte]
              rw [indicator_of_mem (by exact hp), ha, mul_left_comm,
                ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ hd,
                ENNReal.ofReal_ofNat]
              exact le_add_self
      _ = ∑' p, a p + 3 ^ d * ∑' p : {p // p ∉ F}, a p := by
          rw [ENNReal.tsum_add, ← tsum_subtype {p | p ∉ F}, ENNReal.tsum_mul_left]
          -- `↥{p | p ∉ F}` is notation for the subtype `{p // p ∉ F}`.
          rfl
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
      hx.2.mp ((eventually_closedBall_subset (hF.isOpen_compl.mem_nhds
        fun hxF => hx.1 (hFA hxF))).mono fun r hr hle => ?_)
  · have hcap : Fᶜ ∩ (A \ F) = A \ F := inter_eq_right.2 fun _ hy => hy.2
    rw [Measure.restrict_apply hF.isOpen_compl.measurableSet, hcap] at key
    simpa using key.trans hAF.le
  · rwa [Measure.restrict_apply measurableSet_closedBall, show closedBall x r ∩ (A \ F) =
      A ∩ closedBall x r from by
        ext y; constructor
        · exact fun hy => ⟨hy.2.1, hy.1⟩
        · exact fun hy => ⟨hy.2, hy.1, hr.2 hy.2⟩]

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

end MetricSpace

section Euclidean

/-- The normalizing constant `ω_k / 2 ^ k` is nonzero. -/
private lemma volume_ball_div_two_pow_ne_zero (k : ℕ) :
    volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k ≠ 0 :=
  ENNReal.div_ne_zero.2 ⟨(measure_ball_pos _ _ one_pos).ne', by simp⟩

/-- The normalizing constant `ω_k / 2 ^ k` is finite. -/
private lemma volume_ball_div_two_pow_ne_top (k : ℕ) :
    volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k ≠ ∞ :=
  ENNReal.div_ne_top measure_ball_lt_top.ne (by simp)

/-- The volume of a closed ball of radius `r ≥ 0` in `EuclideanSpace ℝ (Fin k)` is
`(ω_k / 2 ^ k) (2 r) ^ k`. -/
private lemma volume_closedBall_eq_div_mul (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) {r : ℝ}
    (hr : 0 ≤ r) :
    volume (closedBall x r) = volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k *
      ENNReal.ofReal (2 * r) ^ (k : ℝ) := by
  rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin, ENNReal.rpow_natCast,
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_pow, ENNReal.ofReal_pow hr,
    ENNReal.div_eq_inv_mul]
  have h2 : ((2 : ℝ≥0∞) ^ k)⁻¹ * 2 ^ k = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
  calc _ = ((2 : ℝ≥0∞) ^ k)⁻¹ * 2 ^ k * (volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) *
        ENNReal.ofReal r ^ k) := by rw [h2, one_mul, mul_comm]
    _ = _ := by ring

/-- On `EuclideanSpace ℝ (Fin k)`, volume is `(ω_k / 2 ^ k) • μH[k]`: the density comparison
gives one inequality and the isodiametric inequality the other. -/
private lemma volume_eq_smul_hausdorffMeasure (k : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))) =
      (volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k) • μH[k] := by
  set ω' := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k
  have hω0 : ω' ≠ 0 := volume_ball_div_two_pow_ne_zero k
  have hωtop : ω' ≠ ∞ := volume_ball_div_two_pow_ne_top k
  refine le_antisymm (Measure.le_iff'.2 fun s => ?_) (Measure.le_iff'.2 fun s => ?_)
  · -- Isodiametric inequality: `volume s ≤ ω' ediam s ^ k`.
    have hle : ω'⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin k))) ≤ μH[k] :=
      le_hausdorffMeasure _ _ 1 one_pos fun t _ => by
        rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_le_iff hω0 hωtop, ENNReal.rpow_natCast]
        refine (volume_le_ediam_div_two_pow_mul_volume_ball t).trans_eq ?_
        rw [finrank_euclideanSpace_fin, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]
        simp only [ω', div_eq_mul_inv]
        ring
    rw [Measure.smul_apply, smul_eq_mul, ← ENNReal.inv_mul_le_iff hω0 hωtop]
    simpa using hle s
  · rw [Measure.smul_apply, smul_eq_mul]
    exact mul_hausdorffMeasure_le_measure volume (Nat.cast_nonneg k) fun x _ =>
      (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) =>
        (volume_closedBall_eq_div_mul k x hr.le).ge).frequently

variable {X : Type u} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Normalization of Euclidean Hausdorff measure.** Mathlib's `k`-dimensional Euclidean
Hausdorff measure is `ω_k / 2 ^ k` times the raw `k`-dimensional Hausdorff measure, where
`ω_k` is the volume of the unit ball of `EuclideanSpace ℝ (Fin k)`. -/
theorem euclideanHausdorffMeasure_eq_smul_hausdorffMeasure (k : ℕ) :
    (μHE[k] : Measure X) = (volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k) • μH[k] := by
  set ω' := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k
  set a := addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin k))) μH[k]
  suffices ha : (a : ℝ≥0∞) = ω' by
    rw [euclideanHausdorffMeasure_def, ← ha, ENNReal.smul_def]
  -- Compare the two expressions for volume on `EuclideanSpace ℝ (Fin k)` at the unit ball.
  have hdef := congr($(EuclideanSpace.euclideanHausdorffMeasure_eq_volume k)
    (ball (0 : EuclideanSpace ℝ (Fin k)) 1))
  have hvol := congr($(volume_eq_smul_hausdorffMeasure k)
    (ball (0 : EuclideanSpace ℝ (Fin k)) 1))
  rw [euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hdef
  rw [Measure.smul_apply, smul_eq_mul] at hvol
  have hB0 : μH[k] (ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≠ 0 := fun h0 =>
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin k)) one_pos).ne'
      (by rw [hvol, h0, mul_zero])
  have hBtop : μH[k] (ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≠ ∞ := fun htop => by
    exact measure_ball_lt_top.ne (hvol.trans (by
      rw [htop]; exact ENNReal.mul_top (volume_ball_div_two_pow_ne_zero k)))
  exact (ENNReal.mul_left_inj hB0 hBtop).1 (hdef.trans hvol)

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Density comparison for Euclidean Hausdorff measure**, open-set form. If at every point `x`
of `A` there are arbitrarily small radii `r > 0` with `c ω_k r ^ k ≤ μ (closedBall x r)`, where
`ω_k r ^ k` is the volume of a ball of radius `r` in `EuclideanSpace ℝ (Fin k)`, then
`c * μHE[k] A ≤ μ U` for every open set `U` containing `A`. -/
theorem mul_euclideanHausdorffMeasure_le_measure_of_isOpen (μ : Measure X) (k : ℕ) {c : ℝ≥0∞}
    {A U : Set X} (hU : IsOpen U) (hAU : A ⊆ U)
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0,
      c * volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≤ μ (closedBall x r)) :
    c * μHE[k] A ≤ μ U := by
  rw [euclideanHausdorffMeasure_eq_smul_hausdorffMeasure, Measure.smul_apply, smul_eq_mul,
    ← mul_assoc]
  refine mul_hausdorffMeasure_le_measure_of_isOpen μ (Nat.cast_nonneg k) hU hAU fun x hx =>
    (h x hx).mp (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) hle => ?_)
  rwa [volume_closedBall_eq_div_mul k 0 hr.le, ← mul_assoc] at hle

/-- **Density comparison for Euclidean Hausdorff measure**, outer regular form. If `μ` is outer
regular and at every point `x` of `A` there are arbitrarily small radii `r > 0` with
`c ω_k r ^ k ≤ μ (closedBall x r)`, then `c * μHE[k] A ≤ μ A`. -/
theorem mul_euclideanHausdorffMeasure_le_measure (μ : Measure X) [μ.OuterRegular] (k : ℕ)
    {c : ℝ≥0∞} {A : Set X}
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0,
      c * volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≤ μ (closedBall x r)) :
    c * μHE[k] A ≤ μ A := by
  refine le_of_forall_gt fun b hb => ?_
  obtain ⟨U, hAU, hU, hUb⟩ := A.exists_isOpen_lt_of_lt b hb
  exact (mul_euclideanHausdorffMeasure_le_measure_of_isOpen μ k hU hAU h).trans_lt hUb

/-- **Zero density outside a set**, Euclidean normalization. A null-measurable set `A` of finite
`k`-dimensional Euclidean Hausdorff measure satisfies
`μHE[k] (A ∩ closedBall x r) / (ω_k r ^ k) → 0` as `r → 0⁺` for `μHE[k]`-almost every `x ∉ A`,
where `ω_k r ^ k` is the volume of a ball of radius `r` in `EuclideanSpace ℝ (Fin k)`. -/
theorem ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div (k : ℕ) {A : Set X}
    (hA : NullMeasurableSet A μHE[k]) (hAfin : μHE[k] A ≠ ∞) :
    ∀ᵐ x ∂μHE[k], x ∉ A → Tendsto (fun r => μHE[k] (A ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  set ω' := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k
  have hω0 : ω' ≠ 0 := volume_ball_div_two_pow_ne_zero k
  have hωtop : ω' ≠ ∞ := volume_ball_div_two_pow_ne_top k
  rw [euclideanHausdorffMeasure_eq_smul_hausdorffMeasure] at hA hAfin ⊢
  replace hAfin : μH[k] A ≠ ∞ := fun h => hAfin (by
    rw [Measure.smul_apply, smul_eq_mul, h]; exact ENNReal.mul_top hω0)
  refine ae_smul_measure ?_ _
  filter_upwards [ae_tendsto_hausdorffMeasure_inter_closedBall_div (Nat.cast_nonneg k)
    (hA.mono_ac (absolutelyContinuous_smul hω0)) hAfin] with x hx hxA
  refine (hx hxA).congr' (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) => ?_)
  dsimp only
  rw [Measure.smul_apply, smul_eq_mul, volume_closedBall_eq_div_mul k 0 hr.le,
    ENNReal.mul_div_mul_left _ _ hω0 hωtop]

end Euclidean

end TauCeti
