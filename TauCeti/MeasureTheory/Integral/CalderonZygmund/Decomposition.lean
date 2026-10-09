/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average
public import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube
import TauCeti.Analysis.Normed.Group.InfiniteSum
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# The Calderón–Zygmund decomposition

Let `f : (ι → ℝ) → E` be integrable on `ℝⁿ`, `n ≥ 1`, and let `t > 0`. The **Calderón–Zygmund
decomposition** of `f` at height `t` writes

`f = g + ∑_Q b_Q`,

where the sum runs over a countable family of pairwise disjoint dyadic cubes `Q`, the
*Calderón–Zygmund cubes*, such that

* `t < ⨍_Q ‖f‖ ≤ 2ⁿ t` on each cube, and `t |⋃ Q| ≤ ∫_{⋃ Q} ‖f‖`;
* the **good part** `g` is `f` off the cubes and the average of `f` on each cube, so that
  `‖g‖ ≤ 2ⁿ t` almost everywhere and `‖g‖₁ ≤ ‖f‖₁`;
* each **bad part** `b_Q` is supported on `Q`, has integral zero, and `‖b_Q‖₁ ≤ 2 ∫_Q ‖f‖`;
  if `f ∈ Lᵖ` for a finite `p`, the series `∑_Q b_Q` converges to `f - g` in `Lᵖ`.

It is the device that turns `L²` bounds for singular integral operators into weak type `(1, 1)`
bounds (`ContinuousLinearMap.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`): the
good part is bounded, hence in `L²` with `‖g‖₂² ≤ 2ⁿ t ‖f‖₁`, while the bad parts have mean
zero on small cubes, where the smoothness of the kernel makes them nearly cancel. Together with
Marcinkiewicz interpolation this gives `Lᵖ` boundedness for `1 < p < 2`; the range `2 < p < ∞`
then follows by applying the corresponding bounds to the adjoint and using duality.

The cubes are the maximal dyadic cubes on which the average of `‖f‖` exceeds `t`
(`TauCeti.calderonZygmundCubes`). They exist because averages over large cubes are small, which
is where integrability and positive dimension enter; and `‖f‖ ≤ t` almost everywhere off them by
the Lebesgue differentiation theorem along dyadic cubes. The selection of the cubes is stated for
an arbitrary `g : (ι → ℝ) → ℝ≥0∞` in place of `‖f‖ₑ`.

## Main declarations

* `TauCeti.calderonZygmundCubes`: the Calderón–Zygmund cubes of `g` at height `t`, with
  `TauCeti.lt_setLAverage_of_mem_calderonZygmundCubes`,
  `TauCeti.setLAverage_le_of_mem_calderonZygmundCubes`,
  `TauCeti.pairwiseDisjoint_calderonZygmundCubes`,
  `TauCeti.exists_mem_calderonZygmundCubes_of_lt_setLAverage`,
  `TauCeti.ae_le_of_forall_notMem_calderonZygmundCubes` and
  `TauCeti.mul_volume_biUnion_calderonZygmundCubes_le`.
* `TauCeti.calderonZygmundBad`, `TauCeti.calderonZygmundGood`: the bad parts and the good part,
  with `TauCeti.calderonZygmundGood_add_tsum_calderonZygmundBad` (the decomposition),
  `TauCeti.integral_calderonZygmundBad`, `TauCeti.lintegral_enorm_calderonZygmundBad_le`,
  `TauCeti.ae_enorm_calderonZygmundGood_le` and
  `TauCeti.lintegral_enorm_calderonZygmundGood_le`.
* `TauCeti.sq_eLpNorm_calderonZygmundGood_le`, `TauCeti.memLp_two_calderonZygmundGood`: the good
  part is in `L²`, with `‖g‖₂² ≤ 2ⁿ t ‖f‖₁`.
* `TauCeti.hasSum_toLp_calderonZygmundBad`: in `Lᵖ`, `p < ∞`, the bad parts sum to `f - g`.

## References

* A. P. Calderón and A. Zygmund, *On the existence of certain singular integrals*, Acta Math.
  **88** (1952), 85–139.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I, §4.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3.1.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {ι : Type*} [Fintype ι]

section Cubes

variable {g : (ι → ℝ) → ℝ≥0∞} {t : ℝ≥0∞} {q : ℤ × (ι → ℤ)}

/-- The **Calderón–Zygmund cubes** of `g` at height `t`: the dyadic cubes, recorded by level and
position, on which the average of `g` exceeds `t` while it is at most `t` on every dyadic cube of
higher level containing them. These are the maximal dyadic cubes on which the average of `g`
exceeds `t`. -/
def calderonZygmundCubes (g : (ι → ℝ) → ℝ≥0∞) (t : ℝ≥0∞) : Set (ℤ × (ι → ℤ)) :=
  {q | t < ⨍⁻ x in dyadicCube q.1 q.2, g x ∂volume ∧
    ∀ j m, q.1 < j → dyadicCube q.1 q.2 ⊆ dyadicCube j m →
      ⨍⁻ x in dyadicCube j m, g x ∂volume ≤ t}

theorem mem_calderonZygmundCubes :
    q ∈ calderonZygmundCubes g t ↔ t < ⨍⁻ x in dyadicCube q.1 q.2, g x ∂volume ∧
      ∀ j m, q.1 < j → dyadicCube q.1 q.2 ⊆ dyadicCube j m →
        ⨍⁻ x in dyadicCube j m, g x ∂volume ≤ t :=
  Iff.rfl

/-- The average over a Calderón–Zygmund cube exceeds the height. -/
theorem lt_setLAverage_of_mem_calderonZygmundCubes (hq : q ∈ calderonZygmundCubes g t) :
    t < ⨍⁻ x in dyadicCube q.1 q.2, g x ∂volume :=
  hq.1

/-- The integral over a Calderón–Zygmund cube exceeds the height times its volume. -/
theorem mul_volume_lt_setLIntegral_of_mem_calderonZygmundCubes
    (hq : q ∈ calderonZygmundCubes g t) :
    t * volume (dyadicCube q.1 q.2) < ∫⁻ x in dyadicCube q.1 q.2, g x := by
  have h := lt_setLAverage_of_mem_calderonZygmundCubes hq
  rwa [setLAverage_eq, ENNReal.lt_div_iff_mul_lt (.inl (volume_dyadicCube_pos _ _).ne')
    (.inl (volume_dyadicCube_ne_top _ _))] at h

/-- The average over a Calderón–Zygmund cube is at most `2ⁿ` times the height: the average over
its parent cube is at most the height, and the parent is `2ⁿ` times larger. -/
theorem setLAverage_le_of_mem_calderonZygmundCubes (hq : q ∈ calderonZygmundCubes g t) :
    ⨍⁻ x in dyadicCube q.1 q.2, g x ∂volume ≤ 2 ^ Fintype.card ι * t := by
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (volume_dyadicCube_pos q.1 q.2).ne'
  have hsub := dyadicCube_subset_dyadicCube (lt_add_one q.1).le hx
  have hparent := hq.2 _ _ (lt_add_one q.1) hsub
  rw [setLAverage_eq]
  refine ENNReal.div_le_of_le_mul ?_
  calc ∫⁻ y in dyadicCube q.1 q.2, g y
      ≤ ∫⁻ y in dyadicCube (q.1 + 1) (dyadicIndex (q.1 + 1) x), g y := lintegral_mono_set hsub
    _ = volume (dyadicCube (q.1 + 1) (dyadicIndex (q.1 + 1) x)) *
          ⨍⁻ y in dyadicCube (q.1 + 1) (dyadicIndex (q.1 + 1) x), g y ∂volume :=
        (measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _)).symm
    _ ≤ volume (dyadicCube (q.1 + 1) (dyadicIndex (q.1 + 1) x)) * t := by gcongr
    _ = 2 ^ Fintype.card ι * t * volume (dyadicCube q.1 q.2) := by
        rw [volume_dyadicCube_add_one q.1 q.2]
        ring

/-- Distinct Calderón–Zygmund cubes are disjoint. -/
theorem pairwiseDisjoint_calderonZygmundCubes :
    (calderonZygmundCubes g t).PairwiseDisjoint fun q => dyadicCube q.1 q.2 := by
  have key : ∀ q ∈ calderonZygmundCubes g t, ∀ q' ∈ calderonZygmundCubes g t, q.1 ≤ q'.1 →
      q ≠ q' → Disjoint (dyadicCube q.1 q.2) (dyadicCube q'.1 q'.2) := by
    intro q hq q' hq' hle hne
    refine (dyadicCube_subset_or_disjoint hle q.2 q'.2).resolve_left fun hsub => ?_
    rcases hle.lt_or_eq with hlt | heq
    · exact (hq'.1.trans_le (hq.2 _ _ hlt hsub)).false
    · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (volume_dyadicCube_pos q.1 q.2).ne'
      have hx' := mem_dyadicCube.1 (hsub hx)
      rw [← heq, mem_dyadicCube.1 hx] at hx'
      exact hne (Prod.ext heq hx')
  intro q hq q' hq' hne
  rcases le_total q.1 q'.1 with h | h
  · exact key q hq q' hq' h hne
  · exact (key q' hq' q hq h hne.symm).symm

/-- In positive dimension, every dyadic cube on which the average of an integrable `g` exceeds a
positive height `t` lies in a Calderón–Zygmund cube of `g` at height `t`. -/
theorem exists_mem_calderonZygmundCubes_of_lt_setLAverage [Nonempty ι] (hg : ∫⁻ x, g x ≠ ∞)
    (ht : t ≠ 0) {k : ℤ} {m : ι → ℤ} (h : t < ⨍⁻ x in dyadicCube k m, g x ∂volume) :
    ∃ q ∈ calderonZygmundCubes g t, k ≤ q.1 ∧ dyadicCube k m ⊆ dyadicCube q.1 q.2 := by
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (volume_dyadicCube_pos k m).ne'
  let A : ℤ → ℝ≥0∞ := fun j => ⨍⁻ y in dyadicCube j (dyadicIndex j x), g y ∂volume
  -- The averages over the cubes containing `x` are eventually below `t`, since they are at most
  -- `∫⁻ g` divided by the volume of the cube.
  have hsmall : ∀ᶠ j in atTop, A j < t := by
    have hlim : Tendsto (fun j => (∫⁻ y, g y) / volume (dyadicCube j (dyadicIndex j x)))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_div (tendsto_volume_dyadicCube_atTop _) (.inr hg)
    filter_upwards [(tendsto_order.1 hlim).2 t (pos_iff_ne_zero.2 ht)] with j hj
    refine lt_of_le_of_lt ?_ hj
    simp only [A, setLAverage_eq]
    exact ENNReal.div_le_div_right (setLIntegral_le_lintegral _ _) _
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  obtain ⟨j₀, ⟨hkj₀, hj₀⟩, hmax⟩ := Int.exists_greatest_of_bdd (P := fun j => k ≤ j ∧ t < A j)
    ⟨N, fun j hj => le_of_not_gt fun hNj => (hN j hNj.le).not_gt hj.2⟩
    ⟨k, le_rfl, by simpa [A, mem_dyadicCube.1 hx] using h⟩
  refine ⟨(j₀, dyadicIndex j₀ x), ⟨hj₀, fun j m' hj hsub => ?_⟩, hkj₀,
    dyadicCube_subset_dyadicCube hkj₀ hx⟩
  have hm' : dyadicIndex j x = m' := mem_dyadicCube.1 (hsub (mem_dyadicCube_dyadicIndex j₀ x))
  subst hm'
  exact le_of_not_gt fun hlt => (hmax j ⟨hkj₀.trans hj.le, hlt⟩).not_gt hj

/-- In positive dimension, an integrable `g` is at most `t` almost everywhere off its
Calderón–Zygmund cubes at a positive height `t`. -/
theorem ae_le_of_forall_notMem_calderonZygmundCubes [Nonempty ι] (hg : AEMeasurable g)
    (hg' : ∫⁻ x, g x ≠ ∞) (ht : t ≠ 0) :
    ∀ᵐ x, (∀ q ∈ calderonZygmundCubes g t, x ∉ dyadicCube q.1 q.2) → g x ≤ t := by
  filter_upwards [ae_tendsto_setLAverage_dyadicCube hg hg'] with x hx hnot
  refine le_of_tendsto hx (Eventually.of_forall fun k => le_of_not_gt fun hlt => ?_)
  obtain ⟨q, hq, -, hsub⟩ := exists_mem_calderonZygmundCubes_of_lt_setLAverage hg' ht hlt
  exact hnot q hq (hsub (mem_dyadicCube_dyadicIndex k x))

private theorem pairwise_disjoint_calderonZygmundCubes :
    Pairwise (Function.onFun Disjoint fun q : calderonZygmundCubes g t => dyadicCube q.1.1 q.1.2) :=
  fun q q' hne => pairwiseDisjoint_calderonZygmundCubes q.2 q'.2 (Subtype.val_injective.ne hne)

/-- The union of the Calderón–Zygmund cubes is measurable. -/
theorem measurableSet_biUnion_calderonZygmundCubes (g : (ι → ℝ) → ℝ≥0∞) (t : ℝ≥0∞) :
    MeasurableSet (⋃ q ∈ calderonZygmundCubes g t, dyadicCube q.1 q.2) :=
  MeasurableSet.biUnion (to_countable _) fun q _ => measurableSet_dyadicCube q.1 q.2

/-- The **Calderón–Zygmund measure estimate**: `t` times the measure of the union of the
Calderón–Zygmund cubes of `g` at height `t` is at most the integral of `g` over that union. -/
theorem mul_volume_biUnion_calderonZygmundCubes_le :
    t * volume (⋃ q ∈ calderonZygmundCubes g t, dyadicCube q.1 q.2) ≤
      ∫⁻ x in ⋃ q ∈ calderonZygmundCubes g t, dyadicCube q.1 q.2, g x := by
  rw [biUnion_eq_iUnion,
    measure_iUnion pairwise_disjoint_calderonZygmundCubes fun q => measurableSet_dyadicCube _ _,
    lintegral_iUnion (fun q => measurableSet_dyadicCube _ _) pairwise_disjoint_calderonZygmundCubes,
    ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun q =>
    (mul_volume_lt_setLIntegral_of_mem_calderonZygmundCubes q.2).le

end Cubes

section Decomposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : (ι → ℝ) → E} {t : ℝ≥0∞}
  {q : ℤ × (ι → ℤ)} {x : ι → ℝ}

/-- The **bad part** of `f` on the dyadic cube `q`: `f` minus its average over the cube, on the
cube, and `0` off it. -/
noncomputable def calderonZygmundBad (f : (ι → ℝ) → E) (q : ℤ × (ι → ℤ)) : (ι → ℝ) → E :=
  (dyadicCube q.1 q.2).indicator fun x => f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume

@[simp]
theorem calderonZygmundBad_of_mem (hx : x ∈ dyadicCube q.1 q.2) :
    calderonZygmundBad f q x = f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume :=
  indicator_of_mem hx _

@[simp]
theorem calderonZygmundBad_of_notMem (hx : x ∉ dyadicCube q.1 q.2) :
    calderonZygmundBad f q x = 0 :=
  indicator_of_notMem hx _

/-- The **good part** of the Calderón–Zygmund decomposition of `f` at height `t`: `f` minus its
bad parts on the Calderón–Zygmund cubes of `‖f‖ₑ` at height `t`. It is the average of `f` on each
of these cubes (`TauCeti.calderonZygmundGood_of_mem`) and `f` off them
(`TauCeti.calderonZygmundGood_of_forall_notMem`). -/
noncomputable def calderonZygmundGood (f : (ι → ℝ) → E) (t : ℝ≥0∞) : (ι → ℝ) → E :=
  fun x => f x - ∑' q : calderonZygmundCubes (‖f ·‖ₑ) t, calderonZygmundBad f q x

/-- The **Calderón–Zygmund decomposition**: `f` is its good part plus the sum of its bad parts on
the Calderón–Zygmund cubes. At each point at most one bad part is nonzero. -/
theorem calderonZygmundGood_add_tsum_calderonZygmundBad (f : (ι → ℝ) → E) (t : ℝ≥0∞)
    (x : ι → ℝ) :
    calderonZygmundGood f t x +
      ∑' q : calderonZygmundCubes (‖f ·‖ₑ) t, calderonZygmundBad f q x = f x :=
  sub_add_cancel _ _

/-- On a Calderón–Zygmund cube, the good part is the average of `f` over the cube. -/
theorem calderonZygmundGood_of_mem (hq : q ∈ calderonZygmundCubes (‖f ·‖ₑ) t)
    (hx : x ∈ dyadicCube q.1 q.2) :
    calderonZygmundGood f t x = ⨍ y in dyadicCube q.1 q.2, f y ∂volume := by
  have hsum : ∑' q' : calderonZygmundCubes (‖f ·‖ₑ) t, calderonZygmundBad f q' x =
      calderonZygmundBad f q x := by
    refine tsum_eq_single (f := fun q' : calderonZygmundCubes (‖f ·‖ₑ) t =>
      calderonZygmundBad f q' x) ⟨q, hq⟩ fun q' hne => calderonZygmundBad_of_notMem fun hx' => ?_
    exact Set.disjoint_left.1 (pairwiseDisjoint_calderonZygmundCubes q'.2 hq
      fun h => hne (Subtype.ext h)) hx' hx
  rw [calderonZygmundGood, hsum, calderonZygmundBad_of_mem hx, sub_sub_cancel]

/-- Off the Calderón–Zygmund cubes, the good part is `f`. -/
theorem calderonZygmundGood_of_forall_notMem
    (hx : ∀ q ∈ calderonZygmundCubes (‖f ·‖ₑ) t, x ∉ dyadicCube q.1 q.2) :
    calderonZygmundGood f t x = f x := by
  simp [calderonZygmundGood, calderonZygmundBad_of_notMem (hx _ (Subtype.prop _))]

/-- The bad parts of an integrable function are integrable. -/
theorem integrable_calderonZygmundBad (hf : Integrable f) (q : ℤ × (ι → ℤ)) :
    Integrable (calderonZygmundBad f q) :=
  (hf.integrableOn.sub (integrableOn_const (volume_dyadicCube_ne_top q.1 q.2))).integrable_indicator
    (measurableSet_dyadicCube q.1 q.2)

/-- Each bad part has integral zero. -/
@[simp]
theorem integral_calderonZygmundBad [CompleteSpace E] (f : (ι → ℝ) → E) (q : ℤ × (ι → ℤ)) :
    ∫ x, calderonZygmundBad f q x = 0 := by
  rw [calderonZygmundBad, integral_indicator (measurableSet_dyadicCube q.1 q.2)]
  exact setAverage_sub_setAverage (volume_dyadicCube_ne_top q.1 q.2) f

/-- Each bad part has `L¹` norm at most twice the integral of `‖f‖` over its cube. -/
theorem lintegral_enorm_calderonZygmundBad_le (f : (ι → ℝ) → E) (q : ℤ × (ι → ℤ)) :
    ∫⁻ x, ‖calderonZygmundBad f q x‖ₑ ≤ 2 * ∫⁻ x in dyadicCube q.1 q.2, ‖f x‖ₑ := by
  simp_rw [calderonZygmundBad, enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator (measurableSet_dyadicCube q.1 q.2), two_mul]
  calc ∫⁻ x in dyadicCube q.1 q.2, ‖f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ
      ≤ ∫⁻ x in dyadicCube q.1 q.2, (‖f x‖ₑ + ‖⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ) :=
        lintegral_mono fun x => enorm_sub_le
    _ = (∫⁻ x in dyadicCube q.1 q.2, ‖f x‖ₑ) +
          ∫⁻ _ in dyadicCube q.1 q.2, ‖⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ :=
        lintegral_add_right _ measurable_const
    _ ≤ _ := by
        rw [setLIntegral_const, mul_comm]
        gcongr
        exact measure_mul_enorm_setAverage_le _ _ _

/-- In positive dimension, the good part of an integrable `f` at a positive height `t` is bounded
by `2ⁿ t` almost everywhere. -/
theorem ae_enorm_calderonZygmundGood_le [Nonempty ι] (hf : Integrable f) (ht : t ≠ 0) :
    ∀ᵐ x, ‖calderonZygmundGood f t x‖ₑ ≤ 2 ^ Fintype.card ι * t := by
  filter_upwards [ae_le_of_forall_notMem_calderonZygmundCubes hf.1.enorm
    hf.2.ne ht] with x hx
  by_cases hmem : ∃ q ∈ calderonZygmundCubes (‖f ·‖ₑ) t, x ∈ dyadicCube q.1 q.2
  · obtain ⟨q, hq, hxq⟩ := hmem
    rw [calderonZygmundGood_of_mem hq hxq]
    exact (enorm_setAverage_le_setLAverage _ _ _).trans
      (setLAverage_le_of_mem_calderonZygmundCubes hq)
  · push Not at hmem
    rw [calderonZygmundGood_of_forall_notMem hmem]
    exact (hx hmem).trans (le_mul_of_one_le_left' (one_le_pow₀ one_le_two))

/-- The good part has `L¹` norm at most that of `f`. -/
theorem lintegral_enorm_calderonZygmundGood_le (f : (ι → ℝ) → E) (t : ℝ≥0∞) :
    ∫⁻ x, ‖calderonZygmundGood f t x‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ := by
  set Ω := ⋃ q ∈ calderonZygmundCubes (‖f ·‖ₑ) t, dyadicCube q.1 q.2
  have hΩ : MeasurableSet Ω := measurableSet_biUnion_calderonZygmundCubes _ _
  rw [← lintegral_add_compl _ hΩ, ← lintegral_add_compl (fun x => ‖f x‖ₑ) hΩ]
  gcongr ?_ + ?_
  · simp only [Ω, biUnion_eq_iUnion]
    rw [lintegral_iUnion (fun q => measurableSet_dyadicCube _ _)
        pairwise_disjoint_calderonZygmundCubes,
      lintegral_iUnion (fun q => measurableSet_dyadicCube _ _)
        pairwise_disjoint_calderonZygmundCubes]
    refine ENNReal.tsum_le_tsum fun q => ?_
    rw [setLIntegral_congr_fun (measurableSet_dyadicCube _ _)
      fun x hx => by rw [calderonZygmundGood_of_mem q.2 hx], setLIntegral_const, mul_comm]
    exact measure_mul_enorm_setAverage_le _ _ _
  · refine (setLIntegral_congr_fun hΩ.compl fun x hx => ?_).le
    rw [calderonZygmundGood_of_forall_notMem fun q hq hxq => hx (mem_biUnion hq hxq)]

/-- The good part of an almost everywhere strongly measurable `f` is almost everywhere strongly
measurable: it is constant on each Calderón–Zygmund cube and equal to `f` off them. -/
theorem aestronglyMeasurable_calderonZygmundGood (hf : AEStronglyMeasurable f) (t : ℝ≥0∞) :
    AEStronglyMeasurable (calderonZygmundGood f t) := by
  set Ω := ⋃ q ∈ calderonZygmundCubes (‖f ·‖ₑ) t, dyadicCube q.1 q.2
  have hΩ : MeasurableSet Ω := measurableSet_biUnion_calderonZygmundCubes _ _
  rw [← Measure.restrict_univ (μ := volume), ← union_compl_self Ω, aestronglyMeasurable_union_iff]
  refine ⟨?_, ?_⟩
  · simp only [Ω, biUnion_eq_iUnion, aestronglyMeasurable_iUnion_iff]
    refine fun q =>
      (aestronglyMeasurable_const (b := ⨍ y in dyadicCube q.1.1 q.1.2, f y ∂volume)).congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_dyadicCube q.1.1 q.1.2)] with x hx
    rw [calderonZygmundGood_of_mem q.2 hx]
  · refine hf.restrict.congr ?_
    filter_upwards [ae_restrict_mem hΩ.compl] with x hx
    rw [calderonZygmundGood_of_forall_notMem fun q hq hxq => hx (mem_biUnion hq hxq)]

/-- The good part of an integrable `f` is integrable. -/
theorem integrable_calderonZygmundGood (hf : Integrable f) (t : ℝ≥0∞) :
    Integrable (calderonZygmundGood f t) :=
  ⟨aestronglyMeasurable_calderonZygmundGood hf.1 t, hasFiniteIntegral_iff_enorm.2 <|
    (lintegral_enorm_calderonZygmundGood_le f t).trans_lt (hasFiniteIntegral_iff_enorm.1 hf.2)⟩

/-- The bad parts of a function in `Lᵖ` are in `Lᵖ`. -/
theorem memLp_calderonZygmundBad {p : ℝ≥0∞} (hf : MemLp f p) (q : ℤ × (ι → ℤ)) :
    MemLp (calderonZygmundBad f q) p := by
  have : IsFiniteMeasure (volume.restrict (dyadicCube q.1 q.2)) :=
    isFiniteMeasure_restrict.2 (volume_dyadicCube_ne_top q.1 q.2)
  rw [calderonZygmundBad,
    memLp_indicator_iff_restrict (measurableSet_dyadicCube q.1 q.2).nullMeasurableSet]
  exact hf.restrict _ |>.sub (memLp_const _)

/-- In positive dimension, the square of the `L²` norm of the good part of an integrable `f` at a
positive height `t` is at most `2ⁿ t ‖f‖₁`: the good part is bounded by `2ⁿ t` and has `L¹` norm at
most `‖f‖₁`. -/
theorem sq_eLpNorm_calderonZygmundGood_le [Nonempty ι] (hf : Integrable f) (ht : t ≠ 0) :
    eLpNorm (calderonZygmundGood f t) 2 volume ^ 2 ≤
      2 ^ Fintype.card ι * t * ∫⁻ x, ‖f x‖ₑ := by
  have hg := aestronglyMeasurable_calderonZygmundGood hf.1 t
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hg
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [h]
  calc ∫⁻ x, ‖calderonZygmundGood f t x‖ₑ ^ 2
      ≤ ∫⁻ x, 2 ^ Fintype.card ι * t * ‖calderonZygmundGood f t x‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_enorm_calderonZygmundGood_le hf ht] with x hx
        rw [sq]
        gcongr
    _ = 2 ^ Fintype.card ι * t * ∫⁻ x, ‖calderonZygmundGood f t x‖ₑ :=
        lintegral_const_mul'' _ hg.enorm
    _ ≤ 2 ^ Fintype.card ι * t * ∫⁻ x, ‖f x‖ₑ :=
        mul_le_mul_right (lintegral_enorm_calderonZygmundGood_le f t) _

/-- In positive dimension, the good part of an integrable `f` at a finite positive height is in
`L²`. -/
theorem memLp_two_calderonZygmundGood [Nonempty ι] (hf : Integrable f) (ht : t ≠ 0)
    (ht' : t ≠ ∞) : MemLp (calderonZygmundGood f t) 2 := by
  have h := (sq_eLpNorm_calderonZygmundGood_le hf ht).trans_lt <|
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ht'.lt_top) hf.2
  exact memLp_iff.2 ((WithTop.pow_lt_top_iff.1 h).resolve_right two_ne_zero)

/-- At each point at most one bad part is nonzero. -/
theorem subsingleton_support_calderonZygmundBad (f : (ι → ℝ) → E) (t : ℝ≥0∞) (x : ι → ℝ) :
    (Function.support fun q : calderonZygmundCubes (‖f ·‖ₑ) t =>
      calderonZygmundBad f q x).Subsingleton := by
  have hmem {q : ℤ × (ι → ℤ)} (h : calderonZygmundBad f q x ≠ 0) : x ∈ dyadicCube q.1 q.2 :=
    by_contra fun hx => h (calderonZygmundBad_of_notMem hx)
  intro q hq q' hq'
  by_contra hne
  exact Set.disjoint_left.1 (pairwiseDisjoint_calderonZygmundCubes q.2 q'.2
    fun h => hne (Subtype.ext h)) (hmem hq) (hmem hq')

/-- If `f` and its good part at height `t` are in `Lᵖ` for a finite `p ≥ 1`, then the bad parts sum
in `Lᵖ` to `f` minus the good part. -/
theorem hasSum_toLp_calderonZygmundBad {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (hf : MemLp f p)
    (hg : MemLp (calderonZygmundGood f t) p) :
    HasSum (fun q : calderonZygmundCubes (‖f ·‖ₑ) t => (memLp_calderonZygmundBad hf q.1).toLp _)
      ((hf.sub hg).toLp (f - calderonZygmundGood f t)) := by
  set 𝒬 := calderonZygmundCubes (‖f ·‖ₑ) t
  set F : Finset 𝒬 → (ι → ℝ) → E := fun s x => ∑ q ∈ s, calderonZygmundBad f q x
  -- Pointwise, `f - g` is the sum of the bad parts, which has at most one nonzero term.
  have hsum (x : ι → ℝ) : (f - calderonZygmundGood f t) x =
      ∑' q : 𝒬, calderonZygmundBad f q x := by
    rw [Pi.sub_apply, ← calderonZygmundGood_add_tsum_calderonZygmundBad f t x, add_sub_cancel_left]
  have hpt (x : ι → ℝ) := subsingleton_support_calderonZygmundBad f t x
  have hconv (x : ι → ℝ) : HasSum (fun q : 𝒬 => calderonZygmundBad f q x)
      (∑' q : 𝒬, calderonZygmundBad f q x) :=
    (summable_of_hasFiniteSupport (hpt x).finite).hasSum
  simp only [HasSum, SummationFilter.unconditional_filter]
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine (tendsto_eLpNorm_sub_of_ae_tendsto (f := F) (C := 1)
    (zero_lt_one.trans_le Fact.out).ne' hp
    (.of_forall fun s => Finset.aestronglyMeasurable_fun_sum s fun q _ =>
      (memLp_calderonZygmundBad hf q.1).aestronglyMeasurable)
    (hf.sub hg).aestronglyMeasurable (hf.sub hg)
    (.of_forall fun s => .of_forall fun x => by
      simpa [F, hsum x] using (hpt x).enorm_sum_sub_tsum_le s)
    (.of_forall fun x => by
      simpa [F, hsum x, HasSum, SummationFilter.unconditional_filter] using hconv x)).congr
    fun s => eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_finsetSum s fun q : 𝒬 => (memLp_calderonZygmundBad hf q.1).toLp _,
    ae_all_iff.2 fun q : 𝒬 => (memLp_calderonZygmundBad hf q.1).coeFn_toLp,
    (hf.sub hg).coeFn_toLp] with x hx hq hfg
  simp only [Pi.sub_apply, F, hx, Finset.sum_apply, hq, hfg]

end Decomposition

end TauCeti
