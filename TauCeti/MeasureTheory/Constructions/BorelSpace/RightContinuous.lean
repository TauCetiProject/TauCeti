/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import TauCeti.Topology.Order.LeftRight
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Measurability of running maxima and right-hand limits of right-continuous processes

The event `{∃ t ≤ T, a < X_t}`, the running maximum `sup_{t ≤ T} X_t`, and the convergence set
`{x | ∃ y, Tendsto (fun t ↦ f t x) (𝓝[>] a) (𝓝 y)}` of a family indexed by a real parameter involve
uncountably many times, so they need not be measurable even when every slice is. When the paths are
right-continuous, countably many times determine both operations:

* If the paths of `X` are almost surely right-continuous before `T` and the time set is second
  countable (for instance `ℝ≥0` or `ℕ`), the running maximum agrees almost everywhere with a
  supremum over countably many times, hence is almost everywhere measurable whenever every `X_t` is.
* If `f : ℝ → X → Y` takes values in a complete second-countable metric space, is measurable at
  each rational in `(a, b)`, and is right-continuous on `(a, b)` at every point of a measurable
  set `s`, then the set of `x ∈ s` where `f t x` converges as `t → a⁺` — and more generally where
  the limit lies in a given Borel set `T ⊆ Y` — is measurable.

## Main declarations

* `MeasureTheory.exists_countable_subset_Iic_iSup_ae_eq`: the running supremum of an `ℝ≥0∞`-valued
  process with right-continuous paths before `T` agrees almost everywhere with the supremum over a
  countable set of times `≤ T`.
* `MeasureTheory.exists_countable_subset_Iic_iSup_ofReal_ae_eq` and
  `MeasureTheory.exists_countable_subset_Iic_iSup_eNorm_ae_eq`: specializations to `ENNReal.ofReal`
  of a real-valued process and `‖·‖ₑ` of a `ContinuousENorm`-valued process.
* `MeasureTheory.aemeasurable_iSup_le`, `MeasureTheory.aemeasurable_iSup_le_ofReal`, and
  `MeasureTheory.aemeasurable_iSup_le_eNorm`: almost everywhere measurability of the running
  maximum for `ℝ≥0∞`-, `ℝ`-, and `ContinuousENorm`-valued right-continuous processes.
* `MeasureTheory.measurableSet_setOf_exists_tendsto_nhdsGT` and
  `MeasureTheory.measurableSet_setOf_exists_mem_tendsto_nhdsGT`: measurability of the set of
  points where a right-continuous family converges as `t → a⁺` (resp. converges to a limit in a
  Borel set `T`).
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

/-- The running supremum `⨆ t ≤ T, Y t ω` of an `ℝ≥0∞`-valued process whose paths are almost
surely right-continuous before `T` agrees almost everywhere with the supremum over a single
countable set of times `≤ T`. -/
theorem exists_countable_subset_Iic_iSup_ae_eq {Y : ι → Ω → ℝ≥0∞} {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ Y u ω) (Ioi t) t) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧
      (fun ω ↦ ⨆ t ≤ T, Y t ω) =ᵐ[μ] fun ω ↦ ⨆ t ∈ S, Y t ω := by
  obtain ⟨S, hSc, hST, hS⟩ :=
    TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt (α := ℝ≥0∞) T
  refine ⟨S, hSc, hST, ?_⟩
  filter_upwards [hcont] with ω hω
  refine le_antisymm ?_ (iSup₂_le fun s hs ↦ le_iSup₂_of_le s (hST hs) le_rfl)
  refine iSup₂_le fun t htT ↦ le_of_forall_lt fun a ha ↦ ?_
  obtain ⟨s, hs, has⟩ := hS hω htT ha
  exact has.trans_le (le_iSup₂ (f := fun s _ ↦ Y s ω) s hs)

/-- The running supremum `⨆ t ≤ T, Y t ω` of an `ℝ≥0∞`-valued process with almost everywhere
measurable values on `(-∞, T]` and almost surely right-continuous paths before `T` is almost
everywhere measurable. -/
theorem aemeasurable_iSup_le {Y : ι → Ω → ℝ≥0∞} {T : ι}
    (hY : ∀ t ≤ T, AEMeasurable (Y t) μ)
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ Y u ω) (Ioi t) t) :
    AEMeasurable (fun ω ↦ ⨆ t ≤ T, Y t ω) μ := by
  obtain ⟨S, hSc, hST, hae⟩ := exists_countable_subset_Iic_iSup_ae_eq hcont
  have := hSc.to_subtype
  refine (AEMeasurable.iSup fun s : S ↦ hY s (hST s.2)).congr ?_
  filter_upwards [hae] with ω hω
  rw [hω, iSup_subtype']

/-- For a real-valued process whose paths are almost surely right-continuous before `T`, the
running supremum `⨆ t ≤ T, ENNReal.ofReal (X t ω)` agrees almost everywhere with the supremum over
a countable set of times `≤ T`. -/
theorem exists_countable_subset_Iic_iSup_ofReal_ae_eq {X : ι → Ω → ℝ} {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧
      (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (X t ω)) =ᵐ[μ] fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (X t ω) :=
  exists_countable_subset_Iic_iSup_ae_eq <| hcont.mono fun _ hω t ht ↦
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hω t ht)

/-- The running maximum `sup_{t ≤ T} X_t` of a process whose values `X_t` are almost everywhere
measurable and whose paths are almost surely right-continuous before `T` is almost everywhere
measurable: it agrees almost everywhere with the supremum over a countable set of times. -/
theorem aemeasurable_iSup_le_ofReal {X : ι → Ω → ℝ} (hX : ∀ t, AEMeasurable (X t) μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    AEMeasurable (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (X t ω)) μ :=
  aemeasurable_iSup_le (fun t _ ↦ (hX t).ennreal_ofReal) <| hcont.mono fun _ hω t ht ↦
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hω t ht)

/-- For a process valued in a `ContinuousENorm` space whose paths are almost surely
right-continuous before `T`, the running extended norm supremum `⨆ t ≤ T, ‖X t ω‖ₑ` agrees almost
everywhere with the supremum over a countable set of times `≤ T`. -/
theorem exists_countable_subset_Iic_iSup_eNorm_ae_eq {E : Type*} [TopologicalSpace E]
    [ContinuousENorm E] {X : ι → Ω → E} {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧
      (fun ω ↦ ⨆ t ≤ T, ‖X t ω‖ₑ) =ᵐ[μ] fun ω ↦ ⨆ t ∈ S, ‖X t ω‖ₑ :=
  exists_countable_subset_Iic_iSup_ae_eq <| hcont.mono fun _ hω t ht ↦
    ContinuousENorm.continuous_eNorm.continuousAt.comp_continuousWithinAt (hω t ht)

/-- The running extended norm supremum `⨆ t ≤ T, ‖X t ω‖ₑ` of a `ContinuousENorm`-valued process
with almost everywhere measurable extended norms on `(-∞, T]` and almost surely right-continuous
paths before `T` is almost everywhere measurable. -/
theorem aemeasurable_iSup_le_eNorm {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {X : ι → Ω → E} {T : ι} (hX : ∀ t ≤ T, AEMeasurable (fun ω ↦ ‖X t ω‖ₑ) μ)
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t) :
    AEMeasurable (fun ω ↦ ⨆ t ≤ T, ‖X t ω‖ₑ) μ :=
  aemeasurable_iSup_le hX <| hcont.mono fun _ hω t ht ↦
    ContinuousENorm.continuous_eNorm.continuousAt.comp_continuousWithinAt (hω t ht)

section RightLimit

open Filter Metric
open scoped Topology

/-- A function `f : ℝ → Y` into a complete pseudometric space that is right-continuous on `(a, b)`
has a right-hand limit as `t → a⁺` if and only if its values on rationals in `(a, b)` satisfy the
Cauchy condition near `a⁺`. -/
private theorem exists_tendsto_nhdsGT_iff_rat {Y : Type*} [PseudoMetricSpace Y] [CompleteSpace Y]
    {f : ℝ → Y} {a b : ℝ} (hab : a < b)
    (hrc : ∀ r ∈ Ioo a b, ContinuousWithinAt f (Ioi r) r) :
    (∃ y : Y, Tendsto f (𝓝[>] a) (𝓝 y)) ↔
      ∀ k : ℕ, ∃ m : ℕ,
        ∀ p : ℚ, a < (p : ℝ) → (p : ℝ) < min b (a + 1 / ((m : ℝ) + 1)) →
        ∀ q : ℚ, a < (q : ℝ) → (q : ℝ) < min b (a + 1 / ((m : ℝ) + 1)) →
          dist (f p) (f q) ≤ 1 / ((k : ℝ) + 1) := by
  constructor
  · rintro ⟨y, hy⟩ k
    have hε : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by positivity
    obtain ⟨u, hu, huf⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 (Metric.tendsto_nhds.1 hy _ hε)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hu)
    refine ⟨m, fun p hp hp' q hq hq' ↦ ?_⟩
    have hpm : (p : ℝ) ∈ Ioc a u := ⟨hp, hp'.le.trans ((min_le_right _ _).trans (by linarith))⟩
    have hqm : (q : ℝ) ∈ Ioc a u := ⟨hq, hq'.le.trans ((min_le_right _ _).trans (by linarith))⟩
    have hsum : 1 / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) = 1 / ((k : ℝ) + 1) := by
      field_simp
      ring
    have hpy : dist (f p) y < 1 / (2 * ((k : ℝ) + 1)) := huf hpm
    have hqy : dist (f q) y < 1 / (2 * ((k : ℝ) + 1)) := huf hqm
    linarith [dist_triangle_right (f p) (f q) y]
  · intro hcauchy
    have hreal (k : ℕ) : ∃ R > a, ∀ r ∈ Ioo a R, ∀ s ∈ Ioo a R,
        dist (f r) (f s) ≤ 1 / ((k : ℝ) + 1) := by
      obtain ⟨m, hm⟩ := hcauchy k
      refine ⟨min b (a + 1 / ((m : ℝ) + 1)),
        lt_min hab (lt_add_of_pos_right a (by positivity)), fun r hr s hs ↦ ?_⟩
      have hstep1 (p : ℚ) (hp : (p : ℝ) ∈ Ioo a (min b (a + 1 / ((m : ℝ) + 1)))) :
          dist (f p) (f s) ≤ 1 / ((k : ℝ) + 1) := by
        obtain ⟨q, -, hq, hqlim⟩ := Real.exists_seq_rat_strictAnti_tendsto s
        have hqlim' : Tendsto (fun n ↦ (q n : ℝ)) atTop (𝓝[>] s) :=
          tendsto_nhdsWithin_iff.2 ⟨hqlim, .of_forall hq⟩
        have hlim := (tendsto_const_nhds (x := f p)).dist
          ((hrc s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩).tendsto.comp hqlim')
        refine le_of_tendsto hlim ?_
        filter_upwards [hqlim.eventually (gt_mem_nhds hs.2)] with n hn
        exact hm p hp.1 hp.2 (q n) (hs.1.trans (hq n)) hn
      obtain ⟨p, -, hp, hplim⟩ := Real.exists_seq_rat_strictAnti_tendsto r
      have hplim' : Tendsto (fun n ↦ (p n : ℝ)) atTop (𝓝[>] r) :=
        tendsto_nhdsWithin_iff.2 ⟨hplim, .of_forall hp⟩
      have hlim := ((hrc r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩).tendsto.comp hplim').dist
        (tendsto_const_nhds (x := f s))
      refine le_of_tendsto hlim ?_
      filter_upwards [hplim.eventually (gt_mem_nhds hr.2)] with n hn
      exact hstep1 (p n) ⟨hr.1.trans (hp n), hn⟩
    have hcau : Cauchy (map f (𝓝[>] a)) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε ↦ ?_⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨R, hR, hRle⟩ := hreal k
      refine ⟨f '' Ioo a R, image_mem_map (Ioo_mem_nhdsGT hR), ?_⟩
      rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
      exact (hRle r hr s hs).trans_lt hk
    exact CompleteSpace.complete hcau

/-- For a family `f : ℝ → X → Y` valued in a complete second-countable pseudometric space that is
measurable at each rational in `(a, b)` and right-continuous on `(a, b)` at every point of a
measurable set `s`, the set of points `x ∈ s` where `f t x` converges as `t → a⁺` is measurable. -/
theorem measurableSet_setOf_exists_tendsto_nhdsGT {X Y : Type*} [MeasurableSpace X]
    [PseudoMetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {f : ℝ → X → Y} {s : Set X} {a b : ℝ} (hab : a < b)
    (hs : MeasurableSet s) (hf : ∀ q : ℚ, a < (q : ℝ) → (q : ℝ) < b → Measurable (f q))
    (hrc : ∀ x ∈ s, ∀ r ∈ Ioo a b, ContinuousWithinAt (fun t ↦ f t x) (Ioi r) r) :
    MeasurableSet {x ∈ s | ∃ y : Y, Tendsto (fun t ↦ f t x) (𝓝[>] a) (𝓝 y)} := by
  have heq : {x ∈ s | ∃ y : Y, Tendsto (fun t ↦ f t x) (𝓝[>] a) (𝓝 y)} =
      s ∩ ⋂ k : ℕ, ⋃ m : ℕ,
        ⋂ (p : ℚ) (_ : a < (p : ℝ)) (_ : (p : ℝ) < min b (a + 1 / ((m : ℝ) + 1)))
          (q : ℚ) (_ : a < (q : ℝ)) (_ : (q : ℝ) < min b (a + 1 / ((m : ℝ) + 1))),
          {x | dist (f p x) (f q x) ≤ 1 / ((k : ℝ) + 1)} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
    exact and_congr_right fun hx ↦ exists_tendsto_nhdsGT_iff_rat hab (hrc x hx)
  rw [heq]
  refine hs.inter (MeasurableSet.iInter fun k ↦ MeasurableSet.iUnion fun m ↦
    MeasurableSet.iInter fun p ↦ MeasurableSet.iInter fun hp ↦ MeasurableSet.iInter fun hp' ↦
    MeasurableSet.iInter fun q ↦ MeasurableSet.iInter fun hq ↦ MeasurableSet.iInter fun hq' ↦ ?_)
  exact measurableSet_le
    ((hf p hp (hp'.trans_le (min_le_left _ _))).dist (hf q hq (hq'.trans_le (min_le_left _ _))))
    measurable_const

/-- For a family `f : ℝ → X → Y` valued in a complete second-countable metric space that is
measurable at each rational in `(a, b)` and right-continuous on `(a, b)` at every point of a
measurable set `s`, the set of points `x ∈ s` where `f t x` converges as `t → a⁺` to a limit in a
measurable set `T ⊆ Y` is measurable. -/
theorem measurableSet_setOf_exists_mem_tendsto_nhdsGT {X Y : Type*} [MeasurableSpace X]
    [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : ℝ → X → Y} {s : Set X} {T : Set Y} {a b : ℝ} (hab : a < b)
    (hs : MeasurableSet s) (hT : MeasurableSet T)
    (hf : ∀ q : ℚ, a < (q : ℝ) → (q : ℝ) < b → Measurable (f q))
    (hrc : ∀ x ∈ s, ∀ r ∈ Ioo a b, ContinuousWithinAt (fun t ↦ f t x) (Ioi r) r) :
    MeasurableSet {x ∈ s | ∃ y ∈ T, Tendsto (fun t ↦ f t x) (𝓝[>] a) (𝓝 y)} := by
  set A : Set X := {x ∈ s | ∃ y : Y, Tendsto (fun t ↦ f t x) (𝓝[>] a) (𝓝 y)}
  have hA : MeasurableSet A := measurableSet_setOf_exists_tendsto_nhdsGT hab hs hf hrc
  obtain ⟨q, hqanti, hqgt, hqlim⟩ := Real.exists_seq_rat_strictAnti_tendsto a
  obtain ⟨N, hN⟩ := (hqlim.eventually (gt_mem_nhds hab)).exists
  have hqlt (n : ℕ) : (q (n + N) : ℝ) < b :=
    lt_of_le_of_lt (Rat.cast_le.2 (hqanti.antitone (Nat.le_add_left N n))) hN
  have hqNHDS : Tendsto (fun n ↦ (q (n + N) : ℝ)) atTop (𝓝[>] a) :=
    tendsto_nhdsWithin_iff.2 ⟨hqlim.comp (tendsto_add_atTop_nat N), .of_forall fun n ↦ hqgt _⟩
  let L : A → Y := fun x ↦ x.2.2.choose
  have hL : Measurable L := by
    refine measurable_of_tendsto_metrizable (f := fun n (x : A) ↦ f (q (n + N)) x.1)
      (fun n ↦ (hf (q (n + N)) (hqgt _) (hqlt n)).comp measurable_subtype_coe) ?_
    rw [tendsto_pi_nhds]
    intro x
    exact x.2.2.choose_spec.comp hqNHDS
  have heq : {x ∈ s | ∃ y ∈ T, Tendsto (fun t ↦ f t x) (𝓝[>] a) (𝓝 y)} =
      ((↑) : A → X) '' (L ⁻¹' T) := by
    ext x
    constructor
    · rintro ⟨hxs, y, hyT, hy⟩
      have hxA : x ∈ A := ⟨hxs, y, hy⟩
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      have hLy : L ⟨x, hxA⟩ = y := tendsto_nhds_unique hxA.2.choose_spec hy
      simpa [hLy] using hyT
    · rintro ⟨⟨x, hxA⟩, hxT, rfl⟩
      exact ⟨hxA.1, L ⟨x, hxA⟩, hxT, hxA.2.choose_spec⟩
  rw [heq]
  exact (MeasurableEmbedding.subtype_coe hA).measurableSet_image.2 (hT.preimage hL)

end RightLimit

end MeasureTheory
