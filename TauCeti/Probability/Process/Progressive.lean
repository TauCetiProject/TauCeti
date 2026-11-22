/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Progressive measurability and right-continuous adapted processes

A strongly adapted process on a second-countable linearly ordered time index with the order
topology and measurable open sets, having everywhere right-continuous paths into a pseudometrizable
space, is strongly progressive on its original filtration. No completeness or right continuity of
the filtration is required, and no separability is required on the state space. In particular, the
result applies to adapted càdlàg processes and permits use of the progressive stopped-evaluation
API. Restricting a strongly progressive process to an event measurable at every time also preserves
strong progressivity.

On each fixed horizon `T`, right-endpoint samples are taken in finite exhaustions of a countable
dense set augmented with `T` and the right-isolated points below `T`. These approximations are
measurable for the horizon's product sigma algebra; they need not be adapted at earlier times.
Almost-sure path regularity alone does not give the literal conclusion for a raw version.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §1.
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

/-- Restricting a progressive process to an event measurable at every time preserves
progressivity. No topology on the time or state space is needed. -/
theorem MeasureTheory.IsProgressive.indicator
    {ι Ω E : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    [MeasurableSpace ι] [MeasurableSpace E] [Zero E]
    {ℱ : Filtration ι m} {X : ι → Ω → E} {A : Set Ω}
    (hX : IsProgressive ℱ X) (hA : ∀ t, MeasurableSet[ℱ t] A) :
    IsProgressive ℱ (fun t ↦ A.indicator (X t)) :=
  fun T ↦ (hX T).indicator ((hA T).preimage measurable_snd)

/-- Restricting a strongly progressive process to an event measurable at every time preserves
strong progressivity. No topology on the time index is needed. -/
theorem MeasureTheory.IsStronglyProgressive.indicator
    {ι Ω E : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    [MeasurableSpace ι] [TopologicalSpace E] [Zero E]
    {ℱ : Filtration ι m} {X : ι → Ω → E} {A : Set Ω}
    (hX : IsStronglyProgressive ℱ X) (hA : ∀ t, MeasurableSet[ℱ t] A) :
    IsStronglyProgressive ℱ (fun t ↦ A.indicator (X t)) :=
  fun T ↦ (hX T).indicator ((hA T).preimage measurable_snd)

/-- A strongly adapted process on a second-countable order-topological time index with measurable
open sets and everywhere right-continuous paths into a pseudometrizable space is strongly
progressive on its original filtration. The state space need not be separable. -/
theorem MeasureTheory.StronglyAdapted.isStronglyProgressive_of_isRightContinuous
    {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    {m : MeasurableSpace Ω} [TopologicalSpace E] [PseudoMetrizableSpace E]
    {ℱ : Filtration ι m} {u : ι → Ω → E} (hu : StronglyAdapted ℱ u)
    (hc : ∀ ω, IsRightContinuous (fun t => u t ω)) : IsStronglyProgressive ℱ u := by
  classical
  intro T
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  let S : Set ι := insert T ((D ∪ {x : ι | ∃ y, x ⋖ y}) ∩ Iic T)
  have hSc : S.Countable :=
    ((hDc.union countable_setOfPred_covBy_right).mono inter_subset_left).insert T
  obtain ⟨seq, hseq⟩ := hSc.exists_surjective ⟨T, mem_insert T _⟩
  let F (n : ℕ) : Finset ι := insert T ((Finset.range n).image fun k => (seq k : ι))
  have hTF (n : ℕ) : T ∈ F n := Finset.mem_insert_self _ _
  have hFT (n : ℕ) : ∀ x ∈ F n, x ≤ T := by
    rintro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact le_rfl
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx'
      rcases (seq k).property with hT | ⟨_, hxT⟩
      · exact hT.le
      · exact hxT
  have hF_mono {m n : ℕ} (hmn : m ≤ n) : F m ⊆ F n :=
    Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.range_mono hmn))
  have hS_mem (x : ι) (hx : x ∈ S) : ∃ N, x ∈ F N := by
    obtain ⟨k, hk⟩ := hseq ⟨x, hx⟩
    refine ⟨k + 1, Finset.mem_insert_of_mem (Finset.mem_image.mpr ?_)⟩
    exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), congrArg Subtype.val hk⟩
  let sampleSet (n : ℕ) (t : Iic T) : Finset ι := (F n).filter fun x => (t : ι) ≤ x
  have sampleSet_nonempty (n : ℕ) (t : Iic T) : (sampleSet n t).Nonempty :=
    ⟨T, Finset.mem_filter.mpr ⟨hTF n, t.property⟩⟩
  let sample (n : ℕ) (t : Iic T) : ι := (sampleSet n t).min' (sampleSet_nonempty n t)
  have hle (n : ℕ) (t : Iic T) : (t : ι) ≤ sample n t :=
    (Finset.mem_filter.mp (Finset.min'_mem _ (sampleSet_nonempty n t))).2
  have hsample_mem (n : ℕ) (t : Iic T) : sample n t ∈ F n :=
    (Finset.mem_filter.mp (Finset.min'_mem _ (sampleSet_nonempty n t))).1
  have hT_le (n : ℕ) (t : Iic T) : sample n t ≤ T := hFT n _ (hsample_mem n t)
  have hmin_le (n : ℕ) (t : Iic T) {x : ι} (hx : x ∈ F n) (htx : (t : ι) ≤ x) :
      sample n t ≤ x :=
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hx, htx⟩)
  let : MeasurableSpace Ω := ℱ T
  have hm (n : ℕ) : StronglyMeasurable (fun p : Iic T × Ω => u (sample n p.1) p.2) := by
    let : MeasurableSpace (F n) := ⊤
    let sampleIdx (t : Iic T) : F n := ⟨sample n t, hsample_mem n t⟩
    have hmeas : Measurable sampleIdx := by
      intro s _
      have heq : sampleIdx ⁻¹' s = ⋃ x ∈ s, sampleIdx ⁻¹' {x} := by
        ext t; simp
      rw [heq]
      refine MeasurableSet.biUnion s.to_countable fun x _ => ?_
      have hpre : sampleIdx ⁻¹' {x} =
          {t : Iic T | (t : ι) ≤ x.val} ∩
            ⋂ y ∈ F n, ⋂ (_ : y < x.val), {t : Iic T | y < (t : ι)} := by
        ext t
        simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff, sampleIdx, mem_inter_iff,
          mem_ofPred_eq, mem_iInter]
        constructor
        · intro h
          refine ⟨h ▸ hle n t, fun y hyF hyx => ?_⟩
          by_contra! hty
          exact absurd (h ▸ hmin_le n t hyF hty) (not_le_of_gt hyx)
        · rintro ⟨htx, hlt⟩
          refine le_antisymm (hmin_le n t x.property htx) ?_
          by_contra! hlt_x
          exact absurd (hlt (sample n t) (hsample_mem n t) hlt_x) (not_lt_of_ge (hle n t))
      rw [hpre]
      exact (measurableSet_Iic.preimage measurable_subtypeVal).inter
        (MeasurableSet.biInter (F n).countable_toSet fun y _ =>
          MeasurableSet.iInter fun _ => measurableSet_Ioi.preimage measurable_subtypeVal)
    have hs : StronglyMeasurable (Function.uncurry fun x : F n => u x.val) :=
      stronglyMeasurable_uncurry_of_countable fun x =>
        (hu x.val).mono (ℱ.mono (hFT n x.val x.property))
    exact hs.comp_measurable ((hmeas.comp measurable_fst).prodMk measurable_snd)
  apply stronglyMeasurable_of_tendsto atTop hm
  apply tendsto_pi_nhds.mpr
  rintro ⟨⟨t, htT⟩, ω⟩
  refine (continuousWithinAt_Ioi_iff_Ici.mp (hc ω t)).tendsto.comp ?_
  rcases eq_or_lt_of_le htT with rfl | htT_lt
  · have hconst (n : ℕ) : sample n ⟨t, htT⟩ = t :=
      le_antisymm (hT_le n ⟨t, htT⟩) (hle n ⟨t, htT⟩)
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall fun n => hle n ⟨t, htT⟩⟩
    simpa only [Function.comp_def, hconst] using tendsto_const_nhds
  · refine tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall fun n => hle n ⟨t, htT⟩⟩
    rw [tendsto_iff_forall_eventually_mem]
    intro V hV
    obtain ⟨v, ⟨htv, hvT⟩, hvV⟩ :=
      (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset htT_lt).mp (mem_nhdsWithin_of_mem_nhds hV)
    by_cases hcov : t ⋖ v
    · obtain ⟨N, hNT⟩ := hS_mem t (Or.inr ⟨Or.inr ⟨v, hcov⟩, htT⟩)
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hvV ⟨hle n ⟨t, htT⟩, (hmin_le n ⟨t, htT⟩ (hF_mono hn hNT) le_rfl).trans_lt htv⟩
    · obtain ⟨d, hdD, htd, hdv⟩ := hDd.exists_mem_open isOpen_Ioo
        ((not_covBy_iff_exists_mem_Ioo htv).mp hcov)
      obtain ⟨N, hNd⟩ := hS_mem d (Or.inr ⟨Or.inl hdD, hdv.le.trans hvT⟩)
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hvV ⟨hle n ⟨t, htT⟩, (hmin_le n ⟨t, htT⟩ (hF_mono hn hNd) htd.le).trans_lt hdv⟩

/-- An adapted process on a second-countable order-topological time index with measurable open
sets and everywhere right-continuous paths in a second-countable pseudometrizable Borel state
space is progressive, without usual-filtration assumptions. -/
theorem MeasureTheory.Adapted.isProgressive_of_isRightContinuous
    {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    {m : MeasurableSpace Ω} [TopologicalSpace E] [PseudoMetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {ℱ : Filtration ι m} {u : ι → Ω → E} (hu : Adapted ℱ u)
    (hc : ∀ ω, IsRightContinuous (fun t => u t ω)) : IsProgressive ℱ u :=
  ((stronglyAdapted_iff_adapted.mpr hu).isStronglyProgressive_of_isRightContinuous hc).isProgressive
