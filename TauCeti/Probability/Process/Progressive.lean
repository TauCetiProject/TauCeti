/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.Probability.Process.Filtration.Progressive

/-!
# Progressive measurability of stochastic processes

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

For progressive processes, pathwise time-a.e. agreement lifts to product-a.e. agreement
under arbitrary s-finite time and sample measures.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §1.
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

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

section RightSample

open Classical in
/-- Given a finite horizon grid `F` containing `T`, `rightSample F T hTF t` picks the least point
of `F` at or above `t ∈ (-∞, T]`. -/
private noncomputable def rightSample {ι : Type*} [LinearOrder ι] (F : Finset ι) (T : ι)
    (hTF : T ∈ F) (t : Iic T) : ι :=
  (F.filter fun x => (t : ι) ≤ x).min' ⟨T, Finset.mem_filter.mpr ⟨hTF, t.property⟩⟩

private theorem le_rightSample {ι : Type*} [LinearOrder ι] (F : Finset ι) (T : ι)
    (hTF : T ∈ F) (t : Iic T) : (t : ι) ≤ rightSample F T hTF t := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

private theorem rightSample_mem {ι : Type*} [LinearOrder ι] (F : Finset ι) (T : ι)
    (hTF : T ∈ F) (t : Iic T) : rightSample F T hTF t ∈ F := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

private theorem rightSample_min_le {ι : Type*} [LinearOrder ι] (F : Finset ι) (T : ι)
    (hTF : T ∈ F) (t : Iic T) {x : ι} (hx : x ∈ F) (htx : (t : ι) ≤ x) :
    rightSample F T hTF t ≤ x := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hx, htx⟩)

private theorem measurable_rightSample {ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι] (F : Finset ι) (T : ι)
    (hTF : T ∈ F) :
    letI : MeasurableSpace F := ⊤
    Measurable (fun t : Iic T => (⟨rightSample F T hTF t, rightSample_mem F T hTF t⟩ : F)) := by
  let _ : MeasurableSpace F := ⊤
  intro s _
  have heq : (fun t : Iic T => (⟨rightSample F T hTF t, rightSample_mem F T hTF t⟩ : F)) ⁻¹' s =
      ⋃ x ∈ s, {t : Iic T | rightSample F T hTF t = x.val} := by
    ext t
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq, exists_prop]
    exact ⟨fun ht => ⟨_, ht, rfl⟩, fun ⟨x, hx, hxt⟩ => by
      have : (⟨rightSample F T hTF t, rightSample_mem F T hTF t⟩ : F) = x := Subtype.ext hxt
      rwa [this]⟩
  rw [heq]
  refine MeasurableSet.biUnion s.to_countable fun x _ => ?_
  have hpre : {t : Iic T | rightSample F T hTF t = x.val} =
      {t : Iic T | (t : ι) ≤ x.val} ∩
        ⋂ y ∈ F, ⋂ (_ : y < x.val), {t : Iic T | y < (t : ι)} := by
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h
      refine ⟨h ▸ le_rightSample F T hTF t, fun y hyF hyx => ?_⟩
      by_contra! hty
      exact absurd (h ▸ rightSample_min_le F T hTF t hyF hty) (not_le_of_gt hyx)
    · rintro ⟨htx, hlt⟩
      refine le_antisymm (rightSample_min_le F T hTF t x.property htx) ?_
      by_contra! hlt_x
      exact absurd (hlt (rightSample F T hTF t) (rightSample_mem F T hTF t) hlt_x)
        (not_lt_of_ge (le_rightSample F T hTF t))
  rw [hpre]
  exact (measurableSet_Iic.preimage measurable_subtypeVal).inter
    (MeasurableSet.biInter F.countable_toSet fun y _ =>
      MeasurableSet.iInter fun _ => measurableSet_Ioi.preimage measurable_subtypeVal)

private theorem tendsto_rightSample {ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] {D : Set ι} (hDd : Dense D) {T : ι} (F : ℕ → Finset ι)
    (hTF : ∀ n, T ∈ F n) (hFT : ∀ n, ∀ x ∈ F n, x ≤ T)
    (hF_mono : ∀ ⦃m n : ℕ⦄, m ≤ n → F m ⊆ F n)
    (hS_mem : ∀ x ∈ insert T ((D ∪ {x : ι | ∃ y, x ⋖ y}) ∩ Iic T), ∃ N, x ∈ F N) (t : Iic T) :
    Tendsto (fun n => rightSample (F n) T (hTF n) t) atTop (𝓝[≥] (t : ι)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall fun n => le_rightSample (F n) T (hTF n) t⟩
  rcases eq_or_lt_of_le t.property with htT | htT_lt
  · have hconst (n : ℕ) : rightSample (F n) T (hTF n) t = t :=
      le_antisymm ((hFT n _ (rightSample_mem (F n) T (hTF n) t)).trans_eq htT.symm)
        (le_rightSample (F n) T (hTF n) t)
    simpa only [hconst] using tendsto_const_nhds
  · rw [tendsto_iff_forall_eventually_mem]
    intro V hV
    obtain ⟨v, ⟨htv, hvT⟩, hvV⟩ :=
      (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset htT_lt).mp (mem_nhdsWithin_of_mem_nhds hV)
    by_cases hcov : (t : ι) ⋖ v
    · obtain ⟨N, hNT⟩ := hS_mem t (Or.inr ⟨Or.inr ⟨v, hcov⟩, t.property⟩)
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hvV ⟨le_rightSample (F n) T (hTF n) t,
        (rightSample_min_le (F n) T (hTF n) t (hF_mono hn hNT) le_rfl).trans_lt htv⟩
    · obtain ⟨d, hdD, htd, hdv⟩ := hDd.exists_mem_open isOpen_Ioo
        ((not_covBy_iff_exists_mem_Ioo htv).mp hcov)
      obtain ⟨N, hNd⟩ := hS_mem d (Or.inr ⟨Or.inl hdD, hdv.le.trans hvT⟩)
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hvV ⟨le_rightSample (F n) T (hTF n) t,
        (rightSample_min_le (F n) T (hTF n) t (hF_mono hn hNd) htd.le).trans_lt hdv⟩

end RightSample

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
  -- Stage 1: build an increasing finite exhaustion `F n ⊆ Iic T` of a countable dense set plus
  -- right-isolated points below `T`.
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
  -- Stage 2: prove joint strong measurability of each sampled approximation on `Iic T × Ω`.
  let : MeasurableSpace Ω := ℱ T
  have hm (n : ℕ) : StronglyMeasurable
      (fun p : Iic T × Ω => u (rightSample (F n) T (hTF n) p.1) p.2) := by
    let : MeasurableSpace (F n) := ⊤
    have hs : StronglyMeasurable (Function.uncurry fun x : F n => u x.val) :=
      stronglyMeasurable_uncurry_of_countable fun x =>
        (hu x.val).mono (ℱ.mono (hFT n x.val x.property))
    exact hs.comp_measurable
      (((measurable_rightSample (F n) T (hTF n)).comp measurable_fst).prodMk measurable_snd)
  -- Stage 3: pass to the pointwise limit using right continuity of every path.
  refine stronglyMeasurable_of_tendsto atTop hm (tendsto_pi_nhds.mpr fun ⟨t, ω⟩ => ?_)
  exact (continuousWithinAt_Ioi_iff_Ici.mp (hc ω t)).tendsto.comp
    (tendsto_rightSample hDd F hTF hFT (fun _ _ hmn => hF_mono hmn) hS_mem t)

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

/-- Progressive processes that agree time-a.e. on almost every path agree product-a.e.
for s-finite time and sample measures. Neither completeness nor usual conditions on the
filtration are needed. -/
theorem MeasureTheory.IsProgressive.ae_eq_prod_of_ae_eq
    {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E] [MeasurableEq E]
    {ℱ : Filtration ℝ≥0 m} {H K : ℝ≥0 → Ω → E}
    (hH : IsProgressive ℱ H) (hK : IsProgressive ℱ K)
    {μ : Measure ℝ≥0} {P : Measure Ω} [SFinite μ] [SFinite P]
    (heq : ∀ᵐ ω ∂P, (fun t ↦ H t ω) =ᵐ[μ] (fun t ↦ K t ω)) :
    Function.uncurry H =ᵐ[μ.prod P] Function.uncurry K := by
  have hm := measurableSet_eq_fun hH.measurable hK.measurable
  exact (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr heq)
