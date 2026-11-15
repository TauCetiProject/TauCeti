/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import TauCeti.MeasureTheory.Group.Arithmetic
import TauCeti.Probability.Independence.Sup
import TauCeti.Probability.Process.Filtration.RightCont

/-!
# Increments independent of the past

A process `X` adapted to a filtration `ℱ` has *increments independent of the past* if every
increment `X t - X s`, `s ≤ t`, is independent of `ℱ s`. This is how Brownian motion relative to a
filtration is defined, and it is the form in which a change of measure delivers independence. This
file derives the consequences that do not depend on the law of the increments.

## Main declarations

* `MeasureTheory.Adapted.indep_comap_sub_of_indep_comap_sub`: increments independent of the past
  on `[s, u]` and on `[u, t]` give an increment independent of the past on `[s, t]`.
* `MeasureTheory.Adapted.hasIndepIncrements`: increments independent of the past are independent
  increments in the sense of `ProbabilityTheory.HasIndepIncrements`.
* `MeasureTheory.Adapted.indep_comap_sub_Ici` and
  `MeasureTheory.Adapted.indep_comap_shift_sub`: increments independent of the past make the whole
  future increment process `(X t - X s)_{t ≥ s}`, and on a canonically ordered additive index type
  the shifted process `t ↦ X (s + t) - X s`, independent of `ℱ s`.
* `MeasureTheory.Adapted.indep_comap_sub_Ioi_rightCont`,
  `MeasureTheory.Adapted.indep_comap_sub_Ici_rightCont`, and
  `MeasureTheory.Adapted.indep_comap_shift_sub_rightCont`: almost-sure right continuity at a single
  time `s` passes future-increment independence from `ℱ` to the right-continuous slice
  `ℱ.rightCont s`.
-/

public section

open MeasureTheory

namespace MeasureTheory.Adapted

open ProbabilityTheory

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Preorder ι]
  {ℱ : Filtration ι mΩ} [MeasurableSpace E] {X : ι → Ω → E}

/-- If the increment of an adapted process over `[s, u]` is independent of `ℱ s` and its
increment over `[u, t]` is independent of `ℱ u`, then its increment over `[s, t]` is independent
of `ℱ s`. -/
theorem indep_comap_sub_of_indep_comap_sub [AddGroup E] [MeasurableSub₂ E]
    [IsZeroOrProbabilityMeasure μ] (hX : Adapted ℱ X) {s u t : ι} (hsu : s ≤ u)
    (h₁ : Indep (.comap (X u - X s) inferInstance) (ℱ s) μ)
    (h₂ : Indep (.comap (X t - X u) inferInstance) (ℱ u) μ) :
    Indep (.comap (X t - X s) inferInstance) (ℱ s) μ := by
  have : MeasurableAdd₂ E := TauCeti.measurableAdd₂_of_measurableSub₂
  have hm₁ : MeasurableSpace.comap (X u - X s) inferInstance ≤ ℱ u :=
    ((hX u).sub (hX.measurable_le hsu)).comap_le
  have hsup := h₁.sup_left (indep_of_indep_of_le_right h₂ (sup_le hm₁ (ℱ.mono hsu)))
    (hm₁.trans (ℱ.le u)) (hX.measurable.sub hX.measurable).comap_le (ℱ.le s)
  refine indep_of_indep_of_le_left hsup (Measurable.comap_le ?_)
  rw [← sub_add_sub_cancel (X t) (X u) (X s)]
  exact ((comap_measurable _).mono le_sup_right le_rfl).add
    ((comap_measurable _).mono le_sup_left le_rfl)

/-- A process adapted to `ℱ` whose increments `X t - X s`, `s ≤ t`, are independent of `ℱ s` has
independent increments. -/
theorem hasIndepIncrements [Sub E] [MeasurableSub₂ E] [IsProbabilityMeasure μ] (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ) :
    HasIndepIncrements X μ := by
  classical
  intro n t ht
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S B hB
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S haS ih =>
    -- The increments with index below `a` are known at the start of the `a`-th increment.
    have hpast : MeasurableSet[ℱ (t a.castSucc)]
        (⋂ i ∈ S, (fun ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) ⁻¹' B i) :=
      Finset.measurableSet_biInter S fun i hi ↦
        (((hX _).sub (hX.measurable_le (ht i.castSucc_le_succ))).mono
          (ℱ.mono (ht (Fin.succ_le_castSucc_iff.2 (haS i hi)))) le_rfl)
          (hB i (Finset.mem_insert_of_mem hi))
    rw [Finset.set_biInter_insert, Finset.prod_insert fun h ↦ lt_irrefl a (haS a h),
      ← ih fun i hi ↦ hB i (Finset.mem_insert_of_mem hi)]
    exact (Indep_iff _ _ _).1 (hindep (ht a.castSucc_le_succ)) _ _
      ⟨B a, hB a (Finset.mem_insert_self a S), rfl⟩ hpast

end MeasureTheory.Adapted

namespace MeasureTheory.Adapted

open ProbabilityTheory

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  {ℱ : Filtration ι mΩ} [MeasurableSpace E] [AddGroup E] [MeasurableSub₂ E]
  [IsZeroOrProbabilityMeasure μ] {X : ι → Ω → E}

/-- If the increments of an adapted process are independent of the past, then for every finite
set `J` of times after `s`, the increments `X t - X s`, `t ∈ J`, jointly generate a sigma-algebra
independent of `ℱ s`. -/
theorem indep_biSup_comap_sub (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ)
    (J : Finset ι) {s : ι} (hJ : ∀ t ∈ J, s ≤ t) :
    Indep (⨆ t ∈ J, .comap (X t - X s) inferInstance) (ℱ s) μ := by
  classical
  have : MeasurableAdd₂ E := TauCeti.measurableAdd₂_of_measurableSub₂
  induction J using Finset.induction_on_min generalizing s with
  | empty => simpa using indep_bot_left (ℱ s)
  | insert a S hlt ih =>
    have hsa : s ≤ a := hJ a (Finset.mem_insert_self a S)
    -- Increments after `a` are measured from `a`; they are independent of `ℱ a`.
    have hm₁ : MeasurableSpace.comap (X a - X s) inferInstance ≤ ℱ a :=
      ((hX a).sub (hX.measurable_le hsa)).comap_le
    have hm₂ : (⨆ t ∈ S, MeasurableSpace.comap (X t - X a) inferInstance) ≤ mΩ :=
      iSup₂_le fun _ _ ↦ (hX.measurable.sub hX.measurable).comap_le
    have h₂ := indep_of_indep_of_le_right (ih (fun t ht ↦ (hlt t ht).le))
      (sup_le hm₁ (ℱ.mono hsa))
    have hsup := (hindep hsa).sup_left h₂ (hm₁.trans (ℱ.le a)) hm₂ (ℱ.le s)
    refine indep_of_indep_of_le_left hsup ?_
    rw [Finset.iSup_insert]
    refine sup_le le_sup_left (iSup₂_le fun t ht ↦ Measurable.comap_le ?_)
    rw [← sub_add_sub_cancel (X t) (X a) (X s)]
    have hle := le_iSup₂
      (f := fun t (_ : t ∈ S) ↦ MeasurableSpace.comap (X t - X a) inferInstance) t ht
    exact ((comap_measurable _).mono (hle.trans le_sup_right) le_rfl).add
      ((comap_measurable _).mono le_sup_left le_rfl)

/-- If the increments of an adapted process are independent of the past, then the whole future
increment process `(X t - X s)_{t ≥ s}` is independent of `ℱ s`. -/
theorem indep_comap_sub_Ici (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ) (s : ι) :
    Indep (.comap (fun ω (t : Set.Ici s) ↦ X t ω - X s ω) inferInstance) (ℱ s) μ := by
  classical
  rw [MeasurableSpace.comap_process_pi, iSup_eq_iSup_finset]
  refine indep_iSup_of_monotone (fun J ↦ ?_) (fun J ↦ ?_) (ℱ.le s)
    (fun _ _ h ↦ iSup_le_iSup_of_subset h)
  · refine indep_of_indep_of_le_left
      (hX.indep_biSup_comap_sub hindep (J.map (Function.Embedding.subtype _))
        (s := s) (by simp +contextual)) ?_
    exact iSup₂_le fun t ht ↦
      le_iSup₂_of_le (t : ι) (Finset.mem_map_of_mem _ ht) le_rfl
  · exact iSup₂_le fun _ _ ↦ (hX.measurable.sub hX.measurable).comap_le

/-- On a canonically ordered additive index type, if the increments of an adapted process are
independent of the past, then the shifted increment process `t ↦ X (s + t) - X s` is
independent of `ℱ s`. -/
theorem indep_comap_shift_sub [Add ι] [CanonicallyOrderedAdd ι] (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ) (s : ι) :
    Indep (.comap (fun ω t ↦ X (s + t) ω - X s ω) inferInstance) (ℱ s) μ := by
  refine indep_of_indep_of_le_left (hX.indep_comap_sub_Ici hindep s) ?_
  have hcomp : (fun ω t ↦ X (s + t) ω - X s ω) =
      (fun (f : Set.Ici s → E) t ↦ f ⟨s + t, le_self_add⟩) ∘
        fun ω (u : Set.Ici s) ↦ X u ω - X s ω := rfl
  rw [hcomp, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.of_eval fun t ↦ measurable_pi_apply _).comap_le

section RightCont

open Filter Set
open scoped Topology _root_.BoundedContinuousFunction ENNReal

private lemma indep_rightCont_pi_sub_of_lt (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ)
    {s u : ι} (hsu : s < u) (I : Finset (Ioi s)) (hu : ∀ t ∈ I, u ≤ (t : ι)) :
    Indep (.comap (fun ω (t : I) ↦ X (t : ι) ω - X u ω) inferInstance) (ℱ.rightCont s) μ := by
  classical
  have hJ := hX.indep_biSup_comap_sub hindep (I.image Subtype.val) (s := u)
    (by simpa using fun t ht ↦ hu t ht)
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hJ ?_)
    (ℱ.rightCont_le_of_lt hsu)
  rw [MeasurableSpace.comap_process_pi]
  exact iSup_le fun t ↦
    le_iSup₂_of_le (t : ι) (Finset.mem_image_of_mem Subtype.val t.2) le_rfl

variable [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [FirstCountableTopology ι]
  [TopologicalSpace E] [BorelSpace E] [HasOuterApproxClosed E] [ContinuousSub E]

/-- If an adapted process on a densely ordered first-countable time index into a Borel additive
group with outer closed approximation and continuous subtraction has increments independent of the
past and is almost surely right-continuous at `s`, then the strict future increment process
`(X t - X s)_{t > s}` is independent of `ℱ.rightCont s`. -/
theorem indep_comap_sub_Ioi_rightCont (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ) {s : ι}
    (hcont : ∀ᵐ ω ∂μ, ContinuousWithinAt (X · ω) (Ioi s) s) :
    Indep (.comap (fun ω (t : Ioi s) ↦ X t ω - X s ω) inferInstance) (ℱ.rightCont s) μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [Indep_iff]
  refine (indep_comap_process_of_prod_bcf (ℱ.rightCont.le s)
    (fun _ ↦ (hX.measurable.sub hX.measurable).aemeasurable) fun A hA I f ↦ ?_).symm
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp [integral_const, smul_eq_mul, mul_comm]
  have hg : Measurable fun z : I → E ↦ ∏ t : I, f t (z t) :=
    Finset.measurable_prod _ fun t _ ↦ (f t).continuous.measurable.comp (measurable_pi_apply t)
  obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictAnti_tendsto' (I.min' hne).2
  have hu' : Tendsto u atTop (𝓝[>] s) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n ↦ (hu n).1⟩
  have hUn (n : ℕ) : Measurable fun ω (t : I) ↦ X (t : ι) ω - X (u n) ω :=
    measurable_pi_iff.2 fun _ ↦ hX.measurable.sub hX.measurable
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (fun ω ↦ ∏ t : I, f t (X (t : ι) ω - X (u n) ω)) μ :=
    (hg.comp (hUn n)).aestronglyMeasurable
  have hbound (n : ℕ) :
      ∀ᵐ ω ∂μ, ‖∏ t : I, f t (X (t : ι) ω - X (u n) ω)‖ ≤ ∏ t : I, ‖f t‖ :=
    Eventually.of_forall fun ω ↦ by
      rw [norm_prod]
      gcongr with t
      exact (f t).norm_coe_le_norm _
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∏ t : I, f t (X (t : ι) ω - X (u n) ω))
      atTop (𝓝 (∏ t : I, f t (X (t : ι) ω - X s ω))) :=
    hcont.mono fun ω hω ↦ tendsto_finsetProd _ fun t _ ↦
      (f t).continuous.continuousAt.tendsto.comp (tendsto_const_nhds.sub (hω.tendsto.comp hu'))
  have hall := tendsto_integral_of_dominated_convergence (fun _ ↦ ∏ t : I, ‖f t‖)
    hmeas (integrable_const _) hbound hconv
  have hset := tendsto_integral_of_dominated_convergence (μ := μ.restrict A)
    (fun _ ↦ ∏ t : I, ‖f t‖) (fun n ↦ (hmeas n).restrict) (integrable_const _)
    (fun n ↦ ae_restrict_of_ae (hbound n)) (ae_restrict_of_ae hconv)
  have heq (n : ℕ) : ∫ ω in A, (∏ t : I, f t (X (t : ι) ω - X (u n) ω)) ∂μ =
      μ.real A * ∫ ω, (∏ t : I, f t (X (t : ι) ω - X (u n) ω)) ∂μ :=
    (indep_rightCont_pi_sub_of_lt hX hindep (hu n).1 I fun t ht ↦
      (hu n).2.le.trans (I.min'_le t ht)).symm.setIntegral_eq_mul
      (ℱ.rightCont.le s) (hUn n).aemeasurable hA hg.aestronglyMeasurable
  exact tendsto_nhds_unique hset ((tendsto_const_nhds.mul hall).congr fun n ↦ (heq n).symm)

/-- If an adapted process on a densely ordered first-countable time index into a Borel additive
group with outer closed approximation and continuous subtraction has increments independent of the
past and is almost surely right-continuous at `s`, then the future increment process
`(X t - X s)_{t ≥ s}` is independent of `ℱ.rightCont s`. -/
theorem indep_comap_sub_Ici_rightCont (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ) {s : ι}
    (hcont : ∀ᵐ ω ∂μ, ContinuousWithinAt (X · ω) (Ioi s) s) :
    Indep (.comap (fun ω (t : Ici s) ↦ X t ω - X s ω) inferInstance) (ℱ.rightCont s) μ := by
  classical
  refine indep_of_indep_of_le_left (hX.indep_comap_sub_Ioi_rightCont hindep hcont) ?_
  have hcomp : (fun ω (t : Ici s) ↦ X t ω - X s ω) =
      (fun (f : Ioi s → E) (t : Ici s) ↦
        if ht : s < (t : ι) then f ⟨t, ht⟩ else 0) ∘
        fun ω (u : Ioi s) ↦ X u ω - X s ω := by
    ext ω ⟨t, ht⟩
    dsimp only [Function.comp_apply]
    split_ifs with hlt
    · rfl
    · simp [le_antisymm (not_lt.1 hlt) ht]
  rw [hcomp, ← MeasurableSpace.comap_comp]
  refine MeasurableSpace.comap_mono (Measurable.of_eval fun t ↦ ?_).comap_le
  by_cases ht : s < (t : ι)
  · simpa [ht] using measurable_pi_apply (⟨t, ht⟩ : Ioi s)
  · simp [ht]

/-- On a densely ordered first-countable canonically ordered additive index type, if an adapted
process into a Borel additive group with outer closed approximation and continuous subtraction has
increments independent of the past and is almost surely right-continuous at `s`, then the shifted
increment process `t ↦ X (s + t) - X s` is independent of `ℱ.rightCont s`. -/
theorem indep_comap_shift_sub_rightCont [Add ι] [CanonicallyOrderedAdd ι] (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ) {s : ι}
    (hcont : ∀ᵐ ω ∂μ, ContinuousWithinAt (X · ω) (Ioi s) s) :
    Indep (.comap (fun ω t ↦ X (s + t) ω - X s ω) inferInstance) (ℱ.rightCont s) μ := by
  refine indep_of_indep_of_le_left (hX.indep_comap_sub_Ici_rightCont hindep hcont) ?_
  have hcomp : (fun ω t ↦ X (s + t) ω - X s ω) =
      (fun (f : Ici s → E) t ↦ f ⟨s + t, le_self_add⟩) ∘
        fun ω (u : Ici s) ↦ X u ω - X s ω := rfl
  rw [hcomp, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.of_eval fun t ↦ measurable_pi_apply _).comap_le

end RightCont

end MeasureTheory.Adapted
