/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.BoundedContinuousFunction
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Process.Adapted
import TauCeti.MeasureTheory.Group.Arithmetic
import TauCeti.Probability.Independence.Limit
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
* `MeasureTheory.Adapted.indep_comap_sub_Ici`, `MeasureTheory.Adapted.indep_comap_shift`: increments
  independent of the past make the whole future increment process `(X t - X s)_{t ≥ s}` (and the
  shifted increment process `(X (s + u) - X s)_u`) independent of `ℱ s`.
* `MeasureTheory.Adapted.indep_comap_sub_rightCont`,
  `MeasureTheory.Adapted.indep_comap_shift_rightCont`: almost-sure right-hand sequential limits
  upgrade increment and future-shift independence from `ℱ` to `ℱ.rightCont`.
-/

public section

open Filter MeasureTheory
open scoped Topology

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

/-- On a canonically ordered additive time index (such as `ℝ≥0` or `ℕ`), if the increments of an
adapted process are independent of the past, then the shifted future increment process
`(X (s + u) - X s)_u` is independent of `ℱ s`. -/
theorem indep_comap_shift [Add ι] [CanonicallyOrderedAdd ι] (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ) (s : ι) :
    Indep (.comap (fun ω u ↦ X (s + u) ω - X s ω) inferInstance) (ℱ s) μ := by
  refine indep_of_indep_of_le_left (hX.indep_comap_sub_Ici hindep s) ?_
  have hg : Measurable fun (z : Set.Ici s → E) (u : ι) ↦
      z ⟨s + u, Set.mem_Ici.mpr le_self_add⟩ :=
    measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _
  have hcomp : (fun ω u ↦ X (s + u) ω - X s ω) =
      (fun (z : Set.Ici s → E) (u : ι) ↦ z ⟨s + u, Set.mem_Ici.mpr le_self_add⟩) ∘
        fun ω (t : Set.Ici s) ↦ X t ω - X s ω :=
    rfl
  rw [hcomp, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

end MeasureTheory.Adapted

namespace MeasureTheory.Adapted

open ProbabilityTheory

/-- If the increments of an adapted process are independent of `ℱ` and at time `s` there exists a
sequence `u n > s` converging to `s` along which `X (u n)` converges to `X s` almost surely, then
the increment `X t - X s` (`s ≤ t`) is independent of the right-continuous past `ℱ.rightCont s`. -/
theorem indep_comap_sub_rightCont {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    {ℱ : Filtration ι mΩ} [TopologicalSpace E] [AddGroup E] [ContinuousSub E]
    [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E] [MeasurableSub₂ E]
    {X : ι → Ω → E} (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ)
    {s t : ι} (hst : s ≤ t)
    (hlim : ∃ u : ℕ → ι, (∀ n, s < u n) ∧ Tendsto u atTop (𝓝 s) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (u n) ω) atTop (𝓝 (X s ω))) :
    Indep (.comap (X t - X s) inferInstance) (ℱ.rightCont s) μ := by
  rcases hst.eq_or_lt with rfl | hst
  · have hzero : X s - X s = fun _ ↦ (0 : E) := funext fun _ ↦ sub_self _
    rw [hzero, MeasurableSpace.comap_const]
    exact indep_bot_left (ℱ.rightCont s)
  · obtain ⟨u, hsu, hutend, hae⟩ := hlim
    let v : ℕ → ι := fun n ↦ min t (u n)
    have hind (n : ℕ) : Indep (ℱ.rightCont s) (.comap (X t - X (v n)) inferInstance) μ :=
      indep_of_indep_of_le_left (hindep (min_le_left t (u n))).symm
        (ℱ.rightCont_le_of_lt (lt_min hst (hsu n)))
    have hev : ∀ᶠ n in atTop, v n = u n :=
      (hutend.eventually (gt_mem_nhds hst)).mono fun _ hn ↦ min_eq_right hn.le
    refine (indep_comap_of_ae_tendsto (ℱ.rightCont.le s)
      (fun n ↦ (hX.measurable.sub hX.measurable).aemeasurable)
      (hX.measurable.sub hX.measurable).aemeasurable hind ?_).symm
    filter_upwards [hae] with ω hω
    exact tendsto_const_nhds.sub (hω.congr' (hev.mono fun _ hn ↦ by rw [← hn]))

/-- If the increments of an adapted process are independent of `ℱ` and at every time `r` there
exists a sequence `u n > r` converging to `r` along which `X (u n)` converges to `X r` almost
surely, then at every time `s` the entire future increment process `(X (s + v) - X s)_v` is
independent of `ℱ.rightCont s`. -/
theorem indep_comap_shift_rightCont {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [Add ι] [CanonicallyOrderedAdd ι] {ℱ : Filtration ι mΩ}
    [TopologicalSpace E] [AddGroup E] [ContinuousSub E]
    [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E] [MeasurableSub₂ E]
    {X : ι → Ω → E} (hX : Adapted ℱ X)
    (hindep : ∀ ⦃s t : ι⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) μ)
    (hlim : ∀ r : ι, ∃ u : ℕ → ι, (∀ n, r < u n) ∧ Tendsto u atTop (𝓝 r) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (u n) ω) atTop (𝓝 (X r ω)))
    (s : ι) :
    Indep (.comap (fun ω v ↦ X (s + v) ω - X s ω) inferInstance) (ℱ.rightCont s) μ :=
  Adapted.indep_comap_shift (fun i ↦ (hX i).mono (ℱ.le_rightCont i) le_rfl)
    (fun _ _ hrt ↦ hX.indep_comap_sub_rightCont hindep hrt (hlim _)) s

end MeasureTheory.Adapted
