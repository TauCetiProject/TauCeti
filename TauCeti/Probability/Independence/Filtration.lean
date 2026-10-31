/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Process.Adapted
import TauCeti.Probability.Independence.Sup

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
theorem indep_comap_sub_of_indep_comap_sub [AddGroup E] [MeasurableAdd₂ E] [MeasurableSub₂ E]
    [IsZeroOrProbabilityMeasure μ] (hX : Adapted ℱ X) {s u t : ι} (hsu : s ≤ u)
    (h₁ : Indep (.comap (X u - X s) inferInstance) (ℱ s) μ)
    (h₂ : Indep (.comap (X t - X u) inferInstance) (ℱ u) μ) :
    Indep (.comap (X t - X s) inferInstance) (ℱ s) μ := by
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
