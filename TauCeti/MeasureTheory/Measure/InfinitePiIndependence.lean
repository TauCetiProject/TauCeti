/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Process.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Independence of disjoint coordinate restrictions of an infinite product

The restrictions of a product sample to disjoint index sets are independent.  The resulting
joint-law identity is useful when a conditionally independent process is split into observed and
unobserved coordinates.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.MeasureTheory

variable {ι α : Type*} [MeasurableSpace α]

/-- Under a product probability law, the restrictions to two disjoint sets of coordinates have
the product of their marginal laws. -/
@[simp]
theorem infinitePi_map_pair_domRestrict (P : ι → ProbabilityMeasure α) {S T : Set ι}
    (hST : Disjoint S T) :
    (Measure.infinitePi fun i : ι => (P i : Measure α)).map
        (fun x => (S.domRestrict x, T.domRestrict x)) =
      (Measure.infinitePi fun i : S => (P i : Measure α)).prod
        (Measure.infinitePi fun i : T => (P i : Measure α)) := by
  classical
  let ρ : Measure (ι → α) := Measure.infinitePi fun i : ι => (P i : Measure α)
  have hi : iIndepFun (fun i : ι => fun x : ι → α => x i) ρ :=
    iIndepFun_infinitePi (X := fun _ : ι => (id : α → α)) fun _ => measurable_id
  have hind : IndepFun (fun x : ι → α => S.domRestrict x)
      (fun x : ι → α => T.domRestrict x) ρ := by
    apply IndepFun.process_indepFun_process
      (X := fun i : S => fun x : ι → α => x i)
      (Y := fun i : T => fun x : ι → α => x i)
      (fun _ => measurable_pi_apply _) (fun _ => measurable_pi_apply _)
    intro I J
    let A : Finset ι := I.image Subtype.val
    let B : Finset ι := J.image Subtype.val
    have hAB : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro i hiA hiB
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hiA
      obtain ⟨t, -, heq⟩ := Finset.mem_image.mp hiB
      exact (Set.disjoint_left.mp hST s.property) (heq ▸ t.property)
    have h := hi.indepFun_finset A B hAB (fun _ => measurable_pi_apply _)
    -- Reindex the finite products from images to the original subtype index sets.
    let f : (A → α) → I → α := fun y i =>
      y ⟨i.1.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
    let g : (B → α) → J → α := fun y i =>
      y ⟨i.1.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
    have hf : Measurable f := Measurable.of_eval fun _ => measurable_pi_apply _
    have hg : Measurable g := Measurable.of_eval fun _ => measurable_pi_apply _
    exact h.comp hf hg
  have hprod := hind.map_prod_eq_prod_map_map
    (Set.measurable_restrict S).aemeasurable (Set.measurable_restrict T).aemeasurable
  simpa only [ρ, Measure.infinitePi_map_restrict'] using hprod

end TauCeti.MeasureTheory
