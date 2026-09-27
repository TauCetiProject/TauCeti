/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Process.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Probability.Independence.DisjointBlocks

/-!
# Independence of disjoint coordinate restrictions of an infinite product

The restrictions of a product sample to disjoint index sets are independent.  The resulting
joint-law identity is useful when a conditionally independent process is split into observed and
unobserved coordinates.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.MeasureTheory.Measure

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
    apply TauCeti.Probability.indepFun_of_measurable_blockSigma
      (hZ := hi.precomp (g := (Subtype.val : ↥(S ∪ T) → ι)) Subtype.val_injective)
      (fun _ _ => measurable_pi_apply _) hST
    · rw [TauCeti.Probability.blockSigma_eq_comap_restrict]
      exact Measurable.of_comap_le le_rfl
    · rw [TauCeti.Probability.blockSigma_eq_comap_restrict]
      exact Measurable.of_comap_le le_rfl
  have hprod := hind.map_prod_eq_prod_map_map
    (Set.measurable_restrict S).aemeasurable (Set.measurable_restrict T).aemeasurable
  simpa only [ρ, Measure.infinitePi_map_restrict'] using hprod

end TauCeti.MeasureTheory.Measure
