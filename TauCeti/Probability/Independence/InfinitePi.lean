/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Probability.Independence.DisjointBlocks

/-!
# Independence of disjoint coordinate restrictions of an infinite product

The restrictions of a product sample to disjoint index sets are independent.  The resulting
joint-law identity is useful when a conditionally independent process is split into observed and
unobserved coordinates.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- Restrictions to disjoint coordinate sets are independent under a product probability law. -/
theorem indepFun_domRestrict_infinitePi (P : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] {S T : Set ι}
    (hST : Disjoint S T) :
    IndepFun (fun x : ∀ i, α i => S.domRestrict x)
      (fun x : ∀ i, α i => T.domRestrict x) (Measure.infinitePi P) := by
  classical
  let ρ : Measure (∀ i, α i) := Measure.infinitePi P
  have hi : iIndepFun (fun i : ι => fun x : ∀ j, α j => x i) ρ :=
    iIndepFun_infinitePi (X := fun i : ι => (id : α i → α i)) fun _ => measurable_id
  apply TauCeti.Probability.indepFun_of_measurable_blockSigma
    (hZ := hi.precomp (g := (Subtype.val : ↥(S ∪ T) → ι)) Subtype.val_injective)
    (fun _ _ => measurable_pi_apply _) hST
  · rw [TauCeti.Probability.blockSigma_eq_comap_restrict]
    exact Measurable.of_comap_le le_rfl
  · rw [TauCeti.Probability.blockSigma_eq_comap_restrict]
    exact Measurable.of_comap_le le_rfl

/-- Under a product probability law, the restrictions to two disjoint sets of coordinates have
the product of their marginal laws. -/
@[simp]
theorem infinitePi_map_pair_domRestrict (P : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] {S T : Set ι}
    (hST : Disjoint S T) :
    (Measure.infinitePi P).map
        (fun x => (S.domRestrict x, T.domRestrict x)) =
      (Measure.infinitePi fun i : S => P i).prod
        (Measure.infinitePi fun i : T => P i) := by
  have hind := indepFun_domRestrict_infinitePi P hST
  have hprod := hind.map_prod_eq_prod_map_map
    (Set.measurable_restrict S).aemeasurable (Set.measurable_restrict T).aemeasurable
  simpa only [Measure.infinitePi_map_restrict'] using hprod

end TauCeti.Probability
