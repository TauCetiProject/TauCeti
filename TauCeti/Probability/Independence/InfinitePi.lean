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

The restrictions of a product sample to disjoint index sets are independent, and so are its
selections along maps with disjoint ranges.  The resulting joint-law identities are useful when a
conditionally independent process is split into observed and unobserved coordinates.

When the factors have no atoms, two distinct coordinates of a product sample are moreover almost
surely different, so a sample can be used to order the indices it is attached to.
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

/-- Under a product law, selections along maps with disjoint ranges are independent, and an
injective selection has the product of the selected factors as its law. The first selection need
not be injective. -/
theorem infinitePi_map_pair_comp {ι κ₁ κ₂ β : Type*} [MeasurableSpace β] (P : ι → Measure β)
    [∀ i, IsProbabilityMeasure (P i)] {e : κ₁ → ι} {g : κ₂ → ι} (hg : Function.Injective g)
    (heg : Disjoint (Set.range e) (Set.range g)) :
    (Measure.infinitePi P).map (fun x => (fun a => x (e a), fun b => x (g b))) =
      ((Measure.infinitePi P).map fun x a => x (e a)).prod
        (Measure.infinitePi fun b => P (g b)) := by
  have hS (a : κ₁) : e a ∈ (Set.range g)ᶜ := Set.disjoint_left.mp heg ⟨a, rfl⟩
  have hφ : Measurable fun (y : ↥(Set.range g)ᶜ → β) a => y ⟨e a, hS a⟩ :=
    Measurable.of_eval fun a => measurable_pi_apply _
  have hψ : Measurable fun (y : ↥(Set.range g) → β) b => y ⟨g b, b, rfl⟩ :=
    Measurable.of_eval fun b => measurable_pi_apply _
  have hind : IndepFun (fun x : ι → β => fun a => x (e a)) (fun x b => x (g b))
      (Measure.infinitePi P) :=
    (indepFun_domRestrict_infinitePi P disjoint_compl_left).comp hφ hψ
  rw [hind.map_prod_eq_prod_map_map
    (Measurable.of_eval fun a => measurable_pi_apply _).aemeasurable
    (Measurable.of_eval fun b => measurable_pi_apply _).aemeasurable,
    Measure.map_infinitePi_infinitePi_of_inj hg]

/-- **Two coordinates of a product of atomless laws are almost surely distinct.** Under a product
of probability laws without atoms on a space with a measurable diagonal, two distinct coordinates
of a sample almost surely take different values. -/
theorem ae_apply_ne_apply_infinitePi {ι β : Type*} [MeasurableSpace β] [MeasurableEq β]
    (P : ι → Measure β) [∀ i, IsProbabilityMeasure (P i)] [∀ i, NullSingletonClass (P i)]
    {i j : ι} (hij : i ≠ j) :
    ∀ᵐ x ∂Measure.infinitePi P, x i ≠ x j := by
  have hmeas : Measurable fun x : ι → β => (x i, x j) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hdiag : MeasurableSet {p : β × β | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hset : {x : ι → β | ¬x i ≠ x j} = (fun x => (x i, x j)) ⁻¹' {p | p.1 = p.2} := by
    ext x
    simp
  rw [ae_iff, hset, ← Measure.map_apply hmeas hdiag, Measure.infinitePi_map_eval_prod hij,
    Measure.prod_apply hdiag]
  simp

end TauCeti.Probability
