/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProductMeasure
-- Non-public: independence of disjoint coordinate blocks is used only inside the proof.
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Probability.Independence.DisjointBlocks

/-!
# Splitting coordinates of an infinite product measure

For a family of probability measures `μ : ∀ i, Measure (X i)`, the infinite product measure
`Measure.infinitePi μ` is the law of an assignment `x` whose coordinates are independent with laws
`μ i`.

Splitting the index type along a decidable predicate `p : ι → Prop` via
`MeasurableEquiv.piEquivPiSubtypeProd` carries `Measure.infinitePi μ` to the binary product of the
infinite product measures on `{i // p i}` and `{i // ¬ p i}`
(`TauCeti.measurePreserving_infinitePi_piEquivPiSubtypeProd`). This is the infinite-product
analogue of Mathlib's `MeasureTheory.measurePreserving_piEquivPiSubtypeProd`.

For a family indexed by `Option ι`, reading `x` as `(x none, fun i => x (some i))` similarly
separates the coordinate at `none` from the remaining coordinates
(`TauCeti.MeasureTheory.Measure.infinitePi_map_none_some`), the infinite-product analogue of
Mathlib's `MeasureTheory.Measure.pi_map_piOptionEquivProd`.

## Main results

* `TauCeti.measurePreserving_infinitePi_piEquivPiSubtypeProd` — splitting an infinite product
  measure along a decidable predicate `p : ι → Prop`.
* `TauCeti.MeasureTheory.Measure.infinitePi_map_none_some` — splitting off the coordinate `none`
  of an `Option ι`-indexed infinite product measure.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

/-- **Splitting an infinite product measure along a predicate.** For a family of probability
measures `μ` and a decidable predicate `p` on the index type, `MeasurableEquiv.piEquivPiSubtypeProd`
is measure-preserving from `Measure.infinitePi μ` to the product of the infinite product measures
on `{i // p i}` and `{i // ¬ p i}`. -/
theorem measurePreserving_infinitePi_piEquivPiSubtypeProd {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd X p) (Measure.infinitePi μ)
      ((Measure.infinitePi fun i : {i // p i} => μ i).prod
        (Measure.infinitePi fun i : {i // ¬ p i} => μ i)) := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd X p
  refine ⟨e.measurable, ?_⟩
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  refine (Measure.eq_infinitePi μ fun s t ht => ?_).symm
  have hpre : e.symm ⁻¹' (s : Set ι).pi t =
      ((s.subtype p : Set {i // p i}).pi (fun i => t i)) ×ˢ
        ((s.subtype (fun i => ¬ p i) : Set {i // ¬ p i}).pi (fun i => t i)) := by
    ext ⟨y, z⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_subtype,
      Subtype.forall, e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
    constructor
    · intro h
      exact ⟨fun i hp hi => by simpa [hp] using h i hi,
        fun i hnp hi => by simpa [hnp] using h i hi⟩
    · rintro ⟨hy, hz⟩ i hi
      by_cases hp : p i <;> simp [hp, hy, hz, hi]
  rw [Measure.map_apply e.symm.measurable (MeasurableSet.pi s.countable_toSet fun i _ => ht i),
    hpre, Measure.prod_prod,
    Measure.infinitePi_pi (fun i : {i // p i} => μ i) (fun i _ => ht i.1),
    Measure.infinitePi_pi (fun i : {i // ¬ p i} => μ i) (fun i _ => ht i.1),
    Finset.prod_subtype_eq_prod_filter (f := fun i => μ i (t i)),
    Finset.prod_subtype_eq_prod_filter (f := fun i => μ i (t i)),
    Finset.prod_filter_mul_prod_filter_not]

namespace MeasureTheory

namespace Measure

/-- **Splitting off the coordinate `none` of an infinite product measure.** Under the product of
probability measures indexed by `Option ι`, the coordinate at `none` and the family of coordinates
at `some i` are independent, with laws `μ none` and the product of the `μ (some i)`. -/
@[simp]
theorem infinitePi_map_none_some {ι : Type*} {X : Option ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.infinitePi μ).map (fun x => (x none, fun i => x (some i)))
      = (μ none).prod (Measure.infinitePi fun i => μ (some i)) := by
  -- The two pieces read the disjoint coordinate blocks `{none}` and `range some`.
  have hsome : Measurable[TauCeti.Probability.blockSigma (fun i (x : ∀ i, X i) => x i)
      (Set.range some)] fun x : ∀ i, X i => fun i => x (some i) :=
    @Measurable.of_eval _ _ _ (TauCeti.Probability.blockSigma _ _) _ _ fun i =>
      TauCeti.Probability.measurable_blockSigma_of_mem ⟨i, rfl⟩
  have hind : IndepFun (fun x : ∀ i, X i => x none) (fun x i => x (some i))
      (Measure.infinitePi μ) :=
    TauCeti.Probability.indepFun_of_measurable_blockSigma
      ((iIndepFun_infinitePi (X := fun _ y => y) fun _ => measurable_id).precomp
        Subtype.val_injective)
      (fun i _ => measurable_pi_apply i)
      (Set.disjoint_singleton_left.mpr fun h : none ∈ Set.range (some : ι → Option ι) =>
        Option.some_ne_none _ h.choose_spec)
      (TauCeti.Probability.measurable_blockSigma_of_mem rfl) hsome
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
      (Measurable.of_eval fun i => measurable_pi_apply (some i)).aemeasurable,
    Measure.infinitePi_map_eval, Measure.map_infinitePi_infinitePi_of_inj (Option.some_injective ι)]

end Measure

end MeasureTheory

end TauCeti
