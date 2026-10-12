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
# Splitting off one coordinate of an infinite product measure

For a family of probability measures indexed by `Option ι`, the product measure
`Measure.infinitePi μ` is the law of an assignment `x` whose coordinates are independent with laws
`μ i`. Reading `x` as its value at `none` together with its restriction to the indices `some i`
separates it into two independent pieces, so

```text
(Measure.infinitePi μ).map (fun x => (x none, fun i => x (some i)))
  = μ none ⊗ Measure.infinitePi (fun i => μ (some i)).
```

This is the infinite-product analogue of Mathlib's `MeasureTheory.Measure.pi_map_piOptionEquivProd`,
which is stated for `Measure.pi` over a finite index type. It isolates one distinguished
coordinate — a global or initial variable — from the independent remaining coordinates, each
with its respective law.

## Main results

* `TauCeti.MeasureTheory.Measure.infinitePi_map_none_some` — the displayed identity.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

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
      (Set.disjoint_singleton_left.mpr fun h => Option.some_ne_none _ h.choose_spec)
      (TauCeti.Probability.measurable_blockSigma_of_mem rfl) hsome
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
      (Measurable.of_eval fun i => measurable_pi_apply (some i)).aemeasurable,
    Measure.infinitePi_map_eval, Measure.map_infinitePi_infinitePi_of_inj (Option.some_injective ι)]

end Measure

end MeasureTheory

end TauCeti
