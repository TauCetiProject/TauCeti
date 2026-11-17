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
* `MeasureTheory.Measure.infinitePi_subtype_map_dite_const` — pushing `Measure.infinitePi` over a
  subtype forward by padding deterministic (Dirac) coordinates recovers the full infinite product.
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
      (Set.disjoint_singleton_left.mpr fun h : none ∈ Set.range (some : ι → Option ι) =>
        Option.some_ne_none _ h.choose_spec)
      (TauCeti.Probability.measurable_blockSigma_of_mem rfl) hsome
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
      (Measurable.of_eval fun i => measurable_pi_apply (some i)).aemeasurable,
    Measure.infinitePi_map_eval, Measure.map_infinitePi_infinitePi_of_inj (Option.some_injective ι)]

end Measure

end MeasureTheory

end TauCeti

namespace MeasureTheory.Measure

/-- **Padding an infinite product measure with deterministic coordinates.** If every coordinate
outside a decidable predicate `p` has Dirac law `Measure.dirac (a₀ i)`, then pushing the infinite
product over `{i // p i}` forward by padding missing coordinates with `a₀ i` recovers
`Measure.infinitePi μ`. -/
theorem infinitePi_subtype_map_dite_const {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {p : ι → Prop} [DecidablePred p]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {a₀ : ∀ i, α i} (hdirac : ∀ i, ¬ p i → μ i = Measure.dirac (a₀ i)) :
    (Measure.infinitePi fun i : {i : ι // p i} => μ i.1).map
      (fun z i => if h : p i then z ⟨i, h⟩ else a₀ i) = Measure.infinitePi μ := by
  let pad : (∀ i : {i : ι // p i}, α i.1) → ∀ i, α i :=
    fun z i => if h : p i then z ⟨i, h⟩ else a₀ i
  have hpad : Measurable pad := Measurable.of_eval fun i => by
    dsimp [pad]
    split_ifs with h
    · exact measurable_pi_apply (⟨i, h⟩ : {i : ι // p i})
    · exact measurable_const
  -- Verify equality on finite measurable cylinder sets `s.pi t`.
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply hpad (.pi s.countable_toSet fun i _ => ht i)]
  by_cases hmem : ∀ i ∈ s, ¬ p i → a₀ i ∈ t i
  · -- Every padded coordinate in `s` lies in `t i`, so the preimage is the restricted cylinder.
    have hpre : pad ⁻¹' (s : Set ι).pi t =
        (s.subtype p : Set {i : ι // p i}).pi (fun i => t i.1) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, pad]
      constructor
      · intro hz i hi
        simpa [i.2] using hz i.1 (Finset.mem_subtype.mp hi)
      · intro hz i hi
        split_ifs with h
        · exact hz ⟨i, h⟩ (Finset.mem_subtype.mpr hi)
        · exact hmem i hi h
    rw [hpre, Measure.infinitePi_pi _ (fun i _ => ht i.1),
      Finset.prod_subtype_eq_prod_filter (f := fun i => μ i (t i))]
    symm
    rw [← Finset.prod_filter_mul_prod_filter_not s p]
    have hone : ∏ i ∈ s.filter (fun i => ¬ p i), μ i (t i) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [hdirac i hi.2, Measure.dirac_apply' _ (ht i),
        Set.indicator_of_mem (hmem i hi.1 hi.2), Pi.one_apply]
    rw [hone, mul_one]
  · -- Some padded coordinate in `s` misses `t i₀`, so both the preimage and the product vanish.
    push Not at hmem
    obtain ⟨i₀, hi₀s, hi₀p, hi₀notmem⟩ := hmem
    have hpre : pad ⁻¹' (s : Set ι).pi t = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_forall]
      exact ⟨i₀, hi₀s, by simpa [pad, hi₀p] using hi₀notmem⟩
    rw [hpre, measure_empty]
    symm
    refine Finset.prod_eq_zero hi₀s ?_
    rw [hdirac i₀ hi₀p, Measure.dirac_apply' _ (ht i₀), Set.indicator_of_notMem hi₀notmem]

end MeasureTheory.Measure
