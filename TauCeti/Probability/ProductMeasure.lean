/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProductMeasure
-- Non-public: independence of disjoint coordinate blocks is used only inside the proofs.
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Probability.Independence.DisjointBlocks
import TauCeti.Probability.Independence.InfinitePi

/-!
# Infinite product measures: coordinate splitting and cylinders

For a family of probability measures `μ i` on measurable spaces `X i`, the infinite product measure
`Measure.infinitePi μ` on `∀ i, X i` satisfies:

* **Splitting off a distinguished coordinate**
  (`TauCeti.MeasureTheory.Measure.infinitePi_map_none_some`):
  for an index type `Option ι`, reading `x` as `(x none, fun i => x (some i))` pushes
  `Measure.infinitePi μ` to `(μ none).prod (Measure.infinitePi fun i => μ (some i))`, the
  infinite-product analogue of Mathlib's `MeasureTheory.Measure.pi_map_piOptionEquivProd`.
* **Splitting along a predicate** (`TauCeti.measurePreserving_piEquivPiSubtypeProd_infinitePi`):
  `MeasurableEquiv.piEquivPiSubtypeProd X p` carries `Measure.infinitePi μ` to the binary product
  of the two complementary sub-products, extending
  `MeasureTheory.measurePreserving_piEquivPiSubtypeProd` from finite to arbitrary index types.
* **Unconditional finite-cylinder evaluation** (`TauCeti.infinitePi_pi'`):
  `Measure.infinitePi μ ((s : Set ι).pi t) = ∏ i ∈ s, μ i (t i)` holds for every `s : Finset ι`
  and arbitrary (not necessarily measurable) coordinate sets `t i`, matching
  `MeasureTheory.Measure.pi_pi` and `MeasureTheory.Measure.prod_prod`.

The finite-cylinder formula gives positivity on nonempty open sets and the Haar property of
`Measure.infinitePi` without measurability hypotheses on open sets
(`MeasureTheory.Measure.infinitePi.isOpenPosMeasure`,
`MeasureTheory.Measure.infinitePi.isHaarMeasure`).

## Main results

* `TauCeti.MeasureTheory.Measure.infinitePi_map_none_some`: splitting off `none` in `Option ι`.
* `TauCeti.measurePreserving_piEquivPiSubtypeProd_infinitePi`: splitting along a predicate `p`.
* `TauCeti.infinitePi_pi'`: unconditional finite-cylinder formula for `Measure.infinitePi`.
* `MeasureTheory.Measure.infinitePi_subtype_map_dite_const`: padding `Measure.infinitePi` over a
  subtype by deterministic (Dirac) coordinates recovers the full infinite product.
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

section SplitAndCylinder

open _root_.MeasureTheory.Measure Set
open scoped Topology

universe u v

variable {ι : Type u} {X : ι → Type v} [∀ i, MeasurableSpace (X i)]

/-- Splitting coordinates along a predicate `p` via `MeasurableEquiv.piEquivPiSubtypeProd` carries
an infinite product of probability measures to the product of the two complementary infinite
product measures. -/
theorem measurePreserving_piEquivPiSubtypeProd_infinitePi
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd X p) (infinitePi μ)
      ((infinitePi fun i : {i // p i} ↦ μ i.val).prod
        (infinitePi fun i : {i // ¬ p i} ↦ μ i.val)) :=
  ⟨(MeasurableEquiv.piEquivPiSubtypeProd X p).measurable, by
    have hfun : (MeasurableEquiv.piEquivPiSubtypeProd X p :
        (∀ i, X i) → (∀ i : {i // p i}, X i.val) × (∀ i : {i // ¬ p i}, X i.val)) =
        fun x ↦ ({i | p i}.domRestrict x, {i | ¬ p i}.domRestrict x) := by
      funext x
      exact Prod.ext
        (funext fun i ↦ by simp [MeasurableEquiv.piEquivPiSubtypeProd_apply])
        (funext fun i ↦ by simp [MeasurableEquiv.piEquivPiSubtypeProd_apply])
    rw [hfun]
    exact TauCeti.Probability.infinitePi_map_pair_domRestrict μ (S := {i | p i})
      (T := {i | ¬ p i}) disjoint_compl_right⟩

/-- The infinite product measure of a finite cylinder `(s : Set ι).pi t` is `∏ i ∈ s, μ i (t i)`
without any measurability assumption on the coordinate sets `t i`, matching `Measure.pi_pi` and
`Measure.prod_prod`. -/
@[simp]
theorem infinitePi_pi' (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (t : ∀ i, Set (X i)) :
    infinitePi μ ((s : Set ι).pi t) = ∏ i ∈ s, μ i (t i) := by
  classical
  let e₀ := MeasurableEquiv.piEquivPiSubtypeProd X (· ∈ s)
  have hmp := (measurePreserving_piEquivPiSubtypeProd_infinitePi μ (· ∈ s)).symm e₀
  have hpre : e₀.symm ⁻¹' (s : Set ι).pi t = (Set.univ.pi fun i : s ↦ t i.val) ×ˢ Set.univ := by
    rw [← MeasurableEquiv.coe_toEquiv_symm, ← Set.univ_pi_ite]
    dsimp only [e₀, MeasurableEquiv.piEquivPiSubtypeProd]
    rw [Equiv.preimage_piEquivPiSubtypeProd_symm_pi]
    congr 1
    · congr 1
      funext i
      exact ite_eq_left i.property
    · trans Set.univ.pi fun _ : {i // i ∉ s} ↦ (Set.univ : Set (X _))
      · congr 1
        funext j
        exact ite_eq_right j.property
      · exact Set.pi_univ _
  rw [← hmp.map_eq, MeasurableEquiv.map_apply, hpre, prod_prod, measure_univ, mul_one,
    infinitePi_eq_pi, pi_pi, Finset.univ_eq_attach,
    Finset.prod_attach s fun i ↦ μ i (t i)]

end SplitAndCylinder

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
    (Measure.infinitePi fun i : {i : ι // p i} => μ i.val).map
      (fun z i => if h : p i then z ⟨i, h⟩ else a₀ i) = Measure.infinitePi μ := by
  let pad : (∀ i : {i : ι // p i}, α i.val) → ∀ i, α i :=
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
        (s.subtype p : Set {i : ι // p i}).pi (fun i => t i.val) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, pad]
      constructor
      · intro hz i hi
        simpa [i.property] using hz i.val (Finset.mem_subtype.mp hi)
      · intro hz i hi
        split_ifs with h
        · exact hz ⟨i, h⟩ (Finset.mem_subtype.mpr hi)
        · exact hmem i hi h
    rw [hpre, Measure.infinitePi_pi _ (fun i _ => ht i.val),
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
