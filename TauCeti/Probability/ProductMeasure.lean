/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.ProductMeasure
-- Non-public: independence of disjoint coordinate blocks is used only inside the proofs.
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Probability.Independence.DisjointBlocks
import TauCeti.Probability.Independence.InfinitePi

/-!
# Infinite product measures: coordinate splitting, cylinders, and invariance

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
* **Invariance, open-positivity, and Haar measures**: `Measure.infinitePi μ` inherits left, right,
  and inversion invariance (`TauCeti.instIsMulLeftInvariantInfinitePi`,
  `TauCeti.instIsMulRightInvariantInfinitePi`, `TauCeti.instIsInvInvariantInfinitePi`), positivity
  on nonempty open sets without assuming `OpensMeasurableSpace`
  (`TauCeti.instIsOpenPosMeasureInfinitePi`), and the Haar-measure property on `∀ i, X i` with the
  product σ-algebra (`TauCeti.instIsHaarMeasureInfinitePi`,
  `TauCeti.instIsAddHaarMeasureInfinitePi`).

## Main results

* `TauCeti.MeasureTheory.Measure.infinitePi_map_none_some`: splitting off `none` in `Option ι`.
* `TauCeti.measurePreserving_piEquivPiSubtypeProd_infinitePi`: splitting along a predicate `p`.
* `TauCeti.infinitePi_pi'`: unconditional finite-cylinder formula for `Measure.infinitePi`.
* `TauCeti.instIsHaarMeasureInfinitePi` / `TauCeti.instIsAddHaarMeasureInfinitePi`: infinite
  products of probability Haar measures are probability Haar measures.
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
      ((infinitePi fun i : {i // p i} ↦ μ i.1).prod
        (infinitePi fun i : {i // ¬ p i} ↦ μ i.1)) :=
  ⟨(MeasurableEquiv.piEquivPiSubtypeProd X p).measurable, by
    have hfun : (MeasurableEquiv.piEquivPiSubtypeProd X p :
        (∀ i, X i) → (∀ i : {i // p i}, X i.1) × (∀ i : {i // ¬ p i}, X i.1)) =
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
  have hpre : e₀.symm ⁻¹' (s : Set ι).pi t = (Set.univ.pi fun i : s ↦ t i.1) ×ˢ Set.univ := by
    rw [← MeasurableEquiv.coe_toEquiv_symm, ← Set.univ_pi_ite]
    dsimp only [e₀, MeasurableEquiv.piEquivPiSubtypeProd]
    rw [Equiv.preimage_piEquivPiSubtypeProd_symm_pi]
    congr 1
    · congr 1
      funext i
      exact ite_eq_left i.2
    · trans Set.univ.pi fun _ : {i // i ∉ s} ↦ (Set.univ : Set (X _))
      · congr 1
        funext j
        exact ite_eq_right j.2
      · exact Set.pi_univ _
  rw [← hmp.map_eq, MeasurableEquiv.map_apply, hpre, prod_prod, measure_univ, mul_one,
    infinitePi_eq_pi, pi_pi, Finset.univ_eq_attach,
    Finset.prod_attach s fun i ↦ μ i (t i)]

end SplitAndCylinder

section Invariance

open _root_.MeasureTheory.Measure Set
open scoped Topology

universe u v

variable {ι : Type u} {X : ι → Type v} [∀ i, MeasurableSpace (X i)]

/-- An infinite product of left-invariant probability measures is left-invariant. -/
@[to_additive
/-- An infinite product of left-add-invariant probability measures is left-add-invariant. -/]
instance instIsMulLeftInvariantInfinitePi [∀ i, Mul (X i)] [∀ i, MeasurableMul (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsMulLeftInvariant] :
    (infinitePi μ).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    have hmul : (g * · : (∀ i, X i) → ∀ i, X i) = fun x i ↦ g i * x i :=
      funext fun x ↦ funext fun i ↦ Pi.mul_apply g x i
    rw [hmul, infinitePi_map_pi μ fun i ↦ measurable_const_mul (g i)]
    simp_rw [map_mul_left_eq_self]

/-- An infinite product of right-invariant probability measures is right-invariant. -/
@[to_additive
/-- An infinite product of right-add-invariant probability measures is right-add-invariant. -/]
instance instIsMulRightInvariantInfinitePi [∀ i, Mul (X i)] [∀ i, MeasurableMul (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsMulRightInvariant] :
    (infinitePi μ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have hmul : (· * g : (∀ i, X i) → ∀ i, X i) = fun x i ↦ x i * g i :=
      funext fun x ↦ funext fun i ↦ Pi.mul_apply x g i
    rw [hmul, infinitePi_map_pi μ fun i ↦ measurable_mul_const (g i)]
    simp_rw [map_mul_right_eq_self]

/-- An infinite product of inversion-invariant probability measures is inversion-invariant. -/
@[to_additive
/-- An infinite product of negation-invariant probability measures is negation-invariant. -/]
instance instIsInvInvariantInfinitePi [∀ i, Inv (X i)] [∀ i, MeasurableInv (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsInvInvariant] :
    (infinitePi μ).IsInvInvariant where
  inv_eq_self := by
    have hinv : (Inv.inv : (∀ i, X i) → ∀ i, X i) = fun x i ↦ (x i)⁻¹ :=
      funext fun x ↦ funext fun i ↦ Pi.inv_apply x i
    rw [Measure.inv_def, hinv, infinitePi_map_pi μ fun _ ↦ measurable_inv]
    simp_rw [← Measure.inv_def, Measure.inv_eq_self]

/-- An infinite product of probability measures giving positive mass to nonempty open sets gives
positive mass to nonempty open sets in the product topology. -/
instance instIsOpenPosMeasureInfinitePi [∀ i, TopologicalSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsOpenPosMeasure] :
    (infinitePi μ).IsOpenPosMeasure where
  open_pos U hU := by
    rintro ⟨x, hx⟩
    obtain ⟨s, t, ht, hsU⟩ := isOpen_pi_iff.mp hU x hx
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsU))
    rw [infinitePi_pi', CanonicallyOrderedAdd.prod_pos]
    exact fun i hi ↦ (ht i hi).1.measure_pos (μ i) ⟨x i, (ht i hi).2⟩

/-- An infinite product of probability Haar measures is a probability Haar measure on `∀ i, X i`
with the product σ-algebra. -/
@[to_additive
/-- An infinite product of probability additive Haar measures is a probability additive Haar
measure on `∀ i, X i` with the product σ-algebra. -/]
instance instIsHaarMeasureInfinitePi [∀ i, Group (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, MeasurableMul (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsHaarMeasure] :
    (infinitePi μ).IsHaarMeasure where

end Invariance

end TauCeti
