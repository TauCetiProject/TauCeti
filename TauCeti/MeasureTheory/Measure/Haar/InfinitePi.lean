/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.ProductMeasure

/-!
# Infinite products of probability Haar measures

For an arbitrary index type `ι` and probability measures `μ i` on measurable spaces `X i`,
`Measure.infinitePi μ` is the infinite product measure on `∀ i, X i` equipped with the product
σ-algebra:

* Splitting coordinates along a predicate `p : ι → Prop` via
  `MeasurableEquiv.piEquivPiSubtypeProd X p` carries `Measure.infinitePi μ` to the binary product
  of the two sub-products (`measurePreserving_piEquivPiSubtypeProd_infinitePi`), extending
  `MeasureTheory.measurePreserving_piEquivPiSubtypeProd` from finite to arbitrary index types.
* As a consequence, `Measure.infinitePi μ ((s : Set ι).pi t) = ∏ i ∈ s, μ i (t i)` holds for every
  finite index set `s : Finset ι` and arbitrary (not necessarily measurable) coordinate sets `t i`
  (`infinitePi_pi'`), matching `MeasureTheory.Measure.pi_pi` and `MeasureTheory.Measure.prod_prod`.
* When the factors carry measurable multiplication or inversion and invariant probability measures,
  `Measure.infinitePi μ` inherits left, right, and inversion invariance; when the factors are
  topological spaces and each `μ i` gives positive mass to nonempty open sets, so does
  `Measure.infinitePi μ` (without assuming `OpensMeasurableSpace`). In particular, an arbitrary
  product of probability Haar measures is a probability Haar measure on `∀ i, X i` for the product
  σ-algebra (`instIsHaarMeasureInfinitePi`, `instIsAddHaarMeasureInfinitePi`).
-/

public section

namespace TauCeti

open MeasureTheory MeasureTheory.Measure Set
open scoped Topology

universe u v

section SplitAndCylinder

variable {ι : Type u} {X : ι → Type v} [∀ i, MeasurableSpace (X i)]

/-- Splitting coordinates along a predicate `p` via `MeasurableEquiv.piEquivPiSubtypeProd` carries
an infinite product of probability measures to the product of the two complementary infinite
product measures. -/
theorem measurePreserving_piEquivPiSubtypeProd_infinitePi
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd X p) (infinitePi μ)
      ((infinitePi fun i : {i // p i} ↦ μ i.1).prod
        (infinitePi fun i : {i // ¬ p i} ↦ μ i.1)) := by
  let e := (MeasurableEquiv.piEquivPiSubtypeProd X p).symm
  refine MeasurePreserving.symm e ⟨e.measurable, eq_infinitePi μ fun s t ht ↦ ?_⟩
  let s₁ : Finset {i // p i} := s.subtype p
  let s₂ : Finset {i // ¬ p i} := s.subtype fun i ↦ ¬ p i
  have hcoe (q : (∀ i : {i // p i}, X i.1) × (∀ i : {i // ¬ p i}, X i.1)) :
      e q = (Equiv.piEquivPiSubtypeProd p X).symm q := rfl
  have hpre : e ⁻¹' (s : Set ι).pi t =
      ((s₁ : Set {i // p i}).pi fun i ↦ t i.1) ×ˢ
        ((s₂ : Set {i // ¬ p i}).pi fun i ↦ t i.1) := by
    ext q
    simp only [mem_preimage, hcoe, Set.mem_pi, Finset.mem_coe, mem_prod, s₁, s₂,
      Finset.mem_subtype]
    constructor
    · intro h
      refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
      · simpa only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left i.2] using h i.1 hi
      · simpa only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_right i.2] using h i.1 hi
    · rintro ⟨h₁, h₂⟩ i hi
      by_cases hp : p i
      · simpa only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left hp] using h₁ ⟨i, hp⟩ hi
      · simpa only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_right hp] using h₂ ⟨i, hp⟩ hi
  rw [e.map_apply, hpre, prod_prod,
    infinitePi_pi _ fun i _ ↦ ht i.1,
    infinitePi_pi _ fun i _ ↦ ht i.1]
  dsimp only [s₁, s₂]
  rw [Finset.prod_subtype_eq_prod_filter (fun i ↦ μ i (t i)),
    Finset.prod_subtype_eq_prod_filter (fun i ↦ μ i (t i)),
    Finset.prod_filter_mul_prod_filter_not]

/-- The infinite product measure of a finite cylinder `(s : Set ι).pi t` is `∏ i ∈ s, μ i (t i)`
without any measurability assumption on the coordinate sets `t i`, matching `Measure.pi_pi` and
`Measure.prod_prod`. -/
theorem infinitePi_pi' (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (t : ∀ i, Set (X i)) :
    infinitePi μ ((s : Set ι).pi t) = ∏ i ∈ s, μ i (t i) := by
  classical
  let e₀ := MeasurableEquiv.piEquivPiSubtypeProd X (· ∈ s)
  let e := e₀.symm
  have hmp := (measurePreserving_piEquivPiSubtypeProd_infinitePi μ (· ∈ s)).symm e₀
  have hcoe (q : (∀ i : s, X i.1) × (∀ i : {i // i ∉ s}, X i.1)) :
      e q = (Equiv.piEquivPiSubtypeProd (· ∈ s) X).symm q := rfl
  have hpre : e ⁻¹' (s : Set ι).pi t = (Set.univ.pi fun i : s ↦ t i.1) ×ˢ Set.univ := by
    ext q
    simp only [mem_preimage, hcoe, Set.mem_pi, Finset.mem_coe, mem_prod, mem_univ,
      forall_true_left, and_true]
    refine ⟨fun h i ↦ ?_, fun h i hi ↦ ?_⟩
    · simpa only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left i.2] using h i.1 i.2
    · simpa only [Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left hi] using h ⟨i, hi⟩
  rw [← hmp.map_eq, e.map_apply, hpre, prod_prod, measure_univ, mul_one,
    infinitePi_eq_pi, pi_pi, Finset.univ_eq_attach,
    Finset.prod_attach s fun i ↦ μ i (t i)]

end SplitAndCylinder

section Invariance

variable {ι : Type u} {X : ι → Type v} [∀ i, MeasurableSpace (X i)]

@[to_additive]
instance instIsMulLeftInvariantInfinitePi [∀ i, Mul (X i)] [∀ i, MeasurableMul (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsMulLeftInvariant] :
    (infinitePi μ).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    have hmul : (g * · : (∀ i, X i) → ∀ i, X i) = fun x i ↦ g i * x i :=
      funext fun x ↦ funext fun i ↦ Pi.mul_apply g x i
    rw [hmul, infinitePi_map_pi μ fun i ↦ measurable_const_mul (g i)]
    simp_rw [map_mul_left_eq_self]

@[to_additive]
instance instIsMulRightInvariantInfinitePi [∀ i, Mul (X i)] [∀ i, MeasurableMul (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsMulRightInvariant] :
    (infinitePi μ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have hmul : (· * g : (∀ i, X i) → ∀ i, X i) = fun x i ↦ x i * g i :=
      funext fun x ↦ funext fun i ↦ Pi.mul_apply x g i
    rw [hmul, infinitePi_map_pi μ fun i ↦ measurable_mul_const (g i)]
    simp_rw [map_mul_right_eq_self]

@[to_additive]
instance instIsInvInvariantInfinitePi [∀ i, Inv (X i)] [∀ i, MeasurableInv (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsInvInvariant] :
    (infinitePi μ).IsInvInvariant where
  inv_eq_self := by
    have hinv : (Inv.inv : (∀ i, X i) → ∀ i, X i) = fun x i ↦ (x i)⁻¹ :=
      funext fun x ↦ funext fun i ↦ Pi.inv_apply x i
    rw [Measure.inv_def, hinv, infinitePi_map_pi μ fun _ ↦ measurable_inv]
    simp_rw [← Measure.inv_def, Measure.inv_eq_self]

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
