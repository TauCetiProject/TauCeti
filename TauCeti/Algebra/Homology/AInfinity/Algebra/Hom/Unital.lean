/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.LinearAlgebra.TensorCoalgebra.Degenerate

/-!
# Strictly unital morphisms of A-infinity algebras

An `A∞` morphism between algebras with chosen strict units is strictly unital when its linear
component carries the source unit to the target unit and every higher component vanishes as soon
as one input is the source unit.  This file packages that property for general `A∞` morphisms.

The definition is stated through the unsuspended components, so it can be used without exposing
the reduced bar construction.  The identity morphism is strictly unital, and a strict morphism is
strictly unital in this sense exactly when its underlying linear map preserves the unit.  Thus the
existing bundled strictly unital strict morphisms embed into the general notion. General
strictly unital morphisms are closed under composition: their bar maps preserve the span of
unit-containing words, and their Taylor maps read only its one-letter component.

## Main definitions

* `TauCeti.AInfinityHom.IsStrictlyUnital`: the strictly unitality predicate for a general
  `A∞` morphism.

## Main results

* `TauCeti.AInfinityHom.isStrictlyUnital_id`: the identity is strictly unital.
* `TauCeti.AInfinityHom.IsStrict.isStrictlyUnital_iff`: for a strict `A∞` morphism,
  strictly unitality is equivalent to preservation of the unit by its linear part.
* `TauCeti.AInfinityHom.IsStrictlyUnital.comp`: composition preserves strict unitality,
  including when both factors have nonzero higher components.
* `TauCeti.AInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom`: a bundled strictly
  unital strict morphism gives a strictly unital `A∞` morphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.4.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

namespace AInfinityHom

/-! ### The strictly unitality predicate -/

/-- A general `A∞` morphism is **strictly unital** when its linear component preserves the
chosen unit and every component of arity other than one vanishes on a tuple containing the source
unit.  Since `A∞` algebras here are uncurved, the arity-zero clause is vacuous. -/
structure IsStrictlyUnital (f : AInfinityHom AA BB) {eA : A} {eB : B}
    (_hA : AA.StrictUnit eA) (_hB : BB.StrictUnit eB) : Prop where
  /-- The linear component preserves the chosen strict unit. -/
  map_unit : f.linearPart eA = eB
  /-- Every higher component vanishes on a tuple containing the source strict unit. -/
  component_eq_zero : ∀ {n : ℕ}, n ≠ 1 → ∀ (x : Fin n → A),
    (∃ i, x i = eA) → f.component n x = 0

namespace IsStrictlyUnital

variable {f : AInfinityHom AA BB} {eA : A} {eB : B}
  {hA : AA.StrictUnit eA} {hB : BB.StrictUnit eB}

/-- A higher component of a strictly unital morphism vanishes when a specified input is the
source unit.  This is not a `simp` lemma: neither the units nor the index of the unit input can
be recovered from the left-hand side. -/
theorem component_eq_zero_of_eq_unit (hf : f.IsStrictlyUnital hA hB) {n : ℕ} (hn : n ≠ 1)
    (x : Fin n → A) {i : Fin n} (hi : x i = eA) : f.component n x = 0 :=
  hf.component_eq_zero hn x ⟨i, hi⟩

end IsStrictlyUnital

end AInfinityHom

namespace AInfinityHom

/-- A strict `A∞` morphism is strictly unital exactly when its linear part preserves the chosen
strict unit.  All higher unit clauses follow from strictness. -/
theorem IsStrict.isStrictlyUnital_iff {f : AInfinityHom AA BB} {eA : A} {eB : B}
    {hA : AA.StrictUnit eA} {hB : BB.StrictUnit eB} (hf : f.IsStrict) :
    f.IsStrictlyUnital hA hB ↔ f.linearPart eA = eB := by
  constructor
  · exact IsStrictlyUnital.map_unit
  · intro hunit
    refine ⟨hunit, ?_⟩
    intro n hn x _hx
    rw [← hf.toAInfinityHom_toStrictHom]
    exact MultilinearMap.congr_fun
      (hf.toStrictHom.component_toAInfinityHom_eq_zero hn) x

/-- A strict `A∞` morphism whose linear part preserves the unit is strictly unital. -/
theorem IsStrict.isStrictlyUnital {f : AInfinityHom AA BB} {eA : A} {eB : B}
    {hA : AA.StrictUnit eA} {hB : BB.StrictUnit eB} (hf : f.IsStrict)
    (hunit : f.linearPart eA = eB) : f.IsStrictlyUnital hA hB :=
  hf.isStrictlyUnital_iff.2 hunit

/-! ### Unit-containing bar words and general composition -/

namespace IsStrictlyUnital

variable {f : AInfinityHom AA BB} {eA : A} {eB : B}
  {hA : AA.StrictUnit eA} {hB : BB.StrictUnit eB}

/-- A higher suspended Taylor component vanishes on any word containing the source unit. -/
theorem taylor_of_tprod_eq_zero (hf : f.IsStrictlyUnital hA hB)
    (n : {n : ℕ // 0 < n}) (hn : n.1 ≠ 1) (x : Fin n.1 → A)
    (hx : ∃ i, x i = eA) :
    f.taylor (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) = 0 := by
  have htwist : f.component n.1
      (fun i ↦ AA.grading.koszulTwist ((n.1 : ℤ) - 1 - i) (x i)) =
      f.taylor (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) := by
    rw [component_apply f n.1 n.2]
    simp only [InternalGrading.koszulTwist_koszulTwist]
  rw [← htwist]
  apply hf.component_eq_zero hn
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, by rw [hi, AA.grading.koszulTwist_apply_of_mem_zero hA.degree_zero]⟩

/-- The bar map of a strictly unital morphism preserves the span of unit-containing words. -/
theorem barMap_mem_degenerateWords (hf : f.IsStrictlyUnital hA hB)
    {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.degenerateWords R A eA) :
    f.barMap z ∈ ReducedTensorWords.degenerateWords R B eB := by
  rw [f.barMap_eq_coalgHom]
  exact ReducedTensorWords.coalgHom_mem_degenerateWords f.taylor
    (by rw [← linearPart_apply, hf.map_unit]) hf.taylor_of_tprod_eq_zero hz

/-- On unit-containing bar words the Taylor map reads only the one-letter component. -/
theorem taylor_eq_linearPart_letter (hf : f.IsStrictlyUnital hA hB)
    {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.degenerateWords R A eA) :
    f.taylor z = f.linearPart (ReducedTensorWords.letter R A z) := by
  rw [linearPart_apply]
  exact ReducedTensorWords.apply_eq_comp_letter_of_mem_degenerateWords f.taylor
    hf.taylor_of_tprod_eq_zero hz

/-- The composite of two general strictly unital `A∞` morphisms is strictly unital. -/
theorem comp {CC : AInfinityAlgebra R C} {g : AInfinityHom BB CC} {eC : C}
    {hC : CC.StrictUnit eC} (hg : g.IsStrictlyUnital hB hC)
    (hf : f.IsStrictlyUnital hA hB) : (g.comp f).IsStrictlyUnital hA hC := by
  refine ⟨?_, ?_⟩
  · rw [linearPart_comp, LinearMap.comp_apply, hf.map_unit, hg.map_unit]
  · intro n hn x hx
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hnpos : 0 < n := by omega
      let y : Fin n → A := fun i ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)
      have hy : ∃ i, y i = eA := by
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, by simp only [y, hi,
          AA.grading.koszulTwist_apply_of_mem_zero hA.degree_zero]⟩
      have hz := ReducedTensorWords.of_tprod_mem_degenerateWords (R := R) ⟨n, hnpos⟩ y hy
      rw [component_apply _ n hnpos, taylor_comp, LinearMap.comp_apply,
        hg.taylor_eq_linearPart_letter (hf.barMap_mem_degenerateWords hz)]
      rw [← LinearMap.comp_apply (ReducedTensorWords.letter R B), ← f.taylor_def,
        hf.taylor_of_tprod_eq_zero ⟨n, hnpos⟩ hn y hy, map_zero]

end IsStrictlyUnital

/-! ### Identities -/

/-- The identity `A∞` morphism is strictly unital for every strict unit. -/
@[simp]
theorem isStrictlyUnital_id {eA : A} (hA : AA.StrictUnit eA) :
    (AInfinityHom.id AA).IsStrictlyUnital hA hA := by
  apply (isStrict_id AA).isStrictlyUnital
  rw [linearPart_id]
  rfl

end AInfinityHom

/-! ### Bundled strictly unital strict morphisms -/

namespace AInfinityStrictUnitalHom

variable {eA : A} {eB : B} {hA : AA.StrictUnit eA} {hB : BB.StrictUnit eB}

/-- A bundled strictly unital strict morphism, regarded as a general `A∞` morphism, is strictly
unital in the componentwise sense. -/
@[simp]
theorem isStrictlyUnital_toAInfinityHom (f : AInfinityStrictUnitalHom hA hB) :
    f.toAInfinityStrictHom.toAInfinityHom.IsStrictlyUnital hA hB := by
  apply (AInfinityHom.isStrict_toAInfinityHom f.toAInfinityStrictHom).isStrictlyUnital
  rw [AInfinityStrictHom.linearPart_toAInfinityHom]
  exact f.map_unit

end AInfinityStrictUnitalHom

end TauCeti
