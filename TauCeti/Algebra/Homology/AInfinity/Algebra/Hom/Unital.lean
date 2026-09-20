/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Component
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict

/-!
# Strictly unital morphisms of A-infinity algebras

An `A∞` morphism between algebras with chosen strict units is strictly unital when its linear
component carries the source unit to the target unit and every higher component vanishes as soon
as one input is the source unit.  This file packages that property for general `A∞` morphisms.

The definition is stated through the unsuspended components, so it can be used without exposing
the reduced bar construction.  The identity morphism is strictly unital, and a strict morphism is
strictly unital in this sense exactly when its underlying linear map preserves the unit.  Thus the
existing bundled strictly unital strict morphisms embed into the general notion.

## Main definitions

* `TauCeti.AInfinityHom.IsStrictlyUnital`: the strictly unitality predicate for a general
  `A∞` morphism.

## Main results

* `TauCeti.AInfinityHom.isStrictlyUnital_id`: the identity is strictly unital.
* `TauCeti.AInfinityHom.IsStrict.isStrictlyUnital_iff`: for a strict `A∞` morphism,
  strictly unitality is equivalent to preservation of the unit by its linear part.
* `TauCeti.AInfinityHom.IsStrictlyUnital.comp_of_isStrict`: postcomposition by a strict
  unit-preserving morphism preserves strictly unitality.
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

attribute [simp] map_unit

/-- A higher component of a strictly unital morphism vanishes when a specified input is the
source unit. -/
theorem component_eq_zero_of_eq_unit (hf : f.IsStrictlyUnital hA hB) {n : ℕ} (hn : n ≠ 1)
    (x : Fin n → A) {i : Fin n} (hi : x i = eA) : f.component n x = 0 :=
  hf.component_eq_zero hn x ⟨i, hi⟩

end IsStrictlyUnital

end AInfinityHom

/-! ### Components of strict morphisms -/

namespace AInfinityStrictHom

/-- The unsuspended component of a strict morphism in arity other than one is zero. -/
theorem component_toAInfinityHom_eq_zero (f : AInfinityStrictHom AA BB) {n : ℕ} (hn : n ≠ 1) :
    f.toAInfinityHom.component n = 0 := by
  rcases n with _ | n
  · exact f.toAInfinityHom.component_zero
  · apply MultilinearMap.ext
    intro x
    rw [AInfinityHom.component_apply _ (n + 1) (by omega), taylor_toAInfinityHom,
      LinearMap.comp_apply, ReducedTensorWords.letter_apply]
    have hlength : (⟨n + 1, by omega⟩ : {k : ℕ // 0 < k}) ≠ 1 := by
      intro h
      apply hn
      simpa using congrArg Subtype.val h
    rw [ReducedTensorWords.component_of_of_ne R A hlength]
    simp

/-- The arity-one component of a strict morphism is its underlying linear map. -/
theorem component_toAInfinityHom_one (f : AInfinityStrictHom AA BB) :
    f.toAInfinityHom.component 1 =
      (MultilinearMap.ofSubsingleton R A B (0 : Fin 1)) f.toLinearMap := by
  rw [AInfinityHom.component_one, linearPart_toAInfinityHom]

end AInfinityStrictHom

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

/-! ### Composition with a strict outer morphism -/

/-- Postcomposition by a strict unit-preserving morphism preserves strictly unitality. This is the
composition case in which the outer morphism has no higher components. -/
theorem IsStrictlyUnital.comp_toAInfinityHom {CC : AInfinityAlgebra R C}
    {f : AInfinityHom AA BB} (g : AInfinityStrictHom BB CC)
    {eA : A} {eB : B} {eC : C}
    {hA : AA.StrictUnit eA} {hB : BB.StrictUnit eB} {hC : CC.StrictUnit eC}
    (hf : f.IsStrictlyUnital hA hB) (hgunit : g eB = eC) :
    (g.toAInfinityHom.comp f).IsStrictlyUnital hA hC := by
  refine ⟨?_, ?_⟩
  · rw [linearPart_comp, AInfinityStrictHom.linearPart_toAInfinityHom,
      LinearMap.comp_apply, hf.map_unit]
    exact hgunit
  · intro n hn x hx
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    rw [component_apply _ n hnpos, taylor_comp, LinearMap.comp_apply,
      AInfinityStrictHom.taylor_toAInfinityHom, LinearMap.comp_apply]
    let w := ReducedTensorWords.of R A ⟨n, hnpos⟩
      (PiTensorProduct.tprod R fun i ↦
        AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i))
    have htaylor : ReducedTensorWords.letter R B (f.barMap w) = f.taylor w := by
      rw [f.taylor_def, LinearMap.comp_apply]
    rw [htaylor]
    rw [← component_apply f n hnpos, hf.component_eq_zero hn x hx, map_zero]

/-- Postcomposition by a strict `A∞` morphism whose linear part preserves the chosen unit
preserves strictly unitality. -/
theorem IsStrictlyUnital.comp_of_isStrict {CC : AInfinityAlgebra R C}
    {f : AInfinityHom AA BB} {g : AInfinityHom BB CC}
    {eA : A} {eB : B} {eC : C}
    {hA : AA.StrictUnit eA} {hB : BB.StrictUnit eB} {hC : CC.StrictUnit eC}
    (hf : f.IsStrictlyUnital hA hB) (hg : g.IsStrict) (hgunit : g.linearPart eB = eC) :
    (g.comp f).IsStrictlyUnital hA hC := by
  have hunit : hg.toStrictHom eB = eC := by
    rw [← AInfinityStrictHom.coe_toLinearMap, hg.toStrictHom_toLinearMap]
    exact hgunit
  have h := hf.comp_toAInfinityHom (hC := hC) hg.toStrictHom hunit
  rw [hg.toAInfinityHom_toStrictHom] at h
  exact h

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
