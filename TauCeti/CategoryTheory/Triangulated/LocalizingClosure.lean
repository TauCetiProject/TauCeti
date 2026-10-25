/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Triangulated.Generators
public import TauCeti.CategoryTheory.Preadditive.EilenbergSwindle
public import TauCeti.CategoryTheory.Triangulated.Opposite.Subcategory

/-!
# Localizing and colocalizing closures in a pretriangulated category

Let `P` be a class of objects of a pretriangulated category `C`. Its **localizing closure** is
the smallest isomorphism-closed triangulated subcategory of `C` containing `P` and closed under
coproducts indexed by types in the hom universe of `C`; it is the infimum of all such
subcategories. Dually, the **colocalizing closure** is the smallest isomorphism-closed
triangulated subcategory containing `P` and closed under such products.

A triangulated subcategory closed under countable coproducts is closed under direct summands, by
the Eilenberg swindle `CategoryTheory.Retract.biprodSigmaIso`: if `X` is a retract of `Y`, then
`X ⊞ Y^(ℕ) ≅ Y^(ℕ)`, and the split triangle `X ⟶ X ⊞ Y^(ℕ) ⟶ Y^(ℕ) ⟶ X⟦1⟧` puts `X` in the
subcategory. The dual statement for products follows by passing to the opposite category.
Consequently, when `C` has countable coproducts (respectively products), the thick closure
`P.triangEnvelope` is contained in the localizing (respectively colocalizing) closure.

For curved DG modules, with `P` the class of totalizations of short exact sequences, these are
Positselski's absolutely acyclic (`P.triangEnvelope`), coacyclic (`P.localizingClosure`) and
contraacyclic (`P.colocalizingClosure`) objects, and the two inclusions are those inducing the
comparison functors from the absolute derived category to the coderived and contraderived
categories.

## Main definitions

* `CategoryTheory.ObjectProperty.localizingClosure`: the localizing closure of `P`.
* `CategoryTheory.ObjectProperty.colocalizingClosure`: the colocalizing closure of `P`.

## Main results

* `CategoryTheory.ObjectProperty.isStableUnderRetracts_of_isClosedUnderCoproducts_nat`:
  an isomorphism-closed property closed under countable coproducts and satisfying
  `IsTriangulatedClosed₁` (for instance a triangulated subcategory) is closed under retracts.
* `CategoryTheory.ObjectProperty.isStableUnderRetracts_of_isClosedUnderProducts_nat`: the dual
  statement for countable products, assuming `IsTriangulatedClosed₃`.
* `CategoryTheory.ObjectProperty.localizingClosure_le_iff`,
  `CategoryTheory.ObjectProperty.colocalizingClosure_le_iff`: the universal properties.
* `CategoryTheory.ObjectProperty.triangEnvelope_le_localizingClosure`,
  `CategoryTheory.ObjectProperty.triangEnvelope_le_colocalizingClosure`: the thick closure is
  contained in the localizing and in the colocalizing closure.

## References

* A. Neeman, *Triangulated categories*, Annals of Mathematics Studies 148, Princeton University
  Press (2001), Proposition 1.6.8 and Definition 3.2.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6.
-/

public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated Pretriangulated.Opposite ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section Thick

variable (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]

/-- An isomorphism-closed property closed under countable coproducts, and such that the first
object of a distinguished triangle satisfies it whenever the other two do, is closed under
retracts (Eilenberg swindle). This applies in particular to triangulated subcategories. -/
theorem isStableUnderRetracts_of_isClosedUnderCoproducts_nat [P.IsTriangulatedClosed₁]
    [HasCoproductsOfShape ℕ C] [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] :
    P.IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    have hW : P (∐ fun _ : ℕ ↦ Y) := P.prop_colimit _ fun _ ↦ hY
    exact P.ext_of_isTriangulatedClosed₁ _ (binaryBiproductTriangle_distinguished X _)
      (P.prop_of_iso h.biprodSigmaIso.symm hW) hW

/-- An isomorphism-closed property closed under countable products, and such that the third
object of a distinguished triangle satisfies it whenever the other two do, is closed under
retracts. This applies in particular to triangulated subcategories. -/
theorem isStableUnderRetracts_of_isClosedUnderProducts_nat [P.IsTriangulatedClosed₃]
    [HasProductsOfShape ℕ C] [P.IsClosedUnderLimitsOfShape (Discrete ℕ)] :
    P.IsStableUnderRetracts := by
  have : P.op.IsClosedUnderColimitsOfShape (Discrete ℕ) :=
    have := (P.isClosedUnderLimitsOfShape_iff_op (Discrete ℕ)).1 inferInstance
    .of_equivalence (Discrete.opposite ℕ)
  have := P.op.isStableUnderRetracts_of_isClosedUnderCoproducts_nat
  exact ⟨fun h hY ↦ P.op.prop_of_retract h.op hY⟩

end Thick

section Localizing

variable (P : ObjectProperty C)

/-- The localizing closure of `P`: the smallest isomorphism-closed triangulated subcategory
containing `P` and closed under coproducts indexed by types in `Type v`, defined as the
infimum of all such subcategories. -/
def localizingClosure : ObjectProperty C :=
  ⨅ (Q : ObjectProperty C) (_ : P ≤ Q) (_ : Q.IsTriangulated) (_ : Q.IsClosedUnderIsomorphisms)
    (_ : ∀ J : Type v, Q.IsClosedUnderColimitsOfShape (Discrete J)), Q

/-- An object lies in the localizing closure of `P` exactly when it lies in every
isomorphism-closed triangulated subcategory containing `P` and closed under
coproducts indexed by `Type v`. -/
lemma prop_localizingClosure_iff (X : C) :
    P.localizingClosure X ↔ ∀ Q : ObjectProperty C, P ≤ Q → Q.IsTriangulated →
      Q.IsClosedUnderIsomorphisms → (∀ J : Type v, Q.IsClosedUnderColimitsOfShape (Discrete J)) →
        Q X := by
  simp [localizingClosure]

lemma le_localizingClosure : P ≤ P.localizingClosure :=
  fun X hX ↦ (P.prop_localizingClosure_iff X).2 fun _ hPQ _ _ _ ↦ hPQ X hX

variable {P} in
lemma localizingClosure_le {Q : ObjectProperty C} [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] [∀ J : Type v, Q.IsClosedUnderColimitsOfShape (Discrete J)]
    (h : P ≤ Q) : P.localizingClosure ≤ Q :=
  fun X hX ↦ (P.prop_localizingClosure_iff X).1 hX Q h inferInstance inferInstance inferInstance

/-- The universal property of the localizing closure. -/
lemma localizingClosure_le_iff {Q : ObjectProperty C} [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] [∀ J : Type v, Q.IsClosedUnderColimitsOfShape (Discrete J)] :
    P.localizingClosure ≤ Q ↔ P ≤ Q :=
  ⟨(P.le_localizingClosure).trans, localizingClosure_le⟩

instance : P.localizingClosure.IsClosedUnderIsomorphisms where
  of_iso e hX := (P.prop_localizingClosure_iff _).2 fun Q hPQ _ _ _ ↦
    Q.prop_of_iso e ((P.prop_localizingClosure_iff _).1 hX Q hPQ ‹_› ‹_› ‹_›)

instance : P.localizingClosure.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, (P.prop_localizingClosure_iff _).2 fun Q _ _ _ _ ↦
    Q.prop_of_isZero (isZero_zero C)⟩
  isStableUnderShiftBy a := ⟨fun X hX ↦ (P.prop_localizingClosure_iff _).2 fun Q hPQ _ _ _ ↦
    Q.le_shift a X ((P.prop_localizingClosure_iff _).1 hX Q hPQ ‹_› ‹_› ‹_›)⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    (P.prop_localizingClosure_iff _).2 fun Q hPQ _ _ _ ↦ Q.ext_of_isTriangulatedClosed₂ T hT
      ((P.prop_localizingClosure_iff _).1 h₁ Q hPQ ‹_› ‹_› ‹_›)
      ((P.prop_localizingClosure_iff _).1 h₃ Q hPQ ‹_› ‹_› ‹_›)

instance (J : Type v) : P.localizingClosure.IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := fun _ ⟨h⟩ ↦ (P.prop_localizingClosure_iff _).2 fun _ hPQ _ _ _ ↦
    (h.ofLE (localizingClosure_le hPQ)).prop

instance [HasCoproductsOfShape ℕ C] : P.localizingClosure.IsStableUnderRetracts :=
  have : P.localizingClosure.IsClosedUnderColimitsOfShape (Discrete ℕ) :=
    .of_equivalence (Discrete.equivalence Equiv.ulift.{v})
  P.localizingClosure.isStableUnderRetracts_of_isClosedUnderCoproducts_nat

/-- When `C` has countable coproducts, the thick closure of `P` is contained in its localizing
closure. -/
theorem triangEnvelope_le_localizingClosure [HasCoproductsOfShape ℕ C] :
    P.triangEnvelope ≤ P.localizingClosure :=
  P.triangEnvelope_le_iff.2 P.le_localizingClosure

variable {P} in
lemma monotone_localizingClosure {Q : ObjectProperty C} (h : P ≤ Q) :
    P.localizingClosure ≤ Q.localizingClosure :=
  localizingClosure_le (h.trans Q.le_localizingClosure)

end Localizing

section Colocalizing

variable (P : ObjectProperty C)

/-- The colocalizing closure of `P`: the smallest isomorphism-closed triangulated subcategory
containing `P` and closed under products indexed by types in `Type v`, defined as the infimum
of all such subcategories. -/
def colocalizingClosure : ObjectProperty C :=
  ⨅ (Q : ObjectProperty C) (_ : P ≤ Q) (_ : Q.IsTriangulated) (_ : Q.IsClosedUnderIsomorphisms)
    (_ : ∀ J : Type v, Q.IsClosedUnderLimitsOfShape (Discrete J)), Q

/-- An object lies in the colocalizing closure of `P` exactly when it lies in every
isomorphism-closed triangulated subcategory containing `P` and closed under
products indexed by `Type v`. -/
lemma prop_colocalizingClosure_iff (X : C) :
    P.colocalizingClosure X ↔ ∀ Q : ObjectProperty C, P ≤ Q → Q.IsTriangulated →
      Q.IsClosedUnderIsomorphisms → (∀ J : Type v, Q.IsClosedUnderLimitsOfShape (Discrete J)) →
        Q X := by
  simp [colocalizingClosure]

lemma le_colocalizingClosure : P ≤ P.colocalizingClosure :=
  fun X hX ↦ (P.prop_colocalizingClosure_iff X).2 fun _ hPQ _ _ _ ↦ hPQ X hX

variable {P} in
lemma colocalizingClosure_le {Q : ObjectProperty C} [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] [∀ J : Type v, Q.IsClosedUnderLimitsOfShape (Discrete J)]
    (h : P ≤ Q) : P.colocalizingClosure ≤ Q :=
  fun X hX ↦ (P.prop_colocalizingClosure_iff X).1 hX Q h inferInstance inferInstance inferInstance

/-- The universal property of the colocalizing closure. -/
lemma colocalizingClosure_le_iff {Q : ObjectProperty C} [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] [∀ J : Type v, Q.IsClosedUnderLimitsOfShape (Discrete J)] :
    P.colocalizingClosure ≤ Q ↔ P ≤ Q :=
  ⟨(P.le_colocalizingClosure).trans, colocalizingClosure_le⟩

instance : P.colocalizingClosure.IsClosedUnderIsomorphisms where
  of_iso e hX := (P.prop_colocalizingClosure_iff _).2 fun Q hPQ _ _ _ ↦
    Q.prop_of_iso e ((P.prop_colocalizingClosure_iff _).1 hX Q hPQ ‹_› ‹_› ‹_›)

instance : P.colocalizingClosure.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, (P.prop_colocalizingClosure_iff _).2 fun Q _ _ _ _ ↦
    Q.prop_of_isZero (isZero_zero C)⟩
  isStableUnderShiftBy a := ⟨fun X hX ↦ (P.prop_colocalizingClosure_iff _).2 fun Q hPQ _ _ _ ↦
    Q.le_shift a X ((P.prop_colocalizingClosure_iff _).1 hX Q hPQ ‹_› ‹_› ‹_›)⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    (P.prop_colocalizingClosure_iff _).2 fun Q hPQ _ _ _ ↦ Q.ext_of_isTriangulatedClosed₂ T hT
      ((P.prop_colocalizingClosure_iff _).1 h₁ Q hPQ ‹_› ‹_› ‹_›)
      ((P.prop_colocalizingClosure_iff _).1 h₃ Q hPQ ‹_› ‹_› ‹_›)

instance (J : Type v) : P.colocalizingClosure.IsClosedUnderLimitsOfShape (Discrete J) where
  limitsOfShape_le := fun _ ⟨h⟩ ↦ (P.prop_colocalizingClosure_iff _).2 fun _ hPQ _ _ _ ↦
    (h.ofLE (colocalizingClosure_le hPQ)).prop

instance [HasProductsOfShape ℕ C] : P.colocalizingClosure.IsStableUnderRetracts :=
  have : P.colocalizingClosure.IsClosedUnderLimitsOfShape (Discrete ℕ) :=
    .of_equivalence (Discrete.equivalence Equiv.ulift.{v})
  P.colocalizingClosure.isStableUnderRetracts_of_isClosedUnderProducts_nat

/-- When `C` has countable products, the thick closure of `P` is contained in its colocalizing
closure. -/
theorem triangEnvelope_le_colocalizingClosure [HasProductsOfShape ℕ C] :
    P.triangEnvelope ≤ P.colocalizingClosure :=
  P.triangEnvelope_le_iff.2 P.le_colocalizingClosure

variable {P} in
lemma monotone_colocalizingClosure {Q : ObjectProperty C} (h : P ≤ Q) :
    P.colocalizingClosure ≤ Q.colocalizingClosure :=
  colocalizingClosure_le (h.trans Q.le_colocalizingClosure)

end Colocalizing

end CategoryTheory.ObjectProperty
