/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Enriched.OppositeFunctor
public import TauCeti.CategoryTheory.DG.Opposite
public import TauCeti.CategoryTheory.DG.QuasiEquivalence

/-!
# Opposite differential graded functors

The opposite of a DG functor uses its original chain map on each reversed Hom complex. Thus
its action on homogeneous morphisms is unchanged after reversing sources and targets, and it
preserves quasi-full faithfulness. This is the functorial counterpart of the Koszul-signed
opposite DG category.

## References

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

namespace CategoryTheory.EnrichedFunctor

open Opposite TauCeti

universe v u₁ u₂

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂}
  [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- The opposite DG functor acts on a homogeneous morphism by the original functor's
degreewise map, with its source and target reversed. -/
@[simp]
theorem dgMap_op {X Y : C} (n : ℤ) (f : DGHom R n Y X) :
    F.op.dgMap n (X := Opposite.op X) (Y := Opposite.op Y) f = F.dgMap n f := by
  simp only [dgMap_apply, op_map]
  rfl

/-- A quasi-fully faithful DG functor remains quasi-fully faithful on opposite DG categories:
the Hom chain maps are literally the same maps with source and target reversed. -/
theorem IsQuasiFullyFaithful.op (hF : F.IsQuasiFullyFaithful) :
    F.op.IsQuasiFullyFaithful := by
  apply (isQuasiFullyFaithful_iff_isIso_homologyMap F.op).2
  intro X Y n
  cases X with
  | op X =>
    cases Y with
    | op Y =>
      -- Opposite Hom complexes are the original Hom complexes with their endpoints reversed.
      change IsIso (HomologicalComplex.homologyMap (F.map Y X) n)
      exact hF.isIso_homologyMap Y X n

end CategoryTheory.EnrichedFunctor
