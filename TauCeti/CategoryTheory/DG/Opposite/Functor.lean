/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Enriched.OppositeFunctor
public import TauCeti.CategoryTheory.DG.Opposite.Basic
public import TauCeti.CategoryTheory.DG.QuasiEquivalence

/-!
# Opposite differential graded functors

The opposite of a DG functor uses its original chain map on each reversed Hom complex. Thus
its action on homogeneous morphisms is unchanged after reversing sources and targets, and it
preserves quasi-full faithfulness. This is the functorial counterpart of the Koszul-signed
opposite DG category.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
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
theorem op_dgMap {X Y : Cᵒᵖ} (n : ℤ) (f : DGHom R n Y.unop X.unop) :
    F.op.dgMap n (X := X) (Y := Y) f = F.dgMap n f := by
  simp only [dgMap_apply, op_map]
  -- Opposite Hom complexes are definitionally the original complexes with endpoints reversed.
  rfl

/-- A DG functor is quasi-fully faithful exactly when its opposite is: the Hom chain maps are
the same maps with source and target reversed. -/
@[simp]
theorem isQuasiFullyFaithful_op_iff : F.op.IsQuasiFullyFaithful ↔ F.IsQuasiFullyFaithful := by
  constructor
  · intro hF
    apply (isQuasiFullyFaithful_iff_isIso_homologyMap F).2
    intro X Y n
    have h := hF.isIso_homologyMap (Opposite.op Y) (Opposite.op X) n
    -- `op_map` rewrites the map but does not normalize the Hom-complex types in `IsIso`.
    change IsIso (HomologicalComplex.homologyMap (F.map X Y) n) at h
    exact h
  · intro hF
    apply (isQuasiFullyFaithful_iff_isIso_homologyMap F.op).2
    intro X Y n
    cases X with
    | op X =>
      cases Y with
      | op Y =>
        -- `op_map` rewrites the map but does not normalize the opposite Hom-complex types.
        change IsIso (HomologicalComplex.homologyMap (F.map Y X) n)
        exact hF.isIso_homologyMap Y X n

/-- A quasi-fully faithful DG functor remains quasi-fully faithful on opposite DG categories. -/
theorem IsQuasiFullyFaithful.op (hF : F.IsQuasiFullyFaithful) :
    F.op.IsQuasiFullyFaithful := (isQuasiFullyFaithful_op_iff F).2 hF

end CategoryTheory.EnrichedFunctor
