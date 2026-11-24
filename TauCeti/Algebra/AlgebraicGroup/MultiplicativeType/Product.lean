/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Product

/-!
# Products of groups of multiplicative type

Over an algebraic closure, a product of diagonalizable groups is diagonalizable. The
tensor-product comparison for scalar extension therefore proves closure of finite-type
groups of multiplicative type under products.
-/

public section

open CategoryTheory

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

/-- Products of finite-type groups of multiplicative type are of multiplicative type. -/
theorem tensorProduct (k : Type u) [Field k] (H K : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (hK : multiplicativeTypeCommHopfAlgProperty k K) :
    multiplicativeTypeCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
  rw [multiplicativeTypeCommHopfAlgProperty_iff] at hH hK ⊢
  exact (DiagonalizableGroup.groupLikeSpannedProperty (AlgebraicClosure k)).prop_of_iso
    (FiniteTypeCommHopfAlgCat.baseChangeTensorProductIso (AlgebraicClosure k) H K).symm
    (DiagonalizableGroup.groupLikeSpannedProperty.tensorProduct (AlgebraicClosure k) _ _ hH hK)

end TauCeti.multiplicativeTypeCommHopfAlgProperty
