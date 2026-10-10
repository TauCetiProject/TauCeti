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

Over an algebraic closure, a product of diagonalizable groups has the product character group.
The tensor-product comparison for scalar extension therefore proves closure of finite-type
groups of multiplicative type under products.

This supplies product closure for the ReductiveGroups roadmap Layer 4 target
"Diagonalizable groups and groups of multiplicative type".
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
  rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing] at hH hK ⊢
  obtain ⟨G, ⟨e⟩⟩ := hH
  obtain ⟨G', ⟨f⟩⟩ := hK
  exact ⟨FGCommGrpCat.of (G × G'), ⟨
    DiagonalizableGroup.productCoordinateRingIso (AlgebraicClosure k) G G' ≪≫
    FiniteTypeCommHopfAlgCat.tensorProductCongr e f ≪≫
    (FiniteTypeCommHopfAlgCat.baseChangeTensorProductIso (AlgebraicClosure k) H K).symm⟩⟩

end TauCeti.multiplicativeTypeCommHopfAlgProperty
