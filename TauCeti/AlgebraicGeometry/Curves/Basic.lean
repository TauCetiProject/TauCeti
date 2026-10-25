/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic
public import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# Proper integral curves over a field

A curve over a field is an integral scheme that is proper and one-dimensional over that field.
Its function field is therefore an algebraic function field of one variable. The two-chart model
of any algebraic function field provides a regular proper curve with that function field. A
rational point of a curve is a point of codimension one, that is, the generic point of a prime
divisor.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A curve over a field is an integral, proper scheme of dimension one over that field. -/
class IsCurveOver (k : Type u) [Field k] [X.Over (Spec (.of k))] : Prop
    extends IsIntegral X, IsProper (X ↘ Spec (.of k)) where
  /-- The curve has dimension one. -/
  topologicalKrullDim_eq_one : topologicalKrullDim X = 1

/-- The defining properties of a curve over a field. -/
@[simp]
theorem isCurveOver_iff : X.IsCurveOver k ↔
    IsIntegral X ∧ IsProper (X ↘ Spec (.of k)) ∧ topologicalKrullDim X = 1 := by
  constructor
  · intro hX
    exact ⟨hX.toIsIntegral, hX.toIsProper, hX.topologicalKrullDim_eq_one⟩
  · rintro ⟨hI, hP, hdim⟩
    exact @IsCurveOver.mk X k _ _ hI hP hdim

/-- The function field of a curve over `k` is an algebraic function field of one variable. -/
theorem IsCurveOver.isFunctionField [X.IsCurveOver k] :
    TauCeti.IsFunctionField k X.functionField := by
  exact (TauCeti.AlgebraicGeometry.isFunctionField_functionField_iff k).2
    (IsCurveOver.topologicalKrullDim_eq_one k)

/-- Every point of a curve has coheight at most one. -/
theorem IsCurveOver.coheight_le_one [X.IsCurveOver k] (x : X) : Order.coheight x ≤ 1 := by
  exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim x).trans
    (IsCurveOver.topologicalKrullDim_eq_one k).le

variable (k X) in
/-- A curve over a field is a Noetherian scheme. -/
theorem IsCurveOver.isNoetherian [X.IsCurveOver k] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  exact {}

variable (k X) in
/-- The structure morphism of a curve satisfies the existence part of the valuative criterion. -/
theorem IsCurveOver.valuativeCriterion_existence [X.IsCurveOver k] :
    ValuativeCriterion.Existence (X ↘ Spec (.of k)) :=
  (UniversallyClosed.eq_valuativeCriterion ▸
    (inferInstance : UniversallyClosed (X ↘ Spec (.of k)))).1

variable (k X) in
/-- **The local rings of a regular proper curve are valuation rings**: for a curve `X` over `k`
whose codimension-one local rings are discrete valuation rings, the local ring at the generic point
is the function field, and every other point has codimension one. -/
theorem IsCurveOver.valuationRing_stalk [X.IsCurveOver k]
    [∀ y : TauCeti.AlgebraicGeometry.CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (y : X))] (p : X) :
    ValuationRing (X.presheaf.stalk p) :=
  TauCeti.AlgebraicGeometry.Scheme.valuationRing_stalk_of_topologicalKrullDim_le_one
    (IsCurveOver.topologicalKrullDim_eq_one k).le p

variable (k) in
/-- **A rational point of a curve has codimension one.** The image of a section of the structure
morphism of a curve over `k` is a closed point; it is not the generic point, since the curve has
dimension one, so it has coheight one. -/
theorem IsCurveOver.coheight_section_eq_one [X.IsCurveOver k] {s : Spec (.of k) ⟶ X}
    (hs : s ≫ (X ↘ Spec (.of k)) = 𝟙 _) :
    Order.coheight (s (IsLocalRing.closedPoint k)) = 1 := by
  have hX := IsCurveOver.topologicalKrullDim_eq_one (X := X) k
  rw [TauCeti.AlgebraicGeometry.Scheme.coheight_eq_one_iff_ne_genericPoint hX.le]
  intro h
  have hc := TauCeti.AlgebraicGeometry.isClosed_singleton_of_section hs
  rw [h] at hc
  -- The generic point would be closed, hence the only point, and of coheight zero.
  have hall (y : X) : y = genericPoint X := (genericPoint_specializes y).mem_closed hc rfl
  have : ⨆ y : X, (Order.coheight y : WithBot ℕ∞) ≤ 0 := iSup_le fun y ↦ by
    rw [hall y, Order.coheight_eq_zero.mpr TauCeti.AlgebraicGeometry.Scheme.isMax_genericPoint]
    rfl
  rw [← TauCeti.topologicalKrullDim_eq_iSup_coheight, hX] at this
  exact absurd this (by decide)

end AlgebraicGeometry.Scheme
