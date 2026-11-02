/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.RingTheory.Algebraic.Basic

/-!
# Algebraic extensions of the constant field

Adjoining an arbitrary algebraic extension of constants to a function field produces an
algebraic extension of it, and a function field over the enlarged constants, even when the
extension is infinite.  An element of `F` transcendental over `k` stays transcendental over `k'`
in `F'`.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- The compositum with an algebraic algebra of constants is algebraic over the original field.
The constants need only form a commutative ring, and their map into the ambient field need not
be injective. -/
theorem isAlgebraic_constantCompositum
    {k' : Type u'} [CommRing k'] [Algebra k k'] [Algebra k' F']
    [IsScalarTower k k' F'] [Algebra.IsAlgebraic k k'] :
    Algebra.IsAlgebraic F (constantCompositum F k' F') := by
  rw [constantCompositum_def]
  apply IntermediateField.isAlgebraic_adjoin
  rintro x ⟨c, rfl⟩
  exact (IsIntegral.algebraMap
    ((Algebra.IsAlgebraic.isAlgebraic (R := k) c).isIntegral)).tower_top

/-- If `F'` is the compositum of `F` with an algebraic algebra of constants, then `F'` is
algebraic over `F`. -/
theorem isAlgebraic_of_constantCompositum_eq_top
    {k' : Type u'} [CommRing k'] [Algebra k k'] [Algebra k' F']
    [IsScalarTower k k' F'] [Algebra.IsAlgebraic k k'] (h : constantCompositum F k' F' = ⊤) :
    Algebra.IsAlgebraic F F' := by
  have halg := isAlgebraic_constantCompositum (k := k) (k' := k') (F := F) (F' := F')
  rw [h] at halg
  exact IntermediateField.topEquiv.isAlgebraic_iff.mp halg

/-- The compositum is finitely generated over the new constants. A finite field-generating
set for `F / k` also generates `F' / k'`, since the two fields generate the compositum. -/
theorem essFiniteType_of_constantCompositum_eq_top [Algebra.EssFiniteType k F]
    (h : constantCompositum F k' F' = ⊤) : Algebra.EssFiniteType k' F' := by
  obtain ⟨S, hS⟩ := IntermediateField.fg_top k F
  apply IntermediateField.fg_top_iff.mp
  rw [← adjoin_image_eq_top_of_constantCompositum_eq_top hS h]
  exact IntermediateField.fg_adjoin_of_finite (S.finite_toSet.image _)

/-- Adjoining an arbitrary algebraic extension of constants to a function field gives a
function field over the enlarged constants, provided the ambient field is their compositum.
No finite-degree or separability assumption on the constants is needed. -/
theorem IsFunctionField.of_constantCompositum_eq_top
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) : IsFunctionField k' F' := by
  let : Algebra.EssFiniteType k F := hF.essFiniteType
  let : Algebra.EssFiniteType k' F' := essFiniteType_of_constantCompositum_eq_top (k := k) h
  rw [isFunctionField_iff_trdeg_eq_one]
  have := isAlgebraic_of_constantCompositum_eq_top (k := k) h
  rw [trdeg_eq_of_isAlgebraic_base (R := k)]
  exact hF.trdeg_eq_one_of_isAlgebraic

end TauCeti
