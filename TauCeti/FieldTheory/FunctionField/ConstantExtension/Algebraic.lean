/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic

/-!
# Algebraic extensions of the constant field

The compositum of a function field with algebraic constants is again a function field over
the enlarged constant field, even when the extension of constants is infinite. The proof
separates algebraicity, transcendence degree, and finite generation over the new constants.

The field-theoretic setting follows Stichtenoth, *Algebraic Function Fields and Codes*,
second edition, Section III.6.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- The compositum with algebraic constants is algebraic over the original field, even for an
infinite extension of constants. -/
theorem isAlgebraic_of_constantCompositum_eq_top [Algebra.IsAlgebraic k k']
    (h : constantCompositum F k' F' = ⊤) : Algebra.IsAlgebraic F F' := by
  have h' : Algebra.IsAlgebraic F (constantCompositum F k' F') := by
    rw [constantCompositum_def]
    apply IntermediateField.isAlgebraic_adjoin
    rintro x ⟨c, rfl⟩
    exact (IsIntegral.algebraMap
      ((Algebra.IsAlgebraic.isAlgebraic (R := k) c).isIntegral)).tower_top
  rw [h] at h'
  exact IntermediateField.topEquiv.isAlgebraic_iff.mp h'

/-- Adjoining algebraic constants preserves transcendence degree one. In particular, no new
transcendental parameter appears in the compositum. -/
theorem trdeg_constantCompositum_eq_one [Algebra.IsAlgebraic k k']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) :
    Algebra.trdeg k' F' = 1 := by
  let : Algebra.IsAlgebraic F F' := isAlgebraic_of_constantCompositum_eq_top (k := k) h
  have htr : Algebra.trdeg k F' = 1 := hF.trdeg_eq_one_of_isAlgebraic
  have htower := lift_trdeg_add_eq k k' F'
  rw [trdeg_eq_zero_iff.mpr (inferInstance : Algebra.IsAlgebraic k k'),
    Cardinal.lift_zero, zero_add, htr, Cardinal.lift_one] at htower
  simpa using htower

/-- The compositum is finitely generated over the new constants. A finite field-generating
set for `F / k` also generates `F' / k'`, since the two fields generate the compositum. -/
theorem essFiniteType_of_constantCompositum_eq_top [Algebra.EssFiniteType k F]
    (h : constantCompositum F k' F' = ⊤) : Algebra.EssFiniteType k' F' := by
  classical
  obtain ⟨S, hS⟩ := IntermediateField.fg_top k F
  let T : Set F' := (algebraMap F F') '' (S : Set F)
  let K : IntermediateField k' F' := IntermediateField.adjoin k' T
  have hmap : (IsScalarTower.toAlgHom k F F').fieldRange ≤ K.restrictScalars k := by
    rw [AlgHom.fieldRange_eq_map, ← hS, IntermediateField.adjoin_map]
    exact IntermediateField.adjoin_le_iff.mpr (fun x hx ↦
      IntermediateField.subset_adjoin k' T hx)
  have hle : (constantCompositum F k' F' : Set F') ⊆ (K : Set F') := by
    rw [constantCompositum_def]
    refine (IntermediateField.adjoin_subset_adjoin_iff F).2 ?_
    constructor
    · rintro x ⟨f, rfl⟩
      exact hmap ⟨f, rfl⟩
    · rintro x ⟨c, rfl⟩
      exact K.algebraMap_mem c
  have hK : K = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact hle (by simp [h])
  have hT : T.Finite := S.finite_toSet.image _
  have hfg : (⊤ : IntermediateField k' F').FG := by
    rw [← hK]
    exact IntermediateField.fg_adjoin_of_finite hT
  exact IntermediateField.fg_top_iff.mp hfg

/-- Adjoining an arbitrary algebraic extension of constants to a function field gives a
function field over the enlarged constants, provided the ambient field is their compositum.
No finite-degree or separability assumption on the constants is needed. -/
theorem IsFunctionField.of_constantCompositum_eq_top
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) : IsFunctionField k' F' := by
  let : Algebra.EssFiniteType k F := hF.essFiniteType
  let : Algebra.EssFiniteType k' F' := essFiniteType_of_constantCompositum_eq_top (k := k) h
  rw [isFunctionField_iff_trdeg_eq_one]
  exact trdeg_constantCompositum_eq_one hF h

end TauCeti
