/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.NumberTheory.LocalField.RamificationGroup

/-!
# Lower ramification groups on finite Galois intermediate fields

Finite Galois subextensions of an algebraic closure are the finite levels used to define wild
inertia and the tame quotient of the absolute Galois group. This file equips such an intermediate
field with the local-field structures constructed from the base field, then reads its lower
ramification groups through the canonical local-field filtration. Each finite-level group
`G_i(L/K)` is normal in `Gal(L/K)`.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The `i`-th lower ramification group of a finite Galois intermediate field of the algebraic
closure, with the local-field structure induced from `K`. -/
def finiteGaloisLowerRamificationGroup
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (i : ℤ) :
    Subgroup (L ≃ₐ[K] L) := by
  letI := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L.toIntermediateField
  letI := finiteIntermediateFieldTopology K (AlgebraicClosure K) L.toIntermediateField
  haveI := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K)
    L.toIntermediateField
  haveI := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    L.toIntermediateField
  exact lowerRamificationGroup K L i

/-- The finite-level adapter is the canonical lower ramification group on the induced local-field
structure. -/
theorem finiteGaloisLowerRamificationGroup_def
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (i : ℤ) :
    by
  letI := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L.toIntermediateField
  letI := finiteIntermediateFieldTopology K (AlgebraicClosure K) L.toIntermediateField
  haveI := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K)
    L.toIntermediateField
  haveI := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    L.toIntermediateField
  exact finiteGaloisLowerRamificationGroup K L i = lowerRamificationGroup K L i := by
  rfl

/-- Membership in the finite-level adapter is membership in the canonical lower ramification
group for the induced local-field structure. -/
@[simp]
theorem mem_finiteGaloisLowerRamificationGroup_iff
    {L : FiniteGaloisIntermediateField K (AlgebraicClosure K)} {i : ℤ}
    {σ : L ≃ₐ[K] L} :
    by
  letI := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L.toIntermediateField
  letI := finiteIntermediateFieldTopology K (AlgebraicClosure K) L.toIntermediateField
  haveI := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K)
    L.toIntermediateField
  haveI := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    L.toIntermediateField
  exact σ ∈ finiteGaloisLowerRamificationGroup K L i ↔
    σ ∈ lowerRamificationGroup K L i := by
  rw [finiteGaloisLowerRamificationGroup_def]

/-- Every finite-level lower ramification group `G_i(L/K)` is normal in `Gal(L/K)`. -/
instance instNormalFiniteGaloisLowerRamificationGroup
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (i : ℤ) :
    (finiteGaloisLowerRamificationGroup K L i).Normal := by
  let := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L.toIntermediateField
  let := finiteIntermediateFieldTopology K (AlgebraicClosure K) L.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K)
    L.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    L.toIntermediateField
  rw [finiteGaloisLowerRamificationGroup_def]
  infer_instance

end TauCeti.LocalFieldsRamification
