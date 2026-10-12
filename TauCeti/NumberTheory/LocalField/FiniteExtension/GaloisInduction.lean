/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.GroupTheory.Solvable
import TauCeti.NumberTheory.LocalField.Solvable

/-!
# Degree induction for finite Galois extensions of local fields

A nontrivial finite Galois extension of local fields has an intermediate field of prime
Galois degree over the base and smaller remaining degree. A shared induction on that remaining
degree lets norm statements supply their own prime-degree case and tower transitivity.
-/

public section

open Module

universe u v

namespace TauCeti

/-- A nontrivial finite Galois extension of local fields has a prime-degree Galois first step
and a strictly smaller remaining degree. The intermediate field carries the canonical local
field structures from `FiniteExtension.IntermediateField`. -/
theorem exists_prime_degree_intermediateField (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L]
    [Nontrivial (L ≃ₐ[K] L)] :
    ∃ F : IntermediateField K L, IsGalois K F ∧ (finrank K F).Prime ∧
      finrank F L < finrank K L := by
  obtain ⟨H, hH, hp⟩ := Group.IsSolvable.exists_normal_index_prime (L ≃ₐ[K] L)
  let F := IntermediateField.fixedField H
  have hF : finrank K F = H.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField]
  refine ⟨F, inferInstance, hF ▸ hp, ?_⟩
  rw [← Module.finrank_mul_finrank K F L, hF]
  have := hp.two_le
  have := Module.finrank_pos (R := F) (M := L)
  nlinarith

/-- Induction on the finite degree of a Galois local-field extension, keeping the top field
fixed. The step may use the property over every base with smaller remaining degree. -/
theorem finiteGaloisLocalField_induction_finrank_le (L : Type v)
    [Field L] [ValuativeRel L]
    (P : ∀ (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
      [IsGalois F L], Prop)
    (step : ∀ (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
      [IsGalois F L],
      (∀ (F' : Type v) [Field F'] [ValuativeRel F'] [TopologicalSpace F']
        [IsNonarchimedeanLocalField F'] [Algebra F' L] [ValuativeExtension F' L]
        [Module.Finite F' L] [IsGalois F' L], finrank F' L < finrank F L → P F') → P F)
    (d : ℕ) :
    ∀ (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
      [IsGalois F L], finrank F L ≤ d → P F := by
  induction d with
  | zero =>
    intro F _ _ _ _ _ _ _ _ h
    exact absurd h (Nat.not_le.2 Module.finrank_pos)
  | succ d ih =>
    intro F _ _ _ _ _ _ _ _ h
    exact step F fun F' _ _ _ _ _ _ _ _ h' ↦ ih F' (by omega)

end TauCeti
