/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Retract
public import TauCeti.Algebra.Module.Generator

/-!
# Generators of module categories as retracts

A generator `M` of the category of modules over `R` (`TauCeti.Module.IsGenerator`) has the regular
module as a retract of a finite power `Mⁿ` (`ModuleCat.exists_retract_pi_of_isGenerator`): finitely
many linear forms `φⱼ : M → R` and elements `mⱼ ∈ M` with `∑ φⱼ mⱼ = 1` give maps `R → Mⁿ` and
`Mⁿ → R` composing to the identity. This is the module-category counterpart of
`TauCeti/Algebra/Category/FGModuleCat/Generator.lean`.

## Main results

* `ModuleCat.exists_retract_pi_of_isGenerator`: the regular module is a retract of a finite power
  of a generator.
-/

public section

open CategoryTheory TauCeti

universe u

variable {R : Type u} [Ring R]

/-- **The regular module is a retract of a finite power of a generator.** -/
theorem ModuleCat.exists_retract_pi_of_isGenerator (M : ModuleCat.{u} R) [Module.IsGenerator R M] :
    ∃ n : ℕ, Nonempty (Retract (ModuleCat.of R R) (ModuleCat.of R (Fin n → M))) := by
  obtain ⟨n, φ, m, h⟩ := Module.isGenerator_iff_exists_sum_eq_one.1 ‹Module.IsGenerator R M›
  let i : R →ₗ[R] (Fin n → M) := LinearMap.pi fun j ↦ LinearMap.toSpanSingleton R M (m j)
  let r : (Fin n → M) →ₗ[R] R := ∑ j, φ j ∘ₗ LinearMap.proj j
  refine ⟨n, ⟨⟨ModuleCat.ofHom i, ModuleCat.ofHom r, ?_⟩⟩⟩
  ext
  simp [i, r, h]
