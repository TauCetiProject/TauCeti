/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Basic

import TauCeti.Algebra.Module.Injective.AdditiveClosure
import TauCeti.LinearAlgebra.Pi.Retract

/-!
# Additive closures of modules

In `ModuleCat A`, an `A`-module `Y` lies in the additive closure `add X` of an `A`-module `X`
exactly when `Y` is a retract of a finite power `Fin n → X`, with `A`-linear maps
`s : Y → Xⁿ` and `r : Xⁿ → Y` such that `r ∘ s = id`
(`ModuleCat.additiveClosure_iff_exists_comp_eq_id_pi`). This translates the categorical notion,
defined through biproducts, into the linear-algebraic form used for modules.

In particular, if a ring `Γ` acts faithfully and `A`-linearly on a finitely generated `A`-module
`M`, every finitely generated projective and injective `Γ`-module lies in `add M`
(`ModuleCat.additiveClosure_of_projective_of_injective`).

## Main results

* `ModuleCat.additiveClosure_iff_exists_comp_eq_id_pi`: `Y ∈ add X` exactly when `Y` is a retract
  of a finite power of `X`.
* `ModuleCat.additiveClosure_of_projective_of_injective`: a finitely generated projective-injective
  `Γ`-module lies in the additive closure of a faithful finitely generated module.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti

universe v

/-- **Additive closures in `ModuleCat` through finite powers.** An `A`-module `Y` lies in the
additive closure of `X` exactly when it is a retract of a finite power `Fin n → X`. -/
theorem additiveClosure_iff_exists_comp_eq_id_pi {A : Type*} [Ring A] {X Y : ModuleCat.{v} A} :
    additiveClosure X Y ↔
      ∃ (n : ℕ) (s : Y →ₗ[A] (Fin n → X)) (r : (Fin n → X) →ₗ[A] Y), r ∘ₗ s = .id := by
  rw [additiveClosure_iff_exists_sum_comp_eq_id]
  constructor
  · rintro ⟨n, a, b, h⟩
    refine ⟨n, LinearMap.pi fun j ↦ (a j).hom, ∑ j, (b j).hom ∘ₗ LinearMap.proj j,
      LinearMap.comp_eq_id_of_sum_comp_eq_id ?_⟩
    simpa using congrArg Hom.hom h
  · rintro ⟨n, s, r, h⟩
    refine ⟨n, fun j ↦ ofHom (LinearMap.proj j ∘ₗ s),
      fun j ↦ ofHom (r ∘ₗ LinearMap.single A (fun _ ↦ X) j), hom_ext ?_⟩
    simpa [LinearMap.comp_assoc] using LinearMap.sum_comp_eq_id_of_comp_eq_id h

/-- **A finitely generated projective-injective module lies in the additive closure.** Let `Γ` act
faithfully and `A`-linearly on a finitely generated `A`-module `M`, for instance
`Γ = Module.End A M`. Then every finitely generated projective and injective `Γ`-module `P` lies in
the additive closure of `M` in `ModuleCat Γ`. -/
theorem additiveClosure_of_projective_of_injective (A : Type*) [Semiring A] {Γ : Type*} [Ring Γ]
    (M : Type v) [AddCommGroup M] [Module A M] [Module Γ M] [SMulCommClass Γ A M]
    [FaithfulSMul Γ M] [Module.Finite A M] (P : ModuleCat.{v} Γ) [Module.Finite Γ P]
    [Module.Projective Γ P] [Module.Injective Γ P] : additiveClosure (ModuleCat.of Γ M) P :=
  additiveClosure_iff_exists_comp_eq_id_pi.2
    (exists_comp_eq_id_pi_of_projective_of_injective A M P)

end ModuleCat
