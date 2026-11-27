/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Module.Injective.AdditiveClosure

/-!
# Projective-injective modules and restriction of scalars along a ring embedding

Let a ring `Γ'` act faithfully and `A`-linearly on a finitely generated `A`-module `W`, and let
`σ : Γ →+* Γ'` be an injective ring homomorphism. Restricting scalars along `σ` makes `W` a
`Γ`-module, on which `Γ` again acts faithfully and `A`-linearly. So the additive-closure statement
`TauCeti.exists_comp_eq_id_pi_of_projective_of_injective` applies to it: every finitely generated
projective and injective `Γ`-module is a retract of a finite power of `W`, viewed as a `Γ`-module
(`RingHom.exists_comp_eq_id_pi_restrictScalars`).

In the Morita-Tachikawa correspondence this places a generator-cogenerator of one algebra, viewed
through an isomorphism of endomorphism rings, in the additive closure of another.

## Main results

* `RingHom.exists_comp_eq_id_pi_restrictScalars`: a finitely generated projective-injective module
  is a retract of a finite power of `W`, viewed as a module through a ring embedding.
-/

public section

universe u

namespace RingHom

/-- **Additive closure through a ring embedding.** Let `Γ'` act faithfully and `A`-linearly on a
finitely generated `A`-module `W`, and let `σ : Γ →+* Γ'` be an injective ring homomorphism. Then
every finitely generated projective and injective `Γ`-module `P` is a retract of a finite power of
`W`, viewed as a `Γ`-module through `σ`. -/
theorem exists_comp_eq_id_pi_restrictScalars {A : Type*} [Semiring A] {Γ Γ' : Type*} [Ring Γ]
    [Ring Γ'] (σ : Γ →+* Γ') (hσ : Function.Injective σ) (W : Type u) [AddCommGroup W]
    [Module A W] [Module Γ' W] [SMulCommClass Γ' A W] [FaithfulSMul Γ' W] [Module.Finite A W]
    (P : Type u) [AddCommGroup P] [Module Γ P] [Module.Finite Γ P] [Module.Projective Γ P]
    [Module.Injective Γ P] :
    ∃ (n : ℕ) (s : P →ₗ[Γ] (Fin n → (ModuleCat.restrictScalars σ).obj (ModuleCat.of Γ' W)))
      (r : (Fin n → (ModuleCat.restrictScalars σ).obj (ModuleCat.of Γ' W)) →ₗ[Γ] P),
      r ∘ₗ s = .id := by
  -- Restriction of scalars keeps the carrier `W` by definition, so `W`'s `A`-action carries over.
  let : Module A ((ModuleCat.restrictScalars σ).obj (ModuleCat.of Γ' W)) :=
    inferInstanceAs (Module A W)
  -- An element `y` of the restricted module is an element of `W`, again by definition.
  have : SMulCommClass Γ A ((ModuleCat.restrictScalars σ).obj (ModuleCat.of Γ' W)) :=
    ⟨fun γ a y ↦ smul_comm (σ γ) a (show W from y)⟩
  have : FaithfulSMul Γ ((ModuleCat.restrictScalars σ).obj (ModuleCat.of Γ' W)) :=
    ⟨fun h ↦ hσ (eq_of_smul_eq_smul (α := W) h)⟩
  have : Module.Finite A ((ModuleCat.restrictScalars σ).obj (ModuleCat.of Γ' W)) :=
    inferInstanceAs (Module.Finite A W)
  exact TauCeti.exists_comp_eq_id_pi_of_projective_of_injective A _ P

end RingHom
