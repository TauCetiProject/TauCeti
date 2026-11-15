/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Set.Operations

/-!
# Lifting homomorphisms through injections

A multiplicative or additive homomorphism lifts through an injective homomorphism if and only if
its values lie in the range of that homomorphism, and the lift is then unique. This gives
coefficient descent whenever the coefficient map is injective and the values of a character
already lie in its image.
-/

public section

namespace MonoidHom

variable {M N P : Type*} [MulOne M] [MulOne N] [MulOne P]

/-- A homomorphism lifts uniquely through an injective homomorphism if and only if its values lie
in the range of that homomorphism. -/
@[to_additive /-- An additive homomorphism lifts uniquely through an injective additive
homomorphism if and only if its values lie in the range of that homomorphism. -/]
theorem existsUnique_comp_eq_iff_of_injective (χ : M →* P) (f : N →* P)
    (hf : Function.Injective f) :
    (∃! ψ : M →* N, f.comp ψ = χ) ↔ ∀ g, χ g ∈ Set.range f := by
  refine ⟨fun ⟨ψ, hψ, _⟩ g => ⟨ψ g, by rw [← hψ, comp_apply]⟩, fun hχ => ?_⟩
  let ψ : M → N := fun g => (hχ g).choose
  have hψ g : f (ψ g) = χ g := (hχ g).choose_spec
  let ψ' : M →* N :=
    { toFun := ψ
      map_one' := hf (by simp [hψ])
      map_mul' := fun _ _ => hf (by simp [hψ]) }
  have hψ' : f.comp ψ' = χ := MonoidHom.ext hψ
  exact ⟨ψ', hψ', fun _ h => (MonoidHom.cancel_left hf).mp (h.trans hψ'.symm)⟩

end MonoidHom
