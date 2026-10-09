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

A homomorphism whose values lie in the range of an injective homomorphism lifts uniquely
through it. This gives coefficient descent whenever the coefficient map is injective and
the values of a character already lie in its image.
-/

public section

namespace MonoidHom

variable {M N P : Type*} [MulOne M] [MulOne N] [MulOne P]

/-- A homomorphism lifts uniquely through an injective homomorphism if its values lie in the
range of that homomorphism. -/
theorem existsUnique_comp_eq_of_injective (χ : M →* P) (f : N →* P)
    (hf : Function.Injective f) (hχ : ∀ g, χ g ∈ Set.range f) :
    ∃! ψ : M →* N, f.comp ψ = χ := by
  let ψ : M → N := fun g => Classical.choose (hχ g)
  have hψ : ∀ g, f (ψ g) = χ g := fun g => Classical.choose_spec (hχ g)
  let ψ' : M →* N :=
    { toFun := ψ
      map_one' := hf (by simp [hψ])
      map_mul' := fun g h => hf (by simp [hψ]) }
  have hψ' : f.comp ψ' = χ := MonoidHom.ext hψ
  exact ⟨ψ', hψ', fun ψ'' hψ'' => (MonoidHom.cancel_left hf).mp (hψ''.trans hψ'.symm)⟩

end MonoidHom
