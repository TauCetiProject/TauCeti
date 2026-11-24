/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Operations

/-!
# Lifting homomorphisms through injections and surjections

A multiplicative or additive homomorphism lifts through an injective homomorphism if and only if
its values lie in the range of that homomorphism, and the lift is then unique. This gives
coefficient descent whenever the coefficient map is injective and the values of a character
already lie in its image.

Dually, a homomorphism out of a group factors through a surjective group homomorphism if and only
if it kills the kernel of that surjection, and the factorization is then unique. The target only
needs to be a monoid: a homomorphism out of a group lands in the units.
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

/-- A homomorphism out of a group factors uniquely through a surjective group homomorphism if and
only if it kills the kernel of that surjection. The target may be any monoid. -/
@[to_additive /-- An additive homomorphism out of an additive group factors uniquely through a
surjective additive group homomorphism if and only if it kills the kernel of that surjection. The
target may be any additive monoid. -/]
theorem existsUnique_comp_eq_iff_ker_le {G H M : Type*} [Group G] [Group H] [Monoid M]
    (χ : G →* M) (f : G →* H) (hf : Function.Surjective f) :
    (∃! ψ : H →* M, ψ.comp f = χ) ↔ f.ker ≤ χ.ker := by
  refine ⟨fun ⟨ψ, hψ, _⟩ g hg => by
    rw [mem_ker, ← hψ, comp_apply, (mem_ker).mp hg, map_one], fun hχ => ?_⟩
  -- `χ` lands in the units of `M`, where `f` lifts through any homomorphism killing its kernel.
  have hker : f.ker ≤ χ.toHomUnits.ker := fun g hg => by
    simpa [mem_ker, Units.ext_iff] using hχ hg
  have hcomp : ((Units.coeHom M).comp (f.liftOfSurjective hf ⟨χ.toHomUnits, hker⟩)).comp f = χ := by
    ext g
    simp
  exact ⟨_, hcomp, fun ψ hψ => (cancel_right hf).mp (hψ.trans hcomp.symm)⟩

end MonoidHom
