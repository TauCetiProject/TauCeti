/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Operations
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Lifting homomorphisms through injections and surjections

A multiplicative or additive homomorphism lifts through an injective homomorphism if and only if
its values lie in the range of that homomorphism, and the lift is then unique. This gives
coefficient descent whenever the coefficient map is injective and the values of a character
already lie in its image.

Dually, a homomorphism out of a group factors through a surjective group homomorphism if and only
if it kills the kernel of that surjection, and the factorization is then unique. The target only
needs to be a monoid: a homomorphism out of a group lands in the units. Moreover,
`MonoidHom.liftOfSurjectiveToMonoid` constructs this descended homomorphism explicitly together
with its `_apply`, `_comp`, `_unique`, kernel, and injectivity laws (and additive counterparts
under `AddMonoidHom`).
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

section LiftOfSurjectiveToMonoid

variable {P Q M' : Type*} [Group P] [Group Q] [Monoid M']
  (p : P →* Q) (hp : Function.Surjective p) (ψ : P →* M') (hψ : p.ker ≤ ψ.ker)

/-- Descend a monoid-valued homomorphism along a surjective group homomorphism whose kernel is
contained in `ψ.ker`. Unlike `MonoidHom.liftOfSurjective`, the target `M'` need only be a
monoid. -/
@[to_additive
  /-- Descend an additive-monoid-valued homomorphism along a surjective additive group
  homomorphism whose kernel is contained in `ψ.ker`. -/]
noncomputable def liftOfSurjectiveToMonoid : Q →* M' :=
  (QuotientGroup.lift p.ker ψ hψ).comp
    (QuotientGroup.quotientKerEquivOfSurjective p hp).symm.toMonoidHom

/-- The descended homomorphism agrees with `ψ` after precomposing with `p`. -/
@[to_additive (attr := simp)
  /-- The descended additive homomorphism agrees with `ψ` after precomposing with `p`. -/]
theorem liftOfSurjectiveToMonoid_apply (g : P) :
    liftOfSurjectiveToMonoid p hp ψ hψ (p g) = ψ g := by
  dsimp only [liftOfSurjectiveToMonoid]
  rw [comp_apply, MulEquiv.coe_toMonoidHom,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_symm_apply, QuotientGroup.lift_mk]

/-- Precomposing the descended homomorphism with `p` recovers `ψ`. -/
@[to_additive (attr := simp)
  /-- Precomposing the descended additive homomorphism with `p` recovers `ψ`. -/]
theorem liftOfSurjectiveToMonoid_comp :
    (liftOfSurjectiveToMonoid p hp ψ hψ).comp p = ψ :=
  MonoidHom.ext (liftOfSurjectiveToMonoid_apply p hp ψ hψ)

/-- A homomorphism out of the target of a surjection is uniquely determined by its precomposition
with `p`. -/
@[to_additive
  /-- An additive homomorphism out of the target of a surjection is uniquely determined by its
  precomposition with `p`. -/]
theorem liftOfSurjectiveToMonoid_unique (χ : Q →* M') (hχ : ∀ g, χ (p g) = ψ g) :
    χ = liftOfSurjectiveToMonoid p hp ψ hψ :=
  (cancel_right hp).mp ((MonoidHom.ext hχ).trans (liftOfSurjectiveToMonoid_comp p hp ψ hψ).symm)

/-- The kernel of the descended homomorphism is the image of `ψ.ker` under `p`. -/
@[to_additive
  /-- The kernel of the descended additive homomorphism is the image of `ψ.ker` under `p`. -/]
theorem ker_liftOfSurjectiveToMonoid :
    (liftOfSurjectiveToMonoid p hp ψ hψ).ker = ψ.ker.map p :=
  ker_eq_map_of_comp_eq hp (liftOfSurjectiveToMonoid_comp p hp ψ hψ)

/-- The descended homomorphism is injective if and only if `ψ.ker = p.ker`. -/
@[to_additive
  /-- The descended additive homomorphism is injective if and only if `ψ.ker = p.ker`. -/]
theorem injective_liftOfSurjectiveToMonoid_iff :
    Function.Injective (liftOfSurjectiveToMonoid p hp ψ hψ) ↔ ψ.ker = p.ker := by
  rw [liftOfSurjectiveToMonoid, coe_comp, MulEquiv.coe_toMonoidHom,
    EquivLike.injective_comp, QuotientGroup.injective_lift_iff, eq_comm]

end LiftOfSurjectiveToMonoid

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
  exact ⟨liftOfSurjectiveToMonoid f hf χ hχ, liftOfSurjectiveToMonoid_comp f hf χ hχ,
    fun ψ hψ => liftOfSurjectiveToMonoid_unique f hf χ hχ ψ fun g => by
      rw [← hψ, comp_apply]⟩

end MonoidHom
