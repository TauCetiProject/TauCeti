/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Powers and preimages under monoid homomorphisms

Powers of an element lie in the preimage of the powers of its image under a monoid
homomorphism. For an injective homomorphism, these submonoids are equal. The additive
counterparts describe natural multiples and preimages under additive monoid homomorphisms.
-/

public section

namespace Submonoid

variable {M N F : Type*} [Monoid M] [Monoid N] [FunLike F M N] [MonoidHomClass F M N]

/-- Powers of an element map into the powers of its image under a monoid homomorphism. -/
@[to_additive
  /-- Natural multiples of an element map into the natural multiples of its image under an
  additive monoid homomorphism. -/]
theorem powers_le_comap_powers (f : F) (m : M) : powers m ≤ (powers (f m)).comap f :=
  powers_le.mpr (mem_comap.mpr (mem_powers (f m)))

/-- The preimage of the powers of an image under an injective monoid homomorphism is the
submonoid of powers of the original element. -/
@[to_additive
  /-- The preimage of the natural multiples of an image under an injective additive monoid
  homomorphism is the additive submonoid of natural multiples of the original element. -/]
theorem comap_powers_of_injective (f : F) (hf : Function.Injective f) (m : M) :
    (powers (f m)).comap f = powers m := by
  refine le_antisymm ?_ (powers_le_comap_powers f m)
  rintro x ⟨n, hn⟩
  exact ⟨n, hf ((map_pow f m n).trans hn)⟩

end Submonoid
