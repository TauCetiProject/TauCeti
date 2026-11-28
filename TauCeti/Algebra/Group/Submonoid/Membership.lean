/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Membership
import TauCeti.Data.Set.Prod

/-!
# Powers and preimages under monoid homomorphisms

Powers of an element lie in the preimage of the powers of its image under a monoid
homomorphism. For an injective homomorphism, these submonoids are equal. The additive
counterparts describe natural multiples and preimages under additive monoid homomorphisms.
-/

public section

namespace Submonoid

/-- A point of the graph image is determined by its second coordinate in the source monoid. -/
@[to_additive AddSubmonoid.mem_map_prod_id_iff]
theorem mem_map_prod_id_iff {N M : Type*} [Monoid N] [Monoid M]
    (s : Submonoid N) (f : N →* M) (x : M × N) :
    x ∈ s.map (f.prod (MonoidHom.id N)) ↔ x.2 ∈ s ∧ x.1 = f x.2 := by
  have hf : ⇑(f.prod (MonoidHom.id N)) = fun n => (f n, n) := by
    funext n
    simp only [MonoidHom.prod_apply, MonoidHom.id_apply]
  rw [← SetLike.mem_coe, Submonoid.coe_map, hf]
  simpa only [SetLike.mem_coe] using Set.mem_image_prodMk_self_snd_iff f (s : Set N) x

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
