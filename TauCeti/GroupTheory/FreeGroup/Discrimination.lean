/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Defs
public import TauCeti.GroupTheory.FreeGroup.ConjugateBasis
import Mathlib.Basic.Countable.Defs
import TauCeti.GroupTheory.FreeGroup.Basic

/-!
# Free groups are discriminated by the free group of rank two

Every finite family of nonidentity elements of a free group `FreeGroup ι`, of arbitrary rank,
survives simultaneously under a single homomorphism to `FreeGroup (Fin 2)`.

The finitely many elements lie in a free factor `FreeGroup β` of countable rank, and a retraction
of `FreeGroup ι` onto `FreeGroup β` fixes them (`FreeGroup.exists_countable_retraction`), so it
keeps them nontrivial. Then `FreeGroup β` embeds in `FreeGroup (Fin 2)` by
`FreeGroup.injective_lift_conj_zpow_of_ne`.

This shows that the choice of free target in the definitions of residually free and fully
residually free groups is immaterial: the free group of rank two always suffices.

## Main results

* `FreeGroup.exists_monoidHom_fin_two_forall_ne_one`: finitely many nonidentity elements of a free
  group survive under one homomorphism to `FreeGroup (Fin 2)`.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), §2.3.
-/

public section

namespace FreeGroup

variable {ι : Type*}

/-- **Free groups are discriminated by `F₂`.** Finitely many nonidentity elements of a free group
of arbitrary rank survive simultaneously under one homomorphism to the free group of rank two. -/
theorem exists_monoidHom_fin_two_forall_ne_one (s : Finset (FreeGroup ι))
    (hs : ∀ x ∈ s, x ≠ 1) :
    ∃ φ : FreeGroup ι →* FreeGroup (Fin 2), ∀ x ∈ s, φ x ≠ 1 := by
  -- The elements of `s` survive the retraction `r` onto a free factor `FreeGroup β` of countable
  -- rank, which embeds in `FreeGroup (Fin 2)`.
  obtain ⟨β, hβ, r, -, hr⟩ := exists_countable_retraction ((↑) : s → FreeGroup ι)
  have := hβ.to_subtype
  obtain ⟨k, hk⟩ := Countable.exists_injective_nat β
  refine ⟨(lift fun i : β => of (1 : Fin 2) ^ (k i : ℤ) * of 0 * (of 1 ^ (k i : ℤ))⁻¹).comp r,
    fun x hx hφ => hs x hx ?_⟩
  have hrx : r x = 1 := (map_eq_one_iff _
    (injective_lift_conj_zpow_of_ne Fin.zero_ne_one (Nat.cast_injective.comp hk))).1 hφ
  have hx' : map ((↑) : β → ι) (r x) = x := hr ⟨x, hx⟩
  rw [← hx', hrx, _root_.map_one]

end FreeGroup
