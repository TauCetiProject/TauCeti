/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Submodule

/-!
# Submodules of a Lie submodule

Inclusion identifies the Lie submodules of `N` with the interval of ambient Lie submodules
contained in `N`. This transports lattice properties, such as complete reducibility, between
the two descriptions.

## References

The interval order isomorphism adapts Mathlib's `Submodule.MapSubtype.orderIso` and
`Submodule.mapIic` from `Mathlib.Algebra.Module.Submodule.Range` to Lie submodules.
-/

public section

namespace LieSubmodule

variable {R L M : Type*} [CommRing R] [LieRing L]
  [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- Inclusion identifies the submodules of a Lie submodule with the ambient submodules
contained in it. -/
def mapInclOrderIso (N : LieSubmodule R L M) :
    LieSubmodule R L N ≃o Set.Iic N where
  toFun P := ⟨P.map N.incl, by rintro _ ⟨x, _, rfl⟩; exact x.property⟩
  invFun P := P.val.comap N.incl
  left_inv P := by
    ext x
    simp only [mem_comap, mem_map, incl_apply, Subtype.coe_inj, exists_eq_right]
  right_inv P := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, P.property hx⟩, hx, rfl⟩
  map_rel_iff' := map_le_map_iff Subtype.val_injective

/-- The ambient submodule corresponding to a submodule of `N` is its image under inclusion. -/
@[simp]
theorem mapInclOrderIso_apply (N : LieSubmodule R L M) (P : LieSubmodule R L N) :
    (N.mapInclOrderIso P).val = P.map N.incl := (rfl)

/-- The submodule of `N` corresponding to an ambient submodule is its inverse image.

This is not a simp lemma: unfolding the inverse prevents simplification by the order
isomorphism's round-trip laws. -/
theorem mapInclOrderIso_symm_apply (N : LieSubmodule R L M) (P : Set.Iic N) :
    N.mapInclOrderIso.symm P = P.val.comap N.incl := (rfl)

end LieSubmodule
