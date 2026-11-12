/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# Subgroups of Galois groups

For a tower of fields `E ⊆ F ⊆ K` in which `K` is Galois over `E` with Galois group `G` and
Galois over `F` with Galois group a subgroup `H` of `G`, the index of `H` in `G` is the degree
`[F : E]`. This is the counting half of the Galois correspondence, in the `IsGaloisGroup` form:
Mathlib's `IsGaloisGroup.card_eq_finrank` gives `Nat.card H = [K : F]` and
`Nat.card G = [K : E]`, and the tower law cancels `[K : F]`.

For any extension `M / K`, every subgroup `H` of `Gal(M/K)` is a Galois group of `M` over
its fixed field `M ^ H`. Mathlib's `IsGaloisGroup.subgroup` records this for the fixed points of a
subgroup of an abstract Galois group; the instance here is the `IntermediateField.fixedField`
form, which Mathlib's ring-of-integers instance then lifts to `𝓞 (M ^ H) ⊆ 𝓞 M`.

## Main results

* `IsGaloisGroup.index_eq_finrank`: `H.index = Module.finrank E F`.
* `IsGaloisGroup.fixedField`: `H` is a Galois group of `M` over `IntermediateField.fixedField H`.

## Provenance

Built directly on Mathlib's `IsGaloisGroup.card_eq_finrank` and `Module.finrank_mul_finrank`,
and on the faithful subgroup action and the definition of `IntermediateField.fixedField`.
-/

public section

namespace IsGaloisGroup

/-- **The index of a subgroup is the degree of its fixed field.** If `K` is Galois over `E` with
Galois group `G` and `H` is a subgroup of `G` whose fixed field is `F`, then `H.index = [F : E]`.
This is `IsGaloisGroup.card_eq_finrank` at the two ends of the tower `E ⊆ F ⊆ K`, combined with
the tower law for degrees. -/
theorem index_eq_finrank {G : Type*} [Group G] (H : Subgroup G) (E F K : Type*) [Field E]
    [Field F] [Field K] [Algebra E F] [Algebra F K] [Algebra E K] [IsScalarTower E F K]
    [FiniteDimensional F K] [MulSemiringAction G K] [IsGaloisGroup G E K] [IsGaloisGroup H F K] :
    H.index = Module.finrank E F := by
  have h : H.index * Nat.card H = Nat.card G := Subgroup.index_mul_card H
  rw [card_eq_finrank H F K, card_eq_finrank G E K, ← Module.finrank_mul_finrank E F K] at h
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h

/-- **A subgroup is the Galois group over its fixed field.** For any extension `M / K` and a
subgroup `H` of `Gal(M/K)`, the action of `H` on `M` makes it a Galois group of `M / M ^ H`. -/
instance fixedField {K M : Type*} [Field K] [Field M] [Algebra K M]
    (H : Subgroup (M ≃ₐ[K] M)) : IsGaloisGroup H ↥(IntermediateField.fixedField H) M where
  faithful := inferInstance
  commutes := ⟨fun g a b ↦ by
    -- The subgroup action evaluates the underlying automorphism, and fixed-field scalar
    -- multiplication is multiplication by the coerced field element. `change` exposes these
    -- definitions so `map_mul` and fixed-field membership apply to the resulting equality.
    change g.1 (a.1 * b) = a.1 * g.1 b
    rw [map_mul, (IntermediateField.mem_fixedField_iff H a.1).1 a.2 g g.2]⟩
  isInvariant := ⟨fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

end IsGaloisGroup
