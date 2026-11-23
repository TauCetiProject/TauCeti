/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Set.Finite.Basic

/-!
# Multiplicative maps applied entrywise and homomorphism extensionality

A multiplicative map applied entrywise to a scalar multiple `c • v` of a family gives
`f c • (f ∘ v)`. This is the scalar companion of Mathlib's `map_comp_mul` and `map_comp_pow`.

Composing a monoid homomorphism with an injective one does not change whether it is trivial.
This is the triviality companion of Mathlib's `MonoidHom.cancel_left`.

Two homomorphisms from an infinite group into a cancellative monoid that disagree on only
finitely many elements are equal (`MonoidHom.eq_of_finite_setOf_ne` and
`AddMonoidHom.eq_of_finite_setOf_ne`).

## Main results

* `TauCeti.map_comp_smul`: `f ∘ (c • v) = f c • (f ∘ v)`.
* `MonoidHom.comp_eq_one_iff`: for injective `g`, `g.comp f = 1 ↔ f = 1`.
* `MonoidHom.eq_of_finite_setOf_ne` / `AddMonoidHom.eq_of_finite_setOf_ne`: two homomorphisms from
  an infinite group into a cancellative monoid agreeing cofinitely are equal.
-/

public section

namespace TauCeti

/-- A multiplicative map applied entrywise to `c • v` gives `f c • (f ∘ v)`. -/
@[simp]
theorem map_comp_smul {F M N ι : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    (f : F) (c : M) (v : ι → M) : f ∘ (c • v) = f c • (f ∘ v) :=
  funext fun _ ↦ map_mul f _ _

end TauCeti

/-- Composing with an injective monoid homomorphism detects the trivial homomorphism. -/
@[to_additive /-- Composing with an injective additive monoid homomorphism detects the zero
homomorphism. -/]
theorem MonoidHom.comp_eq_one_iff {M N P : Type*} [MulOne M] [MulOneClass N] [MulOneClass P]
    {g : N →* P} (hg : Function.Injective g) {f : M →* N} : g.comp f = 1 ↔ f = 1 := by
  simpa only [MonoidHom.comp_one] using MonoidHom.cancel_left (f₁ := f) (f₂ := 1) hg

/-- Two monoid homomorphisms from an infinite group into a cancellative monoid that disagree on
only finitely many elements are equal. -/
@[to_additive /-- Two additive monoid homomorphisms from an infinite additive group into an
additive cancellative monoid that disagree on only finitely many elements are equal. -/]
theorem MonoidHom.eq_of_finite_setOf_ne {G H : Type*} [Group G] [CancelMonoid H] [Infinite G]
    (f₁ f₂ : G →* H) (hfin : {x : G | f₁ x ≠ f₂ x}.Finite) : f₁ = f₂ := by
  ext x
  obtain ⟨y, hy⟩ := (Set.infinite_univ.sdiff (hfin.union (hfin.image (fun z => x⁻¹ * z)))).nonempty
  have hgy : f₁ y = f₂ y := not_not.mp fun hmem => hy.2 (Or.inl hmem)
  have hgxy : f₁ (x * y) = f₂ (x * y) := not_not.mp fun hmem =>
    hy.2 (Or.inr ⟨x * y, hmem, inv_mul_cancel_left x y⟩)
  rw [map_mul, map_mul, hgy] at hgxy
  exact mul_right_cancel hgxy
