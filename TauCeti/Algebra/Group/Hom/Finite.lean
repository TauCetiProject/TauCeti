/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Set.Finite.Basic

/-!
# Homomorphism extensionality from cofinite agreement

Two homomorphisms from an infinite group into a cancellative monoid that disagree on only
finitely many elements are equal (`MonoidHom.eq_of_finite_setOf_ne` and
`AddMonoidHom.eq_of_finite_setOf_ne`).

## Main results

* `MonoidHom.eq_of_finite_setOf_ne` / `AddMonoidHom.eq_of_finite_setOf_ne`: two homomorphisms from
  an infinite group into a cancellative monoid agreeing cofinitely are equal.
-/

public section

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
