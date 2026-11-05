/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Group homology in degrees zero and one

Complements to Mathlib's `Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree`, which
identifies `H₀(G, A)` with the coinvariants of `A`, and `H₁(G, A)` with `Gᵃᵇ ⊗ A` for trivial
coefficients `A`.

## Main results

* `TauCeti.groupHomology.H0π_eq_iff`: two elements of `A` have the same class in `H₀(G, A)`
  exactly when their difference lies in the augmentation submodule
  `Representation.Coinvariants.ker A.ρ`.
* `TauCeti.groupHomology.isZero_H1_of_forall_exists_zpow_eq`: if every element of `G` is an
  `m`-th power and `m` kills the trivial coefficients `A`, then `H₁(G, A) = 0`.
-/

public section

universe u

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-- Two elements of `A` have the same class in `H₀(G, A)` exactly when their difference lies in
the augmentation submodule `Representation.Coinvariants.ker A.ρ`, the kernel of the projection to
the coinvariants. -/
theorem H0π_eq_iff {x y : A.V} :
    H0π A x = H0π A y ↔ x - y ∈ Representation.Coinvariants.ker A.ρ := by
  rw [← coinvariantsMk_comp_H0Iso_inv_apply, ← coinvariantsMk_comp_H0Iso_inv_apply]
  exact (H0Iso A).toLinearEquiv.symm.injective.eq_iff.trans
    (Representation.Coinvariants.mk_eq_iff _)

open TensorProduct in
/-- **First homology of a divisible group.** If every element of `G` is an `m`-th power and
multiplication by `m` is zero on the trivial representation `A`, then `H₁(G, A) = Gᵃᵇ ⊗ A`
vanishes. -/
theorem isZero_H1_of_forall_exists_zpow_eq [A.IsTrivial] (m : ℤ) (hG : ∀ g : G, ∃ x, x ^ m = g)
    (hA : ∀ a : A.V, m • a = 0) : CategoryTheory.Limits.IsZero (H1 A) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  suffices Subsingleton (Additive (Abelianization G) ⊗[ℤ] A) from
    (H1AddEquivOfIsTrivial A).injective.subsingleton
  rw [subsingleton_iff_forall_eq 0]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x a =>
    -- the class of `g = yᵐ` is `m` times that of `y`, and `m` kills `a`
    obtain ⟨g, hg⟩ : ∃ g, Abelianization.of g = x.toMul := QuotientGroup.mk_surjective x.toMul
    obtain ⟨y, rfl⟩ := hG g
    rw [← ofMul_toMul x, ← hg, map_zpow, ofMul_zpow, TensorProduct.smul_tmul, hA,
      TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

end TauCeti.groupHomology
