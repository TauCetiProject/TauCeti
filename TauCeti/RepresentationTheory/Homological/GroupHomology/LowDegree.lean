/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Group homology in low degrees

Complements to Mathlib's `Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree`, which
identifies `H₀(G, A)` with the coinvariants of `A` and, for trivial `A`, `H₁(G, A)` with
`Gᵃᵇ ⊗[ℤ] A`.

## Main results

* `TauCeti.groupHomology.H0π_eq_iff`: two elements of `A` have the same class in `H₀(G, A)`
  exactly when their difference lies in the augmentation submodule
  `Representation.Coinvariants.ker A.ρ`.
* `TauCeti.subsingleton_groupHomology_one_of_forall_exists_sq`: `H₁(G; k) = 0` when every element
  of `G` is a square and `2 = 0` in `k`.
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

end TauCeti.groupHomology

namespace TauCeti

open TensorProduct

variable (k : Type u) [CommRing k] {G : Type u} [Group G]

/-- **The first homology of a two-divisible group vanishes in characteristic two.** If every element
of `G` is a square and `2 = 0` in `k`, then `H₁(G; k) = Gᵃᵇ ⊗ k` vanishes: every element of the
abelianization is twice another, and twice every element of `k` is zero. -/
theorem subsingleton_groupHomology_one_of_forall_exists_sq (hk : (2 : k) = 0)
    (h : ∀ g : G, ∃ x, x ^ 2 = g) : Subsingleton (groupHomology (Rep.trivial k G k) 1) := by
  suffices Subsingleton (Additive (Abelianization G) ⊗[ℤ] k) by
    exact (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial k G k)).injective.subsingleton
  refine ⟨fun s t ↦ ?_⟩
  suffices ∀ s : Additive (Abelianization G) ⊗[ℤ] k, s = 0 by rw [this s, this t]
  intro s
  induction s using TensorProduct.inductionOn with
  | add s t hs ht => rw [hs, ht, add_zero]
  | tmul a b =>
    -- `a` is the class of a square `x ^ 2`, so `a ⊗ b = x ⊗ 2b = 0`
    -- `Abelianization.of` is the quotient map, so it is surjective
    obtain ⟨g, hg⟩ : ∃ g, Abelianization.of g = Additive.toMul a :=
      QuotientGroup.mk_surjective _
    obtain ⟨x, rfl⟩ := h g
    have ha : a = Additive.ofMul (Abelianization.of x) + Additive.ofMul (Abelianization.of x) := by
      rw [← ofMul_mul, ← map_mul, ← pow_two, hg, ofMul_toMul]
    rw [ha, TensorProduct.add_tmul, ← TensorProduct.tmul_add, ← two_mul, hk, zero_mul,
      TensorProduct.tmul_zero]

end TauCeti
