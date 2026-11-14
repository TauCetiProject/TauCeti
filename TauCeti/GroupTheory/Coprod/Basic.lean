/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Trivial factors and quotients of free products of two monoids

If one factor of a free product `M ∗ N` is trivial, the inclusion of the other factor is onto.

Killing relators that lie in one free factor of a free product `G ∗ H` of groups only affects that
factor: for a set `R` of elements of `H`, the quotient of `G ∗ H` by the normal closure of `R` is
the free product of `G` and the quotient of `H` by the normal closure of `R`.

## Main definitions

* `Monoid.Coprod.quotientNormalClosureInrEquiv R`: the isomorphism
  `(G ∗ H) ⧸ ncl(R) ≃* G ∗ (H ⧸ ncl(R))` for `R ⊆ H`.

## Main results

* `Monoid.Coprod.inl_surjective`, `Monoid.Coprod.inr_surjective`: if one factor of a free product
  `M ∗ N` is trivial, the inclusion of the other one is onto.
-/

public section

namespace Monoid.Coprod

section TrivialFactor

variable {M N : Type*} [MulOneClass M] [MulOneClass N]

/-- If `N` is trivial, every element of the free product `M ∗ N` comes from `M`. -/
theorem inl_surjective [Subsingleton N] : Function.Surjective (inl : M →* Coprod M N) := fun x ↦ by
  induction x using induction_on with
  | inl m => exact ⟨m, rfl⟩
  | inr n => exact ⟨1, by simp [Subsingleton.elim n 1]⟩
  | mul x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩

/-- If `M` is trivial, every element of the free product `M ∗ N` comes from `N`. -/
theorem inr_surjective [Subsingleton M] : Function.Surjective (inr : N →* Coprod M N) := by
  rw [← swap_comp_inl, MonoidHom.coe_comp]
  exact swap_surjective.comp inl_surjective

end TrivialFactor

open Subgroup

variable {G H : Type*} [Group G] [Group H] (R : Set H)

/-- Relators in the right factor of a free product only affect that factor: for `R ⊆ H`, the
quotient of `G ∗ H` by the normal closure of `R` is the free product of `G` and the quotient of
`H` by the normal closure of `R`. -/
def quotientNormalClosureInrEquiv :
    Coprod G H ⧸ normalClosure ((inr : H →* Coprod G H) '' R) ≃*
      Coprod G (H ⧸ normalClosure R) :=
  MonoidHom.toMulEquiv
    (QuotientGroup.lift _ (map (.id G) (QuotientGroup.mk' (normalClosure R))) <|
      normalClosure_le_normal <| by
        rintro _ ⟨r, hr, rfl⟩
        simp [MonoidHom.mem_ker, (QuotientGroup.eq_one_iff r).2 (subset_normalClosure hr)])
    (lift ((QuotientGroup.mk' _).comp inl) <|
      QuotientGroup.lift _ ((QuotientGroup.mk' _).comp inr) <| normalClosure_le_normal <| by
        rintro r hr
        simp [MonoidHom.mem_ker,
          (QuotientGroup.eq_one_iff _).2 (subset_normalClosure (Set.mem_image_of_mem inr hr))])
    (QuotientGroup.monoidHom_ext _ <| hom_ext (by ext; simp) (by ext; simp))
    (hom_ext (by ext; simp) (QuotientGroup.monoidHom_ext _ (by ext; simp)))

@[simp]
theorem quotientNormalClosureInrEquiv_mk (w : Coprod G H) :
    quotientNormalClosureInrEquiv R (w : Coprod G H ⧸ normalClosure (inr '' R)) =
      map (.id G) (QuotientGroup.mk' (normalClosure R)) w := (rfl)

@[simp]
theorem quotientNormalClosureInrEquiv_symm_inl (g : G) :
    (quotientNormalClosureInrEquiv R).symm (inl g) = ((inl g : Coprod G H) : Coprod G H ⧸ _) :=
  (rfl)

@[simp]
theorem quotientNormalClosureInrEquiv_symm_inr_mk (h : H) :
    (quotientNormalClosureInrEquiv R).symm (inr (h : H ⧸ normalClosure R)) =
      ((inr h : Coprod G H) : Coprod G H ⧸ _) := (rfl)

end Monoid.Coprod
