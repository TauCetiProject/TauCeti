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
# Quotients of free products of two groups

Killing relators that lie in one free factor of a free product `G ∗ H` only affects that factor:
for a set `R` of elements of `H`, the quotient of `G ∗ H` by the normal closure of `R` is the free
product of `G` and the quotient of `H` by the normal closure of `R`.

## Main definitions

* `Monoid.Coprod.quotientNormalClosureInrEquiv R`: the isomorphism
  `(G ∗ H) ⧸ ncl(R) ≃* G ∗ (H ⧸ ncl(R))` for `R ⊆ H`.
-/

public section

namespace Monoid.Coprod

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
