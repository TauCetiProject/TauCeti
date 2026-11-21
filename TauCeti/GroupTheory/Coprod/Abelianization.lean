/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Abelianization of a free product of two groups

Abelianization is left adjoint to the forgetful functor from commutative groups to groups, so it
turns coproducts of groups into coproducts of commutative groups. For two factors `G` and `H`, the
coproduct in commutative groups coincides with the direct product, giving the canonical isomorphism

`Group.Abelianization (G ∗ H) ≃* Group.Abelianization G × Group.Abelianization H`.

It sends the class of `inl g` to `(of g, 1)` and the class of `inr h` to `(1, of h)`, and its
inverse multiplies the maps induced on abelianizations by `inl` and `inr`.

## Main definitions

* `Group.Abelianization.coprodMulEquiv`: the isomorphism
  `Group.Abelianization (G ∗ H) ≃* Group.Abelianization G × Group.Abelianization H`.

## Main results

* `Group.Abelianization.coprodMulEquiv_of_inl`, `Group.Abelianization.coprodMulEquiv_of_inr`:
  values of `coprodMulEquiv` on classes of elements from the two factors.
* `Group.Abelianization.coprodMulEquiv_symm_apply`, `Group.Abelianization.coprodMulEquiv_symm_of`:
  formulas for `coprodMulEquiv.symm`.
* `Group.Abelianization.natCard_coprod`: the cardinality of `Group.Abelianization (G ∗ H)` is the
  product of the cardinalities of `Group.Abelianization G` and `Group.Abelianization H`.
-/

public section

open scoped Monoid.Coprod

namespace Group.Abelianization

variable {G H : Type*} [Group G] [Group H]

private def coprodToProd :
    Group.Abelianization (G ∗ H) →* Group.Abelianization G × Group.Abelianization H :=
  lift (Monoid.Coprod.lift ((MonoidHom.inl _ _).comp of) ((MonoidHom.inr _ _).comp of))

private def prodToCoprod :
    Group.Abelianization G × Group.Abelianization H →* Group.Abelianization (G ∗ H) :=
  (map (Monoid.Coprod.inl : G →* G ∗ H)).coprod (map (Monoid.Coprod.inr : H →* G ∗ H))

/-- **The abelianization of a free product** of two groups is the product of their
abelianizations: the class of `inl g` corresponds to `(of g, 1)` and the class of `inr h` to
`(1, of h)`. -/
def coprodMulEquiv :
    Group.Abelianization (G ∗ H) ≃* Group.Abelianization G × Group.Abelianization H :=
  MonoidHom.toMulEquiv coprodToProd prodToCoprod
    (hom_ext _ _ (Monoid.Coprod.hom_ext (by ext; simp [coprodToProd, prodToCoprod])
      (by ext; simp [coprodToProd, prodToCoprod])))
    (by
      have h1 := DFunLike.congr_fun (hom_ext
        ((coprodToProd.comp prodToCoprod).comp (.inl (Group.Abelianization G)
          (Group.Abelianization H)))
        (.inl _ _) (by ext <;> simp [coprodToProd, prodToCoprod]))
      have h2 := DFunLike.congr_fun (hom_ext
        ((coprodToProd.comp prodToCoprod).comp (.inr (Group.Abelianization G)
          (Group.Abelianization H)))
        (.inr _ _) (by ext <;> simp [coprodToProd, prodToCoprod]))
      refine MonoidHom.ext fun ⟨a, b⟩ ↦ ?_
      have hab : (a, b) = (a, 1) * (1, b) := by simp
      rw [MonoidHom.id_apply, hab, map_mul]
      simpa [← hab] using congrArg₂ (· * ·) (h1 a) (h2 b))

@[simp]
theorem coprodMulEquiv_of_inl (g : G) :
    coprodMulEquiv (of (Monoid.Coprod.inl g : G ∗ H)) = (of g, 1) := by
  simp [coprodMulEquiv, coprodToProd]

@[simp]
theorem coprodMulEquiv_of_inr (h : H) :
    coprodMulEquiv (of (Monoid.Coprod.inr h : G ∗ H)) = (1, of h) := by
  simp [coprodMulEquiv, coprodToProd]

@[simp]
theorem coprodMulEquiv_symm_apply (p : Group.Abelianization G × Group.Abelianization H) :
    coprodMulEquiv.symm p = map Monoid.Coprod.inl p.1 * map Monoid.Coprod.inr p.2 :=
  (rfl)

theorem coprodMulEquiv_symm_of (g : G) (h : H) :
    coprodMulEquiv.symm (of g, of h) =
      of (Monoid.Coprod.inl g * Monoid.Coprod.inr h : G ∗ H) := by
  simp

/-- The cardinality of the abelianization of a free product `G ∗ H` is the product of the
cardinalities of the abelianizations of `G` and `H`. -/
theorem natCard_coprod (G H : Type*) [Group G] [Group H] :
    Nat.card (Group.Abelianization (G ∗ H)) =
      Nat.card (Group.Abelianization G) * Nat.card (Group.Abelianization H) :=
  (Nat.card_congr coprodMulEquiv.toEquiv).trans (Nat.card_prod _ _)

end Group.Abelianization
