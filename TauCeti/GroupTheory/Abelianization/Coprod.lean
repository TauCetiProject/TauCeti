/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coprod.Basic
import TauCeti.GroupTheory.Abelianization.Basic

/-!
# Abelianization of a free product of groups

The abelianization functor is a left adjoint and therefore sends coproducts in the category of
groups (free products `Monoid.Coprod G H`) to coproducts in the category of abelian groups, which
coincide with binary direct products `Group.Abelianization G × Group.Abelianization H`.

## Main definitions and results

* `Group.Abelianization.coprodMulEquiv`: the canonical isomorphism
  `Group.Abelianization (Monoid.Coprod G H) ≃* Group.Abelianization G × Group.Abelianization H`.
* `Group.Abelianization.coprodMulEquiv_of`, `Group.Abelianization.coprodMulEquiv_of_inl`,
  `Group.Abelianization.coprodMulEquiv_of_inr`,
  `Group.Abelianization.coprodMulEquiv_symm_apply`: evaluation of `coprodMulEquiv` and its inverse
  on classes of elements.
-/

public section

namespace Group.Abelianization

variable {G H : Type*} [Group G] [Group H]

/-- **Abelianization of a free product.** The abelianization of `Monoid.Coprod G H` is canonically
isomorphic to `Group.Abelianization G × Group.Abelianization H`: the class of an element projects to
the classes of its two factor projections, and conversely `(a, b)` maps to the product of the
images of `a` and `b` under the canonical embeddings. -/
def coprodMulEquiv :
    Group.Abelianization (Monoid.Coprod G H) ≃*
      Group.Abelianization G × Group.Abelianization H :=
  MonoidHom.toMulEquiv
    ((map Monoid.Coprod.fst).prod (map Monoid.Coprod.snd))
    ((map (Monoid.Coprod.inl : G →* Monoid.Coprod G H)).coprod
      (map (Monoid.Coprod.inr : H →* Monoid.Coprod G H)))
    (by ext <;> simp)
    (by ext <;> simp)

/-- `coprodMulEquiv` sends the class of `w` to the pair of classes of its factor projections. -/
@[simp]
theorem coprodMulEquiv_of (w : Monoid.Coprod G H) :
    coprodMulEquiv (of w) = (of (Monoid.Coprod.fst w), of (Monoid.Coprod.snd w)) :=
  (rfl)

/-- `coprodMulEquiv` sends the class of `inl g` to `(of g, 1)`. -/
theorem coprodMulEquiv_of_inl (g : G) :
    coprodMulEquiv (of (Monoid.Coprod.inl g : Monoid.Coprod G H)) = (of g, 1) := by
  simp

/-- `coprodMulEquiv` sends the class of `inr h` to `(1, of h)`. -/
theorem coprodMulEquiv_of_inr (h : H) :
    coprodMulEquiv (of (Monoid.Coprod.inr h : Monoid.Coprod G H)) = (1, of h) := by
  simp

/-- The inverse of `coprodMulEquiv` multiplies the induced embeddings of the two coordinates. -/
@[simp]
theorem coprodMulEquiv_symm_apply (p : Group.Abelianization G × Group.Abelianization H) :
    coprodMulEquiv.symm p =
      map (Monoid.Coprod.inl : G →* Monoid.Coprod G H) p.1 *
        map (Monoid.Coprod.inr : H →* Monoid.Coprod G H) p.2 :=
  (rfl)

/-- The inverse of `coprodMulEquiv` sends `(of g, of h)` to the class of `inl g * inr h`. -/
theorem coprodMulEquiv_symm_of (g : G) (h : H) :
    coprodMulEquiv.symm (of g, of h) =
      of (Monoid.Coprod.inl g * Monoid.Coprod.inr h) := by
  simp

end Group.Abelianization
