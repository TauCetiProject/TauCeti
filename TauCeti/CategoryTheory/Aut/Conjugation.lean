/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Conj

/-!
# Conjugation of automorphisms along isomorphisms

An isomorphism `e : x ≅ y` conjugates `Aut x` onto `Aut y` (Mathlib's `Aut.autMulEquivOfIso`).
This file records how this conjugation depends on `e`. When `Aut x` is commutative, it does not
depend on `e` at all (`Aut.autMulEquivOfIso_eq_of_commute`): two isomorphisms `x ≅ y` differ by
an automorphism of `x`, whose inner conjugation is trivial. This is the first part of the
Stacks Project, Lemma 8.11.8 (tag 0CJY): the automorphism groups of a gerbe with abelian inertia
are identified with each other independently of the chosen object isomorphisms. Without
commutativity the statement fails: in `Fin 3`, conjugation by the identity and by the
transposition `(0 1)` differ on the transposition `(1 2)`.

Conjugation is compatible with composition of isomorphisms (`Aut.autMulEquivOfIso_trans`) and
with every functor (`Functor.mapAut_autMulEquivOfIso`), and conjugates of automorphisms related
by isomorphisms `c : x₁ ≅ x₂`, `d : y₁ ≅ y₂` stay related, whatever isomorphisms `x₁ ≅ y₁` and
`x₂ ≅ y₂` are used (`Aut.autMulEquivOfIso_hom_comp_of_commute`), again when `Aut x₁` is
commutative.

## Main declarations

* `CategoryTheory.Aut.autMulEquivOfIso_eq_of_commute`: conjugation does not depend on the
  isomorphism when `Aut x` is commutative.
* `CategoryTheory.Aut.autMulEquivOfIso_eq_conjAut`: agreement with Mathlib's `Iso.conjAut`.
* `CategoryTheory.Aut.autMulEquivOfIso_trans`, `CategoryTheory.Aut.autMulEquivOfIso_refl`:
  composition and identity, from the corresponding facts for `Iso.conjAut`.
* `CategoryTheory.Functor.mapAut_autMulEquivOfIso`: compatibility with a functor.
* `CategoryTheory.Aut.autMulEquivOfIso_hom_comp_of_commute`: conjugates of related automorphisms
  are related.

## References

* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Aut

variable {x y z : C}

/-- Mathlib's two conjugations along an isomorphism, `Aut.autMulEquivOfIso` and `Iso.conjAut`,
agree. -/
theorem autMulEquivOfIso_eq_conjAut (e : x ≅ y) : autMulEquivOfIso e = e.conjAut :=
  MulEquiv.ext fun a ↦ Aut.ext (by rw [Iso.conjAut_apply, autMulEquivOfIso_apply_asIso])

/-- Conjugation along the identity is the identity. -/
@[simp]
theorem autMulEquivOfIso_refl (x : C) : autMulEquivOfIso (Iso.refl x) = MulEquiv.refl _ := by
  refine MulEquiv.ext fun a ↦ Aut.ext (Iso.ext ?_)
  simp

/-- Conjugation along a composite of isomorphisms is the composite of the conjugations. -/
@[simp]
theorem autMulEquivOfIso_trans (e : x ≅ y) (d : y ≅ z) :
    autMulEquivOfIso (e ≪≫ d) = (autMulEquivOfIso e).trans (autMulEquivOfIso d) := by
  simp only [autMulEquivOfIso_eq_conjAut]
  exact MulEquiv.ext fun a ↦ Iso.trans_conjAut e d a

/-- **Conjugation does not depend on the isomorphism** when `Aut x` is commutative: two
isomorphisms `e e' : x ≅ y` conjugate `Aut x` onto `Aut y` in the same way (the first part of
the Stacks Project, Lemma 8.11.8). -/
theorem autMulEquivOfIso_eq_of_commute (h : ∀ a b : Aut x, a * b = b * a) (e e' : x ≅ y) :
    autMulEquivOfIso e = autMulEquivOfIso e' := by
  refine MulEquiv.ext fun a ↦ Aut.ext (Iso.ext ?_)
  have hab := congrArg (fun b : Aut x ↦ b.asIso.hom) (h a (.of (e' ≪≫ e.symm)))
  simp only [mul_asIso, Iso.trans_hom, Iso.symm_hom, Category.assoc] at hab
  simp only [autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_epi e'.hom, ← cancel_mono e.inv]
  simpa using hab

/-- Conjugates of automorphisms related by isomorphisms stay related: if `a₁ ∈ Aut x₁` and
`a₂ ∈ Aut x₂` satisfy `a₁ ≫ c = c ≫ a₂` for `c : x₁ ≅ x₂`, then their conjugates along arbitrary
isomorphisms `e₁ : x₁ ≅ y₁` and `e₂ : x₂ ≅ y₂` satisfy the same relation with any `d : y₁ ≅ y₂`,
provided `Aut x₁` is commutative. No compatibility of `e₁`, `e₂`, `c` and `d` is assumed. -/
theorem autMulEquivOfIso_hom_comp_of_commute {x₁ x₂ y₁ y₂ : C}
    (h : ∀ a b : Aut x₁, a * b = b * a) (c : x₁ ≅ x₂) (d : y₁ ≅ y₂) (e₁ : x₁ ≅ y₁)
    (e₂ : x₂ ≅ y₂) (a₁ : Aut x₁) (a₂ : Aut x₂) (ha : a₁.asIso.hom ≫ c.hom = c.hom ≫ a₂.asIso.hom) :
    (autMulEquivOfIso e₁ a₁).asIso.hom ≫ d.hom = d.hom ≫ (autMulEquivOfIso e₂ a₂).asIso.hom := by
  have key := congrArg (fun b : Aut y₂ ↦ b.asIso.hom)
    (DFunLike.congr_fun (autMulEquivOfIso_eq_of_commute h (e₁ ≪≫ d) (c ≪≫ e₂)) a₁)
  simp only [autMulEquivOfIso_apply_asIso, Iso.symm_hom, Iso.trans_inv, Iso.trans_hom,
    Category.assoc, reassoc_of% ha, Iso.inv_hom_id_assoc] at key
  simp only [autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← cancel_epi d.inv, ← key]
  simp

end Aut

/-- Conjugation along an isomorphism commutes with every functor: `G` maps the conjugate of `a`
along `e` to the conjugate of `G a` along `G e`. -/
theorem Functor.mapAut_autMulEquivOfIso (G : C ⥤ D) {x y : C} (e : x ≅ y) (a : Aut x) :
    G.mapAut y (Aut.autMulEquivOfIso e a) =
      Aut.autMulEquivOfIso (G.mapIso e) (G.mapAut x a) := by
  simp only [Aut.autMulEquivOfIso_eq_conjAut]
  exact Aut.ext (G.map_conjAut e a)

end CategoryTheory
