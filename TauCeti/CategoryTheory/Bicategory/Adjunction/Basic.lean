/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Inverses and composites of adjoint equivalences in a bicategory

An adjoint equivalence `a ≌ b` in a bicategory (Mathlib's `Bicategory.Equivalence`) has an
inverse `e.symm : b ≌ a`, exchanging the two `1`-morphisms, and equivalences `a ≌ b` and
`b ≌ c` compose to `e₁.trans e₂ : a ≌ c`, with `1`-morphisms the composites. Both are built
with `Bicategory.Equivalence.mkOfAdjointifyCounit`, so only the unit and counit isomorphisms
are given and the counit is adjointified. The given counits already satisfy the triangle
identities, so adjointification leaves them unchanged (`adjointifyCounit_eq_of_left_triangle`),
and `symm_counit` and `trans_counit` state them directly.

## Main definitions

* `CategoryTheory.Bicategory.Equivalence.symm`, `CategoryTheory.Bicategory.Equivalence.trans`:
  the inverse and the composite of adjoint equivalences in a bicategory.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): internal adjoint equivalences in
  bicategories.
-/

public section

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

/-- Adjointifying a counit which already satisfies the left triangle identity with `η` does not
change it. -/
lemma adjointifyCounit_eq_of_left_triangle {f : a ⟶ b} {g : b ⟶ a} {η : 𝟙 a ≅ f ≫ g}
    {ε : g ≫ f ≅ 𝟙 b} (h : leftZigzagIso η ε = λ_ f ≪≫ (ρ_ f).symm) :
    adjointifyCounit η ε = ε := by
  rw [adjointifyCounit, ← leftZigzagIso_symm, h]
  ext
  simp

namespace Equivalence

/-- The inverse of an adjoint equivalence in a bicategory: its `1`-morphisms are exchanged, and
its unit and counit are the inverses of the counit and the unit, adjointified. -/
-- The body is exposed so that the types of `symm_unit` and `symm_counit`, which mention the
-- `1`-morphisms of `e.symm`, can be computed.
@[expose] def symm (e : a ≌ b) : b ≌ a :=
  mkOfAdjointifyCounit e.counit.symm e.unit.symm

@[simp]
lemma symm_hom (e : a ≌ b) : e.symm.hom = e.inv :=
  (rfl)

@[simp]
lemma symm_inv (e : a ≌ b) : e.symm.inv = e.hom :=
  (rfl)

@[simp]
lemma symm_unit (e : a ≌ b) : e.symm.unit = e.counit.symm :=
  (rfl)

/-- The counit of `e.symm` is the inverse of the unit of `e`: adjointification does not change
it, by the right triangle identity of `e`. -/
@[simp]
lemma symm_counit (e : a ≌ b) : e.symm.counit = e.unit.symm :=
  adjointifyCounit_eq_of_left_triangle <| by
    rw [← Iso.symm_symm_eq (leftZigzagIso _ _), leftZigzagIso_symm, Iso.symm_symm_eq,
      Iso.symm_symm_eq, e.right_triangle]
    ext
    simp

/-- The composite of adjoint equivalences `e₁ : a ≌ b` and `e₂ : b ≌ c` in a bicategory. Its
`1`-morphisms are `e₁.hom ≫ e₂.hom` and `e₂.inv ≫ e₁.inv`; its unit inserts the unit of `e₂`
inside the unit of `e₁`, and its counit, before adjointification, inserts the counit of `e₁`
inside the counit of `e₂`. -/
-- The body is exposed so that the types of `trans_unit` and `trans_counit`, which mention the
-- `1`-morphisms of `e₁.trans e₂`, can be computed.
@[expose] def trans (e₁ : a ≌ b) (e₂ : b ≌ c) : a ≌ c :=
  mkOfAdjointifyCounit
    (e₁.unit ≪≫ whiskerLeftIso e₁.hom ((λ_ e₁.inv).symm ≪≫ whiskerRightIso e₂.unit e₁.inv ≪≫
      α_ e₂.hom e₂.inv e₁.inv) ≪≫ (α_ e₁.hom e₂.hom (e₂.inv ≫ e₁.inv)).symm)
    (α_ e₂.inv e₁.inv (e₁.hom ≫ e₂.hom) ≪≫ whiskerLeftIso e₂.inv
      ((α_ e₁.inv e₁.hom e₂.hom).symm ≪≫ whiskerRightIso e₁.counit e₂.hom ≪≫ λ_ e₂.hom) ≪≫
        e₂.counit)

@[simp]
lemma trans_hom (e₁ : a ≌ b) (e₂ : b ≌ c) : (e₁.trans e₂).hom = e₁.hom ≫ e₂.hom :=
  (rfl)

@[simp]
lemma trans_inv (e₁ : a ≌ b) (e₂ : b ≌ c) : (e₁.trans e₂).inv = e₂.inv ≫ e₁.inv :=
  (rfl)

@[simp]
lemma trans_unit (e₁ : a ≌ b) (e₂ : b ≌ c) :
    (e₁.trans e₂).unit = e₁.unit ≪≫ whiskerLeftIso e₁.hom ((λ_ e₁.inv).symm ≪≫
      whiskerRightIso e₂.unit e₁.inv ≪≫ α_ e₂.hom e₂.inv e₁.inv) ≪≫
        (α_ e₁.hom e₂.hom (e₂.inv ≫ e₁.inv)).symm :=
  (rfl)

/-- The counit of `e₁.trans e₂` inserts the counit of `e₁` inside the counit of `e₂`:
adjointification does not change it, since these units and counits are those of the composite
of the adjunctions `e₁.adj` and `e₂.adj`. -/
@[simp]
lemma trans_counit (e₁ : a ≌ b) (e₂ : b ≌ c) :
    (e₁.trans e₂).counit = α_ e₂.inv e₁.inv (e₁.hom ≫ e₂.hom) ≪≫ whiskerLeftIso e₂.inv
      ((α_ e₁.inv e₁.hom e₂.hom).symm ≪≫ whiskerRightIso e₁.counit e₂.hom ≪≫ λ_ e₂.hom) ≪≫
        e₂.counit :=
  adjointifyCounit_eq_of_left_triangle <| by
    apply Iso.ext
    refine Eq.trans ?_ (Adjunction.comp_left_triangle_aux e₁.adj e₂.adj)
    simp only [leftZigzagIso_hom, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      whiskerRightIso_hom, whiskerLeft_comp, comp_whiskerRight, leftZigzag,
      Adjunction.compUnit, Adjunction.compCounit, adj_unit, adj_counit]
    bicategory

end Equivalence

end CategoryTheory.Bicategory
