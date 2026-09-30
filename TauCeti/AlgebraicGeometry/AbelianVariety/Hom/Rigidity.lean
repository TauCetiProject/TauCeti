/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Basic
public import TauCeti.AlgebraicGeometry.Rigidity

/-!
# Morphisms of abelian varieties preserving the identity are homomorphisms

A morphism `f : A.toOver ⟶ B.toOver` of the underlying schemes over `Spec K` that sends the
identity of `A` to the identity of `B` is automatically a homomorphism of group schemes. The
defect `h (x, y) = f (x + y) - f x - f y` is a morphism
`A.toOver ⊗ A.toOver ⟶ B.toOver` that vanishes on `A × {0}`,
so by `TauCeti.AlgebraicGeometry.eq_snd_comp_lift_comp` it depends only on `y`, and it
vanishes on `{0} × A`.

Consequently the homomorphisms `A ⟶ B` of abelian varieties are exactly the pointed morphisms
`A.toOver ⟶ B.toOver` over `Spec K`. This is how morphisms of abelian varieties arise in
practice, for instance from the universal property of the Jacobian, where a morphism of schemes
is produced first and only then recognised as a homomorphism.

## Main declarations

* `TauCeti.AlgebraicGeometry.isMonHom_of_one_hom`: a morphism of group schemes preserving the
  identity is a homomorphism when the source is proper and geometrically integral;
* `TauCeti.AlgebraicGeometry.AbelianVariety.Hom.equivPointed`: homomorphisms `A ⟶ B` are
  equivalent to the morphisms `A.toOver ⟶ B.toOver` preserving the identity.

## References

* D. Mumford, *Abelian Varieties*, Section 4, Corollary 1 to the rigidity lemma.
* J. S. Milne, *Abelian Varieties*, Corollary 1.2.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K]

/-- A morphism of group schemes over `K` from a proper geometrically integral source to a
separated locally finite type target is a homomorphism if it preserves the identity. -/
theorem isMonHom_of_one_hom {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    [IsProper A.hom] [GeometricallyIntegral A.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  -- The defect `h (x, y) = f (x y) / (f x * f y)`, in the group of morphisms `A × A ⟶ B`.
  let h : A ⊗ A ⟶ B :=
    (μ ≫ f) / ((fst _ _ ≫ f) * (snd _ _ ≫ f))
  have key {W : Over (Spec (.of K))} (a b : W ⟶ A) :
      lift a b ≫ h = ((a * b) ≫ f) / ((a ≫ f) * (b ≫ f)) := by
    simp only [h, GrpObj.comp_div, comp_mul, ← Category.assoc, ← Hom.mul_def,
      lift_fst, lift_snd]
  have hf₁ (X : Over _) : (1 : X ⟶ A) ≫ f = 1 := by
    rw [Hom.one_def, Hom.one_def, Category.assoc, hf]
  have H := eq_snd_comp_lift_comp h η η η (by
    rw [key]
    simp only [← Hom.one_def, Category.id_comp, hf₁, _root_.mul_one, div_self'])
  rw [key] at H
  simp only [← Hom.one_def, Category.id_comp, hf₁, comp_one, _root_.one_mul,
    div_self'] at H
  refine ⟨hf, ?_⟩
  rw [← lift_fst_comp_snd_comp, ← Hom.mul_def]
  exact div_eq_one.mp H

namespace AbelianVariety

namespace Hom

/-- Homomorphisms of abelian varieties are exactly the morphisms of the underlying schemes over
`Spec K` preserving the identity. -/
noncomputable def equivPointed (A B : AbelianVariety K) :
    (A ⟶ B) ≃ {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]} where
  toFun f := ⟨toOverHom f, one_hom f⟩
  invFun f := mk' f.1 f.2 (isMonHom_of_one_hom f.1 f.2).mul_hom
  left_inv _ := toOverHom_injective (toOverHom_mk' _ _ _)
  right_inv _ := Subtype.ext (toOverHom_mk' _ _ _)

/-- The homomorphism attached to a pointed morphism has that morphism as its morphism over
`Spec K`. -/
@[simp]
lemma toOverHom_equivPointed_symm_apply {A B : AbelianVariety K}
    (f : {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]}) :
    toOverHom ((equivPointed A B).symm f) = f :=
  toOverHom_mk' _ _ _

end Hom

/-- The pointed morphism underlying a homomorphism is its morphism over `Spec K`. -/
@[simp]
lemma coe_equivPointed_apply {A B : AbelianVariety K} (f : A ⟶ B) :
    (Hom.equivPointed A B f : A.toOver ⟶ B.toOver) = Hom.toOverHom f :=
  by simp [Hom.equivPointed]

end AbelianVariety

end AlgebraicGeometry

end TauCeti
