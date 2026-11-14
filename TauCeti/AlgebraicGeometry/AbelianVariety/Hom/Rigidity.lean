/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Basic
public import TauCeti.AlgebraicGeometry.Rigidity.GroupScheme

/-!
# Morphisms of abelian varieties preserving the identity are homomorphisms

A morphism `f : A.toOver ⟶ B.toOver` of the underlying schemes over `Spec K` that sends the
identity of `A` to the identity of `B` is automatically a homomorphism of group schemes
(`TauCeti.AlgebraicGeometry.isMonHom_of_one_hom`, proved in
`TauCeti.AlgebraicGeometry.Rigidity.GroupScheme` as a specialization of the relative theorem over an
arbitrary base scheme).

Consequently the homomorphisms `A ⟶ B` of abelian varieties are exactly the pointed morphisms
`A.toOver ⟶ B.toOver` over `Spec K`. This is how morphisms of abelian varieties arise in
practice, for instance from the universal property of the Jacobian, where a morphism of schemes
is produced first and only then recognised as a homomorphism.

## Main declarations

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
