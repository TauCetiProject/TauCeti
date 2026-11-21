/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra

/-!
# The affine quotient `X // G` of an affine scheme by an affine group action

Let `H` be a commutative `R`-bialgebra and `A` a commutative `H`-comodule algebra, so that the
affine monoid scheme `G = Spec H` acts on `X = Spec A` on the right. The **affine quotient**
`X // G = Spec A^{co H}` is the spectrum of the coinvariants `TauCeti.ComoduleAlgebra.coinvariants`,
with quotient morphism `X ⟶ X // G` induced by the inclusion of the invariant functions.

The quotient morphism is invariant: it has the same composite with the action
`Spec (A ⊗[R] H) ⟶ X` and with the projection `Spec (A ⊗[R] H) ⟶ X`
(`TauCeti.ComoduleAlgebra.AffineQuotient.act_projection`). Every invariant morphism from `X` to
an affine scheme factors uniquely through it
(`TauCeti.ComoduleAlgebra.AffineQuotient.existsUnique_desc`): `X // G` is a categorical quotient
in affine schemes. No hypothesis on `G` is needed for this.

For a reductive group over a field `k` and `A` finitely generated over `k`, `X // G` is the
geometric-invariant-theory quotient of Seshadri. Its finite generation over `k` (which needs `A`
finitely generated over `k`), the description of its geometric points by closed orbits, and the
universal property for non-affine targets use reductivity and are not proved here. For `H`
linearly reductive over a field `k` and `A` finitely generated over `k`, finite generation of
`A^{co H}` over `k` is `TauCeti.ComoduleAlgebra.finiteType_coinvariants`.

The construction and the proof of the universal property follow the affine invariant quotient of
a ring by a monoid action, `TauCeti.AffineInvariantQuotient` in
`TauCeti.AlgebraicGeometry.Quotient.Affine` (its `quotient`, `projection`, `desc` and
`existsUnique_desc`), with the fixed subring replaced by the coinvariants of a coaction.

## Main declarations

* `TauCeti.ComoduleAlgebra.AffineQuotient.quotient`: the affine quotient `Spec A^{co H}`.
* `TauCeti.ComoduleAlgebra.AffineQuotient.projection`: the quotient morphism.
* `TauCeti.ComoduleAlgebra.AffineQuotient.act_projection`: the quotient morphism is invariant.
* `TauCeti.ComoduleAlgebra.AffineQuotient.desc`: descent of an invariant morphism to an affine
  target.
* `TauCeti.ComoduleAlgebra.AffineQuotient.existsUnique_desc`: the affine-target universal
  property.

## References

* C. S. Seshadri, *Geometric reductivity over arbitrary base*, Adv. Math. **26** (1977), 225–274,
  Theorem 3.
* D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*, third edition, Springer (1994),
  Chapter 0, §2 and Chapter 1, §2.
* G. Böckle, M. Harris, C. Khare, J. A. Thorne, arXiv:1609.03491v2, §3 (the paragraph before
  Proposition 3.2, and Proposition 3.2).
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra.AffineQuotient

universe u

variable (R : Type*) (H A : Type u) [CommRing R] [CommRing H] [Bialgebra R H]
  [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]

/-- The **affine quotient** `X // G = Spec A^{co H}` of `X = Spec A` by the action of
`G = Spec H`: the spectrum of the coinvariants. -/
noncomputable abbrev quotient : Scheme.{u} :=
  Spec (CommRingCat.of (coinvariants R H A))

/-- The quotient morphism `X ⟶ X // G`, induced by the inclusion of the invariant functions. -/
noncomputable def projection : Spec (CommRingCat.of A) ⟶ quotient R H A :=
  Spec.algebraMap (coinvariants R H A) A

/-- The defining equation for the quotient morphism. -/
theorem projection_def : projection R H A = Spec.algebraMap (coinvariants R H A) A := (rfl)

/-- **The quotient morphism is invariant**: composing it with the action
`Spec (coact) : Spec (A ⊗[R] H) ⟶ X` or with the projection
`Spec (a ↦ a ⊗ 1) : Spec (A ⊗[R] H) ⟶ X` gives the same morphism. -/
@[reassoc]
theorem act_projection :
    Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom) ≫ projection R H A =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)) ≫
        projection R H A := by
  rw [projection_def, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  simpa using mem_coinvariants.1 a.property

variable {R H A}

/-- An invariant morphism to an affine scheme pulls back functions to invariant functions. -/
private theorem preimage_mem_coinvariants {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)) ≫ f)
    (a : Γ(Y, ⊤)) :
    (Spec.preimage (f ≫ Y.isoSpec.hom)).hom a ∈ coinvariants R H A := by
  have h : Spec.map (Spec.preimage (f ≫ Y.isoSpec.hom) ≫
      CommRingCat.ofHom (coactAlgHom R H A).toRingHom) =
      Spec.map (Spec.preimage (f ≫ Y.isoSpec.hom) ≫
        CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)) := by
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, ← Category.assoc, hf, Category.assoc]
  have ha := congrArg (fun k ↦ k.hom a) (Spec.map_injective h)
  rw [mem_coinvariants]
  simpa using ha

/-- **Descent of an invariant morphism to an affine target** through the affine quotient. -/
noncomputable def desc {Y : Scheme.{u}} [IsAffine Y] (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)) ≫ f) :
    quotient R H A ⟶ Y :=
  Spec.map (CommRingCat.ofHom
    ((Spec.preimage (f ≫ Y.isoSpec.hom)).hom.codRestrict
      (coinvariants R H A) (preimage_mem_coinvariants f hf))) ≫ Y.isoSpec.inv

/-- The descended morphism factors the given invariant morphism. -/
@[reassoc (attr := simp)]
theorem projection_desc {Y : Scheme.{u}} [IsAffine Y] (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)) ≫ f) :
    projection R H A ≫ desc f hf = f := by
  rw [desc, projection_def, ← Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom
      ((Spec.preimage (f ≫ Y.isoSpec.hom)).hom.codRestrict
        (coinvariants R H A) (preimage_mem_coinvariants f hf)) ≫
      CommRingCat.ofHom (algebraMap (coinvariants R H A) A) =
      Spec.preimage (f ≫ Y.isoSpec.hom) := by
    ext a
    rfl
  rw [h, Spec.map_preimage]
  simp

/-- Morphisms from the affine quotient to an affine scheme are determined by their composition
with the quotient morphism. -/
@[ext]
theorem hom_ext {Y : Scheme.{u}} [IsAffine Y] {f g : quotient R H A ⟶ Y}
    (hfg : projection R H A ≫ f = projection R H A ≫ g) : f = g := by
  apply eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (coinvariants R H A).val.toRingHom)
    Subtype.val_injective ⊤ (isAffineOpen_top Y) (by simp) (by simp)
  exact hfg

/-- **The affine quotient is a categorical quotient in affine schemes**: every invariant morphism
to an affine scheme factors uniquely through the quotient morphism. -/
theorem existsUnique_desc {Y : Scheme.{u}} [IsAffine Y] (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : Spec.map (CommRingCat.ofHom (coactAlgHom R H A).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)) ≫ f) :
    ∃! g : quotient R H A ⟶ Y, projection R H A ≫ g = f :=
  ⟨desc f hf, projection_desc f hf, fun _ hg ↦ hom_ext (hg.trans (projection_desc f hf).symm)⟩

/-- Descending the composite of the quotient morphism with a morphism to an affine scheme
recovers that morphism. -/
@[simp]
theorem desc_projection {Y : Scheme.{u}} [IsAffine Y] (f : quotient R H A ⟶ Y) :
    desc (projection R H A ≫ f) (by rw [act_projection_assoc]) = f :=
  hom_ext (projection_desc _ _)

end TauCeti.ComoduleAlgebra.AffineQuotient
