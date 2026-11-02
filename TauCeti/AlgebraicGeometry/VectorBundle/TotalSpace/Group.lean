/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Group
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Zero section and fibrewise addition on the total space of a vector bundle

The geometric total space `𝕍(E) = Spec_X (Sym E^∨)` of a finite locally free sheaf `E` on a
scheme `X` is the relative spectrum of a symmetric algebra, so it carries the structure of a
commutative group scheme over `X` (`addGrpObjRelativeSpecSymmetricAlgebra`): a zero section
`X ⟶ 𝕍(E)` and an addition `𝕍(E) ×_X 𝕍(E) ⟶ 𝕍(E)` over `X`. This file identifies that structure
with addition of sections. For a scheme `q : T ⟶ X` over `X`, the bijection
`totalSpaceHomEquiv` between morphisms `T ⟶ 𝕍(E)` over `X` and sections `𝒪_T ⟶ q^* E` is an
isomorphism of abelian groups (`totalSpaceHomAddEquiv`). Hence

* the point `T ⟶ X ⟶ 𝕍(E)` through the zero section of `𝕍(E)` corresponds to the zero section
  of `q^* E` (`totalSpaceHomEquiv_toUnit_comp_zero`, and `totalSpaceHomEquiv_zero_eq_zero` for
  `T = X`); and
* adding two points `t₁, t₂ : T ⟶ 𝕍(E)` with the addition morphism of `𝕍(E)` corresponds to adding
  their sections of `q^* E` (`totalSpaceHomEquiv_lift_comp_add`).

A morphism `a : E ⟶ F` of finite locally free sheaves induces a homomorphism of group schemes
`𝕍(E) ⟶ 𝕍(F)` (`isAddMonHom_totalSpaceScheme_map`), so `E ↦ 𝕍(E)` is a functor to group objects
of `Over X` (`totalSpaceAddGrp`).

The bijection `totalSpaceHomEquiv` is the additive bijection
`Hom_X(T, Spec_X (Sym E^∨)) ≃+ Hom(q^* (E^∨), 𝒪_T)` of
`relativeSpecSymmetricAlgebraPullbackHomAddEquiv`, followed by precomposition with the base-change
isomorphism `𝓗om(q^* E, 𝒪_T) ≅ q^* (E^∨)` and by the identification of linear functionals on
`𝓗om(q^* E, 𝒪_T)` with sections of `q^* E`. The last step is additive because the tensor product
of `𝒪_T`-modules is additive in each variable.

## Main declarations

* `TauCeti.AlgebraicGeometry.addGrpObjTotalSpaceScheme` and
  `TauCeti.AlgebraicGeometry.isCommAddMonObjTotalSpaceScheme`: the total space of a vector bundle
  is a commutative additive group object of `Over X`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomAddEquiv`: its group of `T`-points is the group of
  sections of `q^* E`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_toUnit_comp_zero`,
  `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_zero_eq_zero` and
  `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_lift_comp_add`: the zero section and fibrewise
  addition in terms of sections;
* `TauCeti.AlgebraicGeometry.isAddMonHom_totalSpaceScheme_map` and
  `TauCeti.AlgebraicGeometry.totalSpaceAddGrp`: morphisms of vector bundles induce homomorphisms of
  group schemes, functorially.

## References

These use the convention `V(F) = Spec_X (Sym F)`, in which the total space of `E` is `V(E^∨)`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`.

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite AddMonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}} (E : FiniteLocallyFreeSheaf X)

/-- **The total space of a vector bundle is an additive group scheme over `X`.** The total space
`𝕍(E)` is the relative spectrum `Spec_X (Sym E^∨)`, with the group structure of
`addGrpObjRelativeSpecSymmetricAlgebra`; its group of `T`-points is the group of sections of
`q^* E` (`totalSpaceHomAddEquiv`). -/
instance addGrpObjTotalSpaceScheme :
    AddGrpObj ((MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :=
  addGrpObjRelativeSpecSymmetricAlgebra ((toQuasicoherent X).obj (dual E))

/-- **The additive group structure of the total space of a vector bundle is commutative.** -/
instance isCommAddMonObjTotalSpaceScheme :
    IsCommAddMonObj ((MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :=
  isCommAddMonObjRelativeSpecSymmetricAlgebra ((toQuasicoherent X).obj (dual E))

/-- **The group of points of the total space of a vector bundle is the group of sections.** For a
finite locally free sheaf `E` on `X` and a scheme `q : T ⟶ X` over `X`, the bijection
`totalSpaceHomEquiv` between morphisms `T ⟶ 𝕍(E)` over `X` and global sections `𝒪_T ⟶ q^* E` is an
isomorphism of groups, for the group structure on `T`-points given by `addGrpObjTotalSpaceScheme`
and addition of sections. -/
def totalSpaceHomAddEquiv (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) ≃+
      (𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj E.obj) where
  toEquiv := totalSpaceHomEquiv E T
  map_add' t₁ t₂ := by
    -- The linear functional on `q^* (E^∨)` of a point is additive in the point ...
    have h : relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) T
        (t₁ + t₂) =
        relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) T t₁ +
          relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) T t₂ :=
      (relativeSpecSymmetricAlgebraPullbackHomAddEquiv_apply _ T _).symm.trans <|
        ((relativeSpecSymmetricAlgebraPullbackHomAddEquiv _ T).map_add t₁ t₂).trans <|
          congrArg₂ (· + ·) (relativeSpecSymmetricAlgebraPullbackHomAddEquiv_apply _ T t₁)
            (relativeSpecSymmetricAlgebraPullbackHomAddEquiv_apply _ T t₂)
    -- ... and passing from a functional on `𝓗om(q^* E, 𝒪_T)` to a section of `q^* E` is additive,
    -- since tensoring `𝒪_T`-modules is additive in each variable.
    let : MonoidalPreadditive T.left.Modules := SheafOfModules.monoidalPreadditive T.left.sheaf
    simp only [Equiv.toFun_as_coe, totalSpaceHomEquiv_apply, h, Preadditive.comp_add,
      Scheme.Modules.dualHomUnitEquiv_apply, MonoidalPreadditive.add_whiskerRight,
      Preadditive.add_comp]

/-- The section of a point of `𝕍(E)` in the group of sections of `q^* E` is the one given by
`totalSpaceHomEquiv`. -/
@[simp]
lemma totalSpaceHomAddEquiv_apply (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomAddEquiv E T t = totalSpaceHomEquiv E T t :=
  (rfl)

/-- The point of `𝕍(E)` of a section of `q^* E` is the one given by `totalSpaceHomEquiv`. -/
@[simp]
lemma totalSpaceHomAddEquiv_symm_apply (T : Over X)
    (s : 𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj E.obj) :
    (totalSpaceHomAddEquiv E T).symm s = (totalSpaceHomEquiv E T).symm s :=
  (rfl)

/-- **The zero point of the total space is the zero section.** For a scheme `q : T ⟶ X` over `X`,
the point `T ⟶ X ⟶ 𝕍(E)` through the zero section of the group scheme `𝕍(E)` corresponds to the
zero section of `q^* E`. -/
@[simp]
lemma totalSpaceHomEquiv_toUnit_comp_zero (T : Over X) :
    totalSpaceHomEquiv E T
      (toUnit T ≫ (ζ : 𝟙_ (Over X) ⟶
        (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E))) = 0 :=
  -- `toUnit T ≫ ζ` is by definition the zero point `0 : T ⟶ 𝕍(E)`
  (totalSpaceHomAddEquiv E T).map_zero

/-- **The zero section of the total space is the zero section of the vector bundle.** The zero
section `X ⟶ 𝕍(E)` over `X` of the group scheme `𝕍(E)` corresponds to the zero section of
`(𝟙 X)^* E`. Not a `simp` lemma: `simp` rewrites the unit object of `Over X` in the type of the
section; `totalSpaceHomEquiv_toUnit_comp_zero` is the `simp` form over an arbitrary base. -/
lemma totalSpaceHomEquiv_zero_eq_zero :
    totalSpaceHomEquiv E (𝟙_ (Over X))
      (ζ : 𝟙_ (Over X) ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) =
      0 := by
  simpa using totalSpaceHomEquiv_toUnit_comp_zero E (𝟙_ (Over X))

/-- **Fibrewise addition on the total space is addition of sections.** For points
`t₁ t₂ : T ⟶ 𝕍(E)` over `X`, the point `T ⟶ 𝕍(E) ×_X 𝕍(E) ⟶ 𝕍(E)` obtained from the pair
`(t₁, t₂)` and the addition morphism of `𝕍(E)` corresponds to the sum of the sections of `q^* E`
of `t₁` and `t₂`. -/
@[simp]
lemma totalSpaceHomEquiv_lift_comp_add {T : Over X}
    (t₁ t₂ : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomEquiv E T (lift t₁ t₂ ≫ σ) =
      totalSpaceHomEquiv E T t₁ + totalSpaceHomEquiv E T t₂ :=
  -- `lift t₁ t₂ ≫ σ` is by definition the sum `t₁ + t₂` of points
  (totalSpaceHomAddEquiv E T).map_add t₁ t₂

variable {E} in
/-- **A morphism of vector bundles is a homomorphism of group schemes on total spaces.** The
morphism `𝕍(E) ⟶ 𝕍(F)` over `X` induced by `a : E ⟶ F` respects the zero sections and fibrewise
addition. -/
instance isAddMonHom_totalSpaceScheme_map {F : FiniteLocallyFreeSheaf X} (a : E ⟶ F) :
    IsAddMonHom ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map a)) :=
  -- `(totalSpaceScheme X).map a` is by definition (`totalSpaceScheme_map`) the relative-spectrum
  -- map of `Sym` of the dual map `F^∨ ⟶ E^∨`
  isAddMonHom_relativeSpec_map ((toQuasicoherent X).map (dualFunctor.map a.op : dual F ⟶ dual E))

variable (X) in
/-- The total space `E ↦ 𝕍(E)` as a covariant functor from finite locally free sheaves on `X` to
group schemes over `X`: the dual `E^∨`, followed by the contravariant functor
`relativeSpecSymmetricAlgebraAddGrp` from quasicoherent sheaves to group schemes. Its underlying
functor to `Over X` is the total space `totalSpaceScheme X` (`totalSpaceAddGrp_obj_X` and
`totalSpaceAddGrp_map_hom_hom`). -/
-- exposed so that its underlying objects are seen to be the total spaces: without this, the
-- statement of `totalSpaceAddGrp_map_hom_hom` does not typecheck
@[expose]
def totalSpaceAddGrp : FiniteLocallyFreeSheaf X ⥤ AddGrp (Over X) :=
  dualFunctor.rightOp ⋙ (toQuasicoherent X).op ⋙ relativeSpecSymmetricAlgebraAddGrp X

/-- The group scheme `(totalSpaceAddGrp X).obj E` is the total space `𝕍(E)`. -/
@[simp]
lemma totalSpaceAddGrp_obj_X :
    ((totalSpaceAddGrp X).obj E).X =
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E) :=
  (rfl)

/-- The homomorphism of group schemes `(totalSpaceAddGrp X).map a` is the map of total spaces
induced by `a`. -/
@[simp]
lemma totalSpaceAddGrp_map_hom_hom {E F : FiniteLocallyFreeSheaf X} (a : E ⟶ F) :
    ((totalSpaceAddGrp X).map a).hom.hom =
      (MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map a) :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
