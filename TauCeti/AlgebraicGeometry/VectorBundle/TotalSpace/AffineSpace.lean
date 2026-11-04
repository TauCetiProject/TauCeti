/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.AffineSpace
public import TauCeti.AlgebraicGeometry.VectorBundle.Free.Sections
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.Group

/-!
# The total space of a free vector bundle is affine space

For a finite type `I`, the geometric total space `𝕍(𝒪_X^I) = Spec_X (Sym (𝒪_X^I)^∨)` of the free
sheaf on `I` is the affine space `𝔸(I; X)` over `X` (`totalSpaceFreeIso`). It is the relative
spectrum of the symmetric algebra of the self-duality `𝒪_X^I ≅ (𝒪_X^I)^∨`
(`FiniteLocallyFreeSheaf.freeIsoDual`), followed by the identification
`Spec_X (Sym 𝒪_X^I) ≅ 𝔸(I; X)` (`relativeSpecSymmetricAlgebraFreeIso`).

Both sides represent `I`-tuples of global functions. For a scheme `q : T ⟶ X` over `X`, the
points `T ⟶ 𝕍(𝒪_X^I)` over `X` correspond to families `I → Γ(T, ⊤)`, naturally in `T`
(`totalSpaceFreeHomEquiv`, `totalSpaceFreeHomEquiv_comp`), and the isomorphism sends a point to the
point `AffineSpace.homOfVector` of `𝔸(I; X)` with the same coordinates
(`comp_totalSpaceFreeIso_hom_left`, `homOfVector_comp_totalSpaceFreeIso_inv_left`).

These coordinates are those of the section of the point. The section-valued universal property
`totalSpaceHomEquiv` identifies the points of `𝕍(𝒪_X^I)` over `T` with the global sections
`𝒪_T ⟶ q^* 𝒪_X^I`, and such a section `s` has coordinates `I → Γ(T, ⊤)`
(`pullbackFreeSectionsEquiv`, in `TauCeti.AlgebraicGeometry.VectorBundle.Free.Sections`): the
values on the basis sections of `𝒪_X^I` of the transpose of the linear functional
`q^* 𝒪_X^I ≅ q^* 𝓗om(𝒪_X^I, 𝒪_X) ≅ 𝓗om(q^* 𝒪_X^I, 𝒪_T) ⟶ 𝒪_T` given by evaluation at `s`.
Taking the section of a point and then its coordinates gives the coordinates of
the point (`totalSpaceHomEquiv_trans_pullbackFreeSectionsEquiv`). Hence `𝕍(𝒪_X^I)` represents
`I`-tuples of sections, compatibly with Mathlib's description of the points of `𝔸(I; X)`.

The isomorphism `𝕍(𝒪_X^I) ≅ 𝔸(I; X)` is an isomorphism of additive group schemes over `X`
(`isAddMonHom_totalSpaceFreeIso_hom`), for the group structure of the total space given by
addition of sections (`addGrpObjTotalSpaceScheme`) and the additive group of the ring scheme
`𝔸(I; X)`: the coordinates of a sum of points are the sums of their coordinates
(`totalSpaceFreeHomEquiv_add`).

Taking `I = ULift (Fin r)` gives the affine space of rank `r`, whose points are `r`-tuples of
global functions; taking `I = PUnit` gives the affine line `𝔸(PUnit; X)`.

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceFreeIso`: the isomorphism `𝕍(𝒪_X^I) ≅ 𝔸(I; X)` of affine
  schemes over `X`;
* `TauCeti.AlgebraicGeometry.totalSpaceFreeHomEquiv`: points of `𝕍(𝒪_X^I)` over `T` are
  `I`-indexed families of global functions on `T`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_trans_pullbackFreeSectionsEquiv`: the coordinates
  of a point are the coordinates of its section;
* `TauCeti.AlgebraicGeometry.isAddMonHom_totalSpaceFreeIso_hom`: `𝕍(𝒪_X^I) ≅ 𝔸(I; X)` is an
  isomorphism of additive group schemes over `X`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}} (I : Type u) [Finite I]

variable (X) in
/-- The self-duality `𝒪_X^I ≅ (𝒪_X^I)^∨` as an isomorphism of quasicoherent sheaves, with source
the free quasicoherent sheaf whose relative spectrum of the symmetric algebra is `𝔸(I; X)`. -/
private def freeIsoDualFree :
    QuasicoherentSheaf.free X I ≅ (toQuasicoherent X).obj (dual (free X I)) :=
  ObjectProperty.isoMk _ (eqToIso (free_obj X I).symm) ≪≫
    (toQuasicoherent X).mapIso (freeIsoDual X I)

variable (X) in
/-- **The total space of a free vector bundle is affine space.** For a finite type `I`, the
geometric total space `𝕍(𝒪_X^I) = Spec_X (Sym (𝒪_X^I)^∨)` of the free sheaf on `I` is isomorphic
over `X` to the affine space `𝔸(I; X)`, compatibly with the descriptions of the points of both as
`I`-tuples of global functions (`comp_totalSpaceFreeIso_hom_left` and
`homOfVector_comp_totalSpaceFreeIso_inv_left`). -/
def totalSpaceFreeIso : (totalSpaceScheme X).obj (free X I) ≅ affineSpaceOver X I :=
  (relativeSpec X).mapIso ((symmetricAlgebra X).mapIso (freeIsoDualFree X I)).op ≪≫
    relativeSpecSymmetricAlgebraFreeIso X I

/-- **Points of the total space of a free vector bundle.** For a finite type `I` and a scheme
`q : T ⟶ X` over `X`, morphisms `T ⟶ 𝕍(𝒪_X^I)` over `X` correspond to `I`-indexed families of
global functions on `T`. These are the coordinates of the section of the point
(`totalSpaceHomEquiv_trans_pullbackFreeSectionsEquiv`). -/
def totalSpaceFreeHomEquiv (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) ≃
      (I → Γ(T.left, ⊤)) :=
  ((MorphismProperty.Over.forget _ _ X).mapIso ((relativeSpec X).mapIso
      ((symmetricAlgebra X).mapIso (freeIsoDualFree X I)).op)).homToEquiv.trans
    (relativeSpecSymmetricAlgebraFreeHomEquiv I T)

/-- The coordinates of a point of `𝕍(𝒪_X^I)` are those of the corresponding point of
`Spec_X (Sym 𝒪_X^I)`. -/
private lemma totalSpaceFreeHomEquiv_eq (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) :
    totalSpaceFreeHomEquiv I T t = relativeSpecSymmetricAlgebraFreeHomEquiv I T
      (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((relativeSpec X).map ((symmetricAlgebra X).map (freeIsoDualFree X I).hom).op)) :=
  (rfl)

/-- The bijection `totalSpaceFreeHomEquiv` is natural in the scheme over `X`: composing a point
with `g : T' ⟶ T` over `X` pulls back its global functions along `g`. -/
lemma totalSpaceFreeHomEquiv_comp {T' T : Over X} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) :
    totalSpaceFreeHomEquiv I T' (g ≫ t) = g.left.appTop ∘ totalSpaceFreeHomEquiv I T t := by
  rw [totalSpaceFreeHomEquiv_eq, totalSpaceFreeHomEquiv_eq, Category.assoc,
    relativeSpecSymmetricAlgebraFreeHomEquiv_comp]

/-- The isomorphism `𝕍(𝒪_X^I) ≅ 𝔸(I; X)` sends a point `t` of `𝕍(𝒪_X^I)` over `X` to the point of
`𝔸(I; X)` with the same coordinates. -/
lemma comp_totalSpaceFreeIso_hom_left (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) :
    t.left ≫ (totalSpaceFreeIso X I).hom.left =
      AffineSpace.homOfVector T.hom (totalSpaceFreeHomEquiv I T t) := by
  rw [totalSpaceFreeHomEquiv_eq, ← comp_relativeSpecSymmetricAlgebraFreeIso_hom_left]
  -- The underlying morphism of a composite of isomorphisms over `X` is the composite of the
  -- underlying morphisms, by definition of composition in `Over X`.
  rfl

/-- The inverse isomorphism `𝔸(I; X) ≅ 𝕍(𝒪_X^I)` sends the point of `𝔸(I; X)` with coordinates
`v` to the point of `𝕍(𝒪_X^I)` with coordinates `v`. -/
lemma homOfVector_comp_totalSpaceFreeIso_inv_left (T : Over X) (v : I → Γ(T.left, ⊤)) :
    AffineSpace.homOfVector T.hom v ≫ (totalSpaceFreeIso X I).inv.left =
      ((totalSpaceFreeHomEquiv I T).symm v).left :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (homOfVector_comp_relativeSpecSymmetricAlgebraFreeIso_inv_left I T v))

/-- **The coordinates of a point of `𝕍(𝒪_X^I)` are those of its section.** Taking the section
`𝒪_T ⟶ q^* 𝒪_X^I` of a point `T ⟶ 𝕍(𝒪_X^I)` over `X` (`totalSpaceHomEquiv`) and then its
coordinates (`pullbackFreeSectionsEquiv`) gives the coordinates of the point
(`totalSpaceFreeHomEquiv`), which `totalSpaceFreeIso` matches with the coordinates of `𝔸(I; X)`. -/
theorem totalSpaceHomEquiv_trans_pullbackFreeSectionsEquiv (T : Over X) :
    (totalSpaceHomEquiv (free X I) T).trans (pullbackFreeSectionsEquiv I T) =
      totalSpaceFreeHomEquiv I T := by
  ext t : 1
  -- Both sides are the coordinates of the module map `𝒪_X^I ≅ 𝓗om(𝒪_X^I, 𝒪_X) ⟶ q_* 𝒪_T` of `t`.
  -- The composites mix the `X.Modules` and underlying sheaf category instances, so the steps
  -- after unfolding the definitions are applied as terms rather than by `rw`.
  have h := relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map
    (F := (toQuasicoherent X).obj (dual (free X I))) (freeIsoDualFree X I).hom T t
  have hψ : (Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _
      (relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual (free X I))) T
        t) = relativeSpecSymmetricAlgebraHomEquiv ((toQuasicoherent X).obj (dual (free X I))) T t :=
    (congrArg _ (relativeSpecSymmetricAlgebraPullbackHomEquiv_apply _ T t)).trans
      (Equiv.apply_symm_apply _ _)
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv_naturality_left
    (freeIsoDual X I).hom.hom
    (relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual (free X I))) T t)
  rw [Equiv.trans_apply, totalSpaceFreeHomEquiv_eq, relativeSpecSymmetricAlgebraFreeHomEquiv_apply,
    pullbackFreeSectionsEquiv_apply, totalSpaceHomEquiv_apply, Equiv.symm_apply_apply,
    IsIso.hom_inv_id_assoc]
  refine Eq.trans ?_ (congrArg (T.hom.freeHomPushforwardEquiv I) h).symm
  exact congrArg (T.hom.freeHomPushforwardEquiv I)
    (congrArg (_ ≫ ·) (hn.trans (congrArg (_ ≫ ·) hψ)))

section Group

open AddMonObj

/-- The point of `𝔸(I; X)` corresponding to a point `t` of `𝕍(𝒪_X^I)` under the isomorphism
`totalSpaceFreeIso` has the coordinates of `t`. -/
lemma homAsOverEquiv_comp_totalSpaceFreeIso_hom (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) :
    AffineSpace.homAsOverEquiv (S := X) T
        (t ≫ (MorphismProperty.Over.forget _ _ X).map (totalSpaceFreeIso X I).hom) =
      totalSpaceFreeHomEquiv I T t :=
  funext fun i ↦ (AffineSpace.homAsOverEquiv_apply T _ i).trans <|
    (congrArg (fun f ↦ f.appTop (AffineSpace.coord X i))
      (comp_totalSpaceFreeIso_hom_left I T t)).trans
        (AffineSpace.homOfVector_appTop_coord _ _ i)

/-- **`𝕍(𝒪_X^I) ≅ 𝔸(I; X)` is an isomorphism of additive group schemes.** The isomorphism
`totalSpaceFreeIso` respects the zero sections and the fibrewise additions, for the group
structure of the total space (`addGrpObjTotalSpaceScheme`) and the additive group of the ring
scheme `𝔸(I; X)` (`AlgebraicGeometry.AffineSpace.commRingObjAsOver`). -/
instance isAddMonHom_totalSpaceFreeIso_hom :
    IsAddMonHom (N' := 𝔸(I; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).map (totalSpaceFreeIso X I).hom) := by
  -- `totalSpaceFreeIso` is the relative-spectrum map of `Sym` of the self-duality of `𝒪_X^I`,
  -- a homomorphism of group schemes, followed by `relativeSpecSymmetricAlgebraFreeIso`.
  have h : IsAddMonHom (N' := 𝔸(I; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).map
          ((relativeSpec X).map ((symmetricAlgebra X).map (freeIsoDualFree X I).hom).op) ≫
        (MorphismProperty.Over.forget _ _ X).map (relativeSpecSymmetricAlgebraFreeIso X I).hom :
          _ ⟶ 𝔸(I; X).asOver X) :=
    instIsAddMonHomComp _ _
  -- The goal's morphism is this composite by definition of `totalSpaceFreeIso` (`Iso.trans_hom`,
  -- `Functor.mapIso_hom`, `Iso.op_hom` and `Functor.map_comp`). These cannot be rewritten in the
  -- goal: its forgetful functor carries the morphism property `IsAffineHom`, which makes the
  -- rewrite motive ill-typed, and `simp` unfolds past the composite, losing the intermediate
  -- group structure that `instIsAddMonHomComp` needs.
  exact h

/-- The coordinates of a sum of points of `𝕍(𝒪_X^I)` are the sums of their coordinates. -/
@[simp]
lemma totalSpaceFreeHomEquiv_add (T : Over X)
    (t₁ t₂ : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) :
    totalSpaceFreeHomEquiv I T (t₁ + t₂) =
      totalSpaceFreeHomEquiv I T t₁ + totalSpaceFreeHomEquiv I T t₂ := by
  rw [← homAsOverEquiv_comp_totalSpaceFreeIso_hom, ← homAsOverEquiv_comp_totalSpaceFreeIso_hom,
    ← homAsOverEquiv_comp_totalSpaceFreeIso_hom]
  exact (congrArg (AffineSpace.homAsOverEquiv T)
    (AddMonObj.add_comp (N := 𝔸(I; X).asOver X) t₁ t₂ _)).trans
      (AffineSpace.homAsOverEquiv_add T _ _)

end Group

end

end TauCeti.AlgebraicGeometry
