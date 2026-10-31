/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic

/-!
# The relative spectrum of the symmetric algebra of a free sheaf is affine space

For a finite type `I`, the relative spectrum `Spec_X (Sym 𝒪_X^I)` of the symmetric algebra of the
free sheaf on `I` is the affine space `𝔸(I; X)` over `X`.

Both schemes represent `I`-tuples of global functions. For a scheme `q : T ⟶ X` over `X`, a
morphism `T ⟶ Spec_X (Sym 𝒪_X^I)` over `X` is a module map `𝒪_X^I ⟶ q_* 𝒪_T`, that is an
`I`-indexed family of global sections of `q_* 𝒪_T`, that is an `I`-indexed family of global
functions on `T` (`relativeSpecSymmetricAlgebraFreeHomEquiv`). On the other side, Mathlib's
`AlgebraicGeometry.AffineSpace.homOfVector` builds the morphism `T ⟶ 𝔸(I; X)` over `X` with
prescribed coordinates. The isomorphism `relativeSpecSymmetricAlgebraFreeIso` matches the two
descriptions: a point of `Spec_X (Sym 𝒪_X^I)` goes to the point of `𝔸(I; X)` with the same
coordinates (`comp_relativeSpecSymmetricAlgebraFreeIso_hom_left`), and conversely
(`homOfVector_comp_relativeSpecSymmetricAlgebraFreeIso_inv_left`).

## Main declarations

* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraFreeHomEquiv`: morphisms
  `T ⟶ Spec_X (Sym 𝒪_X^I)` over `X` are `I`-indexed families of global functions on `T`;
* `TauCeti.AlgebraicGeometry.affineSpaceOver X I`: the affine space `𝔸(I; X)` as an affine scheme
  over `X`;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraFreeIso`: the isomorphism
  `Spec_X (Sym 𝒪_X^I) ≅ 𝔸(I; X)` of affine schemes over `X`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory Opposite

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

variable (X) in
-- The body is exposed so that the underlying scheme and structure morphism compute: the type of
-- `affineSpaceOver_hom` depends on `affineSpaceOver_left` holding by unfolding.
/-- The affine space `𝔸(I; X)` over `X`, as an affine scheme over `X`. -/
@[expose]
def affineSpaceOver (I : Type u) : AffineSchemeOver X :=
  MorphismProperty.Over.mk ⊤ (𝔸(I; X) ↘ X) inferInstance

/-- The underlying scheme of `affineSpaceOver X I` is `𝔸(I; X)`. -/
@[simp]
lemma affineSpaceOver_left (I : Type u) : (affineSpaceOver X I).left = 𝔸(I; X) :=
  (rfl)

/-- The structure morphism of `affineSpaceOver X I` is the projection `𝔸(I; X) ⟶ X`. -/
@[simp]
lemma affineSpaceOver_hom (I : Type u) : (affineSpaceOver X I).hom = 𝔸(I; X) ↘ X :=
  (rfl)

variable (I : Type u) [Finite I]

/-- **Points of `Spec_X (Sym 𝒪_X^I)`.** For a finite type `I` and a scheme `q : T ⟶ X` over `X`,
morphisms `T ⟶ Spec_X (Sym 𝒪_X^I)` over `X` correspond to `I`-indexed families of global
functions on `T`. It is `relativeSpecSymmetricAlgebraHomEquiv` followed by
`Scheme.Hom.freeHomPushforwardEquiv`. -/
def relativeSpecSymmetricAlgebraFreeHomEquiv (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj (QuasicoherentSheaf.free X I))))) ≃
      (I → Γ(T.left, ⊤)) :=
  (relativeSpecSymmetricAlgebraHomEquiv _ T).trans (T.hom.freeHomPushforwardEquiv I)

/-- The family of global functions of a point of `Spec_X (Sym 𝒪_X^I)` is that of its module map
`𝒪_X^I ⟶ q_* 𝒪_T`. -/
lemma relativeSpecSymmetricAlgebraFreeHomEquiv_apply (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj (QuasicoherentSheaf.free X I))))) :
    relativeSpecSymmetricAlgebraFreeHomEquiv I T t =
      T.hom.freeHomPushforwardEquiv I (relativeSpecSymmetricAlgebraHomEquiv _ T t) :=
  (rfl)

/-- The bijection `relativeSpecSymmetricAlgebraFreeHomEquiv` is natural in the scheme over `X`:
composing a point with `g : T' ⟶ T` over `X` pulls back its global functions along `g`. -/
lemma relativeSpecSymmetricAlgebraFreeHomEquiv_comp {T' T : Over X} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj (QuasicoherentSheaf.free X I))))) :
    relativeSpecSymmetricAlgebraFreeHomEquiv I T' (g ≫ t) =
      g.left.appTop ∘ relativeSpecSymmetricAlgebraFreeHomEquiv I T t := by
  rw [relativeSpecSymmetricAlgebraFreeHomEquiv_apply,
    relativeSpecSymmetricAlgebraFreeHomEquiv_apply, relativeSpecSymmetricAlgebraHomEquiv_comp]
  exact Scheme.Hom.freeHomPushforwardEquiv_comp g.left (Over.w g) I _

/-- The point of `𝔸(I; X)` with the coordinates of a point `t : T ⟶ Spec_X (Sym 𝒪_X^I)` is the
composite of `t` with the point of `𝔸(I; X)` given by the coordinates of the identity. -/
private lemma comp_homOfVector_relativeSpecSymmetricAlgebraFreeHomEquiv_id (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj (QuasicoherentSheaf.free X I))))) :
    t.left ≫ AffineSpace.homOfVector ((relativeSpec X).obj
        (op ((symmetricAlgebra X).obj (QuasicoherentSheaf.free X I)))).hom
        (relativeSpecSymmetricAlgebraFreeHomEquiv I _ (𝟙 _)) =
      AffineSpace.homOfVector T.hom (relativeSpecSymmetricAlgebraFreeHomEquiv I T t) :=
  (AffineSpace.comp_homOfVector _ _ _).trans (congrArg₂ AffineSpace.homOfVector (Over.w t)
    ((relativeSpecSymmetricAlgebraFreeHomEquiv_comp I t (𝟙 _)).symm.trans
      (congrArg _ (Category.comp_id t))))

/-- The point of `Spec_X (Sym 𝒪_X^I)` with the coordinates of the point `homOfVector T.hom v` of
`𝔸(I; X)` has coordinates `v`. -/
private lemma relativeSpecSymmetricAlgebraFreeHomEquiv_homMk_homOfVector_comp (T : Over X)
    (v : I → Γ(T.left, ⊤)) :
    relativeSpecSymmetricAlgebraFreeHomEquiv I T
        (Over.homMk (V := Over.mk (𝔸(I; X) ↘ X)) (AffineSpace.homOfVector T.hom v)
            (AffineSpace.homOfVector_over _ _) ≫
          (relativeSpecSymmetricAlgebraFreeHomEquiv I _).symm (AffineSpace.coord X)) = v := by
  rw [relativeSpecSymmetricAlgebraFreeHomEquiv_comp, Equiv.apply_symm_apply]
  exact funext (AffineSpace.homOfVector_appTop_coord _ _)

variable (X) in
/-- **`Spec_X (Sym 𝒪_X^I)` is the affine space `𝔸(I; X)`.** For a finite type `I`, the relative
spectrum of the symmetric algebra of the free sheaf on `I` is isomorphic over `X` to the affine
space `𝔸(I; X)`, compatibly with the descriptions of the points of both as `I`-tuples of global
functions (`comp_relativeSpecSymmetricAlgebraFreeIso_hom_left` and
`homOfVector_comp_relativeSpecSymmetricAlgebraFreeIso_inv_left`). -/
def relativeSpecSymmetricAlgebraFreeIso :
    (relativeSpec X).obj (op ((symmetricAlgebra X).obj (QuasicoherentSheaf.free X I))) ≅
      affineSpaceOver X I :=
  MorphismProperty.Over.isoMk
    { hom := AffineSpace.homOfVector _ (relativeSpecSymmetricAlgebraFreeHomEquiv I _ (𝟙 _))
      inv := ((relativeSpecSymmetricAlgebraFreeHomEquiv I (Over.mk (𝔸(I; X) ↘ X))).symm
        (AffineSpace.coord X)).left
      hom_inv_id := congrArg CommaMorphism.left
        ((relativeSpecSymmetricAlgebraFreeHomEquiv I _).injective
          (relativeSpecSymmetricAlgebraFreeHomEquiv_homMk_homOfVector_comp I _ _))
      inv_hom_id := by
        refine (comp_homOfVector_relativeSpecSymmetricAlgebraFreeHomEquiv_id I _ _).trans ?_
        rw [Equiv.apply_symm_apply]
        -- The point of `𝔸(I; X)` with the standard coordinates is the identity.
        exact AffineSpace.hom_ext (f := AffineSpace.homOfVector (𝔸(I; X) ↘ X) (AffineSpace.coord X))
          (g := 𝟙 𝔸(I; X)) (by simp) (by simp) }
    (AffineSpace.homOfVector_over _ _)

/-- The isomorphism `Spec_X (Sym 𝒪_X^I) ≅ 𝔸(I; X)` sends a point `t` of `Spec_X (Sym 𝒪_X^I)`
over `X` to the point of `𝔸(I; X)` with the same coordinates. -/
lemma comp_relativeSpecSymmetricAlgebraFreeIso_hom_left (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj (QuasicoherentSheaf.free X I))))) :
    t.left ≫ (relativeSpecSymmetricAlgebraFreeIso X I).hom.left =
      AffineSpace.homOfVector T.hom (relativeSpecSymmetricAlgebraFreeHomEquiv I T t) :=
  comp_homOfVector_relativeSpecSymmetricAlgebraFreeHomEquiv_id I T t

/-- The inverse isomorphism `𝔸(I; X) ≅ Spec_X (Sym 𝒪_X^I)` sends the point of `𝔸(I; X)` with
coordinates `v` to the point of `Spec_X (Sym 𝒪_X^I)` with coordinates `v`. -/
lemma homOfVector_comp_relativeSpecSymmetricAlgebraFreeIso_inv_left (T : Over X)
    (v : I → Γ(T.left, ⊤)) :
    AffineSpace.homOfVector T.hom v ≫ (relativeSpecSymmetricAlgebraFreeIso X I).inv.left =
      ((relativeSpecSymmetricAlgebraFreeHomEquiv I T).symm v).left :=
  congrArg CommaMorphism.left ((Equiv.eq_symm_apply _).mpr
    (relativeSpecSymmetricAlgebraFreeHomEquiv_homMk_homOfVector_comp I T v))

-- Not a simp lemma: simp unfolds `symmetricAlgebra` in the type of its left-hand side.
/-- The coordinates of the isomorphism `Spec_X (Sym 𝒪_X^I) ≅ 𝔸(I; X)` are those of the
tautological point of `Spec_X (Sym 𝒪_X^I)`. -/
lemma relativeSpecSymmetricAlgebraFreeIso_hom_left_appTop_coord (i : I) :
    (relativeSpecSymmetricAlgebraFreeIso X I).hom.left.appTop (AffineSpace.coord X i) =
      relativeSpecSymmetricAlgebraFreeHomEquiv I _ (𝟙 _) i :=
  AffineSpace.homOfVector_appTop_coord _ _ i

end TauCeti.AlgebraicGeometry
