/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import TauCeti.AlgebraicGeometry.Modules.Algebra.AffineBase
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# The relative spectrum of the symmetric algebra of `Ñ` over `Spec R`

For a module `N` over a commutative ring `R`, the relative spectrum `Spec_X (Sym Ñ)` of the
symmetric algebra of the associated quasicoherent sheaf `Ñ` on `X = Spec R` is the spectrum
`Spec (Sym_R N)` of the symmetric algebra of `N`, as an affine scheme over `Spec R`
(`relativeSpecSymmetricAlgebraTildeIso`).

Both schemes represent `R`-linear maps into global functions. For a scheme `q : T ⟶ Spec R`, let
`R` act on `Γ(T, ⊤)` through `q`.

* A morphism `T ⟶ Spec_X (Sym Ñ)` over `Spec R` is a module map `Ñ ⟶ q_* 𝒪_T`
  (`relativeSpecSymmetricAlgebraHomEquiv`), hence by the adjunction between `M ↦ M~` and global
  sections an `R`-linear map from `N` to the global sections of `q_* 𝒪_T`, which are the global
  functions on `T` (`moduleSpecΓPushforwardIso`). This is
  `relativeSpecSymmetricAlgebraTildeHomEquiv`.
* A morphism `T ⟶ Spec (Sym_R N)` over `Spec R` is an `R`-algebra map `Sym_R N → Γ(T, ⊤)`, hence
  an `R`-linear map `N → Γ(T, ⊤)` (`specSymmetricAlgebraHomEquiv`, through the general
  `overHomSpecEquivAlgHom` and `SymmetricAlgebra.lift`).

Both bijections are natural in `T`, so both schemes represent the same functor on schemes over
`Spec R`, and the isomorphism is Mathlib's `CategoryTheory.Functor.RepresentableBy.uniqueUpToIso`
between them. It is the affine-base computation of the linear scheme `Spec_X (Sym F)` through
Mathlib's `AlgebraicGeometry.tildeEquiv`. For a finite projective module it computes the total
space of the associated vector bundle (`TauCeti.AlgebraicGeometry.totalSpaceFiniteProjectiveIso`).

## Main declarations

* `TauCeti.AlgebraicGeometry.specSymmetricAlgebraOver R N`: `Spec (Sym_R N)` as an affine scheme
  over `Spec R`;
* `TauCeti.AlgebraicGeometry.specSymmetricAlgebraHomEquiv`: points of `Spec (Sym_R N)` are
  `R`-linear maps `N → Γ(T, ⊤)`;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraTildeHomEquiv`: points of
  `Spec_X (Sym Ñ)` are `R`-linear maps `N → Γ(T, ⊤)`;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraTildeIso`: the isomorphism
  `Spec_X (Sym Ñ) ≅ Spec (Sym_R N)` over `Spec R`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1) and
  [Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory Opposite

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- Pullback of global functions along a morphism `g : T' ⟶ T` of schemes over `Spec R` is
`R`-linear. -/
private def appTopLinearMap {T' T : Over (Spec R)} (g : T' ⟶ T) :
    (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
        (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)) ⟶
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T'.hom.appTop).hom).obj
        (ModuleCat.of Γ(T'.left, ⊤) Γ(T'.left, ⊤)) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
      (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)))
    (Y := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T'.hom.appTop).hom).obj
      (ModuleCat.of Γ(T'.left, ⊤) Γ(T'.left, ⊤)))
    { toFun := g.left.appTop
      map_add' := map_add g.left.appTop.hom
      map_smul' r x := by
        -- `R` acts on `Γ(T', ⊤)` through `T'.hom = g.left ≫ T.hom`.
        have hr : ((Scheme.ΓSpecIso R).inv ≫ T'.hom.appTop) r =
            g.left.appTop (((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop) r) := by
          rw [← Over.w g, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply,
            CommRingCat.comp_apply]
        rw [RingHom.id_apply]
        refine ((congrArg g.left.appTop (ModuleCat.restrictScalars.smul_def _ r x)).trans
          ?_).trans (ModuleCat.restrictScalars.smul_def
            ((Scheme.ΓSpecIso R).inv ≫ T'.hom.appTop).hom
            (M := ModuleCat.of Γ(T'.left, ⊤) Γ(T'.left, ⊤)) r _).symm
        rw [smul_eq_mul, smul_eq_mul, map_mul, hr] }

/-- The functor of points represented by `Spec_X (Sym Ñ)` and `Spec (Sym_R N)`: a scheme
`q : T ⟶ Spec R` goes to the `R`-linear maps `N → Γ(T, ⊤)`. -/
private def linearMapsToGlobalFunctions (N : ModuleCat.{u} R) :
    (Over (Spec R))ᵒᵖ ⥤ Type u where
  obj T := N ⟶ (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.unop.hom.appTop).hom).obj
    (ModuleCat.of Γ(T.unop.left, ⊤) Γ(T.unop.left, ⊤))
  map g := TypeCat.ofHom fun f ↦ f ≫ appTopLinearMap g.unop
  map_id T := by
    ext f n
    change (𝟙 T.unop : T.unop ⟶ T.unop).left.appTop (f n) = f n
    rw [Over.id_left, Scheme.Hom.id_appTop]
    exact CommRingCat.id_apply _ _
  map_comp g g' := by
    ext f n
    change (g ≫ g').unop.left.appTop (f n) = g'.unop.left.appTop (g.unop.left.appTop (f n))
    rw [unop_comp, Over.comp_left, Scheme.Hom.comp_appTop]
    exact CommRingCat.comp_apply _ _ _

variable (N : ModuleCat.{u} R)

variable (R) in
-- The body is exposed so that the underlying scheme and structure morphism compute: the type of
-- `specSymmetricAlgebraOver_hom` depends on `specSymmetricAlgebraOver_left` holding by unfolding.
/-- The spectrum `Spec (Sym_R N)` of the symmetric algebra of an `R`-module `N`, as an affine
scheme over `Spec R`. -/
@[expose]
def specSymmetricAlgebraOver : AffineSchemeOver (Spec R) :=
  MorphismProperty.Over.mk ⊤
    (Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R N)))) inferInstance

/-- The underlying scheme of `specSymmetricAlgebraOver R N` is `Spec (Sym_R N)`. -/
@[simp]
lemma specSymmetricAlgebraOver_left :
    (specSymmetricAlgebraOver R N).left = Spec (.of (SymmetricAlgebra R N)) :=
  (rfl)

/-- The structure morphism of `specSymmetricAlgebraOver R N` is `Spec` of the structure map
`R → Sym_R N`. -/
@[simp]
lemma specSymmetricAlgebraOver_hom :
    (specSymmetricAlgebraOver R N).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R N))) :=
  (rfl)

/-- **Points of `Spec (Sym_R N)`.** For a scheme `q : T ⟶ Spec R`, morphisms
`T ⟶ Spec (Sym_R N)` over `Spec R` correspond to `R`-linear maps `N → Γ(T, ⊤)`, where `R` acts on
global functions through `q`. A morphism goes to the pullback of the generators `N → Sym_R N`
along it; an `R`-linear map goes to `Spec` of the `R`-algebra map `Sym_R N → Γ(T, ⊤)` extending
it. -/
def specSymmetricAlgebraHomEquiv (T : Over (Spec R)) :
    (T ⟶ (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)) ≃
      (N ⟶ (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
        (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤))) :=
  letI := ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom.toAlgebra
  (overHomSpecEquivAlgHom (SymmetricAlgebra R N) T).trans
    (SymmetricAlgebra.lift.symm.trans (ModuleCat.homEquiv (M := N)
      (N := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
        (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)))).symm)

/-- The `R`-linear map `N → Γ(T, ⊤)` of a point `t : T ⟶ Spec (Sym_R N)` sends `n` to the
pullback along `t` of the generator `n` of `Sym_R N`. -/
lemma specSymmetricAlgebraHomEquiv_apply (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)) (n : N) :
    specSymmetricAlgebraHomEquiv N T t n =
      ((Scheme.ΓSpecIso _).inv ≫ t.left.appTop) (SymmetricAlgebra.ι R N n) := by
  let _ := ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom.toAlgebra
  -- The linear map of the algebra homomorphism `φ` of `t` is the restriction of `φ` to the
  -- generators, since `φ` is the lift of that restriction.
  exact (SymmetricAlgebra.lift_ι_apply
    (SymmetricAlgebra.lift.symm (overHomSpecEquivAlgHom _ T t)) n).symm.trans
      (congrArg (· (SymmetricAlgebra.ι R N n))
        (SymmetricAlgebra.lift.apply_symm_apply (overHomSpecEquivAlgHom _ T t)) |>.trans
          (overHomSpecEquivAlgHom_apply _ T t _))

/-- The bijection `specSymmetricAlgebraHomEquiv` is natural in the scheme over `Spec R`:
composing a point with `g : T' ⟶ T` pulls back its linear map along `g`. -/
lemma specSymmetricAlgebraHomEquiv_comp {T' T : Over (Spec R)} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)) (n : N) :
    specSymmetricAlgebraHomEquiv N T' (g ≫ t) n =
      g.left.appTop (specSymmetricAlgebraHomEquiv N T t n) := by
  rw [specSymmetricAlgebraHomEquiv_apply, specSymmetricAlgebraHomEquiv_apply]
  exact (overHomSpecEquivAlgHom_apply _ T' (g ≫ t) _).symm.trans
    ((overHomSpecEquivAlgHom_comp _ g t _).trans
      (congrArg g.left.appTop (overHomSpecEquivAlgHom_apply _ T t _)))

/-- The point of `Spec (Sym_R N)` of an `R`-linear map `f : N → Γ(T, ⊤)` has as ring map the
`R`-algebra map `Sym_R N → Γ(T, ⊤)` extending `f`. -/
lemma specSymmetricAlgebraHomEquiv_symm_appTop (T : Over (Spec R))
    (f : N ⟶ (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
      (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤))) :
    letI := ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom.toAlgebra
    (Scheme.ΓSpecIso _).inv ≫ ((specSymmetricAlgebraHomEquiv N T).symm f).left.appTop =
      CommRingCat.ofHom (SymmetricAlgebra.lift (A := Γ(T.left, ⊤)) f.hom).toRingHom :=
  overHomSpecEquivAlgHom_symm_appTop _ T _

/-- **Points of `Spec_X (Sym Ñ)` over `X = Spec R`.** For an `R`-module `N` and a scheme
`q : T ⟶ Spec R`, morphisms `T ⟶ Spec_X (Sym Ñ)` over `Spec R` correspond to `R`-linear maps
`N → Γ(T, ⊤)`, where `R` acts on global functions through `q`. It is
`relativeSpecSymmetricAlgebraHomEquiv`, followed by the adjunction between `M ↦ M~` and global
sections and by the identification of the global sections of `q_* 𝒪_T` with `Γ(T, ⊤)`. -/
def relativeSpecSymmetricAlgebraTildeHomEquiv (T : Over (Spec R)) :
    (T ⟶ (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N))))) ≃
      (N ⟶ (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
        (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤))) :=
  (relativeSpecSymmetricAlgebraHomEquiv _ T).trans
    ((tilde.adjunction.homEquiv N _).trans (moduleSpecΓPushforwardIso T).homToEquiv)

/-- The linear map of a point `t : T ⟶ Spec_X (Sym Ñ)` is the adjoint of its module map
`Ñ ⟶ q_* 𝒪_T`, read in the global functions on `T`. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_apply (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N))))) :
    relativeSpecSymmetricAlgebraTildeHomEquiv N T t =
      tilde.adjunction.homEquiv N _ (relativeSpecSymmetricAlgebraHomEquiv _ T t) ≫
        (moduleSpecΓPushforwardIso T).hom :=
  (rfl)

/-- The point of `Spec_X (Sym Ñ)` of an `R`-linear map `f : N → Γ(T, ⊤)` is the point whose
module map `Ñ ⟶ q_* 𝒪_T` is the adjoint of `f`, read in the global sections of `q_* 𝒪_T`. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_symm_apply (T : Over (Spec R))
    (f : N ⟶ (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
      (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤))) :
    (relativeSpecSymmetricAlgebraTildeHomEquiv N T).symm f =
      (relativeSpecSymmetricAlgebraHomEquiv _ T).symm
        ((tilde.adjunction.homEquiv N _).symm (f ≫ (moduleSpecΓPushforwardIso T).inv)) :=
  (rfl)

/-- The bijection `relativeSpecSymmetricAlgebraTildeHomEquiv` is natural in the scheme over
`Spec R`: composing a point with `g : T' ⟶ T` pulls back its linear map along `g`. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_comp {T' T : Over (Spec R)} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N))))) (n : N) :
    relativeSpecSymmetricAlgebraTildeHomEquiv N T' (g ≫ t) n =
      g.left.appTop (relativeSpecSymmetricAlgebraTildeHomEquiv N T t n) := by
  rw [relativeSpecSymmetricAlgebraTildeHomEquiv_apply,
    relativeSpecSymmetricAlgebraTildeHomEquiv_apply, relativeSpecSymmetricAlgebraHomEquiv_comp]
  -- The composite with pullback of functions is formed in `(Spec R).Modules`, which `rw` does not
  -- identify with the category of sheaves of modules in which the adjunction is stated.
  erw [Adjunction.homEquiv_naturality_right]
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply]
  exact moduleSpecΓPushforwardIso_hom_naturality g _

/-- `Spec (Sym_R N)` represents `R`-linear maps `N → Γ(T, ⊤)`. -/
private def specSymmetricAlgebraRepresentableBy :
    (linearMapsToGlobalFunctions N).RepresentableBy
      ((MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)) where
  homEquiv := specSymmetricAlgebraHomEquiv N _
  homEquiv_comp g t := ModuleCat.hom_ext (LinearMap.ext fun n ↦
    specSymmetricAlgebraHomEquiv_comp N g t n)

/-- `Spec_X (Sym Ñ)` represents `R`-linear maps `N → Γ(T, ⊤)`. -/
private def relativeSpecSymmetricAlgebraTildeRepresentableBy :
    (linearMapsToGlobalFunctions N).RepresentableBy
      ((MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N))))) where
  homEquiv := relativeSpecSymmetricAlgebraTildeHomEquiv N _
  homEquiv_comp g t := ModuleCat.hom_ext (LinearMap.ext fun n ↦
    relativeSpecSymmetricAlgebraTildeHomEquiv_comp N g t n)

/-- The isomorphism `Spec_X (Sym Ñ) ≅ Spec (Sym_R N)` of schemes over `Spec R` between two
representing objects of `R`-linear maps `N → Γ(T, ⊤)`. -/
private def relativeSpecSymmetricAlgebraTildeOverIso :
    (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N)))) ≅
      (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N) :=
  (relativeSpecSymmetricAlgebraTildeRepresentableBy N).uniqueUpToIso
    (specSymmetricAlgebraRepresentableBy N)

/-- **`Spec_X (Sym Ñ)` is `Spec (Sym_R N)` over `X = Spec R`.** For an `R`-module `N`, the
relative spectrum of the symmetric algebra of the associated quasicoherent sheaf `Ñ` is
isomorphic over `Spec R` to the spectrum of the symmetric algebra `Sym_R N`, compatibly with the
descriptions of the points of both as `R`-linear maps `N → Γ(T, ⊤)`
(`specSymmetricAlgebraHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_hom` and
`relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv`). -/
def relativeSpecSymmetricAlgebraTildeIso :
    (relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N))) ≅
      specSymmetricAlgebraOver R N :=
  MorphismProperty.Over.isoMk ((Over.forget _).mapIso (relativeSpecSymmetricAlgebraTildeOverIso N))
    (Over.w (relativeSpecSymmetricAlgebraTildeOverIso N).hom)

/-- The isomorphism `Spec_X (Sym Ñ) ≅ Spec (Sym_R N)` preserves the linear maps `N → Γ(T, ⊤)` of
points. -/
lemma specSymmetricAlgebraHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_hom
    (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N))))) :
    specSymmetricAlgebraHomEquiv N T
        (t ≫ (MorphismProperty.Over.forget _ _ _).map
          (relativeSpecSymmetricAlgebraTildeIso N).hom) =
      relativeSpecSymmetricAlgebraTildeHomEquiv N T t := by
  change (specSymmetricAlgebraRepresentableBy N).homEquiv
      (t ≫ (relativeSpecSymmetricAlgebraTildeOverIso N).hom) =
    (relativeSpecSymmetricAlgebraTildeRepresentableBy N).homEquiv t
  -- Mathlib's `uniqueUpToIso` is the Yoneda preimage of the composite bijection of points, so it
  -- is the point corresponding to the universal point of the source.
  rw [show (relativeSpecSymmetricAlgebraTildeOverIso N).hom =
      (specSymmetricAlgebraRepresentableBy N).homEquiv.symm
        ((relativeSpecSymmetricAlgebraTildeRepresentableBy N).homEquiv (𝟙 _)) from rfl,
    Functor.RepresentableBy.comp_homEquiv_symm, Equiv.apply_symm_apply,
    ← Functor.RepresentableBy.homEquiv_comp, Category.comp_id]

/-- The inverse isomorphism `Spec (Sym_R N) ≅ Spec_X (Sym Ñ)` preserves the linear maps
`N → Γ(T, ⊤)` of points. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv
    (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)) :
    relativeSpecSymmetricAlgebraTildeHomEquiv N T
        (t ≫ (MorphismProperty.Over.forget _ _ _).map
          (relativeSpecSymmetricAlgebraTildeIso N).inv) =
      specSymmetricAlgebraHomEquiv N T t := by
  change (relativeSpecSymmetricAlgebraTildeRepresentableBy N).homEquiv
      (t ≫ (relativeSpecSymmetricAlgebraTildeOverIso N).inv) =
    (specSymmetricAlgebraRepresentableBy N).homEquiv t
  -- Mathlib's `uniqueUpToIso` is the Yoneda preimage of the composite bijection of points, so it
  -- is the point corresponding to the universal point of the source.
  rw [show (relativeSpecSymmetricAlgebraTildeOverIso N).inv =
      (relativeSpecSymmetricAlgebraTildeRepresentableBy N).homEquiv.symm
        ((specSymmetricAlgebraRepresentableBy N).homEquiv (𝟙 _)) from rfl,
    Functor.RepresentableBy.comp_homEquiv_symm, Equiv.apply_symm_apply,
    ← Functor.RepresentableBy.homEquiv_comp, Category.comp_id]

end TauCeti.AlgebraicGeometry
