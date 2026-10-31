/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
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
  an `R`-linear map `N → Γ(T, ⊤)` (`specSymmetricAlgebraHomEquiv`).

Both bijections are natural in `T`, and the isomorphism is the one they induce. It is the
affine-base computation of the linear scheme `Spec_X (Sym F)` through Mathlib's
`AlgebraicGeometry.tildeEquiv`. For a finite projective module it computes the total space of the
associated vector bundle (`TauCeti.AlgebraicGeometry.totalSpaceFiniteProjectiveIso`).

## Main declarations

* `TauCeti.AlgebraicGeometry.moduleSpecΓPushforwardIso`: the global sections of `q_* 𝒪_T`, as an
  `R`-module, are the global functions on `T`;
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

/-- The identification of the global sections of `q_* 𝒪_T` with the global functions on `T` is
`R`-linear, where `R` acts on global functions through `q : T ⟶ Spec R`. -/
private def moduleSpecΓPushforwardLinearEquiv (T : Over (Spec R)) :
    (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules)) ≃ₗ[R]
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
        (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)) where
  toFun x := T.hom.pushforwardStructureAlgebraΓRingEquiv.symm x
  map_add' := map_add T.hom.pushforwardStructureAlgebraΓRingEquiv.symm
  map_smul' r x := by
    -- `r` acts on global sections of `q_* 𝒪_T` through the structure map of the function
    -- algebra, which is pullback of functions along `q`. The two carriers agree only up to
    -- unfolding `moduleSpecΓFunctor`, so `x` is read as a section of the function algebra.
    have h : r • x = algebraMap Γ(Spec R, ⊤) Γ(T.hom.pushforwardStructureAlgebra.X, ⊤)
        ((Scheme.ΓSpecIso R).inv r) * (show Γ(T.hom.pushforwardStructureAlgebra.X, ⊤) from x) :=
      Algebra.smul_def ((Scheme.ΓSpecIso R).inv r)
        (show Γ(T.hom.pushforwardStructureAlgebra.X, ⊤) from x)
    erw [h]
    rw [map_mul, Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_algebraMap]
    rfl
  invFun y := T.hom.pushforwardStructureAlgebraΓRingEquiv y
  left_inv := T.hom.pushforwardStructureAlgebraΓRingEquiv.apply_symm_apply
  right_inv := T.hom.pushforwardStructureAlgebraΓRingEquiv.symm_apply_apply

/-- For a scheme `q : T ⟶ Spec R`, the `R`-module of global sections of `q_* 𝒪_T` is the
module of global functions on `T`, on which `R` acts through `q`. The isomorphism is the
identification of the global sections of `q_* 𝒪_T` with the global functions on `T`. -/
def moduleSpecΓPushforwardIso (T : Over (Spec R)) :
    (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules)) ≅
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
        (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)) where
  hom := ModuleCat.ofHom (X := (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules)))
    (Y := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
      (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)))
    (moduleSpecΓPushforwardLinearEquiv T).toLinearMap
  inv := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
      (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)))
    (Y := (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules)))
    (moduleSpecΓPushforwardLinearEquiv T).symm.toLinearMap
  hom_inv_id := by
    ext x
    exact (moduleSpecΓPushforwardLinearEquiv T).symm_apply_apply x
  inv_hom_id := by
    ext y
    exact (moduleSpecΓPushforwardLinearEquiv T).apply_symm_apply y

/-- The identification `moduleSpecΓPushforwardIso` is the identification of the global sections
of `q_* 𝒪_T` with the global functions on `T`. -/
lemma moduleSpecΓPushforwardIso_hom_apply (T : Over (Spec R))
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules))) :
    (moduleSpecΓPushforwardIso T).hom x = T.hom.pushforwardStructureAlgebraΓRingEquiv.symm x :=
  (rfl)

/-- The inverse of `moduleSpecΓPushforwardIso` is the identification of the global functions on
`T` with the global sections of `q_* 𝒪_T`. -/
lemma moduleSpecΓPushforwardIso_inv_apply (T : Over (Spec R))
    (y : (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
      (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤))) :
    (moduleSpecΓPushforwardIso T).inv y = T.hom.pushforwardStructureAlgebraΓRingEquiv y :=
  (rfl)

/-- The identification `moduleSpecΓPushforwardIso` turns pullback of regular functions along a
morphism `g : T' ⟶ T` over `Spec R` into pullback of global functions along `g`. -/
lemma moduleSpecΓPushforwardIso_hom_naturality {T' T : Over (Spec R)} (g : T' ⟶ T)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules))) :
    (moduleSpecΓPushforwardIso T').hom (moduleSpecΓFunctor.map
        (Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g)).hom.hom x) =
      g.left.appTop ((moduleSpecΓPushforwardIso T).hom x) :=
  (congrArg T'.hom.pushforwardStructureAlgebraΓRingEquiv.symm
    (CommMon.sectionsAlgHom_apply
      (Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g)) ⊤ x).symm).trans
      (Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_sectionsAlgHom g.left (Over.w g) x)

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
        (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤))) where
  toFun t := ModuleCat.ofHom (X := N)
    (Y := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom).obj
      (ModuleCat.of Γ(T.left, ⊤) Γ(T.left, ⊤)))
    { toFun n := ((Scheme.ΓSpecIso _).inv ≫ t.left.appTop) (SymmetricAlgebra.ι R N n)
      map_add' x y := by
        rw [map_add, map_add]
        rfl
      map_smul' r n := by
        rw [map_smul, Algebra.smul_def, map_mul]
        congr 1
        exact ConcreteCategory.congr_hom
          ((comp_spec_map_eq_iff (R := R) _ t.left T.hom).mp (Over.w t)) r }
  invFun f :=
    letI : Algebra R Γ(T.left, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom.toAlgebra
    let φ : SymmetricAlgebra R N →ₐ[R] Γ(T.left, ⊤) := SymmetricAlgebra.lift
      { toFun := f.hom, map_add' := f.hom.map_add, map_smul' := f.hom.map_smul }
    Over.homMk (ΓSpec.adjunction.homEquiv T.left (op (.of (SymmetricAlgebra R N)))
        (CommRingCat.ofHom φ.toRingHom).op) <| by
      refine (comp_spec_map_eq_iff (R := R) _ _ T.hom).mpr ?_
      rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
      ext r
      exact φ.commutes r
  left_inv t := by
    let _ : Algebra R Γ(T.left, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom.toAlgebra
    -- The pullback of functions along `t` is an `R`-algebra map, so it is the lift of its
    -- restriction to the generators.
    let ψ : SymmetricAlgebra R N →ₐ[R] Γ(T.left, ⊤) :=
      { ((Scheme.ΓSpecIso _).inv ≫ t.left.appTop).hom with
        commutes' := ConcreteCategory.congr_hom
          ((comp_spec_map_eq_iff (R := R) _ t.left T.hom).mp (Over.w t)) }
    refine Over.OverMorphism.ext (ext_to_Spec ?_)
    refine (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _).trans (CommRingCat.hom_ext ?_)
    exact congrArg AlgHom.toRingHom (SymmetricAlgebra.algHom_ext (F := SymmetricAlgebra.lift _)
      (G := ψ) (LinearMap.ext fun n ↦ SymmetricAlgebra.lift_ι_apply _ n))
  right_inv f := by
    let _ : Algebra R Γ(T.left, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom.toAlgebra
    ext n
    exact (ConcreteCategory.congr_hom (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _) _).trans
      (SymmetricAlgebra.lift_ι_apply _ n)

/-- The `R`-linear map `N → Γ(T, ⊤)` of a point `t : T ⟶ Spec (Sym_R N)` sends `n` to the
pullback along `t` of the generator `n` of `Sym_R N`. -/
lemma specSymmetricAlgebraHomEquiv_apply (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)) (n : N) :
    specSymmetricAlgebraHomEquiv N T t n =
      ((Scheme.ΓSpecIso _).inv ≫ t.left.appTop) (SymmetricAlgebra.ι R N n) :=
  (rfl)

/-- The bijection `specSymmetricAlgebraHomEquiv` is natural in the scheme over `Spec R`:
composing a point with `g : T' ⟶ T` pulls back its linear map along `g`. -/
lemma specSymmetricAlgebraHomEquiv_comp {T' T : Over (Spec R)} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)) (n : N) :
    specSymmetricAlgebraHomEquiv N T' (g ≫ t) n =
      g.left.appTop (specSymmetricAlgebraHomEquiv N T t n) := by
  rw [specSymmetricAlgebraHomEquiv_apply, specSymmetricAlgebraHomEquiv_apply, Over.comp_left,
    Scheme.Hom.comp_appTop]
  rfl

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

/-- `Spec_X (Sym Ñ)` as a scheme over `X = Spec R`. -/
private abbrev relativeSpecTildeOver : Over (Spec R) :=
  (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
    (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N))))

/-- `Spec (Sym_R N)` as a scheme over `Spec R`. -/
private abbrev specSymmetricAlgebraOver' : Over (Spec R) :=
  (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)

/-- The morphism `Spec_X (Sym Ñ) ⟶ Spec (Sym_R N)` over `X = Spec R` whose linear map is that of
the identity of `Spec_X (Sym Ñ)`. -/
private def relativeSpecSymmetricAlgebraTildeHom :
    relativeSpecTildeOver N ⟶ specSymmetricAlgebraOver' N :=
  (specSymmetricAlgebraHomEquiv N (relativeSpecTildeOver N)).symm
    (relativeSpecSymmetricAlgebraTildeHomEquiv N (relativeSpecTildeOver N)
      (𝟙 (relativeSpecTildeOver N)))

/-- The morphism `Spec (Sym_R N) ⟶ Spec_X (Sym Ñ)` over `X = Spec R` whose linear map is that of
the identity of `Spec (Sym_R N)`. -/
private def relativeSpecSymmetricAlgebraTildeInv :
    specSymmetricAlgebraOver' N ⟶ relativeSpecTildeOver N :=
  (relativeSpecSymmetricAlgebraTildeHomEquiv N (specSymmetricAlgebraOver' N)).symm
    (specSymmetricAlgebraHomEquiv N (specSymmetricAlgebraOver' N)
      (𝟙 (specSymmetricAlgebraOver' N)))

private lemma specSymmetricAlgebraHomEquiv_tildeHom :
    specSymmetricAlgebraHomEquiv N (relativeSpecTildeOver N)
        (relativeSpecSymmetricAlgebraTildeHom N) =
      relativeSpecSymmetricAlgebraTildeHomEquiv N (relativeSpecTildeOver N)
        (𝟙 (relativeSpecTildeOver N)) :=
  (specSymmetricAlgebraHomEquiv N (relativeSpecTildeOver N)).apply_symm_apply _

private lemma relativeSpecSymmetricAlgebraTildeHomEquiv_tildeInv :
    relativeSpecSymmetricAlgebraTildeHomEquiv N (specSymmetricAlgebraOver' N)
        (relativeSpecSymmetricAlgebraTildeInv N) =
      specSymmetricAlgebraHomEquiv N (specSymmetricAlgebraOver' N)
        (𝟙 (specSymmetricAlgebraOver' N)) :=
  (relativeSpecSymmetricAlgebraTildeHomEquiv N (specSymmetricAlgebraOver' N)).apply_symm_apply _

private lemma specSymmetricAlgebraHomEquiv_comp_tildeHom (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N))))) :
    specSymmetricAlgebraHomEquiv N T (t ≫ relativeSpecSymmetricAlgebraTildeHom N) =
      relativeSpecSymmetricAlgebraTildeHomEquiv N T t := by
  refine ModuleCat.hom_ext (LinearMap.ext fun n ↦ ?_)
  refine (specSymmetricAlgebraHomEquiv_comp N t _ n).trans ?_
  refine (congrArg (fun φ ↦ t.left.appTop (φ n))
    (specSymmetricAlgebraHomEquiv_tildeHom N)).trans ?_
  exact (relativeSpecSymmetricAlgebraTildeHomEquiv_comp N t (𝟙 _) n).symm.trans
    (congrArg (fun s ↦ relativeSpecSymmetricAlgebraTildeHomEquiv N T s n) (Category.comp_id t))

private lemma relativeSpecSymmetricAlgebraTildeHomEquiv_comp_tildeInv (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)) :
    relativeSpecSymmetricAlgebraTildeHomEquiv N T (t ≫ relativeSpecSymmetricAlgebraTildeInv N) =
      specSymmetricAlgebraHomEquiv N T t := by
  refine ModuleCat.hom_ext (LinearMap.ext fun n ↦ ?_)
  refine (relativeSpecSymmetricAlgebraTildeHomEquiv_comp N t _ n).trans ?_
  refine (congrArg (fun φ ↦ t.left.appTop (φ n))
    (relativeSpecSymmetricAlgebraTildeHomEquiv_tildeInv N)).trans ?_
  exact (specSymmetricAlgebraHomEquiv_comp N t (𝟙 _) n).symm.trans
    (congrArg (fun s ↦ specSymmetricAlgebraHomEquiv N T s n) (Category.comp_id t))

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
  MorphismProperty.Over.isoMk
    { hom := (relativeSpecSymmetricAlgebraTildeHom N).left
      inv := (relativeSpecSymmetricAlgebraTildeInv N).left
      hom_inv_id := congrArg CommaMorphism.left <|
        (relativeSpecSymmetricAlgebraTildeHomEquiv N _).injective <|
          (relativeSpecSymmetricAlgebraTildeHomEquiv_comp_tildeInv N _ _).trans
            (specSymmetricAlgebraHomEquiv_tildeHom N)
      inv_hom_id := congrArg CommaMorphism.left <|
        (specSymmetricAlgebraHomEquiv N _).injective <|
          (specSymmetricAlgebraHomEquiv_comp_tildeHom N _ _).trans
            (relativeSpecSymmetricAlgebraTildeHomEquiv_tildeInv N) }
    (Over.w (relativeSpecSymmetricAlgebraTildeHom N))

/-- The isomorphism `Spec_X (Sym Ñ) ≅ Spec (Sym_R N)` preserves the linear maps `N → Γ(T, ⊤)` of
points. -/
lemma specSymmetricAlgebraHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_hom
    (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj N))))) :
    specSymmetricAlgebraHomEquiv N T
        (t ≫ (MorphismProperty.Over.forget _ _ _).map
          (relativeSpecSymmetricAlgebraTildeIso N).hom) =
      relativeSpecSymmetricAlgebraTildeHomEquiv N T t :=
  specSymmetricAlgebraHomEquiv_comp_tildeHom N T t

/-- The inverse isomorphism `Spec (Sym_R N) ≅ Spec_X (Sym Ñ)` preserves the linear maps
`N → Γ(T, ⊤)` of points. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv
    (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ _).obj (specSymmetricAlgebraOver R N)) :
    relativeSpecSymmetricAlgebraTildeHomEquiv N T
        (t ≫ (MorphismProperty.Over.forget _ _ _).map
          (relativeSpecSymmetricAlgebraTildeIso N).inv) =
      specSymmetricAlgebraHomEquiv N T t :=
  relativeSpecSymmetricAlgebraTildeHomEquiv_comp_tildeInv N T t

end TauCeti.AlgebraicGeometry
