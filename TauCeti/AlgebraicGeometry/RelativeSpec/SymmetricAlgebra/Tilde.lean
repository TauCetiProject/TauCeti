/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.Tilde
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic

/-!
# The relative spectrum of the symmetric algebra of `M~`

For a commutative ring `R` and an `R`-module `M`, the relative spectrum
`Spec_{Spec R} (Sym M~)` of the symmetric algebra of the associated quasicoherent sheaf `M~` is
the spectrum `Spec (Sym_R M)` of the symmetric algebra of `M`, as schemes over `Spec R`
(`relativeSpecSymmetricAlgebraTildeIso`). No finiteness, freeness or projectivity assumption on
`M` is needed.

Both schemes represent `R`-linear maps from `M` to global functions. For a scheme
`q : T ⟶ Spec R`, regard `Γ(T, ⊤)` as an `R`-module through `R ≅ Γ(Spec R, ⊤) ⟶ Γ(T, ⊤)`. Then:

* module maps `M~ ⟶ q_* 𝒪_T` are the `R`-linear maps `M → Γ(T, ⊤)`, by the adjunction between
  `~` and global sections (`Scheme.Hom.tildeHomPushforwardEquiv`), naturally in `T`
  (`Scheme.Hom.tildeHomPushforwardEquiv_comp`). Combined with the universal property of
  `Spec_X (Sym F)`, the points `T ⟶ Spec_{Spec R} (Sym M~)` over `Spec R` are these linear maps
  (`relativeSpecSymmetricAlgebraTildeHomEquiv`);
* morphisms `T ⟶ Spec (Sym_R M)` over `Spec R` are the `R`-algebra maps `Sym_R M → Γ(T, ⊤)`,
  hence again these linear maps, by the adjunction between `Spec` and global sections and the
  universal property of `Sym_R M`.

The isomorphism is built from these two descriptions. Its forward map corresponds to the
`R`-algebra map `Sym_R M → Γ(Spec_{Spec R} (Sym M~), ⊤)` extending the tautological linear map
(`relativeSpecSymmetricAlgebraTildeIso_hom_left_appTop_ι`), and its inverse is the point of
`Spec_{Spec R} (Sym M~)` over `Spec (Sym_R M)` given by the generators `m ∈ Sym_R M`
(`relativeSpecSymmetricAlgebraTildeHomEquiv_forget_map_inv_apply`).

This is the affine computation of `𝕍(F) = Spec_X (Sym F)` through the equivalence
`tildeEquiv` between `R`-modules and quasicoherent sheaves on `Spec R`.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraTildeHomEquiv`: points of
  `Spec_{Spec R} (Sym M~)` over `Spec R` are `R`-linear maps `M → Γ(T, ⊤)`;
* `TauCeti.AlgebraicGeometry.specSymmetricAlgebraOver M`: the scheme `Spec (Sym_R M)` as an affine
  scheme over `Spec R`;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraTildeIso`: the isomorphism
  `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)` of affine schemes over `Spec R`.

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

variable {R : CommRingCat.{u}}

variable (M : ModuleCat.{u} R)

/-- **Points of `Spec_{Spec R} (Sym M~)`.** For an `R`-module `M` and a scheme `q : T ⟶ Spec R`,
morphisms `T ⟶ Spec_{Spec R} (Sym M~)` over `Spec R` correspond to `R`-linear maps
`M → Γ(T, ⊤)`, where `R` acts on `Γ(T, ⊤)` through `R ≅ Γ(Spec R, ⊤) ⟶ Γ(T, ⊤)`. It is
`relativeSpecSymmetricAlgebraHomEquiv` followed by `Scheme.Hom.tildeHomPushforwardEquiv`. -/
def relativeSpecSymmetricAlgebraTildeHomEquiv (T : Over (Spec R)) :
    (T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M))))) ≃
      (M →ₛₗ[((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom] Γ(T.left, ⊤)) :=
  (relativeSpecSymmetricAlgebraHomEquiv _ T).trans (T.hom.tildeHomPushforwardEquiv M)

/-- The linear map of a point `t : T ⟶ Spec_{Spec R} (Sym M~)` over `Spec R` is that of its module
map `M~ ⟶ q_* 𝒪_T`. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_apply (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
      (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M))))) :
    relativeSpecSymmetricAlgebraTildeHomEquiv M T t =
      T.hom.tildeHomPushforwardEquiv M (relativeSpecSymmetricAlgebraHomEquiv _ T t) :=
  (rfl)

/-- The bijection `relativeSpecSymmetricAlgebraTildeHomEquiv` is natural in the scheme over
`Spec R`: composing a point with `g : T' ⟶ T` over `Spec R` composes its linear map with pullback
of global functions along `g`. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_comp {T' T : Over (Spec R)} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
      (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M))))) (m : M) :
    relativeSpecSymmetricAlgebraTildeHomEquiv M T' (g ≫ t) m =
      g.left.appTop (relativeSpecSymmetricAlgebraTildeHomEquiv M T t m) := by
  rw [relativeSpecSymmetricAlgebraTildeHomEquiv_apply, relativeSpecSymmetricAlgebraHomEquiv_comp]
  exact Scheme.Hom.tildeHomPushforwardEquiv_comp g.left (Over.w g) M _ m

-- The body is exposed so that the underlying scheme and structure morphism compute, as for
-- `affineSpaceOver`.
/-- The spectrum `Spec (Sym_R M)` of the symmetric algebra of an `R`-module `M`, as an affine
scheme over `Spec R`. -/
@[expose]
def specSymmetricAlgebraOver : AffineSchemeOver (Spec R) :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M))))
    inferInstance

/-- The underlying scheme of `specSymmetricAlgebraOver M` is `Spec (Sym_R M)`. -/
@[simp]
lemma specSymmetricAlgebraOver_left :
    (specSymmetricAlgebraOver M).left = Spec (.of (SymmetricAlgebra R M)) :=
  (rfl)

/-- The structure morphism of `specSymmetricAlgebraOver M` is `Spec` of `R → Sym_R M`. -/
@[simp]
lemma specSymmetricAlgebraOver_hom :
    (specSymmetricAlgebraOver M).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M))) :=
  (rfl)

/-- The relative spectrum `Spec_{Spec R} (Sym M~)`. -/
private abbrev relSpec : AffineSchemeOver (Spec R) :=
  (relativeSpec (Spec R)).obj
    (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M)))

/-- The linear map `M → Γ(Spec_{Spec R} (Sym M~), ⊤)` of the identity point. -/
private abbrev tautological :=
  relativeSpecSymmetricAlgebraTildeHomEquiv M ((MorphismProperty.Over.forget _ _ _).obj (relSpec M))
    (𝟙 _)

/-- The ring map `Sym_R M → Γ(Spec_{Spec R} (Sym M~), ⊤)` extending the tautological linear map,
which is semilinear over `R ≅ Γ(Spec R, ⊤) ⟶ Γ(Spec_{Spec R} (Sym M~), ⊤)`. -/
private def toSpecRingHom :
    CommRingCat.of (SymmetricAlgebra R M) ⟶ Γ((relSpec M).left, ⊤) :=
  letI : Algebra R Γ((relSpec M).left, ⊤) :=
    ((Scheme.ΓSpecIso R).inv ≫ (relSpec M).hom.appTop).hom.toAlgebra
  CommRingCat.ofHom (SymmetricAlgebra.lift (R := R) (M := M) (A := Γ((relSpec M).left, ⊤))
    { toFun := tautological M, map_add' := (tautological M).map_add,
      map_smul' := (tautological M).map_smulₛₗ }).toRingHom

private lemma toSpecRingHom_ι (m : M) :
    toSpecRingHom M (SymmetricAlgebra.ι R M m) = tautological M m := by
  let _ : Algebra R Γ((relSpec M).left, ⊤) :=
    ((Scheme.ΓSpecIso R).inv ≫ (relSpec M).hom.appTop).hom.toAlgebra
  exact SymmetricAlgebra.lift_ι_apply (A := Γ((relSpec M).left, ⊤)) _ m

private lemma algebraMap_comp_toSpecRingHom :
    CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M)) ≫ toSpecRingHom M =
      (Scheme.ΓSpecIso R).inv ≫ (relSpec M).hom.appTop := by
  let _ : Algebra R Γ((relSpec M).left, ⊤) :=
    ((Scheme.ΓSpecIso R).inv ≫ (relSpec M).hom.appTop).hom.toAlgebra
  ext r
  exact AlgHom.commutes (SymmetricAlgebra.lift (R := R) (M := M) (A := Γ((relSpec M).left, ⊤))
    { toFun := tautological M, map_add' := (tautological M).map_add,
      map_smul' := (tautological M).map_smulₛₗ }) r

/-- The forward map `Spec_{Spec R} (Sym M~) ⟶ Spec (Sym_R M)`. -/
private def toSpecLeft : (relSpec M).left ⟶ Spec (.of (SymmetricAlgebra R M)) :=
  (relSpec M).left.toSpecΓ ≫ Spec.map (toSpecRingHom M)

private lemma toSpecLeft_comp :
    toSpecLeft M ≫ (specSymmetricAlgebraOver M).hom = (relSpec M).hom := by
  rw [toSpecLeft, specSymmetricAlgebraOver_hom, Category.assoc, ← Spec.map_comp,
    algebraMap_comp_toSpecRingHom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  exact (congrArg _ (toSpecΓ_SpecMap_ΓSpecIso_inv R)).trans (Category.comp_id _)

/-- The linear map `M → Γ(Spec (Sym_R M), ⊤)` given by the generators of `Sym_R M`. -/
private def ofSpecLinear :
    M →ₛₗ[((Scheme.ΓSpecIso R).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M)))).appTop).hom]
      Γ(Spec (.of (SymmetricAlgebra R M)), ⊤) where
  toFun m := (Scheme.ΓSpecIso _).inv (SymmetricAlgebra.ι R M m)
  map_add' m n := by rw [map_add, map_add]
  map_smul' r m := by
    rw [map_smul, Algebra.smul_def, map_mul, smul_eq_mul, ← Scheme.ΓSpecIso_inv_naturality]
    -- Both sides are the product of `R → Γ(Spec (Sym_R M), ⊤)` at `r` with the generator.
    rfl

/-- The inverse point of `Spec_{Spec R} (Sym M~)` over `Spec (Sym_R M)`. -/
private def ofSpec :
    (MorphismProperty.Over.forget _ _ (Spec R)).obj (specSymmetricAlgebraOver M) ⟶
      (MorphismProperty.Over.forget _ _ (Spec R)).obj (relSpec M) :=
  (relativeSpecSymmetricAlgebraTildeHomEquiv M _).symm (ofSpecLinear M)

-- A separate name for the underlying morphism keeps the `Over` category of the source, whose
-- morphism property is only definitionally a `MorphismProperty`, out of rewriting motives.
/-- The underlying morphism `Spec (Sym_R M) ⟶ Spec_{Spec R} (Sym M~)` of `ofSpec`. -/
private def ofSpecLeft : Spec (.of (SymmetricAlgebra R M)) ⟶ (relSpec M).left :=
  (ofSpec M).left

private lemma relativeSpecSymmetricAlgebraTildeHomEquiv_ofSpec :
    relativeSpecSymmetricAlgebraTildeHomEquiv M _ (ofSpec M) = ofSpecLinear M :=
  Equiv.apply_symm_apply _ _

/-- `Γ(toSpecLeft)` sends the generator `m` to the tautological linear map at `m`. -/
private lemma ΓSpecIso_inv_comp_toSpecLeft_appTop :
    (Scheme.ΓSpecIso _).inv ≫ (toSpecLeft M).appTop = toSpecRingHom M := by
  rw [toSpecLeft, Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

private lemma homMk_toSpecLeft_comp_ofSpec :
    (Over.homMk (V := (MorphismProperty.Over.forget _ _ (Spec R)).obj (specSymmetricAlgebraOver M))
      (toSpecLeft M) (toSpecLeft_comp M)) ≫ ofSpec M = 𝟙 _ := by
  apply (relativeSpecSymmetricAlgebraTildeHomEquiv M _).injective
  ext m
  refine (relativeSpecSymmetricAlgebraTildeHomEquiv_comp M _ _ m).trans ?_
  rw [relativeSpecSymmetricAlgebraTildeHomEquiv_ofSpec]
  exact (ConcreteCategory.congr_hom (ΓSpecIso_inv_comp_toSpecLeft_appTop M)
    (SymmetricAlgebra.ι R M m)).trans (toSpecRingHom_ι M m)

private lemma toSpecRingHom_comp_ofSpecLeft_appTop :
    toSpecRingHom M ≫ (ofSpecLeft M).appTop = (Scheme.ΓSpecIso _).inv := by
  ext : 1
  refine SymmetricAlgebra.ringHom_ext ?_ fun m ↦ ?_
  · -- On scalars both maps are `R ⟶ Γ(Spec R, ⊤) ⟶ Γ(Spec (Sym_R M), ⊤)`, since `ofSpec` lies over
    -- `Spec R`.
    have h : CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M)) ≫ toSpecRingHom M ≫
        (ofSpecLeft M).appTop =
          CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M)) ≫ (Scheme.ΓSpecIso _).inv := by
      -- `Over.w (ofSpec M)` is stated in the `Over` category of the source, so it needs `erw`.
      erw [← Category.assoc, algebraMap_comp_toSpecRingHom, Category.assoc,
        ← Scheme.Hom.comp_appTop, Over.w (ofSpec M)]
      exact (Scheme.ΓSpecIso_inv_naturality _).symm
    exact congrArg CommRingCat.Hom.hom h
  · refine (congrArg (ofSpec M).left.appTop (toSpecRingHom_ι M m)).trans ?_
    refine (relativeSpecSymmetricAlgebraTildeHomEquiv_comp M (ofSpec M) (𝟙 _) m).symm.trans ?_
    rw [Category.comp_id, relativeSpecSymmetricAlgebraTildeHomEquiv_ofSpec]
    -- `ofSpecLinear M m` is the generator `m`, by definition.
    rfl

private lemma ofSpecLeft_comp_toSpecLeft : ofSpecLeft M ≫ toSpecLeft M = 𝟙 _ := by
  have h := Scheme.toSpecΓ_naturality (ofSpecLeft M)
  have h' : Spec.map ((ofSpecLeft M).appTop) ≫ Spec.map (toSpecRingHom M) =
      Spec.map (Scheme.ΓSpecIso _).inv := by
    rw [← Spec.map_comp, toSpecRingHom_comp_ofSpecLeft_appTop]
  rw [toSpecLeft, ← Category.assoc, h, Category.assoc, h']
  exact toSpecΓ_SpecMap_ΓSpecIso_inv _

/-- **`Spec_{Spec R} (Sym M~)` is `Spec (Sym_R M)`.** For an `R`-module `M`, the relative spectrum
of the symmetric algebra of the associated quasicoherent sheaf `M~` on `Spec R` is isomorphic over
`Spec R` to the spectrum of the symmetric algebra of `M`. The forward map is characterised by
`relativeSpecSymmetricAlgebraTildeIso_hom_left_appTop_ι` and the inverse by
`relativeSpecSymmetricAlgebraTildeHomEquiv_forget_map_inv_apply`. -/
def relativeSpecSymmetricAlgebraTildeIso :
    (relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M))) ≅
      specSymmetricAlgebraOver M :=
  MorphismProperty.Over.isoMk
    { hom := toSpecLeft M
      inv := ofSpecLeft M
      hom_inv_id := congrArg CommaMorphism.left (homMk_toSpecLeft_comp_ofSpec M)
      inv_hom_id := ofSpecLeft_comp_toSpecLeft M }
    (toSpecLeft_comp M)

-- Not a simp lemma: simp unfolds `symmetricAlgebra` in the type of its left-hand side.
/-- The forward isomorphism `Spec_{Spec R} (Sym M~) ⟶ Spec (Sym_R M)` pulls the generator
`m ∈ Sym_R M` back to the global function at `m` of the tautological linear map, that is of the
identity point of `Spec_{Spec R} (Sym M~)`. -/
lemma relativeSpecSymmetricAlgebraTildeIso_hom_left_appTop_ι (m : M) :
    (relativeSpecSymmetricAlgebraTildeIso M).hom.left.appTop
        ((Scheme.ΓSpecIso _).inv (SymmetricAlgebra.ι R M m)) =
      relativeSpecSymmetricAlgebraTildeHomEquiv M _ (𝟙 _) m :=
  (ConcreteCategory.congr_hom (ΓSpecIso_inv_comp_toSpecLeft_appTop M)
    (SymmetricAlgebra.ι R M m)).trans (toSpecRingHom_ι M m)

/-- The inverse isomorphism `Spec (Sym_R M) ⟶ Spec_{Spec R} (Sym M~)`, as a point of
`Spec_{Spec R} (Sym M~)` over `Spec R`, is the linear map sending `m` to the generator `m` of
`Sym_R M`, viewed as a global function on `Spec (Sym_R M)`. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_forget_map_inv_apply (m : M) :
    relativeSpecSymmetricAlgebraTildeHomEquiv M _
        ((MorphismProperty.Over.forget _ _ (Spec R)).map
          (relativeSpecSymmetricAlgebraTildeIso M).inv) m =
      (Scheme.ΓSpecIso _).inv (SymmetricAlgebra.ι R M m) :=
  DFunLike.congr_fun (relativeSpecSymmetricAlgebraTildeHomEquiv_ofSpec M) m

end TauCeti.AlgebraicGeometry

end
