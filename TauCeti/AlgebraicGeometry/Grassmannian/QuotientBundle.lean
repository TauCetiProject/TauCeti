/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.AlgebraicGeometry.Modules.AffineSubmodule
public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic

import TauCeti.AlgebraicGeometry.AffineScheme.Basic

/-!
# The universal quotient bundle on the Grassmannian scheme

Let `R` be a commutative ring, `M` an `R`-module and `k` a natural number, and write
`π : G(k, M) ⟶ Spec R` for the Grassmannian scheme `Module.Grassmannian.scheme R M k`. This file
constructs the **universal quotient** of `π^* M~` on `G(k, M)`: a finite locally free
`𝒪_{G(k, M)}`-module `Q` with an epimorphism `π^* M~ ⟶ Q`
(`Module.Grassmannian.universalQuotientπ`), whose sections over every affine open `U` are
`(Γ(G(k, M), U) ⊗[R] M) ⧸ N_U`, where `N_U` is the point of `G(k, Γ(G(k, M), U) ⊗[R] M)`
classified by the inclusion `Spec Γ(G(k, M), U) ⟶ G(k, M)` (`Module.Grassmannian.sectionsPoint`),
so that `Q` is locally free of rank `k`.

The construction needs no gluing of modules along the charts. The points `N_U` are compatible with
restriction: for affine opens `V ≤ U`, `N_V` is the base change of `N_U` along
`Γ(G(k, M), U) → Γ(G(k, M), V)` (`Module.Grassmannian.map_sectionsPoint`), by naturality of the
functor of points. Over an affine open `U`, pulling back sections exhibits `Γ(π^* M~, U)` as
`Γ(G(k, M), U) ⊗[R] M` (`Module.Grassmannian.isBaseChange_sectionsLinearMap`), so the `N_U` form
submodules of the sections of `π^* M~` over the affine opens, compatible with restriction. They
are the sections of the quasi-coherent kernel of the universal quotient
(`AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData`), and the universal quotient is the
cokernel of its inclusion.

## Main definitions

* `Module.Grassmannian.sectionsPoint U`: the point of `G(k, Γ(G(k, M), U) ⊗[R] M)` classified by the
  inclusion of an affine open `U`.
* `Module.Grassmannian.universalKernelData R M k`: the submodules `N_U` of the sections of
  `π^* M~` over the affine opens `U`.
* `Module.Grassmannian.universalQuotient R M k`: the universal quotient `Q`, with its projection
  `Module.Grassmannian.universalQuotientπ R M k : π^* M~ ⟶ Q`.
* `Module.Grassmannian.sectionsUniversalQuotientEquiv U`: over an affine open `U`, the sections
  of `Q` are `(Γ(G(k, M), U) ⊗[R] M) ⧸ N_U`.

## Main results

* `Module.Grassmannian.toSchemeHom_sectionsPoint`: the point `N_U` classifies the inclusion of `U`.
* `Module.Grassmannian.map_sectionsPoint`: the points `N_U` are compatible with restriction.
* `Module.Grassmannian.isFiniteLocallyFree_universalQuotient`: the universal quotient is finite
  locally free, and its sections over every affine open have rank `k` at every prime
  (`Module.Grassmannian.rankAtStalk_sectionsUniversalQuotient`).

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  the Grassmannian and its universal quotient.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (k : ℕ)

variable (R) in
/-- The `R`-algebra structure on the functions on an open `U` of the Grassmannian scheme
`G(k, M)`, through its structure morphism to `Spec R`. -/
abbrev sectionsAlgebra (U : (scheme R M k).Opens) : Algebra R Γ(scheme R M k, U) :=
  (((toSpec R M k).appLE ⊤ U le_top).hom.comp (algebraMap R Γ(Spec R, ⊤))).toAlgebra

attribute [local instance] sectionsAlgebra

/-- The algebra map `R → Γ(G(k, M), U)` is the composite of `R → Γ(Spec R, ⊤)` with the map on
functions of the structure morphism. -/
theorem sectionsAlgebra_algebraMap (U : (scheme R M k).Opens) (r : R) :
    algebraMap R Γ(scheme R M k, U) r =
      (toSpec R M k).appLE ⊤ U le_top (algebraMap R Γ(Spec R, ⊤) r) :=
  (rfl)

/-- On an affine open `U`, the inclusion `Spec Γ(G(k, M), U) ⟶ G(k, M)` lies over `Spec R`. -/
theorem fromSpec_toSpec (U : (scheme R M k).affineOpens) :
    U.property.fromSpec ≫ toSpec R M k =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(scheme R M k, U))) := by
  refine (IsAffineOpen.fromSpec_comp_eq_SpecMap _ U.property).trans ?_
  congr 1

/-- The point of `G(k, Γ(G(k, M), U) ⊗[R] M)` classified by the inclusion of an affine open `U` of
the Grassmannian scheme: its quotient is the universal quotient over `U`. -/
def sectionsPoint (U : (scheme R M k).affineOpens) :
    G(k, Γ(scheme R M k, U) ⊗[R] M; Γ(scheme R M k, U)) :=
  (schemeHomEquiv R M k Γ(scheme R M k, U)).symm ⟨U.property.fromSpec, fromSpec_toSpec M k U⟩

/-- **The point `N_U` classifies the inclusion of `U`.** -/
@[simp]
theorem toSchemeHom_sectionsPoint (U : (scheme R M k).affineOpens) :
    toSchemeHom (sectionsPoint M k U) = U.property.fromSpec :=
  toSchemeHom_schemeHomEquiv_symm_apply _

/-- Restriction of functions from an open `U` of `G(k, M)` to an open `V ≤ U`, as a map of
`R`-algebras. -/
def restrictAlgHom {U V : (scheme R M k).Opens} (h : V ≤ U) :
    Γ(scheme R M k, U) →ₐ[R] Γ(scheme R M k, V) where
  toRingHom := ((scheme R M k).presheaf.map (homOfLE h).op).hom
  commutes' r := by
    have := (toSpec R M k).appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op
    exact congrArg (fun φ ↦ φ.hom (algebraMap R Γ(Spec R, ⊤) r)) this

/-- `restrictAlgHom` is restriction of functions. -/
@[simp]
theorem restrictAlgHom_apply {U V : (scheme R M k).Opens} (h : V ≤ U) (a : Γ(scheme R M k, U)) :
    restrictAlgHom M k h a = (scheme R M k).presheaf.map (homOfLE h).op a :=
  (rfl)

/-- **The points `N_U` are compatible with restriction.** For affine opens `V ≤ U` of `G(k, M)`,
the point classified by `V` is the base change of the point classified by `U` along restriction
of functions. -/
theorem map_sectionsPoint {U V : (scheme R M k).affineOpens} (h : (V : (scheme R M k).Opens) ≤ U) :
    map (restrictAlgHom M k h) (sectionsPoint M k U) = sectionsPoint M k V := by
  refine toSchemeHom_injective ?_
  rw [toSchemeHom_map, toSchemeHom_sectionsPoint, toSchemeHom_sectionsPoint]
  exact IsAffineOpen.map_fromSpec U.property V.property (homOfLE h).op

variable (R) in
/-- The pullback `π^* M~` along the structure morphism `π : G(k, M) ⟶ Spec R` of the
quasi-coherent module `M~` on `Spec R`. The universal quotient is a quotient of it. -/
abbrev pullbackTilde : (scheme R M k).Modules :=
  (Scheme.Modules.pullback (toSpec R M k)).obj (tilde M)

variable (R) in
/-- The `R`-module structure on the sections of `π^* M~` over an open `U` of `G(k, M)`, by
restriction of scalars along `R → Γ(G(k, M), U)`. -/
abbrev sectionsModule (U : (scheme R M k).Opens) : Module R Γ(pullbackTilde R M k, U) :=
  Module.compHom _ (algebraMap R Γ(scheme R M k, U))

attribute [local instance] sectionsModule

instance (U : (scheme R M k).Opens) :
    IsScalarTower R Γ(scheme R M k, U) Γ(pullbackTilde R M k, U) :=
  IsScalarTower.of_compHom _ _ _

/-- The `R`-linear map `M → Γ(π^* M~, U)` pulling back the global section `m` of `M~` to an open
`U` of `G(k, M)`. Over an affine open `U` it exhibits `Γ(π^* M~, U)` as the base change of `M`
along `R → Γ(G(k, M), U)` (`Module.Grassmannian.isBaseChange_sectionsLinearMap`). -/
def sectionsLinearMap (U : (scheme R M k).Opens) : M →ₗ[R] Γ(pullbackTilde R M k, U) where
  toFun m := (toSpec R M k).pullbackSectionsLE (tilde M) ⊤ U le_top (tildeToTop M m)
  map_add' m m' := by rw [map_add, map_add]
  map_smul' r m := by
    rw [map_smul, ← algebraMap_smul Γ(Spec R, ⊤) r (tildeToTop M m), map_smulₛₗ]
    rfl

/-- `sectionsLinearMap` pulls back global sections of `M~`. -/
theorem sectionsLinearMap_apply (U : (scheme R M k).Opens) (m : M) :
    sectionsLinearMap M k U m =
      (toSpec R M k).pullbackSectionsLE (tilde M) ⊤ U le_top (tildeToTop M m) :=
  (rfl)

/-- Pulling back global sections of `M~` commutes with restriction of sections of `π^* M~`. -/
theorem map_sectionsLinearMap {U V : (scheme R M k).Opens} (h : V ≤ U) (m : M) :
    (pullbackTilde R M k).presheaf.map (homOfLE h).op (sectionsLinearMap M k U m) =
      sectionsLinearMap M k V m :=
  Scheme.Hom.presheaf_map_pullbackSectionsLE _ _ _ _ _ _ _

/-- **Sections of `π^* M~` over an affine open are a base change of `M`.** Over an affine open `U`
of `G(k, M)`, pulling back global sections of `M~` exhibits `Γ(π^* M~, U)` as
`Γ(G(k, M), U) ⊗[R] M`. -/
theorem isBaseChange_sectionsLinearMap (U : (scheme R M k).affineOpens) :
    IsBaseChange Γ(scheme R M k, U) (sectionsLinearMap M k U) := by
  let : Algebra Γ(Spec R, ⊤) Γ(scheme R M k, U) :=
    ((toSpec R M k).appLE ⊤ U le_top).hom.toAlgebra
  let : Module Γ(Spec R, ⊤) Γ(pullbackTilde R M k, U) :=
    Module.compHom _ (algebraMap Γ(Spec R, ⊤) Γ(scheme R M k, U))
  have : IsScalarTower Γ(Spec R, ⊤) Γ(scheme R M k, U) Γ(pullbackTilde R M k, U) :=
    IsScalarTower.of_compHom _ _ _
  have : IsScalarTower R Γ(Spec R, ⊤) Γ(scheme R M k, U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R Γ(Spec R, ⊤) Γ(pullbackTilde R M k, U) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let φ : Γ(tilde M, ⊤) →ₗ[Γ(Spec R, ⊤)] Γ(pullbackTilde R M k, U) :=
    { toFun := (toSpec R M k).pullbackSectionsLE (tilde M) ⊤ U le_top
      map_add' := map_add _
      map_smul' := fun r s ↦ (toSpec R M k).pullbackSectionsLE (tilde M) ⊤ U le_top |>.map_smulₛₗ
        r s }
  have h := (isBaseChange_tildeToTop M).comp
    ((toSpec R M k).isBaseChange_pullbackSectionsLE (tilde M) (isAffineOpen_top _) U.property
      le_top (fun _ ↦ rfl) φ (fun _ ↦ rfl))
  exact h

/-- The identification `Γ(G(k, M), U) ⊗[R] M ≃ Γ(π^* M~, U)` over an affine open `U`, sending
`a ⊗ m` to `a` times the pullback of the global section `m` of `M~`. -/
def sectionsEquiv (U : (scheme R M k).affineOpens) :
    Γ(scheme R M k, U) ⊗[R] M ≃ₗ[Γ(scheme R M k, U)] Γ(pullbackTilde R M k, U) :=
  (isBaseChange_sectionsLinearMap M k U).equiv

/-- `sectionsEquiv` sends `a ⊗ m` to `a` times the pullback of `m`. -/
@[simp]
theorem sectionsEquiv_tmul (U : (scheme R M k).affineOpens) (a : Γ(scheme R M k, U)) (m : M) :
    sectionsEquiv M k U (a ⊗ₜ m) = a • sectionsLinearMap M k U m :=
  IsBaseChange.equiv_tmul _ _ _

/-- `sectionsEquiv` commutes with restriction to a smaller affine open. -/
theorem sectionsEquiv_rTensor {U V : (scheme R M k).affineOpens}
    (h : (V : (scheme R M k).Opens) ≤ U) (x : Γ(scheme R M k, U) ⊗[R] M) :
    sectionsEquiv M k V ((restrictAlgHom M k h).toLinearMap.rTensor M x) =
      (pullbackTilde R M k).presheaf.map (homOfLE h).op (sectionsEquiv M k U x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [LinearMap.rTensor_tmul, sectionsEquiv_tmul, sectionsEquiv_tmul, Scheme.Modules.map_smul,
      map_sectionsLinearMap]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The submodule `N_U` of `Γ(π^* M~, U)` over an affine open `U`: the image under `sectionsEquiv`
of the point `sectionsPoint U` classified by `U`. -/
def sectionsKernel (U : (scheme R M k).affineOpens) :
    Submodule Γ(scheme R M k, U) Γ(pullbackTilde R M k, U) :=
  (sectionsPoint M k U).toSubmodule.map (sectionsEquiv M k U).toLinearMap

/-- For affine opens `V ≤ U`, the submodule `N_V` is spanned by the restrictions of `N_U`. -/
theorem sectionsKernel_eq_span {U V : (scheme R M k).affineOpens}
    (h : (V : (scheme R M k).Opens) ≤ U) :
    sectionsKernel M k V = Submodule.span Γ(scheme R M k, V)
      ((pullbackTilde R M k).presheaf.map (homOfLE h).op '' sectionsKernel M k U) := by
  rw [sectionsKernel, ← map_sectionsPoint M k h, map_toSubmodule_eq_span, Submodule.map_span,
    sectionsKernel, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ ↦ sectionsEquiv_rTensor M k h x

variable (R) in
/-- The submodules `N_U` of the sections of `π^* M~` over the affine opens `U` of `G(k, M)`,
compatible with restriction. They are the sections of the kernel of the universal quotient. -/
@[expose]
def universalKernelData : (pullbackTilde R M k).AffineSubmoduleData where
  submodule U := sectionsKernel M k U
  submodule_eq_span h := sectionsKernel_eq_span M k h

variable (R) in
/-- The **universal quotient** on the Grassmannian scheme `G(k, M)`: the quotient of `π^* M~` by
the quasi-coherent submodule whose sections over each affine open `U` are the point `N_U`
classified by `U`. It is finite locally free
(`Module.Grassmannian.isFiniteLocallyFree_universalQuotient`), of rank `k`
(`Module.Grassmannian.rankAtStalk_sectionsUniversalQuotient`). -/
@[expose]
def universalQuotient : (scheme R M k).Modules :=
  (universalKernelData R M k).quotient

variable (R) in
/-- The projection `π^* M~ ⟶ Q` onto the universal quotient. -/
@[expose]
def universalQuotientπ : pullbackTilde R M k ⟶ universalQuotient R M k :=
  (universalKernelData R M k).π

instance : Epi (universalQuotientπ R M k) :=
  inferInstanceAs (Epi (universalKernelData R M k).π)

/-- The universal quotient is quasi-coherent. -/
instance isQuasicoherent_universalQuotient : (universalQuotient R M k).IsQuasicoherent :=
  inferInstanceAs (universalKernelData R M k).quotient.IsQuasicoherent

/-- **Sections of the universal quotient over an affine open.** Over an affine open `U` of
`G(k, M)`, the sections of the universal quotient are the quotient of `Γ(G(k, M), U) ⊗[R] M` by the
point `N_U` classified by `U`. -/
def sectionsUniversalQuotientEquiv (U : (scheme R M k).affineOpens) :
    Γ(universalQuotient R M k, U) ≃ₗ[Γ(scheme R M k, U)]
      (Γ(scheme R M k, U) ⊗[R] M) ⧸ (sectionsPoint M k U).toSubmodule :=
  (universalKernelData R M k).sectionsQuotientEquiv U ≪≫ₗ
    Submodule.Quotient.equiv _ _ (sectionsEquiv M k U).symm
      ((Submodule.map_symm_eq_iff _).2 rfl)

/-- Under `sectionsUniversalQuotientEquiv`, the projection `π^* M~ ⟶ Q` is the quotient map
`Γ(G(k, M), U) ⊗[R] M → (Γ(G(k, M), U) ⊗[R] M) ⧸ N_U`. -/
@[simp]
theorem sectionsUniversalQuotientEquiv_π_app (U : (scheme R M k).affineOpens)
    (x : Γ(scheme R M k, U) ⊗[R] M) :
    sectionsUniversalQuotientEquiv M k U
        ((universalQuotientπ R M k).app U (sectionsEquiv M k U x)) =
      Submodule.Quotient.mk x := by
  have h := (universalKernelData R M k).sectionsQuotientEquiv_π_app U (sectionsEquiv M k U x)
  exact (congrArg (Submodule.Quotient.equiv _ _ (sectionsEquiv M k U).symm
    ((Submodule.map_symm_eq_iff _).2 rfl)) h).trans
    (congrArg Submodule.Quotient.mk ((sectionsEquiv M k U).symm_apply_apply x))

/-- **The universal quotient is finite locally free**: over every affine open `U` its sections are
the quotient of `Γ(G(k, M), U) ⊗[R] M` by a point of the Grassmannian, which is finitely generated
and projective. -/
theorem isFiniteLocallyFree_universalQuotient :
    Scheme.Modules.isFiniteLocallyFree _ (universalQuotient R M k) :=
  (Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen _).2 fun U hU ↦
    let e := sectionsUniversalQuotientEquiv M k ⟨U, hU⟩
    ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- **The universal quotient has rank `k`**: over every affine open `U`, its sections have rank `k`
at every prime of `Γ(G(k, M), U)`. -/
theorem rankAtStalk_sectionsUniversalQuotient (U : (scheme R M k).affineOpens)
    (p : PrimeSpectrum Γ(scheme R M k, U)) :
    Module.rankAtStalk (R := Γ(scheme R M k, U)) Γ(universalQuotient R M k, U) p = k := by
  rw [Module.rankAtStalk_eq_of_equiv (sectionsUniversalQuotientEquiv M k U)]
  exact (sectionsPoint M k U).rankAtStalk_eq p

end Module.Grassmannian
