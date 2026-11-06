/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.AlgebraicGeometry.Cohomology.Cech.Linear
public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Scheme.Opens
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor

/-!
# Base change for the Čech cohomology of quasi-coherent sheaves

Let `X` be a scheme over a commutative ring `R`, let `R → R'` be a ring map and let
`Y = X ×_R R'` be the base change, given as a pullback square `H` with projection `g : Y ⟶ X`.
Let `M` be a quasi-coherent sheaf on `X` and `U` a finite family of opens covering `X` whose
nonempty finite intersections are affine; for instance an affine open cover of a quasi-compact
scheme with affine diagonal. This file shows that the Čech complex `Č(U, M)` of `R`-modules of
sections computes the cohomology of every base change: `Hⁿ(Y, g^* M)` is the `n`-th cohomology of
`R' ⊗_R Č(U, M)`, with no flatness of `R → R'`. When the sections of `M` over the finite
intersections of `U` are flat `R`-modules, for instance when its sections over affine opens are,
every term of `Č(U, M)` is flat (`TauCeti.CategoryTheory.flat_cechComplexFunctor_obj_X`).
Together, for such `M`, these are the first step of the theory of cohomology and base change: the
cohomology of all the base changes of `M`, in particular of all its fibres `X ×_R κ(p)`, is
computed by a single complex of flat `R`-modules.

When `R → R'` is flat, extension of scalars commutes with taking cohomology, which gives flat base
change `Hⁿ(Y, g^* M) ≅ R' ⊗_R Hⁿ(X, M)` in every degree `n`.

The proof computes both sides by Čech complexes. The inverse images `g⁻¹ U` form a cover of `Y` of
the same kind, because `g` is affine. By Leray's theorem, `Hⁿ(X, M)` is the cohomology of
`Č(U, M)`, and likewise on `Y` (`AlgebraicGeometry.Scheme.Modules.homologyCechComplexLinearEquiv`).
On an affine open `W` of `X`, the sections of `g^* M` over `g⁻¹ W` are the base change of the
sections of `M` over `W` (`AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSections`), with no
flatness hypothesis. As the finite intersections of `U` are affine, `R' ⊗_R Č(U, M)` is therefore
the Čech complex of `g^* M` for `g⁻¹ U`.

The base change of the Čech complex is an explicit isomorphism of complexes
(`TauCeti.AlgebraicGeometry.cechComplexBaseChangeIso`), while the isomorphisms on cohomology are
stated as `Nonempty` linear equivalences: their construction depends on the chosen cover, and no
naturality is claimed. For a quasi-compact scheme with affine diagonal, the
canonical map `R' ⊗_R Hⁿ(X, M) ⟶ Hⁿ(Y, g^* M)` induced by pullback is an isomorphism when `R → R'`
is flat (`TauCeti.AlgebraicGeometry.bijective_cohomologyBaseChange`); its proof uses flat base
change here to see that `g^*` preserves the vanishing of higher cohomology. Flat base change in
degrees zero and one on a two-affine cover, along any base-ring map in degree one, is in
`TauCeti.AlgebraicGeometry.Cohomology.BaseChange`.

## Main definitions

* `TauCeti.AlgebraicGeometry.sectionsPullbackExtend`: the map of presheaves of `R'`-modules
  `R' ⊗_R Γ(M, -) ⟶ Γ(g^* M, g⁻¹ -)`, `s ⊗ m ↦ s • g^* m`, adjoint to pulling back sections
  (`extendRestrictScalarsAdj_homEquiv_sectionsPullbackExtend_app_hom_apply`).
* `TauCeti.AlgebraicGeometry.cechComplexBaseChangeIso`: the isomorphism of complexes
  `R' ⊗_R Č(U, M) ≅ Č(g⁻¹ U, g^* M)`, along any ring map `R → R'`. Its factors are the components
  of `sectionsPullbackExtend` (`cechComplexBaseChangeIso_hom_f_π`).

## Main results

All in the namespace `TauCeti.AlgebraicGeometry`:

* `nonempty_linearEquiv_homology_extendScalars_cechComplex_cohomology_pullback_of_iSup_eq_top`:
  `Hⁿ(Y, g^* M)` is the cohomology of `R' ⊗_R Č(U, M)`, along any ring map `R → R'`.
* `nonempty_linearEquiv_tensor_cohomology_pullback_of_iSup_eq_top`:
  flat base change for a finite cover with affine intersections.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change), and the Čech
  complex in the proof of Proposition III.12.2 (cohomology of all base changes).
* D. Mumford, *Abelian Varieties*, Section 5 (the Čech complex in the proof of the main lemma).
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base change.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite TensorProduct
open TauCeti.CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

section FlatBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  {R' : Type u} [CommRing R'] [Algebra R R'] {Y : Scheme.{u}} [Y.Over (Spec (.of R'))]
  {g : Y ⟶ X}
  (C : CommSq g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
  (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

/-- The presheaf of `R'`-modules of sections of `g^* M` over the inverse images of the opens of
`X`. -/
private abbrev pullbackSectionsPresheaf (g : Y ⟶ X) (M : X.Modules) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} R' :=
  (Opens.map g.base).op ⋙ (sectionsBasePresheafFunctor R').obj ((Scheme.Modules.pullback g).obj M)

section SectionsPullback

variable (M : X.Modules) (W : X.Opens)

include C in
/-- Pulling back sections over `W` along `g`, as an `R`-linear map: this is
`Scheme.Hom.pullbackSectionsBaseLinear`, for the actions of `R` and `R'` on sections through
`Scheme.baseRingToStructurePresheaf`. -/
private def sectionsPullbackApp :
    ((sectionsBasePresheafFunctor R).obj M).obj (op W) ⟶
      (pullbackSectionsPresheaf (R' := R') g M ⋙
        ModuleCat.restrictScalars (algebraMap R R')).obj (op W) := by
  letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  letI : Algebra R' Γ(Y, g ⁻¹ᵁ W) :=
    ((Y.baseRingToStructurePresheaf R').app (op (g ⁻¹ᵁ W))).hom.toAlgebra
  letI := sectionsBaseModule R M W
  letI := sectionsBaseModule R' ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ W)
  letI : Module R Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    Module.compHom _ (algebraMap R R')
  letI : Module R ((pullbackSectionsPresheaf (R' := R') g M).obj (op W)) :=
    Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R Γ(X, W) Γ(M, W) := .of_algebraMap_smul fun _ _ ↦ rfl
  haveI : IsScalarTower R' Γ(Y, g ⁻¹ᵁ W) Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  haveI : IsScalarTower R R' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  exact ModuleCat.ofHom (g.pullbackSectionsBaseLinear M W C)

private lemma sectionsPullbackApp_hom_apply (x : Γ(M, W)) :
    (sectionsPullbackApp C M W).hom x = g.pullbackSections M W x := by
  let : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  let : Algebra R' Γ(Y, g ⁻¹ᵁ W) :=
    ((Y.baseRingToStructurePresheaf R').app (op (g ⁻¹ᵁ W))).hom.toAlgebra
  let := sectionsBaseModule R M W
  let := sectionsBaseModule R' ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ W)
  let : Module R Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    Module.compHom _ (algebraMap R R')
  have : IsScalarTower R Γ(X, W) Γ(M, W) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R' Γ(Y, g ⁻¹ᵁ W) Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R R' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  exact g.pullbackSectionsBaseLinear_apply M W C x

end SectionsPullback

/-- Pulling back sections along `g`, as a morphism of presheaves of `R`-modules on `X`. -/
private def sectionsPullback (M : X.Modules) :
    (sectionsBasePresheafFunctor R).obj M ⟶
      pullbackSectionsPresheaf (R' := R') g M ⋙ ModuleCat.restrictScalars (algebraMap R R') where
  app W := sectionsPullbackApp C M W.unop
  naturality _ _ i := by
    ext (x : Γ(M, _))
    exact (sectionsPullbackApp_hom_apply C M _ _).trans
      ((g.pullbackSections_restrict M _ i.unop x).symm.trans
        (congrArg _ (sectionsPullbackApp_hom_apply C M _ x).symm))

/-- The morphism of presheaves of `R'`-modules `R' ⊗[R] Γ(M, -) ⟶ Γ(g^* M, g⁻¹ -)` on `X`,
`s ⊗ m ↦ s • g^* m`: the adjoint, under extension and restriction of scalars along `R → R'`, of
pulling back sections along `g` (`AlgebraicGeometry.Scheme.Hom.pullbackSectionsBaseLinear`). -/
def sectionsPullbackExtend (M : X.Modules) :
    (sectionsBasePresheafFunctor R).obj M ⋙ ModuleCat.extendScalars (algebraMap R R') ⟶
      (Opens.map g.base).op ⋙
        (sectionsBasePresheafFunctor R').obj ((Scheme.Modules.pullback g).obj M) where
  app W := ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv _ _).symm
    ((sectionsPullback C M).app W)
  naturality W V i := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm,
      (sectionsPullback C M).naturality, Functor.comp_map,
      Adjunction.homEquiv_naturality_right_symm]

/-- `sectionsPullbackExtend` is adjoint to pulling back sections along `g`: its adjoint under
extension and restriction of scalars along `R → R'` sends a section `m` of `M` to `g^* m`. -/
theorem extendRestrictScalarsAdj_homEquiv_sectionsPullbackExtend_app_hom_apply (M : X.Modules)
    (W : X.Opensᵒᵖ) (m : Γ(M, W.unop)) :
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv _ _
      ((sectionsPullbackExtend C M).app W)).hom m = g.pullbackSections M W.unop m := by
  dsimp only [sectionsPullbackExtend]
  rw [Equiv.apply_symm_apply]
  exact sectionsPullbackApp_hom_apply C M W.unop m

/-- On an affine open, sections of `g^* M` are the base change of sections of `M`, so the
adjoint of the pullback of sections is an isomorphism. -/
theorem isIso_sectionsPullbackExtend_app (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W) : IsIso ((sectionsPullbackExtend H.toCommSq M).app (op W)) := by
  let : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  let : Algebra R' Γ(Y, g ⁻¹ᵁ W) :=
    ((Y.baseRingToStructurePresheaf R').app (op (g ⁻¹ᵁ W))).hom.toAlgebra
  let := sectionsBaseModule R M W
  let := sectionsBaseModule R' ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ W)
  let : Module R Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    Module.compHom _ (algebraMap R R')
  have : IsScalarTower R Γ(X, W) Γ(M, W) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R' Γ(Y, g ⁻¹ᵁ W) Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R R' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have h := ModuleCat.isIso_extendRestrictScalarsAdj_homEquiv_symm_of_isBaseChange
    (g.isBaseChange_pullbackSections M W H hW)
  have e : (sectionsPullback H.toCommSq M).app (op W) = ModuleCat.ofHom
      (g.pullbackSectionsBaseLinear M W H.toCommSq) ≫
        (ModuleCat.restrictScalarsAlgebraMapIso _).inv :=
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ (sectionsPullbackApp_hom_apply H.toCommSq M W x).trans
      ((g.pullbackSectionsBaseLinear_apply M W H.toCommSq x).symm.trans
        (ModuleCat.restrictScalarsAlgebraMapIso_inv_apply (R := R) (S := R')
          Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) _).symm))
  -- The component of `sectionsPullbackExtend` is the adjoint of that of `sectionsPullback`.
  dsimp only [sectionsPullbackExtend]
  rw [e]
  exact h

section CechComplex

variable {ι : Type u}

/-- On the finite intersections of `U`, which are affine, sections of `g^* M` are the base change
of sections of `M`, so the map of Čech complexes induced by `sectionsPullbackExtend` is an
isomorphism. -/
private lemma isIso_cechComplexFunctor_map_sectionsPullbackExtend (U : ι → X.Opens)
    (M : X.Modules) [M.IsQuasicoherent]
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) :
    IsIso ((cechComplexFunctor U).map (sectionsPullbackExtend H.toCommSq M)) := by
  have (k : ℕ) :
      IsIso (((cechComplexFunctor U).map (sectionsPullbackExtend H.toCommSq M)).f k) := by
    let φ (a : Fin (k + 1) → ι) :=
      (sectionsPullbackExtend H.toCommSq M).app (op (∏ᶜ fun j ↦ U (a j)))
    have (a : Fin (k + 1) → ι) : IsIso (φ a) :=
      isIso_sectionsPullbackExtend_app H M
        (CompleteLattice.finite_product_of_forall_finset_inf U hU a)
    -- In each degree the map of Čech complexes is the product of the components.
    have e : ((cechComplexFunctor U).map (sectionsPullbackExtend H.toCommSq M)).f k =
        Limits.Pi.map φ :=
      Pi.hom_ext _ _ fun a ↦ (cechComplexFunctor_map_f_π U _ _ k a).trans (Pi.map_π φ a).symm
    rw [e]
    exact Pi.map_isIso φ
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The Čech complex commutes with base change.** Extending scalars from `R` to `R'` in the
Čech complex of the sections of `M` for `U` gives the Čech complex of the sections of `g^* M` for
`g⁻¹ U`. No flatness of `R → R'` is needed, as `U` has affine finite intersections. -/
def cechComplexBaseChangeIso [Finite ι] (U : ι → X.Opens) (M : X.Modules)
    [M.IsQuasicoherent]
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) :
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex _).obj
        ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor R).obj M)) ≅
      (cechComplexFunctor fun i ↦ g ⁻¹ᵁ U i).obj
        ((sectionsBasePresheafFunctor R').obj ((Scheme.Modules.pullback g).obj M)) :=
  haveI := isIso_cechComplexFunctor_map_sectionsPullbackExtend H U M hU
  (cechComplexFunctorMapIso U _).app _ ≪≫
    asIso ((cechComplexFunctor U).map (sectionsPullbackExtend H.toCommSq M)) ≪≫
    (cechComplexCompIso (Opens.map g.base) U _).symm

/-- The factor indexed by `a` of the degree `n` component of `cechComplexBaseChangeIso` is the
component `R' ⊗_R Γ(M, W) ⟶ Γ(g^* M, g⁻¹ W)` of `sectionsPullbackExtend` at the intersection
`W = U (a 0) ∩ ⋯ ∩ U (a n)`, followed by the identification of `g⁻¹ W` with the intersection of
the `g⁻¹ U (a j)`. -/
@[reassoc]
theorem cechComplexBaseChangeIso_hom_f_π [Finite ι] (U : ι → X.Opens) (M : X.Modules)
    [M.IsQuasicoherent] (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (n : ℕ)
    (a : Fin (n + 1) → ι) :
    (cechComplexBaseChangeIso H U M hU).hom.f n ≫ Pi.π (fun a : Fin (n + 1) → ι ↦
        ((sectionsBasePresheafFunctor R').obj ((Scheme.Modules.pullback g).obj M)).obj
          (op (∏ᶜ fun j ↦ g ⁻¹ᵁ U (a j)))) a =
      (ModuleCat.extendScalars (algebraMap R R')).map (Pi.π (fun a : Fin (n + 1) → ι ↦
          ((sectionsBasePresheafFunctor R).obj M).obj (op (∏ᶜ fun j ↦ U (a j)))) a) ≫
        (sectionsPullbackExtend H.toCommSq M).app (op (∏ᶜ fun j ↦ U (a j))) ≫
          ((sectionsBasePresheafFunctor R').obj ((Scheme.Modules.pullback g).obj M)).map
            (homOfLE (g.preimage_finite_product fun j ↦ U (a j)).ge).op := by
  let Q := (sectionsBasePresheafFunctor R').obj ((Scheme.Modules.pullback g).obj M)
  let E := cechComplexCompIso (Opens.map g.base) U Q
  let r := (homOfLE (g.preimage_finite_product fun j ↦ U (a j)).ge).op
  -- The restrictions between the equal opens `∏ g⁻¹ U (a j)` and `g⁻¹ ∏ U (a j)` are inverse.
  have hr : Q.map (piComparison (Opens.map g.base) fun j ↦ U (a j)).op ≫
      Q.map r = 𝟙 _ := by
    rw [← Q.map_comp, ← Q.map_id]
    exact congrArg Q.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  -- So the factors of the inverse of `cechComplexCompIso` are restrictions.
  have h : E.hom.f n ≫
      Pi.π (fun a : Fin (n + 1) → ι ↦ Q.obj (op (g ⁻¹ᵁ ∏ᶜ fun j ↦ U (a j)))) a ≫ Q.map r =
        Pi.π (fun a : Fin (n + 1) → ι ↦ Q.obj (op (∏ᶜ fun j ↦ g ⁻¹ᵁ U (a j)))) a :=
    (cechComplexCompIso_hom_f_π_assoc _ U Q n a (Q.map r)).trans <|
      (congrArg (_ ≫ ·) hr).trans (Category.comp_id _)
  have hE : E.inv.f n ≫
      Pi.π (fun a : Fin (n + 1) → ι ↦ Q.obj (op (∏ᶜ fun j ↦ g ⁻¹ᵁ U (a j)))) a =
        Pi.π (fun a : Fin (n + 1) → ι ↦ Q.obj (op (g ⁻¹ᵁ ∏ᶜ fun j ↦ U (a j)))) a ≫ Q.map r := by
    rw [← h, ← HomologicalComplex.comp_f_assoc, E.inv_hom_id, HomologicalComplex.id_f]
    exact Category.id_comp _
  -- `cechComplexBaseChangeIso` is the composite of three isomorphisms of complexes.
  simp only [cechComplexBaseChangeIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    HomologicalComplex.comp_f]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_)
  rw [hE]
  -- The middle factor is the component of `sectionsPullbackExtend` at `∏ U (a j)`, and the first
  -- is extension of scalars applied to the projection.
  exact (congrArg (_ ≫ ·) ((cechComplexFunctor_map_f_π_assoc U _ (sectionsPullbackExtend
    H.toCommSq M) n a (Q.map r)).trans (Category.assoc _ _ _))).trans <|
      (Category.assoc _ _ _).symm.trans (cechComplexFunctorMapIso_hom_app_f_π_assoc U
        (ModuleCat.extendScalars (algebraMap R R')) ((sectionsBasePresheafFunctor R).obj M) n a _)

include H in
/-- **The Čech complex computes the cohomology of every base change.** Let `X` be a scheme over
`R`, let `R → R'` be any ring map and let `Y = X ×_R R'`, given as a pullback square. Let `M` be a
quasi-coherent sheaf on `X` and `U` a finite family of opens covering `X` whose nonempty finite
intersections are affine. Then `Hⁿ(Y, g^* M)` is the `n`-th cohomology of the complex
`R' ⊗_R Č(U, M)` obtained by extending scalars in the Čech complex of the sections of `M`, through
the isomorphism of complexes `cechComplexBaseChangeIso`. -/
theorem nonempty_linearEquiv_homology_extendScalars_cechComplex_cohomology_pullback_of_iSup_eq_top
    (M : X.Modules) [M.IsQuasicoherent] [Finite ι] (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (hcover : ⨆ i, U i = ⊤) (n : ℕ) :
    Nonempty ((((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        _).obj ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor R).obj M))).homology n
          ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  have hcoverV : ⨆ i, g ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  exact ⟨(HomologicalComplex.homologyMapIso (cechComplexBaseChangeIso H U M hU) n
      |>.toLinearEquiv) ≪≫ₗ
    homologyCechComplexLinearEquiv _ (g.isAffineOpen_finset_inf_preimage hU) hcoverV _ n⟩

include H in
/-- **Flat base change for the cohomology of quasi-coherent sheaves**, for a finite cover with
affine intersections. Let `X` be a scheme over `R`, let `R → R'` be a flat ring map and let
`Y = X ×_R R'`, given as a pullback square. Let `M` be a
quasi-coherent sheaf on `X` and suppose that `X` is covered by finitely many opens whose nonempty
finite intersections are affine. Then `Hⁿ(Y, g^* M) ≅ R' ⊗_R Hⁿ(X, M)` for every `n`. -/
theorem nonempty_linearEquiv_tensor_cohomology_pullback_of_iSup_eq_top [Module.Flat R R']
    (M : X.Modules) [M.IsQuasicoherent] [Finite ι] (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (hcover : ⨆ i, U i = ⊤) (n : ℕ) :
    Nonempty (R' ⊗[R] Cohomology M n ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  -- Extension of scalars along the flat map `R → R'` is exact, so it commutes with homology.
  let E := ModuleCat.extendScalars.{u, u, u} (algebraMap R R')
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat R R'›)
  have : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
  let C := (cechComplexFunctor U).obj ((sectionsBasePresheafFunctor R).obj M)
  obtain ⟨e⟩ :=
    nonempty_linearEquiv_homology_extendScalars_cechComplex_cohomology_pullback_of_iSup_eq_top
      H M U hU hcover n
  -- `R' ⊗[R] Hⁿ(X, M) ≅ R' ⊗[R] Hⁿ(Č(U, M)) ≅ Hⁿ(R' ⊗[R] Č(U, M)) ≅ Hⁿ(Y, g^* M)`.
  exact ⟨LinearEquiv.baseChange R R' _ _ (homologyCechComplexLinearEquiv U hU hcover M n).symm ≪≫ₗ
    (ModuleCat.extendScalarsAlgebraMapIso _).symm.toLinearEquiv ≪≫ₗ
    ((C.sc n).mapHomologyIso E).symm.toLinearEquiv ≪≫ₗ e⟩

end CechComplex

end FlatBaseChange

end TauCeti.AlgebraicGeometry
