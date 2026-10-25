/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients
public import TauCeti.Topology.Sheaves.Leray

/-!
# Čech cohomology of quasi-coherent sheaves as modules over the base ring

Let `X` be a scheme over a commutative ring `S` and let `M` be a sheaf of modules on `X`. Its
sections over every open are `S`-modules, through the global functions `Γ(X, ⊤)`, and the
restriction maps are `S`-linear; this is the presheaf of `S`-modules
`(Scheme.Modules.sectionsBasePresheafFunctor S).obj M`. Its Čech complex for a family of opens is
therefore a complex of `S`-modules, and so is its cohomology.

Let `X` be locally Noetherian, `M` quasi-coherent and `U` a finite family of opens covering `X`
whose nonempty finite intersections are affine. Leray's theorem identifies the Čech cohomology of
`M` for `U` with the cohomology `Hⁿ(X, M)` as abelian groups
(`TauCeti.Topology.homologyCechComplexIsoH`). This file shows that the identification is
`S`-linear (`Scheme.Modules.homologyCechComplexLinearEquiv`): the Čech complex of the presheaf of
`S`-modules computes `Hⁿ(X, M)` as an `S`-module. Linear-algebraic operations on the Čech complex,
such as extension of scalars along a flat ring map, thus become available for cohomology.

The underlying complex of abelian groups of the Čech complex of a presheaf of modules is the Čech
complex of the underlying presheaf of abelian groups
(`TauCeti.CategoryTheory.cechComplexFunctorMapIso`), and forgetting the module structure preserves
homology. The action of `s : S` on the Čech cohomology is induced by multiplication by `s` on the
presheaf, which is the endomorphism of `M` given by multiplication by the global function `s`, and
Leray's comparison is natural in the coefficient sheaf.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.sectionsBasePresheafFunctor`: the presheaf of sections of a
  sheaf of modules on a scheme over `S`, as a presheaf of `S`-modules.
* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexLinearEquiv`: the `S`-linear equivalence
  between the Čech cohomology of this presheaf for a finite cover with affine intersections and
  `Hⁿ(X, M)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Theorem III.4.5.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite
open TauCeti TauCeti.CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (S : Type u) [CommRing S] {X : Scheme.{u}} [X.Over (Spec (.of S))]

/-- The action of `S` on the sections over `W` of a sheaf of modules on a scheme over `S`, through
`Scheme.baseRingToStructurePresheaf`, as in `Scheme.Modules.isScalarTower_sections`. -/
abbrev sectionsBaseModule (M : X.Modules) (W : X.Opens) : Module S Γ(M, W) :=
  Module.compHom Γ(M, W) ((X.baseRingToStructurePresheaf S).app (op W)).hom

/-- Restriction of sections commutes with the action of the base ring through
`Scheme.baseRingToStructurePresheaf`. -/
lemma presheaf_map_baseRingToStructurePresheaf_smul (M : X.Modules) {W V : X.Opens}
    (i : V ⟶ W) (s : S) (x : Γ(M, W)) :
    M.presheaf.map i.op ((X.baseRingToStructurePresheaf S).app (op W) s • x) =
      (X.baseRingToStructurePresheaf S).app (op V) s • M.presheaf.map i.op x := by
  have h := congrArg (fun f ↦ f.hom s) ((X.baseRingToStructurePresheaf S).naturality i.op)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
    CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [map_smul, ← h]

/-- The presheaf of sections of a sheaf of modules on a scheme over `S`, as a presheaf of
`S`-modules: the sections over `W` keep their carrier and restriction maps, and `S` acts through
`Scheme.baseRingToStructurePresheaf` (`Scheme.Modules.sectionsBaseModule`). -/
@[expose]
def sectionsBasePresheafFunctor : X.Modules ⥤ (X.Opensᵒᵖ ⥤ ModuleCat.{u} S) where
  obj M :=
    { obj W := letI := sectionsBaseModule S M W.unop; ModuleCat.of S Γ(M, W.unop)
      map {W V} i :=
        letI := sectionsBaseModule S M W.unop
        letI := sectionsBaseModule S M V.unop
        ModuleCat.ofHom
          { toFun := M.presheaf.map i
            map_add' := map_add _
            map_smul' := presheaf_map_baseRingToStructurePresheaf_smul S M i.unop }
      map_id W :=
        letI := sectionsBaseModule S M W.unop
        ModuleCat.hom_ext (LinearMap.ext fun x ↦ congrArg (fun f ↦ f.hom x) (M.presheaf.map_id W))
      map_comp {W _ Z} i j :=
        letI := sectionsBaseModule S M W.unop
        letI := sectionsBaseModule S M Z.unop
        ModuleCat.hom_ext (LinearMap.ext fun x ↦
          congrArg (fun f ↦ f.hom x) (M.presheaf.map_comp i j)) }
  map {M N} f :=
    { app W :=
        letI := sectionsBaseModule S M W.unop
        letI := sectionsBaseModule S N W.unop
        ModuleCat.ofHom
          { toFun := f.app W.unop
            map_add' := map_add _
            map_smul' _ _ := Hom.app_smul _ _ _ }
      naturality W V i :=
        letI := sectionsBaseModule S M W.unop
        letI := sectionsBaseModule S N V.unop
        ModuleCat.hom_ext (LinearMap.ext fun x ↦
          congrArg (fun g ↦ g.hom x) (f.mapPresheaf.naturality i)) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction maps of the presheaf of `S`-modules of sections are those of `M`. -/
@[simp]
lemma sectionsBasePresheafFunctor_obj_map_hom_apply (M : X.Modules) {W V : X.Opensᵒᵖ}
    (i : W ⟶ V) (x : Γ(M, W.unop)) :
    (((sectionsBasePresheafFunctor S).obj M).map i).hom x = M.presheaf.map i x :=
  rfl

/-- A morphism of sheaves of modules acts on the presheaves of `S`-modules of sections by its
action on sections. -/
@[simp]
lemma sectionsBasePresheafFunctor_map_app_hom_apply {M N : X.Modules} (f : M ⟶ N)
    (W : X.Opensᵒᵖ) (x : Γ(M, W.unop)) :
    (((sectionsBasePresheafFunctor S).map f).app W).hom x = f.app W.unop x :=
  rfl

/-- The underlying presheaf of abelian groups of the presheaf of `S`-modules of sections is the
presheaf of sections. -/
def sectionsBasePresheafCompForget₂Iso (M : X.Modules) :
    (sectionsBasePresheafFunctor S).obj M ⋙ forget₂ (ModuleCat.{u} S) Ab ≅ M.presheaf :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

/-- Multiplication by `s : S` on the presheaf of `S`-modules of sections is induced by the
multiplication by the global function `s` on the sheaf of modules. -/
lemma sectionsBasePresheafFunctor_map_globalSectionsSmul (M : X.Modules) (s : S) :
    (sectionsBasePresheafFunctor S).map (M.globalSectionsSmul (baseRingToGlobalSections S X s)) =
      s • 𝟙 ((sectionsBasePresheafFunctor S).obj M) := by
  ext W (x : Γ(M, W.unop))
  -- Both sides multiply `x` by the restriction of the global function `s` to `W`.
  change (M.globalSectionsSmul (baseRingToGlobalSections S X s)).app W.unop x =
    (X.baseRingToStructurePresheaf S).app (op W.unop) s • x
  rw [globalSectionsSmul_app, Scheme.baseRingToStructurePresheaf_app]
  rfl

variable {S} [IsLocallyNoetherian X] {ι : Type u} [Finite ι] (U : ι → X.Opens)
  (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (hcover : ⨆ i, U i = ⊤)

omit [Finite ι] in
include hU in
/-- A quasi-coherent sheaf on a locally Noetherian scheme has no cohomology in positive degrees on
a nonempty finite intersection of members of `U`, which is affine. -/
private lemma subsingleton_cohomologyOn_inf_succ (M : X.Modules) [M.IsQuasicoherent]
    (s : Finset ι) (hs : s.Nonempty) (k : ℕ) : Subsingleton (cohomologyOn M (k + 1) (s.inf U)) :=
  have : IsNoetherianRing Γ(X, s.inf U) := IsLocallyNoetherian.component_noetherian ⟨_, hU s hs⟩
  subsingleton_cohomologyOn_succ_of_isAffineOpen M (hU s hs) k

/-- Forgetting the module structure commutes with taking cohomology. -/
private def homologyCechIso₁ (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat.{u} S) Ab).obj
        (((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).homology n) ≅
      (((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).obj
        ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M))).homology n :=
  ((((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).sc n).mapHomologyIso
    (forget₂ (ModuleCat.{u} S) Ab)).symm

/-- Forgetting the module structure commutes with forming Čech complexes. -/
private def homologyCechIso₂ (M : X.Modules) (n : ℕ) :
    (((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).obj
        ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M))).homology n ≅
      ((cechComplexFunctor U).obj M.presheaf).homology n :=
  HomologicalComplex.homologyMapIso
    ((cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} S) Ab)).app _ ≪≫
      (cechComplexFunctor U).mapIso (sectionsBasePresheafCompForget₂Iso S M)) n

omit [IsLocallyNoetherian X] [Finite ι] in
/-- `homologyCechIso₁` is natural. -/
@[reassoc]
private lemma homologyCechIso₁_hom_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (forget₂ (ModuleCat.{u} S) Ab).map (HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f)) n) ≫
        (homologyCechIso₁ U N n).hom =
      (homologyCechIso₁ U M n).hom ≫ HomologicalComplex.homologyMap
        (((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).map
          ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f))) n :=
  ShortComplex.mapHomologyIso_inv_naturality _ _

omit [IsLocallyNoetherian X] in
/-- `homologyCechIso₂` is natural. -/
@[reassoc]
private lemma homologyCechIso₂_hom_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).map
          ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f))) n ≫
        (homologyCechIso₂ U N n).hom =
      (homologyCechIso₂ U M n).hom ≫ HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map f.mapPresheaf) n := by
  have h : ((forget₂ (ModuleCat.{u} S) Ab).mapHomologicalComplex _).map
        ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f)) ≫
        ((cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} S) Ab)).app _ ≪≫
          (cechComplexFunctor U).mapIso (sectionsBasePresheafCompForget₂Iso S N)).hom =
      ((cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} S) Ab)).app _ ≪≫
          (cechComplexFunctor U).mapIso (sectionsBasePresheafCompForget₂Iso S M)).hom ≫
        (cechComplexFunctor U).map f.mapPresheaf := by
    rw [Iso.trans_hom, Iso.trans_hom, Iso.app_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.mapIso_hom, ← Category.assoc,
      ← Functor.comp_map (cechComplexFunctor U) (Functor.mapHomologicalComplex _ _),
      (cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} S) Ab)).hom.naturality,
      Category.assoc, Functor.comp_map]
    have h' : ((Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u} S) Ab)).map
          ((sectionsBasePresheafFunctor S).map f) ≫ (sectionsBasePresheafCompForget₂Iso S N).hom =
        (sectionsBasePresheafCompForget₂Iso S M).hom ≫ f.mapPresheaf := by
      ext W x
      rfl
    rw [← Functor.map_comp (cechComplexFunctor U), h', Functor.map_comp]
    simp only [Category.assoc]
  simp only [homologyCechIso₂, HomologicalComplex.homologyMapIso_hom]
  rw [← HomologicalComplex.homologyMap_comp, h, HomologicalComplex.homologyMap_comp]

/-- Leray's comparison of the Čech cohomology of the presheaf of `S`-modules of sections with the
cohomology of `M`, as abelian groups: forget the module structure, which commutes with taking
homology and with forming Čech complexes, and apply Leray's theorem. -/
private def homologyCechComplexAddIso (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (forget₂ (ModuleCat.{u} S) Ab).obj
        (((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).homology n) ≅
      AddCommGrpCat.of (Cohomology M n) :=
  homologyCechIso₁ U M n ≪≫ homologyCechIso₂ U M n ≪≫
    TauCeti.Topology.homologyCechComplexIsoH U hcover _
      (subsingleton_cohomologyOn_inf_succ U hU M) n

/-- `homologyCechComplexAddIso` is the composite of its three steps. -/
private lemma homologyCechComplexAddIso_hom (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (homologyCechComplexAddIso (S := S) U hU hcover M n).hom =
      (homologyCechIso₁ (S := S) U M n).hom ≫ (homologyCechIso₂ (S := S) U M n).hom ≫
        (TauCeti.Topology.homologyCechComplexIsoH U hcover _
          (subsingleton_cohomologyOn_inf_succ U hU M) n).hom :=
  rfl

/-- `homologyCechComplexAddIso` is natural in the quasi-coherent sheaf. -/
private lemma homologyCechComplexAddIso_hom_naturality {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (f : M ⟶ N) (n : ℕ) :
    (forget₂ (ModuleCat.{u} S) Ab).map (HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map f)) n) ≫
        (homologyCechComplexAddIso U hU hcover N n).hom =
      (homologyCechComplexAddIso U hU hcover M n).hom ≫ (cohomologyFunctor X n).map f := by
  rw [homologyCechComplexAddIso_hom, homologyCechComplexAddIso_hom]
  -- The goal mentions the abelian sheaf of `M` through two defeq presentations of the ring
  -- sheaf, so the naturality squares are composed as terms rather than by rewriting.
  exact ((homologyCechIso₁_hom_naturality_assoc U f n _).trans (congrArg (_ ≫ ·)
    ((homologyCechIso₂_hom_naturality_assoc U f n _).trans (congrArg (_ ≫ ·)
      (TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoH_hom U hcover _ _
        ((SheafOfModules.toSheaf X.ringCatSheaf).map f) n))))).trans
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)

/-- **Čech cohomology computes cohomology, linearly over the base ring.** Let `X` be a locally
Noetherian scheme over `S`, `M` a quasi-coherent sheaf of modules on `X` and `U` a finite family of
opens covering `X` whose nonempty finite intersections are affine. Then the cohomology of the Čech
complex of the presheaf of `S`-modules of sections of `M` for `U` is `S`-linearly equivalent to
`Hⁿ(X, M)`, for every `n`. The underlying additive equivalence is Leray's comparison
`TauCeti.Topology.homologyCechComplexIsoH`. -/
def homologyCechComplexLinearEquiv (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((cechComplexFunctor U).obj ((sectionsBasePresheafFunctor S).obj M)).homology n ≃ₗ[S]
      Cohomology M n where
  toAddEquiv := (homologyCechComplexAddIso U hU hcover M n).addCommGroupIsoToAddEquiv
  map_smul' s x := by
    have h := ConcreteCategory.congr_hom (homologyCechComplexAddIso_hom_naturality U hU hcover
      (M.globalSectionsSmul (baseRingToGlobalSections S X s)) n) x
    have hx : (forget₂ (ModuleCat.{u} S) Ab).map (HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((sectionsBasePresheafFunctor S).map
          (M.globalSectionsSmul (baseRingToGlobalSections S X s)))) n) x = s • x := by
      rw [sectionsBasePresheafFunctor_map_globalSectionsSmul, Functor.map_smul,
        CategoryTheory.Functor.map_id,
        HomologicalComplex.homologyMap_smul, HomologicalComplex.homologyMap_id]
      rfl
    -- The additive equivalence applies the homomorphism of the isomorphism.
    change (homologyCechComplexAddIso U hU hcover M n).hom (s • x) =
      s • (homologyCechComplexAddIso U hU hcover M n).hom x
    rw [base_smul_cohomology, cohomology_smul, ← hx]
    exact h

end AlgebraicGeometry.Scheme.Modules
