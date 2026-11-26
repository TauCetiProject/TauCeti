/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Solid
public import Mathlib.Topology.Category.Profinite.Nobeling.Induction
public import TauCeti.Condensed.Discrete.LocallyConstant
public import TauCeti.Condensed.Discrete.Module
public import TauCeti.Topology.Category.Profinite.Extend
public import TauCeti.Topology.LocallyConstant.FinsuppEquiv

/-!
# The free solid module on a profinite set

For a profinite set `S` and a ring `R`, Mathlib defines the free solid module `R[S]^solid`
(`Condensed.profiniteSolid R`) as the right Kan extension of the free condensed modules on
finite sets along `FintypeCat.toProfinite`, that is, as the limit of `R[F]` over all maps from
`S` to finite sets `F`. This file computes it: `R[S]^solid` is the condensed `R`-module of
`R`-valued measures on `S`,

`T ↦ Hom_ℤ(C(S, ℤ), C(T, R))`,

where `C(-, -)` denotes locally constant (equivalently, continuous) functions
(`TauCeti.profiniteSolidIsoLocallyConstantIntDual`). By Nöbeling's theorem
(`LocallyConstant.freeOfProfinite`) `C(S, ℤ)` is a free abelian group, and a basis indexed by `I`
identifies `R[S]^solid` with the product of `I` copies of the discrete condensed module `R`
(`TauCeti.locallyConstantIntDualIsoPi`, `TauCeti.exists_profiniteSolid_iso_pi`).

The proof evaluates the limit defining `R[S]^solid` on a compact Hausdorff space `T`. There the
free condensed module on a finite set `F` has sections `LocallyConstant T (F →₀ R)`
(`TauCeti.finFreeIso`), which is `Hom(C(F, ℤ), C(T, R))` by
`TauCeti.locallyConstantFinsuppEquiv`. The limit of these over maps `S → F` is
`Hom(C(S, ℤ), C(T, R))`, because every locally constant function on `S` factors through a finite
discrete quotient and any two such factorizations have a common refinement
(`Profinite.exists_structuredArrow_surjective_refinement`).

For a commutative ring `R`, `TauCeti.Condensed.Solid.LocallyConstantDual` describes `R[S]^solid`
instead as the `R`-linear dual of `LocallyConstant S R`, naturally in `S`
(`TauCeti.profiniteSolidIsoLocallyConstantDual`), and decomposes it as a product given a basis of
`LocallyConstant S R`. The `ℤ`-linear dual used here needs no commutativity, and Nöbeling's
theorem supplies the basis, so the product decomposition holds for every profinite set.

## Main definitions and results

* `TauCeti.finFreeIso`: the free condensed module on a finite set `F` is the discrete condensed
  module on `F →₀ R`.
* `TauCeti.locallyConstantIntDual`: the condensed module `T ↦ Hom_ℤ(C(S, ℤ), C(T, R))`.
* `TauCeti.profiniteSolidToFin`: the projection `R[S]^solid ⟶ R[F]` along a map `S → F` to a
  finite set; `TauCeti.profiniteSolidification_app_comp_profiniteSolidToFin` computes it on the
  solidification map `R[S] ⟶ R[S]^solid`.
* `TauCeti.profiniteSolidIsoLocallyConstantIntDual`: the isomorphism
  `R[S]^solid ≅ locallyConstantIntDual R S`, characterized by
  `TauCeti.profiniteSolidIsoLocallyConstantIntDual_hom_app_apply`.
* `TauCeti.isLimitLocallyConstantIntDualFan`, `TauCeti.locallyConstantIntDualIsoPi`: a `ℤ`-basis of
  `C(S, ℤ)` indexed by `I` exhibits `locallyConstantIntDual R S` as the product of `I` copies of
  the discrete condensed module `R`.
* `TauCeti.exists_profiniteSolid_iso_pi`: `R[S]^solid` is a product of copies of the discrete
  condensed module `R`.

## References

* D. Clausen and P. Scholze, *Lectures on condensed mathematics*, Lecture V.
-/

public section

universe u

open CategoryTheory Limits Opposite Condensed

namespace TauCeti

local instance discreteTopology_toProfinite_obj (F : FintypeCat.{u}) :
    DiscreteTopology (FintypeCat.toProfinite.obj F) :=
  FintypeCat.discreteTopology F

/-- The finite set underlying `FintypeCat.toProfinite.obj F`, as a `Fintype`. -/
noncomputable local instance fintypeToProfiniteObj (F : FintypeCat.{u}) :
    Fintype (FintypeCat.toProfinite.obj F) :=
  Fintype.ofFinite _

variable (R : Type (u + 1)) [Ring R]

/-- The discrete condensed `R`-module on `F →₀ R`, as a functor of the finite set `F`. -/
noncomputable abbrev finLocallyConstant : FintypeCat.{u} ⥤ CondensedMod.{u} R :=
  FintypeCat.incl ⋙ uliftFunctor.{u + 1} ⋙ ModuleCat.free R ⋙ CondensedMod.LocallyConstant.functor R

/-- The free condensed `R`-module on a finite set `F` is the discrete condensed module on
`F →₀ R`; its sections over `T` are `LocallyConstant T (F →₀ R)`. -/
noncomputable def finFreeIso : finFree R ≅ finLocallyConstant R :=
  Functor.isoWhiskerRight toProfiniteCompProfiniteToCondensedIso (free R) ≪≫
    Functor.isoWhiskerLeft (FintypeCat.incl ⋙ uliftFunctor.{u + 1}) (locallyConstantCompFreeIso R)

/-- `finFreeIso` at a finite set `F` is the free condensed module functor applied to
`toProfiniteCompProfiniteToCondensedIso`, followed by `locallyConstantCompFreeIso`; the latter is
characterized by `unit_app_comp_map_locallyConstantCompFreeIso_hom_app`. -/
theorem finFreeIso_hom_app (F : FintypeCat.{u}) :
    (finFreeIso R).hom.app F =
      (free R).map (toProfiniteCompProfiniteToCondensedIso.hom.app F) ≫
        (locallyConstantCompFreeIso R).hom.app (ULift.{u + 1} F) := by
  simp [finFreeIso]

variable (S : Profinite.{u})

/-- The presheaf `T ↦ Hom_ℤ(C(S, ℤ), C(T, R))` of `R`-valued measures on `S`, where `C(-, -)`
denotes locally constant functions. -/
@[expose]
noncomputable def locallyConstantIntDualPresheaf : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj T := ModuleCat.of R (LocallyConstant S ℤ →+ LocallyConstant T.unop R)
  map g := ModuleCat.ofHom
    { toFun h := (LocallyConstant.comapAddMonoidHom g.unop.hom.hom).comp h
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

@[simp]
theorem locallyConstantIntDualPresheaf_obj (T : CompHaus.{u}ᵒᵖ) :
    (locallyConstantIntDualPresheaf R S).obj T =
      ModuleCat.of R (LocallyConstant S ℤ →+ LocallyConstant T.unop R) :=
  (rfl)

@[simp]
theorem locallyConstantIntDualPresheaf_map_hom_apply {T T' : CompHaus.{u}ᵒᵖ} (g : T ⟶ T')
    (h : LocallyConstant S ℤ →+ LocallyConstant T.unop R) :
    (locallyConstantIntDualPresheaf R S).map g h =
      (LocallyConstant.comapAddMonoidHom g.unop.hom.hom).comp h :=
  (rfl)

/-- The projection `R[S]^solid ⟶ R[F]` along a map `S ⟶ F` to a finite set: `profiniteSolid R`
applied to the map, followed by the counit `profiniteSolidCounit R` and `finFreeIso`. It is the
component at the map of the limit cone defining `R[S]^solid`, followed by `finFreeIso`. -/
noncomputable def profiniteSolidToFin (j : StructuredArrow S FintypeCat.toProfinite) :
    (profiniteSolid R).obj S ⟶ (finLocallyConstant R).obj j.right :=
  (profiniteSolid R).map j.hom ≫ (profiniteSolidCounit R).app j.right ≫
    (finFreeIso R).hom.app j.right

/-- `profiniteSolidification` followed by the projection to `R[F]` along `S ⟶ F` is the free
condensed module functor applied to `S ⟶ F`, followed by `finFreeIso`. -/
@[reassoc (attr := simp)]
theorem profiniteSolidification_app_comp_profiniteSolidToFin
    (j : StructuredArrow S FintypeCat.toProfinite) :
    (profiniteSolidification R).app S ≫ profiniteSolidToFin R S j =
      (profiniteFree R).map j.hom ≫ (finFreeIso R).hom.app j.right := by
  simp [profiniteSolidToFin, ← NatTrans.naturality_assoc, profiniteSolidification]

variable (T : CompHaus.{u})

/-- The sections over `T` of the diagram defining `R[S]^solid`, after `finFreeIso`. -/
private noncomputable def sectionsDiagram :
    StructuredArrow S FintypeCat.toProfinite ⥤ ModuleCat.{u + 1} R where
  obj j := ModuleCat.of R
    (LocallyConstant T (ULift.{u + 1} (FintypeCat.toProfinite.obj j.right) →₀ R))
  map k := ModuleCat.ofHom (LocallyConstant.mapₗ R
    (Finsupp.lmapDomain R R (ULift.map (FintypeCat.toProfinite.map k.right).hom.hom)))
  map_id j := by
    refine ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_)
    ext t y
    exact congrArg (· y) (Finsupp.mapDomain_id (v := v t))
  map_comp k k' := by
    refine ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_)
    ext t y
    exact congrArg (· y) (Finsupp.mapDomain_comp (v := v t)
      (f := ULift.map (FintypeCat.toProfinite.map k.right).hom.hom)
      (g := ULift.map (FintypeCat.toProfinite.map k'.right).hom.hom))

/-- `sectionsDiagram` is the evaluation at `T` of the diagram defining `R[S]^solid`. -/
private noncomputable def sectionsDiagramIso :
    StructuredArrow.proj S FintypeCat.toProfinite ⋙ finLocallyConstant R ⋙
      sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op T) ≅ sectionsDiagram R S T :=
  -- Both sides agree on the nose: `ModuleCat.free R` acts on maps by `Finsupp.lmapDomain` and
  -- `CondensedMod.LocallyConstant.functor R` by `LocallyConstant.mapₗ`.
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

private theorem sectionsDiagramIso_hom_app (j : StructuredArrow S FintypeCat.toProfinite) :
    (sectionsDiagramIso R S T).hom.app j = 𝟙 ((sectionsDiagram R S T).obj j) :=
  rfl

/-- The legs of the cone with apex `Hom(C(S, ℤ), C(T, R))` over `sectionsDiagram`. -/
private noncomputable def homConeπ (j : StructuredArrow S FintypeCat.toProfinite) :
    (LocallyConstant S ℤ →+ LocallyConstant T R) →ₗ[R]
      LocallyConstant T (ULift.{u + 1} (FintypeCat.toProfinite.obj j.right) →₀ R) where
  toFun h := (locallyConstantFinsuppEquiv R (FintypeCat.toProfinite.obj j.right) T).symm
    (h.comp (LocallyConstant.comapAddMonoidHom j.hom.hom.hom))
  map_add' _ _ := by simp [AddMonoidHom.add_comp]
  map_smul' _ _ := by simp [AddMonoidHom.smul_comp]

private theorem locallyConstantFinsuppEquiv_homConeπ (j : StructuredArrow S FintypeCat.toProfinite)
    (h : LocallyConstant S ℤ →+ LocallyConstant T R) :
    locallyConstantFinsuppEquiv R _ T (homConeπ R S T j h) =
      h.comp (LocallyConstant.comapAddMonoidHom j.hom.hom.hom) :=
  LinearEquiv.apply_symm_apply _ _

private theorem homConeπ_naturality {j j' : StructuredArrow S FintypeCat.toProfinite} (k : j ⟶ j')
    (h : LocallyConstant S ℤ →+ LocallyConstant T R) :
    (homConeπ R S T j h).map
        (Finsupp.mapDomain (ULift.map (FintypeCat.toProfinite.map k.right).hom.hom)) =
      homConeπ R S T j' h := by
  apply (locallyConstantFinsuppEquiv R (FintypeCat.toProfinite.obj j'.right) T).injective
  rw [locallyConstantFinsuppEquiv_homConeπ, locallyConstantFinsuppEquiv_map,
    locallyConstantFinsuppEquiv_homConeπ, AddMonoidHom.comp_assoc]
  congr 1
  ext φ : 1
  exact Profinite.comap_comap_of_structuredArrow_hom k φ

/-- The cone with apex `Hom(C(S, ℤ), C(T, R))` over `sectionsDiagram`. -/
private noncomputable def homCone : Cone (sectionsDiagram R S T) where
  pt := ModuleCat.of R (LocallyConstant S ℤ →+ LocallyConstant T R)
  π :=
    { app j := ModuleCat.ofHom (homConeπ R S T j)
      naturality _ _ k :=
        ModuleCat.hom_ext (LinearMap.ext fun h ↦ (homConeπ_naturality R S T k h).symm) }

private theorem homCone_π_app (j : StructuredArrow S FintypeCat.toProfinite) :
    (homCone R S T).π.app j = ModuleCat.ofHom (homConeπ R S T j) :=
  rfl

variable {R S T}

private theorem pairing_π_eq_of_hom (s : Cone (sectionsDiagram R S T))
    {j j' : StructuredArrow S FintypeCat.toProfinite} (k : j ⟶ j') (m : s.pt)
    (φ : LocallyConstant (FintypeCat.toProfinite.obj j'.right) ℤ) :
    locallyConstantFinsuppEquiv R _ T (s.π.app j' m) φ =
      locallyConstantFinsuppEquiv R _ T (s.π.app j m)
        (LocallyConstant.comap (FintypeCat.toProfinite.map k.right).hom.hom φ) := by
  have h : (s.π.app j' m :
        LocallyConstant T (ULift.{u + 1} (FintypeCat.toProfinite.obj j'.right) →₀ R)) =
      (s.π.app j m :
        LocallyConstant T (ULift.{u + 1} (FintypeCat.toProfinite.obj j.right) →₀ R)).map
        (Finsupp.mapDomain (ULift.map (FintypeCat.toProfinite.map k.right).hom.hom)) :=
    -- Composition in `ModuleCat` is composition of the underlying linear maps, and
    -- `(sectionsDiagram R S T).map k` is `LocallyConstant.mapₗ` of `Finsupp.lmapDomain`, both
    -- by definition.
    (congrArg (fun f ↦ f.hom m) (s.w k)).symm
  rw [h]
  exact DFunLike.congr_fun (locallyConstantFinsuppEquiv_map _ _) φ

/-- The pairing of a compatible family with an integer valued function on a finite quotient
depends only on the pulled back function on `S`. -/
private theorem pairing_π_eq (s : Cone (sectionsDiagram R S T)) (m : s.pt)
    {j₁ j₂ : StructuredArrow S FintypeCat.toProfinite}
    (φ₁ : LocallyConstant (FintypeCat.toProfinite.obj j₁.right) ℤ)
    (φ₂ : LocallyConstant (FintypeCat.toProfinite.obj j₂.right) ℤ)
    (h : LocallyConstant.comap j₁.hom.hom.hom φ₁ = LocallyConstant.comap j₂.hom.hom.hom φ₂) :
    locallyConstantFinsuppEquiv R _ T (s.π.app j₁ m) φ₁ =
      locallyConstantFinsuppEquiv R _ T (s.π.app j₂ m) φ₂ := by
  obtain ⟨j, k₁, k₂, hj⟩ := S.exists_structuredArrow_surjective_refinement j₁ j₂
  rw [pairing_π_eq_of_hom s k₁, pairing_π_eq_of_hom s k₂]
  congr 1
  apply LocallyConstant.comap_injective j.hom.hom.hom hj
  rw [Profinite.comap_comap_of_structuredArrow_hom k₁,
    Profinite.comap_comap_of_structuredArrow_hom k₂, h]

/-- The lift of a cone over `sectionsDiagram` to `homCone`, at one element of its apex, as a
function: `f` is paired with the image of `m` in the discrete quotient of `S` by the fibres of
`f`. -/
private noncomputable def homConeLiftFun (s : Cone (sectionsDiagram R S T)) (m : s.pt)
    (f : LocallyConstant S ℤ) : LocallyConstant T R :=
  locallyConstantFinsuppEquiv R _ T
    (s.π.app ((Profinite.Extend.functor S.asLimitCone).obj f.discreteQuotient) m)
    (S.liftOfDiscreteQuotient f)

/-- `homConeLiftFun` agrees with the pairing at every map from `S` to a finite set. -/
private theorem homConeLiftFun_comap (s : Cone (sectionsDiagram R S T)) (m : s.pt)
    (j : StructuredArrow S FintypeCat.toProfinite)
    (φ : LocallyConstant (FintypeCat.toProfinite.obj j.right) ℤ) :
    homConeLiftFun s m (LocallyConstant.comap j.hom.hom.hom φ) =
      locallyConstantFinsuppEquiv R _ T (s.π.app j m) φ :=
  pairing_π_eq s m _ _ (S.comap_liftOfDiscreteQuotient _)

/-- The lift of a cone over `sectionsDiagram` to `homCone`, at one element of its apex. -/
private noncomputable def homConeLiftAux (s : Cone (sectionsDiagram R S T)) (m : s.pt) :
    LocallyConstant S ℤ →+ LocallyConstant T R where
  toFun := homConeLiftFun s m
  map_zero' :=
    -- `LocallyConstant.comap _ 0` is `0` by definition.
    (homConeLiftFun_comap s m ((Profinite.Extend.functor S.asLimitCone).obj
      (0 : LocallyConstant S ℤ).discreteQuotient) 0).trans (map_zero _)
  map_add' f g := by
    obtain ⟨j, k₁, k₂, -⟩ := S.exists_structuredArrow_surjective_refinement
      ((Profinite.Extend.functor S.asLimitCone).obj f.discreteQuotient)
      ((Profinite.Extend.functor S.asLimitCone).obj g.discreteQuotient)
    let φ := LocallyConstant.comap (FintypeCat.toProfinite.map k₁.right).hom.hom
      (S.liftOfDiscreteQuotient f)
    let ψ := LocallyConstant.comap (FintypeCat.toProfinite.map k₂.right).hom.hom
      (S.liftOfDiscreteQuotient g)
    have hf : LocallyConstant.comap j.hom.hom.hom φ = f :=
      (Profinite.comap_comap_of_structuredArrow_hom k₁ _).trans
        (S.comap_liftOfDiscreteQuotient f)
    have hg : LocallyConstant.comap j.hom.hom.hom ψ = g :=
      (Profinite.comap_comap_of_structuredArrow_hom k₂ _).trans
        (S.comap_liftOfDiscreteQuotient g)
    have hfg : LocallyConstant.comap j.hom.hom.hom (φ + ψ) = f + g :=
      (map_add (LocallyConstant.comapAddMonoidHom j.hom.hom.hom) φ ψ).trans (congrArg₂ _ hf hg)
    rw [← hfg, ← hf, ← hg]
    simp only [homConeLiftFun_comap, map_add]

private theorem homConeLiftAux_apply (s : Cone (sectionsDiagram R S T)) (m : s.pt)
    (f : LocallyConstant S ℤ) : homConeLiftAux s m f = homConeLiftFun s m f :=
  rfl

variable (R S T)

/-- `Hom(C(S, ℤ), C(T, R))` is the limit of the sections over `T` of the free condensed modules
on the finite quotients of `S`. -/
private noncomputable def isLimitHomCone : IsLimit (homCone R S T) where
  lift s := ModuleCat.ofHom
    { toFun := homConeLiftAux s
      map_add' m₁ m₂ := by
        ext f : 1
        obtain ⟨j, φ, rfl⟩ := S.exists_structuredArrow_comap_eq f
        simp only [AddMonoidHom.add_apply, homConeLiftAux_apply, homConeLiftFun_comap, map_add]
        exact DFunLike.congr_fun (map_add (locallyConstantFinsuppEquiv R _ T) _ _) φ
      map_smul' r m := by
        ext f : 1
        obtain ⟨j, φ, rfl⟩ := S.exists_structuredArrow_comap_eq f
        simp only [AddMonoidHom.smul_apply, homConeLiftAux_apply, homConeLiftFun_comap, map_smul,
          RingHom.id_apply]
        exact DFunLike.congr_fun (map_smul (locallyConstantFinsuppEquiv R _ T) _ _) φ }
  fac s j := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
    apply (locallyConstantFinsuppEquiv R (FintypeCat.toProfinite.obj j.right) T).injective
    ext φ : 1
    exact (DFunLike.congr_fun (locallyConstantFinsuppEquiv_homConeπ R S T j _) φ).trans
      (homConeLiftFun_comap s m j φ)
  uniq s m' hm := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ AddMonoidHom.ext fun f ↦ ?_)
    obtain ⟨j, φ, rfl⟩ := S.exists_structuredArrow_comap_eq f
    have h : (s.π.app j).hom x = homConeπ R S T j (m'.hom x) := by
      rw [← hm, homCone_π_app]
      -- Composition in `ModuleCat` is composition of the underlying linear maps by definition.
      rfl
    exact (DFunLike.congr_fun (locallyConstantFinsuppEquiv_homConeπ R S T j (m'.hom x))
      φ).symm.trans
      ((congrArg (fun v ↦ locallyConstantFinsuppEquiv R _ T v φ) h.symm).trans
        (homConeLiftFun_comap s x j φ).symm)

/-- The limit cone defining `R[S]^solid`, evaluated at `T`, is a limit cone. -/
private noncomputable def isLimitSectionsCone :
    IsLimit ((Cone.postcompose (sectionsDiagramIso R S T).hom).obj
      ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op T)).mapCone
        ((Cone.postcompose (Functor.isoWhiskerLeft (StructuredArrow.proj S FintypeCat.toProfinite)
          (finFreeIso R)).hom).obj
            ((Functor.RightExtension.mk _ (profiniteSolidCounit R)).coneAt S)))) :=
  (IsLimit.postcomposeHomEquiv (sectionsDiagramIso R S T) _).symm
    (isLimitOfPreserves _ ((IsLimit.postcomposeHomEquiv _ _).symm
      (profiniteSolidIsPointwiseRightKanExtension R S)))

/-- The leg at `j` of the limit cone in `isLimitSectionsCone` is `profiniteSolidToFin R S j`
on sections over `T`. -/
private theorem sectionsCone_π_app (j : StructuredArrow S FintypeCat.toProfinite) :
    ((Cone.postcompose (sectionsDiagramIso R S T).hom).obj
      ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op T)).mapCone
        ((Cone.postcompose (Functor.isoWhiskerLeft (StructuredArrow.proj S FintypeCat.toProfinite)
          (finFreeIso R)).hom).obj
            ((Functor.RightExtension.mk _ (profiniteSolidCounit R)).coneAt S)))).π.app j =
      (profiniteSolidToFin R S j).hom.app (op T) := by
  simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Functor.mapCone_π_app,
    Functor.RightExtension.coneAt_π_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, evaluation_obj_map,
    Category.assoc, sectionsDiagramIso_hom_app, profiniteSolidToFin]
  -- `simp` cannot cancel the identity: its object `(sectionsDiagram R S T).obj j` is the
  -- sections of `(finLocallyConstant R).obj j.right` over `T` only by definition.
  exact Category.comp_id _

/-- The sections of `R[S]^solid` over `T` are `Hom(C(S, ℤ), C(T, R))`. -/
private noncomputable def profiniteSolidSectionsIso :
    ((profiniteSolid R).obj S).obj.obj (op T) ≅
      ModuleCat.of R (LocallyConstant S ℤ →+ LocallyConstant T R) :=
  (isLimitSectionsCone R S T).conePointUniqueUpToIso (isLimitHomCone R S T)

private theorem profiniteSolidSectionsIso_hom_apply_comap
    (x : ((profiniteSolid R).obj S).obj.obj (op T)) (j : StructuredArrow S FintypeCat.toProfinite)
    (φ : LocallyConstant (FintypeCat.toProfinite.obj j.right) ℤ) :
    (profiniteSolidSectionsIso R S T).hom x (LocallyConstant.comap j.hom.hom.hom φ) =
      locallyConstantFinsuppEquiv R (FintypeCat.toProfinite.obj j.right) T
        ((profiniteSolidToFin R S j).hom.app (op T) x :
          LocallyConstant T (ULift.{u + 1} (FintypeCat.toProfinite.obj j.right) →₀ R)) φ := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp (isLimitSectionsCone R S T)
    (isLimitHomCone R S T) j
  rw [homCone_π_app, sectionsCone_π_app] at h
  -- `profiniteSolidSectionsIso` is this `conePointUniqueUpToIso` by definition, and composition
  -- in `ModuleCat` is composition of the underlying linear maps by definition.
  have h' := congrArg (fun v ↦ locallyConstantFinsuppEquiv R _ T v φ)
    (congrArg (fun f ↦ f.hom x) h)
  exact (DFunLike.congr_fun (locallyConstantFinsuppEquiv_homConeπ R S T j _) φ).symm.trans h'

private theorem profiniteSolidSectionsIso_naturality {T T' : CompHaus.{u}} (g : T' ⟶ T)
    (x : ((profiniteSolid R).obj S).obj.obj (op T)) :
    (profiniteSolidSectionsIso R S T').hom (((profiniteSolid R).obj S).obj.map g.op x) =
      (LocallyConstant.comapAddMonoidHom g.hom.hom).comp
        ((profiniteSolidSectionsIso R S T).hom x) := by
  ext f : 1
  obtain ⟨j, φ, rfl⟩ := S.exists_structuredArrow_comap_eq f
  -- Both sides are the pairing of `φ` with the image of `x` in `R[F]`, pulled back along `g`.
  -- Two steps hold by definition: the restriction maps of the discrete condensed module
  -- `(finLocallyConstant R).obj j.right` are `LocallyConstant.comap`, so the output of
  -- `CondensedMod.hom_naturality_apply` is the `v.comap g.hom.hom` expected by
  -- `locallyConstantFinsuppEquiv_comap`; and the right-hand side applied to `comap j φ` is
  -- `comap g.hom.hom` of `(profiniteSolidSectionsIso R S T).hom x (comap j φ)` by
  -- `AddMonoidHom.comp_apply`.
  refine (profiniteSolidSectionsIso_hom_apply_comap R S T' _ j φ).trans ?_
  refine (congrArg (fun v ↦ locallyConstantFinsuppEquiv R _ T' v φ)
    (CondensedMod.hom_naturality_apply R (profiniteSolidToFin R S j) g.op x)).trans ?_
  exact (locallyConstantFinsuppEquiv_comap _ _ _).trans
    (congrArg (LocallyConstant.comap g.hom.hom)
      (profiniteSolidSectionsIso_hom_apply_comap R S T x j φ).symm)

/-- The presheaf underlying `R[S]^solid` is `locallyConstantIntDualPresheaf R S`. -/
noncomputable def profiniteSolidPresheafIso :
    ((profiniteSolid R).obj S).obj ≅ locallyConstantIntDualPresheaf R S :=
  NatIso.ofComponents (fun T ↦ profiniteSolidSectionsIso R S T.unop) fun g ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ profiniteSolidSectionsIso_naturality R S g.unop x)

/-- The condensed `R`-module `T ↦ Hom_ℤ(C(S, ℤ), C(T, R))` of `R`-valued measures on the
profinite set `S`, where `C(-, -)` denotes locally constant functions. It is the free solid
module `R[S]^solid` (`profiniteSolidIsoLocallyConstantIntDual`). -/
@[expose]
noncomputable def locallyConstantIntDual : CondensedMod.{u} R :=
  ⟨locallyConstantIntDualPresheaf R S,
    (Presheaf.isSheaf_of_iso_iff (profiniteSolidPresheafIso R S)).mp
      ((profiniteSolid R).obj S).property⟩

@[simp]
theorem locallyConstantIntDual_obj :
    (locallyConstantIntDual R S).obj = locallyConstantIntDualPresheaf R S :=
  (rfl)

/-- The free solid module `R[S]^solid` on a profinite set `S` is the condensed module
`T ↦ Hom_ℤ(C(S, ℤ), C(T, R))` of `R`-valued measures on `S`. -/
noncomputable def profiniteSolidIsoLocallyConstantIntDual :
    (profiniteSolid R).obj S ≅ locallyConstantIntDual R S :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (profiniteSolidPresheafIso R S)

/-- `profiniteSolidIsoLocallyConstantIntDual` sends a section `x` of `R[S]^solid` to the measure
whose value on the pullback of `φ : C(F, ℤ)` along a map `S → F` to a finite set is the pairing
of `φ` with the image of `x` in `R[F]`. -/
theorem profiniteSolidIsoLocallyConstantIntDual_hom_app_apply
    (x : ((profiniteSolid R).obj S).obj.obj (op T)) (j : StructuredArrow S FintypeCat.toProfinite)
    (φ : LocallyConstant (FintypeCat.toProfinite.obj j.right) ℤ) :
    -- The section is an element of the carrier of a `ModuleCat`, which elaboration does not unfold
    -- to the function type `LocallyConstant S ℤ →+ LocallyConstant T R`; `show` exposes it so that
    -- the section can be applied.
    (show LocallyConstant S ℤ →+ LocallyConstant T R from
        (profiniteSolidIsoLocallyConstantIntDual R S).hom.hom.app (op T) x)
        (LocallyConstant.comap j.hom.hom.hom φ) =
      locallyConstantFinsuppEquiv R (FintypeCat.toProfinite.obj j.right) T
        ((profiniteSolidToFin R S j).hom.app (op T) x :
          LocallyConstant T (ULift.{u + 1} (FintypeCat.toProfinite.obj j.right) →₀ R)) φ :=
  profiniteSolidSectionsIso_hom_apply_comap R S T x j φ

variable {R S}

/-- Evaluation of measures on a locally constant function `f : C(S, ℤ)`, as a morphism from
`locallyConstantIntDual R S` to the discrete condensed module `R`. -/
noncomputable def locallyConstantIntDualEval (f : LocallyConstant S ℤ) :
    locallyConstantIntDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R) :=
  ObjectProperty.homMk
    { app T := ModuleCat.ofHom
        { toFun h := (h : LocallyConstant S ℤ →+ LocallyConstant T.unop R) f
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      naturality _ _ _ := rfl }

@[simp]
theorem locallyConstantIntDualEval_hom_app_apply (f : LocallyConstant S ℤ) (T : CompHaus.{u}ᵒᵖ)
    (h : LocallyConstant S ℤ →+ LocallyConstant T.unop R) :
    (locallyConstantIntDualEval (R := R) f).hom.app T h = h f :=
  (rfl)

/-- The fan exhibiting `locallyConstantIntDual R S` as a product of copies of the discrete condensed
module `R`, given a `ℤ`-basis `b` of `C(S, ℤ)`: its legs evaluate measures on the basis
vectors. -/
noncomputable def locallyConstantIntDualFan {I : Type u}
    (b : Module.Basis I ℤ (LocallyConstant S ℤ)) :
    Fan fun _ : I ↦ (CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R) :=
  Fan.mk (locallyConstantIntDual R S) fun i ↦ locallyConstantIntDualEval (b i)

/-- A `ℤ`-basis of `C(S, ℤ)` indexed by `I` exhibits `locallyConstantIntDual R S` as the product of
`I` copies of the discrete condensed module `R`. -/
noncomputable def isLimitLocallyConstantIntDualFan {I : Type u}
    (b : Module.Basis I ℤ (LocallyConstant S ℤ)) :
    IsLimit (locallyConstantIntDualFan (R := R) b) :=
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ fun T ↦
    let e : (LocallyConstant S ℤ →+ LocallyConstant T.unop R) ≃ₗ[R]
        (I → LocallyConstant T.unop R) :=
      addMonoidHomLequivInt R ≪≫ₗ (b.constr R).symm
    -- The `i`-th coordinate of `e h` is `h (b i)`, the value of the leg
    -- `locallyConstantIntDualEval`.
    have he (h : LocallyConstant S ℤ →+ LocallyConstant T.unop R) (i : I) : e h i = h (b i) := by
      simp [e]
    -- In `fac` and `uniq`, `(f ≫ (locallyConstantIntDualFan b).π.app ⟨i⟩).hom x` is
    -- `(x' : _ →+ _) (b i)` for `x' := f.hom x`, by definition: composition in `ModuleCat` is
    -- composition of the underlying linear maps, the legs of `Fan.mk` are the given maps, and
    -- `locallyConstantIntDualEval (b i)` evaluates at `b i`
    -- (`locallyConstantIntDualEval_hom_app_apply`).
    { lift s := ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ LinearMap.pi fun i ↦ (s.π.app ⟨i⟩).hom)
      fac s i := ModuleCat.hom_ext (LinearMap.ext fun x ↦ (he _ i.as).symm.trans
        (congrFun (e.apply_symm_apply fun i ↦ (s.π.app ⟨i⟩).hom x) i.as))
      uniq s m hm := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ e.injective ?_)
        refine Eq.trans ?_ (e.apply_symm_apply _).symm
        funext i
        exact (he _ i).trans (congrArg (fun f ↦ f.hom x) (hm ⟨i⟩)) })

local instance : HasLimitsOfSize.{u, u} (CondensedMod.{u} R) :=
  hasLimitsOfSizeShrink.{u, u, u, u + 1} _

/-- A `ℤ`-basis of `C(S, ℤ)` indexed by `I` identifies `locallyConstantIntDual R S` with the product
of `I` copies of the discrete condensed module `R`. -/
noncomputable def locallyConstantIntDualIsoPi {I : Type u}
    (b : Module.Basis I ℤ (LocallyConstant S ℤ)) :
    locallyConstantIntDual R S ≅ ∏ᶜ fun _ : I ↦ (discrete (ModuleCat R)).obj (ModuleCat.of R R) :=
  (isLimitLocallyConstantIntDualFan b).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    Pi.mapIso fun _ ↦ (CondensedMod.LocallyConstant.functorIsoDiscrete R).app _

/-- The `i`-th component of `locallyConstantIntDualIsoPi b` evaluates measures on the basis vector
`b i`. -/
@[reassoc (attr := simp)]
theorem locallyConstantIntDualIsoPi_hom_π {I : Type u} (b : Module.Basis I ℤ (LocallyConstant S ℤ))
    (i : I) :
    (locallyConstantIntDualIsoPi b).hom ≫ Pi.π _ i =
      locallyConstantIntDualEval (b i) ≫
        (CondensedMod.LocallyConstant.functorIsoDiscrete R).hom.app (ModuleCat.of R R) := by
  simp only [locallyConstantIntDualIsoPi, limit.cone_x, locallyConstantIntDualFan, Iso.trans_hom,
    Category.assoc, Pi.mapIso_hom_π, Iso.app_hom]
  exact (isLimitLocallyConstantIntDualFan (R := R) b).conePointUniqueUpToIso_hom_comp_assoc
    (limit.isLimit _) ⟨i⟩ _

variable (R S)

/-- The free solid module `R[S]^solid` on a profinite set `S` is a product of copies of the
discrete condensed module `R`: by Nöbeling's theorem `C(S, ℤ)` is a free abelian group. -/
theorem exists_profiniteSolid_iso_pi :
    ∃ I : Type u, Nonempty ((profiniteSolid R).obj S ≅
      ∏ᶜ fun _ : I ↦ (discrete (ModuleCat R)).obj (ModuleCat.of R R)) :=
  have := LocallyConstant.freeOfProfinite S
  ⟨_, ⟨profiniteSolidIsoLocallyConstantIntDual R S ≪≫
    locallyConstantIntDualIsoPi (Module.Free.chooseBasis ℤ (LocallyConstant S ℤ))⟩⟩

end TauCeti
