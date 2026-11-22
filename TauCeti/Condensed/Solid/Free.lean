/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Solid
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.Topology.Category.Profinite.Nobeling.Induction
public import TauCeti.Condensed.Discrete.Free
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
(`TauCeti.profiniteSolidIsoLocallyConstantDual`). By Nöbeling's theorem
(`LocallyConstant.freeOfProfinite`) `C(S, ℤ)` is a free abelian group, and a basis indexed by `I`
identifies `R[S]^solid` with the product of `I` copies of the discrete condensed module `R`
(`TauCeti.locallyConstantDualIsoPi`, `TauCeti.exists_profiniteSolid_iso_pi`).

The proof evaluates the limit defining `R[S]^solid` on a compact Hausdorff space `T`. There the
free condensed module on a finite set `F` has sections `LocallyConstant T (F →₀ R)`
(`TauCeti.finFreeIso`), which is `Hom(C(F, ℤ), C(T, R))` by
`TauCeti.locallyConstantFinsuppEquiv`. The limit of these over maps `S → F` is
`Hom(C(S, ℤ), C(T, R))`, because every locally constant function on `S` factors through a finite
discrete quotient and any two such factorizations have a common refinement.

## Main definitions and results

* `TauCeti.finFreeIso`: the free condensed module on a finite set `F` is the discrete condensed
  module on `F →₀ R`.
* `TauCeti.locallyConstantDual`: the condensed module `T ↦ Hom_ℤ(C(S, ℤ), C(T, R))`.
* `TauCeti.profiniteSolidIsoLocallyConstantDual`: the isomorphism
  `R[S]^solid ≅ locallyConstantDual R S`, characterized by
  `TauCeti.profiniteSolidIsoLocallyConstantDual_hom_app_apply`.
* `TauCeti.isLimitLocallyConstantDualFan`, `TauCeti.locallyConstantDualIsoPi`: a `ℤ`-basis of
  `C(S, ℤ)` indexed by `I` exhibits `locallyConstantDual R S` as the product of `I` copies of
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
  Functor.isoWhiskerRight fintypeToCondensedIso (free R) ≪≫
    Functor.isoWhiskerLeft (FintypeCat.incl ⋙ uliftFunctor.{u + 1}) (freeLocallyConstantIso R)

variable (S : Profinite.{u})

/-- The presheaf `T ↦ Hom_ℤ(C(S, ℤ), C(T, R))` of `R`-valued measures on `S`, where `C(-, -)`
denotes locally constant functions. -/
@[expose]
noncomputable def locallyConstantDualPresheaf : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj T := ModuleCat.of R (LocallyConstant S ℤ →+ LocallyConstant T.unop R)
  map g := ModuleCat.ofHom
    { toFun h := (LocallyConstant.comapAddMonoidHom g.unop.hom.hom).comp h
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

@[simp]
theorem locallyConstantDualPresheaf_obj (T : CompHaus.{u}ᵒᵖ) :
    (locallyConstantDualPresheaf R S).obj T =
      ModuleCat.of R (LocallyConstant S ℤ →+ LocallyConstant T.unop R) :=
  (rfl)

@[simp]
theorem locallyConstantDualPresheaf_map_hom_apply {T T' : CompHaus.{u}ᵒᵖ} (g : T ⟶ T')
    (h : LocallyConstant S ℤ →+ LocallyConstant T.unop R) :
    (locallyConstantDualPresheaf R S).map g h =
      (LocallyConstant.comapAddMonoidHom g.unop.hom.hom).comp h :=
  (rfl)

/-- The component, at a map `S ⟶ F` to a finite set, of the limit cone defining `R[S]^solid`,
followed by `finFreeIso`: the projection `R[S]^solid ⟶ R[F]`. -/
noncomputable def profiniteSolidToFin (j : StructuredArrow S FintypeCat.toProfinite) :
    (profiniteSolid R).obj S ⟶ (finLocallyConstant R).obj j.right :=
  ((Functor.RightExtension.mk _ (profiniteSolidCounit R)).coneAt S).π.app j ≫
    (finFreeIso R).hom.app j.right

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
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

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

omit [Ring R] in
private theorem comap_comap_of_hom {j j' : StructuredArrow S FintypeCat.toProfinite} (k : j ⟶ j')
    {Z : Type*} (φ : LocallyConstant (FintypeCat.toProfinite.obj j'.right) Z) :
    LocallyConstant.comap j.hom.hom.hom
        (LocallyConstant.comap (FintypeCat.toProfinite.map k.right).hom.hom φ) =
      LocallyConstant.comap j'.hom.hom.hom φ := by
  ext x
  exact congrArg φ (congrArg (fun f ↦ f.hom.hom x) (StructuredArrow.w k))

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
  exact comap_comap_of_hom S k φ

/-- The cone with apex `Hom(C(S, ℤ), C(T, R))` over `sectionsDiagram`. -/
private noncomputable def homCone : Cone (sectionsDiagram R S T) where
  pt := ModuleCat.of R (LocallyConstant S ℤ →+ LocallyConstant T R)
  π :=
    { app j := ModuleCat.ofHom (homConeπ R S T j)
      naturality _ _ k :=
        ModuleCat.hom_ext (LinearMap.ext fun h ↦ (homConeπ_naturality R S T k h).symm) }

/-- The projection of `S` to a discrete quotient, as an object of the indexing category. -/
private noncomputable def ofDiscreteQuotient (Q : DiscreteQuotient S) :
    StructuredArrow S FintypeCat.toProfinite :=
  StructuredArrow.mk (S.asLimitCone.π.app Q)

/-- A locally constant function on `S`, as a function on its discrete quotient by fibres. -/
private noncomputable def liftOfDiscreteQuotient (f : LocallyConstant S ℤ) :
    LocallyConstant (FintypeCat.toProfinite.obj (ofDiscreteQuotient S f.discreteQuotient).right)
      ℤ :=
  ⟨(f.lift : _ → ℤ), IsLocallyConstant.of_discrete _⟩

private theorem comap_liftOfDiscreteQuotient (f : LocallyConstant S ℤ) :
    LocallyConstant.comap (ofDiscreteQuotient S f.discreteQuotient).hom.hom.hom
      (liftOfDiscreteQuotient S f) = f :=
  rfl

/-- Any two maps from `S` to finite sets factor through a common surjection onto a finite set. -/
private theorem exists_refinement (j₁ j₂ : StructuredArrow S FintypeCat.toProfinite) :
    ∃ (j : StructuredArrow S FintypeCat.toProfinite) (_ : j ⟶ j₁) (_ : j ⟶ j₂),
      Function.Surjective j.hom.hom.hom := by
  let f : LocallyConstant S
      (FintypeCat.toProfinite.obj j₁.right × FintypeCat.toProfinite.obj j₂.right) :=
    ⟨fun x ↦ (j₁.hom x, j₂.hom x),
      ((IsLocallyConstant.iff_continuous _).mpr j₁.hom.hom.hom.continuous).prodMk
        ((IsLocallyConstant.iff_continuous _).mpr j₂.hom.hom.hom.continuous)⟩
  refine ⟨ofDiscreteQuotient S f.discreteQuotient,
    StructuredArrow.homMk (FintypeCat.homMk fun q ↦ (f.lift q).1) ?_,
    StructuredArrow.homMk (FintypeCat.homMk fun q ↦ (f.lift q).2) ?_,
    f.discreteQuotient.proj_surjective⟩
  · ext x
    rfl
  · ext x
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
  obtain ⟨j, k₁, k₂, hj⟩ := exists_refinement S j₁ j₂
  rw [pairing_π_eq_of_hom s k₁, pairing_π_eq_of_hom s k₂]
  congr 1
  apply LocallyConstant.comap_injective _ hj
  rw [comap_comap_of_hom S k₁, comap_comap_of_hom S k₂, h]

/-- The lift of a cone over `sectionsDiagram` to `homCone`, at one element of its apex. -/
private noncomputable def homConeLiftAux (s : Cone (sectionsDiagram R S T)) (m : s.pt) :
    LocallyConstant S ℤ →+ LocallyConstant T R where
  toFun f := locallyConstantFinsuppEquiv R _ T
    (s.π.app (ofDiscreteQuotient S f.discreteQuotient) m) (liftOfDiscreteQuotient S f)
  map_zero' := by
    rw [pairing_π_eq s m _ (0 : LocallyConstant (FintypeCat.toProfinite.obj
      (ofDiscreteQuotient S (0 : LocallyConstant S ℤ).discreteQuotient).right) ℤ)
      (by rw [comap_liftOfDiscreteQuotient]; rfl), map_zero]
  map_add' f g := by
    obtain ⟨j, k₁, k₂, -⟩ := exists_refinement S (ofDiscreteQuotient S f.discreteQuotient)
      (ofDiscreteQuotient S g.discreteQuotient)
    rw [pairing_π_eq s m _
        (LocallyConstant.comap (FintypeCat.toProfinite.map k₁.right).hom.hom
          (liftOfDiscreteQuotient S f) +
        LocallyConstant.comap (FintypeCat.toProfinite.map k₂.right).hom.hom
          (liftOfDiscreteQuotient S g)),
      map_add, ← pairing_π_eq_of_hom, ← pairing_π_eq_of_hom]
    rw [comap_liftOfDiscreteQuotient, ← LocallyConstant.comapAddMonoidHom_apply j.hom.hom.hom,
      map_add, LocallyConstant.comapAddMonoidHom_apply, LocallyConstant.comapAddMonoidHom_apply,
      comap_comap_of_hom S k₁, comap_comap_of_hom S k₂, comap_liftOfDiscreteQuotient,
      comap_liftOfDiscreteQuotient]

private theorem homConeLiftAux_comap (s : Cone (sectionsDiagram R S T)) (m : s.pt)
    (j : StructuredArrow S FintypeCat.toProfinite)
    (φ : LocallyConstant (FintypeCat.toProfinite.obj j.right) ℤ) :
    homConeLiftAux s m (LocallyConstant.comap j.hom.hom.hom φ) =
      locallyConstantFinsuppEquiv R _ T (s.π.app j m) φ :=
  pairing_π_eq s m _ _ (comap_liftOfDiscreteQuotient S _)

variable (R S T)

/-- `Hom(C(S, ℤ), C(T, R))` is the limit of the sections over `T` of the free condensed modules
on the finite quotients of `S`. -/
private noncomputable def isLimitHomCone : IsLimit (homCone R S T) where
  lift s := ModuleCat.ofHom
    { toFun := homConeLiftAux s
      map_add' m₁ m₂ := by
        ext f : 1
        simp only [homConeLiftAux, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add,
          AddMonoidHom.add_apply]
        exact DFunLike.congr_fun (map_add (locallyConstantFinsuppEquiv R _ T) _ _) _
      map_smul' r m := by
        ext f : 1
        simp only [homConeLiftAux, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul,
          RingHom.id_apply, AddMonoidHom.smul_apply]
        exact DFunLike.congr_fun (map_smul (locallyConstantFinsuppEquiv R _ T) _ _) _ }
  fac s j := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
    apply (locallyConstantFinsuppEquiv R (FintypeCat.toProfinite.obj j.right) T).injective
    ext φ : 1
    exact (DFunLike.congr_fun (locallyConstantFinsuppEquiv_homConeπ R S T j _) φ).trans
      (homConeLiftAux_comap s m j φ)
  uniq s m' hm := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ AddMonoidHom.ext fun f ↦ ?_)
    have h : (s.π.app (ofDiscreteQuotient S f.discreteQuotient)).hom x =
        homConeπ R S T _ (m'.hom x) := by
      rw [← hm]
      rfl
    refine (DFunLike.congr_fun (locallyConstantFinsuppEquiv_homConeπ R S T
      (ofDiscreteQuotient S f.discreteQuotient) (m'.hom x)) (liftOfDiscreteQuotient S f)).symm.trans
      ?_
    exact congrArg (fun v ↦ locallyConstantFinsuppEquiv R _ T v (liftOfDiscreteQuotient S f))
      h.symm

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
  have h := congrArg (fun f ↦ f.hom x)
    (IsLimit.conePointUniqueUpToIso_hom_comp (isLimitSectionsCone R S T) (isLimitHomCone R S T) j)
  have h' := congrArg (fun v ↦ locallyConstantFinsuppEquiv R _ T v φ) h
  exact (DFunLike.congr_fun (locallyConstantFinsuppEquiv_homConeπ R S T j _) φ).symm.trans h'

private theorem profiniteSolidSectionsIso_naturality {T T' : CompHaus.{u}} (g : T' ⟶ T)
    (x : ((profiniteSolid R).obj S).obj.obj (op T)) :
    (profiniteSolidSectionsIso R S T').hom (((profiniteSolid R).obj S).obj.map g.op x) =
      (LocallyConstant.comapAddMonoidHom g.hom.hom).comp
        ((profiniteSolidSectionsIso R S T).hom x) := by
  ext f : 1
  rw [← comap_liftOfDiscreteQuotient S f, profiniteSolidSectionsIso_hom_apply_comap,
    AddMonoidHom.comp_apply, profiniteSolidSectionsIso_hom_apply_comap,
    LocallyConstant.comapAddMonoidHom_apply, CondensedMod.hom_naturality_apply]
  exact locallyConstantFinsuppEquiv_comap _ _ _

/-- The presheaf underlying `R[S]^solid` is `locallyConstantDualPresheaf R S`. -/
noncomputable def profiniteSolidPresheafIso :
    ((profiniteSolid R).obj S).obj ≅ locallyConstantDualPresheaf R S :=
  NatIso.ofComponents (fun T ↦ profiniteSolidSectionsIso R S T.unop) fun g ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ profiniteSolidSectionsIso_naturality R S g.unop x)

/-- The condensed `R`-module `T ↦ Hom_ℤ(C(S, ℤ), C(T, R))` of `R`-valued measures on the
profinite set `S`, where `C(-, -)` denotes locally constant functions. It is the free solid
module `R[S]^solid` (`profiniteSolidIsoLocallyConstantDual`). -/
@[expose]
noncomputable def locallyConstantDual : CondensedMod.{u} R :=
  ⟨locallyConstantDualPresheaf R S, (Presheaf.isSheaf_of_iso_iff (profiniteSolidPresheafIso R S)).mp
    ((profiniteSolid R).obj S).property⟩

@[simp]
theorem locallyConstantDual_obj : (locallyConstantDual R S).obj = locallyConstantDualPresheaf R S :=
  (rfl)

/-- The free solid module `R[S]^solid` on a profinite set `S` is the condensed module
`T ↦ Hom_ℤ(C(S, ℤ), C(T, R))` of `R`-valued measures on `S`. -/
noncomputable def profiniteSolidIsoLocallyConstantDual :
    (profiniteSolid R).obj S ≅ locallyConstantDual R S :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (profiniteSolidPresheafIso R S)

/-- `profiniteSolidIsoLocallyConstantDual` sends a section `x` of `R[S]^solid` to the measure
whose value on the pullback of `φ : C(F, ℤ)` along a map `S → F` to a finite set is the pairing
of `φ` with the image of `x` in `R[F]`. -/
theorem profiniteSolidIsoLocallyConstantDual_hom_app_apply
    (x : ((profiniteSolid R).obj S).obj.obj (op T)) (j : StructuredArrow S FintypeCat.toProfinite)
    (φ : LocallyConstant (FintypeCat.toProfinite.obj j.right) ℤ) :
    (show LocallyConstant S ℤ →+ LocallyConstant T R from
        (profiniteSolidIsoLocallyConstantDual R S).hom.hom.app (op T) x)
        (LocallyConstant.comap j.hom.hom.hom φ) =
      locallyConstantFinsuppEquiv R (FintypeCat.toProfinite.obj j.right) T
        ((profiniteSolidToFin R S j).hom.app (op T) x :
          LocallyConstant T (ULift.{u + 1} (FintypeCat.toProfinite.obj j.right) →₀ R)) φ :=
  profiniteSolidSectionsIso_hom_apply_comap R S T x j φ

variable {R S}

/-- Evaluation of measures on a locally constant function `f : C(S, ℤ)`, as a morphism from
`locallyConstantDual R S` to the discrete condensed module `R`. -/
noncomputable def locallyConstantDualEval (f : LocallyConstant S ℤ) :
    locallyConstantDual R S ⟶ (CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R) :=
  ObjectProperty.homMk
    { app T := ModuleCat.ofHom
        { toFun h := (h : LocallyConstant S ℤ →+ LocallyConstant T.unop R) f
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      naturality _ _ _ := rfl }

@[simp]
theorem locallyConstantDualEval_hom_app_apply (f : LocallyConstant S ℤ) (T : CompHaus.{u}ᵒᵖ)
    (h : LocallyConstant S ℤ →+ LocallyConstant T.unop R) :
    (show LocallyConstant T.unop R from (locallyConstantDualEval (R := R) f).hom.app T h) = h f :=
  (rfl)

/-- The fan exhibiting `locallyConstantDual R S` as a product of copies of the discrete condensed
module `R`, given a `ℤ`-basis `b` of `C(S, ℤ)`: its legs evaluate measures on the basis
vectors. -/
noncomputable def locallyConstantDualFan {I : Type u} (b : Module.Basis I ℤ (LocallyConstant S ℤ)) :
    Fan fun _ : I ↦ (CondensedMod.LocallyConstant.functor R).obj (ModuleCat.of R R) :=
  Fan.mk (locallyConstantDual R S) fun i ↦ locallyConstantDualEval (b i)

/-- A `ℤ`-basis of `C(S, ℤ)` indexed by `I` exhibits `locallyConstantDual R S` as the product of
`I` copies of the discrete condensed module `R`. -/
noncomputable def isLimitLocallyConstantDualFan {I : Type u}
    (b : Module.Basis I ℤ (LocallyConstant S ℤ)) :
    IsLimit (locallyConstantDualFan (R := R) b) :=
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ fun T ↦
    let e : (LocallyConstant S ℤ →+ LocallyConstant T.unop R) ≃ₗ[R]
        (I → LocallyConstant T.unop R) :=
      addMonoidHomLequivInt R ≪≫ₗ (b.constr R).symm
    { lift s := ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ LinearMap.pi fun i ↦ (s.π.app ⟨i⟩).hom)
      fac s i := ModuleCat.hom_ext (LinearMap.ext fun x ↦
        congrFun (e.apply_symm_apply fun i ↦ (s.π.app ⟨i⟩).hom x) i.as)
      uniq s m hm := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ e.injective ?_)
        refine Eq.trans ?_ (e.apply_symm_apply _).symm
        funext i
        exact congrArg (fun f ↦ f.hom x) (hm ⟨i⟩) })

local instance : HasLimitsOfSize.{u, u} (CondensedMod.{u} R) :=
  hasLimitsOfSizeShrink.{u, u, u, u + 1} _

/-- A `ℤ`-basis of `C(S, ℤ)` indexed by `I` identifies `locallyConstantDual R S` with the product
of `I` copies of the discrete condensed module `R`. -/
noncomputable def locallyConstantDualIsoPi {I : Type u}
    (b : Module.Basis I ℤ (LocallyConstant S ℤ)) :
    locallyConstantDual R S ≅ ∏ᶜ fun _ : I ↦ (discrete (ModuleCat R)).obj (ModuleCat.of R R) :=
  (isLimitLocallyConstantDualFan b).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    Pi.mapIso fun _ ↦ (CondensedMod.LocallyConstant.functorIsoDiscrete R).app _

variable (R S)

/-- The free solid module `R[S]^solid` on a profinite set `S` is a product of copies of the
discrete condensed module `R`: by Nöbeling's theorem `C(S, ℤ)` is a free abelian group. -/
theorem exists_profiniteSolid_iso_pi :
    ∃ I : Type u, Nonempty ((profiniteSolid R).obj S ≅
      ∏ᶜ fun _ : I ↦ (discrete (ModuleCat R)).obj (ModuleCat.of R R)) :=
  have := LocallyConstant.freeOfProfinite S
  ⟨_, ⟨profiniteSolidIsoLocallyConstantDual R S ≪≫
    locallyConstantDualIsoPi (Module.Free.chooseBasis ℤ (LocallyConstant S ℤ))⟩⟩

end TauCeti
