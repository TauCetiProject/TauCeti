/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LocalCohomology.RightDerived
public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.RingTheory.Depth.LocalCohomology
public import TauCeti.Topology.Sheaves.SupportedCohomology.Derived
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Flasque
import TauCeti.Topology.Sheaves.SupportedCohomology.Resolution

/-!
# Algebraic local cohomology and sheaf cohomology with closed supports

Let `R` be a commutative ring, `I` an ideal of `R`, and `M` an `R`-module with associated
quasi-coherent sheaf `M~` on `Spec R`. Write `V(I)` (`AlgebraicGeometry.Spec.zeroLocusClosed I`)
for the closed vanishing locus of `I` in `Spec R`.

1. **Degree zero (`I.FG`).** A global section `m ∈ M ≅ Γ(Spec R, M~)` restricts to zero on
   `Spec R \ V(I) = ⋃_{f ∈ I} D(f)` if and only if every `f ∈ I` annihilates `m` at some power.
   When `I` is finitely generated, this holds if and only if `m ∈ I.primaryComponent M`, giving a
   natural isomorphism
   `tildeSheafFunctor R ⋙ supportedSubmoduleSectionsFunctor (Spec.zeroLocusClosed I) ⊤ ≅
     I.primaryComponentFunctor` (`tildeCompSupportedSubmoduleSectionsTopIso`).
2. **All degrees (`IsNoetherianRing R`, Stacks 0955 and 0A6T).** The functor
   `tildeSheafFunctor R : M ↦ M~` is exact and sends injective `R`-modules over a Noetherian ring
   to flasque sheaves (`isFlasque_tilde_of_injective`), while flasque sheaves are adapted to
   `supportedSubmoduleSectionsFunctor`
   (`shortExact_map_supportedSubmoduleSectionsFunctor_of_isFlasque`). Right deriving via
   `Functor.compRightDerivedIsoOfResolution` identifies
   `tildeSheafFunctor R ⋙
     (supportedSubmoduleSectionsFunctor (Spec.zeroLocusClosed I) ⊤).rightDerived q`
   with `I.primaryComponentFunctor.rightDerived q` (`tildeCompRightDerivedSupportedSectionsIso`),
   and combining with `rightDerivedSupportedSubmoduleSectionsIso` and
   `localCohomology.isoRightDerivedPrimaryComponent` gives the natural isomorphism with algebraic
   local cohomology (`tildeCompSupportedModuleHTopIsoLocalCohomology`,
   `supportedModuleHTopTildeLinearEquivLocalCohomology`):
   `H^q_{V(I)}(Spec R, M~) ≃ₗ[R] H^q_I(M)`.
3. **Depth vanishing (`IsNoetherianRing R`, Stacks 0AVZ).** Over a Noetherian ring,
   `H^q_{V(I)}(Spec R, M~)` vanishes for `q < I.depth M` when `M` is finite.

## Main definitions

* `TauCeti.AlgebraicGeometry.tildeCompSupportedSubmoduleSectionsTopIso`: the degree-zero natural
  isomorphism `M ↦ Γ_{V(I)}(Spec R, M~) ≅ Γ_I(M)` for finitely generated `I`.
* `TauCeti.AlgebraicGeometry.tildeCompRightDerivedSupportedSectionsIso` (Stacks 0955): the natural
  isomorphism `(R^q Γ_{V(I)}(Spec R, -)) ∘ (~) ≅ R^q Γ_I` over a Noetherian ring `R`.
* `TauCeti.AlgebraicGeometry.tildeCompSupportedModuleHTopIsoLocalCohomology` and
  `TauCeti.AlgebraicGeometry.supportedModuleHTopTildeLinearEquivLocalCohomology` (Stacks 0A6T):
  the comparison `H^q_{V(I)}(Spec R, M~) ≃ₗ[R] H^q_I(M)` over a Noetherian ring `R`.

## Main results

* `TauCeti.AlgebraicGeometry.subsingleton_supportedModuleH_tilde_of_lt_depth` (Stacks 0AVZ):
  `H^q_{V(I)}(Spec R, M~)` vanishes for `q < I.depth M` when `R` is Noetherian and `M` is finite.

## References

* [The Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [The Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [The Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
* A. Grothendieck, *Local Cohomology*, Lecture Notes in Mathematics 41, Proposition 2.2.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, §3.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open PrimeSpectrum CategoryTheory.Sheaf

section Comparison

variable {R : CommRingCat.{u}}

/-- For any set `s ⊆ R` and element `m : M`, the global section `tilde.toOpen M ⊤ m` of `M~` is
supported in `V(s)` if and only if every `f ∈ s` annihilates `m` at some power. -/
theorem tilde_toOpen_top_mem_supportedSubmodule_iff (s : Set R) (M : ModuleCat.{u} R) (m : M) :
    tilde.toOpen M ⊤ m ∈
        (modulesSpecToSheaf.obj (tilde M)).supportedSubmodule
          (Spec.zeroLocusClosed (R := R) s) ⊤ ↔
      ∀ f ∈ s, ∃ n : ℕ, f ^ n • m = 0 := by
  let Z : Closeds (Spec R) := Spec.zeroLocusClosed s
  let F := modulesSpecToSheaf.obj (tilde M)
  rw [F.mem_supportedSubmodule_iff]
  have hres : F.obj.map (Z.complInclusion ⊤).op (tilde.toOpen M ⊤ m) =
      tilde.toOpen M (⊤ ⊓ Z.compl) m :=
    ConcreteCategory.congr_hom (tilde.toOpen_res M ⊤ (⊤ ⊓ Z.compl) (Z.complInclusion ⊤)) m
  have hU : (⊤ ⊓ Z.compl : Opens (Spec R)) =
      ⨆ f ∈ s, (basicOpen f : Opens (Spec R)) := by
    rw [top_inf_eq]
    exact Spec.compl_zeroLocusClosed_eq_iSup_basicOpen s
  rw [hres]
  constructor
  · intro hm f hf
    let Uf : Opens (Spec R) := basicOpen f
    have hle : Uf ≤ ⊤ ⊓ Z.compl :=
      hU ▸ le_iSup₂ (f := fun f (_ : f ∈ s) ↦ (basicOpen f : Opens (Spec R))) f hf
    have hresf : F.obj.map (homOfLE hle).op (tilde.toOpen M (⊤ ⊓ Z.compl) m) =
        tilde.toOpen M Uf m :=
      ConcreteCategory.congr_hom (tilde.toOpen_res M (⊤ ⊓ Z.compl) Uf (homOfLE hle)) m
    have hmf : tilde.toOpen M (basicOpen f) m = 0 := by
      rw [← hresf, hm, map_zero]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f)
      (tilde.toOpen M (basicOpen f)).hom).mp hmf
    exact ⟨n, hn⟩
  · intro hm
    refine TopCat.Presheaf.IsSheaf.section_ext F.property fun p hp ↦ ?_
    have hp' : p ∈ ⨆ f ∈ s, (basicOpen f : Opens (Spec R)) := hU ▸ hp
    obtain ⟨f, hp'⟩ := Opens.mem_iSup.mp hp'
    obtain ⟨hf, hp'⟩ := Opens.mem_iSup.mp hp'
    have hle : (basicOpen f : Opens (Spec R)) ≤ ⊤ ⊓ Z.compl :=
      hU ▸ le_iSup₂ (f := fun f (_ : f ∈ s) ↦ (basicOpen f : Opens (Spec R))) f hf
    obtain ⟨n, hn⟩ := hm f hf
    refine ⟨basicOpen f, hle, hp', ?_⟩
    rw [map_zero]
    refine (ConcreteCategory.congr_hom
      (tilde.toOpen_res M (⊤ ⊓ Z.compl) (basicOpen f) (homOfLE hle)) m).trans ?_
    exact (IsLocalizedModule.eq_zero_iff (.powers f)
      (tilde.toOpen M (basicOpen f)).hom).mpr ⟨⟨_, n, rfl⟩, hn⟩

/-- For a finitely generated ideal `I` of `R`, the global section `tilde.toOpen M ⊤ m` is
supported in `V(I)` if and only if `m ∈ I.primaryComponent M`. -/
theorem tilde_toOpen_top_mem_supportedSubmodule_iff_mem_primaryComponent
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) (m : M) :
    tilde.toOpen M ⊤ m ∈
        (modulesSpecToSheaf.obj (tilde M)).supportedSubmodule
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ ↔
      m ∈ I.primaryComponent M := by
  obtain ⟨G, hG⟩ := hI
  have hZ : Spec.zeroLocusClosed (R := R) (I : Set R) = Spec.zeroLocusClosed (G : Set R) := by
    rw [← hG, Spec.zeroLocusClosed_span]
  rw [hZ, tilde_toOpen_top_mem_supportedSubmodule_iff, ← hG, Ideal.mem_primaryComponent_span_iff]
  rfl

/-- For a finitely generated ideal `I`, the `I`-primary component `Γ_I(M)` is `R`-linearly
equivalent to the global sections of `M~` supported in `V(I)`. -/
def primaryComponentEquivSupportedSubmoduleTop {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    I.primaryComponent M ≃ₗ[R]
      (modulesSpecToSheaf.obj (tilde M)).supportedSubmodule
        (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ :=
  let e := (tilde.isoTop M).toLinearEquiv
  let S := (modulesSpecToSheaf.obj (tilde M)).supportedSubmodule
    (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤
  (LinearEquiv.ofEq (I.primaryComponent M) (S.comap e.toLinearMap)
    (Submodule.ext fun m ↦
      (tilde_toOpen_top_mem_supportedSubmodule_iff_mem_primaryComponent hI M m).symm)).trans
    (e.ofSubmodule' S)

@[simp]
lemma coe_primaryComponentEquivSupportedSubmoduleTop_apply
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) (m : I.primaryComponent M) :
    (primaryComponentEquivSupportedSubmoduleTop hI M m :
        (modulesSpecToSheaf.obj (tilde M)).obj.obj (op ⊤)) =
      tilde.toOpen M ⊤ m.val :=
  (rfl)

private def primaryComponentEquivSupportedSubmoduleTopIso
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    ModuleCat.of R (I.primaryComponent M) ≅
      (tildeSheafFunctor R ⋙
        supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).obj M :=
  (primaryComponentEquivSupportedSubmoduleTop hI M).toModuleIso

private def primaryComponentIsoSupportedSubmoduleTop
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    I.primaryComponentFunctor.obj M ≅
      (tildeSheafFunctor R ⋙
        supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).obj M :=
  I.primaryComponentFunctorObjIso M ≪≫
    primaryComponentEquivSupportedSubmoduleTopIso hI M

private lemma primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    (primaryComponentIsoSupportedSubmoduleTop hI M).hom ≫
        (((tildeSheafFunctor R).obj M).supportedSubmoduleι
          (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤) =
      I.primaryComponentFunctorι.app M ≫ tilde.toOpen M ⊤ := by
  have he : (primaryComponentEquivSupportedSubmoduleTopIso hI M).hom ≫
      (((tildeSheafFunctor R).obj M).supportedSubmoduleι
        (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤) =
    ModuleCat.ofHom (I.primaryComponent M).subtype ≫ tilde.toOpen M ⊤ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact (((tildeSheafFunctor R).obj M).supportedSubmoduleι_hom_app_apply
      (Spec.zeroLocusClosed (R := R) (I : Set R)) (op ⊤)
      (primaryComponentEquivSupportedSubmoduleTop hI M m)).trans
      (coe_primaryComponentEquivSupportedSubmoduleTop_apply hI M m)
  dsimp only [primaryComponentIsoSupportedSubmoduleTop]
  rw [Iso.trans_hom, Category.assoc, he]
  exact ((I.primaryComponentFunctorObjIso_inv_comp_ι_app_assoc M (tilde.toOpen M ⊤) ▸
    Iso.hom_inv_id_assoc (I.primaryComponentFunctorObjIso M) _))

/-- For a finitely generated ideal `I` of `R`, `M ↦ Γ_{V(I)}(Spec R, M~)` is naturally isomorphic
to the `I`-power torsion functor `I.primaryComponentFunctor`. -/
def tildeCompSupportedSubmoduleSectionsTopIso {I : Ideal R} (hI : I.FG) :
    tildeSheafFunctor R ⋙
        supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ ≅
      I.primaryComponentFunctor :=
  (NatIso.ofComponents (primaryComponentIsoSupportedSubmoduleTop hI) fun {M N} f ↦ by
    refine (cancel_mono
      ((((tildeSheafFunctor R).obj N).supportedSubmoduleι
        (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤))).1 ?_
    simp only [Category.assoc]
    rw [Functor.comp_map, supportedSubmoduleSectionsFunctor_map_ι_hom_app,
      ← Category.assoc (primaryComponentIsoSupportedSubmoduleTop hI M).hom,
      primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι hI M,
      primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι hI N]
    exact ((I.primaryComponentFunctorι.naturality_assoc f (tilde.toOpen N ⊤)).trans
      (congrArg (I.primaryComponentFunctorι.app M ≫ ·) (tilde.toOpen_map_app f ⊤).symm)).trans
        (Category.assoc _ _ _).symm).symm

/-- **Derived supported global sections agree with derived `I`-power torsion (Stacks 0955).**
Over a Noetherian ring `R`, composing `M ↦ M~` with the `q`-th right derived functor of
`Γ_{V(I)}(Spec R, -)` is naturally isomorphic to `(R^q Γ_I)`. -/
@[stacks 0955]
def tildeCompRightDerivedSupportedSectionsIso [IsNoetherianRing R] (I : Ideal R) (q : ℕ) :
    tildeSheafFunctor R ⋙
        (supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).rightDerived q ≅
      I.primaryComponentFunctor.{u}.rightDerived q :=
  Functor.compRightDerivedIsoOfResolution
    (supportedSubmoduleSectionsFunctor (R := R)
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤)
    (isFlasque (Spec R) (ModuleCat.{u} R))
    (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    (fun _ hT h₁ h₂ ↦ by
      have := isFlasque_iff.mp h₁
      have := isFlasque_iff.mp h₂
      exact isFlasque_iff.mpr hT.isFlasque_X₃_of_isFlasque)
    (fun _ hT h₁ _ ↦ by
      have := isFlasque_iff.mp h₁
      exact shortExact_map_supportedSubmoduleSectionsFunctor_of_isFlasque _ ⊤ hT)
    (tildeSheafFunctor R)
    I.primaryComponentFunctor.{u}
    (tildeCompSupportedSubmoduleSectionsTopIso (IsNoetherian.noetherian I))
    (fun M _ ↦ isFlasque_iff.mpr (isFlasque_modulesSpecToSheaf_tilde_of_injective M))
    q

/-- **Algebraic local cohomology agrees with sheaf cohomology with supports (Stacks 0A6T).**
Over a Noetherian ring `R`, the functor `M ↦ H^q_{V(I)}(Spec R, M~)` is naturally isomorphic to
`localCohomology I q`. -/
@[stacks 0A6T]
def tildeCompSupportedModuleHTopIsoLocalCohomology [IsNoetherianRing R] (I : Ideal R) (q : ℕ) :
    tildeSheafFunctor R ⋙
        supportedModuleHPresheafFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) q ⋙
        (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat.{u} R)).obj (op ⊤) ≅
      localCohomology I q :=
  (Functor.isoWhiskerLeft (tildeSheafFunctor R)
    (rightDerivedSupportedSubmoduleSectionsIso
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q)).symm ≪≫
    tildeCompRightDerivedSupportedSectionsIso I q ≪≫
    (localCohomology.isoRightDerivedPrimaryComponent I q).symm

/-- **Module-level local cohomology comparison (Stacks 0A6T).** Over a Noetherian ring `R`,
`H^q_{V(I)}(Spec R, M~)` is `R`-linearly equivalent to `H^q_I(M)`. -/
@[stacks 0A6T]
def supportedModuleHTopTildeLinearEquivLocalCohomology [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (q : ℕ) :
    (modulesSpecToSheaf.obj (tilde M)).supportedModuleH
        (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q ≃ₗ[R]
      (localCohomology I q).obj M :=
  ((tildeCompSupportedModuleHTopIsoLocalCohomology I q).app M).toLinearEquiv

/-- `supportedModuleHTopTildeLinearEquivLocalCohomology` commutes with morphisms `f : M ⟶ N` of
`R`-modules. -/
lemma supportedModuleHTopTildeLinearEquivLocalCohomology_naturality [IsNoetherianRing R]
    (I : Ideal R) {M N : ModuleCat.{u} R} (f : M ⟶ N) (q : ℕ)
    (x : (modulesSpecToSheaf.obj (tilde M)).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q) :
    (localCohomology I q).map f
        (supportedModuleHTopTildeLinearEquivLocalCohomology I M q x) =
      supportedModuleHTopTildeLinearEquivLocalCohomology I N q
        (((supportedModuleHPresheafFunctor
          (Spec.zeroLocusClosed (R := R) (I : Set R)) q).map
            ((tildeSheafFunctor R).map f)).app (op ⊤) x) :=
  (ConcreteCategory.congr_hom
    ((tildeCompSupportedModuleHTopIsoLocalCohomology I q).hom.naturality f) x).symm

/-- **Geometric depth vanishing.** For a finite module `M` over a Noetherian ring `R` and an ideal
`I`, the supported sheaf cohomology `H^q_{V(I)}(Spec R, M~)` vanishes for `q < I.depth M`. -/
@[stacks 0AVZ]
theorem subsingleton_supportedModuleH_tilde_of_lt_depth [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] {q : ℕ} (hq : (q : ℕ∞) < I.depth M) :
    Subsingleton ((modulesSpecToSheaf.obj (tilde M)).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q) := by
  have := ModuleCat.subsingleton_of_isZero (localCohomology.isZero_obj_of_lt_depth I M hq)
  exact (supportedModuleHTopTildeLinearEquivLocalCohomology I M q).subsingleton

end Comparison

end TauCeti.AlgebraicGeometry
