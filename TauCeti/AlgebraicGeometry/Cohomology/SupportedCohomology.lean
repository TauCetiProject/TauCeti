/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.Algebra.Homology.LocalCohomology.RightDerived
public import TauCeti.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.RingTheory.Depth.LocalCohomology
public import TauCeti.Topology.Sheaves.SupportedCohomology.Derived
import Mathlib.RingTheory.MvPolynomial.Ideal
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
3. **Depth vanishing, DVR cohomology, and non-Noetherian failure.** Over a Noetherian ring,
   `H^q_{V(I)}(Spec R, M~)` vanishes for `q < I.depth M` when `M` is finite; over a discrete
   valuation ring `(R, 𝔪)` with fraction field `K`, `H⁰_{V(𝔪)} = 0`, `H¹_{V(𝔪)} ≃ₗ[R] K ⧸ R`, and
   `H^{n+2}_{V(𝔪)} = 0`. Without finite generation, for
   `A = k[x₀, x₁, …] / (x₀², x₁³, …)` and `I = (x₀, x₁, …)`, `V(I) = Spec A` so geometric
   `H⁰_{V(I)}(Spec A, 𝒪_{Spec A})` is nontrivial, whereas `I.primaryComponent A = ⊥` and algebraic
   `H⁰_I(A) = 0`.

## Main definitions

* `TauCeti.AlgebraicGeometry.tildeSheafFunctor R`: the exact functor `M ↦ M~` from `ModuleCat R` to
  sheaves of `R`-modules on `Spec R`.
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
* `TauCeti.AlgebraicGeometry.subsingleton_supportedModuleH_dvr_zero`,
  `TauCeti.AlgebraicGeometry.supportedModuleHDvrDegreeOneLinearEquiv`, and
  `TauCeti.AlgebraicGeometry.subsingleton_supportedModuleH_dvr_add_two`: supported cohomology of the
  structure sheaf at the closed point of a discrete valuation ring.
* `TauCeti.AlgebraicGeometry.nontrivial_supportedModuleH_zero_nonNoetherianExampleRing` and
  `TauCeti.AlgebraicGeometry.isZero_localCohomology_zero_nonNoetherianExampleRing`: non-Noetherian
  failure of the degree-zero comparison when `I` is not finitely generated.

## References

* [The Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [The Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [The Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
* A. Grothendieck, *Local Cohomology*, Lecture Notes in Mathematics 41, Proposition 2.2.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, §3 and Exercise III.3.3.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open PrimeSpectrum CategoryTheory.Sheaf

section Comparison

variable (R : CommRingCat.{u})

/-- The functor `M ↦ M~` from `R`-modules to sheaves of `R`-modules on `Spec R`. -/
abbrev tildeSheafFunctor :
    ModuleCat.{u} R ⥤ Sheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R) :=
  tilde.functor R ⋙ modulesSpecToSheaf

variable {R}

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
    refine TopCat.Presheaf.IsSheaf.section_ext F.2 fun p hp ↦ ?_
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
  LinearEquiv.ofLinearMap
    ((tilde.toOpen M ⊤).hom.comp (I.primaryComponent M).subtype |>.codRestrict _
      fun m ↦ (tilde_toOpen_top_mem_supportedSubmodule_iff_mem_primaryComponent hI M m.1).mpr m.2)
    (((tilde.isoTop M).inv.hom.comp
        ((modulesSpecToSheaf.obj (tilde M)).supportedSubmodule _ ⊤).subtype).codRestrict
      _ fun s ↦ by
        refine (tilde_toOpen_top_mem_supportedSubmodule_iff_mem_primaryComponent hI M _).mp ?_
        simp only [LinearMap.comp_apply, Submodule.subtype_apply]
        have h : tilde.toOpen M ⊤ ((tilde.isoTop M).inv.hom s.1) = s.1 :=
          ConcreteCategory.congr_hom (tilde.isoTop M).inv_hom_id s.1
        rw [h]
        exact s.2)
    (LinearMap.ext fun s ↦ Subtype.ext <|
      ConcreteCategory.congr_hom (tilde.isoTop M).inv_hom_id s.1)
    (LinearMap.ext fun m ↦ Subtype.ext <|
      ConcreteCategory.congr_hom (tilde.isoTop M).hom_inv_id m.1)

@[simp]
lemma coe_primaryComponentEquivSupportedSubmoduleTop_apply
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) (m : I.primaryComponent M) :
    (primaryComponentEquivSupportedSubmoduleTop hI M m :
        (modulesSpecToSheaf.obj (tilde M)).obj.obj (op ⊤)) =
      tilde.toOpen M ⊤ m.1 :=
  (rfl)

private def tildeToOpenTop (M : ModuleCat.{u} R) :
    M ⟶ ((tildeSheafFunctor R).obj M).obj.obj (op ⊤) :=
  tilde.toOpen M ⊤

private lemma tildeToOpenTop_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    tildeToOpenTop M ≫ ((tildeSheafFunctor R).map f).hom.app (op ⊤) =
      f ≫ tildeToOpenTop N :=
  tilde.toOpen_map_app f ⊤

private def primaryComponentIsoSupportedSubmoduleTop
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    I.primaryComponentFunctor.obj M ≅
      (tildeSheafFunctor R ⋙
        supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).obj M :=
  (primaryComponentEquivSupportedSubmoduleTop hI M).toModuleIso

private lemma primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    (primaryComponentIsoSupportedSubmoduleTop hI M).hom ≫
        (((tildeSheafFunctor R).obj M).supportedSubmoduleι
          (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤) =
      I.primaryComponentFunctorι.app M ≫ tildeToOpenTop M := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact (((tildeSheafFunctor R).obj M).supportedSubmoduleι_hom_app_apply
    (Spec.zeroLocusClosed (R := R) (I : Set R)) (op ⊤)
    (primaryComponentEquivSupportedSubmoduleTop hI M m)).trans
    (coe_primaryComponentEquivSupportedSubmoduleTop_apply hI M m)

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
    rw [Functor.comp_map, primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι hI N,
      I.primaryComponentFunctorι.naturality_assoc f, Functor.id_map,
      supportedSubmoduleSectionsFunctor_map_ι_hom_app,
      ← Category.assoc (primaryComponentIsoSupportedSubmoduleTop hI M).hom,
      primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι hI M, Category.assoc]
    exact congrArg (I.primaryComponentFunctorι.app M ≫ ·) (tildeToOpenTop_naturality f).symm).symm

/-- **Derived supported global sections agree with derived `I`-power torsion (Stacks 0955).**
Over a Noetherian ring `R`, composing `M ↦ M~` with the `q`-th right derived functor of
`Γ_{V(I)}(Spec R, -)` is naturally isomorphic to `(R^q Γ_I)`. -/
@[stacks 0955]
def tildeCompRightDerivedSupportedSectionsIso [IsNoetherianRing R] (I : Ideal R) (q : ℕ) :
    tildeSheafFunctor R ⋙
        (supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).rightDerived q ≅
      I.primaryComponentFunctor.rightDerived q :=
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
    I.primaryComponentFunctor
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

section DiscreteValuationRing

variable (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Over a discrete valuation ring `(R, 𝔪)`, `H⁰_{V(𝔪)}(Spec R, 𝒪_{Spec R}) = 0`. -/
theorem subsingleton_supportedModuleH_dvr_zero :
    Subsingleton ((modulesSpecToSheaf.obj (tilde (.of R R))).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (IsLocalRing.maximalIdeal R : Set R)) ⊤ 0) := by
  have := ModuleCat.subsingleton_of_isZero (localCohomology.isZero_dvr_zero R)
  exact (supportedModuleHTopTildeLinearEquivLocalCohomology (R := R)
    (IsLocalRing.maximalIdeal R) (.of R R) 0).subsingleton

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`,
`H¹_{V(𝔪)}(Spec R, 𝒪_{Spec R}) ≃ₗ[R] K ⧸ R`. -/
def supportedModuleHDvrDegreeOneLinearEquiv :
    (modulesSpecToSheaf.obj (tilde (.of R R))).supportedModuleH
        (Spec.zeroLocusClosed (R := R) (IsLocalRing.maximalIdeal R : Set R)) ⊤ 1 ≃ₗ[R]
      K ⧸ LinearMap.range (Algebra.linearMap R K) :=
  (supportedModuleHTopTildeLinearEquivLocalCohomology (R := R)
    (IsLocalRing.maximalIdeal R) (.of R R) 1).trans (localCohomology.dvrDegreeOneLinearEquiv R K)

/-- Over a discrete valuation ring `(R, 𝔪)`, `H^{n+2}_{V(𝔪)}(Spec R, 𝒪_{Spec R}) = 0`. -/
theorem subsingleton_supportedModuleH_dvr_add_two (n : ℕ) :
    Subsingleton ((modulesSpecToSheaf.obj (tilde (.of R R))).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (IsLocalRing.maximalIdeal R : Set R)) ⊤ (n + 2)) :=
  have := ModuleCat.subsingleton_of_isZero (localCohomology.isZero_dvr_add_two R n)
  (supportedModuleHTopTildeLinearEquivLocalCohomology (R := R)
    (IsLocalRing.maximalIdeal R) (.of R R) (n + 2)).subsingleton

end DiscreteValuationRing

section NonNoetherianCounterexample

variable (k : Type u) [CommRing k] [Nontrivial k]

/-- The monomial relation ideal `(X₀², X₁³, …, X_j^{j+2}, …)` in `k[X₀, X₁, …]`. -/
def nonNoetherianRelIdeal : Ideal (MvPolynomial ℕ k) :=
  Ideal.span { MvPolynomial.X j ^ (j + 2) | j : ℕ }

/-- The non-Noetherian ring `A = k[X₀, X₁, …] ⧸ (X₀², X₁³, …)` on which geometric and algebraic
degree-zero local cohomology disagree at the variable ideal `(x₀, x₁, …)`. -/
abbrev NonNoetherianExampleRing : Type u :=
  MvPolynomial ℕ k ⧸ nonNoetherianRelIdeal k

/-- `NonNoetherianExampleRing k` bundled as an object of `CommRingCat.{u}`. -/
abbrev nonNoetherianExampleRingCat : CommRingCat.{u} :=
  CommRingCat.of (NonNoetherianExampleRing k)

/-- The ideal `I = (x₀, x₁, …)` in `nonNoetherianExampleRingCat k`. -/
def nonNoetherianVarIdeal : Ideal (nonNoetherianExampleRingCat k) :=
  Ideal.map (Ideal.Quotient.mk (nonNoetherianRelIdeal k))
    (Ideal.span (Set.range MvPolynomial.X))

omit [Nontrivial k] in
/-- A polynomial lies in `(X_j^{j+2} | j : ℕ)` if and only if all of its coefficients at
multi-indices `d` satisfying `∀ j, d j < j + 2` vanish. -/
private lemma mem_nonNoetherianRelIdeal_iff (p : MvPolynomial ℕ k) :
    p ∈ nonNoetherianRelIdeal k ↔ ∀ d : ℕ →₀ ℕ, (∀ j, d j < j + 2) → p.coeff d = 0 := by
  have hspan : nonNoetherianRelIdeal k =
      Ideal.span ((fun s ↦ MvPolynomial.monomial s (1 : k)) ''
        Set.range fun j : ℕ ↦ Finsupp.single j (j + 2)) := by
    unfold nonNoetherianRelIdeal
    congr 1
    ext x
    simp [MvPolynomial.X_pow_eq_monomial]
  rw [hspan, MvPolynomial.mem_ideal_span_monomial_image]
  simp only [MvPolynomial.mem_support_iff, Set.mem_range, exists_exists_eq_and,
    Finsupp.single_le_iff]
  constructor
  · intro hp d hd
    by_contra hne
    obtain ⟨j, hj⟩ := hp d hne
    exact (hd j).not_ge hj
  · intro hp d hne
    by_contra! hlt
    exact hne (hp d hlt)

instance instNontrivialNonNoetherianExampleRing : Nontrivial (NonNoetherianExampleRing k) := by
  refine Ideal.Quotient.nontrivial_iff.mpr fun htop ↦ ?_
  have h1 : (1 : MvPolynomial ℕ k) ∈ nonNoetherianRelIdeal k := htop ▸ Submodule.mem_top
  exact one_ne_zero (α := k) <| by
    simpa using (mem_nonNoetherianRelIdeal_iff k 1).mp h1 0 (fun j ↦ Nat.zero_lt_succ (j + 1))

omit [Nontrivial k] in
/-- Every generator of `nonNoetherianVarIdeal k` is nilpotent, so `V(I) = Spec A`. -/
theorem zeroLocusClosed_nonNoetherianVarIdeal :
    Spec.zeroLocusClosed (R := nonNoetherianExampleRingCat k)
      (nonNoetherianVarIdeal k : Set (nonNoetherianExampleRingCat k)) = ⊤ := by
  rw [← Closeds.coe_eq_univ, Set.eq_univ_iff_forall]
  intro 𝔭
  rw [SetLike.mem_coe, Spec.mem_zeroLocusClosed, SetLike.coe_subset_coe, nonNoetherianVarIdeal,
    Ideal.map_le_iff_le_comap, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap]
  refine 𝔭.isPrime.mem_of_pow_mem (j + 2) ?_
  have hj0 : Ideal.Quotient.mk (nonNoetherianRelIdeal k) (MvPolynomial.X j ^ (j + 2)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  rw [← map_pow, hj0]
  exact 𝔭.asIdeal.zero_mem

/-- On `A = nonNoetherianExampleRingCat k`, geometric `H⁰_{V(I)}(Spec A, 𝒪_{Spec A})` is nontrivial
because the unit global section `1` is killed locally on `Spec A \ V(I) = ∅`. -/
theorem nontrivial_supportedModuleH_zero_nonNoetherianExampleRing :
    Nontrivial ((modulesSpecToSheaf.obj
      (tilde (.of (nonNoetherianExampleRingCat k)
        (nonNoetherianExampleRingCat k)))).supportedModuleH
      (Spec.zeroLocusClosed (R := nonNoetherianExampleRingCat k)
        (nonNoetherianVarIdeal k : Set (nonNoetherianExampleRingCat k))) ⊤ 0) := by
  let A := nonNoetherianExampleRingCat k
  let F := modulesSpecToSheaf.obj (tilde (.of A A))
  let Z : Closeds (Spec A) := Spec.zeroLocusClosed (nonNoetherianVarIdeal k : Set A)
  have h1 : tilde.toOpen (.of A A) ⊤ (1 : A) ∈ F.supportedSubmodule Z ⊤ := by
    have hZ : Z = Spec.zeroLocusClosed (R := A)
        ((Ideal.Quotient.mk (nonNoetherianRelIdeal k)) '' Set.range MvPolynomial.X) := by
      dsimp only [Z]
      rw [nonNoetherianVarIdeal, Ideal.map_span, Spec.zeroLocusClosed_span]
    rw [hZ, tilde_toOpen_top_mem_supportedSubmodule_iff]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨j + 2, ?_⟩
    rw [smul_eq_mul, mul_one, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  have hne : (⟨tilde.toOpen (.of A A) ⊤ (1 : A), h1⟩ : F.supportedSubmodule Z ⊤) ≠
      0 := fun h0 ↦ one_ne_zero (α := A) <| by
    have hval : tilde.toOpen (.of A A) ⊤ (1 : A) = 0 := congr(Subtype.val $h0)
    have hinv := ConcreteCategory.congr_hom (tilde.isoTop (.of A A)).hom_inv_id (1 : A)
    simpa [hval] using hinv.symm
  have : Nontrivial (F.supportedSubmodule Z ⊤) := ⟨⟨_, h1⟩, 0, hne⟩
  exact (F.supportedModuleHZeroEquiv Z ⊤).toEquiv.nontrivial

omit [Nontrivial k] in
/-- In `A = nonNoetherianExampleRingCat k`, no nonzero element is annihilated by a uniform power
`I ^ n` of `I = (x₀, x₁, …)`, so `I.primaryComponent A = ⊥`. -/
theorem primaryComponent_nonNoetherianVarIdeal_eq_bot :
    (nonNoetherianVarIdeal k).primaryComponent (nonNoetherianExampleRingCat k) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  by_contra hp0
  have hpJ : p ∉ nonNoetherianRelIdeal k := fun h ↦ hp0 (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hnot := mt (mem_nonNoetherianRelIdeal_iff k p).mpr hpJ
  push Not at hnot
  obtain ⟨d₀, hd₀, hp₀⟩ := hnot
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (nonNoetherianExampleRingCat k)
    (nonNoetherianVarIdeal k) _).mp ha
  let N : ℕ := max n (d₀.support.sup id + 1)
  have hxN : Ideal.Quotient.mk (nonNoetherianRelIdeal k) (MvPolynomial.X N) ^ n ∈
      nonNoetherianVarIdeal k ^ n :=
    Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self N))) n
  have hprod : MvPolynomial.X N ^ n * p ∈ nonNoetherianRelIdeal k := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [map_mul, map_pow] using (Submodule.mem_torsionBySet_iff _ _).mp hn ⟨_, hxN⟩
  have hd' : ∀ j, (Finsupp.single N n + d₀) j < j + 2 := fun j ↦ by
    by_cases hj : j = N
    · subst hj
      have hdN : d₀ N = 0 := Finsupp.notMem_support_iff.mp fun hmem ↦
        not_le_of_gt (Nat.lt_succ_self (d₀.support.sup id))
          ((le_max_right n _).trans (Finset.le_sup (f := id) hmem) |>.trans_eq rfl)
      simpa [hdN] using lt_of_le_of_lt (le_max_left n _) (Nat.lt_add_of_pos_right two_pos)
    · simpa [hj] using hd₀ j
  have hzero := (mem_nonNoetherianRelIdeal_iff k _).mp hprod (Finsupp.single N n + d₀) hd'
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul, one_mul] at hzero
  exact hp₀ hzero

omit [Nontrivial k] in
/-- Algebraic degree-zero local cohomology `H⁰_I(A)` vanishes on `nonNoetherianExampleRingCat k`,
disagreeing with geometric `H⁰_{V(I)}(Spec A, 𝒪_{Spec A})`. -/
theorem isZero_localCohomology_zero_nonNoetherianExampleRing :
    IsZero ((localCohomology (nonNoetherianVarIdeal k) 0).obj
      (.of (nonNoetherianExampleRingCat k) (nonNoetherianExampleRingCat k))) :=
  IsZero.of_iso
    (Ideal.isZero_primaryComponentFunctor_obj_of_eq_bot _
      (primaryComponent_nonNoetherianVarIdeal_eq_bot k))
    ((localCohomology.degreeZeroIsoPrimaryComponentFunctor (nonNoetherianVarIdeal k)).app _)

/-- `nonNoetherianVarIdeal k` is not finitely generated; otherwise degree-zero geometric and
algebraic local cohomology would agree. -/
theorem not_fg_nonNoetherianVarIdeal : ¬ (nonNoetherianVarIdeal k).FG := fun hfg ↦ by
  let A := nonNoetherianExampleRingCat k
  have : Subsingleton ((nonNoetherianVarIdeal k).primaryComponent A) :=
    (Submodule.eq_bot_iff _).mp (primaryComponent_nonNoetherianVarIdeal_eq_bot k) |> fun h ↦
      ⟨fun x y ↦ Subtype.ext ((h x.1 x.2).trans (h y.1 y.2).symm)⟩
  have : Subsingleton ((modulesSpecToSheaf.obj (tilde (.of A A))).supportedModuleH
      (Spec.zeroLocusClosed (R := A) (nonNoetherianVarIdeal k : Set A)) ⊤ 0) :=
    ((primaryComponentEquivSupportedSubmoduleTop hfg (.of A A)).trans
      ((modulesSpecToSheaf.obj (tilde (.of A A))).supportedModuleHZeroEquiv
        _ ⊤).symm).toEquiv.symm.subsingleton
  have := nontrivial_supportedModuleH_zero_nonNoetherianExampleRing k
  exact false_of_nontrivial_of_subsingleton
    ((modulesSpecToSheaf.obj (tilde (.of A A))).supportedModuleH
      (Spec.zeroLocusClosed (R := A) (nonNoetherianVarIdeal k : Set A)) ⊤ 0)

/-- `NonNoetherianExampleRing k` is not Noetherian. -/
theorem not_isNoetherianRing_nonNoetherianExampleRing :
    ¬ IsNoetherianRing (NonNoetherianExampleRing k) :=
  fun _ ↦ not_fg_nonNoetherianVarIdeal k (IsNoetherian.noetherian _)

end NonNoetherianCounterexample

end TauCeti.AlgebraicGeometry
