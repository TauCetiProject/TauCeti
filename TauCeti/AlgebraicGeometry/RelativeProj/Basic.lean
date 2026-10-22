/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Localization
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.RingTheory.GradedAlgebra.DirectSum

/-!
# The relative `Proj` of a graded quasi-coherent algebra

Let `A = ⨁ₙ Aₙ` be a graded algebra on a scheme `X` whose homogeneous components are
quasi-coherent. Over an affine open `U` of `X`, the sections of the homogeneous components form the
graded `Γ(X, U)`-algebra `⨁ n, Γ(Aₙ, U)` (`CategoryTheory.CommMon.gCommRingSections`), internally
graded by its summands (`CategoryTheory.CommMon.gradedSectionsGrading`), and its projective
spectrum is a scheme over `Spec Γ(X, U) ≅ U`. This file glues these schemes into the *relative
`Proj`*

`Proj_X(A) ⟶ X`,

a scheme over `X` whose part over every affine open `U` is `Proj (⨁ n, Γ(Aₙ, U))`. Relative `Proj`
is the construction behind blowups of quasi-coherent ideals and projective morphisms.

The gluing uses Mathlib's relative gluing along the affine opens of `X`
(`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`), whose transition maps are inclusions of
basic opens `D(f) ⊆ U`. Its input is that these charts are compatible with restriction: for an
affine open `U` and `f ∈ Γ(X, U)`, restriction of sections exhibits `⨁ n, Γ(Aₙ, D(f))` as the
base change of `⨁ n, Γ(Aₙ, U)` along `Γ(X, U) → Γ(X, D(f))`, because both are localizations away
from `f` (`CategoryTheory.CommMon.isLocalization_gradedSections_basicOpen`). As `Proj` commutes
with base change (`AlgebraicGeometry.Proj.isPullback_map_of_isBaseChange`), the chart over `D(f)` is
the pullback of the chart over `U`.

## Main definitions

* `CategoryTheory.CommMon.gradedSectionsGrading A U`: the grading of `⨁ n, Γ(Aₙ, U)` by its
  summands.
* `CategoryTheory.CommMon.restrictGradedSectionsGradedHom A i`: restriction of sections along
  `V ≤ U`, as a graded ring homomorphism.
* `CategoryTheory.CommMon.relativeProj A`: the relative `Proj` of `A`, with structure morphism
  `CategoryTheory.CommMon.relativeProjToBase A` and open cover
  `CategoryTheory.CommMon.relativeProjCover A` by the schemes `Proj (⨁ n, Γ(Aₙ, U))`.

## Main results

* `CategoryTheory.CommMon.isPullback_proj_restrictGradedSections`: over an inclusion of a basic open
  `D(f)` into an affine open `U`, the chart over `D(f)` is the base change of the chart over `U`.
* `CategoryTheory.CommMon.isPullback_relativeProjCover`: over an affine open `U` of `X`, the
  relative `Proj` is `Proj (⨁ n, Γ(Aₙ, U))`.

## References

* [The Stacks Project, Section 27.15, Relative Proj](https://stacks.math.columbia.edu/tag/01NS)
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §3.1.
* R. Hartshorne, *Algebraic Geometry*, Section II.7, before Proposition II.7.10.
-/

public section

open CategoryTheory Limits Opposite DirectSum

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules))

/-- The grading of the ring `⨁ n, Γ(Aₙ, U)` of sections of a graded algebra by its summands
`Γ(Aₙ, U)`. -/
abbrev _root_.CategoryTheory.CommMon.gradedSectionsGrading (U : X.Opens) :
    ℕ → Submodule Γ(X, U) (⨁ n, Γ(A.X n, U)) :=
  TauCeti.DirectSum.summand Γ(X, U) fun n ↦ Γ(A.X n, U)

variable {A} in
/-- A homogeneous section of degree `n` lies in the degree-`n` summand. -/
theorem _root_.CategoryTheory.CommMon.of_mem_gradedSectionsGrading {U : X.Opens} (n : ℕ)
    (x : Γ(A.X n, U)) : DirectSum.of _ n x ∈ A.gradedSectionsGrading U n :=
  TauCeti.DirectSum.of_mem_summand (R := Γ(X, U)) (M := fun n ↦ Γ(A.X n, U)) n x

/-- Restriction of sections along an inclusion of opens `V ≤ U`, as a graded ring homomorphism
between the graded rings of sections. -/
def _root_.CategoryTheory.CommMon.restrictGradedSectionsGradedHom {U V : X.Opens} (i : V ⟶ U) :
    A.gradedSectionsGrading U →+*ᵍ A.gradedSectionsGrading V where
  __ := A.restrictGradedSections i
  map_mem {n x} hx := by
    obtain ⟨x, rfl⟩ := TauCeti.DirectSum.mem_summand.mp hx
    simpa using CommMon.of_mem_gradedSectionsGrading n _

/-- The graded restriction of sections is the restriction of sections. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.restrictGradedSectionsGradedHom_apply {U V : X.Opens}
    (i : V ⟶ U) (x : ⨁ n, Γ(A.X n, U)) :
    A.restrictGradedSectionsGradedHom i x = A.restrictGradedSections i x :=
  (rfl)

/-- Graded restriction of sections along the identity is the identity. -/
theorem _root_.CategoryTheory.CommMon.restrictGradedSectionsGradedHom_id (U : X.Opens) :
    A.restrictGradedSectionsGradedHom (𝟙 U) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x ↦ by simp

/-- Graded restriction of sections along a composite of inclusions is the composite of the graded
restrictions. -/
theorem _root_.CategoryTheory.CommMon.restrictGradedSectionsGradedHom_comp {U V W : X.Opens}
    (i : V ⟶ U) (j : W ⟶ V) :
    A.restrictGradedSectionsGradedHom (j ≫ i) =
      (A.restrictGradedSectionsGradedHom j).comp (A.restrictGradedSectionsGradedHom i) :=
  GradedRingHom.ext fun x ↦ by simp [CommMon.restrictGradedSections_comp]

section BasicOpen

variable {U : X.Opens} (f : Γ(X, U))

/-- The `Γ(X, U)`-algebra structure on `⨁ n, Γ(Aₙ, D(f))` whose underlying module structure is the
one by restriction of scalars along `Γ(X, U) → Γ(X, D(f))` (`Scheme.Modules.moduleBasicOpen`). -/
private abbrev algebraBasicOpen : Algebra Γ(X, U) (⨁ n, Γ(A.X n, X.basicOpen f)) :=
  Algebra.ofModule
    (fun r x y ↦ by rw [← algebraMap_smul Γ(X, X.basicOpen f) r, ← algebraMap_smul
      Γ(X, X.basicOpen f) r, smul_mul_assoc])
    (fun r x y ↦ by rw [← algebraMap_smul Γ(X, X.basicOpen f) r, ← algebraMap_smul
      Γ(X, X.basicOpen f) r, mul_smul_comm])

/-- Restriction of sections from `U` to `D(f)` is a homomorphism of `Γ(X, U)`-algebras. -/
private theorem restrictGradedSections_algebraMap_basicOpen (r : Γ(X, U)) :
    let := algebraBasicOpen A f
    A.restrictGradedSectionsGradedHom (homOfLE (X.basicOpen_le f))
        (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) r) =
      algebraMap Γ(X, U) (⨁ n, Γ(A.X n, X.basicOpen f)) r := by
  intro
  rw [CommMon.restrictGradedSectionsGradedHom_apply, CommMon.restrictGradedSections_algebraMap,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact algebraMap_smul Γ(X, X.basicOpen f) r (1 : ⨁ n, Γ(A.X n, X.basicOpen f))

variable [∀ n, (A.X n).IsQuasicoherent] (hU : IsAffineOpen U)
include hU

/-- Over an affine open `U` and `f ∈ Γ(X, U)`, restriction of sections exhibits
`⨁ n, Γ(Aₙ, D(f))` as the base change of `⨁ n, Γ(Aₙ, U)` along `Γ(X, U) → Γ(X, D(f))`. -/
private theorem isBaseChange_restrictGradedSections :
    let := algebraBasicOpen A f
    IsBaseChange Γ(X, X.basicOpen f)
      (AlgHom.mk (R := Γ(X, U))
        (A.restrictGradedSectionsGradedHom (homOfLE (X.basicOpen_le f))).toRingHom
        (restrictGradedSections_algebraMap_basicOpen A f)).toLinearMap := by
  intro
  let := (A.restrictGradedSections (homOfLE (X.basicOpen_le f))).toAlgebra
  have := IsScalarTower.of_algebraMap_eq (R := Γ(X, U)) (S := ⨁ n, Γ(A.X n, U))
    (A := ⨁ n, Γ(A.X n, X.basicOpen f)) fun r ↦
      (restrictGradedSections_algebraMap_basicOpen A f r).symm
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  have hloc := A.isLocalization_gradedSections_basicOpen hU f
  have : IsLocalization (Algebra.algebraMapSubmonoid (⨁ n, Γ(A.X n, U)) (Submonoid.powers f))
      (⨁ n, Γ(A.X n, X.basicOpen f)) := by
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  exact (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) Γ(X, X.basicOpen f) _).mp
    ((isLocalizedModule_iff_isLocalization (S := Submonoid.powers f)).mpr inferInstance)

/-- Restriction of sections from an affine open `U` to a basic open `D(f)` induces a morphism of
projective spectra `Proj (⨁ n, Γ(Aₙ, D(f))) ⟶ Proj (⨁ n, Γ(Aₙ, U))`. -/
theorem _root_.CategoryTheory.CommMon.irrelevant_le_map_restrictGradedSectionsGradedHom
    (i : X.basicOpen f ⟶ U) :
    HomogeneousIdeal.irrelevant (A.gradedSectionsGrading (X.basicOpen f)) ≤
      (HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U)).map
        (A.restrictGradedSectionsGradedHom i) := by
  obtain rfl : i = homOfLE (X.basicOpen_le f) := Subsingleton.elim _ _
  let := algebraBasicOpen A f
  exact HomogeneousIdeal.irrelevant_le_map_of_isBaseChange _ _ _
    (isBaseChange_restrictGradedSections A f hU)

/-- **The charts of the relative `Proj` are compatible with restriction.** For an affine open `U`
of `X` and `f ∈ Γ(X, U)`, the square

`Proj (⨁ n, Γ(Aₙ, D(f))) ⟶ Proj (⨁ n, Γ(Aₙ, U))`, `Spec Γ(X, D(f)) ⟶ Spec Γ(X, U)`

formed by restriction of sections and the coefficient projections is cartesian. -/
theorem _root_.CategoryTheory.CommMon.isPullback_proj_restrictGradedSections
    (i : X.basicOpen f ⟶ U) :
    IsPullback (Proj.map (A.restrictGradedSectionsGradedHom i)
        (A.irrelevant_le_map_restrictGradedSectionsGradedHom f hU i))
      (Proj.toSpecCoeff (A.gradedSectionsGrading (X.basicOpen f)))
      (Proj.toSpecCoeff (A.gradedSectionsGrading U)) (Spec.map (X.presheaf.map i.op)) := by
  obtain rfl : i = homOfLE (X.basicOpen_le f) := Subsingleton.elim _ _
  let := algebraBasicOpen A f
  -- the algebra structure of `Γ(X, D(f))` over `Γ(X, U)` is restriction of functions
  exact Proj.isPullback_map_of_isBaseChange _ _ _ (isBaseChange_restrictGradedSections A f hU)

end BasicOpen

section Gluing

open Scheme.AffineZariskiSite

variable [∀ n, (A.X n).IsQuasicoherent]

/-- An arrow `U ⟶ V` of the small affine Zariski site of `X` is the inclusion of a basic open of
the affine open `V`, so restriction of sections along it induces a morphism of projective
spectra. -/
theorem
    _root_.CategoryTheory.CommMon.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U.toOpens) ≤
      (HomogeneousIdeal.irrelevant (A.gradedSectionsGrading V.toOpens)).map
        (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map i)) := by
  obtain ⟨U, hU⟩ := U
  obtain ⟨f, rfl⟩ := leOfHom i
  exact A.irrelevant_le_map_restrictGradedSectionsGradedHom f V.2 _

/-- The schemes `Proj (⨁ n, Γ(Aₙ, U))` over the affine opens `U` of `X`, with the morphisms
induced by restriction of sections to basic opens. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeProjFunctor : X.AffineZariskiSite ⥤ Scheme.{u} where
  obj U := Proj (A.gradedSectionsGrading U.toOpens)
  map i := Proj.map _ (A.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i)
  map_id U := (Proj.map_congr (by
    rw [Subsingleton.elim ((toOpensFunctor X).map (𝟙 U)) (𝟙 _),
      CommMon.restrictGradedSectionsGradedHom_id]
    -- `(toOpensFunctor X).obj U` is `U.toOpens` by definition
    rfl) _ _).trans Proj.map_id
  map_comp i j := (Proj.map_congr
    (g := (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map i)).comp
      (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map j)))
    (by rw [Functor.map_comp, CommMon.restrictGradedSectionsGradedHom_comp]) _ _).trans
      (Proj.map_comp _ _ _ _)

/-- The coefficient projections `Proj (⨁ n, Γ(Aₙ, U)) ⟶ Spec Γ(X, U)`, natural in the affine
open `U`. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeProjToSpec :
    A.relativeProjFunctor ⟶ toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec where
  app U := Proj.toSpecCoeff (A.gradedSectionsGrading U.toOpens)
  naturality U V i := by
    obtain ⟨U, hU⟩ := U
    obtain ⟨f, rfl⟩ := leOfHom i
    exact (A.isPullback_proj_restrictGradedSections f V.2 _).w

/-- The coefficient projections of the charts of the relative `Proj` form an equifibered natural
transformation: every naturality square is cartesian. -/
theorem _root_.CategoryTheory.CommMon.equifibered_relativeProjToSpec :
    A.relativeProjToSpec.Equifibered := by
  intro U V i
  obtain ⟨U, hU⟩ := U
  obtain ⟨f, rfl⟩ := leOfHom i
  exact A.isPullback_proj_restrictGradedSections f V.2 _

/-- The relative gluing datum of the relative `Proj` of `A`: the schemes `Proj (⨁ n, Γ(Aₙ, U))`
over the affine opens `U` of `X`. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeProjGluingData :
    (directedCover X).RelativeGluingData where
  functor := A.relativeProjFunctor
  natTrans := A.relativeProjToSpec ≫ (restrictIsoSpec X).inv
  equifibered :=
    A.equifibered_relativeProjToSpec.comp (NatTrans.Equifibered.of_isIso (restrictIsoSpec X).inv)

/-- The gluing diagram of the relative `Proj` is locally directed. -/
instance _root_.CategoryTheory.CommMon.isLocallyDirected_relativeProjGluingData :
    (A.relativeProjGluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The **relative `Proj`** `Proj_X(A)` of a graded algebra `A` on `X` with quasi-coherent
homogeneous components, glued from the schemes `Proj (⨁ n, Γ(Aₙ, U))` over the affine opens `U`
of `X`. -/
@[expose, stacks 01NS]
def _root_.CategoryTheory.CommMon.relativeProj : Scheme.{u} :=
  A.relativeProjGluingData.glued

/-- The structure morphism `Proj_X(A) ⟶ X` of the relative `Proj`. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeProjToBase : A.relativeProj ⟶ X :=
  A.relativeProjGluingData.toBase

/-- The open cover of the relative `Proj` by the schemes `Proj (⨁ n, Γ(Aₙ, U))` over the affine
opens `U` of `X`. -/
@[expose]
def _root_.CategoryTheory.CommMon.relativeProjCover : A.relativeProj.OpenCover :=
  A.relativeProjGluingData.cover

/-- The charts of the relative `Proj` are open immersions. -/
instance _root_.CategoryTheory.CommMon.isOpenImmersion_relativeProjCover_f
    (U : X.AffineZariskiSite) : IsOpenImmersion (A.relativeProjCover.f U) :=
  A.relativeProjCover.map_prop U

/-- The chart of the relative `Proj` over an affine open `U` is `Proj (⨁ n, Γ(Aₙ, U))`. -/
theorem _root_.CategoryTheory.CommMon.relativeProjCover_X (U : X.AffineZariskiSite) :
    A.relativeProjCover.X U = Proj (A.gradedSectionsGrading U.toOpens) :=
  (rfl)

/-- Over an affine open `U`, the structure morphism of the relative `Proj` is the coefficient
projection `Proj (⨁ n, Γ(Aₙ, U)) ⟶ Spec Γ(X, U)` followed by the chart `Spec Γ(X, U) ⟶ X`. -/
@[reassoc]
theorem _root_.CategoryTheory.CommMon.relativeProjCover_f_relativeProjToBase
    (U : X.AffineZariskiSite) :
    A.relativeProjCover.f U ≫ A.relativeProjToBase =
      Proj.toSpecCoeff (A.gradedSectionsGrading U.toOpens) ≫ U.2.fromSpec := by
  -- the gluing datum's map to `U` is the coefficient projection followed by `U.2.isoSpec.inv`,
  -- and `U.2.isoSpec.inv ≫ U.ι = U.2.fromSpec` (`IsAffineOpen.isoSpec_inv_ι`) by definition
  exact (A.relativeProjGluingData.ι_toBase U).trans (Category.assoc _ _ _)

/-- The preimage of an affine open `U` under the structure morphism of the relative `Proj` is the
image of the chart `Proj (⨁ n, Γ(Aₙ, U))`. -/
theorem _root_.CategoryTheory.CommMon.relativeProjToBase_preimage (U : X.AffineZariskiSite) :
    A.relativeProjToBase ⁻¹ᵁ U.toOpens = (A.relativeProjCover.f U).opensRange := by
  have h := A.relativeProjGluingData.toBase_preimage_eq_opensRange_ι U
  simp only [Scheme.Opens.opensRange_ι] at h
  exact h

/-- **Over an affine open `U` of `X`, the relative `Proj` is `Proj (⨁ n, Γ(Aₙ, U))`**: the chart
of the relative `Proj` over `U` is the base change of its structure morphism along `U ⟶ X`. -/
theorem _root_.CategoryTheory.CommMon.isPullback_relativeProjCover (U : X.AffineZariskiSite) :
    IsPullback (Proj.toSpecCoeff (A.gradedSectionsGrading U.toOpens) ≫ U.2.isoSpec.inv)
      (A.relativeProjCover.f U) U.toOpens.ι A.relativeProjToBase :=
  A.relativeProjGluingData.isPullback_natTrans_ι_toBase U

end Gluing

end

end TauCeti
