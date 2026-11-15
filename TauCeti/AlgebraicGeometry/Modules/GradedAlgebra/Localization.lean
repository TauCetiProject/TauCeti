/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import TauCeti.Algebra.Module.LocalizedModule.DirectSum
public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Localization

/-!
# Graded rings of sections over basic opens

Let `A = ⨁ₙ Aₙ` be a graded algebra on a scheme `X` whose homogeneous components are
quasicoherent, let `U` be an affine open of `X` and `f ∈ Γ(X, U)`. Restriction of sections
identifies the graded ring `⨁ n, Γ(Aₙ, X.basicOpen f)` with the localization of the graded ring
`⨁ n, Γ(Aₙ, U)` away from `f`, placed in degree zero. In each degree this is the localization of
the sections of a quasicoherent module (`Scheme.Modules.isLocalizedModule_basicOpenRestrict`), and
localization of modules commutes with direct sums.

This is the compatibility of the affine graded charts of `A` with passage to basic opens: it is
what identifies the spectrum, or the `Proj`, of the graded ring over `X.basicOpen f` with the
corresponding open subscheme of the construction over `U`, as needed to glue affine-local
constructions with graded algebras. It is the graded counterpart of
`CategoryTheory.CommMon.isLocalization_basicOpen` for commutative `𝒪_X`-algebras.

## Main statements

* `CategoryTheory.CommMon.isLocalization_gradedSections_basicOpen`: the restriction
  `⨁ n, Γ(Aₙ, U) → ⨁ n, Γ(Aₙ, X.basicOpen f)` is a localization away from `f`.
* `CategoryTheory.CommMon.isBaseChange_restrictGradedSections`: the same restriction exhibits
  `⨁ n, Γ(Aₙ, X.basicOpen f)` as the base change of `⨁ n, Γ(Aₙ, U)` along
  `Γ(X, U) → Γ(X, X.basicOpen f)`, for the algebra structure
  `CategoryTheory.CommMon.algebraGradedSectionsBasicOpen`.
* `CategoryTheory.CommMon.coequifibered_toGradedSectionsPresheaf`: on the affine opens of `X`, the
  presheaf of graded rings of sections is coequifibered over the structure presheaf.
-/

public section

open CategoryTheory Opposite DirectSum AlgebraicGeometry Scheme.AffineZariskiSite

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules))

/-- The `Γ(X, U)`-module structure on the graded sections over `X.basicOpen f`, assembled from the
module structures `Scheme.Modules.moduleBasicOpen` of the homogeneous components, is
multiplication by the restriction of the structure map `Γ(X, U) → ⨁ n, Γ(Aₙ, U)`. -/
private lemma smul_gradedSections_basicOpen {U : X.Opens} (f r : Γ(X, U))
    (z : ⨁ n, Γ(A.X n, X.basicOpen f)) :
    r • z = A.restrictGradedSections (homOfLE (X.basicOpen_le f))
      (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) r) * z := by
  rw [CommMon.restrictGradedSections_algebraMap, ← Algebra.smul_def]
  ext n
  rw [DirectSum.smul_apply, DirectSum.smul_apply]
  -- The `Γ(X, U)`-algebra structure on `Γ(X, X.basicOpen f)` is restriction of functions
  -- (`AlgebraicGeometry.Scheme.algebra_section_section_basicOpen`), so its algebra map is the
  -- restriction appearing on the right.
  exact (algebraMap_smul Γ(X, X.basicOpen f) r (z n)).symm

/-- For a graded algebra `A` with quasicoherent homogeneous components, an affine open `U` and
`f ∈ Γ(X, U)`, restriction exhibits the graded ring of sections `⨁ n, Γ(Aₙ, X.basicOpen f)` as the
localization of `⨁ n, Γ(Aₙ, U)` away from the image of `f` in degree zero. -/
theorem _root_.CategoryTheory.CommMon.isLocalization_gradedSections_basicOpen
    [∀ n, (A.X n).IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    letI := (A.restrictGradedSections (homOfLE (X.basicOpen_le f))).toAlgebra
    IsLocalization.Away (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f)
      (⨁ n, Γ(A.X n, X.basicOpen f)) := by
  let := (A.restrictGradedSections (homOfLE (X.basicOpen_le f))).toAlgebra
  -- Restriction of graded sections is the direct sum of the degreewise restrictions, each of
  -- which is a localization of modules away from `f`.
  let φ := DirectSum.lmap fun n ↦ (A.X n).basicOpenRestrict f
  have := fun n ↦ (A.X n).isLocalizedModule_basicOpenRestrict hU f
  have hφ (x : ⨁ n, Γ(A.X n, U)) :
      φ x = algebraMap (⨁ n, Γ(A.X n, U)) (⨁ n, Γ(A.X n, X.basicOpen f)) x := by
    ext n
    rw [DirectSum.lmap_apply, Scheme.Modules.basicOpenRestrict_apply,
      RingHom.algebraMap_toAlgebra, CommMon.restrictGradedSections_apply]
  refine (isLocalization_iff _ _).mpr ⟨?_, fun z ↦ ?_, fun {x y} h ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [map_pow, RingHom.algebraMap_toAlgebra, CommMon.restrictGradedSections_algebraMap]
    exact ((X.toRingedSpace.isUnit_res_basicOpen f).map _).pow k
  · obtain ⟨⟨x, _, k, rfl⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers f) φ z
    refine ⟨⟨x, ⟨_, k, rfl⟩⟩, ?_⟩
    dsimp only at hx ⊢
    rw [Submonoid.smul_def, smul_gradedSections_basicOpen, hφ, map_pow] at hx
    rw [mul_comm, ← hx, RingHom.algebraMap_toAlgebra]
  · obtain ⟨⟨_, k, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
      (f := φ) ((hφ x).trans (h.trans (hφ y).symm))
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def] at hc
    dsimp only
    rwa [← map_pow]

section BaseChange

variable {U : X.Opens} (f : Γ(X, U))

/-- The `Γ(X, U)`-algebra structure on `⨁ n, Γ(Aₙ, D(f))` whose underlying module structure is the
one by restriction of scalars along `Γ(X, U) → Γ(X, D(f))` (`Scheme.Modules.moduleBasicOpen`). -/
abbrev _root_.CategoryTheory.CommMon.algebraGradedSectionsBasicOpen :
    Algebra Γ(X, U) (⨁ n, Γ(A.X n, X.basicOpen f)) :=
  Algebra.ofModule
    (fun r x y ↦ by rw [← algebraMap_smul Γ(X, X.basicOpen f) r, ← algebraMap_smul
      Γ(X, X.basicOpen f) r, smul_mul_assoc])
    (fun r x y ↦ by rw [← algebraMap_smul Γ(X, X.basicOpen f) r, ← algebraMap_smul
      Γ(X, X.basicOpen f) r, mul_smul_comm])

/-- Restriction of sections from `U` to `D(f)` is a homomorphism of `Γ(X, U)`-algebras. -/
theorem _root_.CategoryTheory.CommMon.restrictGradedSections_algebraMap_basicOpen (r : Γ(X, U)) :
    let := A.algebraGradedSectionsBasicOpen f
    A.restrictGradedSectionsGradedHom (homOfLE (X.basicOpen_le f))
        (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) r) =
      algebraMap Γ(X, U) (⨁ n, Γ(A.X n, X.basicOpen f)) r := by
  intro
  rw [CommMon.restrictGradedSectionsGradedHom_apply, CommMon.restrictGradedSections_algebraMap,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact algebraMap_smul Γ(X, X.basicOpen f) r (1 : ⨁ n, Γ(A.X n, X.basicOpen f))

/-- Over an affine open `U` and `f ∈ Γ(X, U)`, restriction of sections exhibits
`⨁ n, Γ(Aₙ, D(f))` as the base change of `⨁ n, Γ(Aₙ, U)` along `Γ(X, U) → Γ(X, D(f))`. -/
theorem _root_.CategoryTheory.CommMon.isBaseChange_restrictGradedSections
    [∀ n, (A.X n).IsQuasicoherent] (hU : IsAffineOpen U) :
    let := A.algebraGradedSectionsBasicOpen f
    IsBaseChange Γ(X, X.basicOpen f)
      (AlgHom.mk (R := Γ(X, U))
        (A.restrictGradedSectionsGradedHom (homOfLE (X.basicOpen_le f))).toRingHom
        (A.restrictGradedSections_algebraMap_basicOpen f)).toLinearMap := by
  intro
  let := (A.restrictGradedSections (homOfLE (X.basicOpen_le f))).toAlgebra
  have := IsScalarTower.of_algebraMap_eq (R := Γ(X, U)) (S := ⨁ n, Γ(A.X n, U))
    (A := ⨁ n, Γ(A.X n, X.basicOpen f)) fun r ↦
      ((A.restrictGradedSectionsGradedHom_apply _ _).symm.trans
        (A.restrictGradedSections_algebraMap_basicOpen f r)).symm
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  have hloc := A.isLocalization_gradedSections_basicOpen hU f
  have : IsLocalization (Algebra.algebraMapSubmonoid (⨁ n, Γ(A.X n, U)) (Submonoid.powers f))
      (⨁ n, Γ(A.X n, X.basicOpen f)) := by
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  have key : IsBaseChange Γ(X, X.basicOpen f) (IsScalarTower.toAlgHom Γ(X, U)
      (⨁ n, Γ(A.X n, U)) (⨁ n, Γ(A.X n, X.basicOpen f))).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) Γ(X, X.basicOpen f) _).mp
      ((isLocalizedModule_iff_isLocalization (S := Submonoid.powers f)).mpr inferInstance)
  convert key using 1
  exact LinearMap.ext fun x ↦ A.restrictGradedSectionsGradedHom_apply _ x

end BaseChange

/-- On the affine opens of `X`, the presheaf of graded rings of sections of a graded algebra with
quasicoherent homogeneous components is coequifibered over the structure presheaf: its graded rings
of sections over basic opens are localizations. This is the condition under which Mathlib glues the
spectra of its sections (`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`). -/
theorem _root_.CategoryTheory.CommMon.coequifibered_toGradedSectionsPresheaf
    [∀ n, (A.X n).IsQuasicoherent] :
    ((toOpensFunctor X).op.whiskerLeft A.toGradedSectionsPresheaf).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U f
  rw [Functor.whiskerLeft_app, CommMon.toGradedSectionsPresheaf_app]
  exact A.isLocalization_gradedSections_basicOpen U.2 f

end

end TauCeti
