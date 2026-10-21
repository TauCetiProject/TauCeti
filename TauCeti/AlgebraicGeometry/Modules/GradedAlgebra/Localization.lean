/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.RingTheory.RingHom.FiniteType
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

Since this localization is the base change of the graded-section algebra along the localization
of the base ring, finite generation over the ring of regular functions is preserved on basic
opens (`CategoryTheory.CommMon.finiteType_gradedSections_basicOpen`).

## Main statements

* `CategoryTheory.CommMon.isLocalization_gradedSections_basicOpen`: the restriction
  `⨁ n, Γ(Aₙ, U) → ⨁ n, Γ(Aₙ, X.basicOpen f)` is a localization away from `f`.
* `CategoryTheory.CommMon.finiteType_gradedSections_basicOpen`: if the graded-section algebra over
  `U` is finitely generated, then so is the graded-section algebra over `X.basicOpen f`.
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

/-- Finite generation of a graded ring of sections over the ring of regular functions is
preserved on basic opens. The target algebra is the base change of the source algebra along
`Γ(X, U) → Γ(X, X.basicOpen f)`, because both rings are localized away from `f`. -/
theorem _root_.CategoryTheory.CommMon.finiteType_gradedSections_basicOpen
    [∀ n, (A.X n).IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    [Algebra.FiniteType Γ(X, U) (⨁ n, Γ(A.X n, U))] :
    Algebra.FiniteType Γ(X, X.basicOpen f) (⨁ n, Γ(A.X n, X.basicOpen f)) := by
  let i : X.basicOpen f ⟶ U := homOfLE (X.basicOpen_le f)
  let := (X.presheaf.map i.op).hom.toAlgebra
  let := (A.restrictGradedSections i).toAlgebra
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  have : IsLocalization.Away
      (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f)
      (⨁ n, Γ(A.X n, X.basicOpen f)) :=
    A.isLocalization_gradedSections_basicOpen hU f
  rw [← RingHom.finiteType_algebraMap]
  let g := IsLocalization.Away.map Γ(X, X.basicOpen f)
    (⨁ n, Γ(A.X n, X.basicOpen f))
      (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U))) f
  have hg : g.FiniteType := RingHom.localization_away_map_finiteType
    Γ(X, U) (⨁ n, Γ(A.X n, U)) Γ(X, X.basicOpen f)
      (⨁ n, Γ(A.X n, X.basicOpen f))
      (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U))) f
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have heq : algebraMap Γ(X, X.basicOpen f)
      (⨁ n, Γ(A.X n, X.basicOpen f)) = g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    dsimp only [g]
    rw [IsLocalization.Away.map, IsLocalization.map_comp]
    apply RingHom.ext
    intro r
    exact (A.restrictGradedSections_algebraMap i r).symm
  rwa [heq]

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
