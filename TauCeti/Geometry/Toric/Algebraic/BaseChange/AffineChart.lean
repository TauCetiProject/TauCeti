/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import TauCeti.Algebra.MonoidAlgebra.Localization
public import TauCeti.AlgebraicGeometry.MonoidAlgebra.BaseChange
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation

/-!
# Affine toric charts over an arbitrary commutative ring

For a commutative ring `R` and a cone `σ` with dual semigroup `P_σ`, the affine toric chart of
`σ` over `R` is `Spec R[P_σ]`, where `R[P_σ]` is the additive monoid algebra with coefficients
in `R`. No hypothesis is placed on `R`: it may be the zero ring, nonreduced, or non-noetherian,
and nilpotent coefficients are kept.

A face `τ` of `σ` has the larger dual semigroup `P_τ ⊇ P_σ`, and the inclusion induces the
restriction map `R[P_σ] → R[P_τ]`. When `σ` is lattice rational, `τ = σ ⊓ ker m` for a character
`m ∈ P_σ`, and this map is the localization away from the monomial `e_m`: the affine chart of `τ`
is the basic open subscheme of the affine chart of `σ` where `e_m` is invertible. These open
immersions are the maps along which the affine charts of a fan are glued.

A homomorphism `R → S` of coefficient rings changes coefficients in the charts. This commutes
with the face maps, and the square formed by the face maps of `τ ≼ σ` over `R` and over `S` is
cartesian. Both facts follow from the affine base-change square
`TauCeti.AlgebraicGeometry.isPullback_addMonoidAlgebraSpec`, which identifies `Spec S[P]` with
`Spec R[P] ×_{Spec R} Spec S` with no flatness hypothesis.

## Main declarations

* `TauCeti.Toric.affineChartRing`, `TauCeti.Toric.affineChart`: the coordinate ring `R[P_σ]` and
  the affine toric chart `Spec R[P_σ]`.
* `TauCeti.Toric.faceAffineChartRingMap`, `TauCeti.Toric.faceAffineChartMap`: the restriction map
  and the chart morphism attached to a face inclusion, with identity and composition laws.
* `TauCeti.Toric.IsLatticeRational.exists_isLocalization_away_faceAffineChartRingMap` and
  `TauCeti.Toric.IsLatticeRational.isOpenImmersion_faceAffineChartMap`: face maps of a lattice
  rational cone are localizations at one monomial and open immersions.
* `TauCeti.Toric.IsLatticeRational.range_faceAffineChartMap_inf`: the images of two faces meet in
  the image of their intersection.
* `TauCeti.Toric.isPullback_faceAffineChartMap`: coefficient change and face maps form cartesian
  squares.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2–1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1–1.3.
* K.-W. Lan, *Arithmetic Compactifications of PEL-Type Shimura Varieties*, 6.1.1–6.1.2.
-/

public section

open AlgebraicGeometry CategoryTheory Limits AddMonoidAlgebra
open scoped AlgebraMonoidAlgebra

namespace TauCeti.Toric

/-! ### Coordinate rings -/

section Ring

variable (R : Type*) [CommSemiring R] {N V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (hi : IsIntegralLattice i) {σ τ υ : PointedCone ℝ V}

/-- The coordinate ring `R[P_σ]` of the affine toric chart of a cone `σ` over a commutative ring
`R`: the additive monoid algebra of the dual semigroup of `σ` with coefficients in `R`. -/
abbrev affineChartRing (σ : PointedCone ℝ V) : Type _ :=
  AddMonoidAlgebra R (dualSemigroup hi σ)

/-- A face inclusion `τ ≼ σ` induces the restriction map `R[P_σ] → R[P_τ]`, sending the monomial
of a character of `σ` to the monomial of the same character, viewed in the dual semigroup of
`τ`. -/
noncomputable def faceAffineChartRingMap (hτσ : τ.IsFaceOf σ) :
    affineChartRing R hi σ →ₐ[R] affineChartRing R hi τ :=
  mapDomainAlgHom R R (AddSubmonoid.inclusion (dualSemigroup_anti hi hτσ.le))

/-- Restriction along a face sends a monomial to the monomial of the same character. -/
@[simp]
theorem faceAffineChartRingMap_single (hτσ : τ.IsFaceOf σ) (m : dualSemigroup hi σ) (r : R) :
    faceAffineChartRingMap R hi hτσ (single m r) =
      single (AddSubmonoid.inclusion (dualSemigroup_anti hi hτσ.le) m) r := by
  simp [faceAffineChartRingMap]

/-- Restriction to a cone viewed as its own face is the identity. -/
@[simp]
theorem faceAffineChartRingMap_id :
    faceAffineChartRingMap R hi (PointedCone.IsFaceOf.refl σ) =
      AlgHom.id R (affineChartRing R hi σ) := by
  apply AlgHom.toLinearMap_injective
  ext m : 2
  simpa using congrArg (single · (1 : R)) (Subtype.ext rfl :
    AddSubmonoid.inclusion (dualSemigroup_anti hi le_rfl) m = m)

/-- Restriction through two successive face inclusions is restriction along their composite. -/
@[simp]
theorem faceAffineChartRingMap_comp (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ) :
    (faceAffineChartRingMap R hi hυτ).comp (faceAffineChartRingMap R hi hτσ) =
      faceAffineChartRingMap R hi (hυτ.trans hτσ) := by
  apply AlgHom.toLinearMap_injective
  ext m : 2
  simpa using congrArg (single · (1 : R)) (Subtype.ext rfl :
    AddSubmonoid.inclusion (dualSemigroup_anti hi hυτ.le)
      (AddSubmonoid.inclusion (dualSemigroup_anti hi hτσ.le) m) =
    AddSubmonoid.inclusion (dualSemigroup_anti hi (hυτ.trans hτσ).le) m)

/-- Changing coefficients along `R → S` commutes with restriction to a face. -/
theorem faceAffineChartRingMap_comp_algebraMap (S : Type*) [CommSemiring S] [Algebra R S]
    (hτσ : τ.IsFaceOf σ) :
    (faceAffineChartRingMap S hi hτσ).toRingHom.comp
        (algebraMap (affineChartRing R hi σ) (affineChartRing S hi σ)) =
      (algebraMap (affineChartRing R hi τ) (affineChartRing S hi τ)).comp
        (faceAffineChartRingMap R hi hτσ).toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp
  · intro m
    simp

/-- For a character `m` in the dual semigroup of a finitely generated cone `σ`, restriction from
`R[P_σ]` to the coordinate ring of the face `σ ⊓ ker m` is the localization away from the monomial
of `m`. -/
theorem isLocalization_away_faceAffineChartRingMap_inf_ker (hσ : σ.FG) (m : dualSemigroup hi σ) :
    letI := (faceAffineChartRingMap R hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.property))).toRingHom.toAlgebra
    IsLocalization.Away (single m (1 : R))
      (affineChartRing R hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) := by
  set F := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))
  have hF : F.IsFaceOf σ := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.property)
  have hring : (faceAffineChartRingMap R hi hF).toRingHom =
      mapDomainRingHom R (AddSubmonoid.inclusion (dualSemigroup_anti hi hF.le)) := by
    apply AddMonoidAlgebra.ringHom_ext <;> simp
  rw [hring]
  refine AddMonoidAlgebra.isLocalization_away_mapDomainRingHom R _
    (AddSubmonoid.inclusion_injective _) m ?_ fun y ↦ ?_
  · -- The image of `m` is an additive unit because `-m` lies in the dual semigroup of the face.
    refine ⟨⟨_, ⟨-(m : N →+ ℤ), neg_mem_dualSemigroup_inf_ker hi σ m⟩, ?_, ?_⟩, rfl⟩ <;>
      ext1 <;> simp
  · obtain ⟨n, hn⟩ := exists_add_nsmul_mem_dualSemigroup hi hσ m.property y.property
    exact ⟨n, ⟨_, hn⟩, Subtype.ext (by simp)⟩

/-- For a face `τ` of a lattice-rational cone `σ`, restriction from `R[P_σ]` to `R[P_τ]` is the
localization away from the monomial of a character in the dual semigroup of `σ`. -/
theorem IsLatticeRational.exists_isLocalization_away_faceAffineChartRingMap
    (hσ : IsLatticeRational i σ) (hτσ : τ.IsFaceOf σ) :
    ∃ m : dualSemigroup hi σ,
      letI := (faceAffineChartRingMap R hi hτσ).toRingHom.toAlgebra
      IsLocalization.Away (single m (1 : R)) (affineChartRing R hi τ) := by
  obtain ⟨m, hm, rfl⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτσ
  exact ⟨⟨m, hm⟩, isLocalization_away_faceAffineChartRingMap_inf_ker R hi hσ.fg ⟨m, hm⟩⟩

end Ring

/-! ### Affine charts -/

section Scheme

universe u

/- Morphisms of schemes require a common universe, so the coefficient ring and the lattice live
in the same universe; the ambient real vector space remains universe polymorphic. -/
variable (R : Type u) [CommRing R] {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (hi : IsIntegralLattice i) {σ τ υ : PointedCone ℝ V}

/-- The affine toric chart `Spec R[P_σ]` of a cone `σ` over a commutative ring `R`. -/
noncomputable abbrev affineChart (σ : PointedCone ℝ V) : Scheme.{u} :=
  Spec (.of (affineChartRing R hi σ))

/-- The chart morphism attached to a face inclusion `τ ≼ σ`, from the affine chart of `τ` to the
affine chart of `σ`. -/
noncomputable def faceAffineChartMap (hτσ : τ.IsFaceOf σ) :
    affineChart R hi τ ⟶ affineChart R hi σ :=
  Spec.map (CommRingCat.ofHom (faceAffineChartRingMap R hi hτσ).toRingHom)

/-- The face chart morphism is the spectrum of the restriction map. -/
theorem faceAffineChartMap_def (hτσ : τ.IsFaceOf σ) :
    faceAffineChartMap R hi hτσ =
      Spec.map (CommRingCat.ofHom (faceAffineChartRingMap R hi hτσ).toRingHom) :=
  (rfl)

/-- The chart morphism of a cone viewed as its own face is the identity. -/
@[simp]
theorem faceAffineChartMap_id :
    faceAffineChartMap R hi (PointedCone.IsFaceOf.refl σ) = 𝟙 (affineChart R hi σ) := by
  rw [faceAffineChartMap_def, faceAffineChartRingMap_id]
  exact Spec.map_id _

/-- The chart morphism of a composite face inclusion is the composite of the chart morphisms. -/
@[reassoc (attr := simp)]
theorem faceAffineChartMap_comp (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ) :
    faceAffineChartMap R hi hυτ ≫ faceAffineChartMap R hi hτσ =
      faceAffineChartMap R hi (hυτ.trans hτσ) := by
  rw [faceAffineChartMap_def, faceAffineChartMap_def, faceAffineChartMap_def, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← faceAffineChartRingMap_comp R hi hυτ hτσ]
  rfl

/-- Face chart morphisms are morphisms over `Spec R`. -/
@[reassoc (attr := simp)]
theorem faceAffineChartMap_comp_specAlgebraMap (hτσ : τ.IsFaceOf σ) :
    faceAffineChartMap R hi hτσ ≫ Spec.algebraMap R (affineChartRing R hi σ) =
      Spec.algebraMap R (affineChartRing R hi τ) := by
  rw [faceAffineChartMap_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ))
    (faceAffineChartRingMap R hi hτσ).comp_algebraMap

private theorem range_faceAffineChartMap_of_eq (hσ : σ.FG) (hτσ : τ.IsFaceOf σ)
    (m : dualSemigroup hi σ)
    (hm : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ) :
    Set.range (faceAffineChartMap R hi hτσ) =
      (PrimeSpectrum.basicOpen (single m (1 : R)) :
        Set (PrimeSpectrum (affineChartRing R hi σ))) := by
  subst hm
  let := (faceAffineChartRingMap R hi hτσ).toRingHom.toAlgebra
  have := isLocalization_away_faceAffineChartRingMap_inf_ker R hi hσ m
  rw [faceAffineChartMap_def]
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- For a character `m` in the dual semigroup of a finitely generated cone `σ`, the image of the
affine chart of the face `σ ⊓ ker m` in the affine chart of `σ` is the basic open set where the
monomial of `m` does not vanish. -/
theorem range_faceAffineChartMap (hσ : σ.FG) (m : dualSemigroup hi σ) :
    Set.range (faceAffineChartMap R hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.property))) =
      (PrimeSpectrum.basicOpen (single m (1 : R)) :
        Set (PrimeSpectrum (affineChartRing R hi σ))) :=
  range_faceAffineChartMap_of_eq R hi hσ _ m rfl

namespace IsLatticeRational

/-- For a face `τ` of a lattice-rational cone `σ`, the chart morphism from the affine chart of `τ`
to that of `σ` is an open immersion. -/
theorem isOpenImmersion_faceAffineChartMap (hσ : IsLatticeRational i σ) (hτσ : τ.IsFaceOf σ) :
    IsOpenImmersion (faceAffineChartMap R hi hτσ) := by
  obtain ⟨m, hm⟩ := hσ.exists_isLocalization_away_faceAffineChartRingMap R hi hτσ
  let := (faceAffineChartRingMap R hi hτσ).toRingHom.toAlgebra
  have h := IsOpenImmersion.of_isLocalization (S := affineChartRing R hi τ) (single m (1 : R))
  rwa [RingHom.algebraMap_toAlgebra] at h

/-- For two faces `τ` and `υ` of a lattice-rational cone `σ`, the image of the affine chart of
`τ ⊓ υ` in that of `σ` is the intersection of the images of the affine charts of `τ` and `υ`. -/
theorem range_faceAffineChartMap_inf (hσ : IsLatticeRational i σ) (hτσ : τ.IsFaceOf σ)
    (hυσ : υ.IsFaceOf σ) :
    Set.range (faceAffineChartMap R hi (hτσ.inf_left hυσ)) =
      Set.range (faceAffineChartMap R hi hτσ) ∩ Set.range (faceAffineChartMap R hi hυσ) := by
  obtain ⟨m₁, hm₁, h₁⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτσ
  obtain ⟨m₂, hm₂, h₂⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hυσ
  have single_add_one : single (⟨m₁, hm₁⟩ + ⟨m₂, hm₂⟩ : dualSemigroup hi σ) (1 : R) =
      single ⟨m₁, hm₁⟩ 1 * single ⟨m₂, hm₂⟩ 1 := by
    rw [single_mul_single, mul_one]
  rw [range_faceAffineChartMap_of_eq R hi hσ.fg hτσ ⟨m₁, hm₁⟩ h₁,
    range_faceAffineChartMap_of_eq R hi hσ.fg hυσ ⟨m₂, hm₂⟩ h₂,
    range_faceAffineChartMap_of_eq R hi hσ.fg _ (⟨m₁, hm₁⟩ + ⟨m₂, hm₂⟩)
      (by rw [AddSubmonoid.coe_add, map_add, PointedCone.inf_ker_add
        ((mem_dualSemigroup hi m₁).1 hm₁) ((mem_dualSemigroup hi m₂).1 hm₂), h₁, h₂]),
    single_add_one, PrimeSpectrum.basicOpen_mul]
  exact TopologicalSpace.Opens.coe_inf ..

end IsLatticeRational

/-! ### Change of coefficients -/

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Changing coefficients along `R → S` commutes with the face chart morphisms. -/
@[reassoc]
theorem faceAffineChartMap_comp_specAlgebraMap_affineChartRing (hτσ : τ.IsFaceOf σ) :
    faceAffineChartMap S hi hτσ ≫
        Spec.algebraMap (affineChartRing R hi σ) (affineChartRing S hi σ) =
      Spec.algebraMap (affineChartRing R hi τ) (affineChartRing S hi τ) ≫
        faceAffineChartMap R hi hτσ := by
  rw [faceAffineChartMap_def, faceAffineChartMap_def, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    faceAffineChartRingMap_comp_algebraMap R hi S hτσ]

/-- The face chart morphisms of `τ ≼ σ` over `R` and over `S` form a cartesian square with the
coefficient changes: the face chart over `S` is the inverse image of the face chart over `R`. -/
theorem isPullback_faceAffineChartMap (hτσ : τ.IsFaceOf σ) :
    IsPullback (faceAffineChartMap S hi hτσ)
      (Spec.algebraMap (affineChartRing R hi τ) (affineChartRing S hi τ))
      (Spec.algebraMap (affineChartRing R hi σ) (affineChartRing S hi σ))
      (faceAffineChartMap R hi hτσ) := by
  refine IsPullback.of_right ?_ (faceAffineChartMap_comp_specAlgebraMap_affineChartRing R hi S hτσ)
    (AlgebraicGeometry.isPullback_addMonoidAlgebraSpec R S (dualSemigroup hi σ)).flip
  simpa using (AlgebraicGeometry.isPullback_addMonoidAlgebraSpec R S (dualSemigroup hi τ)).flip

end Scheme

end TauCeti.Toric
