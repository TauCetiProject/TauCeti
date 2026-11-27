/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.Scheme.SpecAlgHom

import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import TauCeti.AlgebraicGeometry.Normalization.IsIso

/-!
# Relative normalization of a morphism of affine schemes

## Main results

* `TauCeti.AlgebraicGeometry.isIso_normalizationDesc_spec_iff` characterizes the affine
  normalization comparison by injectivity and containment of the integral elements.
* `TauCeti.AlgebraicGeometry.normalizationSpecIso` identifies the relative normalization of a
  morphism of spectra with the spectrum of its integral closure, compatibly with both maps
  in the normalization factorization.

The comparison uses Mathlib's `Scheme.Hom.normalizationDesc`, `Scheme.ΓSpecIso`,
and `arrowIsoSpecΓOfIsAffine`, together with Tau Ceti's
`Scheme.Hom.isIso_normalizationDesc_app_iff`.

## References

* [Stacks Project, Definition 29.54.3](https://stacks.math.columbia.edu/tag/035H) and
  [Lemma 29.54.4](https://stacks.math.columbia.edu/tag/035I).
-/

public section

open _root_.AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra C B]

/-- The integral-closure criterion for `C → B` is equivalent to the criterion on global
sections of the corresponding spectra, which are identified by `Scheme.ΓSpecIso`. -/
theorem injective_and_isIntegralElem_mem_range_appTop_iff :
    (Function.Injective (Spec.algebraMap C B).appTop ∧
      ∀ s, (Spec.algebraMap A B).appTop.hom.IsIntegralElem s →
        s ∈ (Spec.algebraMap C B).appTop.hom.range) ↔
      Function.Injective (algebraMap C B) ∧
        ∀ b, _root_.IsIntegral A b → b ∈ (algebraMap C B).range := by
  let g := (Spec.algebraMap C B).appTop
  let eB := Scheme.ΓSpecIso (CommRingCat.of B)
  let eC := Scheme.ΓSpecIso (CommRingCat.of C)
  have hB : Function.Bijective eB.hom := ConcreteCategory.bijective_of_isIso _
  have hC : Function.Bijective eC.hom := ConcreteCategory.bijective_of_isIso _
  have hcomp : eB.hom ∘ g = algebraMap C B ∘ eC.hom :=
    funext (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap C B))))
  have hinj : Function.Injective g ↔ Function.Injective (algebraMap C B) := by
    rw [← hB.injective.of_comp_iff g, hcomp, Function.Injective.of_comp_iff' _ hC]
  have hint (s) : (Spec.algebraMap A B).appTop.hom.IsIntegralElem s ↔
      _root_.IsIntegral A (eB.hom s) := by
    let φ := CommRingCat.ofHom (algebraMap A B)
    refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
    · have hmap : ((Spec.map φ).appTop ≫ eB.hom).hom.IsIntegralElem (eB.hom s) :=
        hs.map eB.hom.hom
      rw [Scheme.ΓSpecIso_naturality φ] at hmap
      exact hmap.of_comp
    · have hmap : (φ ≫ eB.inv).hom.IsIntegralElem (eB.inv (eB.hom s)) :=
        RingHom.IsIntegralElem.map hs eB.inv.hom
      rw [Scheme.ΓSpecIso_inv_naturality φ, Iso.hom_inv_id_apply] at hmap
      exact hmap.of_comp
  have hrange : eB.hom ⁻¹' Set.range (algebraMap C B) = Set.range g := by
    rw [← hC.surjective.range_comp (algebraMap C B), ← hcomp, Set.range_comp,
      hB.injective.preimage_image]
  have hmem (s) : eB.hom s ∈ (algebraMap C B).range ↔ s ∈ g.hom.range :=
    Set.ext_iff.mp hrange s
  refine and_congr hinj ?_
  exact (forall_congr' fun s ↦ imp_congr (hint s) (hmem s).symm).trans
    (hB.surjective.forall (p := fun b ↦ _root_.IsIntegral A b → b ∈ (algebraMap C B).range)).symm

variable [Algebra A C] [IsScalarTower A C B]

/-- In a tower of rings with `Spec C → Spec A` integral, the comparison from the relative
normalization of `Spec A` in `Spec B` to `Spec C` is an isomorphism exactly when `C → B` is
injective and its image contains the elements integral over `A` (Stacks, Tag 035I). -/
theorem isIso_normalizationDesc_spec_iff [IsIntegralHom (Spec.algebraMap A C)] :
    IsIso ((Spec.algebraMap A B).normalizationDesc (Spec.algebraMap C B) (Spec.algebraMap A C)
      (Spec.algebraMap_comp_algebraMap A C B).symm) ↔
      Function.Injective (algebraMap C B) ∧
        ∀ b, _root_.IsIntegral A b → b ∈ (algebraMap C B).range := by
  let f := Spec.algebraMap A B
  let g := Spec.algebraMap C B
  let h := Spec.algebraMap A C
  have H : f = g ≫ h := (Spec.algebraMap_comp_algebraMap A C B).symm
  have htop : g.appLE (h ⁻¹ᵁ ⊤) (f ⁻¹ᵁ ⊤)
      (by simp only [Scheme.Hom.preimage_top, le_refl]) = g.appTop :=
    g.appLE_eq_app (U := ⊤)
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have hiso : IsIso (f.normalizationDesc g h H) ↔
      IsIso (f.normalizationDesc g h H).appTop := by
    rw [← MorphismProperty.isomorphisms.iff,
      (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
        (arrowIsoSpecΓOfIsAffine (f.normalizationDesc g h H)),
      MorphismProperty.isomorphisms.iff, isIso_SpecMap_iff, ConcreteCategory.isIso_iff_bijective]
  have hcriterion := f.isIso_normalizationDesc_app_iff g h H (isAffineOpen_top _)
  rw [htop] at hcriterion
  simp only [Scheme.Hom.preimage_top] at hcriterion
  rw [hiso, hcriterion]
  exact injective_and_isIntegralElem_mem_range_appTop_iff

variable [IsIntegralClosure C A B]

/-- The spectrum of an integral closure `C` of `A` in `B` is integral over `Spec A`. -/
theorem isIntegralHom_algebraMap_of_isIntegralClosure (B : Type u) [CommRing B]
    [Algebra A B] [Algebra C B] [IsScalarTower A C B] [IsIntegralClosure C A B] :
    IsIntegralHom (Spec.algebraMap A C) :=
  IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr (IsIntegralClosure.isIntegral_algebra A B))

/-- If `C` is the integral closure of `A` in `B`, the canonical map from the relative
normalization of `Spec A` in `Spec B` to `Spec C` is an isomorphism (Stacks, Tags 035H and 035I). -/
theorem isIso_normalizationDesc_spec_of_isIntegralClosure :
    letI := isIntegralHom_algebraMap_of_isIntegralClosure (A := A) (C := C) B
    IsIso ((Spec.algebraMap A B).normalizationDesc (Spec.algebraMap C B) (Spec.algebraMap A C)
      (Spec.algebraMap_comp_algebraMap A C B).symm) := by
  have := isIntegralHom_algebraMap_of_isIntegralClosure (A := A) (C := C) B
  exact isIso_normalizationDesc_spec_iff.mpr ⟨IsIntegralClosure.algebraMap_injective C A B,
    fun _ hb ↦ RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := C)).mp hb)⟩

/-- If `C` is the integral closure of `A` in `B`, the canonical isomorphism from the relative
normalization of `Spec A` in `Spec B` to `Spec C` (Stacks, Tags 035H and 035I). -/
noncomputable def normalizationSpecIso (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B] [IsIntegralClosure C A B] :
    (Spec.algebraMap A B).normalization ≅ Spec (CommRingCat.of C) :=
  letI := isIntegralHom_algebraMap_of_isIntegralClosure (A := A) (C := C) B
  letI := isIso_normalizationDesc_spec_of_isIntegralClosure (A := A) (B := B) (C := C)
  asIso ((Spec.algebraMap A B).normalizationDesc (Spec.algebraMap C B) (Spec.algebraMap A C)
    (Spec.algebraMap_comp_algebraMap A C B).symm)

/-- The forward map of the affine normalization comparison is the universal descent morphism. -/
theorem normalizationSpecIso_hom :
    letI := isIntegralHom_algebraMap_of_isIntegralClosure (A := A) (C := C) B
    (normalizationSpecIso A B C).hom =
      (Spec.algebraMap A B).normalizationDesc (Spec.algebraMap C B) (Spec.algebraMap A C)
        (Spec.algebraMap_comp_algebraMap A C B).symm := (rfl)

/-- The affine normalization isomorphism identifies the map from `Spec B` with the map given
by the inclusion of its integral closure. -/
@[reassoc (attr := simp)]
theorem toNormalization_normalizationSpecIso_hom :
    (Spec.algebraMap A B).toNormalization ≫ (normalizationSpecIso A B C).hom =
      Spec.algebraMap C B := by
  rw [normalizationSpecIso_hom, Scheme.Hom.toNormalization_normalizationDesc]

/-- The affine normalization isomorphism identifies the structure map to `Spec A`. -/
@[reassoc (attr := simp)]
theorem normalizationSpecIso_hom_algebraMap :
    (normalizationSpecIso A B C).hom ≫ Spec.algebraMap A C =
      (Spec.algebraMap A B).fromNormalization := by
  rw [normalizationSpecIso_hom, Scheme.Hom.normalizationDesc_comp]

end TauCeti.AlgebraicGeometry
