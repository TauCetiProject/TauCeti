/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Normalization

import TauCeti.AlgebraicGeometry.Normalization.IsIso
import TauCeti.AlgebraicGeometry.Scheme.SpecAlgHom

/-!
# Relative normalization of a morphism of affine schemes

## Main results

* `TauCeti.AlgebraicGeometry.exists_iso_normalization_spec_of_isIntegralClosure` identifies
  the relative normalization of a morphism of spectra with the spectrum of its integral closure
  and identifies both maps in the normalization factorization.

The comparison uses Mathlib's `Scheme.Hom.normalizationDesc` and Tau Ceti's
`Scheme.Hom.isIso_normalizationDesc_app_iff`.

## References

* [Stacks Project, Section 29.53](https://stacks.math.columbia.edu/tag/035H).
-/

public section

open _root_.AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]

/-- If `C` is the integral closure of `A` in `B`, its spectrum identifies with the relative
normalization of `Spec A` in `Spec B`. The identification respects both scheme morphisms in
the normalization factorization (Stacks, Section 29.53, Tag 035H). -/
theorem exists_iso_normalization_spec_of_isIntegralClosure [IsIntegralClosure C A B] :
    ∃ e : (Spec.algebraMap A B).normalization ≅
        Spec (CommRingCat.of C),
      (Spec.algebraMap A B).toNormalization ≫ e.hom =
        Spec.algebraMap C B ∧
      e.hom ≫ Spec.algebraMap A C =
        (Spec.algebraMap A B).fromNormalization := by
  let f := Spec.algebraMap A B
  let g := Spec.algebraMap C B
  let h := Spec.algebraMap A C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A B
  have hh : IsIntegralHom h := IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr ‹Algebra.IsIntegral A C›)
  have H : f = g ≫ h := (Spec.algebraMap_comp_algebraMap A C B).symm
  have hi : IsIso (f.normalizationDesc g h H) := by
    have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
    rw [← MorphismProperty.isomorphisms.iff,
      MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
        (arrowIsoSpecΓOfIsAffine (f.normalizationDesc g h H)),
      MorphismProperty.isomorphisms.iff]
    suffices IsIso (f.normalizationDesc g h H).appTop from inferInstance
    apply (f.isIso_normalizationDesc_app_iff g h H (isAffineOpen_top _)).mpr
    have htop : g.appLE (h ⁻¹ᵁ ⊤) (f ⁻¹ᵁ ⊤) (by simp only [Scheme.Hom.preimage_top, le_refl]) =
        g.appTop := g.appLE_eq_app (U := ⊤)
    rw [htop]
    have hgΓ : g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom (algebraMap C B) :=
      Scheme.ΓSpecIso_naturality _
    have hg : Function.Injective g.appTop := by
      have hinj : Function.Injective (g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) := by
        rw [hgΓ]
        exact (IsIntegralClosure.algebraMap_injective C A B).comp
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).hom).injective
      exact hinj.of_comp (f := (Scheme.ΓSpecIso (CommRingCat.of B)).hom)
    have hs (s : Γ(Spec (CommRingCat.of B), ⊤)) (hs : f.appTop.hom.IsIntegralElem s) :
        s ∈ g.appTop.hom.range := by
      let e := Scheme.ΓSpecIso (CommRingCat.of B)
      have hs' := hs.map e.hom.hom
      rw [← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp] at hs'
      have hsB : _root_.IsIntegral A (e.hom s) := hs'.of_comp
      obtain ⟨c, hc⟩ := (IsIntegralClosure.isIntegral_iff (A := C)).mp hsB
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of C)).inv c, ?_⟩
      apply (ConcreteCategory.bijective_of_isIso e.hom).injective
      rw [← CommRingCat.comp_apply, hgΓ]
      simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
        Iso.inv_hom_id_apply] using hc
    exact ⟨hg, hs⟩
  exact ⟨asIso (f.normalizationDesc g h H), f.toNormalization_normalizationDesc g h H,
    f.normalizationDesc_comp g h H⟩

end TauCeti.AlgebraicGeometry
