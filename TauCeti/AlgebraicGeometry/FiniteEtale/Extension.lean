/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections

/-!
# Extending finite étale covers from their sections

For a Noetherian local ring `A` of depth at least two, a finite étale cover `V` of its
punctured spectrum extends to `Spec A` if and only if `Γ(V, ⊤)` is finite étale over `A`.
The extension in the reverse direction is the spectrum of the sections algebra.

The section-recovery result
`TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_flat` recovers the algebra of
an existing extension. In the other direction Mathlib's
`AlgebraicGeometry.Scheme.isPullback_toSpecΓ_toSpecΓ` identifies an affine morphism over a
quasi-affine scheme with the restriction of the morphism on spectra of global sections.

## References

* [The Stacks Project, Lemma 58.20.2](https://stacks.math.columbia.edu/tag/0BLK).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

private theorem sectionsMap_finite_etale_of_spec_extension
    (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme)
    (B : (CommAlgCat.FiniteEtale.{u} (CommRingCat.of A))ᵒᵖ)
    (j : (FiniteEtaleScheme.pullback (puncturedSpectrum A).ι).obj
      ((FiniteEtaleScheme.spec (.of A)).obj B) ≅ V) :
    let φ := (Scheme.ΓSpecIso (.of A)).inv ≫
      (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop
    φ.hom.Finite ∧ φ.hom.Etale := by
  let U := puncturedSpectrum A
  let φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ U.ι).appTop
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B.unop.obj))
  have : IsFinite g := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr B.unop.property.1)
  have : Etale g := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr B.unop.property.2)
  -- Identify the given cover with the open subscheme of the affine extension.
  let j₀ : Over.mk (pullback.snd g U.ι) ≅ V.obj := by
    have hB : ((FiniteEtaleScheme.spec (.of A)).obj B).obj = Over.mk g := by
      rw [FiniteEtaleScheme.spec_obj_obj]
      rfl
    have hj := (finiteEtaleSchemeProperty U.toScheme).ι.mapIso j
    simp only [ObjectProperty.ι_obj, FiniteEtaleScheme.pullback_obj_obj, hB] at hj
    exact hj
  let e₀ := (Over.forget U.toScheme).mapIso j₀
  let eV := e₀.symm ≪≫ pullbackRestrictIsoRestrict g U
  let W := g ⁻¹ᵁ U
  -- Hartogs recovers the extension algebra from sections of this open.
  have hΓ := TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_flat
    (A := A) (B := B.unop.obj) hdepth (W.ι ''ᵁ ⊤) fun p hp ↦ by
      rw [Scheme.Opens.ι_image_top]
      apply (mem_puncturedSpectrum_iff A (g p)).mpr
      intro he
      apply hp
      exact congrArg PrimeSpectrum.asIdeal he
  have : IsIso W.ι.appTop := by
    rw [Scheme.Opens.ι_appTop]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hΓ
  let σ := (Scheme.ΓSpecIso (.of B.unop.obj)).inv ≫ W.ι.appTop ≫ eV.hom.appTop
  have : IsIso eV.hom.appTop := by
    exact Scheme.Γ.map_isIso eV.hom.op
  have : IsIso σ := by dsimp only [σ]; infer_instance
  -- This identification respects the map from the local base ring.
  have heV : eV.hom ≫ W.ι ≫ g = V.obj.hom ≫ U.ι := by
    calc
      _ = e₀.inv ≫ pullback.fst g U.ι ≫ g := by
        simp only [eV, W, Iso.trans_hom, Iso.symm_hom, Category.assoc,
          pullbackRestrictIsoRestrict_hom_ι_assoc]
      _ = e₀.inv ≫ pullback.snd g U.ι ≫ U.ι := by rw [pullback.condition]
      _ = V.obj.hom ≫ U.ι := by
        rw [← Category.assoc]
        exact congrArg (fun k ↦ k ≫ U.ι) (Over.w j₀.inv)
  have hcomp : φ = CommRingCat.ofHom (algebraMap A B.unop.obj) ≫ σ := by
    dsimp only [φ, σ]
    rw [← heV, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    simp only [g, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  have hfinite : IsFinite (Spec.map φ) := by
    rw [hcomp, Spec.map_comp]
    infer_instance
  have hetale : Etale (Spec.map φ) := by
    rw [hcomp, Spec.map_comp]
    infer_instance
  exact ⟨(IsFinite.SpecMap_iff _).mp hfinite,
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hetale⟩

/-- A finite étale cover of the punctured spectrum of a Noetherian local ring of depth at
least two extends across the closed point if and only if its global sections are a finite
étale algebra over the local ring. The algebra structure is induced by the cover's structure
morphism followed by the punctured-spectrum inclusion. -/
@[stacks 0BLK]
theorem extends_iff_sections_finiteEtale (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)),
      Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
    letI := (((Scheme.ΓSpecIso (.of A)).inv ≫
      (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom).toAlgebra
    Module.Finite A Γ(V.obj.left, ⊤) ∧ Algebra.Etale A Γ(V.obj.left, ⊤) := by
  let U := puncturedSpectrum A
  let φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ U.ι).appTop
  -- The canonical algebra structure is `φ.hom.toAlgebra`; the ring-hom formulations
  -- make the following transports independent of a chosen algebra instance.
  change _ ↔ φ.hom.Finite ∧ φ.hom.Etale
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    have : (FiniteEtaleScheme.spec (.of A)).EssSurj := by
      rw [← FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor]
      infer_instance
    obtain ⟨B, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (FiniteEtaleScheme.spec (.of A)) Y
    exact sectionsMap_finite_etale_of_spec_extension A hdepth V B
      ((FiniteEtaleScheme.pullback U.ι).mapIso i ≪≫ e)
  · rintro ⟨hfinite, hetale⟩
    have : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff _).mpr hfinite
    have : Etale (Spec.map φ) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hetale
    let h := (isPullback_puncturedSpectrum_toSpecΓ A hdepth V.obj.hom).flip
    refine ⟨FiniteEtaleScheme.ofHom (Spec.map φ), ⟨ObjectProperty.isoMk _ ?_⟩⟩
    simp only [restrictPunctured, FiniteEtaleScheme.pullback_obj_obj,
      FiniteEtaleScheme.ofHom_obj]
    exact Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd

end TauCeti.IsLocalRing
