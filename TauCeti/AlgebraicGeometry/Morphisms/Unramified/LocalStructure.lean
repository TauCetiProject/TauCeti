/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Étale local structure of unramified morphisms

An unramified morphism is, étale locally on its target, a closed immersion near any given
point. Let `g : Z ⟶ Spec R` be unramified and let `z` be a point of `Z`.

* Some open neighbourhood of `z` is a closed subscheme of `Spec E` over `Spec R`, for an étale
  `R`-algebra `E` (`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_etale_of_unramified`).
  This is the scheme form of Mathlib's `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`:
  a finite type algebra unramified at a prime is, after inverting an element outside it, a
  quotient of a standard étale algebra.
* After base change along `Spec E ⟶ Spec R`, the graph of that closed immersion is an open
  subscheme of `Z ×_{Spec R} Spec E`. It maps isomorphically onto an open neighbourhood of `z`
  in `Z`, and closed-immerses into `Spec E`
  (`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_of_isPullback_etale`). The graph is an
  open immersion because it is a section of the unramified projection to `Z`.

## References

* The Stacks Project, Chapter *Étale Morphisms of Schemes*, Section *Étale local structure of
  unramified morphisms*.
-/

public section

open CategoryTheory Limits TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}

/-- **Local structure of unramified morphisms.** If `g : Z ⟶ Spec R` is unramified, then every
point `z` of `Z` has an open neighbourhood `ι : W ⟶ Z` which is a closed subscheme of `Spec E`
over `Spec R`, for some étale `R`-algebra `E`. -/
theorem exists_isClosedImmersion_etale_of_unramified (g : Z ⟶ Spec (.of R)) [Unramified g]
    (z : Z) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E) (_ : Algebra.Etale R E)
      (W : Scheme.{u}) (ι : W ⟶ Z) (j : W ⟶ Spec (.of E)) (w : W),
      IsOpenImmersion ι ∧ IsClosedImmersion j ∧ j ≫ Spec.algebraMap R E = ι ≫ g ∧ ι w = z := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  replace hV : IsAffineOpen V := hV
  obtain ⟨z₀, rfl⟩ : z ∈ Set.range (Scheme.Opens.ι V) := by simpa using hzV
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hV.isoSpec.inv ≫ Scheme.Opens.ι V ≫ g)
  algebraize [ψ.hom]
  have : Algebra.Unramified R Γ(Z, V) := by
    rw [← Unramified.Spec_iff (φ := ψ), hψ]
    infer_instance
  set Q : PrimeSpectrum Γ(Z, V) := hV.isoSpec.hom z₀ with hQ
  -- Mathlib's local structure theorem: `Γ(Z, V)[1/f]` is a quotient of a standard étale algebra.
  obtain ⟨f, hfQ, P, φ, hφ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) Q.asIdeal
  obtain ⟨w, hw⟩ : Q ∈ Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, V) (Localization.Away f)))) := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_localizationAway]
    exact hfQ
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, _,
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, V) (Localization.Away f))) ≫
      hV.isoSpec.inv ≫ Scheme.Opens.ι V,
    Spec.map (CommRingCat.ofHom φ.toRingHom), w, inferInstance,
    IsClosedImmersion.spec_of_surjective _ hφ, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply R Γ(Z, V) (Localization.Away f) r
  · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw, hQ, Scheme.hom_inv_apply]

/-- **Étale local structure of unramified morphisms.** If `g : Z ⟶ Spec R` is unramified and
`z` is a point of `Z`, then there is an étale `R`-algebra `E` such that on every base change
`Z'` of `Z` along `Spec E ⟶ Spec R`, with projections `p : Z' ⟶ Z` and `g' : Z' ⟶ Spec E`, some
open subscheme `σ : W ⟶ Z'` containing a point above `z` maps isomorphically onto an open
subscheme of `Z` under `p` and is a closed subscheme of `Spec E` under `g'`. -/
theorem exists_isClosedImmersion_of_isPullback_etale (g : Z ⟶ Spec (.of R)) [Unramified g]
    (z : Z) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E) (_ : Algebra.Etale R E),
      ∀ {Z' : Scheme.{u}} (p : Z' ⟶ Z) (g' : Z' ⟶ Spec (.of E)),
        IsPullback p g' g (Spec.algebraMap R E) →
        ∃ (W : Scheme.{u}) (σ : W ⟶ Z') (w : W), IsOpenImmersion σ ∧
          IsOpenImmersion (σ ≫ p) ∧ IsClosedImmersion (σ ≫ g') ∧ p (σ w) = z := by
  obtain ⟨E, _, _, _, W, ι, j, w, hι, hj, hcomm, hw⟩ :=
    g.exists_isClosedImmersion_etale_of_unramified z
  refine ⟨E, inferInstance, inferInstance, inferInstance, fun p g' H ↦ ?_⟩
  have : Etale (Spec.algebraMap R E) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : Unramified p := MorphismProperty.of_isPullback (P := @Unramified) H.flip inferInstance
  -- The graph `W ⟶ Z'` of `j` is a section of `p` over the open subscheme `W` of `Z`.
  have hσp : IsOpenImmersion (H.lift ι j hcomm.symm ≫ p) := by rwa [H.lift_fst]
  have hσg : IsClosedImmersion (H.lift ι j hcomm.symm ≫ g') := by rwa [H.lift_snd]
  refine ⟨W, H.lift ι j hcomm.symm, w,
    MorphismProperty.of_postcomp @IsOpenImmersion (W' := @Unramified) _ p ‹_› hσp, hσp, hσg, ?_⟩
  rw [← Scheme.Hom.comp_apply, H.lift_fst, hw]

end AlgebraicGeometry.Scheme.Hom
