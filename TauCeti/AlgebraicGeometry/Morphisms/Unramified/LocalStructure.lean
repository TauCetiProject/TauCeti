/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.QuasiFinite.Basic
import TauCeti.RingTheory.Spectrum.Prime.Finite

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
* If `R` has finitely many prime ideals, for instance if `R` is a discrete valuation ring, then
  `E` can be taken to be a local ring whose closed point is the image of the chosen point above `z`
  (`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_isLocalRing_etale_of_unramified` and
  `AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_of_isPullback_isLocalRing_etale`). Such
  an `E` has finitely many primes, so its localization at that point inverts a single element.

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

/-- The graph of a morphism `j : W ⟶ Spec E` over `Spec R`, defined on an open subscheme `W` of
`Z`, is an open immersion into the base change of `Z` along the étale `Spec E ⟶ Spec R`: it is a
section of the unramified projection over `W`. -/
private theorem isOpenImmersion_lift_of_isPullback {E : Type u} [CommRing E] [Algebra R E]
    [Algebra.Etale R E] {g : Z ⟶ Spec (.of R)} {W Z' : Scheme.{u}} {ι : W ⟶ Z}
    [IsOpenImmersion ι] {j : W ⟶ Spec (.of E)} {p : Z' ⟶ Z} {g' : Z' ⟶ Spec (.of E)}
    (H : IsPullback p g' g (Spec.algebraMap R E)) (hcomm : j ≫ Spec.algebraMap R E = ι ≫ g) :
    IsOpenImmersion (H.lift ι j hcomm.symm) := by
  have : Etale (Spec.algebraMap R E) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : Unramified p := MorphismProperty.of_isPullback (P := @Unramified) H.flip inferInstance
  have : IsOpenImmersion (H.lift ι j hcomm.symm ≫ p) := by rwa [H.lift_fst]
  exact MorphismProperty.of_postcomp @IsOpenImmersion (W' := @Unramified) _ p ‹_› ‹_›

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
  refine ⟨W, H.lift ι j hcomm.symm, w, isOpenImmersion_lift_of_isPullback H hcomm,
    by rwa [H.lift_fst], by rwa [H.lift_snd], ?_⟩
  rw [← Scheme.Hom.comp_apply, H.lift_fst, hw]

/-- **Local structure of unramified morphisms over a base with finitely many primes.** If `R` has
finitely many prime ideals and `g : Z ⟶ Spec R` is unramified, then every point `z` of `Z` has an
open neighbourhood `ι : W ⟶ Z` which is a closed subscheme `j : W ⟶ Spec E` over `Spec R`, for
some local étale `R`-algebra `E`, such that a point `w` of `W` above `z` maps to the closed point
of `Spec E`. -/
theorem exists_isClosedImmersion_isLocalRing_etale_of_unramified [Finite (PrimeSpectrum R)]
    (g : Z ⟶ Spec (.of R)) [Unramified g] (z : Z) :
    ∃ (E : Type u) (_ : CommRing E) (_ : IsLocalRing E) (_ : Algebra R E) (_ : Algebra.Etale R E)
      (W : Scheme.{u}) (ι : W ⟶ Z) (j : W ⟶ Spec (.of E)) (w : W),
      IsOpenImmersion ι ∧ IsClosedImmersion j ∧ j ≫ Spec.algebraMap R E = ι ≫ g ∧ ι w = z ∧
        j w = IsLocalRing.closedPoint E := by
  obtain ⟨E, _, _, _, W, ι, j, w, hι, hj, hcomm, hw⟩ :=
    g.exists_isClosedImmersion_etale_of_unramified z
  -- `E` is quasi-finite over `R`, so it has finitely many primes, and its localization at `j w`
  -- is a localization `E[1/f]`.
  have : Finite (PrimeSpectrum E) := Algebra.QuasiFinite.finite_primeSpectrum R E
  obtain ⟨f, -, _⟩ := PrimeSpectrum.exists_notMem_isLocalization_atPrime_away (j w)
  have := (j w).isPrime
  have : IsLocalRing (Localization.Away f) :=
    IsLocalization.AtPrime.isLocalRing (Localization.Away f) (j w).asIdeal
  have : Algebra.Etale R (Localization.Away f) := Algebra.Etale.comp R E _
  -- The closed point of `Spec E[1/f]` lies over `j w`.
  obtain ⟨w', hw'₁, hw'₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := j)
    (g := Spec.algebraMap E (Localization.Away f)) w (IsLocalRing.closedPoint _) <| by
      refine .trans (PrimeSpectrum.ext ?_) (Spec.map_apply ..).symm
      rw [PrimeSpectrum.comap_asIdeal]
      exact (IsLocalization.AtPrime.under_maximalIdeal _ (j w).asIdeal).symm
  refine ⟨Localization.Away f, inferInstance, inferInstance, inferInstance, inferInstance, _,
    pullback.fst _ _ ≫ ι, pullback.snd _ _, w', inferInstance, inferInstance, ?_, ?_, hw'₂⟩
  · rw [Category.assoc, ← hcomm, pullback.condition_assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  · rw [Scheme.Hom.comp_apply, hw'₁, hw]

/-- **Étale local structure of unramified morphisms over a base with finitely many primes.** If
`R` has finitely many prime ideals, `g : Z ⟶ Spec R` is unramified and `z` is a point of `Z`, then
there is a local étale `R`-algebra `E`, whose closed point lies over the image of `z`, such that on
every base change `Z'` of `Z` along `Spec E ⟶ Spec R`, with projections `p : Z' ⟶ Z` and
`g' : Z' ⟶ Spec E`, some open subscheme `σ : W ⟶ Z'` maps isomorphically onto an open subscheme
of `Z` under `p` and is a closed subscheme of `Spec E` under `g'`, and contains a point above `z`
mapping to the closed point of `Spec E`. -/
theorem exists_isClosedImmersion_of_isPullback_isLocalRing_etale [Finite (PrimeSpectrum R)]
    (g : Z ⟶ Spec (.of R)) [Unramified g] (z : Z) :
    ∃ (E : Type u) (_ : CommRing E) (_ : IsLocalRing E) (_ : Algebra R E) (_ : Algebra.Etale R E),
      Spec.algebraMap R E (IsLocalRing.closedPoint E) = g z ∧
      ∀ {Z' : Scheme.{u}} (p : Z' ⟶ Z) (g' : Z' ⟶ Spec (.of E)),
        IsPullback p g' g (Spec.algebraMap R E) →
        ∃ (W : Scheme.{u}) (σ : W ⟶ Z') (w : W), IsOpenImmersion σ ∧
          IsOpenImmersion (σ ≫ p) ∧ IsClosedImmersion (σ ≫ g') ∧ p (σ w) = z ∧
          g' (σ w) = IsLocalRing.closedPoint E := by
  obtain ⟨E, _, _, _, _, W, ι, j, w, hι, hj, hcomm, hw, hjw⟩ :=
    g.exists_isClosedImmersion_isLocalRing_etale_of_unramified z
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, ?_, fun p g' H ↦ ?_⟩
  · rw [← hjw, ← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply, hw]
  refine ⟨W, H.lift ι j hcomm.symm, w, isOpenImmersion_lift_of_isPullback H hcomm,
    by rwa [H.lift_fst], by rwa [H.lift_snd], ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, H.lift_fst, hw]
  · rw [← Scheme.Hom.comp_apply, H.lift_snd, hjw]

end AlgebraicGeometry.Scheme.Hom
