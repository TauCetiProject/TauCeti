/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.CoordinateOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-!
# Node charts at smooth points of relative curves

For a morphism locally of finite presentation of pure relative dimension one over `Spec R`,
a point of the smooth locus has an affine étale neighbourhood mapping étale over `Spec R` to
`uv = 0`. At the image of the chosen point the first coordinate is nonzero and the second
vanishes. The construction also applies directly to a smooth morphism of relative dimension
one. These charts complement the normal form at nonsmooth points of a nodal curve.

## References

* Stacks Project, [Tag 0C58](https://stacks.math.columbia.edu/tag/0C58).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

universe u

/-- A scheme smooth of relative dimension one over `Spec R` has an affine étale node chart
at every point, with first coordinate nonzero and second coordinate zero at that point. -/
theorem exists_etale_nodeAlgebra_zero_of_smoothOfRelativeDimension_one
    (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of R))] (x : X) :
    ∃ (T : Type u) (_ : CommRing T) (g : Spec (.of T) ⟶ X)
      (ψ : Spec (.of T) ⟶ Spec (.of (TauCeti.NodeAlgebra R 0))) (y : Spec (.of T)),
      Etale g ∧ Etale ψ ∧ g y = x ∧
        g ≫ (X ↘ Spec (.of R)) = ψ ≫ Spec.algebraMap R (TauCeti.NodeAlgebra R 0) ∧
        TauCeti.NodeAlgebra.coord 0 0 ∉ (ψ y).asIdeal ∧
        TauCeti.NodeAlgebra.coord 0 1 ∈ (ψ y).asIdeal := by
  obtain ⟨V, hxV, hV⟩ :=
    TauCeti.AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension R
      (X := X) 1 x
  let : Algebra R Γ(X, V) :=
    ((X.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 R Γ(X, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hV
  let p := V.property.primeIdealOf ⟨x, hxV⟩
  obtain ⟨t, ht, φ, hφ, hu, hv⟩ :=
    Ideal.exists_notMem_etale_nodeAlgebra_hom_of_isStandardSmoothOfRelativeDimension_one
      R p.asIdeal p.isPrime.ne_top
  let T := Localization.Away t
  have hd : Disjoint (Submonoid.powers t : Set Γ(X, V)) p.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem _ p.isPrime.isRadical).mpr ht
  let Q := p.asIdeal.map (algebraMap Γ(X, V) T)
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ T _ p.isPrime hd
  let y : Spec (.of T) := ⟨Q, inferInstance⟩
  have hy : Spec.algebraMap Γ(X, V) T y = p := by
    rw [Spec.map_apply, CommRingCat.hom_ofHom]
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal, ← Ideal.under_def]
    exact IsLocalization.under_map_of_isPrime_disjoint _ T p.isPrime hd
  have hVbase : V.property.fromSpec ≫ (X ↘ Spec (.of R)) =
      Spec.algebraMap R Γ(X, V) := by
    have := TauCeti.AlgebraicGeometry.isOver_fromSpec R X V
    rwa [Scheme.Hom.isOver_iff, specOverSpec_over] at this
  have : Etale (Spec.algebraMap Γ(X, V) T) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t))
  have : Etale (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hφ
  have := V.property.isOpenImmersion_fromSpec
  refine ⟨T, inferInstance, Spec.algebraMap Γ(X, V) T ≫ V.property.fromSpec,
    Spec.map (CommRingCat.ofHom φ.toRingHom), y, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, hy]
    exact V.property.fromSpec_primeIdealOf ⟨x, hxV⟩
  · have hψ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.algebraMap R (TauCeti.NodeAlgebra R 0) = Spec.algebraMap R T := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, φ.comp_algebraMap]
    rw [hψ, Category.assoc, hVbase, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  · rw [Spec.map_apply, CommRingCat.hom_ofHom, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    exact Q.notMem_of_isUnit hu
  · rw [Spec.map_apply, CommRingCat.hom_ofHom, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    simpa using hv ▸ Q.zero_mem

/-- At a smooth point of a relative curve, there is an affine étale neighbourhood mapping
étale over the base to `uv = 0`, with the first coordinate nonzero at the chosen point and the
second zero. The base ring is arbitrary. -/
theorem exists_etale_nodeAlgebra_zero_of_mem_smoothLocus {R : Type u} [CommRing R]
    (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
    [TauCeti.AlgebraicGeometry.PureRelativeDimension 1 (X ↘ Spec (.of R))]
    {x : X} (hx : x ∈ (X ↘ Spec (.of R)).smoothLocus) :
    ∃ (T : Type u) (_ : CommRing T) (g : Spec (.of T) ⟶ X)
      (ψ : Spec (.of T) ⟶ Spec (.of (TauCeti.NodeAlgebra R 0))) (y : Spec (.of T)),
      Etale g ∧ Etale ψ ∧ g y = x ∧
        g ≫ (X ↘ Spec (.of R)) = ψ ≫ Spec.algebraMap R (TauCeti.NodeAlgebra R 0) ∧
        TauCeti.NodeAlgebra.coord 0 0 ∉ (ψ y).asIdeal ∧
        TauCeti.NodeAlgebra.coord 0 1 ∈ (ψ y).asIdeal := by
  let U := (X ↘ Spec (.of R)).smoothLocus
  let : U.toScheme.Over (Spec (.of R)) := ⟨U.ι ≫ (X ↘ Spec (.of R))⟩
  have : SmoothOfRelativeDimension 1 (U.toScheme ↘ Spec (.of R)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (U.ι ≫ (X ↘ Spec (.of R))))
  obtain ⟨T, _, g, ψ, y, hg, hψ, hgy, hbase, hu, hv⟩ :=
    U.toScheme.exists_etale_nodeAlgebra_zero_of_smoothOfRelativeDimension_one (R := R) ⟨x, hx⟩
  refine ⟨T, inferInstance, g ≫ U.ι, ψ, y, inferInstance, hψ, ?_, ?_, hu, hv⟩
  · rw [Scheme.Hom.comp_apply, hgy, U.ι_apply]
  · exact (Category.assoc _ _ _).trans hbase

end AlgebraicGeometry.Scheme
