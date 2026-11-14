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

A smooth point of a morphism of pure relative dimension one has an étale neighbourhood
mapping étale to the smooth part of `uv = 0`. No base extension is needed. This complements
the normal form at nonsmooth points and allows node charts around every point of a nodal curve.
The first coordinate of the chart is invertible and the second vanishes.

## References

* Stacks Project, [Tag 0C58](https://stacks.math.columbia.edu/tag/0C58).
* Mathlib's `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` supplies
  the étale coordinate used in `Ideal.exists_notMem_etale_nodeAlgebra_hom_of_isStandardSmooth`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

universe u

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
  obtain ⟨V, hxV, hV⟩ :=
    TauCeti.AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension R
      (X := U.toScheme) 1 (⟨x, hx⟩ : U)
  let : Algebra R Γ(U.toScheme, V) :=
    ((U.toScheme.baseRingToStructurePresheaf R).app (op V.1)).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 R Γ(U.toScheme, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hV
  let p := V.2.primeIdealOf ⟨⟨x, hx⟩, hxV⟩
  obtain ⟨t, ht, φ, hφ, hu, hv⟩ :=
    Ideal.exists_notMem_etale_nodeAlgebra_hom_of_isStandardSmooth (R := R) p.asIdeal
  let T := Localization.Away t
  have hd : Disjoint (Submonoid.powers t : Set Γ(U.toScheme, V)) p.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem _ p.2.isRadical).mpr ht
  let Q := p.asIdeal.map (algebraMap Γ(U.toScheme, V) T)
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ T _ p.2 hd
  let y : Spec (.of T) := ⟨Q, inferInstance⟩
  have hy : Spec.algebraMap Γ(U.toScheme, V) T y = p := by
    apply PrimeSpectrum.ext
    exact IsLocalization.under_map_of_isPrime_disjoint _ T p.2 hd
  have hVbase : V.2.fromSpec ≫ (U.toScheme ↘ Spec (.of R)) =
      Spec.algebraMap R Γ(U.toScheme, V) := by
    have := TauCeti.AlgebraicGeometry.isOver_fromSpec R U.toScheme V
    rwa [Scheme.Hom.isOver_iff, specOverSpec_over] at this
  -- Record the structure map of the chosen `Over` instance before rewriting the triangle.
  have hU : (U.toScheme ↘ Spec (.of R)) = U.ι ≫ (X ↘ Spec (.of R)) := rfl
  rw [hU] at hVbase
  have : Etale (Spec.algebraMap Γ(U.toScheme, V) T) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t))
  have : Etale (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hφ
  have := V.2.isOpenImmersion_fromSpec
  refine ⟨T, inferInstance, Spec.algebraMap Γ(U.toScheme, V) T ≫ V.2.fromSpec ≫ U.ι,
    Spec.map (CommRingCat.ofHom φ.toRingHom), y, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, hy]
    exact (Scheme.Hom.comp_apply V.2.fromSpec U.ι p).trans
      (congrArg U.ι (V.2.fromSpec_primeIdealOf ⟨⟨x, hx⟩, hxV⟩))
  · have hψ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.algebraMap R (TauCeti.NodeAlgebra R 0) = Spec.algebraMap R T := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, φ.comp_algebraMap]
    rw [hψ, Category.assoc, Category.assoc, hVbase, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  · exact Q.notMem_of_isUnit hu
  · have hmem : φ (TauCeti.NodeAlgebra.coord 0 1) ∈ Q := hv ▸ Q.zero_mem
    exact hmem

end AlgebraicGeometry.Scheme
