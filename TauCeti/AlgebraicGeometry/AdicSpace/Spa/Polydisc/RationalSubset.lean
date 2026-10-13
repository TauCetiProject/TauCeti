/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.Restricted.OneVariable
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.DenseRange
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Polynomial presentations of rational subsets of the closed unit disc

Every rational subset of the closed unit disc over a nontrivially normed ultrametric
field has a presentation by polynomials. The numerator set can be chosen to contain a
nonzero constant, so it generates the unit ideal even in the polynomial ring.
Conversely, every such polynomial presentation defines a rational subset.

This reduces the description of rational subdomains to polynomial inequalities, to which
factorisation into linear factors can be applied over an algebraically closed field.
Neither completeness nor algebraic closedness is needed for the reduction itself.

The central formal inputs are `TauCeti.Huber.denseRange_eval₂RingHom_weightedX` and
the rational-presentation approximation in `RationalSubset.DenseRange`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 7.34 and Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

local notation "𝒯" K => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "X" => weightedX (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NonarchimedeanRing K]

open scoped Classical in
/-- Rational subsets of the closed unit disc are exactly those admitting polynomial
numerators and denominator with a nonzero constant among the numerators. In particular,
the polynomial numerators themselves generate the unit ideal. -/
theorem mem_spaRationalFamily_iff_exists_polynomial
    (U : Set (spa (powerBoundedSubring (𝒯 K)))) :
    U ∈ spaRationalFamily (powerBoundedSubring (𝒯 K)) ↔
      ∃ (G : Finset (Polynomial K)) (p : Polynomial K) (c : K), c ≠ 0 ∧
        Polynomial.C c ∈ G ∧
        U = Subtype.val ⁻¹' rationalSubset (powerBoundedSubring (𝒯 K))
          (G.image (Polynomial.eval₂RingHom C X)) ((Polynomial.eval₂RingHom C X) p) := by
  classical
  constructor
  · intro hU
    obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalFamily_iff.mp hU
    obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one K
    have hc : IsUnit c := isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hc₀)
    have hn : IsTopologicallyNilpotent (C c : 𝒯 K) :=
      (IsPseudoUniformizer.of_norm_lt_one hc hc₁).isTopologicallyNilpotent.map
        (continuous_weightedC isWeightFamily_one_weight)
    obtain ⟨n, G, p, hmem, heq⟩ :=
      exists_pow_mem_rationalSubset_image_eq_of_denseRange
        (Polynomial.eval₂RingHom C X)
        (denseRange_eval₂RingHom_weightedX isWeightFamily_one_weight)
        (u := Polynomial.C c) (by simpa using hn)
        (powerBoundedSubring (𝒯 K)) T hT s
    refine ⟨G, p, c ^ n, pow_ne_zero _ (norm_pos_iff.mp hc₀),
      by simpa using hmem, ?_⟩
    ext v
    simpa only [Set.mem_preimage, mem_rationalSubset_iff, Finset.mem_image] using
      Set.ext_iff.mp heq.symm v.1
  · rintro ⟨G, p, c, hc, hmem, rfl⟩
    have hunit : IsUnit ((Polynomial.eval₂RingHom C X) (Polynomial.C c) : 𝒯 K) :=
      ((isUnit_iff_ne_zero.mpr hc).map Polynomial.C).map (Polynomial.eval₂RingHom C X)
    have hspan : Ideal.span ((G.image (Polynomial.eval₂RingHom C X) : Finset (𝒯 K)) :
        Set (𝒯 K)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _
        (Ideal.subset_span (Finset.mem_image.mpr ⟨Polynomial.C c, hmem, rfl⟩)) hunit
    exact mem_spaRationalFamily_iff.mpr ⟨_, _, by rw [hspan]; simp, rfl⟩

end TauCeti.ValuationSpectrum
