/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.RingTheory.MvPolynomial.PolynomialGraph
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Closed polynomial graphs avoiding hypersurfaces

The spectrum of the base-`B` substitution is a closed immersion in positive dimension.
For every nonzero polynomial one can choose a base at least two so that its pullback remains
nonzero. Over a domain the inverse image of its principal open is nonempty and dense.
In particular this works over finite fields without requiring a rational point of that open.
The origin identity is `TauCeti.constantCoeff_comp_polynomialGraph`.
-/

public section

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {R : Type*} [CommRing R] {m B : ℕ}

/-- The polynomial graph is a closed immersion in positive dimension, at every base. -/
theorem isClosedImmersion_polynomialGraph (hm : 0 < m) (B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph R m B))) :=
  IsClosedImmersion.spec_of_surjective _ (polynomialGraph_surjective R hm B)

/-- Every nonzero hypersurface equation admits a closed polynomial graph through the origin
on which it remains nonzero. Over a ring with nilpotents this does not assert that the inverse
image of its complement is nonempty. -/
theorem exists_avoiding_graph (hm : 0 < m) {h : MvPolynomial (Fin m) R} (hh : h ≠ 0) :
    ∃ B, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph R m B h ≠ 0 ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph R m B))) := by
  obtain ⟨B, hB, hbound, hne⟩ := exists_polynomialGraph_ne_zero hh
  exact ⟨B, hB, hbound, hne, isClosedImmersion_polynomialGraph hm B⟩

/-- Over a domain, the inverse image of the hypersurface complement along a bounded-base
graph is nonempty and dense. This does not assert that the open contains a rational point,
and does not require positive dimension or a positive base. -/
theorem polynomialGraph_preimage_basicOpen_nonempty_dense [IsDomain R]
    {h : MvPolynomial (Fin m) R} (hh : h ≠ 0)
    (hbound : ∀ d ∈ h.support, ∀ i, d i < B) :
    let U := Spec.map (CommRingCat.ofHom (polynomialGraph R m B)) ⁻¹ᵁ PrimeSpectrum.basicOpen h
    (U : Set (Spec (.of (Polynomial R)))).Nonempty ∧
      Dense (U : Set (Spec (.of (Polynomial R)))) := by
  dsimp only
  rw [SpecMap_preimage_basicOpen]
  have hd := PrimeSpectrum.dense_basicOpen_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr ((polynomialGraph_eq_zero_iff hbound).not.mpr hh))
  exact ⟨hd.nonempty, hd⟩

end TauCeti.AlgebraicGeometry
