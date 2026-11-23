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
# Kronecker graphs avoiding a hypersurface

For a commutative ring `R` and `m ≠ 0`, the spectrum of the base-`B` Kronecker substitution
`MvPolynomial.polynomialGraph R m B` is a closed immersion
`Spec R[T] → Spec R[X_0, …, X_{m-1}]`, the graph `T ↦ (T, T ^ B, …, T ^ (B ^ (m - 1)))` of the
affine line in affine `m`-space. Given a nonzero polynomial `h`, choosing `B` larger than every
exponent of `h` makes the pullback of `h` along this graph nonzero
(`AlgebraicGeometry.exists_avoiding_graph`). The preimage of the complement of the hypersurface
`V(h)` under the graph is the principal open subset of the nonzero pullback. Over a field this is a
nonempty, hence dense, open subset of the affine line, since `k[T]` is a domain; over a ring with
nilpotents it can be empty. This is how a curve through a rational point of an étale chart of
affine space is made to meet a prescribed dense open subset.

The base must be chosen after `h`: for `m ≥ 2` the graph itself lies in the hypersurface
`V(X_1 - X_0 ^ B)`.

For every `m` and `B` the graph is a morphism over `Spec R`, and for `B ≠ 0` it sends the origin
of the line to the origin of affine `m`-space.

## Main results

* `AlgebraicGeometry.isClosedImmersion_spec_map_polynomialGraph`: for `m ≠ 0` the graph is a
  closed immersion.
* `AlgebraicGeometry.exists_avoiding_graph`: a nonzero polynomial in `m ≠ 0` variables has
  nonzero pullback along the closed immersion given by some base `B ≥ 2` exceeding all of its
  exponents.
* `AlgebraicGeometry.SpecMap_polynomialGraph_comp_SpecMap_algebraMap`: the graph is a morphism
  over `Spec R`.
* `AlgebraicGeometry.SpecMap_constantCoeff_comp_SpecMap_polynomialGraph`: for `B ≠ 0` the graph
  sends the origin to the origin.
* `TauCeti.AlgebraicGeometry.nonempty_and_dense_SpecMap_polynomialGraph_preimage_basicOpen`:
  over a domain the preimage of the complement of a hypersurface is nonempty and dense
  when its defining polynomial is nonzero and the base exceeds all of its exponents.

## References

* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945v2, proofs of Corollary 5.2.7 and Proposition 5.3.5, where a curve
  through a rational point meeting a dense open set is needed.
-/

public section

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The graph `Spec R[T] → Spec R[X_0, …, X_{m-1}]` of the base-`B` Kronecker substitution is a
morphism over `Spec R`, for every `m` and every base `B`. -/
@[reassoc]
theorem SpecMap_polynomialGraph_comp_SpecMap_algebraMap (B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph R m B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin m) R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, MvPolynomial.algebraMap_eq,
    polynomialGraph_comp_C, Polynomial.algebraMap_eq]

/-- For `B ≠ 0` the graph of the base-`B` Kronecker substitution sends the origin of the affine
line, the spectrum of `Polynomial.constantCoeff`, to the origin of affine `m`-space, the spectrum
of `MvPolynomial.constantCoeff`. For `B = 0` and `m ≥ 2` it does not, since then `X_1 ↦ 1`. -/
@[reassoc (attr := simp)]
theorem SpecMap_constantCoeff_comp_SpecMap_polynomialGraph {B : ℕ} (hB : B ≠ 0) :
    Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := R))) ≫
      Spec.map (CommRingCat.ofHom (polynomialGraph R m B)) =
      Spec.map (CommRingCat.ofHom (constantCoeff (R := R) (σ := Fin m))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, constantCoeff_comp_polynomialGraph hB]

variable [NeZero m]

/-- For `m ≠ 0` the graph `Spec R[T] → Spec R[X_0, …, X_{m-1}]` of the base-`B` Kronecker
substitution, `T ↦ (T, T ^ B, …, T ^ (B ^ (m - 1)))`, is a closed immersion, for every base `B`. -/
instance isClosedImmersion_spec_map_polynomialGraph (B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph R m B))) :=
  .spec_of_surjective _ polynomialGraph_surjective

/-- **A Kronecker graph avoiding a hypersurface.** For `m ≠ 0` and a nonzero polynomial `h` in
`m` variables over a commutative ring, there is a base `B ≥ 2` exceeding every exponent in the
support of `h` such that the pullback of `h` along the graph `T ↦ (T, T ^ B, …, T ^ (B ^ (m - 1)))`
is nonzero, the graph being a closed immersion. By `MvPolynomial.polynomialGraph_eq_zero_iff`, every
base exceeding all exponents of `h` makes the pullback nonzero. -/
theorem exists_avoiding_graph {h : MvPolynomial (Fin m) R} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph R m B h ≠ 0 ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph R m B))) := by
  obtain ⟨B, hB, hbound, hne⟩ := h.exists_polynomialGraph_ne_zero hh
  exact ⟨B, hB, hbound, hne, inferInstance⟩

end AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Over a domain, the preimage of `D(h)` along a polynomial graph is nonempty and dense if `h`
is nonzero and the base exceeds every exponent in its support. This does not assert that the
preimage has a rational point, and holds even in dimension zero. -/
theorem nonempty_and_dense_SpecMap_polynomialGraph_preimage_basicOpen
    {R : Type*} [CommRing R] [IsDomain R] {m B : ℕ} {h : MvPolynomial (Fin m) R} (hh : h ≠ 0)
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
