/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.RingTheory.MvPolynomial.PolynomialGraph

import Mathlib.RingTheory.Polynomial.Nilpotent
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Polynomial graphs `𝔸¹_k → 𝔸^m_k` avoiding a hypersurface

For a commutative ring `k` and natural numbers `m, B`, the spectrum of the base-`B` Kronecker
substitution `MvPolynomial.polynomialGraph k m B : MvPolynomial (Fin m) k →+* Polynomial k` is the
graph morphism
`Spec.map (CommRingCat.ofHom (MvPolynomial.polynomialGraph k m B))` from `Spec k[T]` to
`Spec k[X_0, …, X_{m-1}]`, geometrically `T ↦ (T, T ^ B, …, T ^ (B ^ (m - 1)))`.

For `m > 0`, `MvPolynomial.polynomialGraph k m B` is surjective, so this graph is a closed
immersion (`TauCeti.AlgebraicGeometry.isClosedImmersion_specMap_polynomialGraph`); over a
nontrivial ring, it is a closed immersion if and only if `0 < m`
(`TauCeti.AlgebraicGeometry.isClosedImmersion_specMap_polynomialGraph_iff`). It is a morphism over
`Spec k` (`TauCeti.AlgebraicGeometry.specMap_polynomialGraph_comp_C`), is natural in base change
along ring homomorphisms (`TauCeti.AlgebraicGeometry.specMap_polynomialGraph_naturality`), and for
`1 ≤ B` carries the origin of `Spec k[T]` to the origin of `Spec k[X_0, …, X_{m-1}]`
(`TauCeti.AlgebraicGeometry.specMap_polynomialGraph_origin`).

Given any nonzero polynomial `h ∈ k[X_0, …, X_{m-1}]` (`0 < m`), choosing `B ≥ 2` strictly
exceeding every exponent in `h` yields a closed-immersion graph along which `h` pulls back to a
nonzero polynomial (`TauCeti.AlgebraicGeometry.exists_avoiding_graph`). Over a reduced ring, the
preimage of the basic open `D(h)` under such a graph is nonempty
(`TauCeti.AlgebraicGeometry.nonempty_preimage_basicOpen_polynomialGraph`), and over a ring with no
zero divisors (in particular over any integral domain or field) it is dense in `Spec k[T]`
(`TauCeti.AlgebraicGeometry.dense_preimage_basicOpen_polynomialGraph`).

## Main results

* `TauCeti.AlgebraicGeometry.isClosedImmersion_specMap_polynomialGraph`,
  `TauCeti.AlgebraicGeometry.isClosedImmersion_specMap_polynomialGraph_iff`: the graph morphism is
  a closed immersion for `0 < m`, and over a nontrivial ring if and only if `0 < m`.
* `TauCeti.AlgebraicGeometry.specMap_polynomialGraph_comp_C`: the graph morphism lies over
  `Spec k`.
* `TauCeti.AlgebraicGeometry.specMap_polynomialGraph_origin`: for `1 ≤ B`, the graph maps the
  origin of `Spec k[T]` to the origin of `Spec k[X_0, …, X_{m-1}]`.
* `TauCeti.AlgebraicGeometry.specMap_polynomialGraph_naturality`: compatibility with base change
  along a ring homomorphism `k →+* K`.
* `TauCeti.AlgebraicGeometry.exists_avoiding_graph`: for `0 < m` and nonzero `h`, there is `B ≥ 2`
  exceeding every exponent of `h` such that `polynomialGraph k m B h ≠ 0` and the graph is a
  closed immersion.
* `TauCeti.AlgebraicGeometry.nonempty_preimage_basicOpen_polynomialGraph`,
  `TauCeti.AlgebraicGeometry.dense_preimage_basicOpen_polynomialGraph`: nonemptiness (over a
  reduced ring) and density (over a ring without zero divisors) of the preimage of `D(h)` when `B`
  exceeds every exponent of a nonzero `h`.

## References

* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945v2, proofs of Corollary 5.2.7 (pp. 52–53) and Proposition 5.3.5
  (p. 54).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace TauCeti.AlgebraicGeometry

/-- For `0 < m`, the spectrum of `MvPolynomial.polynomialGraph k m B` is a closed immersion
`Spec k[T] ⟶ Spec k[X_0, …, X_{m-1}]`, for every `B : ℕ`. -/
theorem isClosedImmersion_specMap_polynomialGraph (k : Type u) [CommRing k] {m : ℕ} (hm : 0 < m)
    (B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) :=
  IsClosedImmersion.spec_of_surjective _ (polynomialGraph_surjective k hm B)

/-- Over a nontrivial commutative ring, the graph morphism
`Spec k[T] ⟶ Spec k[X_0, …, X_{m-1}]` is a closed immersion if and only if `0 < m`. -/
theorem isClosedImmersion_specMap_polynomialGraph_iff (k : Type u) [CommRing k] [Nontrivial k]
    (m B : ℕ) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) ↔ 0 < m := by
  rw [IsClosedImmersion.hasAffineProperty.SpecMap_iff_of_affineAnd RingHom.surjective_respectsIso,
    CommRingCat.hom_ofHom, polynomialGraph_surjective_iff]

/-- The graph morphism `Spec k[T] ⟶ Spec k[X_0, …, X_{m-1}]` is a morphism over `Spec k`. -/
@[reassoc (attr := simp)]
theorem specMap_polynomialGraph_comp_C (k : Type u) [CommRing k] (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ≫
        Spec.map (CommRingCat.ofHom (C : k →+* MvPolynomial (Fin m) k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, polynomialGraph_comp_C]

/-- For `1 ≤ B`, the graph morphism `Spec k[T] ⟶ Spec k[X_0, …, X_{m-1}]` maps the origin of
`Spec k[T]` to the origin of `Spec k[X_0, …, X_{m-1}]`. -/
@[reassoc (attr := simp)]
theorem specMap_polynomialGraph_origin (k : Type u) [CommRing k] (m : ℕ) {B : ℕ} (hB : 1 ≤ B) :
    Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := k))) ≫
        Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (R := k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, constantCoeff_comp_polynomialGraph k m hB]

/-- The graph morphism commutes with base change along a ring homomorphism `f : k →+* K`. -/
@[reassoc]
theorem specMap_polynomialGraph_naturality {k K : Type u} [CommRing k] [CommRing K]
    (f : k →+* K) (m B : ℕ) :
    Spec.map (CommRingCat.ofHom (polynomialGraph K m B)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map f)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
        Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    polynomialGraph_comp_map]

/-- **A Kronecker graph avoiding a hypersurface.** For `0 < m` and a nonzero polynomial `h` in `m`
variables over a commutative ring `k`, there is a base `B ≥ 2` strictly exceeding every exponent in
the support of `h` such that `polynomialGraph k m B h ≠ 0` and the graph
`Spec k[T] ⟶ Spec k[X_0, …, X_{m-1}]` is a closed immersion. -/
theorem exists_avoiding_graph {k : Type u} [CommRing k] {m : ℕ} (hm : 0 < m)
    {h : MvPolynomial (Fin m) k} (hh : h ≠ 0) :
    ∃ B : ℕ, 2 ≤ B ∧ (∀ d ∈ h.support, ∀ i, d i < B) ∧ polynomialGraph k m B h ≠ 0 ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) := by
  obtain ⟨B, hB2, hB, hne⟩ := exists_polynomialGraph_ne_zero hh
  exact ⟨B, hB2, hB, hne, isClosedImmersion_specMap_polynomialGraph k hm B⟩

/-- Over a reduced commutative ring, if `B` strictly exceeds every exponent in a nonzero polynomial
`h`, then the preimage of the basic open `D(h)` under the base-`B` graph morphism is nonempty. -/
theorem nonempty_preimage_basicOpen_polynomialGraph {k : Type u} [CommRing k] [IsReduced k]
    {m B : ℕ} {h : MvPolynomial (Fin m) k} (hh : ∀ d ∈ h.support, ∀ i, d i < B) (hne : h ≠ 0) :
    (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen h : Set (Spec (.of (Polynomial k)))).Nonempty := by
  rw [SpecMap_preimage_basicOpen, CommRingCat.ofHom_apply]
  refine (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp
    ((PrimeSpectrum.basicOpen_eq_bot_iff _).not.mpr fun hnil ↦ ?_)
  rw [Polynomial.isNilpotent_iff] at hnil
  exact (polynomialGraph_eq_zero_iff hh).not.mpr hne
    (by ext n; simpa [isNilpotent_iff_eq_zero] using hnil n)

/-- Over a commutative ring without zero divisors (in particular, over any integral domain or
field), if `B` strictly exceeds every exponent in a nonzero polynomial `h`, then the preimage of
the basic open `D(h)` under the base-`B` graph morphism is dense in `Spec k[T]`. -/
theorem dense_preimage_basicOpen_polynomialGraph {k : Type u} [CommRing k] [NoZeroDivisors k]
    {m B : ℕ} {h : MvPolynomial (Fin m) k} (hh : ∀ d ∈ h.support, ∀ i, d i < B) (hne : h ≠ 0) :
    Dense (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen h : Set (Spec (.of (Polynomial k)))) := by
  rw [SpecMap_preimage_basicOpen, CommRingCat.ofHom_apply]
  exact PrimeSpectrum.dense_basicOpen_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero ((polynomialGraph_eq_zero_iff hh).not.mpr hne))

end TauCeti.AlgebraicGeometry
