/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MaximalIdealPoint

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.RingTheory.Affinoid.Subdomain.Rational.Valuation
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete

/-!
# Density of the classical points in the adic spectrum of an affinoid algebra

Let `A` be a `K`-algebra topologically of finite type over a complete nonarchimedean field `K`.
Its maximal ideals give the classical points of `X = Spa (A, A°)`
(`TauCeti.ValuationSpectrum.maximalSpectrumToSpa`). This file shows that every nonempty rational
subset `R(T/s)` of `X` contains a classical point, and deduces that the classical points are
dense in `X`, since the rational subsets form a basis of its topology.

A point `v` of `R(T/s)` is a continuous valuation with `v(t) ≤ v(s) ≠ 0` for every `t ∈ T`. By
`TauCeti.Huber.IsTopologicallyFiniteType.rationalDomain_nonempty_of_isContinuous` such a valuation
forces the classical rational domain `{x ∈ Sp A : |s(x)| ≠ 0, |t(x)| ≤ |s(x)| for t ∈ T}` to be
nonempty, and the classical points of `R(T/s)` are those of maximal ideals in that domain
(`TauCeti.ValuationSpectrum.maximalSpectrumToSpa_mem_spaBasicOpen_iff`).

Density in the topology of `X` is weaker than Huber's theorem that the classical points are dense
for the constructible topology, which also controls finite Boolean combinations of rational subsets
such as the complement of a rational subset. That theorem is not proved here.

## Main results

* `TauCeti.ValuationSpectrum.exists_maximalSpectrumToSpa_mem_rationalSubset`: every nonempty
  rational subset `R(T/s)` of `Spa (A, A°)` contains a classical point.
* `TauCeti.ValuationSpectrum.denseRange_maximalSpectrumToSpa`: the classical points are dense in
  `Spa (A, A°)`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §7.2.3.
* R. Huber, *Continuous valuations*, Math. Z. 212 (1993), §4.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.58 and Theorem 7.35.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] [Algebra K A]
  [ContinuousSMul K A]

/-- **Every nonempty rational subset contains a classical point.** Let `A` be a `K`-algebra
topologically of finite type. If the rational subset `R(T/s)` of `Spa (A, A°)` has a point, then
it contains the classical point of some maximal ideal of `A`. -/
theorem exists_maximalSpectrumToSpa_mem_rationalSubset
    (hA : IsTopologicallyFiniteType (algebraMap K A)) {T : Finset A} {s : A} {v : Spv A}
    (hv : v ∈ rationalSubset (powerBoundedSubring A) T s) :
    ∃ x : MaximalSpectrum A, (maximalSpectrumToSpa K hA x).val ∈
      rationalSubset (powerBoundedSubring A) T s := by
  obtain ⟨hspa, hle, hs⟩ := (mem_rationalSubset_iff _ _ _ _).mp hv
  have hcont := (isContinuous_def v).mp ((mem_spa_iff _ v).mp hspa).1
  have hvs : v.valuation s ≠ 0 := fun h ↦ hs (by rw [← valuation_le_iff, h, map_zero])
  -- the elements of `T` are the numerators of a classical rational domain
  let f : Fin T.card → A := (↑) ∘ T.equivFin.symm
  obtain ⟨x, hx⟩ := hA.rationalDomain_nonempty_of_isContinuous (g := s) (f := f) hcont hvs
    fun i ↦ (valuation_le_iff v _ _).mpr (hle _ (T.equivFin.symm i).property)
  obtain ⟨hx₀, hx⟩ := mem_rationalDomain.mp hx
  refine ⟨x, mem_spaBasicOpen.mp <| (maximalSpectrumToSpa_mem_spaBasicOpen_iff (hA := hA) T s x).mpr
    ⟨hx₀, fun t ht ↦ by simpa [f] using hx (T.equivFin ⟨t, ht⟩)⟩⟩

/-- **The classical points are dense in `Spa (A, A°)`** for a `K`-algebra `A` topologically of
finite type: every nonempty open subset of the adic spectrum contains the classical point of a
maximal ideal of `A`. -/
theorem denseRange_maximalSpectrumToSpa (hA : IsTopologicallyFiniteType (algebraMap K A)) :
    DenseRange (maximalSpectrumToSpa K hA) := by
  have : IsTateRing A := hA.isTateRing
  refine (isTopologicalBasis_spaRationalFamily _).dense_iff.mpr fun U hU ⟨v, hv⟩ ↦ ?_
  obtain ⟨T, s, -, rfl⟩ := mem_spaRationalFamily_iff.mp hU
  obtain ⟨x, hx⟩ := exists_maximalSpectrumToSpa_mem_rationalSubset hA hv
  exact ⟨_, hx, x, rfl⟩

end TauCeti.ValuationSpectrum
