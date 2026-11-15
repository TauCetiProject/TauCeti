/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MaximalIdealPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Affinoid.TopologicallyFiniteType

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.RingTheory.Affinoid.Subdomain.Rational.Valuation
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Density of the classical points in the adic spectrum of an affinoid algebra

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, with a complete
ultrametric algebra norm. Its maximal ideals give the classical points of `X = Spa (A, A°)`
(`TauCeti.ValuationSpectrum.maximalSpectrumToSpa`). This file shows that every nonempty rational
subset `R(T/s)` of `X` contains a classical point, and deduces that the classical points are
dense in `X`, since the rational subsets form a basis of its topology.

A point `v` of `R(T/s)` is a continuous valuation with `v(t) ≤ v(s) ≠ 0` for every `t ∈ T`. By
`TauCeti.IsAffinoidAlgebra.rationalDomain_nonempty_of_isContinuous` such a valuation forces the
classical rational domain `{x ∈ Sp A : |s(x)| ≠ 0, |t(x)| ≤ |s(x)| for t ∈ T}` to be nonempty, and
the classical point of a maximal ideal in that domain lies in `R(T/s)`: it compares elements of
`A` by their absolute values at the maximal ideal.

Density in the topology of `X` is weaker than Huber's theorem that the classical points are dense
for the constructible topology, which also controls finite Boolean combinations of rational subsets
such as the complement of a rational subset. That theorem is not proved here.

## Main results

* `TauCeti.ValuationSpectrum.exists_maximalSpectrumToSpa_mem_rationalSubset`: every nonempty
  rational subset `R(T/s)` of `Spa (A, A°)` with `(s, T) = A` contains a classical point.
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
  {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormedAlgebra K A] [CompleteSpace A]

/-- **Every nonempty rational subset contains a classical point.** Let `A` be an affinoid algebra
with a complete ultrametric algebra norm, and let `s` and the finite set `T` generate the unit
ideal of `A`. If the rational subset `R(T/s)` of `Spa (A, A°)` has a point, then it contains the
classical point of some maximal ideal of `A`. -/
theorem exists_maximalSpectrumToSpa_mem_rationalSubset (hA : IsAffinoidAlgebra K A)
    {T : Finset A} {s : A} (hT : Ideal.span (insert s (T : Set A)) = ⊤) {v : Spv A}
    (hv : v ∈ rationalSubset (powerBoundedSubring A) T s) :
    ∃ x : MaximalSpectrum A, (maximalSpectrumToSpa K hA.isTopologicallyFiniteType x).1 ∈
      rationalSubset (powerBoundedSubring A) T s := by
  obtain ⟨hspa, hle, hs⟩ := (mem_rationalSubset_iff _ _ _ _).mp hv
  -- enumerate `T` as the numerators of a rational domain
  let f : Fin T.card → A := fun i ↦ T.equivFin.symm i
  have hf : Set.range f = T := by
    ext a
    exact ⟨by rintro ⟨i, rfl⟩; exact (T.equivFin.symm i).2,
      fun ha ↦ ⟨T.equivFin ⟨a, ha⟩, by simp [f]⟩⟩
  have hcont := (isContinuous_def v).mp ((mem_spa_iff _ v).mp hspa).1
  have hvs : v.valuation s ≠ 0 := fun h ↦ hs (by rw [← valuation_le_iff, h, map_zero])
  obtain ⟨x, hx⟩ := hA.rationalDomain_nonempty_of_isContinuous (g := s) (f := f)
    (hf ▸ hT) hcont hvs fun i ↦ (valuation_le_iff v _ _).mpr (hle _ (T.equivFin.symm i).2)
  obtain ⟨hx0, hx⟩ := mem_rationalDomain.mp hx
  -- the classical point at `x` compares elements by their absolute values at `x`
  let := Ideal.Quotient.field x.asIdeal
  have hnorm (a : A) : pointNorm K x a =
      spectralNorm K (A ⧸ x.asIdeal) (Ideal.Quotient.mk x.asIdeal a) :=
    pointNorm_eq_spectralNorm (ψ := Ideal.Quotient.mkₐ K x.asIdeal)
      (fun b hb ↦ (Ideal.Quotient.mkₐ_eq_mk K x.asIdeal ▸
        Ideal.Quotient.eq_zero_iff_mem.mpr hb :)) a
  refine ⟨x, (mem_rationalSubset_iff _ _ _ _).mpr ⟨(maximalSpectrumToSpa K _ x).2,
    fun t ht ↦ ?_, ?_⟩⟩
  · rw [maximalSpectrumToSpa_vle_iff, ← hnorm, ← hnorm]
    simpa [f] using hx (T.equivFin ⟨t, ht⟩)
  · rw [maximalSpectrumToSpa_vle_iff, ← hnorm, ← hnorm, pointNorm_zero]
    exact fun h ↦ hx0 (h.antisymm (pointNorm_nonneg s))

/-- **The classical points are dense in `Spa (A, A°)`** for an affinoid algebra `A` with a
complete ultrametric algebra norm: every nonempty open subset of the adic spectrum contains the
classical point of a maximal ideal of `A`. -/
theorem denseRange_maximalSpectrumToSpa (hA : IsAffinoidAlgebra K A) :
    DenseRange (maximalSpectrumToSpa K hA.isTopologicallyFiniteType) := by
  have : IsTateRing A := IsTateRing.of_normedAlgebra K A
  refine (isTopologicalBasis_spaRationalFamily _).dense_iff.mpr fun U hU ⟨v, hv⟩ ↦ ?_
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalFamily_iff.mp hU
  -- an open ideal of the Tate ring `A` is the unit ideal
  have hsT : Ideal.span (insert s (T : Set A)) = ⊤ :=
    top_le_iff.mp ((IsTateRing.eq_top_of_isOpen hT).symm.le.trans
      (Ideal.span_mono (Set.subset_insert _ _)))
  obtain ⟨x, hx⟩ := exists_maximalSpectrumToSpa_mem_rationalSubset hA hsT hv
  exact ⟨_, hx, x, rfl⟩

end TauCeti.ValuationSpectrum
