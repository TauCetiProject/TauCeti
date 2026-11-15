/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic

/-!
# Rational covers when every prime ideal is open

When every prime ideal of `A` is open, for instance when `A` is discrete, the trivial valuation of
every prime is a point of `Spa(A, A⁺)`, whatever the plus ring `A⁺`
(`trivialSection_mem_spa_iff`). The trivial valuation of a prime `𝔭` takes only the values `0` and
`1`, so it lies in the rational subset `R(T/s)` exactly when `s ∉ 𝔭`
(`trivialSection_mem_rationalSubset_iff`, in the rational-subset API). Testing a covering of
rational subsets on these points turns it into a statement about prime ideals.

If `R(T/s) ⊆ ⋃ⱼ R(Tⱼ/sⱼ)`, then the images of the `sⱼ` generate the unit ideal of the localization
`A_s`: a maximal ideal of `A_s` containing all of them would contract to a prime `𝔭 ∌ s` of `A`
containing every `sⱼ`, and the trivial valuation of `𝔭` would lie in `R(T/s)` but in no `R(Tⱼ/sⱼ)`.
This is the step of Wedhorn's Theorem 8.28 in the discrete case that reduces a rational covering
of `R(T/s)` to the principal open covering of `Spec A_s` by the `D(sⱼ)`. With it, for a finite
cover, the exactness of the Čech complex of localizations (`TauCeti.cechComplexLocalization_exact`)
applies to the `A_s`-module `M_s` and the family `(sⱼ / 1)`, for every `A`-module `M`. The case
of a single rational subset says that `R(T'/s') ⊆ R(T/s)` makes `s` invertible in `A_{s'}`
(`isUnit_algebraMap_of_rationalSubset_subset`), so the localization maps `A_s → A_{s'}` exist.

The covering hypothesis cannot be dropped: for discrete `k[T]` with plus ring `k`, the trivial
valuation with support `(T)` lies in `R(1/1)` but not in `R(1, T/T)`, and `T` does not generate
the unit ideal.

## Main results

* `TauCeti.ValuationSpectrum.span_eq_top_of_rationalSubset_subset_iUnion`: if every prime is open
  and `R(T/s) ⊆ ⋃ⱼ R(Tⱼ/sⱼ)`, the `sⱼ` generate the unit ideal of `A_s`.
* `TauCeti.ValuationSpectrum.isUnit_algebraMap_of_rationalSubset_subset`: if every prime is open
  and `R(T'/s') ⊆ R(T/s)`, then `s` is a unit of `A_{s'}`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 4.6 and Theorem 8.28,
  case (c).
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] {Aplus : Subring A}

/-- **Rational covers when every prime is open.** If every prime ideal of `A` is open (for
instance, `A` is discrete) and the rational subsets `R(Tⱼ/sⱼ)` cover `R(T/s)`, then the images of
the `sⱼ` generate the unit ideal of the localization `A_s`. So, for a finite cover, the Čech
complex of localizations of `M_s` at the `sⱼ` is exact for every `A`-module `M`
(`TauCeti.cechComplexLocalization_exact`). The index type is arbitrary here and the plus ring
plays no role. -/
theorem span_eq_top_of_rationalSubset_subset_iUnion {T : Finset A} {s : A} (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hopen : ∀ 𝔭 : Ideal A, 𝔭.IsPrime → IsOpen (𝔭 : Set A)) {ι : Type*} {T' : ι → Finset A}
    {σ : ι → A} (hcov : rationalSubset Aplus T s ⊆ ⋃ j, rationalSubset Aplus (T' j) (σ j)) :
    Ideal.span (Set.range fun j ↦ algebraMap A S (σ j)) = ⊤ := by
  by_contra hne
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
  let p : PrimeSpectrum A := ⟨𝔪.comap (algebraMap A S), h𝔪.isPrime.comap _⟩
  have hs : s ∉ p.asIdeal := fun h ↦
    h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
    (hcov ((trivialSection_mem_rationalSubset_iff Aplus T s p).mpr ⟨hopen _ p.isPrime, hs⟩))
  exact ((trivialSection_mem_rationalSubset_iff Aplus _ _ p).mp hj).2
    (hle (Ideal.subset_span ⟨j, rfl⟩))

/-- If every prime ideal of `A` is open and `R(T'/s') ⊆ R(T/s)`, then `s` becomes a unit in the
localization `A_{s'}`. This is the one-member case of
`span_eq_top_of_rationalSubset_subset_iUnion`. -/
theorem isUnit_algebraMap_of_rationalSubset_subset {T T' : Finset A} {s s' : A} (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s' S]
    (hopen : ∀ 𝔭 : Ideal A, 𝔭.IsPrime → IsOpen (𝔭 : Set A))
    (h : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    IsUnit (algebraMap A S s) := by
  have hspan := span_eq_top_of_rationalSubset_subset_iUnion (T := T') (s := s') S hopen
    (ι := Unit) (T' := fun _ ↦ T) (σ := fun _ ↦ s) (by rwa [Set.iUnion_const])
  rwa [Set.range_const, Ideal.span_singleton_eq_top] at hspan

end TauCeti.ValuationSpectrum

end
