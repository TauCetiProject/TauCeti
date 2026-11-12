/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Going down for torsion-free integral algebras

Mathlib proves going down for an integral extension `R ⊆ S` of an integrally closed domain `R`
when `S` is a domain (Stacks, Proposition 10.38.7 (00H8)). This file removes the requirement that
`S` be a domain, replacing injectivity of `R → S` by torsion-freeness of `S` as an `R`-module.

A prime `Q` of `S` contains a minimal prime `𝔭` of `S`. Elements of a minimal prime are zero
divisors, while torsion-freeness makes the image of every nonzero element of `R` a
non-zero-divisor, so `𝔭` lies over the zero ideal of `R`. Thus `S ⧸ 𝔭` is an integral extension
domain of `R`, Mathlib's theorem applies to it, and primes of `S ⧸ 𝔭` pull back to primes of `S`
below `Q`.

Torsion-freeness cannot be dropped. Over an integrally closed local domain `(R, 𝔪)` of
positive dimension, the finite algebra `R × R ⧸ 𝔪` has the prime `R × 0` lying over `𝔪`, and no
smaller prime of `R × R ⧸ 𝔪` lies over `0`. This is the closed-point factor that finite normal
algebras over a local ring must exclude when studying finite étale covers of punctured spectra.

## Main results

* `Algebra.HasGoingDown.of_isIntegral_of_isTorsionFree`: an integral, torsion-free algebra over an
  integrally closed domain satisfies going down.

## References

* [Stacks Project, Proposition 10.38.7](https://stacks.math.columbia.edu/tag/00H8), going down
  for integral extensions of a normal domain.
-/

public section

namespace Algebra.HasGoingDown

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An integral algebra `S` over an integrally closed domain `R` satisfies going down as soon as
`S` is torsion free as an `R`-module. This generalizes Stacks, Proposition 10.38.7 (00H8), where
`S` is a domain containing `R`. -/
@[stacks 00H8 "for a torsion-free integral algebra, not necessarily a domain"]
instance of_isIntegral_of_isTorsionFree [IsDomain R] [IsIntegrallyClosed R]
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] : Algebra.HasGoingDown R S where
  exists_ideal_le_liesOver_of_lt {p} _ Q _ hlt := by
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (J := Q) bot_le
    have : P.IsPrime := hP.1.1
    -- The minimal prime `P` lies over `0`: its elements are zero divisors of `S`, while the
    -- nonzero elements of `R` act injectively on `S`.
    have hP0 : ∀ r : R, algebraMap R S r ∈ P → r = 0 := fun r hr ↦ by
      by_contra hr0
      obtain ⟨s, hs, hrs⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hr
      refine hs ((isRegular_iff_ne_zero.mpr hr0).isSMulRegular (a₂ := (0 : S)) ?_)
      simpa [Algebra.smul_def] using hrs
    have : FaithfulSMul R (S ⧸ P) := (faithfulSMul_iff_algebraMap_injective R _).mpr <|
      (injective_iff_map_eq_zero _).mpr fun r hr ↦ hP0 r <| by
        rwa [IsScalarTower.algebraMap_apply R S, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem] at hr
    -- Going down holds for the integral extension domain `S ⧸ P`; pull the prime back to `S`.
    have hQ : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hPQ)
    have hcomap (J : Ideal (S ⧸ P)) : (J.comap (Ideal.Quotient.mk P)).under R = J.under R := by
      rw [Ideal.under_def, Ideal.under_def, Ideal.comap_comap,
        IsScalarTower.algebraMap_eq R S (S ⧸ P), Ideal.Quotient.algebraMap_eq]
    have hmap : (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        sup_eq_left.mpr hPQ]
    have hunder : (Q.map (Ideal.Quotient.mk P)).under R = Q.under R := by
      rw [← hcomap, hmap]
    obtain ⟨P', hP'Q, hP', hP'p⟩ :=
      Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (S := S ⧸ P) _ (hunder ▸ hlt)
    refine ⟨P'.comap (Ideal.Quotient.mk P), ?_, Ideal.comap_isPrime _ _, ⟨?_⟩⟩
    · exact (Ideal.comap_mono hP'Q).trans_eq hmap
    · rw [hcomap, hP'p.over]

end Algebra.HasGoingDown
