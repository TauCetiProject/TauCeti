/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import TauCeti.RingTheory.Derivation.Localization
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# The Jacobian criterion for hypersurfaces

Let `f ∈ A`, and let `P` be a prime of the hypersurface ring `A ⧸ (f)` lying over a prime `Q` of
`A` at which `A` is regular, i.e. `A_Q` is a regular local ring. If some derivation `D` of `A` has
`D f ∉ Q`, then the local ring `(A ⧸ (f))_P` is regular: `f` lies outside the square of the
maximal ideal of the regular local ring `A_Q`, so it is a regular parameter there, and
`(A ⧸ (f))_P` is `A_Q ⧸ (f)`.

For `A = k[X, Y]` over a field `k` and the partial derivatives `∂f/∂X` and `∂f/∂Y`, this is the
Jacobian criterion for plane curves: if `f` is irreducible and `f`, `∂f/∂X`, `∂f/∂Y` generate
the unit ideal, so that the affine curve `f = 0` has no singular point over any extension of `k`,
then the local ring of `k[X, Y] ⧸ (f)` at every nonzero prime is a discrete valuation ring and
`k[X, Y] ⧸ (f)` is a Dedekind domain. In particular the coordinate ring of a smooth affine plane
curve is integrally closed in the function field of the curve; this is what identifies it with
the integral closure of `k[x]` when `y` is integral over `k[x]`, the setting in which differents
of the function field over `k(x)` are computed from `∂f/∂Y`.

## Main results

* `Ideal.isRegularLocalRing_localization_of_derivation_notMem`: the localization of
  `A ⧸ (f)` at a prime over `Q` is a regular local ring when `A_Q` is regular and `D f ∉ Q`.
* `MvPolynomial.isDedekindDomain_quotient_span_singleton`: the coordinate ring of a smooth
  irreducible affine plane curve over a field is a Dedekind domain.

## References

* [Stacks Project, Lemma 10.106.3](https://stacks.math.columbia.edu/tag/00NQ): the quotient of a
  regular local ring by a regular parameter is regular.
* W. Fulton, *Algebraic Curves*, Section 3.2, Theorem 1: a point of a plane curve is simple
  exactly when its local ring is a discrete valuation ring.
-/

public section

open Ideal IsLocalRing

namespace Ideal

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **The Jacobian criterion for a hypersurface.** Let `f ∈ A` and let `P` be a prime of
`A ⧸ (f)` lying over the prime `Q` of `A`, with `A_Q` a regular local ring. If some derivation `D`
of `A` maps `f` outside `Q`, then the localization of `A ⧸ (f)` at `P` is a regular local ring. -/
theorem isRegularLocalRing_localization_of_derivation_notMem {f : A}
    (P : Ideal (A ⧸ span {f})) [P.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime (P.comap (Ideal.Quotient.mk (span {f}))))]
    {D : Derivation R A A} (hD : D f ∉ P.comap (Ideal.Quotient.mk _)) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  set Q := P.comap (Ideal.Quotient.mk (span {f}))
  set B := Localization.AtPrime Q
  -- `f` is a regular parameter of the regular local ring `A_Q`
  have hfm : algebraMap A B f ∈ maximalIdeal B := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q]
    simp [Q, Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self f)]
  have :=
    TauCeti.IsRegularLocalRing.quotient_span_singleton hfm (D.algebraMap_notMem_maximalIdeal_sq hD)
  -- `A_Q ⧸ (f)` is the localization of `A ⧸ (f)` at `P`
  have hspan : (span {f}).map (algebraMap A B) = span {algebraMap A B f} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hsub : Algebra.algebraMapSubmonoid (A ⧸ span {f}) Q.primeCompl = P.primeCompl := by
    ext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨fun ⟨b, hb, hba⟩ ↦ hba ▸ hb, fun ha ↦ ⟨a, ha, rfl⟩⟩
  have hloc : IsLocalization P.primeCompl (B ⧸ (span {f}).map (algebraMap A B)) :=
    hsub ▸ inferInstance
  exact .of_ringEquiv ((quotientEquivAlgOfEq A hspan).toRingEquiv.symm.trans
    (IsLocalization.algEquiv P.primeCompl _ (Localization.AtPrime P)).toRingEquiv)

end Ideal

namespace MvPolynomial

variable {k : Type*} [Field k]

/-- **The coordinate ring of a smooth affine plane curve is a Dedekind domain.** If
`f ∈ k[X, Y]` is irreducible and `f`, `∂f/∂X`, `∂f/∂Y` generate the unit ideal, that is the curve
`f = 0` has no singular point, then `k[X, Y] ⧸ (f)` is a Dedekind domain. -/
theorem isDedekindDomain_quotient_span_singleton {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hsm : span {f, pderiv 0 f, pderiv 1 f} = ⊤) :
    IsDedekindDomain (MvPolynomial (Fin 2) k ⧸ span {f}) := by
  have hprime : (span {f}).IsPrime := (span_singleton_prime hf.ne_zero).mpr hf.prime
  -- the curve has dimension at most one, `f` being a nonzerodivisor of the plane `k[X, Y]`
  have hdim : ringKrullDim (MvPolynomial (Fin 2) k ⧸ span {f}) + 1 ≤ 2 := by
    simpa [ringKrullDim_eq_zero_of_field] using
      ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf.ne_zero)
  refine (isDedekindDomain_iff_isDiscreteValuationRing_atPrime).mpr
    ⟨inferInstance, fun P hP _ ↦ ?_⟩
  -- some partial derivative of `f` does not vanish at `P`
  obtain ⟨i, hi⟩ : ∃ i, pderiv i f ∉ P.comap (Ideal.Quotient.mk (span {f})) := by
    by_contra! h
    refine (Ideal.IsPrime.comap (Ideal.Quotient.mk (span {f})) (hK := ‹_›)).ne_top ?_
    rw [eq_top_iff, ← hsm, span_le, Set.insert_subset_iff, Set.pair_subset_iff]
    exact ⟨by simp [Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self f)], h 0, h 1⟩
  -- so the local ring at `P` is regular, of dimension the height of `P`, which is one
  have := P.isRegularLocalRing_localization_of_derivation_notMem hi
  have hheight : P.height = 1 := by
    have h1 : ((P.height + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((1 + 1 : ℕ∞) : WithBot ℕ∞) := by
      push_cast
      rw [one_add_one_eq_two]
      exact (by gcongr; exact height_le_ringKrullDim_of_isPrime :
        (P.height : WithBot ℕ∞) + 1 ≤ _ + 1).trans hdim
    exact le_antisymm ((ENat.add_le_add_iff_right ENat.one_ne_top).mp (WithBot.coe_le_coe.mp h1))
      (Order.one_le_iff_ne_zero.mpr (height_eq_zero_iff_eq_bot.not.mpr hP))
  rw [TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one,
    IsLocalization.AtPrime.ringKrullDim_eq_height P, hheight]
  rfl

end MvPolynomial
