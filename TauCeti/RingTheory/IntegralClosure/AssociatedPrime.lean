/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import TauCeti.RingTheory.Ideal.Quotient.Colon

/-!
# Integral closedness at the associated primes of principal ideals

Let `R` be a Noetherian domain with fraction field `K`. An element `a / b` of `K` lying in the
localization `R_P` at every associated prime `P` of `R ⧸ (b)` already lies in `R`: otherwise
`a ∉ (b)`, and an associated prime `P` of `R ⧸ (b)` containing the colon ideal `((b) : a)` gives
`a / b = r / s` with `s ∉ P`, so that `s a ∈ (b)` and `s ∈ P`. Hence `R` is integrally closed as
soon as its localizations at these primes are.

In the applications the associated primes of `R ⧸ (b)` have height one, so that the relevant
localizations are one-dimensional, and the criterion reduces integral closedness to discrete
valuation rings. This is how regular rings and rings satisfying Serre's conditions `(R₁)` and
`(S₂)` are shown to be normal.

## Main results

* `TauCeti.IsIntegrallyClosed.of_localization_isAssociatedPrime`: a Noetherian domain is
  integrally closed if its localization at every associated prime of `R ⧸ (b)`, for every
  nonzero `b`, is integrally closed.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 11.5.
* The proof is the last step of `TauCeti.IsRegularRing.isIntegrallyClosed`, ported from
  T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Common/RegularNormal.lean`, `Pcf.Stacks.isIntegrallyClosed_of_isRegularRing`.
-/

public section

namespace TauCeti.IsIntegrallyClosed

open _root_.Ideal

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- A Noetherian domain is integrally closed if, for every nonzero `b`, its localization at every
associated prime of `R ⧸ (b)` is integrally closed. -/
theorem of_localization_isAssociatedPrime
    (h : ∀ b ∈ R⁰, ∀ (P : Ideal R) [P.IsPrime], IsAssociatedPrime P (R ⧸ span {b}) →
      IsIntegrallyClosed (Localization.AtPrime P)) :
    IsIntegrallyClosed R := by
  classical
  let K := FractionRing R
  -- localize at the primes where `R_p` is integrally closed, so that the side condition of
  -- `IsIntegrallyClosed.of_localization` is exactly the defining condition of this set
  apply IsIntegrallyClosed.of_localization
    {p : PrimeSpectrum R | IsIntegrallyClosed (Localization.AtPrime p.asIdeal)}
    fun _ hp ↦ by simpa using hp
  rw [eq_bot_iff]
  intro z hz
  simp only [Algebra.mem_iInf, Set.mem_ofPred_eq] at hz
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) (K := K) z
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  by_cases hab : a ∈ span {b}
  · obtain ⟨r, hr⟩ := mem_span_singleton'.mp hab
    exact Algebra.mem_bot.mpr ⟨r, by rw [← hr, map_mul, mul_div_cancel_right₀ _ hbK]⟩
  exfalso
  -- an associated prime `P = ((b) : c)` of `R ⧸ (b)` containing `((b) : a)`
  obtain ⟨P, hPass, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (span {b}) a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have := hPass.isPrime
  have hcolon : ∀ r, r * a ∈ span {b} → r ∈ P := fun r hr ↦
    hle (Ideal.Quotient.mem_colon_singleton_mk.mpr hr)
  -- `a / b = r / s` with `s ∉ P` gives `s a ∈ (b)`, so `s ∈ P`
  have hzP := hz ⟨P, inferInstance⟩ (h b hb P hPass)
  rw [← Localization.subalgebra.ofField_eq K P.primeCompl P.primeCompl_le_nonZeroDivisors] at hzP
  obtain ⟨r, s, hs, hrs⟩ := hzP
  have hsK : algebraMap R K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (P.primeCompl_le_nonZeroDivisors hs)
  rw [← div_eq_mul_inv, div_eq_div_iff hbK hsK, ← map_mul, ← map_mul] at hrs
  exact hs (hcolon s (mem_span_singleton'.mpr ⟨r, by
    rw [mul_comm s, IsFractionRing.injective R K hrs]⟩))

end TauCeti.IsIntegrallyClosed
