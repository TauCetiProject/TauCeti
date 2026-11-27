/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed
public import TauCeti.RingTheory.Perfectoid.Integral.Basic

import TauCeti.RingTheory.AdicCompletion.Pow

/-!
# Complete absolutely integrally closed domains are integral perfectoid

Let `V` be a domain in which every monic polynomial of positive degree has a root
(`TauCeti.IsAbsolutelyIntegrallyClosed`), and which is `p`-adically complete and separated. Then
`V` is integral perfectoid (`TauCeti.Perfectoid.IsIntegralPerfectoid`). Typical examples are the
`p`-adically complete valuation rings with algebraically closed fraction field, such as the ring
of integers of `ℂ_p` or of the completion of any algebraically closed nonarchimedean field over
`ℚ_p`; with the stability of integral perfectoid rings under products
(`TauCeti.Perfectoid.IsIntegralPerfectoid.pi`), so is every product of such rings. On these
products, which serve as test objects for `p`-adic comparison theorems, Fontaine's map
`θ : W(V♭) → V` is therefore surjective with principal kernel, and tilting is fully faithful.

If `p = 0` in `V`, then `V` has characteristic `p`, its Frobenius is injective because `V` is a
domain, and surjective because `X ^ p - x` has a root; so `V` is perfect, and perfect rings are
integral perfectoid (`TauCeti.Perfectoid.IsIntegralPerfectoid.of_perfectRing`). Otherwise pick
`π` with `π ^ p = p`. Then `V` is `π`-adically complete, since `(π) ^ p = (p)`, and relative
Frobenius `V ⧸ (π) → V ⧸ (π ^ p)` is bijective: it is onto because every element is a `p`-th
power, and injective because `π ^ p ∣ y ^ p` forces `π ∣ y` in an integrally closed domain. This is
the criterion of Bhatt–Morrow–Scholze
(`TauCeti.Perfectoid.IsIntegralPerfectoid.of_bijective_frobeniusModPow`).

## Main results

* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_isAbsolutelyIntegrallyClosed`: a `p`-adically
  complete absolutely integrally closed domain is integral perfectoid.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.10.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/PadicComparison/Descent/TestCovers.lean`, where products of `p`-adically complete
  absolutely integrally closed valuation rings with `p ≠ 0` are the `p`-adic tests; Apache 2.0,
  Copyright 2026 Anthropic, PBC.
-/

public section

open Ideal
open scoped nonZeroDivisors

namespace TauCeti.Perfectoid.IsIntegralPerfectoid

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [CommRing V] [IsDomain V]
  [IsAbsolutelyIntegrallyClosed V] [IsAdicComplete (span {(p : V)}) V]

/-- A `p`-th root `π` of a nonzero `p` in a `p`-adically complete absolutely integrally closed
domain satisfies the hypotheses of the relative Frobenius criterion `of_bijective_frobeniusModPow`.
-/
private theorem of_pow_eq_natCast {π : V} (hπ : π ^ p = p) (hp0 : (p : V) ≠ 0) :
    IsIntegralPerfectoid p V := by
  have hdvd : π ^ p ∣ (p : V) := hπ ▸ dvd_rfl
  -- `(π) ^ p = (p)` and `p ∈ (π)`, so the `π`-adic and `p`-adic topologies agree.
  have : IsAdicComplete (span {π}) V :=
    .of_pow_le_of_pow_le (I := span {(p : V)}) (k := p) (l := 1)
      (by rw [span_singleton_pow, hπ])
      (by
        rw [pow_one, span_singleton_le_span_singleton]
        exact (dvd_pow_self π hp.out.ne_zero).trans hdvd)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hp0 (hπ.symm.trans (zero_pow hp.out.ne_zero))
  refine of_bijective_frobeniusModPow (hdvd := hdvd) (mem_nonZeroDivisors_of_ne_zero hπ0)
    ⟨(frobeniusModPow_injective_iff hdvd).mpr fun y ↦
      (IsIntegrallyClosed.pow_dvd_pow_iff hp.out.ne_zero).mp,
    (frobeniusModPow_surjective_iff hdvd).mpr fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := IsAbsolutelyIntegrallyClosed.exists_pow_nat_eq x hp.out.pos
  exact ⟨y, by rw [hy, sub_self]; exact dvd_zero _⟩

variable (p V) in
/-- **A `p`-adically complete absolutely integrally closed domain is integral perfectoid.** If
`p ≠ 0`, a `p`-th root `π` of `p` makes `V` `π`-adically complete with bijective relative Frobenius
`V ⧸ (π) → V ⧸ (π ^ p)`; if `p = 0`, then `V` is a perfect ring of characteristic `p`. -/
instance (priority := 100) of_isAbsolutelyIntegrallyClosed : IsIntegralPerfectoid p V := by
  by_cases hp0 : (p : V) = 0
  · have : CharP V p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0
    have : PerfectRing V p := .ofSurjective V p fun x ↦
      IsAbsolutelyIntegrallyClosed.exists_pow_nat_eq x hp.out.pos
    infer_instance
  · obtain ⟨π, hπ⟩ := IsAbsolutelyIntegrallyClosed.exists_pow_nat_eq (p : V) hp.out.pos
    exact of_pow_eq_natCast hπ hp0

end TauCeti.Perfectoid.IsIntegralPerfectoid
