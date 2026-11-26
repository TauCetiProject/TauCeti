/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.LocalOrder
import TauCeti.RingTheory.MvPolynomial.FirstJet
import TauCeti.RingTheory.MvPolynomial.Ideal.Point

/-!
# Chinese remainder theorem for multivariate polynomial Taylor jets

This file proves a Chinese remainder theorem for Taylor expansions (`MvPolynomial.taylor`) of
multivariate polynomials at finitely many rational points.

## Main results

* `MvPolynomial.exists_forall_coeff_taylor_eq`: Chinese remainder theorem for polynomial jets —
  at finitely many distinct points `z t : ι → K` over a field `K`, the Taylor coefficients
  `(taylor (z t) p).coeff γ` on any finite exponent set `Γ` can be prescribed arbitrarily.

## References

* L. Alpöge and L. Sernau, grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0,
  Copyright 2026 Anthropic, PBC), `src/Lib/General/Algebra/MultivariatePolynomials.lean`
  (`New.exists_le_weight_of_mem_vanishingIdeal_pow`).
-/

public section

open Ideal

namespace MvPolynomial

/-- Chinese remainder theorem for polynomial Taylor jets: at finitely many distinct points `z t`
over a field `K`, the Taylor coefficients `(taylor (z t) p).coeff γ` on any finite exponent set
`Γ` can be prescribed arbitrarily. -/
theorem exists_forall_coeff_taylor_eq {K ι S : Type*} [Field K] [Finite S] {z : S → ι → K}
    (hz_inj : z.Injective) (Γ : Finset (ι →₀ ℕ)) (y : S × Γ → K) :
    ∃ p : MvPolynomial ι K, ∀ (t : S) (γ : Γ), (taylor (z t) p).coeff γ = y (t, γ) := by
  classical
  have := Fintype.ofFinite S
  let d : ℕ := Γ.sup Finsupp.degree + 1
  have h_coprime : Pairwise (Function.onFun IsCoprime fun t : S ↦ vanishingIdeal K {z t} ^ d) :=
    fun t t' h_ne ↦ .pow (by
      simpa only [vanishingIdeal_singleton_eq_ker_eval] using
        TauCeti.isCoprime_ker_eval (hz_inj.ne h_ne))
  let q (t : S) : MvPolynomial ι K := taylor (-z t) (∑ γ : Γ, monomial γ (y (t, γ)))
  obtain ⟨p, hp⟩ := exists_forall_sub_mem_ideal h_coprime q
  refine ⟨p, fun t γ ↦ ?_⟩
  have h_jet : (taylor (z t) (p - q t)).coeff γ = 0 :=
    le_orderAt_iff.1 ((mem_pow_vanishingIdeal_singleton_iff _ (z t) d).1 (hp t)) γ
      (by exact_mod_cast Nat.lt_succ_of_le (Finset.le_sup γ.property))
  have h_qt : taylor (z t) (q t) = ∑ δ : Γ, monomial δ (y (t, δ)) := by
    simp [q, taylor_taylor]
  simpa [h_qt, coeff_sum, sub_eq_zero] using h_jet

end MvPolynomial
