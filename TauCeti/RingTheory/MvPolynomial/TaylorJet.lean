/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import TauCeti.RingTheory.MvPolynomial.LocalOrder
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.MvPolynomial.FirstJet

/-!
# Chinese remainder theorem for multivariate polynomial Taylor jets

This file provides two results on powers of point vanishing ideals and Taylor expansions
(`MvPolynomial.taylor`) of multivariate polynomials:

* `MvPolynomial.aeval_monomial_mem_vanishingIdeal_pow`: substituting polynomials vanishing at `w`
  into a monomial of degree at least `d` produces an element of `vanishingIdeal K {w} ^ d`.
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

/-- If every `φ u` vanishes at `w`, then `aeval φ (monomial γ 1)` lies in
`vanishingIdeal K {w} ^ d` for every `d ≤ γ.degree`. -/
theorem aeval_monomial_mem_vanishingIdeal_pow {K ι : Type*} [Field K] {w : ι → K}
    {φ : ι → MvPolynomial ι K} (hφ : ∀ u : ι, eval w (φ u) = 0) {d : ℕ} {γ : ι →₀ ℕ}
    (hγ : d ≤ γ.degree) : aeval φ (monomial γ (1 : K)) ∈ vanishingIdeal K {w} ^ d := by
  classical
  have h_vars : idealOfVars ι K ≤ (vanishingIdeal K {w}).comap (aeval φ) := by
    simp [Ideal.span_le, hφ, Set.range_subset_iff]
  have h_mem : monomial γ (1 : K) ∈ idealOfVars ι K ^ d :=
    (mem_pow_idealOfVars_iff d _).2 (by simpa)
  exact le_comap_pow (aeval φ) d (pow_right_mono h_vars d h_mem)

/-- Chinese remainder theorem for polynomial Taylor jets: at finitely many distinct points `z t`
over a field `K`, the Taylor coefficients `(taylor (z t) p).coeff γ` on any finite exponent set
`Γ` can be prescribed arbitrarily. -/
theorem exists_forall_coeff_taylor_eq {K ι S : Type*} [Field K] [Finite S] {z : S → ι → K}
    (hz_inj : z.Injective) (Γ : Finset (ι →₀ ℕ)) (y : S × Γ → K) :
    ∃ p : MvPolynomial ι K, ∀ (t : S) (γ : Γ), (taylor (z t) p).coeff γ = y (t, γ) := by
  classical
  have := Fintype.ofFinite S
  let d : ℕ := Γ.sup Finsupp.degree + 1
  have h_ker (w : ι → K) : vanishingIdeal K {w} = RingHom.ker (eval w) := by
    ext p
    simp
  have h_coprime : Pairwise (Function.onFun IsCoprime fun t : S ↦ vanishingIdeal K {z t} ^ d) :=
    fun t t' h_ne ↦ .pow (by simpa only [h_ker] using TauCeti.isCoprime_ker_eval (hz_inj.ne h_ne))
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
