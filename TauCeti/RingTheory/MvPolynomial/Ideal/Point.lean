/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nullstellensatz
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Ideals of rational points

For a rational point `a : σ → k` of affine space over a field `k`, the vanishing ideal
`MvPolynomial.vanishingIdeal k {a}` is the kernel of evaluation at `a`, and substituting
polynomials that vanish at `a` into a monomial of total degree at least `d` lands in its `d`-th
power.

## Main results

* `MvPolynomial.vanishingIdeal_singleton_eq_ker_eval`: the vanishing ideal of a rational point is
  the kernel of evaluation at that point.
* `MvPolynomial.aeval_monomial_mem_vanishingIdeal_pow`: substituting polynomials vanishing at `w`
  into a monomial of degree at least `d` produces an element of `vanishingIdeal K {w} ^ d`.

## References

* L. Alpöge and L. Sernau, grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0,
  Copyright 2026 Anthropic, PBC), `src/Lib/General/Algebra/MultivariatePolynomials.lean`
  (`New.exists_le_weight_of_mem_vanishingIdeal_pow`), whose proof uses both facts.
-/

public section

namespace MvPolynomial

/-- The vanishing ideal of a rational point is the kernel of evaluation at that point. -/
theorem vanishingIdeal_singleton_eq_ker_eval {σ k : Type*} [Field k] (a : σ → k) :
    vanishingIdeal k {a} = RingHom.ker (eval a) := by
  ext f
  simp only [mem_vanishingIdeal_singleton_iff, RingHom.mem_ker, aeval_eq_eval]

/-- If every `φ u` vanishes at `w`, then `aeval φ (monomial γ 1)` lies in
`vanishingIdeal K {w} ^ d` for every `d ≤ γ.degree`. -/
theorem aeval_monomial_mem_vanishingIdeal_pow {K ι : Type*} [Field K] {w : ι → K}
    {φ : ι → MvPolynomial ι K} (hφ : ∀ u : ι, eval w (φ u) = 0) {d : ℕ} {γ : ι →₀ ℕ}
    (hγ : d ≤ γ.degree) : aeval φ (monomial γ (1 : K)) ∈ vanishingIdeal K {w} ^ d := by
  have h_vars : idealOfVars ι K ≤ (vanishingIdeal K {w}).comap (aeval φ) := by
    rw [← Ideal.map_le_iff_le_comap, map_aeval_idealOfVars, Ideal.span_le]
    rintro _ ⟨u, rfl⟩
    simpa [mem_vanishingIdeal_singleton_iff] using hφ u
  exact Ideal.le_comap_pow (aeval φ) d
    (Ideal.pow_right_mono h_vars d ((monomial_mem_pow_idealOfVars_iff d γ one_ne_zero).2 hγ))

end MvPolynomial
