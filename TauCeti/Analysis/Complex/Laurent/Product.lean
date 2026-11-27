/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.MeromorphicGerm
import TauCeti.RingTheory.LaurentSeries.Multiplication

/-!
# Products of Laurent expansions on small circles

For functions meromorphic at a point, the circle integral giving a coefficient of their
product can be computed from finitely many circle integrals of the factors. The limits
of summation come from lower bounds on the two meromorphic orders. A single choice of
sufficiently small radius works in every degree.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, Chapter 5, §1.3.
-/

public section

open Filter Topology TauCeti TauCeti.meromorphicGerms

/-- On every sufficiently small circle, the Laurent coefficient of degree `n` of a product is
the convolution over `[l, n - r]` for any lower bounds `l` and `r` on the factor orders. -/
theorem MeromorphicAt.eventually_circleLaurentCoeff_mul_eq_sum
    {a : ℂ} {f g : ℂ → ℂ} (hf : MeromorphicAt f a) (hg : MeromorphicAt g a) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ {l r : ℤ}, (l : WithTop ℤ) ≤ meromorphicOrderAt f a →
      (r : WithTop ℤ) ≤ meromorphicOrderAt g a → ∀ n : ℤ,
      circleLaurentCoeff (f * g) a ρ n =
        ∑ i ∈ Finset.Icc l (n - r),
          circleLaurentCoeff f a ρ i * circleLaurentCoeff g a ρ (n - i) := by
  filter_upwards [eventually_coeff_laurentSeries_eq_circleLaurentCoeff (coe_mk f hf),
    eventually_coeff_laurentSeries_eq_circleLaurentCoeff (coe_mk g hg),
    eventually_coeff_laurentSeries_eq_circleLaurentCoeff (coe_mk (f * g) (hf.mul hg))] with
    ρ hρf hρg hρfg l r hl hr n
  rw [← hρfg, mk_mul hf hg, map_mul]
  simp only [← hρf, ← hρg]
  apply LaurentSeries.coeff_mul_eq_sum
  · simpa only [orderTop_laurentSeries, order_mk] using hl
  · simpa only [orderTop_laurentSeries, order_mk] using hr
