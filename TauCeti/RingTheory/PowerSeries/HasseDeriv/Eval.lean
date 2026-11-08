/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.GaussNorm
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Values of Hasse derivatives of restricted power series

Over a complete ultrametric normed commutative ring `R`, a series `q` restricted at a radius `c`
and all its Hasse derivatives `D⁽ᵗ⁾ q` can be evaluated at every point `b` with `‖b‖ ≤ c` of a
complete ultrametric normed `R`-algebra, and evaluation is a ring homomorphism on restricted
series. Evaluating the formal Leibniz rule `PowerSeries.hasseDeriv_succ_X_sub_C_mul` therefore
gives

```text
(D⁽ᵗ⁺¹⁾ ((X - a) * q))(b) = (b - a) * (D⁽ᵗ⁺¹⁾ q)(b) + (D⁽ᵗ⁾ q)(b).
```

This is how vanishing conditions on the Hasse derivatives of `(X - a) * q` pass to `q`, as in the
Schwarz lemma `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_prod`. Evaluating the
composition rule `D⁽ᵗ⁾ ∘ D⁽ᵏ⁾ = (t + k).choose t • D⁽ᵗ⁺ᵏ⁾` likewise shows that `D⁽ᵏ⁾ q` vanishes to
order `T - k` wherever `q` vanishes to order `T`.

The values of Hasse derivatives are also controlled by the coefficients of `q`: if `ε ≥ 0` bounds
the weighted coefficient norms `‖qₖ‖ cᵏ` in every degree `k ≥ n`, then `‖(D⁽ⁿ⁾ q)(a)‖ cⁿ ≤ ε` at
every `a` with `‖a‖ ≤ c`. This needs neither completeness nor `‖1‖ = 1`.

## Main results

* `PowerSeries.norm_evalAt_hasseDeriv_mul_pow_le_of_forall`: a bound on the weighted coefficients
  of `q` in degrees `≥ n` bounds `‖(D⁽ⁿ⁾ q)(a)‖ cⁿ`.
* `PowerSeries.IsRestricted.evalAt_hasseDeriv_succ_X_sub_C_mul`: the evaluated Leibniz rule for
  `(X - a) * q`.
* `PowerSeries.IsRestricted.evalAt_hasseDeriv_hasseDeriv`: the evaluated composition rule
  `(D⁽ᵗ⁾ (D⁽ᵏ⁾ q))(b) = (t + k).choose t • (D⁽ᵗ⁺ᵏ⁾ q)(b)`.
-/

public section

open TauCeti.PowerSeries

namespace PowerSeries

section Bound

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ} {q : R⟦X⟧} {a : R}

/-- If `ε ≥ 0` bounds the weighted coefficient norms `‖qₖ‖ cᵏ` of `q` in every degree `k ≥ n`,
then it bounds `‖(D⁽ⁿ⁾ q)(a)‖ cⁿ` at every point `a` with `‖a‖ ≤ c`. -/
theorem norm_evalAt_hasseDeriv_mul_pow_le_of_forall (hc : 0 < c) (ha : ‖a‖ ≤ c)
    {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) (h : ∀ m, ‖coeff (m + n) q‖ * c ^ (m + n) ≤ ε) :
    ‖(hasseDeriv n q).evalAt a‖ * c ^ n ≤ ε := by
  have hcn : 0 < c ^ n := pow_pos hc n
  rw [← le_div_iff₀ hcn, evalAt_def]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun m ↦ ?_
  rw [smul_eq_mul, le_div_iff₀ hcn]
  calc ‖coeff m (hasseDeriv n q) * a ^ m‖ * c ^ n ≤ ‖coeff (m + n) q‖ * c ^ m * c ^ n := by
        gcongr
        exact (TauCeti.norm_mul_pow_le _ a m).trans
          (mul_le_mul (norm_coeff_hasseDeriv_le q n m) (by gcongr) (by positivity) (norm_nonneg _))
    _ = ‖coeff (m + n) q‖ * c ^ (m + n) := by ring
    _ ≤ ε := h m

end Bound

variable {R A : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormedRing A] [Algebra R A]
  [IsBoundedSMul R A] [IsUltrametricDist A] [CompleteSpace A] {c : ℝ} {q : R⟦X⟧}

/-- **Evaluated Leibniz rule for `(X - a) * q`.** At a point `b` with `‖b‖ ≤ c`, the Hasse
derivative of order `t + 1` of `(X - a) * q`, for `q` restricted at `c`, takes the value
`(b - a) * (D⁽ᵗ⁺¹⁾ q)(b) + (D⁽ᵗ⁾ q)(b)`. -/
theorem IsRestricted.evalAt_hasseDeriv_succ_X_sub_C_mul (hq : q.IsRestricted c) (a : R) {b : A}
    (hb : ‖b‖ ≤ c) (t : ℕ) :
    (PowerSeries.hasseDeriv (t + 1) ((X - C a) * q)).evalAt b =
      (b - algebraMap R A a) * (PowerSeries.hasseDeriv (t + 1) q).evalAt b +
        (PowerSeries.hasseDeriv t q).evalAt b := by
  have hX := isRestricted_X_sub_C (c := c) a
  rw [hasseDeriv_succ_X_sub_C_mul, IsRestricted.evalAt_add (hX.mul (hq.hasseDeriv _))
    (hq.hasseDeriv _) hb, hX.evalAt_mul (hq.hasseDeriv _) hb, evalAt_X_sub_C]

/-- **Evaluated composition of Hasse derivatives.** At a point `b` with `‖b‖ ≤ c`, for `q`
restricted at `c`, `(D⁽ᵗ⁾ (D⁽ᵏ⁾ q))(b) = (t + k).choose t • (D⁽ᵗ⁺ᵏ⁾ q)(b)`. In particular, if `q`
vanishes at `b` to order `T`, then `D⁽ᵏ⁾ q` vanishes at `b` to order `T - k`. -/
theorem IsRestricted.evalAt_hasseDeriv_hasseDeriv (hq : q.IsRestricted c) {b : A} (hb : ‖b‖ ≤ c)
    (t k : ℕ) :
    (PowerSeries.hasseDeriv t (PowerSeries.hasseDeriv k q)).evalAt b =
      (t + k).choose t • (PowerSeries.hasseDeriv (t + k) q).evalAt b := by
  rw [← LinearMap.comp_apply, hasseDeriv_comp, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul R,
    (hq.hasseDeriv _).evalAt_smul _ hb, Nat.cast_smul_eq_nsmul]

end PowerSeries
