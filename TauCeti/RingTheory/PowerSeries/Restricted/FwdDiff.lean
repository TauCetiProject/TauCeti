/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import TauCeti.RingTheory.PowerSeries.EvalAt
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Forward differences of restricted power series

Let `f = ∑ aₘ Xᵐ` be a power series restricted at a radius `c`, so that `f` converges on the closed
disc `‖y‖ ≤ c` of a complete ultrametric normed commutative ring `A` with `‖1‖ = 1`. For a point
`x` and a step `h` in that disc, the forward differences
`Δₕᵏ f(x) = ∑ᵢ (-1)ᵏ⁻ⁱ C(k, i) f(x + i h)` satisfy the **finite-difference coefficient bound**

```text
‖Δₕᵏ f(x)‖ cᵏ ≤ ‖k!‖ ‖h‖ᵏ ‖f‖_c.
```

The factor `‖k!‖` comes from the divisibility of the forward differences of the monomials by
`k!` (`TauCeti.fwdDiff_iter_pow_eq_sum`), which bounds their forward differences termwise
(`TauCeti.norm_fwdDiff_iter_pow_mul_pow_le`). So over a normed field containing `ℚ_p` the Newton
interpolation coefficients `Δₕᵏ f(x) / k!` of `f` along the progression `x + i h` are bounded by
`‖f‖_c (‖h‖ / c)ᵏ`. For a step of norm one this is the bound `‖f‖_c / cᵏ` satisfied by the Hasse
derivatives `(D⁽ᵏ⁾ f)(x)`, the coefficients of the Taylor expansion of `f` at `x`
(`PowerSeries.norm_evalAt_hasseDeriv_mul_pow_le_gaussNorm`).

Combined with the Newton forward-difference formula `f(x + n h) = ∑ₖ C(n, k) Δₕᵏ f(x)`, this gives
the **finite-difference extrapolation estimate**: if `‖f(x + i h)‖ ≤ ε` for `i < n`, then

```text
‖f(x + n h)‖ ≤ max ε (‖n!‖ ‖f‖_c (‖h‖ / c)ⁿ).
```

This is the finite-difference counterpart of the Taylor remainder estimate
`PowerSeries.IsRestricted.norm_evalAt_add_le_max`: small values at `n` consecutive points of a
progression, rather than small Hasse derivatives at one point, control the next value. These
are the finite-difference interpolation estimates of the normal-series calculus in Yu's method of
linear forms in `p`-adic logarithms.

## Main results

* `PowerSeries.IsRestricted.hasSum_fwdDiff_iter_evalAt`: termwise differencing of `f`.
* `PowerSeries.IsRestricted.norm_fwdDiff_iter_evalAt_mul_pow_le`: the finite-difference
  coefficient bound.
* `PowerSeries.IsRestricted.norm_evalAt_add_nsmul_le_max`: the finite-difference extrapolation
  estimate.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
-/

public section

open Finset
open scoped fwdDiff

namespace PowerSeries

open TauCeti.PowerSeries

section NormedRing

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
  [IsUltrametricDist A] [CompleteSpace A] {c : ℝ} {f : R⟦X⟧} {h x : A}

/-- **Termwise differencing of a restricted series.** In a complete ultrametric normed algebra,
for a series `f = ∑ aₘ Xᵐ` restricted at the radius `c` and a point `x` and a step `h` with
`‖x‖ ≤ c` and `‖h‖ ≤ c`, the series `∑ aₘ Δₕᵏ (y ↦ yᵐ)(x)` converges to `Δₕᵏ f(x)`. -/
theorem IsRestricted.hasSum_fwdDiff_iter_evalAt (hf : f.IsRestricted c) (hh : ‖h‖ ≤ c)
    (hx : ‖x‖ ≤ c) (k : ℕ) :
    HasSum (fun m ↦ coeff m f • Δ_[h]^[k] (fun y : A ↦ y ^ m) x)
      (Δ_[h]^[k] (fun y ↦ f.evalAt y) x) := by
  have hshift (i : ℕ) : ‖x + i • h‖ ≤ c :=
    (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hx ((IsUltrametricDist.norm_nsmul_le _ _).trans hh))
  simp only [fwdDiff_iter_eq_sum_shift, smul_sum]
  refine hasSum_sum fun i _ ↦ ?_
  simpa only [smul_comm (coeff _ f)] using
    (hf.hasSum_evalAt (hshift i)).const_smul ((-1) ^ (k - i) * (k.choose i : ℤ))

end NormedRing

section NormedCommRing

variable {R A : Type*} [NormedCommRing R] [NormedCommRing A] [Algebra R A] [IsBoundedSMul R A]
  [NormOneClass A] [IsUltrametricDist A] [CompleteSpace A] {c : ℝ} {f : R⟦X⟧} {h x : A}

/-- **The finite-difference coefficient bound.** In a complete ultrametric normed commutative
algebra with `‖1‖ = 1`, for a series `f` restricted at the radius `c` and a point `x` and a step
`h` with `‖x‖ ≤ c` and `‖h‖ ≤ c`,

```text
‖Δₕᵏ f(x)‖ cᵏ ≤ ‖k!‖ ‖h‖ᵏ ‖f‖_c.
``` -/
theorem IsRestricted.norm_fwdDiff_iter_evalAt_mul_pow_le (hf : f.IsRestricted c) (hh : ‖h‖ ≤ c)
    (hx : ‖x‖ ≤ c) (k : ℕ) :
    ‖Δ_[h]^[k] (fun y ↦ f.evalAt y) x‖ * c ^ k ≤
      ‖(k.factorial : A)‖ * ‖h‖ ^ k * f.gaussNorm norm c := by
  have hc : 0 ≤ c := (norm_nonneg h).trans hh
  have hG : 0 ≤ f.gaussNorm norm c := gaussNorm_nonneg _ _ f fun _ ↦ norm_nonneg _
  rcases (pow_nonneg hc k).eq_or_lt with hck | hck
  · rw [← hck, mul_zero]
    positivity
  rw [← le_div_iff₀ hck, ← (hf.hasSum_fwdDiff_iter_evalAt hh hx k).tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun m ↦ ?_
  rw [le_div_iff₀ hck]
  calc ‖coeff m f • Δ_[h]^[k] (fun y : A ↦ y ^ m) x‖ * c ^ k
      ≤ ‖coeff m f‖ * (‖Δ_[h]^[k] (fun y : A ↦ y ^ m) x‖ * c ^ k) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (norm_smul_le _ _) (by positivity)
    _ ≤ ‖coeff m f‖ * (‖(k.factorial : A)‖ * ‖h‖ ^ k * c ^ m) :=
        mul_le_mul_of_nonneg_left (TauCeti.norm_fwdDiff_iter_pow_mul_pow_le hh hx k m)
          (norm_nonneg _)
    _ = ‖(k.factorial : A)‖ * ‖h‖ ^ k * (‖coeff m f‖ * c ^ m) := by ring
    _ ≤ ‖(k.factorial : A)‖ * ‖h‖ ^ k * f.gaussNorm norm c :=
        mul_le_mul_of_nonneg_left (le_gaussNorm _ _ f (hasGaussNorm_of_isRestricted hf) m)
          (by positivity)

/-- **The finite-difference extrapolation estimate.** In a complete ultrametric normed commutative
algebra with `‖1‖ = 1`, let `f` be restricted at a radius `c > 0` and let `‖x‖ ≤ c`, `‖h‖ ≤ c`.
If `ε` bounds the values `‖f(x + i h)‖` for `i < n`, then

```text
‖f(x + n h)‖ ≤ max ε (‖n!‖ ‖f‖_c (‖h‖ / c) ^ n).
```

For `ε = 0` this bounds `f` at the next point of a progression on which it vanishes. -/
theorem IsRestricted.norm_evalAt_add_nsmul_le_max (hf : f.IsRestricted c) (hc : 0 < c)
    (hh : ‖h‖ ≤ c) (hx : ‖x‖ ≤ c) {n : ℕ} {ε : ℝ}
    (hε : ∀ i < n, ‖f.evalAt (x + i • h)‖ ≤ ε) :
    ‖f.evalAt (x + n • h)‖ ≤
      max ε (‖(n.factorial : A)‖ * f.gaussNorm norm c * (‖h‖ / c) ^ n) := by
  have hG : 0 ≤ f.gaussNorm norm c := gaussNorm_nonneg _ _ f fun _ ↦ norm_nonneg _
  -- the differences of order `k < n` only involve the values at `x + i • h`, `i < n`
  have hlow (k : ℕ) (hk : k < n) : ‖Δ_[h]^[k] (fun y ↦ f.evalAt y) x‖ ≤ ε := by
    rw [fwdDiff_iter_eq_sum_shift]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      ((norm_nonneg _).trans (hε 0 (by omega))) fun i hi ↦
        (IsUltrametricDist.norm_zsmul_le _ _).trans (hε i ?_)
    have := mem_range.mp hi
    omega
  rw [shift_eq_sum_fwdDiff_iter h (fun y ↦ f.evalAt y) n x, sum_range_succ, Nat.choose_self,
    one_smul]
  set B := ‖(n.factorial : A)‖ * f.gaussNorm norm c * (‖h‖ / c) ^ n
  have hB : 0 ≤ B := by positivity
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (le_max_of_le_right ?_))
  · rcases n.eq_zero_or_pos with rfl | hn
    · simpa using le_max_of_le_right hB
    refine le_max_of_le_left (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      ((norm_nonneg _).trans (hε 0 hn)) fun k hk ↦ ?_)
    exact (IsUltrametricDist.norm_nsmul_le _ _).trans (hlow k (mem_range.mp hk))
  · rw [show B = ‖(n.factorial : A)‖ * ‖h‖ ^ n * f.gaussNorm norm c / c ^ n by
      simp only [B, div_pow]; ring, le_div_iff₀ (by positivity)]
    exact hf.norm_fwdDiff_iter_evalAt_mul_pow_le hh hx n

end NormedCommRing

end PowerSeries
