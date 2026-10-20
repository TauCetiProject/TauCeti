/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.RingTheory.PowerSeries.Restricted
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.Basic

/-!
# Hasse derivatives of restricted power series

Over an ultrametric (semi)normed ring, a natural-number multiple of an element has at most the
norm of that element. The coefficients of the Hasse derivative `D⁽ᵏ⁾ f` are natural-number
multiples of the coefficients of `f`, shifted down by `k`, so at a radius `c > 0`

```text
‖D⁽ᵏ⁾ f‖_c ≤ c⁻ᵏ ‖f‖_c
```

for the Gauss norms, and `D⁽ᵏ⁾` preserves restrictedness at every radius. Neither a multiplicative
norm nor `‖1‖ = 1` is needed, and the coefficients need not commute. These are the estimates that
make Hasse derivatives act on Tate algebras of closed discs of any positive radius.

## Main results

* `PowerSeries.norm_coeff_hasseDeriv_le`: `‖coeff n (D⁽ᵏ⁾ f)‖ ≤ ‖coeff (n + k) f‖`.
* `PowerSeries.IsRestricted.hasseDeriv`: Hasse derivatives preserve restrictedness.
* `PowerSeries.HasGaussNorm.hasseDeriv` and `PowerSeries.gaussNorm_hasseDeriv_le`: at a positive
  radius `c`, Hasse derivatives preserve bounded weighted coefficients, and
  `gaussNorm c (D⁽ᵏ⁾ f) ≤ c⁻¹ ^ k * gaussNorm c f`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

section SeminormedRing

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R] {c : ℝ} {f : R⟦X⟧}

variable (f) in
/-- Over an ultrametric ring, a coefficient of a Hasse derivative has at most the norm of the
coefficient of `f` it is a multiple of. -/
theorem norm_coeff_hasseDeriv_le (k n : ℕ) : ‖coeff n (hasseDeriv k f)‖ ≤ ‖coeff (n + k) f‖ := by
  rw [coeff_hasseDeriv, ← nsmul_eq_mul]
  exact IsUltrametricDist.norm_nsmul_le _ _

variable (f) in
/-- The weighted coefficient norms of `D⁽ᵏ⁾ f` at a positive radius `c` are bounded by `c⁻ᵏ` times
those of `f`. -/
theorem norm_coeff_hasseDeriv_mul_pow_le (hc : 0 < c) (k n : ℕ) :
    ‖coeff n (hasseDeriv k f)‖ * c ^ n ≤ c⁻¹ ^ k * (‖coeff (n + k) f‖ * c ^ (n + k)) := by
  have hk : c⁻¹ ^ k * (‖coeff (n + k) f‖ * c ^ (n + k)) = ‖coeff (n + k) f‖ * c ^ n := by
    rw [pow_add, inv_pow]
    field_simp
  rw [hk]
  exact mul_le_mul_of_nonneg_right (norm_coeff_hasseDeriv_le f k n) (pow_nonneg hc.le n)

/-- At a positive radius `c`, the weighted coefficient norms of `D⁽ᵏ⁾ f` are bounded by `c⁻ᵏ`
times the Gauss norm of `f`, whenever `f` has bounded weighted coefficient norms. -/
theorem norm_coeff_hasseDeriv_mul_pow_le_gaussNorm (hc : 0 < c) (hf : f.HasGaussNorm norm c)
    (k n : ℕ) : ‖coeff n (hasseDeriv k f)‖ * c ^ n ≤ c⁻¹ ^ k * f.gaussNorm norm c :=
  (norm_coeff_hasseDeriv_mul_pow_le f hc k n).trans <|
    mul_le_mul_of_nonneg_left (le_gaussNorm norm c f hf (n + k)) (by positivity)

/-- At a positive radius, Hasse derivatives preserve boundedness of the weighted coefficient
norms. -/
theorem HasGaussNorm.hasseDeriv (hc : 0 < c) (hf : f.HasGaussNorm norm c) (k : ℕ) :
    (hasseDeriv k f).HasGaussNorm norm c :=
  ⟨c⁻¹ ^ k * f.gaussNorm norm c, Set.forall_mem_range.mpr
    (norm_coeff_hasseDeriv_mul_pow_le_gaussNorm hc hf k)⟩

/-- **The Gauss-norm estimate for Hasse derivatives**: at a radius `c > 0`,
`‖D⁽ᵏ⁾ f‖_c ≤ c⁻ᵏ ‖f‖_c` whenever `f` has bounded weighted coefficient norms. -/
theorem gaussNorm_hasseDeriv_le (hc : 0 < c) (hf : f.HasGaussNorm norm c) (k : ℕ) :
    (hasseDeriv k f).gaussNorm norm c ≤ c⁻¹ ^ k * f.gaussNorm norm c :=
  (gaussNorm_eq norm c _).trans_le <| ciSup_le (norm_coeff_hasseDeriv_mul_pow_le_gaussNorm hc hf k)

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {c : ℝ} {f : R⟦X⟧}

/-- Over an ultrametric normed ring, Hasse derivatives preserve restrictedness at every radius. -/
theorem IsRestricted.hasseDeriv (hf : f.IsRestricted c) (k : ℕ) :
    (hasseDeriv k f).IsRestricted c := by
  rw [← isRestricted_abs_iff] at hf ⊢
  rw [isRestricted_iff'] at hf ⊢
  rcases (abs_nonneg c).eq_or_lt with hc | hc
  · -- At radius zero every weighted coefficient after the constant one vanishes.
    refine tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    simp [← hc, zero_pow (Nat.one_le_iff_ne_zero.mp hn)]
  · refine squeeze_zero (fun n ↦ by positivity)
      (fun n ↦ norm_coeff_hasseDeriv_mul_pow_le f hc k n) ?_
    simpa using (hf.comp (tendsto_add_atTop_nat k)).const_mul (|c|⁻¹ ^ k)

end NormedRing

end PowerSeries
