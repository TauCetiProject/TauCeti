/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# The Weierstrass division estimate for restricted power series

Let `f` be a restricted power series which is distinguished of degree `s` at the radius `c`: its
Gauss norm is attained in degree `s`, and every later coefficient is strictly smaller. A
*Weierstrass division* of a restricted series by `f` is a decomposition

```text
q * f + r,    q restricted,    r vanishing in every degree ≥ s
```

— that is, `r` is a polynomial of degree less than `s`. This file proves the two facts about such a
decomposition which need no completeness: the norm identity

```text
‖q * f + r‖ = max (‖q‖ * ‖f‖) ‖r‖
```

for the Gauss norm at `c`, and, as a consequence, that `q` and `r` are determined by the series they
sum to. Existence of a Weierstrass division is a separate statement; its proof needs the coefficient
ring to be a complete nonarchimedean field, and it is not carried out here.

The distinguished degree is what drives the identity. Choosing a degree `n` in which `q` attains its
own Gauss norm, the coefficient of `q * f` in degree `n + s` is dominated by the single convolution
term `qₙ · f_s`, whose weighted norm is `‖q‖ * ‖f‖`; and `r` cannot interfere in that degree because
`n + s ≥ s`. So the Gauss norm of the sum is at least `‖q‖ * ‖f‖`, and then at least `‖r‖` as well,
while the reverse inequality is the nonarchimedean bound on a sum.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.gaussNorm_mul_add_eq_max`: the norm identity.
* `TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_add_eq_mul_add`: the quotient and the
  remainder of a Weierstrass division are unique.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2, whose norm identity and
  uniqueness assertion these are; the statements there are for the unit radius.

Mathlib's `PowerSeries.IsWeierstrassDivisionAt` is a different division theorem, for a different
notion of divisor: there the divisor is measured by the order of its image modulo an ideal `I` of an
`I`-adically complete coefficient ring, and both dividend and quotient range over all of `R⟦X⟧`.
Here the divisor is measured by a Gauss norm at a radius, and dividend and quotient are restricted
at that radius. Neither statement implies the other.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedRing R] {c : ℝ} {s : ℕ} {f q r : PowerSeries R}

variable [IsUltrametricDist R] [NormMulClass R]

/-- **The Weierstrass lower bound for the quotient.** In a decomposition `q * f + r` by a
distinguished series `f` of degree `s`, with `r` vanishing in every degree `≥ s`, the Gauss norm of
the sum is at least the Gauss norm of `q * f`.

The dominant coefficient of `q * f` sits in degree `n + s`, where `n` is a degree in which `q`
attains its Gauss norm, and `r` vanishes there. -/
theorem IsDistinguished.le_gaussNorm_mul_add (hf : IsDistinguished c s f) (hc : 0 < c)
    (hfr : f.IsRestricted c) (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    q.gaussNorm norm c * f.gaussNorm norm c ≤ (q * f + r).gaussNorm norm c := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0), zero_mul]
    exact PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg
  obtain ⟨n, hn⟩ := exists_isDistinguished hc hq hq0
  have hsum : (q * f + r).IsRestricted c :=
    PowerSeries.isRestricted.add c (PowerSeries.isRestricted.mul c hq hfr)
      (isRestricted_of_forall_coeff_eq_zero hr)
  have hcoeff : (q * f + r).coeff (n + s) = (q * f).coeff (n + s) := by
    rw [map_add, hr (n + s) (Nat.le_add_left s n), add_zero]
  calc q.gaussNorm norm c * f.gaussNorm norm c
      = ‖(q * f + r).coeff (n + s)‖ * c ^ (n + s) := by
        rw [hcoeff]
        exact (hn.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hf hc
          (hasGaussNorm_of_isRestricted hq) (hasGaussNorm_of_isRestricted hfr)).symm
    _ ≤ (q * f + r).gaussNorm norm c :=
        PowerSeries.le_gaussNorm norm c _ (hasGaussNorm_of_isRestricted hsum) _

/-- **The Weierstrass lower bound for the remainder.** In a decomposition `q * f + r` by a
distinguished series `f` of degree `s`, with `r` vanishing in every degree `≥ s`, the Gauss norm of
the sum is at least the Gauss norm of `r`.

Each coefficient of `r` is the difference of the corresponding coefficients of `q * f + r` and of
`q * f`, so it is bounded by the larger of the two Gauss norms; and the Gauss norm of `q * f` is
already bounded by that of the sum. -/
theorem IsDistinguished.gaussNorm_le_gaussNorm_mul_add (hf : IsDistinguished c s f) (hc : 0 < c)
    (hfr : f.IsRestricted c) (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    r.gaussNorm norm c ≤ (q * f + r).gaussNorm norm c := by
  have hbqf := hasGaussNorm_of_isRestricted (PowerSeries.isRestricted.mul c hq hfr)
  have hbsum := hasGaussNorm_of_isRestricted (PowerSeries.isRestricted.add c
    (PowerSeries.isRestricted.mul c hq hfr) (isRestricted_of_forall_coeff_eq_zero hr))
  have hqf : (q * f).gaussNorm norm c ≤ (q * f + r).gaussNorm norm c :=
    (gaussNorm_mul_of_isRestricted hc hq hfr).le.trans
      (hf.le_gaussNorm_mul_add hc hfr hq hr)
  rw [PowerSeries.gaussNorm_eq]
  refine ciSup_le fun m ↦ ?_
  have hsub : ‖r.coeff m‖ ≤ max ‖(q * f + r).coeff m‖ ‖(q * f).coeff m‖ := by
    have hrw : r.coeff m = (q * f + r).coeff m + -((q * f).coeff m) := by
      rw [map_add]; abel
    rw [hrw]
    simpa only [norm_neg] using
      IsUltrametricDist.isNonarchimedean_norm ((q * f + r).coeff m) (-((q * f).coeff m))
  calc ‖r.coeff m‖ * c ^ m
      ≤ max ‖(q * f + r).coeff m‖ ‖(q * f).coeff m‖ * c ^ m :=
        mul_le_mul_of_nonneg_right hsub (pow_nonneg hc.le m)
    _ = max (‖(q * f + r).coeff m‖ * c ^ m) (‖(q * f).coeff m‖ * c ^ m) :=
        max_mul_of_nonneg _ _ (pow_nonneg hc.le m)
    _ ≤ (q * f + r).gaussNorm norm c :=
        max_le (PowerSeries.le_gaussNorm norm c _ hbsum m)
          ((PowerSeries.le_gaussNorm norm c _ hbqf m).trans hqf)

/-- **The Weierstrass division estimate** (Bosch–Güntzer–Remmert §5.2.1, Theorem 2). If `f` is
restricted and distinguished of degree `s` at the radius `c`, `q` is restricted, and `r` vanishes in
every degree `≥ s`, then

```text
‖q * f + r‖ = max (‖q‖ * ‖f‖) ‖r‖
```

for the Gauss norm at `c`. No cancellation occurs in a Weierstrass decomposition. -/
theorem IsDistinguished.gaussNorm_mul_add_eq_max (hf : IsDistinguished c s f) (hc : 0 < c)
    (hfr : f.IsRestricted c) (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    (q * f + r).gaussNorm norm c =
      max (q.gaussNorm norm c * f.gaussNorm norm c) (r.gaussNorm norm c) := by
  refine le_antisymm ?_ (max_le (hf.le_gaussNorm_mul_add hc hfr hq hr)
    (hf.gaussNorm_le_gaussNorm_mul_add hc hfr hq hr))
  rw [← gaussNorm_mul_of_isRestricted hc hq hfr]
  exact PowerSeries.gaussNorm_add_le_max norm c (q * f) r hc.le norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm
    (hasGaussNorm_of_isRestricted (PowerSeries.isRestricted.mul c hq hfr))
    (hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero hr))

/-- **Uniqueness in Weierstrass division** (Bosch–Güntzer–Remmert §5.2.1, Theorem 2). A restricted
series has at most one decomposition `q * f + r` with `q` restricted and `r` vanishing in every
degree `≥ s`, for `f` restricted and distinguished of degree `s`. -/
theorem IsDistinguished.eq_and_eq_of_mul_add_eq_mul_add (hf : IsDistinguished c s f) (hc : 0 < c)
    (hfr : f.IsRestricted c) {q' r' : PowerSeries R} (hq : q.IsRestricted c)
    (hq' : q'.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0)
    (hr' : ∀ m, s ≤ m → r'.coeff m = 0) (h : q * f + r = q' * f + r') :
    q = q' ∧ r = r' := by
  have hqq : (q - q').IsRestricted c := by
    simpa only [sub_eq_add_neg] using
      PowerSeries.isRestricted.add c hq (PowerSeries.isRestricted.neg c hq')
  have hrr : ∀ m, s ≤ m → (r - r').coeff m = 0 := by
    intro m hm
    rw [map_sub, hr m hm, hr' m hm, sub_zero]
  have hzero : (q - q') * f + (r - r') = 0 := by
    rw [sub_mul, sub_add_sub_comm, h, sub_self]
  have hmax : max ((q - q').gaussNorm norm c * f.gaussNorm norm c)
      ((r - r').gaussNorm norm c) = 0 := by
    rw [← hf.gaussNorm_mul_add_eq_max hc hfr hqq hrr, hzero]
    exact PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)
  have hgq : (q - q').gaussNorm norm c = 0 := by
    have hle : (q - q').gaussNorm norm c * f.gaussNorm norm c ≤ 0 := by
      rw [← hmax]; exact le_max_left _ _
    have hmul := le_antisymm hle (mul_nonneg
      (PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
      (PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg))
    exact (mul_eq_zero.mp hmul).resolve_right hf.gaussNorm_pos.ne'
  have hgr : (r - r').gaussNorm norm c = 0 :=
    le_antisymm (by rw [← hmax]; exact le_max_right _ _)
      (PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
  refine ⟨sub_eq_zero.mp ?_, sub_eq_zero.mp ?_⟩
  · exact (PowerSeries.gaussNorm_eq_zero_iff norm c _ norm_zero norm_nonneg
      (fun _ ↦ norm_eq_zero.mp) hc (hasGaussNorm_of_isRestricted hqq)).mp hgq
  · exact (PowerSeries.gaussNorm_eq_zero_iff norm c _ norm_zero norm_nonneg
      (fun _ ↦ norm_eq_zero.mp) hc
      (hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero hrr))).mp hgr

end TauCeti.PowerSeries
