/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm.Estimates
public import TauCeti.RingTheory.PowerSeries.MulDistinguished
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Weierstrass division for restricted power series

Let `f` be a power series which is distinguished of degree `s` at the radius `c`: its
positive Gauss norm is attained in degree `s`, and every later weighted coefficient norm is
strictly smaller. A *Weierstrass division* by `f` writes a power series as

```text
q * f + r,    q restricted,    r vanishing in every degree ≥ s
```

— that is, with `r` a polynomial of degree less than `s`. This file first proves the two facts
about such a decomposition which need no completeness: the norm identity

```text
‖q * f + r‖ = max (‖q‖ * ‖f‖) ‖r‖
```

for the Gauss norm at `c`, and, as a consequence, that `q` and `r` are determined by the series
they sum to. Neither needs the norm of the coefficient ring to be multiplicative: it suffices that
multiplication by the coefficient of `f` in degree `s` scales norms exactly. This holds when the
norm is multiplicative, and over a commutative ring when `f` is multiplicatively distinguished
(`TauCeti.PowerSeries.IsMulDistinguished`), which is the form the estimate takes for divisors over
Banach rings.

It then proves existence over a complete ultrametric normed commutative ring, for a restricted
divisor `g` which is multiplicatively distinguished. The norm of the coefficient ring need not be
multiplicative, and the ring may have nilpotents, as coefficient algebras of families do. The unit
condition on the distinguished coefficient is what makes the polynomial part `g⁻ = g.trunc (s + 1)`
a unit multiple of a monic polynomial, so that a truncation of the dividend can be divided by it as
an ordinary division of polynomials. Since that coefficient is a multiplicative unit, the norm
identity bounds the polynomial quotient and remainder by the dividend. The division leaves a defect
built from the tail `g - g⁻`, whose Gauss norm is strictly smaller than that of `g`; bounding its
product with the quotient needs only submultiplicativity of the Gauss norm. Each step therefore
shrinks the dividend by a fixed factor, and the resulting series of quotients and remainders
converges coefficientwise. Over a ring with multiplicative norm a distinguished series is
multiplicatively distinguished as soon as its distinguished coefficient is a unit, which is
automatic over a field.

The coefficient ring is allowed to be a ring, rather than a field, for the noetherianity of Tate
algebras in several variables: the Tate algebra in `n` variables is a ring of restricted series in
one variable over the Tate algebra in `n - 1` variables, whose Gauss norm is multiplicative, and
Bosch–Güntzer–Remmert divide there by series whose dominant coefficient is a unit.

Since the quotient and the remainder are themselves restricted at `c`, the division is also
recorded inside the subring `PowerSeries.IsRestricted.subring c` of `R⟦X⟧`, which is the form
its ideal-theoretic consequences use.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.gaussNorm_mul_add_eq_max` and
  `TauCeti.PowerSeries.IsMulDistinguished.gaussNorm_mul_add_eq_max`: the norm identity, for a
  divisor whose distinguished coefficient scales norms, and for a multiplicatively distinguished
  divisor over a commutative ring.
* `TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_add_eq_mul_add` and
  `TauCeti.PowerSeries.IsMulDistinguished.eq_and_eq_of_mul_add_eq_mul_add`: the quotient and the
  remainder of a Weierstrass division are unique.
* `TauCeti.PowerSeries.IsMulDistinguished.exists_mul_add_eq` and
  `TauCeti.PowerSeries.IsMulDistinguished.existsUnique_mul_add_eq`: over a complete ultrametric
  normed commutative ring, every restricted power series has a unique Weierstrass division by a
  restricted multiplicatively distinguished series.
* `TauCeti.PowerSeries.IsMulDistinguished.exists_mul_add_eq_subring` and
  `TauCeti.PowerSeries.IsMulDistinguished.existsUnique_mul_add_eq_subring`: the same division read
  inside the subring `PowerSeries.IsRestricted.subring c` of series restricted at `c`, where
  quotient and remainder are elements of that subring.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2, whose norm identity,
  uniqueness assertion and existence assertion these are; the statements there are for the unit
  radius.
* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Lemma 1.26 and Proposition 1.27, for division by a
  multiplicatively distinguished series over a Banach ring.

Mathlib's `PowerSeries.IsWeierstrassDivisionAt` is a different division theorem, for a different
notion of divisor: there the divisor is measured by the order of its image modulo an ideal `I` of an
`I`-adically complete coefficient ring, and both dividend and quotient range over all of `R⟦X⟧`.
Here the divisor is measured by a Gauss norm at a radius, and the quotient is restricted at that
radius; the resulting series `q * f + r` need not be restricted. Neither statement implies the
other.
-/

public section

namespace TauCeti.PowerSeries

section NormedRing

variable {R : Type*} [NormedRing R] {c : ℝ} {s : ℕ} {f q r : PowerSeries R}

variable [IsUltrametricDist R]

/-- **The Weierstrass lower bound for the quotient.** In a decomposition `q * f + r` by a
distinguished series `f` of degree `s`, with `r` vanishing in every degree `≥ s`, the Gauss norm of
the sum is at least the product of the Gauss norms of `q` and `f`, provided right multiplication by
the coefficient of `f` in degree `s` scales norms exactly. -/
theorem IsDistinguished.le_gaussNorm_mul_add (hf : IsDistinguished c s f) (hc : 0 < c)
    (hmul : ∀ x, ‖x * f.coeff s‖ = ‖x‖ * ‖f.coeff s‖)
    (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    q.gaussNorm norm c * f.gaussNorm norm c ≤ (q * f + r).gaussNorm norm c := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0), zero_mul]
    exact PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg
  obtain ⟨n, hn⟩ := exists_isDistinguished hc hq hq0
  -- Explicit boundedness types fix the coefficient ring before inferring the seminormed norm.
  have hbqf : (q * f).HasGaussNorm norm c :=
    hasGaussNorm_mul hc.le (hasGaussNorm_of_isRestricted hq) hf.hasGaussNorm
  have hbr : r.HasGaussNorm norm c :=
    hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero hr)
  have hsum : (q * f + r).HasGaussNorm norm c := hasGaussNorm_add hc.le hbqf hbr
  have hcoeff : (q * f + r).coeff (n + s) = (q * f).coeff (n + s) := by
    rw [map_add, hr (n + s) (Nat.le_add_left s n), add_zero]
  calc q.gaussNorm norm c * f.gaussNorm norm c
      = ‖(q * f + r).coeff (n + s)‖ * c ^ (n + s) := by
        rw [hcoeff]
        exact (hn.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hf hc (hmul _)).symm
    _ ≤ (q * f + r).gaussNorm norm c :=
        PowerSeries.le_gaussNorm norm c _ hsum _

/-- **The Weierstrass lower bound for the remainder.** In a decomposition `q * f + r` by a
distinguished series `f` of degree `s`, with `r` vanishing in every degree `≥ s`, the Gauss norm of
the sum is at least the Gauss norm of `r`, provided right multiplication by the coefficient of `f`
in degree `s` scales norms exactly. -/
theorem IsDistinguished.gaussNorm_le_gaussNorm_mul_add (hf : IsDistinguished c s f) (hc : 0 < c)
    (hmul : ∀ x, ‖x * f.coeff s‖ = ‖x‖ * ‖f.coeff s‖)
    (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    r.gaussNorm norm c ≤ (q * f + r).gaussNorm norm c := by
  have hbqf : (q * f).HasGaussNorm norm c :=
    hasGaussNorm_mul hc.le (hasGaussNorm_of_isRestricted hq) hf.hasGaussNorm
  have hbr : r.HasGaussNorm norm c :=
    hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero hr)
  have hbsum : (q * f + r).HasGaussNorm norm c := hasGaussNorm_add hc.le hbqf hbr
  have hqf : (q * f).gaussNorm norm c ≤ (q * f + r).gaussNorm norm c :=
    (gaussNorm_mul_le hc.le (hasGaussNorm_of_isRestricted hq) hf.hasGaussNorm :
      (q * f).gaussNorm norm c ≤ _).trans
      (hf.le_gaussNorm_mul_add hc hmul hq hr)
  have hsub := gaussNorm_sub_le_of_le hc.le hbsum hbqf le_rfl hqf
  rwa [add_sub_cancel_left] at hsub

/-- **The Weierstrass division estimate** (Bosch–Güntzer–Remmert §5.2.1, Theorem 2). If `f` is
distinguished of degree `s` at the radius `c`, right multiplication by its coefficient in degree
`s` scales norms exactly, `q` is restricted, and `r` vanishes in every degree `≥ s`, then

```text
‖q * f + r‖ = max (‖q‖ * ‖f‖) ‖r‖
```

for the Gauss norm at `c`. No cancellation occurs in a Weierstrass decomposition. The norm
condition on the distinguished coefficient holds whenever the norm of the coefficient ring is
multiplicative. -/
theorem IsDistinguished.gaussNorm_mul_add_eq_max (hf : IsDistinguished c s f) (hc : 0 < c)
    (hmul : ∀ x, ‖x * f.coeff s‖ = ‖x‖ * ‖f.coeff s‖)
    (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    (q * f + r).gaussNorm norm c =
      max (q.gaussNorm norm c * f.gaussNorm norm c) (r.gaussNorm norm c) := by
  refine le_antisymm ?_ (max_le (hf.le_gaussNorm_mul_add hc hmul hq hr)
    (hf.gaussNorm_le_gaussNorm_mul_add hc hmul hq hr))
  have hqf : (q * f).gaussNorm norm c ≤ q.gaussNorm norm c * f.gaussNorm norm c :=
    gaussNorm_mul_le hc.le (hasGaussNorm_of_isRestricted hq) hf.hasGaussNorm
  exact (PowerSeries.gaussNorm_add_le_max norm c (q * f) r hc.le norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm
    (hasGaussNorm_mul hc.le (hasGaussNorm_of_isRestricted hq) hf.hasGaussNorm)
    (hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero hr))).trans
      (max_le_max hqf le_rfl)

/-- **Uniqueness in Weierstrass division** (Bosch–Güntzer–Remmert §5.2.1, Theorem 2). Any power
series has at most one decomposition `q * f + r` with `q` restricted and `r` vanishing in every
degree `≥ s`, for `f` distinguished of degree `s` such that right multiplication by its
coefficient in degree `s` scales norms exactly. -/
theorem IsDistinguished.eq_and_eq_of_mul_add_eq_mul_add (hf : IsDistinguished c s f) (hc : 0 < c)
    (hmul : ∀ x, ‖x * f.coeff s‖ = ‖x‖ * ‖f.coeff s‖)
    {q' r' : PowerSeries R} (hq : q.IsRestricted c)
    (hq' : q'.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0)
    (hr' : ∀ m, s ≤ m → r'.coeff m = 0) (h : q * f + r = q' * f + r') :
    q = q' ∧ r = r' := by
  have hqq : (q - q').IsRestricted c := by
    simpa only [sub_eq_add_neg] using
      hq.add hq'.neg
  have hrr : ∀ m, s ≤ m → (r - r').coeff m = 0 := by
    intro m hm
    rw [map_sub, hr m hm, hr' m hm, sub_zero]
  have hzero : (q - q') * f + (r - r') = 0 := by
    rw [sub_mul, sub_add_sub_comm, h, sub_self]
  have hmax : max ((q - q').gaussNorm norm c * f.gaussNorm norm c)
      ((r - r').gaussNorm norm c) = 0 := by
    rw [← hf.gaussNorm_mul_add_eq_max hc hmul hqq hrr, hzero]
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

end NormedRing

section MulDistinguished

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ} {s : ℕ}
  {f g q r : PowerSeries R}

/-- **The Weierstrass division estimate for a multiplicatively distinguished divisor.** Over an
ultrametric normed commutative ring, if `g` is multiplicatively distinguished of degree `s` at the
radius `c`, `q` is restricted, and `r` vanishes in every degree `≥ s`, then

```text
‖g * q + r‖ = max (‖g‖ * ‖q‖) ‖r‖
```

for the Gauss norm at `c`. The norm of the coefficient ring need not be multiplicative. In a
Weierstrass division `f = g * q + r` it bounds the quotient by `‖f‖ / ‖g‖` and the remainder by
`‖f‖`. -/
theorem IsMulDistinguished.gaussNorm_mul_add_eq_max (hg : IsMulDistinguished c s g) (hc : 0 < c)
    (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    (g * q + r).gaussNorm norm c =
      max (g.gaussNorm norm c * q.gaussNorm norm c) (r.gaussNorm norm c) := by
  rw [mul_comm g, mul_comm (g.gaussNorm norm c)]
  exact hg.toIsDistinguished.gaussNorm_mul_add_eq_max hc
    hg.norm_mul_coeff hq hr

/-- **Uniqueness in Weierstrass division by a multiplicatively distinguished series.** Over an
ultrametric normed commutative ring, a power series has at most one decomposition `g * q + r`
with `q` restricted and `r` vanishing in every degree `≥ s`, for `g` multiplicatively
distinguished of degree `s`. -/
theorem IsMulDistinguished.eq_and_eq_of_mul_add_eq_mul_add (hg : IsMulDistinguished c s g)
    (hc : 0 < c) {q' r' : PowerSeries R} (hq : q.IsRestricted c) (hq' : q'.IsRestricted c)
    (hr : ∀ m, s ≤ m → r.coeff m = 0) (hr' : ∀ m, s ≤ m → r'.coeff m = 0)
    (h : g * q + r = g * q' + r') : q = q' ∧ r = r' := by
  rw [mul_comm g, mul_comm g] at h
  exact hg.toIsDistinguished.eq_and_eq_of_mul_add_eq_mul_add hc
    hg.norm_mul_coeff hq hq' hr hr' h

omit [IsUltrametricDist R] in
/-- Division of a polynomial `P` by the polynomial part `g⁻` of a multiplicatively distinguished
series `g` of degree `s`: `g⁻` has degree `s` and a unit leading coefficient, so after scaling by
the inverse of that unit it is monic. -/
private theorem exists_trunc_mul_add_of_isMulDistinguished (hg : IsMulDistinguished c s g)
    (P : Polynomial R) :
    ∃ Qp rp : Polynomial R, P = (g.trunc (s + 1) : Polynomial R) * Qp + rp ∧
      rp.degree < (s : WithBot ℕ) := by
  have hPs : (g.trunc (s + 1) : Polynomial R).coeff s = g.coeff s := by
    rw [PowerSeries.coeff_trunc, ite_eq_left (Nat.lt_succ_self s)]
  obtain ⟨u, hu⟩ := hg.isNormMulUnit_coeff.isUnit
  have : Nontrivial R := nontrivial_of_ne _ _ hg.coeff_ne_zero
  have hPm : (Polynomial.C (u⁻¹ : Rˣ).val * (g.trunc (s + 1) : Polynomial R)).IsMonicOfDegree
      s := (Polynomial.isMonicOfDegree_iff _ s).mpr
    ⟨(Polynomial.natDegree_C_mul_le _ _).trans
        (Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt g s)),
      by rw [Polynomial.coeff_C_mul, hPs, ← hu, Units.inv_mul]⟩
  refine ⟨Polynomial.C (u⁻¹ : Rˣ).val * (P /ₘ
      (Polynomial.C (u⁻¹ : Rˣ).val * (g.trunc (s + 1) : Polynomial R))),
    P %ₘ
      (Polynomial.C (u⁻¹ : Rˣ).val * (g.trunc (s + 1) : Polynomial R)), ?_, ?_⟩
  · linear_combination (Polynomial.modByMonic_add_div P
      (Polynomial.C (u⁻¹ : Rˣ).val * (g.trunc (s + 1) : Polynomial R))).symm
  · have hlt := Polynomial.degree_modByMonic_lt P hPm.monic
    rwa [Polynomial.degree_eq_natDegree hPm.ne_zero, hPm.natDegree_eq] at hlt

/-- One step of the Weierstrass division algorithm. Dividing a sufficiently long truncation of
`f` by the polynomial part of `g` — an ordinary division of polynomials by one whose leading
coefficient is a unit — leaves a defect whose Gauss norm has shrunk by the factor `θ` measuring
the tail of `g`. -/
private theorem exists_gaussNorm_sub_mul_add_le (hg : IsMulDistinguished c s g) (hc : 0 < c)
    (hgr : g.IsRestricted c) {θ : ℝ} (hθ : 0 < θ)
    (hθg : (g - ((g.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm norm c
      ≤ θ * g.gaussNorm norm c) (hf : f.IsRestricted c) :
    ∃ q r : PowerSeries R, q.IsRestricted c ∧ (∀ m, s ≤ m → r.coeff m = 0) ∧
      g.gaussNorm norm c * q.gaussNorm norm c ≤ f.gaussNorm norm c ∧
      r.gaussNorm norm c ≤ f.gaussNorm norm c ∧
      (f - (g * q + r)).gaussNorm norm c ≤ θ * f.gaussNorm norm c := by
  -- The polynomial part `g⁻` of `g`, which is again multiplicatively distinguished of degree `s`,
  -- and its tail.
  have hzero : (0 : PowerSeries R).gaussNorm norm c = 0 :=
    PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)
  have hGd : IsMulDistinguished c s ((g.trunc (s + 1) : Polynomial R) : PowerSeries R) := hg.trunc
  have hGn : ((g.trunc (s + 1) : Polynomial R) : PowerSeries R).gaussNorm norm c
      = g.gaussNorm norm c := hg.toIsDistinguished.gaussNorm_trunc
  have htailr : (g - ((g.trunc (s + 1) : Polynomial R) : PowerSeries R)).IsRestricted c := by
    rw [sub_eq_add_neg]
    exact hgr.add (isRestricted_polynomial _).neg
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, 0, PowerSeries.isRestricted_zero c, fun m _ ↦ by simp, by simp [hzero],
      by simp [hzero], by simp [hzero]⟩
  have hfpos : 0 < f.gaussNorm norm c :=
    lt_of_le_of_ne (PowerSeries.gaussNorm_nonneg norm c f norm_nonneg) fun h ↦
      hf0 ((PowerSeries.gaussNorm_eq_zero_iff norm c f norm_zero norm_nonneg
        (fun _ ↦ norm_eq_zero.mp) hc (hasGaussNorm_of_isRestricted hf)).mp h.symm)
  -- Truncate `f` past the degree where its weighted coefficients have dropped below `θ‖f‖`.
  obtain ⟨N, hFn, hsmall⟩ := exists_gaussNorm_trunc_sub_le hf hθ hfpos
  have hsmallr : (f - ((f.trunc N : Polynomial R) : PowerSeries R)).IsRestricted c := by
    rw [sub_eq_add_neg]
    exact hf.add (isRestricted_polynomial _).neg
  -- Divide that truncation by `g⁻`, a polynomial of degree `s` whose leading coefficient is a
  -- unit: after scaling by the inverse of that unit it is monic, so division by it is possible.
  obtain ⟨Qp, rp, hdiv, hrdeg⟩ :=
    exists_trunc_mul_add_of_isMulDistinguished hg (f.trunc N : Polynomial R)
  have hrpz : ∀ m, s ≤ m → ((rp : Polynomial R) : PowerSeries R).coeff m = 0 := fun m hm ↦ by
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt (hrdeg.trans_le (by exact_mod_cast hm))
  have hQr : ((Qp : Polynomial R) : PowerSeries R).IsRestricted c :=
    isRestricted_polynomial Qp
  have hdivPS : ((f.trunc N : Polynomial R) : PowerSeries R)
      = ((g.trunc (s + 1) : Polynomial R) : PowerSeries R) * (Qp : PowerSeries R)
        + (rp : PowerSeries R) := by
    rw [hdiv]; push_cast; ring
  -- The norm identity for `g⁻` bounds the quotient and the remainder by `‖f‖`.
  have hnorm := hGd.gaussNorm_mul_add_eq_max hc hQr hrpz
  rw [← hdivPS, hGn] at hnorm
  have hmax : max (g.gaussNorm norm c * (Qp : PowerSeries R).gaussNorm norm c)
      ((rp : PowerSeries R).gaussNorm norm c) ≤ f.gaussNorm norm c := by
    rw [← hnorm]; exact hFn
  refine ⟨(Qp : PowerSeries R), (rp : PowerSeries R), hQr, hrpz,
    (le_max_left _ _).trans hmax, (le_max_right _ _).trans hmax, ?_⟩
  -- What is left is the discarded tail of `f` minus the tail of `g` times the quotient. Only the
  -- submultiplicativity of the Gauss norm is needed to bound the latter.
  have hdefect : f - (g * (Qp : PowerSeries R) + (rp : PowerSeries R))
      = (f - ((f.trunc N : Polynomial R) : PowerSeries R))
        - (g - ((g.trunc (s + 1) : Polynomial R) : PowerSeries R)) * (Qp : PowerSeries R) := by
    rw [hdivPS]; ring
  rw [hdefect]
  refine gaussNorm_sub_le_of_le hc.le (hasGaussNorm_of_isRestricted hsmallr)
    (hasGaussNorm_of_isRestricted (htailr.mul hQr)) hsmall ?_
  refine (gaussNorm_mul_le_of_le hc.le htailr hQr hθg).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hmax) hθ.le

/-- The successive defects of Weierstrass division steps. Starting from a restricted series `f`,
repeated division steps give quotients `Q n` and remainders `Rr n` and defects `G n` with
`G (n + 1) = G n - (g * Q n + Rr n)`, whose Gauss norms contract by the factor `θ` at every
step. -/
private theorem exists_defect_sequence (hg : IsMulDistinguished c s g) (hc : 0 < c)
    (hgr : g.IsRestricted c) {θ : ℝ} (hθ0 : 0 < θ)
    (hθg : (g - ((g.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm norm c
      ≤ θ * g.gaussNorm norm c) (hf : f.IsRestricted c) :
    ∃ Q Rr G : ℕ → PowerSeries R, G 0 = f ∧ (∀ n, G (n + 1) = G n - (g * Q n + Rr n)) ∧
      ∀ n, (G n).IsRestricted c ∧ (Q n).IsRestricted c ∧ (∀ m, s ≤ m → (Rr n).coeff m = 0) ∧
        g.gaussNorm norm c * (Q n).gaussNorm norm c ≤ (G n).gaussNorm norm c ∧
        (Rr n).gaussNorm norm c ≤ (G n).gaussNorm norm c ∧
        (G n).gaussNorm norm c ≤ θ ^ n * f.gaussNorm norm c := by
  -- A choice of one division step at every restricted series, with contraction factor `θ`.
  have hstep : ∀ h : PowerSeries R, ∃ p : PowerSeries R × PowerSeries R, h.IsRestricted c →
      p.1.IsRestricted c ∧ (∀ m, s ≤ m → p.2.coeff m = 0) ∧
      g.gaussNorm norm c * p.1.gaussNorm norm c ≤ h.gaussNorm norm c ∧
      p.2.gaussNorm norm c ≤ h.gaussNorm norm c ∧
      (h - (g * p.1 + p.2)).gaussNorm norm c ≤ θ * h.gaussNorm norm c := by
    intro h
    by_cases hh : h.IsRestricted c
    · obtain ⟨q, r, h1, h2, h3, h4, h5⟩ :=
        exists_gaussNorm_sub_mul_add_le hg hc hgr hθ0 hθg hh
      exact ⟨(q, r), fun _ ↦ ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨(0, 0), fun hcon ↦ absurd hcon hh⟩
  choose F hF using hstep
  -- The sequence of successive defects.
  let G : ℕ → PowerSeries R := fun n ↦
    Nat.rec (motive := fun _ ↦ PowerSeries R) f (fun _ h ↦ h - (g * (F h).1 + (F h).2)) n
  have hG0 : G 0 = f := rfl
  have hGsucc : ∀ n, G (n + 1) = G n - (g * (F (G n)).1 + (F (G n)).2) := fun _ ↦ rfl
  have hGr : ∀ n, (G n).IsRestricted c := by
    intro n
    induction n with
    | zero => exact hf
    | succ n ih =>
      rw [hGsucc n, sub_eq_add_neg]
      exact ih.add ((hgr.mul (hF (G n) ih).1).add
          (isRestricted_of_forall_coeff_eq_zero (hF (G n) ih).2.1)).neg
  have hGn : ∀ n, (G n).gaussNorm norm c ≤ θ ^ n * f.gaussNorm norm c := by
    intro n
    induction n with
    | zero => simp [hG0]
    | succ n ih =>
      rw [hGsucc n]
      refine ((hF (G n) (hGr n)).2.2.2.2).trans ?_
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left ih hθ0.le
  refine ⟨fun n ↦ (F (G n)).1, fun n ↦ (F (G n)).2, G, rfl, hGsucc, fun n ↦ ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := hF (G n) (hGr n)
  exact ⟨hGr n, h1, h2, h3, h4, hGn n⟩

/-- Summing a sequence of Weierstrass division steps coefficientwise. If the defects `G n` satisfy
`G (n + 1) = G n - (g * Q n + Rr n)`, with restricted quotients `Q n`, remainders `Rr n` vanishing
in degrees `≥ s`, summable Gauss norms of both, and coefficients of `G n` tending to zero, then
`G 0 = g * q + r` for the coefficientwise sums `q` of the quotients and `r` of the remainders. -/
private theorem exists_mul_add_eq_of_tendsto [CompleteSpace R] (hc : 0 < c)
    (Q Rr G : ℕ → PowerSeries R) (hQ : ∀ k, (Q k).IsRestricted c)
    (hRr : ∀ k m, s ≤ m → (Rr k).coeff m = 0) (hsQ : Summable fun k ↦ (Q k).gaussNorm norm c)
    (hsr : Summable fun k ↦ (Rr k).gaussNorm norm c)
    (hGsucc : ∀ n, G (n + 1) = G n - (g * Q n + Rr n))
    (hGlim : ∀ n, Filter.Tendsto (fun m ↦ (G m).coeff n) Filter.atTop (nhds 0)) :
    ∃ q r : PowerSeries R, q.IsRestricted c ∧ (∀ m, s ≤ m → r.coeff m = 0) ∧
      g * q + r = G 0 := by
  -- Sum them coefficientwise; the defects tend to zero, so the sums telescope to `G 0`.
  set q : PowerSeries R := PowerSeries.mk fun i ↦ ∑' k, (Q k).coeff i with hqdef
  set rr : PowerSeries R := PowerSeries.mk fun i ↦ ∑' k, (Rr k).coeff i with hrdef
  have hsumQ : ∀ i, HasSum (fun k ↦ (Q k).coeff i) (q.coeff i) := fun i ↦ by
    rw [hqdef, PowerSeries.coeff_mk]
    exact (summable_coeff_of_summable_gaussNorm (R := R) hc
      (fun k ↦ hasGaussNorm_of_isRestricted (hQ k)) hsQ i).hasSum
  have hsumr : ∀ i, HasSum (fun k ↦ (Rr k).coeff i) (rr.coeff i) := fun i ↦ by
    rw [hrdef, PowerSeries.coeff_mk]
    exact (summable_coeff_of_summable_gaussNorm (R := R) hc
      (fun k ↦ hasGaussNorm_of_isRestricted
        (isRestricted_of_forall_coeff_eq_zero (hRr k))) hsr i).hasSum
  refine ⟨q, rr, isRestricted_mk_tsum_coeff hc hQ hsQ,
    fun m hm ↦ ?_, ?_⟩
  · have hz : (fun k ↦ (Rr k).coeff m) = fun _ : ℕ ↦ (0 : R) :=
      funext fun k ↦ hRr k m hm
    exact (hasSum_zero.unique (hz ▸ hsumr m)).symm
  · refine PowerSeries.ext fun n ↦ ?_
    have hmul : HasSum (fun k ↦ (g * Q k).coeff n) ((g * q).coeff n) := by
      have h := hasSum_sum (s := Finset.antidiagonal n)
        (f := fun p : ℕ × ℕ ↦ fun k ↦ g.coeff p.1 * (Q k).coeff p.2)
        (a := fun p : ℕ × ℕ ↦ g.coeff p.1 * q.coeff p.2)
        (fun p _ ↦ (hsumQ p.2).mul_left (g.coeff p.1))
      simpa only [← PowerSeries.coeff_mul] using h
    have heq : (fun k ↦ (G k).coeff n - (G (k + 1)).coeff n)
        = fun k ↦ (g * Q k).coeff n + (Rr k).coeff n := by
      funext k
      rw [hGsucc k, map_sub, map_add]
      ring
    have hstepSum : HasSum (fun k ↦ (G k).coeff n - (G (k + 1)).coeff n)
        ((g * q + rr).coeff n) := by
      rw [heq, map_add]
      exact hmul.add (hsumr n)
    have htel : HasSum (fun k ↦ (G k).coeff n - (G (k + 1)).coeff n) ((G 0).coeff n) := by
      rw [hstepSum.summable.hasSum_iff_tendsto_nat]
      have hpartial : ∀ m : ℕ, (∑ k ∈ Finset.range m, ((G k).coeff n - (G (k + 1)).coeff n))
          = (G 0).coeff n - (G m).coeff n := fun m ↦ by
        rw [Finset.sum_range_sub' (fun k ↦ (G k).coeff n) m]
      simp only [hpartial]
      simpa using tendsto_const_nhds.sub (hGlim n)
    exact hstepSum.unique htel

/-- **Weierstrass division over a Banach ring** (Martin, Proposition 1.27). Over a complete
ultrametric normed commutative ring, a restricted series `g` multiplicatively distinguished of
degree `s` at a positive radius `c` divides every restricted series `f`:

```text
f = g * q + r,    q restricted,    r a polynomial of degree less than s.
```

The norm of the coefficient ring need not be multiplicative, and the ring may have nilpotents:
only the distinguished coefficient of `g` is asked to scale norms exactly. The decomposition is
unique by `TauCeti.PowerSeries.IsMulDistinguished.eq_and_eq_of_mul_add_eq_mul_add`, and its
quotient and remainder obey the norm identity
`TauCeti.PowerSeries.IsMulDistinguished.gaussNorm_mul_add_eq_max`. -/
theorem IsMulDistinguished.exists_mul_add_eq [CompleteSpace R] (hg : IsMulDistinguished c s g)
    (hc : 0 < c) (hgr : g.IsRestricted c) (hf : f.IsRestricted c) :
    ∃ q r : PowerSeries R, q.IsRestricted c ∧ (∀ m, s ≤ m → r.coeff m = 0) ∧
      g * q + r = f := by
  have hgpos : 0 < g.gaussNorm norm c := hg.gaussNorm_pos
  obtain ⟨θ, hθ0, hθ1, hθg⟩ : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      (g - ((g.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm norm c
        ≤ θ * g.gaussNorm norm c := by
    refine ⟨max (1 / 2) ((g - ((g.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm
      norm c / g.gaussNorm norm c), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
      max_lt (by norm_num) ((div_lt_one hgpos).mpr
        (hg.toIsDistinguished.gaussNorm_sub_trunc_lt hc hgr)), ?_⟩
    rw [← div_le_iff₀ hgpos]
    exact le_max_right _ _
  obtain ⟨Q, Rr, G, hG0, hGsucc, hG⟩ := exists_defect_sequence hg hc hgr hθ0 hθg hf
  -- The quotients and remainders produced along the way have geometrically small Gauss norms.
  have hgeo : Summable fun k : ℕ ↦ θ ^ k * f.gaussNorm norm c :=
    (summable_geometric_of_lt_one hθ0.le hθ1).mul_right _
  have hsQ : Summable fun k ↦ (Q k).gaussNorm norm c := by
    refine Summable.of_nonneg_of_le
      (fun k ↦ PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg) (fun k ↦ ?_)
      (hgeo.div_const (g.gaussNorm norm c))
    rw [le_div_iff₀ hgpos, mul_comm]
    exact (hG k).2.2.2.1.trans (hG k).2.2.2.2.2
  have hsr : Summable fun k ↦ (Rr k).gaussNorm norm c :=
    Summable.of_nonneg_of_le (fun k ↦ PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
      (fun k ↦ (hG k).2.2.2.2.1.trans (hG k).2.2.2.2.2) hgeo
  have hGlim (n : ℕ) : Filter.Tendsto (fun m ↦ (G m).coeff n) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun m ↦ θ ^ m * f.gaussNorm norm c / c ^ n) (fun m ↦ ?_) ?_
    · rw [le_div_iff₀ (pow_pos hc n)]
      exact (PowerSeries.le_gaussNorm norm c _
        (hasGaussNorm_of_isRestricted (hG m).1) n).trans (hG m).2.2.2.2.2
    · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).mul_const
        (f.gaussNorm norm c)).div_const (c ^ n)
  simpa only [hG0] using exists_mul_add_eq_of_tendsto hc Q Rr G (fun k ↦ (hG k).2.1)
    (fun k ↦ (hG k).2.2.1) hsQ hsr hGsucc hGlim

/-- **Weierstrass division over a Banach ring** (Martin, Proposition 1.27), in its
unique-existence form: over a complete ultrametric normed commutative ring, a restricted series
`g` multiplicatively distinguished of degree `s` at a positive radius divides every restricted
series `f` in exactly one way, with a restricted quotient and a remainder that is a polynomial
of degree less than `s`. -/
theorem IsMulDistinguished.existsUnique_mul_add_eq [CompleteSpace R]
    (hg : IsMulDistinguished c s g) (hc : 0 < c) (hgr : g.IsRestricted c)
    (hf : f.IsRestricted c) :
    ∃! p : PowerSeries R × PowerSeries R,
      p.1.IsRestricted c ∧ (∀ m, s ≤ m → p.2.coeff m = 0) ∧ g * p.1 + p.2 = f := by
  obtain ⟨q, r, hq, hr, hqr⟩ := hg.exists_mul_add_eq hc hgr hf
  refine ⟨(q, r), ⟨hq, hr, hqr⟩, fun p ⟨h1, h2, h3⟩ ↦ ?_⟩
  obtain ⟨e1, e2⟩ := hg.eq_and_eq_of_mul_add_eq_mul_add hc h1 hq h2 hr (h3.trans hqr.symm)
  exact Prod.ext e1 e2

end MulDistinguished

section Subring

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {c : ℝ} {s : ℕ}

/-- **Weierstrass division inside the ring of restricted power series.** Over a complete
ultrametric normed commutative ring, a member `f` of the ring of series restricted at a positive
radius `c` which is distinguished of degree `s`, with a multiplicative-unit coefficient
in degree `s`, divides every member `g` with remainder:

```text
g = q * f + r,    r a polynomial of degree less than s,
```

with `q` and `r` again restricted at `c`; the remainder `r` is in general nonzero. This is
`TauCeti.PowerSeries.IsMulDistinguished.exists_mul_add_eq` read in the ring of restricted series,
which is the form ideal-theoretic arguments use. The pair `(q, r)` is unique, by
`TauCeti.PowerSeries.IsMulDistinguished.existsUnique_mul_add_eq_subring`. -/
theorem IsMulDistinguished.exists_mul_add_eq_subring (hc : 0 < c)
    {f : PowerSeries.IsRestricted.subring (R := R) c}
    (hf : IsMulDistinguished c s (f : PowerSeries R))
    (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ∃ q r : PowerSeries.IsRestricted.subring (R := R) c,
      (∀ m, s ≤ m → (r : PowerSeries R).coeff m = 0) ∧ q * f + r = g := by
  obtain ⟨q, r, hq, hr, hqr⟩ := hf.exists_mul_add_eq hc f.2 g.2
  rw [mul_comm] at hqr
  -- the coercion of a sum and of a product in a subring reduces to the sum and product of the
  -- coercions, so `hqr` is literally the required equation of underlying series
  exact ⟨⟨q, hq⟩, ⟨r, isRestricted_of_forall_coeff_eq_zero hr⟩, hr, Subtype.ext hqr⟩

/-- **Weierstrass division inside the ring of restricted power series is unique.** The quotient and
remainder of `TauCeti.PowerSeries.IsMulDistinguished.exists_mul_add_eq_subring` are the only ones: a
member `g` of the ring of series restricted at a positive radius `c` is written as `q * f + r`,
with `r` a polynomial of degree less than the distinguished degree `s` of `f`, in exactly one way.
This is `TauCeti.PowerSeries.IsMulDistinguished.existsUnique_mul_add_eq` read in that ring. -/
theorem IsMulDistinguished.existsUnique_mul_add_eq_subring (hc : 0 < c)
    {f : PowerSeries.IsRestricted.subring (R := R) c}
    (hf : IsMulDistinguished c s (f : PowerSeries R))
    (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ∃! p : PowerSeries.IsRestricted.subring (R := R) c ×
        PowerSeries.IsRestricted.subring (R := R) c,
      (∀ m, s ≤ m → (p.2 : PowerSeries R).coeff m = 0) ∧ p.1 * f + p.2 = g := by
  obtain ⟨q, r, hr, hqr⟩ := hf.exists_mul_add_eq_subring hc g
  refine ⟨(q, r), ⟨hr, hqr⟩, fun p ⟨h2, h3⟩ ↦ ?_⟩
  -- the coercions of the two decompositions are equations of underlying series, to which the
  -- uniqueness of Weierstrass division applies
  have hcoe : (p.1 : PowerSeries R) * (f : PowerSeries R) + (p.2 : PowerSeries R)
      = (q : PowerSeries R) * (f : PowerSeries R) + (r : PowerSeries R) := by
    have := congrArg (Subtype.val (p := (· ∈ PowerSeries.IsRestricted.subring (R := R) c)))
      (h3.trans hqr.symm)
    simpa using this
  obtain ⟨e1, e2⟩ := hf.toIsDistinguished.eq_and_eq_of_mul_add_eq_mul_add hc
    hf.norm_mul_coeff p.1.2 q.2 h2 hr
    hcoe
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

end Subring

end TauCeti.PowerSeries
