/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Weierstrass division for restricted power series

Let `f` be a power series which is distinguished of degree `s` at the radius `c`: its
Gauss norm is attained in degree `s`, and every later coefficient is strictly smaller. A
*Weierstrass division* by `f` writes a power series as

```text
q * f + r,    q restricted,    r vanishing in every degree ≥ s
```

— that is, with `r` a polynomial of degree less than `s`. This file first proves the two facts
about such a decomposition which need no completeness: the norm identity

```text
‖q * f + r‖ = max (‖q‖ * ‖f‖) ‖r‖
```

for the Gauss norm at `c`, and, as a consequence, that `q` and `r` are determined by the series
they sum to.

It then proves existence for restricted `f` whose coefficient in degree `s` is a unit, over a
complete ultrametric normed commutative ring whose norm is multiplicative. Over a field the unit
condition is automatic. Over a ring it is what makes the polynomial part `f⁻ = f.trunc (s + 1)` a
unit multiple of a monic polynomial, so that a truncation of the dividend can be divided by it as
an ordinary division of polynomials. The division leaves a defect built from the tail `f - f⁻`,
whose Gauss norm is strictly smaller than that of `f`. Each step therefore shrinks the dividend by
a fixed factor, and the resulting series of quotients and remainders converges coefficientwise.

The coefficient ring is allowed to be a ring, rather than a field, for the noetherianity of Tate
algebras in several variables: the Tate algebra in `n` variables is a ring of restricted series in
one variable over the Tate algebra in `n - 1` variables, whose Gauss norm is multiplicative, and
Bosch–Güntzer–Remmert divide there by series whose dominant coefficient is a unit.

Since the quotient and the remainder are themselves restricted at `c`, the division is also
recorded inside the subring `PowerSeries.IsRestricted.subring c` of `R⟦X⟧`, which is the form
its ideal-theoretic consequences use.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.gaussNorm_mul_add_eq_max`: the norm identity.
* `TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_add_eq_mul_add`: the quotient and the
  remainder of a Weierstrass division are unique.
* `TauCeti.PowerSeries.IsDistinguished.exists_mul_add_eq` and
  `TauCeti.PowerSeries.IsDistinguished.existsUnique_mul_add_eq`: over a complete ultrametric
  normed commutative ring with multiplicative norm, every restricted power series has a unique
  Weierstrass division by `f`, provided the coefficient of `f` in degree `s` is a unit.
* `TauCeti.PowerSeries.IsDistinguished.exists_mul_add_eq_subring` and
  `TauCeti.PowerSeries.IsDistinguished.existsUnique_mul_add_eq_subring`: the same division read
  inside the subring `PowerSeries.IsRestricted.subring c` of series restricted at `c`, where
  quotient and remainder are elements of that subring.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2, whose norm identity,
  uniqueness assertion and existence assertion these are; the statements there are for the unit
  radius.

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

variable [IsUltrametricDist R] [NormMulClass R]

/-- **The Weierstrass lower bound for the quotient.** In a decomposition `q * f + r` by a
distinguished series `f` of degree `s`, with `r` vanishing in every degree `≥ s`, the Gauss norm of
the sum is at least the Gauss norm of `q * f`. -/
theorem IsDistinguished.le_gaussNorm_mul_add (hf : IsDistinguished c s f) (hc : 0 < c)
    (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    q.gaussNorm norm c * f.gaussNorm norm c ≤ (q * f + r).gaussNorm norm c := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0), zero_mul]
    exact PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg
  obtain ⟨n, hn⟩ := exists_isDistinguished hc hq hq0
  have hbqf := hasGaussNorm_mul hc.le (hasGaussNorm_of_isRestricted hq) hf.hasGaussNorm
  have hbr : r.HasGaussNorm norm c :=
    hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero hr)
  have hsum := hasGaussNorm_add hc.le hbqf hbr
  have hcoeff : (q * f + r).coeff (n + s) = (q * f).coeff (n + s) := by
    rw [map_add, hr (n + s) (Nat.le_add_left s n), add_zero]
  calc q.gaussNorm norm c * f.gaussNorm norm c
      = ‖(q * f + r).coeff (n + s)‖ * c ^ (n + s) := by
        rw [hcoeff]
        exact (hn.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hf hc).symm
    _ ≤ (q * f + r).gaussNorm norm c :=
        PowerSeries.le_gaussNorm norm c _ hsum _

/-- **The Weierstrass lower bound for the remainder.** In a decomposition `q * f + r` by a
distinguished series `f` of degree `s`, with `r` vanishing in every degree `≥ s`, the Gauss norm of
the sum is at least the Gauss norm of `r`. -/
theorem IsDistinguished.gaussNorm_le_gaussNorm_mul_add (hf : IsDistinguished c s f) (hc : 0 < c)
    (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    r.gaussNorm norm c ≤ (q * f + r).gaussNorm norm c := by
  have hbqf := hasGaussNorm_mul hc.le (hasGaussNorm_of_isRestricted hq) hf.hasGaussNorm
  have hbr : r.HasGaussNorm norm c :=
    hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero hr)
  have hbsum := hasGaussNorm_add hc.le hbqf hbr
  have hqf : (q * f).gaussNorm norm c ≤ (q * f + r).gaussNorm norm c :=
    (MvPowerSeries.gaussNorm_mul_le norm (fun _ : Unit ↦ c) q f (fun _ ↦ hc.le)
      norm_nonneg norm_mul_le IsUltrametricDist.isNonarchimedean_norm norm_zero
      (hasGaussNorm_of_isRestricted hq).hasMvGaussNorm hf.hasGaussNorm.hasMvGaussNorm).trans
      (hf.le_gaussNorm_mul_add hc hq hr)
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
distinguished of degree `s` at the radius `c`, `q` is restricted, and `r` vanishes in
every degree `≥ s`, then

```text
‖q * f + r‖ = max (‖q‖ * ‖f‖) ‖r‖
```

for the Gauss norm at `c`. No cancellation occurs in a Weierstrass decomposition. -/
theorem IsDistinguished.gaussNorm_mul_add_eq_max (hf : IsDistinguished c s f) (hc : 0 < c)
    (hq : q.IsRestricted c) (hr : ∀ m, s ≤ m → r.coeff m = 0) :
    (q * f + r).gaussNorm norm c =
      max (q.gaussNorm norm c * f.gaussNorm norm c) (r.gaussNorm norm c) := by
  refine le_antisymm ?_ (max_le (hf.le_gaussNorm_mul_add hc hq hr)
    (hf.gaussNorm_le_gaussNorm_mul_add hc hq hr))
  have hqf : (q * f).gaussNorm norm c = q.gaussNorm norm c * f.gaussNorm norm c := by
    rcases eq_or_ne q 0 with rfl | hq0
    · simp [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
    · obtain ⟨n, hn⟩ := exists_isDistinguished hc hq hq0
      exact (hn.mul hf hc).norm_coeff_mul_pow_eq.symm.trans
        (hn.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hf hc)
  rw [← hqf]
  exact PowerSeries.gaussNorm_add_le_max norm c (q * f) r hc.le norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm
    (hasGaussNorm_mul hc.le (hasGaussNorm_of_isRestricted hq) hf.hasGaussNorm)
    (hasGaussNorm_of_isRestricted (isRestricted_of_forall_coeff_eq_zero hr))

/-- **Uniqueness in Weierstrass division** (Bosch–Güntzer–Remmert §5.2.1, Theorem 2). A restricted
series has at most one decomposition `q * f + r` with `q` restricted and `r` vanishing in every
degree `≥ s`, for `f` distinguished of degree `s`. -/
theorem IsDistinguished.eq_and_eq_of_mul_add_eq_mul_add (hf : IsDistinguished c s f) (hc : 0 < c)
    {q' r' : PowerSeries R} (hq : q.IsRestricted c)
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
    rw [← hf.gaussNorm_mul_add_eq_max hc hqq hrr, hzero]
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

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {c : ℝ} {s : ℕ}
  {f g : PowerSeries R}

/-- One step of the Weierstrass division algorithm. Dividing a sufficiently long truncation of
`g` by the polynomial part of `f` — an ordinary division of polynomials by one whose leading
coefficient is a unit — leaves a defect whose Gauss norm has shrunk by the factor `θ` measuring
the tail of `f`. -/
private theorem exists_gaussNorm_sub_mul_add_le (hf : IsDistinguished c s f)
    (hu : IsUnit (f.coeff s)) (hc : 0 < c) (hfr : f.IsRestricted c) {θ : ℝ} (hθ : 0 < θ)
    (hθf : (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm norm c
      ≤ θ * f.gaussNorm norm c) (hg : g.IsRestricted c) :
    ∃ q r : PowerSeries R, q.IsRestricted c ∧ (∀ m, s ≤ m → r.coeff m = 0) ∧
      q.gaussNorm norm c * f.gaussNorm norm c ≤ g.gaussNorm norm c ∧
      r.gaussNorm norm c ≤ g.gaussNorm norm c ∧
      (g - (q * f + r)).gaussNorm norm c ≤ θ * g.gaussNorm norm c := by
  -- The polynomial part `f⁻` of `f`, which is again distinguished of degree `s`, and its tail.
  have hzero : (0 : PowerSeries R).gaussNorm norm c = 0 :=
    PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)
  have hFd : IsDistinguished c s ((f.trunc (s + 1) : Polynomial R) : PowerSeries R) := hf.trunc
  have hFn : ((f.trunc (s + 1) : Polynomial R) : PowerSeries R).gaussNorm norm c
      = f.gaussNorm norm c := hf.gaussNorm_trunc
  have htailr : (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).IsRestricted c := by
    rw [sub_eq_add_neg]
    exact PowerSeries.isRestricted.add c hfr (PowerSeries.isRestricted.neg c
      (isRestricted_of_forall_coeff_eq_zero (n := s + 1) fun m hm ↦ by
        rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_right (by omega)]))
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨0, 0, PowerSeries.isRestricted_zero c, fun m _ ↦ by simp, by simp [hzero],
      by simp [hzero], by simp [hzero]⟩
  have hgpos : 0 < g.gaussNorm norm c :=
    lt_of_le_of_ne (PowerSeries.gaussNorm_nonneg norm c g norm_nonneg) fun h ↦
      hg0 ((PowerSeries.gaussNorm_eq_zero_iff norm c g norm_zero norm_nonneg
        (fun _ ↦ norm_eq_zero.mp) hc (hasGaussNorm_of_isRestricted hg)).mp h.symm)
  -- Truncate `g` past the degree where its weighted coefficients have dropped below `θ‖g‖`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ m, N ≤ m → ‖g.coeff m‖ * c ^ m ≤ θ * g.gaussNorm norm c := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (((PowerSeries.isRestricted_iff' c g).mp hg).eventually
        (gt_mem_nhds (mul_pos hθ hgpos)))
    exact ⟨N, fun m hm ↦ (hN m hm).le⟩
  have hgcoeff (m : ℕ) : ((g.trunc N : Polynomial R) : PowerSeries R).coeff m =
      if m < N then g.coeff m else 0 := by
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  have hGn : ((g.trunc N : Polynomial R) : PowerSeries R).gaussNorm norm c
      ≤ g.gaussNorm norm c := by
    rw [PowerSeries.gaussNorm_eq]
    refine ciSup_le fun m ↦ ?_
    rw [hgcoeff m]
    split_ifs
    · exact PowerSeries.le_gaussNorm norm c g (hasGaussNorm_of_isRestricted hg) m
    · simpa using PowerSeries.gaussNorm_nonneg norm c g norm_nonneg
  have hsmall : (g - ((g.trunc N : Polynomial R) : PowerSeries R)).gaussNorm norm c
      ≤ θ * g.gaussNorm norm c := by
    rw [PowerSeries.gaussNorm_eq]
    refine ciSup_le fun m ↦ ?_
    rw [map_sub, hgcoeff m]
    split_ifs with hm
    · simp only [sub_self, norm_zero, zero_mul]
      exact mul_nonneg hθ.le hgpos.le
    · rw [sub_zero]
      exact hN m (by omega)
  have hsmallr : (g - ((g.trunc N : Polynomial R) : PowerSeries R)).IsRestricted c := by
    rw [sub_eq_add_neg]
    exact PowerSeries.isRestricted.add c hg (PowerSeries.isRestricted.neg c
      (isRestricted_of_forall_coeff_eq_zero (n := N) fun m hm ↦ by
        rw [hgcoeff m, ite_eq_right (by omega)]))
  -- Divide that truncation by `f⁻`, a polynomial of degree `s` whose leading coefficient is a
  -- unit: after scaling by the inverse of that unit it is monic, so division by it is possible.
  have hPs : (f.trunc (s + 1) : Polynomial R).coeff s = f.coeff s := by
    rw [PowerSeries.coeff_trunc, ite_eq_left (Nat.lt_succ_self s)]
  obtain ⟨Qp, rp, hdiv, hrdeg⟩ : ∃ Qp rp : Polynomial R,
      (g.trunc N : Polynomial R) = (f.trunc (s + 1) : Polynomial R) * Qp + rp ∧
        rp.degree < (s : WithBot ℕ) := by
    obtain ⟨u, hu⟩ := hu
    have : Nontrivial R := nontrivial_of_ne _ _ hf.coeff_ne_zero
    have hPm : (Polynomial.C (u⁻¹ : Rˣ).val * (f.trunc (s + 1) : Polynomial R)).IsMonicOfDegree
        s := (Polynomial.isMonicOfDegree_iff _ s).mpr
      ⟨(Polynomial.natDegree_C_mul_le _ _).trans
          (Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt f s)),
        by rw [Polynomial.coeff_C_mul, hPs, ← hu, Units.inv_mul]⟩
    refine ⟨Polynomial.C (u⁻¹ : Rˣ).val * ((g.trunc N : Polynomial R) /ₘ
        (Polynomial.C (u⁻¹ : Rˣ).val * (f.trunc (s + 1) : Polynomial R))),
      (g.trunc N : Polynomial R) %ₘ
        (Polynomial.C (u⁻¹ : Rˣ).val * (f.trunc (s + 1) : Polynomial R)), ?_, ?_⟩
    · linear_combination (Polynomial.modByMonic_add_div (g.trunc N : Polynomial R)
        (Polynomial.C (u⁻¹ : Rˣ).val * (f.trunc (s + 1) : Polynomial R))).symm
    · have hlt := Polynomial.degree_modByMonic_lt (g.trunc N : Polynomial R) hPm.monic
      rwa [Polynomial.degree_eq_natDegree hPm.ne_zero, hPm.natDegree_eq] at hlt
  have hrpz : ∀ m, s ≤ m → ((rp : Polynomial R) : PowerSeries R).coeff m = 0 := fun m hm ↦ by
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt (hrdeg.trans_le (by exact_mod_cast hm))
  have hQr : ((Qp : Polynomial R) : PowerSeries R).IsRestricted c :=
    isRestricted_of_forall_coeff_eq_zero (n := Qp.natDegree + 1) fun m hm ↦ by
      rw [Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hdivPS : ((g.trunc N : Polynomial R) : PowerSeries R)
      = (Qp : PowerSeries R) * ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)
        + (rp : PowerSeries R) := by
    rw [hdiv]; push_cast; ring
  -- The norm identity for `f⁻` bounds the quotient and the remainder by `‖g‖`.
  have hnorm := hFd.gaussNorm_mul_add_eq_max hc hQr hrpz
  rw [← hdivPS, hFn] at hnorm
  have hmax : max ((Qp : PowerSeries R).gaussNorm norm c * f.gaussNorm norm c)
      ((rp : PowerSeries R).gaussNorm norm c) ≤ g.gaussNorm norm c := by
    rw [← hnorm]; exact hGn
  refine ⟨(Qp : PowerSeries R), (rp : PowerSeries R), hQr, hrpz,
    (le_max_left _ _).trans hmax, (le_max_right _ _).trans hmax, ?_⟩
  -- What is left is the discarded tail of `g` minus the quotient times the tail of `f`.
  have hdefect : g - ((Qp : PowerSeries R) * f + (rp : PowerSeries R))
      = (g - ((g.trunc N : Polynomial R) : PowerSeries R))
        + -((Qp : PowerSeries R)
            * (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R))) := by
    rw [hdivPS]; ring
  have hmulr : ((Qp : PowerSeries R)
      * (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R))).IsRestricted c :=
    PowerSeries.isRestricted.mul c hQr htailr
  have hmulbound : ((Qp : PowerSeries R)
      * (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R))).gaussNorm norm c
      ≤ θ * g.gaussNorm norm c := by
    rw [gaussNorm_mul_of_isRestricted hc hQr htailr]
    calc (Qp : PowerSeries R).gaussNorm norm c
          * (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm norm c
        ≤ (Qp : PowerSeries R).gaussNorm norm c * (θ * f.gaussNorm norm c) :=
          mul_le_mul_of_nonneg_left hθf (PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
      _ = θ * ((Qp : PowerSeries R).gaussNorm norm c * f.gaussNorm norm c) := by ring
      _ ≤ θ * g.gaussNorm norm c :=
          mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hmax) hθ.le
  rw [hdefect]
  refine le_trans (PowerSeries.gaussNorm_add_le_max norm c _ _ hc.le norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm (hasGaussNorm_of_isRestricted hsmallr)
    (hasGaussNorm_of_isRestricted (PowerSeries.isRestricted.neg c hmulr)))
    (max_le hsmall ?_)
  have hneg : (-((Qp : PowerSeries R)
      * (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)))).gaussNorm norm c
      = ((Qp : PowerSeries R)
        * (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R))).gaussNorm norm c :=
    MvPowerSeries.gaussNorm_neg norm (fun _ ↦ c) (fun x ↦ norm_neg x) _
  rw [hneg]
  exact hmulbound

/-- **Weierstrass division** (Bosch–Güntzer–Remmert §5.2.1, Theorem 2). Over a complete
ultrametric normed commutative ring with multiplicative norm, a restricted series `f`
distinguished of degree `s` at a positive radius `c`, whose coefficient in degree `s` is a unit,
divides every restricted series `g`:

```text
g = q * f + r,    q restricted,    r a polynomial of degree less than s.
```

Over a field the unit condition is automatic, since a distinguished series has a nonzero
coefficient in its distinguished degree (`TauCeti.PowerSeries.IsDistinguished.coeff_ne_zero`).
Over a ring it cannot be dropped: a series distinguished of degree `0` whose constant coefficient
is not a unit does not divide `1` with zero remainder. The coefficient ring of interest is the
Tate algebra in fewer variables, over which the Tate algebra in one more variable is a ring of
restricted series. The decomposition is unique by
`TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_add_eq_mul_add`. -/
theorem IsDistinguished.exists_mul_add_eq [CompleteSpace R] (hf : IsDistinguished c s f)
    (hu : IsUnit (f.coeff s)) (hc : 0 < c) (hfr : f.IsRestricted c) (hg : g.IsRestricted c) :
    ∃ q r : PowerSeries R, q.IsRestricted c ∧ (∀ m, s ≤ m → r.coeff m = 0) ∧
      q * f + r = g := by
  have hfpos : 0 < f.gaussNorm norm c := hf.gaussNorm_pos
  obtain ⟨θ, hθ0, hθ1, hθf⟩ : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm norm c
        ≤ θ * f.gaussNorm norm c := by
    refine ⟨max (1 / 2) ((f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm
      norm c / f.gaussNorm norm c), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
      max_lt (by norm_num) ((div_lt_one hfpos).mpr (hf.gaussNorm_sub_trunc_lt hc hfr)), ?_⟩
    rw [← div_le_iff₀ hfpos]
    exact le_max_right _ _
  -- A choice of one division step at every restricted series, with contraction factor `θ`.
  have hstep : ∀ h : PowerSeries R, ∃ p : PowerSeries R × PowerSeries R, h.IsRestricted c →
      p.1.IsRestricted c ∧ (∀ m, s ≤ m → p.2.coeff m = 0) ∧
      p.1.gaussNorm norm c * f.gaussNorm norm c ≤ h.gaussNorm norm c ∧
      p.2.gaussNorm norm c ≤ h.gaussNorm norm c ∧
      (h - (p.1 * f + p.2)).gaussNorm norm c ≤ θ * h.gaussNorm norm c := by
    intro h
    by_cases hh : h.IsRestricted c
    · obtain ⟨q, r, h1, h2, h3, h4, h5⟩ :=
        exists_gaussNorm_sub_mul_add_le hf hu hc hfr hθ0 hθf hh
      exact ⟨(q, r), fun _ ↦ ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨(0, 0), fun hcon ↦ absurd hcon hh⟩
  choose F hF using hstep
  -- The sequence of successive defects.
  let G : ℕ → PowerSeries R := fun n ↦
    Nat.rec (motive := fun _ ↦ PowerSeries R) g (fun _ h ↦ h - ((F h).1 * f + (F h).2)) n
  have hG0 : G 0 = g := rfl
  have hGsucc : ∀ n, G (n + 1) = G n - ((F (G n)).1 * f + (F (G n)).2) := fun _ ↦ rfl
  have hGr : ∀ n, (G n).IsRestricted c := by
    intro n
    induction n with
    | zero => exact hg
    | succ n ih =>
      rw [hGsucc n, sub_eq_add_neg]
      exact PowerSeries.isRestricted.add c ih (PowerSeries.isRestricted.neg c
        (PowerSeries.isRestricted.add c (PowerSeries.isRestricted.mul c (hF (G n) ih).1 hfr)
          (isRestricted_of_forall_coeff_eq_zero (hF (G n) ih).2.1)))
  have hGn : ∀ n, (G n).gaussNorm norm c ≤ θ ^ n * g.gaussNorm norm c := by
    intro n
    induction n with
    | zero => simp [hG0]
    | succ n ih =>
      rw [hGsucc n]
      refine ((hF (G n) (hGr n)).2.2.2.2).trans ?_
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left ih hθ0.le
  -- The quotients and remainders produced along the way have geometrically small Gauss norms.
  have hgeo : Summable fun k : ℕ ↦ θ ^ k * g.gaussNorm norm c :=
    (summable_geometric_of_lt_one hθ0.le hθ1).mul_right _
  have hsQ : Summable fun k ↦ ((F (G k)).1).gaussNorm norm c := by
    refine Summable.of_nonneg_of_le
      (fun k ↦ PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg) (fun k ↦ ?_)
      (hgeo.div_const (f.gaussNorm norm c))
    rw [le_div_iff₀ hfpos]
    exact ((hF (G k) (hGr k)).2.2.1).trans (hGn k)
  have hsr : Summable fun k ↦ ((F (G k)).2).gaussNorm norm c :=
    Summable.of_nonneg_of_le (fun k ↦ PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
      (fun k ↦ ((hF (G k) (hGr k)).2.2.2.1).trans (hGn k)) hgeo
  -- Sum them coefficientwise; the defects tend to zero, so the sums telescope to `g`.
  set q : PowerSeries R := PowerSeries.mk fun i ↦ ∑' k, ((F (G k)).1).coeff i with hqdef
  set rr : PowerSeries R := PowerSeries.mk fun i ↦ ∑' k, ((F (G k)).2).coeff i with hrdef
  have hsumQ : ∀ i, HasSum (fun k ↦ ((F (G k)).1).coeff i) (q.coeff i) := fun i ↦ by
    rw [hqdef, PowerSeries.coeff_mk]
    exact (summable_coeff_of_summable_gaussNorm hc
      (fun k ↦ hasGaussNorm_of_isRestricted (hF (G k) (hGr k)).1) hsQ i).hasSum
  have hsumr : ∀ i, HasSum (fun k ↦ ((F (G k)).2).coeff i) (rr.coeff i) := fun i ↦ by
    rw [hrdef, PowerSeries.coeff_mk]
    exact (summable_coeff_of_summable_gaussNorm hc
      (fun k ↦ hasGaussNorm_of_isRestricted
        (isRestricted_of_forall_coeff_eq_zero (hF (G k) (hGr k)).2.1)) hsr i).hasSum
  refine ⟨q, rr, isRestricted_mk_tsum_coeff hc (fun k ↦ (hF (G k) (hGr k)).1) hsQ,
    fun m hm ↦ ?_, ?_⟩
  · have hz : (fun k ↦ ((F (G k)).2).coeff m) = fun _ : ℕ ↦ (0 : R) :=
      funext fun k ↦ (hF (G k) (hGr k)).2.1 m hm
    exact (hasSum_zero.unique (hz ▸ hsumr m)).symm
  · refine PowerSeries.ext fun n ↦ ?_
    have hmul : HasSum (fun k ↦ ((F (G k)).1 * f).coeff n) ((q * f).coeff n) := by
      have h := hasSum_sum (s := Finset.antidiagonal n)
        (f := fun p : ℕ × ℕ ↦ fun k ↦ ((F (G k)).1).coeff p.1 * f.coeff p.2)
        (a := fun p : ℕ × ℕ ↦ q.coeff p.1 * f.coeff p.2)
        (fun p _ ↦ (hsumQ p.1).mul_right (f.coeff p.2))
      simpa only [← PowerSeries.coeff_mul] using h
    have heq : (fun k ↦ (G k).coeff n - (G (k + 1)).coeff n)
        = fun k ↦ ((F (G k)).1 * f).coeff n + ((F (G k)).2).coeff n := by
      funext k
      rw [hGsucc k, map_sub, map_add]
      ring
    have hstepSum : HasSum (fun k ↦ (G k).coeff n - (G (k + 1)).coeff n)
        ((q * f + rr).coeff n) := by
      rw [heq, map_add]
      exact hmul.add (hsumr n)
    have hbound : ∀ m : ℕ, ‖(G m).coeff n‖ ≤ θ ^ m * g.gaussNorm norm c / c ^ n := fun m ↦ by
      rw [le_div_iff₀ (pow_pos hc n)]
      exact (PowerSeries.le_gaussNorm norm c _
        (hasGaussNorm_of_isRestricted (hGr m)) n).trans (hGn m)
    have hzero : Filter.Tendsto (fun m ↦ (G m).coeff n) Filter.atTop (nhds 0) :=
      squeeze_zero_norm hbound (by
        simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).mul_const
          (g.gaussNorm norm c)).div_const (c ^ n))
    have htel : HasSum (fun k ↦ (G k).coeff n - (G (k + 1)).coeff n) (g.coeff n) := by
      rw [hstepSum.summable.hasSum_iff_tendsto_nat]
      have hpartial : ∀ m : ℕ, (∑ k ∈ Finset.range m, ((G k).coeff n - (G (k + 1)).coeff n))
          = g.coeff n - (G m).coeff n := fun m ↦ by
        rw [Finset.sum_range_sub' (fun k ↦ (G k).coeff n) m, hG0]
      simp only [hpartial]
      simpa using tendsto_const_nhds.sub hzero
    exact hstepSum.unique htel

/-- **Weierstrass division** (Bosch–Güntzer–Remmert §5.2.1, Theorem 2), in its unique-existence
form: over a complete ultrametric normed commutative ring with multiplicative norm, a restricted
series `f` distinguished of degree `s` at a positive radius, whose coefficient in degree `s` is a
unit, divides every restricted series `g` in exactly one way, with a restricted quotient and a
remainder that is a polynomial of degree less than `s`. -/
theorem IsDistinguished.existsUnique_mul_add_eq [CompleteSpace R] (hf : IsDistinguished c s f)
    (hu : IsUnit (f.coeff s)) (hc : 0 < c) (hfr : f.IsRestricted c) (hg : g.IsRestricted c) :
    ∃! p : PowerSeries R × PowerSeries R,
      p.1.IsRestricted c ∧ (∀ m, s ≤ m → p.2.coeff m = 0) ∧ p.1 * f + p.2 = g := by
  obtain ⟨q, r, hq, hr, hqr⟩ := hf.exists_mul_add_eq hu hc hfr hg
  refine ⟨(q, r), ⟨hq, hr, hqr⟩, fun p ⟨h1, h2, h3⟩ ↦ ?_⟩
  obtain ⟨e1, e2⟩ := hf.eq_and_eq_of_mul_add_eq_mul_add hc h1 hq h2 hr (h3.trans hqr.symm)
  exact Prod.ext e1 e2

end NormedCommRing

section Subring

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [CompleteSpace R]
  {c : ℝ} {s : ℕ}

/-- **Weierstrass division inside the ring of restricted power series.** Over a complete
ultrametric normed commutative ring with multiplicative norm, a member `f` of the ring of series
restricted at a positive radius `c` which is distinguished of degree `s`, with a unit coefficient
in degree `s`, divides every member `g` with remainder:

```text
g = q * f + r,    r a polynomial of degree less than s,
```

with `q` and `r` again restricted at `c`; the remainder `r` is in general nonzero. This is
`TauCeti.PowerSeries.IsDistinguished.exists_mul_add_eq` read in the ring of restricted series,
which is the form ideal-theoretic arguments use. The pair `(q, r)` is unique, by
`TauCeti.PowerSeries.IsDistinguished.existsUnique_mul_add_eq_subring`. -/
theorem IsDistinguished.exists_mul_add_eq_subring (hc : 0 < c)
    {f : PowerSeries.IsRestricted.subring (R := R) c}
    (hf : IsDistinguished c s (f : PowerSeries R)) (hu : IsUnit ((f : PowerSeries R).coeff s))
    (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ∃ q r : PowerSeries.IsRestricted.subring (R := R) c,
      (∀ m, s ≤ m → (r : PowerSeries R).coeff m = 0) ∧ q * f + r = g := by
  obtain ⟨q, r, hq, hr, hqr⟩ := hf.exists_mul_add_eq hu hc f.2 g.2
  -- the coercion of a sum and of a product in a subring reduces to the sum and product of the
  -- coercions, so `hqr` is literally the required equation of underlying series
  exact ⟨⟨q, hq⟩, ⟨r, isRestricted_of_forall_coeff_eq_zero hr⟩, hr, Subtype.ext hqr⟩

/-- **Weierstrass division inside the ring of restricted power series is unique.** The quotient and
remainder of `TauCeti.PowerSeries.IsDistinguished.exists_mul_add_eq_subring` are the only ones: a
member `g` of the ring of series restricted at a positive radius `c` is written as `q * f + r`,
with `r` a polynomial of degree less than the distinguished degree `s` of `f`, in exactly one way.
This is `TauCeti.PowerSeries.IsDistinguished.existsUnique_mul_add_eq` read in that ring. -/
theorem IsDistinguished.existsUnique_mul_add_eq_subring (hc : 0 < c)
    {f : PowerSeries.IsRestricted.subring (R := R) c}
    (hf : IsDistinguished c s (f : PowerSeries R)) (hu : IsUnit ((f : PowerSeries R).coeff s))
    (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ∃! p : PowerSeries.IsRestricted.subring (R := R) c ×
        PowerSeries.IsRestricted.subring (R := R) c,
      (∀ m, s ≤ m → (p.2 : PowerSeries R).coeff m = 0) ∧ p.1 * f + p.2 = g := by
  obtain ⟨q, r, hr, hqr⟩ := hf.exists_mul_add_eq_subring hc hu g
  refine ⟨(q, r), ⟨hr, hqr⟩, fun p ⟨h2, h3⟩ ↦ ?_⟩
  -- the coercions of the two decompositions are equations of underlying series, to which the
  -- uniqueness of Weierstrass division applies
  have hcoe : (p.1 : PowerSeries R) * (f : PowerSeries R) + (p.2 : PowerSeries R)
      = (q : PowerSeries R) * (f : PowerSeries R) + (r : PowerSeries R) := by
    have := congrArg (Subtype.val (p := (· ∈ PowerSeries.IsRestricted.subring (R := R) c)))
      (h3.trans hqr.symm)
    simpa using this
  obtain ⟨e1, e2⟩ := hf.eq_and_eq_of_mul_add_eq_mul_add hc p.1.2 q.2 h2 hr hcoe
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

end Subring

end TauCeti.PowerSeries
