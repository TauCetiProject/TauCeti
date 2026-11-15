/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.GaussNorm
import TauCeti.RingTheory.PowerSeries.HasseDeriv.Eval
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Division
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# The Schwarz lemma for restricted and bounded power series

Let `K` be a complete ultrametric normed field and `f = ∑ aₙ Xⁿ` a power series over `K` restricted
at a radius `c > 0`, so that `‖aₙ‖ cⁿ → 0` and `f` converges on the closed disc `‖x‖ ≤ c`. A zero
`a` of `f` in that disc splits off a linear factor without loss of norm:

```text
f = (X - a) * q,    q restricted at c,    ‖f‖_c = c * ‖q‖_c
```

for the Gauss norm `‖·‖_c`, by Weierstrass division by the distinguished polynomial `X - a`
(`TauCeti.PowerSeries.gaussNorm_X_sub_C_mul`).
Peeling off the zeros one at a time, counted with the multiplicity read off from the Hasse
derivatives `D⁽ᵗ⁾ f`, gives the nonarchimedean **Schwarz lemma**: if the points `b` of a finite
multiset `Z` in the closed disc of radius `c` satisfy `(D⁽ᵗ⁾ f)(b) = 0` for every `t` less than
the multiplicity of `b` in `Z`, then at every point `x` of the closed disc of radius `c`, in any
complete normed field extension of `K`,

```text
‖f(x)‖ ≤ ‖f‖_c * ∏_{b ∈ Z} ‖x - b‖ / c.
```

Unlike the archimedean Schwarz lemma there is no change of radius: every factor `‖x - b‖ / c` is
at most `1`, and the bound is sharp for `f = ∏ (X - b)`.

This is the analytic estimate behind the interpolation and extrapolation steps of the method of
linear forms in `p`-adic logarithms: an auxiliary function with many zeros of high multiplicity at
the points of a grid is small at every other point of the disc. For distinct points with
prescribed multiplicities it takes the form
`‖f(x)‖ ≤ ‖f‖_c * ∏_{b ∈ s} (‖x - b‖ / c) ^ T b`. Since `D⁽ᵏ⁾ f` is again restricted at `c`, with
`‖D⁽ᵏ⁾ f‖_c ≤ c⁻ᵏ ‖f‖_c`, and vanishes at each `b` to order `T b - k`, the same bound with
exponents `T b - k` and an extra factor `c⁻ᵏ` holds for the Hasse derivatives of `f`. This is the
form the extrapolation steps use, where vanishing of `f` to high order on a grid controls the
derivatives of lower order at new points.

When all zeros lie in a smaller closed disc of radius `s` (`0 ≤ s ≤ r`, `0 < r`), comparing the
Gauss norms of each peeled factor `X - a` at the two radii `s` and `r` contracts the Gauss norm of
`f` itself over any complete ultrametric normed commutative ring without zero divisors (with
`‖1‖ = 1`):

```text
‖f‖_s ≤ ‖f‖_r * (s / r) ^ Z.card.
```

Approximating `r` from below by radii `r' ∈ (s, r)`, at which bounded weighted coefficients force
restrictedness (`PowerSeries.HasGaussNorm.isRestricted_of_abs_lt`), extends this contraction to
every series with `HasGaussNorm norm r`, even when `f` is not restricted at `r`. Over a complete
ultrametric normed field of characteristic zero, where iterated formal derivatives `d⁄dX^[j] f` and
Hasse derivatives have the same zeros, specializing to `s = 1 < r` bounds every coefficient and
every unit-disc value of `f` by `M * (r ^ (A.card * S))⁻¹` whenever `‖coeff k f‖ * r ^ k ≤ M` and
the first `S` formal derivatives vanish on `A`.

## Main results

* `PowerSeries.IsRestricted.evalAt_eq_zero_iff`: the factor theorem for restricted series, over
  any complete ultrametric normed commutative ring.
* `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_prod`: the Schwarz lemma for a multiset
  of zeros.
* `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_prod_pow`: the Schwarz lemma for distinct
  zeros with multiplicities.
* `PowerSeries.IsRestricted.norm_evalAt_hasseDeriv_le_gaussNorm_mul_prod_pow`: the Schwarz lemma
  for the Hasse derivatives `D⁽ᵏ⁾ f`, whose zeros have multiplicities reduced by `k`.
* `PowerSeries.IsRestricted.gaussNorm_le_gaussNorm_mul_div_pow`,
  `PowerSeries.HasGaussNorm.gaussNorm_le_gaussNorm_mul_div_pow`,
  `PowerSeries.IsRestricted.gaussNorm_le_gaussNorm_mul_div_pow_sum`,
  `PowerSeries.HasGaussNorm.gaussNorm_le_gaussNorm_mul_div_pow_sum`,
  `PowerSeries.IsRestricted.gaussNorm_hasseDeriv_le_gaussNorm_mul_div_pow_sum` and
  `PowerSeries.HasGaussNorm.gaussNorm_hasseDeriv_le_gaussNorm_mul_div_pow_sum`: two-radii
  Gauss-norm contraction from zeros in a smaller closed disc, for restricted and bounded series and
  their Hasse derivatives over complete ultrametric normed commutative rings without zero divisors.
* `PowerSeries.gaussNorm_le_mul_div_pow_sum_of_ofScalarsSum_iterate_derivative_eq_zero`,
  `PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` and
  `PowerSeries.norm_ofScalarsSum_le_of_ofScalarsSum_iterate_derivative_eq_zero`: in characteristic
  zero, vanishing of iterated formal derivatives forces small Gauss norm, coefficients and values.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1 (Weierstrass division).
* A. Baker, *Transcendental Number Theory*, Cambridge University Press, 1975, Chapter 2,
  Lemmas 4 and 5.
* M. Karatarakis, `mkaratarakis/mathlib4`, branch `baker-padic` (`65cdef5722`,
  `Mathlib/NumberTheory/Transcendental/Baker/Padic/Series.lean`), for a formal-sequence version of
  the unit-disc coefficient estimate at natural-number points.
-/

public section

open scoped Topology
open TauCeti.PowerSeries

namespace PowerSeries

section CommRing

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  {c : ℝ} {f : PowerSeries R}

/-- **Factor theorem for restricted series.** Over a complete ultrametric normed commutative ring,
a series restricted at a radius `c > 0` vanishes at a point `a` of the closed disc of radius `c`
exactly when it is `X - a` times a series restricted at `c`. -/
theorem IsRestricted.evalAt_eq_zero_iff (hf : f.IsRestricted c) (hc : 0 < c) {a : R}
    (ha : ‖a‖ ≤ c) :
    f.evalAt a = 0 ↔ ∃ q : PowerSeries R, q.IsRestricted c ∧ f = (X - C a) * q := by
  have hX := isRestricted_X_sub_C (c := c) a
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · obtain ⟨q, r, hq, hr, hqr⟩ := (isMulDistinguished_X_sub_C hc ha).exists_mul_add_eq hc hX hf
    -- the remainder `r` has degree less than `1`, and its value at `a` is `f(a) = 0`
    have hrC : r = C (constantCoeff r) := by
      ext n
      rcases n with _ | n
      · simp
      · simp [hr (n + 1) (by omega)]
    have hr0 : constantCoeff r = 0 := by
      have hrr : r.IsRestricted c := by rw [hrC]; exact isRestricted_C c _
      rw [← hqr, IsRestricted.evalAt_add (hX.mul hq) hrr ha, hX.evalAt_mul hq ha, evalAt_X_sub_C,
        hrC, evalAt_C] at h0
      simpa using h0
    exact ⟨q, hq, by rw [← hqr, hrC, hr0, map_zero, add_zero]⟩
  · rintro ⟨q, hq, rfl⟩
    rw [hX.evalAt_mul hq ha, evalAt_X_sub_C]
    simp

variable [NoZeroDivisors R] {q : PowerSeries R}

omit [NormOneClass R] in
/-- Splitting off a zero `a` keeps the vanishing conditions at the other points: if `f = (X - a) q`
and the Hasse derivatives of `f` of order less than the multiplicity of each point in `a ::ₘ Z`
vanish there, then those of `q` of order less than the multiplicity in `Z` vanish. -/
private theorem IsRestricted.evalAt_hasseDeriv_eq_zero_of_X_sub_C_mul [DecidableEq R]
    (hq : q.IsRestricted c) {a : R} {Z : Multiset R} (hZ : ∀ b ∈ a ::ₘ Z, ‖b‖ ≤ c)
    (hzero : ∀ b ∈ a ::ₘ Z, ∀ t < (a ::ₘ Z).count b,
      (PowerSeries.hasseDeriv t ((X - C a) * q)).evalAt b = 0) :
    ∀ b ∈ Z, ∀ t < Z.count b, (PowerSeries.hasseDeriv t q).evalAt b = 0 := by
  intro b hb t ht
  have hbc := hZ b (Multiset.mem_cons_of_mem hb)
  have hstep := hq.evalAt_hasseDeriv_succ_X_sub_C_mul a hbc
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hstep
  by_cases hba : b = a
  · -- at `a` itself the order drops by one: `(D⁽ᵗ⁾ q)(a) = (D⁽ᵗ⁺¹⁾ f)(a)`
    subst hba
    have h := hzero b (Multiset.mem_cons_self b Z) (t + 1) (by simpa using ht)
    rwa [hstep, sub_self, zero_mul, zero_add] at h
  · -- at another point the order is kept, since `b - a ≠ 0`
    have hcount : (a ::ₘ Z).count b = Z.count b := Multiset.count_cons_of_ne hba Z
    have hba' : b - a ≠ 0 := sub_ne_zero.mpr hba
    induction t with
    | zero =>
      have h := hzero b (Multiset.mem_cons_of_mem hb) 0 (by omega)
      rw [hasseDeriv_zero, LinearMap.id_apply, (isRestricted_X_sub_C a).evalAt_mul hq hbc,
        evalAt_X_sub_C, Algebra.algebraMap_self, RingHom.id_apply] at h
      simpa [hba'] using h
    | succ t ih =>
      have h := hzero b (Multiset.mem_cons_of_mem hb) (t + 1) (by omega)
      rw [hstep, ih (by omega), add_zero] at h
      simpa [hba'] using h

end CommRing

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {c : ℝ}
  {f : PowerSeries K}

/-- **The Schwarz lemma for restricted series.** Let `f` be a power series over a complete
ultrametric normed field `K`, restricted at a radius `c > 0`. Let `Z` be a finite multiset of
points of the closed disc of radius `c` such that `f` vanishes at each `b ∈ Z` to at least the
multiplicity of `b` in `Z`, in the sense that the Hasse derivatives `(D⁽ᵗ⁾ f)(b)` vanish for `t`
below that multiplicity. Then at every point `x` of the closed disc of radius `c` in a complete
normed field extension `L` of `K`,

```text
‖f(x)‖ ≤ ‖f‖_c * ∏_{b ∈ Z} ‖x - b‖ / c,
```

where `‖f‖_c` is the Gauss norm of `f` at `c`. -/
theorem IsRestricted.norm_evalAt_le_gaussNorm_mul_prod [DecidableEq K] {L : Type*}
    [NormedField L] [NormedAlgebra K L] [CompleteSpace L] (hf : f.IsRestricted c) (hc : 0 < c)
    {Z : Multiset K} (hZ : ∀ b ∈ Z, ‖b‖ ≤ c)
    (hzero : ∀ b ∈ Z, ∀ t < Z.count b, (PowerSeries.hasseDeriv t f).evalAt b = 0)
    {x : L} (hx : ‖x‖ ≤ c) :
    ‖f.evalAt x‖ ≤ f.gaussNorm norm c * (Z.map fun b ↦ ‖x - algebraMap K L b‖ / c).prod := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  induction Z using Multiset.induction_on generalizing f with
  | empty => simpa using norm_evalAt_le_gaussNorm (hasGaussNorm_of_isRestricted hf) hx
  | cons a Z ih =>
    have ha := hZ a (Multiset.mem_cons_self a Z)
    have hfa : f.evalAt a = 0 := by
      simpa using hzero a (Multiset.mem_cons_self a Z) 0 (by simp)
    obtain ⟨q, hq, rfl⟩ := (hf.evalAt_eq_zero_iff hc ha).mp hfa
    have hqZ := ih hq (fun b hb ↦ hZ b (Multiset.mem_cons_of_mem hb))
      (hq.evalAt_hasseDeriv_eq_zero_of_X_sub_C_mul hZ hzero)
    rw [(isRestricted_X_sub_C a).evalAt_mul hq hx, evalAt_X_sub_C, norm_mul,
      gaussNorm_X_sub_C_mul hc ha hq, Multiset.map_cons, Multiset.prod_cons]
    calc ‖x - algebraMap K L a‖ * ‖q.evalAt x‖
        ≤ ‖x - algebraMap K L a‖ *
          (q.gaussNorm norm c * (Z.map fun b ↦ ‖x - algebraMap K L b‖ / c).prod) := by
          gcongr
      _ = c * q.gaussNorm norm c *
          (‖x - algebraMap K L a‖ / c * (Z.map fun b ↦ ‖x - algebraMap K L b‖ / c).prod) := by
          field_simp

/-- **The Schwarz lemma for distinct zeros with multiplicities.** Let `f` be a power series over a
complete ultrametric normed field `K`, restricted at a radius `c > 0`, and let `s` be a finite set
of points of the closed disc of radius `c` at each of which the Hasse derivatives `(D⁽ᵗ⁾ f)(b)`
vanish for `t < T b`. Then at every point `x` of the closed disc of radius `c` in a complete normed
field extension `L` of `K`,

```text
‖f(x)‖ ≤ ‖f‖_c * ∏_{b ∈ s} (‖x - b‖ / c) ^ T b.
``` -/
theorem IsRestricted.norm_evalAt_le_gaussNorm_mul_prod_pow {L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] (hf : f.IsRestricted c) (hc : 0 < c) {s : Finset K}
    {T : K → ℕ} (hs : ∀ b ∈ s, ‖b‖ ≤ c)
    (hzero : ∀ b ∈ s, ∀ t < T b, (PowerSeries.hasseDeriv t f).evalAt b = 0)
    {x : L} (hx : ‖x‖ ≤ c) :
    ‖f.evalAt x‖ ≤ f.gaussNorm norm c * ∏ b ∈ s, (‖x - algebraMap K L b‖ / c) ^ T b := by
  classical
  set Z : Multiset K := ∑ b ∈ s, Multiset.replicate (T b) b
  have hmem {b : K} (hb : b ∈ Z) : b ∈ s := by
    obtain ⟨b', hb', hbb'⟩ := Multiset.mem_sum.mp hb
    rwa [Multiset.eq_of_mem_replicate hbb']
  have hcount {b : K} (hb : b ∈ s) : Z.count b = T b := by
    rw [Multiset.count_sum', Finset.sum_eq_single b
      (fun b' _ hb' ↦ Multiset.count_eq_zero.mpr fun h ↦ hb' (Multiset.eq_of_mem_replicate h).symm)
      (fun h ↦ (h hb).elim), Multiset.count_replicate_self]
  have h := hf.norm_evalAt_le_gaussNorm_mul_prod hc (Z := Z) (fun b hb ↦ hs b (hmem hb))
    (fun b hb t ht ↦ hzero b (hmem hb) t (hcount (hmem hb) ▸ ht)) hx
  have hprod : (Z.map fun b ↦ ‖x - algebraMap K L b‖ / c).prod =
      ∏ b ∈ s, (‖x - algebraMap K L b‖ / c) ^ T b := by
    rw [← Multiset.coe_mapAddMonoidHom, map_sum, Multiset.prod_sum]
    simp
  rwa [hprod] at h

/-- **The Schwarz lemma for Hasse derivatives.** Let `f` be a power series over a complete
ultrametric normed field `K`, restricted at a radius `c > 0`, and let `s` be a finite set of points
of the closed disc of radius `c` at each of which the Hasse derivatives `(D⁽ᵗ⁾ f)(b)` vanish for
`t < T b`. Then for every `k` and every point `x` of the closed disc of radius `c` in a complete
normed field extension `L` of `K`,

```text
‖(D⁽ᵏ⁾ f)(x)‖ ≤ c⁻ᵏ * ‖f‖_c * ∏_{b ∈ s} (‖x - b‖ / c) ^ (T b - k).
```

For `k = 0` this is `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_prod_pow`. -/
theorem IsRestricted.norm_evalAt_hasseDeriv_le_gaussNorm_mul_prod_pow {L : Type*}
    [NormedField L] [NormedAlgebra K L] [CompleteSpace L] (hf : f.IsRestricted c) (hc : 0 < c)
    {s : Finset K} {T : K → ℕ} (hs : ∀ b ∈ s, ‖b‖ ≤ c)
    (hzero : ∀ b ∈ s, ∀ t < T b, (PowerSeries.hasseDeriv t f).evalAt b = 0) (k : ℕ)
    {x : L} (hx : ‖x‖ ≤ c) :
    ‖(PowerSeries.hasseDeriv k f).evalAt x‖ ≤
      c⁻¹ ^ k * f.gaussNorm norm c * ∏ b ∈ s, (‖x - algebraMap K L b‖ / c) ^ (T b - k) := by
  -- `D⁽ᵏ⁾ f` vanishes to order `T b - k` at each `b ∈ s`
  have hzero' : ∀ b ∈ s, ∀ t < T b - k,
      (PowerSeries.hasseDeriv t (PowerSeries.hasseDeriv k f)).evalAt b = 0 := fun b hb t ht ↦ by
    rw [hf.evalAt_hasseDeriv_hasseDeriv (hs b hb), hzero b hb _ (by omega), smul_zero]
  have h := (hf.hasseDeriv k).norm_evalAt_le_gaussNorm_mul_prod_pow (L := L) hc hs hzero' hx
  have hk := gaussNorm_hasseDeriv_le (R := K) hc (hasGaussNorm_of_isRestricted hf) k
  exact h.trans <| mul_le_mul_of_nonneg_right hk (Finset.prod_nonneg fun _ _ ↦ by positivity)

end Field

section NoZeroDivisors

variable {R : Type*} [NormedCommRing R] [NoZeroDivisors R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] {f : PowerSeries R}

/-- **Two-radii Gauss-norm contraction for restricted series.** Let `f` be a power series over a
complete ultrametric normed commutative ring `R` without zero divisors (with `‖1‖ = 1`), restricted
at a radius `r > 0`, and let `0 ≤ s ≤ r`. If `Z` is a finite multiset of points of the closed disc
of radius `s` at each of which the Hasse derivatives `(D⁽ᵗ⁾ f)(b)` vanish for `t` below the
multiplicity of `b` in `Z`, then

```text
‖f‖_s ≤ ‖f‖_r * (s / r) ^ Z.card.
``` -/
theorem IsRestricted.gaussNorm_le_gaussNorm_mul_div_pow [DecidableEq R] {r s : ℝ}
    (hf : f.IsRestricted r) (hr : 0 < r) (hs0 : 0 ≤ s) (hsr : s ≤ r) {Z : Multiset R}
    (hZ : ∀ b ∈ Z, ‖b‖ ≤ s)
    (hzero : ∀ b ∈ Z, ∀ t < Z.count b, (PowerSeries.hasseDeriv t f).evalAt b = 0) :
    f.gaussNorm norm s ≤ f.gaussNorm norm r * (s / r) ^ Z.card := by
  induction Z using Multiset.induction_on generalizing f with
  | empty =>
    simpa using gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _) hs0 hsr
      (hasGaussNorm_of_isRestricted hf)
  | cons a Z ih =>
    have ha : ‖a‖ ≤ s := hZ a (Multiset.mem_cons_self a Z)
    have hfa : f.evalAt a = 0 := by
      simpa using hzero a (Multiset.mem_cons_self a Z) 0 (by simp)
    obtain ⟨q, hq, rfl⟩ := (hf.evalAt_eq_zero_iff hr (ha.trans hsr)).mp hfa
    have hqZ := ih hq (fun b hb ↦ hZ b (Multiset.mem_cons_of_mem hb))
      (hq.evalAt_hasseDeriv_eq_zero_of_X_sub_C_mul (fun b hb ↦ (hZ b hb).trans hsr) hzero)
    rw [gaussNorm_X_sub_C_mul hr (ha.trans hsr) hq, Multiset.card_cons, pow_succ]
    rcases hs0.eq_or_lt with rfl | hs
    · obtain rfl : a = 0 := norm_le_zero_iff.mp ha
      simp only [zero_div, mul_zero, map_zero, sub_zero, gaussNorm_eq]
      refine Real.iSup_le (fun n ↦ ?_) le_rfl
      rcases n with _ | n <;> simp
    · have hqs : q.IsRestricted s :=
        isRestricted_of_abs_le hq (by rwa [abs_of_pos hs, abs_of_pos hr])
      rw [gaussNorm_X_sub_C_mul hs ha hqs]
      calc s * q.gaussNorm norm s
          ≤ s * (q.gaussNorm norm r * (s / r) ^ Z.card) := by gcongr
        _ = r * q.gaussNorm norm r * ((s / r) ^ Z.card * (s / r)) := by field_simp

/-- **Two-radii Gauss-norm contraction for bounded series.** Let `f` be a power series over a
complete ultrametric normed commutative ring `R` without zero divisors (with `‖1‖ = 1`), with
bounded weighted coefficient norms at a radius `r > 0`, and let `0 ≤ s ≤ r`. If `Z` is a finite
multiset of points of the closed disc of radius `s` at each of which the Hasse derivatives
`(D⁽ᵗ⁾ f)(b)` vanish for `t` below the multiplicity of `b` in `Z`, then

```text
‖f‖_s ≤ ‖f‖_r * (s / r) ^ Z.card.
```

The series `f` need not be restricted at `r`: for `s < r` it is restricted at every intermediate
radius `r' ∈ (s, r)`. -/
theorem HasGaussNorm.gaussNorm_le_gaussNorm_mul_div_pow [DecidableEq R] {r s : ℝ}
    (hf : f.HasGaussNorm norm r) (hr : 0 < r) (hs0 : 0 ≤ s) (hsr : s ≤ r) {Z : Multiset R}
    (hZ : ∀ b ∈ Z, ‖b‖ ≤ s)
    (hzero : ∀ b ∈ Z, ∀ t < Z.count b, (PowerSeries.hasseDeriv t f).evalAt b = 0) :
    f.gaussNorm norm s ≤ f.gaussNorm norm r * (s / r) ^ Z.card := by
  rcases hsr.eq_or_lt with rfl | hlt
  · simp [div_self hr.ne']
  · have htend : Filter.Tendsto (fun r' : ℝ ↦ f.gaussNorm norm r * (s / r') ^ Z.card) (𝓝[<] r)
        (𝓝 (f.gaussNorm norm r * (s / r) ^ Z.card)) :=
      (((tendsto_const_nhds.div Filter.tendsto_id hr.ne').pow Z.card).const_mul _).mono_left
        nhdsWithin_le_nhds
    refine ge_of_tendsto htend (Filter.eventually_of_mem (Ioo_mem_nhdsLT hlt) fun r' hr' ↦ ?_)
    have hr'0 : 0 < r' := hs0.trans_lt hr'.1
    have hfr' : f.IsRestricted r' :=
      hf.isRestricted_of_abs_lt (by rw [abs_of_pos hr'0]; exact hr'.2)
    have hgr' : f.gaussNorm norm r' ≤ f.gaussNorm norm r :=
      gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _) hr'0.le hr'.2.le hf
    exact (hfr'.gaussNorm_le_gaussNorm_mul_div_pow hr'0 hs0 hr'.1.le hZ hzero).trans
      (mul_le_mul_of_nonneg_right hgr' (by positivity))

/-- **Two-radii Gauss-norm contraction for distinct zeros with multiplicities.** Let `f` be a
power series over a complete ultrametric normed commutative ring `R` without zero divisors (with
`‖1‖ = 1`), with bounded weighted coefficient norms at a radius `r > 0`, let `0 ≤ s ≤ r`, and let
`A` be a finite set of points of the closed disc of radius `s` at each of which `(D⁽ᵗ⁾ f)(b)`
vanishes for `t < T b`. Then

```text
‖f‖_s ≤ ‖f‖_r * (s / r) ^ ∑_{b ∈ A} T b.
``` -/
theorem HasGaussNorm.gaussNorm_le_gaussNorm_mul_div_pow_sum {r s : ℝ}
    (hf : f.HasGaussNorm norm r) (hr : 0 < r) (hs0 : 0 ≤ s) (hsr : s ≤ r)
    {A : Finset R} {T : R → ℕ} (hA : ∀ b ∈ A, ‖b‖ ≤ s)
    (hzero : ∀ b ∈ A, ∀ t < T b, (PowerSeries.hasseDeriv t f).evalAt b = 0) :
    f.gaussNorm norm s ≤ f.gaussNorm norm r * (s / r) ^ ∑ b ∈ A, T b := by
  classical
  set Z : Multiset R := ∑ b ∈ A, Multiset.replicate (T b) b
  have hmem {b : R} (hb : b ∈ Z) : b ∈ A := by
    obtain ⟨b', hb', hbb'⟩ := Multiset.mem_sum.mp hb
    rwa [Multiset.eq_of_mem_replicate hbb']
  have hcount {b : R} (hb : b ∈ A) : Z.count b = T b := by
    rw [Multiset.count_sum', Finset.sum_eq_single b
      (fun b' _ hb' ↦ Multiset.count_eq_zero.mpr fun h ↦ hb' (Multiset.eq_of_mem_replicate h).symm)
      (fun h ↦ (h hb).elim), Multiset.count_replicate_self]
  have hcard : Z.card = ∑ b ∈ A, T b := by simp [Z]
  simpa [hcard] using hf.gaussNorm_le_gaussNorm_mul_div_pow hr hs0 hsr
    (fun b hb ↦ hA b (hmem hb)) (fun b hb t ht ↦ hzero b (hmem hb) t (hcount (hmem hb) ▸ ht))

/-- **Two-radii Gauss-norm contraction for restricted series and distinct zeros.** Specialization
of `PowerSeries.HasGaussNorm.gaussNorm_le_gaussNorm_mul_div_pow_sum` to restricted series. -/
theorem IsRestricted.gaussNorm_le_gaussNorm_mul_div_pow_sum {r s : ℝ}
    (hf : f.IsRestricted r) (hr : 0 < r) (hs0 : 0 ≤ s) (hsr : s ≤ r)
    {A : Finset R} {T : R → ℕ} (hA : ∀ b ∈ A, ‖b‖ ≤ s)
    (hzero : ∀ b ∈ A, ∀ t < T b, (PowerSeries.hasseDeriv t f).evalAt b = 0) :
    f.gaussNorm norm s ≤ f.gaussNorm norm r * (s / r) ^ ∑ b ∈ A, T b :=
  (hasGaussNorm_of_isRestricted hf).gaussNorm_le_gaussNorm_mul_div_pow_sum hr hs0 hsr hA hzero

/-- **Two-radii Gauss-norm contraction for Hasse derivatives of restricted series.** Let `f` be a
power series over a complete ultrametric normed commutative ring `R` without zero divisors (with
`‖1‖ = 1`), restricted at a radius `r > 0`, let `0 ≤ s ≤ r`, and let `A` be a finite set of points
of the closed disc of radius `s` at each of which `(D⁽ᵗ⁾ f)(b)` vanishes for `t < T b`. Then for
every `k`

```text
‖D⁽ᵏ⁾ f‖_s ≤ r⁻ᵏ * ‖f‖_r * (s / r) ^ ∑_{b ∈ A} (T b - k).
``` -/
theorem IsRestricted.gaussNorm_hasseDeriv_le_gaussNorm_mul_div_pow_sum {r s : ℝ}
    (hf : f.IsRestricted r) (hr : 0 < r) (hs0 : 0 ≤ s) (hsr : s ≤ r)
    {A : Finset R} {T : R → ℕ} (hA : ∀ b ∈ A, ‖b‖ ≤ s)
    (hzero : ∀ b ∈ A, ∀ t < T b, (PowerSeries.hasseDeriv t f).evalAt b = 0) (k : ℕ) :
    (PowerSeries.hasseDeriv k f).gaussNorm norm s ≤
      r⁻¹ ^ k * f.gaussNorm norm r * (s / r) ^ ∑ b ∈ A, (T b - k) := by
  have hzero' : ∀ b ∈ A, ∀ t < T b - k,
      (PowerSeries.hasseDeriv t (PowerSeries.hasseDeriv k f)).evalAt b = 0 := fun b hb t ht ↦ by
    rw [hf.evalAt_hasseDeriv_hasseDeriv ((hA b hb).trans hsr), hzero b hb _ (by omega), smul_zero]
  have h := (hf.hasseDeriv k).gaussNorm_le_gaussNorm_mul_div_pow_sum hr hs0 hsr hA hzero'
  have hk := gaussNorm_hasseDeriv_le (R := R) hr (hasGaussNorm_of_isRestricted hf) k
  exact h.trans (mul_le_mul_of_nonneg_right hk (by positivity))

/-- **Two-radii Gauss-norm contraction for Hasse derivatives.** Let `f` be a power series over a
complete ultrametric normed commutative ring `R` without zero divisors (with `‖1‖ = 1`), with
bounded weighted coefficient norms at a radius `r > 0`, let `0 ≤ s ≤ r`, and let `A` be a finite
set of points of the closed disc of radius `s` at each of which `(D⁽ᵗ⁾ f)(b)` vanishes for
`t < T b`. Then for every `k`

```text
‖D⁽ᵏ⁾ f‖_s ≤ r⁻ᵏ * ‖f‖_r * (s / r) ^ ∑_{b ∈ A} (T b - k).
``` -/
theorem HasGaussNorm.gaussNorm_hasseDeriv_le_gaussNorm_mul_div_pow_sum {r s : ℝ}
    (hf : f.HasGaussNorm norm r) (hr : 0 < r) (hs0 : 0 ≤ s) (hsr : s ≤ r)
    {A : Finset R} {T : R → ℕ} (hA : ∀ b ∈ A, ‖b‖ ≤ s)
    (hzero : ∀ b ∈ A, ∀ t < T b, (PowerSeries.hasseDeriv t f).evalAt b = 0) (k : ℕ) :
    (PowerSeries.hasseDeriv k f).gaussNorm norm s ≤
      r⁻¹ ^ k * f.gaussNorm norm r * (s / r) ^ ∑ b ∈ A, (T b - k) := by
  rcases hsr.eq_or_lt with rfl | hlt
  · simpa [div_self hr.ne'] using gaussNorm_hasseDeriv_le (R := R) hr hf k
  · have htend : Filter.Tendsto
        (fun r' : ℝ ↦ r'⁻¹ ^ k * f.gaussNorm norm r * (s / r') ^ ∑ b ∈ A, (T b - k)) (𝓝[<] r)
        (𝓝 (r⁻¹ ^ k * f.gaussNorm norm r * (s / r) ^ ∑ b ∈ A, (T b - k))) :=
      ((((Filter.tendsto_id.inv₀ hr.ne').pow k).mul_const _).mul
        ((tendsto_const_nhds.div Filter.tendsto_id hr.ne').pow _)).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend (Filter.eventually_of_mem (Ioo_mem_nhdsLT hlt) fun r' hr' ↦ ?_)
    have hr'0 : 0 < r' := hs0.trans_lt hr'.1
    have hfr' : f.IsRestricted r' :=
      hf.isRestricted_of_abs_lt (by rw [abs_of_pos hr'0]; exact hr'.2)
    have hgr' : f.gaussNorm norm r' ≤ f.gaussNorm norm r :=
      gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _) hr'0.le hr'.2.le hf
    exact (hfr'.gaussNorm_hasseDeriv_le_gaussNorm_mul_div_pow_sum hr'0 hs0 hr'.1.le hA hzero
      k).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgr' (by positivity)) (by positivity))

end NoZeroDivisors

section CharZero

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]

/-- **Two-radii Gauss-norm contraction from iterated formal derivatives.** Over a complete
ultrametric normed field `K` of characteristic zero, if `‖coeff k f‖ * r ^ k ≤ M` for all `k` at a
radius `r > 0`, `0 ≤ s ≤ r`, and at each point `a` of a finite set `A` in the closed disc of radius
`s` the values of the iterated formal derivatives of `f` of order `< T a` (evaluated via
`FormalMultilinearSeries.ofScalarsSum`) vanish, then

```text
‖f‖_s ≤ M * (s / r) ^ ∑_{a ∈ A} T a.
``` -/
theorem gaussNorm_le_mul_div_pow_sum_of_ofScalarsSum_iterate_derivative_eq_zero
    {f : PowerSeries K} {r s M : ℝ} (hr : 0 < r) (hs0 : 0 ≤ s) (hsr : s ≤ r)
    (hM : ∀ k, ‖coeff k f‖ * r ^ k ≤ M) (A : Finset K) {T : K → ℕ}
    (hA : ∀ a ∈ A, ‖a‖ ≤ s)
    (hvan : ∀ a ∈ A, ∀ j < T a, FormalMultilinearSeries.ofScalarsSum (E := K)
      (fun k ↦ coeff k ((⇑(derivative (R := K)))^[j] f)) a = 0) :
    f.gaussNorm norm s ≤ M * (s / r) ^ ∑ a ∈ A, T a := by
  have hM0 : 0 ≤ M := (by positivity : 0 ≤ ‖coeff 0 f‖ * r ^ 0).trans (hM 0)
  have hf : f.HasGaussNorm norm r := ⟨M, Set.forall_mem_range.mpr hM⟩
  have hfr : f.gaussNorm norm r ≤ M := by
    rw [gaussNorm_eq]
    exact Real.iSup_le hM hM0
  have hzero : ∀ a ∈ A, ∀ j < T a, (hasseDeriv j f).evalAt a = 0 := fun a ha j hj ↦ by
    rw [← evalAt_iterate_derivative_eq_zero_iff, evalAt_eq_ofScalarsSum]
    exact hvan a ha j hj
  exact (hf.gaussNorm_le_gaussNorm_mul_div_pow_sum hr hs0 hsr hA hzero).trans
    (mul_le_mul_of_nonneg_right hfr (by positivity))

private theorem hasGaussNorm_one_and_gaussNorm_le {f : PowerSeries K} {r M : ℝ} (hr : 1 < r)
    (hM : ∀ k, ‖coeff k f‖ * r ^ k ≤ M) (A : Finset K) (hA : ∀ a ∈ A, ‖a‖ ≤ 1) (S : ℕ)
    (hvan : ∀ a ∈ A, ∀ j < S, FormalMultilinearSeries.ofScalarsSum (E := K)
      (fun k ↦ coeff k ((⇑(derivative (R := K)))^[j] f)) a = 0) :
    f.HasGaussNorm norm 1 ∧ f.gaussNorm norm 1 ≤ M * (r ^ (A.card * S))⁻¹ :=
  ⟨HasGaussNorm.of_le ⟨M, Set.forall_mem_range.mpr hM⟩ (fun _ ↦ norm_nonneg _) zero_le_one hr.le,
    by simpa [inv_pow] using
      gaussNorm_le_mul_div_pow_sum_of_ofScalarsSum_iterate_derivative_eq_zero
        (zero_lt_one.trans hr) zero_le_one hr.le hM A (T := fun _ ↦ S) hA hvan⟩

/-- **Many zeros in the unit disc force small coefficients.** Over a complete ultrametric normed
field `K` of characteristic zero, if `‖coeff k f‖ * r ^ k ≤ M` for all `k` at a radius `r > 1`,
and at each point `a` of a finite set `A` in the closed unit disc the values of the iterated formal
derivatives of `f` of order `< S` vanish, then every coefficient of `f` has norm at most
`M * (r ^ (A.card * S))⁻¹`. -/
theorem norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero {f : PowerSeries K}
    {r M : ℝ} (hr : 1 < r) (hM : ∀ k, ‖coeff k f‖ * r ^ k ≤ M) (A : Finset K)
    (hA : ∀ a ∈ A, ‖a‖ ≤ 1) (S : ℕ)
    (hvan : ∀ a ∈ A, ∀ j < S, FormalMultilinearSeries.ofScalarsSum (E := K)
      (fun k ↦ coeff k ((⇑(derivative (R := K)))^[j] f)) a = 0) (k : ℕ) :
    ‖coeff k f‖ ≤ M * (r ^ (A.card * S))⁻¹ := by
  obtain ⟨hf1, hg⟩ := hasGaussNorm_one_and_gaussNorm_le hr hM A hA S hvan
  simpa only [one_pow, mul_one] using (le_gaussNorm norm 1 f hf1 k).trans hg

/-- **Many zeros in the unit disc force small values on the unit disc.** Over a complete
ultrametric normed field `K` of characteristic zero, under the hypotheses of
`PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero`, the value of `f` at every
point `x` of the closed unit disc has norm at most `M * (r ^ (A.card * S))⁻¹`. -/
theorem norm_ofScalarsSum_le_of_ofScalarsSum_iterate_derivative_eq_zero
    {f : PowerSeries K} {r M : ℝ} (hr : 1 < r) (hM : ∀ k, ‖coeff k f‖ * r ^ k ≤ M)
    (A : Finset K) (hA : ∀ a ∈ A, ‖a‖ ≤ 1) (S : ℕ)
    (hvan : ∀ a ∈ A, ∀ j < S, FormalMultilinearSeries.ofScalarsSum (E := K)
      (fun k ↦ coeff k ((⇑(derivative (R := K)))^[j] f)) a = 0)
    {x : K} (hx : ‖x‖ ≤ 1) :
    ‖FormalMultilinearSeries.ofScalarsSum (E := K) (fun k ↦ coeff k f) x‖ ≤
      M * (r ^ (A.card * S))⁻¹ := by
  obtain ⟨hf1, hg⟩ := hasGaussNorm_one_and_gaussNorm_le hr hM A hA S hvan
  rw [← evalAt_eq_ofScalarsSum]
  exact (norm_evalAt_le_gaussNorm hf1 hx).trans hg

end CharZero

end PowerSeries
