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
# The Schwarz lemma for restricted power series

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
`‖f(x)‖ ≤ ‖f‖_c * ∏_{b ∈ s} (‖x - b‖ / c) ^ T b`.

## Main results

* `PowerSeries.IsRestricted.evalAt_eq_zero_iff`: the factor theorem for restricted series, over
  any complete ultrametric normed commutative ring.
* `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_prod`: the Schwarz lemma for a multiset
  of zeros.
* `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_prod_pow`: the Schwarz lemma for distinct
  zeros with multiplicities.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1 (Weierstrass division).
-/

public section

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

end CommRing

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {c : ℝ}
  {f q : PowerSeries K}

/-- Splitting off a zero `a` keeps the vanishing conditions at the other points: if `f = (X - a) q`
and the Hasse derivatives of `f` of order less than the multiplicity of each point in `a ::ₘ Z`
vanish there, then those of `q` of order less than the multiplicity in `Z` vanish. -/
private theorem IsRestricted.evalAt_hasseDeriv_eq_zero_of_X_sub_C_mul [DecidableEq K]
    (hq : q.IsRestricted c) {a : K} {Z : Multiset K} (hZ : ∀ b ∈ a ::ₘ Z, ‖b‖ ≤ c)
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

end Field

end PowerSeries
