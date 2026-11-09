/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Schwarz
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.NumberTheory.Padics.MahlerBasis
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Interpolation on grids of p-adic integers

In the `p`-adic method of linear forms in logarithms, an auxiliary function `f` analytic on a
closed disc of radius `c ≥ 1` over a field `K ⊇ ℚ_p` vanishes to order `T` at the points of a grid
of `p`-adic integers, typically rational integers. The Schwarz lemma for restricted series bounds
`f` at every other `p`-adic integer `x` by the interpolation denominator `∏_{b} (x - b)`:

```text
‖f(x)‖ ≤ ‖f‖_c * (‖∏_{b ∈ s} (x - b)‖ / c ^ #s) ^ T.
```

This file makes the denominators explicit for the grids of the method.

* For an arithmetic progression `a, a + d, …, a + (n - 1) d` with unit step `d`, rescaling by `d`
  turns the denominator into a value `y (y - 1) ⋯ (y - n + 1)` of the descending Pochhammer
  polynomial on `ℤ_p`, which Mathlib bounds by `‖n!‖` (`PadicInt.norm_ascPochhammer_le`). Hence
  `‖∏_{j < n} (x - (a + j d))‖ ≤ ‖n!‖`, whatever the position of `x`.
* For the integers `0 ≤ j < N` not divisible by an auxiliary integer `q` prime to `p`, the grid
  contains the `q - 1` progressions `r + q m`, `1 ≤ r < q`, `m < ⌊N / q⌋`, each with unit step
  `q`. Hence the denominator has norm at most `‖⌊N / q⌋!‖ ^ (q - 1)`.

## Main results

* `PadicInt.norm_prod_range_sub_add_mul_le`: the factorial bound for a progression with unit step.
* `PadicInt.norm_prod_filter_not_dvd_sub_le`: the bound for the integers not divisible by `q`.
* `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_norm_prod`: the Schwarz lemma on a grid
  of `p`-adic integers, with the interpolation denominator.
* `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_norm_factorial`,
  `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm_mul_norm_factorial_pow`: its explicit
  forms on a progression and on the integers not divisible by `q`.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
-/

public section

open Finset

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **Interpolation denominators on a progression.** For `p`-adic integers `x` and `a` and a unit
step `d`, the product of the distances from `x` to the `n` points `a + j d`, `j < n`, has norm at
most `‖n!‖`. -/
theorem norm_prod_range_sub_add_mul_le (x a : ℤ_[p]) {d : ℤ_[p]} (hd : IsUnit d) (n : ℕ) :
    ‖∏ j ∈ range n, (x - (a + j * d))‖ ≤ ‖(n.factorial : ℤ_[p])‖ := by
  obtain ⟨u, rfl⟩ := hd
  -- rescaling by the unit `u` turns the progression into `0, 1, …, n - 1`
  have hprod : ∏ j ∈ range n, (x - (a + j * u)) =
      (u : ℤ_[p]) ^ n * (descPochhammer ℤ_[p] n).eval (↑u⁻¹ * (x - a)) := by
    have h := pow_card_mul_prod (s := range n) (b := (u : ℤ_[p]))
      (f := fun j : ℕ ↦ ↑u⁻¹ * (x - a) - j)
    rw [card_range] at h
    rw [descPochhammer_eval_eq_prod_range, h]
    refine prod_congr rfl fun j _ ↦ ?_
    rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul]
    ring
  rw [hprod, norm_mul, norm_pow, norm_units, one_pow, one_mul,
    descPochhammer_eval_eq_ascPochhammer]
  exact norm_ascPochhammer_le n _

/-- **Interpolation denominators on the integers not divisible by `q`.** Let `q` be prime to
`p`. For a `p`-adic integer `x`, the product of the distances from `x` to the integers
`0 ≤ j < N` not divisible by `q` has norm at most `‖⌊N / q⌋!‖ ^ (q - 1)`. -/
theorem norm_prod_filter_not_dvd_sub_le (x : ℤ_[p]) {q : ℕ} (hq : p.Coprime q) (N : ℕ) :
    ‖∏ j ∈ (range N).filter (¬q ∣ ·), (x - j)‖ ≤ ‖((N / q).factorial : ℤ_[p])‖ ^ (q - 1) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact (Nat.Prime.one_lt Fact.out).ne' (Nat.coprime_zero_right p |>.mp hq)
  -- the `q - 1` progressions `r + q m`, `1 ≤ r < q`, `m < ⌊N / q⌋`, inside the grid
  set g : ℕ × ℕ → ℕ := fun rm ↦ rm.1 + q * rm.2
  have hinj : Set.InjOn g (Ico 1 q ×ˢ range (N / q) : Finset (ℕ × ℕ)) := by
    rintro ⟨r, m⟩ hrm ⟨r', m'⟩ hrm' h
    simp only [coe_product, coe_Ico, coe_range, Set.mem_prod, Set.mem_Ico, Set.mem_Iio] at hrm hrm'
    obtain ⟨⟨-, hr⟩, -⟩ := hrm
    obtain ⟨⟨-, hr'⟩, -⟩ := hrm'
    have hmod := congrArg (· % q) h
    simp only [g, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at hmod
    subst hmod
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq0) (by simpa [g] using h))
  have hsub : (Ico 1 q ×ˢ range (N / q)).image g ⊆ (range N).filter (¬q ∣ ·) := by
    simp only [subset_iff, mem_image, mem_product, mem_Ico, mem_range, mem_filter]
    rintro _ ⟨⟨r, m⟩, ⟨⟨hr1, hrq⟩, hm⟩, rfl⟩
    dsimp only at hr1 hrq hm
    refine ⟨?_, fun h ↦ ?_⟩
    · have h1 := Nat.div_mul_le_self N q
      have h2 : q * (m + 1) ≤ q * (N / q) := Nat.mul_le_mul_left q hm
      simp only [g]
      nlinarith
    · have := (Nat.dvd_add_right (dvd_mul_right q m)).mp (by simpa [g, add_comm] using h)
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  obtain ⟨c, hc⟩ := prod_dvd_prod_of_subset _ _ (fun j : ℕ ↦ x - j) hsub
  rw [hc, norm_mul, prod_image hinj, prod_product]
  refine (mul_le_of_le_one_right (norm_nonneg _) (norm_le_one c)).trans ?_
  rw [norm_prod, ← Nat.card_Ico 1 q, ← prod_const]
  refine prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun r _ ↦ ?_
  simpa [g, mul_comm] using norm_prod_range_sub_add_mul_le x r (isUnit_natCast_of_coprime hq) _

end PadicInt

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] {c : ℝ} {f : PowerSeries K}

/-- **The Schwarz lemma on a grid of `p`-adic integers.** Let `K` be a complete normed field
extension of `ℚ_p` and `f` a power series over `K` restricted at a radius `c ≥ 1`. If the Hasse
derivatives `(D⁽ᵗ⁾ f)(b)` vanish for `t < T` at every point `b` of a finite set `s` of `p`-adic
integers, then at every `p`-adic integer `x`

```text
‖f(x)‖ ≤ ‖f‖_c * (‖∏_{b ∈ s} (x - b)‖ / c ^ #s) ^ T.
``` -/
theorem IsRestricted.norm_evalAt_le_gaussNorm_mul_norm_prod (hf : f.IsRestricted c)
    (hc : 1 ≤ c) {s : Finset ℤ_[p]} {T : ℕ}
    (hzero : ∀ b ∈ s, ∀ t < T, (PowerSeries.hasseDeriv t f).evalAt (algebraMap ℚ_[p] K b) = 0)
    (x : ℤ_[p]) :
    ‖f.evalAt (algebraMap ℚ_[p] K x)‖ ≤
      f.gaussNorm norm c * (‖∏ b ∈ s, (x - b)‖ / c ^ s.card) ^ T := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  classical
  -- the embedding `ℤ_p → K` is isometric and injective
  have hinj : Function.Injective fun b : ℤ_[p] ↦ algebraMap ℚ_[p] K b := fun y z h ↦
    Subtype.ext ((algebraMap ℚ_[p] K).injective h)
  have hle (y : ℤ_[p]) : ‖algebraMap ℚ_[p] K y‖ ≤ c := by
    rw [norm_algebraMap', ← PadicInt.norm_def]
    exact (PadicInt.norm_le_one y).trans hc
  have hdist (b : ℤ_[p]) : ‖algebraMap ℚ_[p] K x - algebraMap ℚ_[p] K b‖ = ‖x - b‖ := by
    rw [← map_sub, ← PadicInt.coe_sub, norm_algebraMap', ← PadicInt.norm_def]
  have h := hf.norm_evalAt_le_gaussNorm_mul_prod_pow (L := K) (zero_lt_one.trans_le hc)
    (s := s.image fun b : ℤ_[p] ↦ algebraMap ℚ_[p] K b) (T := fun _ ↦ T)
    (by simpa using fun b _ ↦ hle b) (by simpa using hzero) (hle x)
  refine h.trans_eq ?_
  rw [prod_image hinj.injOn]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, hdist]
  rw [prod_pow, prod_div_distrib, prod_const, ← norm_prod]

/-- **The Schwarz lemma on a progression of `p`-adic integers.** Let `K` be a complete normed field
extension of `ℚ_p` and `f` a power series over `K` restricted at a radius `c ≥ 1`. If the Hasse
derivatives `(D⁽ᵗ⁾ f)(a + j d)` vanish for `t < T` and `j < n`, where `d` is a unit of `ℤ_p`, then
at every `p`-adic integer `x`

```text
‖f(x)‖ ≤ ‖f‖_c * (‖n!‖ / c ^ n) ^ T.
``` -/
theorem IsRestricted.norm_evalAt_le_gaussNorm_mul_norm_factorial (hf : f.IsRestricted c)
    (hc : 1 ≤ c) (a : ℤ_[p]) {d : ℤ_[p]} (hd : IsUnit d) {n T : ℕ}
    (hzero : ∀ j < n, ∀ t < T,
      (PowerSeries.hasseDeriv t f).evalAt (algebraMap ℚ_[p] K ↑(a + j * d)) = 0)
    (x : ℤ_[p]) :
    ‖f.evalAt (algebraMap ℚ_[p] K x)‖ ≤
      f.gaussNorm norm c * (‖(n.factorial : ℤ_[p])‖ / c ^ n) ^ T := by
  classical
  have hinj : Set.InjOn (fun j : ℕ ↦ a + (j : ℤ_[p]) * d) (range n : Set ℕ) := fun i _ j _ h ↦ by
    simpa [hd.ne_zero] using h
  have h := hf.norm_evalAt_le_gaussNorm_mul_norm_prod hc
    (s := (range n).image fun j : ℕ ↦ a + (j : ℤ_[p]) * d) (T := T)
    (by simpa using hzero) x
  rw [prod_image hinj, card_image_of_injOn hinj, card_range] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (gaussNorm_nonneg _ _ f fun _ ↦ norm_nonneg _))
  gcongr
  exact PadicInt.norm_prod_range_sub_add_mul_le x a hd n

/-- **The Schwarz lemma on the integers not divisible by `q`.** Let `K` be a complete normed field
extension of `ℚ_p`, `f` a power series over `K` restricted at a radius `c ≥ 1`, and `q` an integer
prime to `p`. If the Hasse derivatives `(D⁽ᵗ⁾ f)(j)` vanish for `t < T` at every integer
`0 ≤ j < N` not divisible by `q`, a grid of `S` points, then at every `p`-adic integer `x`

```text
‖f(x)‖ ≤ ‖f‖_c * (‖⌊N / q⌋!‖ ^ (q - 1) / c ^ S) ^ T.
``` -/
theorem IsRestricted.norm_evalAt_le_gaussNorm_mul_norm_factorial_pow (hf : f.IsRestricted c)
    (hc : 1 ≤ c) {q : ℕ} (hq : p.Coprime q) {N T : ℕ}
    (hzero : ∀ j < N, ¬q ∣ j → ∀ t < T, (PowerSeries.hasseDeriv t f).evalAt (j : K) = 0)
    (x : ℤ_[p]) :
    ‖f.evalAt (algebraMap ℚ_[p] K x)‖ ≤
      f.gaussNorm norm c *
        (‖((N / q).factorial : ℤ_[p])‖ ^ (q - 1) / c ^ ((range N).filter (¬q ∣ ·)).card) ^ T := by
  classical
  have hinj : Set.InjOn (Nat.cast : ℕ → ℤ_[p]) ((range N).filter (¬q ∣ ·) : Set ℕ) :=
    Nat.cast_injective.injOn
  have h := hf.norm_evalAt_le_gaussNorm_mul_norm_prod hc
    (s := ((range N).filter (¬q ∣ ·)).image (Nat.cast : ℕ → ℤ_[p])) (T := T) (fun b hb ↦ by
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
      rw [mem_filter, mem_range] at hj
      simpa using hzero j hj.1 hj.2) x
  rw [prod_image hinj, card_image_of_injOn hinj] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (gaussNorm_nonneg _ _ f fun _ ↦ norm_nonneg _))
  gcongr
  exact PadicInt.norm_prod_filter_not_dvd_sub_le x hq N

end PowerSeries
