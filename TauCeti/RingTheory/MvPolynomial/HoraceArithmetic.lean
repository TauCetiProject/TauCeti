/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Nat.Choose.Basic
import TauCeti.Algebra.Order.Floor.Div
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The size inequalities of the differential Horace method

Polynomials of total degree at most `d` in `r` variables form a space of dimension
`N(r, d) = (r + d).choose d`, and a double point in projective `r`-space imposes `r + 1`
conditions on them. The differential Horace method of Alexander and Hirschowitz, in the form of
Brambilla and Ottaviani, proves that `q` general double points impose independent conditions in
degree `d` at the two critical counts `⌊N(r, d) / (r + 1)⌋ ≤ q ≤ ⌈N(r, d) / (r + 1)⌉` by
specializing some of the points to a hyperplane `H`. How many points go to `H` is fixed by the
Euclidean division

  `r * u + e = q * (r + 1) - N(r, d - 1)`, with `0 ≤ e < r`,

taken in `ℤ`: `u` double points are moved onto `H`, `e` further points are moved onto `H` and
then off it again in a family, and the remaining `q - u - e` points stay off `H`. The residual
scheme in degree `d - 1` consists of the `u` points as simple points, the `e` points as double
points of `H` (of length `r`), and the `q - u - e` double points off `H`. This file proves the
numerical inequalities that make this choice work, for `r ≥ 2` and `d ≥ 4`. Apart from `u ≤ q`
they use only `e < r`, not `0 ≤ e`.

## Main results

* `TauCeti.horace_trace_size_le`: for `q ≤ ⌈N(r, d) / (r + 1)⌉`, the part of the residual scheme
  on `H` has length at most the dimension of the forms of degree `d - 1` on `H`:
  `r * e + u ≤ N(r - 1, d - 1)`.
* `TauCeti.horace_residual_size_le`: for the same `q`, the `q - u - e` double points off `H` have
  total length at least the dimension of the forms of degree `d - 2`:
  `N(r, d - 2) ≤ (q - u - e) * (r + 1)`.
* `TauCeti.horace_quartic_residual_ge`: for quartics in dimension `r ≥ 10` there are at least
  `r + 1` points off `H`.
* `TauCeti.horace_critical_bounds`: at the critical counts, `r - 1 ≤ u ≤ q`, so `e ≤ u`, and
  `0 ≤ q - u - e`.

For the Euclidean division, the trace inequality is an equality at `(r, d, q) = (2, 4, 5)` and
`(4, 4, 14)`.

## Implementation notes

For `d = 4` and `r ≤ 4` the general binomial estimate behind the trace inequality fails, and the
integer division is evaluated directly.

## References

* M. C. Brambilla, G. Ottaviani, *On the Alexander–Hirschowitz theorem*, J. Pure Appl. Algebra
  212 (2008), no. 5, 1229–1251, §6, Lemma 6.3 and Theorem 6.4.
-/

public section

namespace TauCeti

/-- For `m ≥ 4`, the binomial coefficient `(s + 1 + m).choose m` is at least
`(s + 5).choose 4`, whose `24`-fold multiple is `(s + 5) (s + 4) (s + 3) (s + 2)`. -/
private lemma choose_four_le {s m : ℕ} (hm : 4 ≤ m) :
    (s + 5) * (s + 4) * (s + 3) * (s + 2) ≤ 24 * (s + 1 + m).choose m := by
  have h24 : 24 * (s + 5).choose 4 = (s + 5) * (s + 4) * (s + 3) * (s + 2) := by
    rw [show (24 : ℕ) = (4 : ℕ).factorial from rfl, ← Nat.descFactorial_eq_factorial_mul_choose]
    simp [Nat.descFactorial_succ, show s + 5 - 1 = s + 4 by omega,
      show s + 5 - 2 = s + 3 by omega, show s + 5 - 3 = s + 2 by omega]
    ring
  have hle : (s + 5).choose (s + 1) ≤ (s + 1 + m).choose (s + 1) :=
    Nat.choose_le_choose _ (by omega)
  rw [show s + 5 = s + 1 + 4 by ring, Nat.choose_symm_add, show s + 1 + 4 = s + 5 by ring,
    Nat.choose_symm_add] at hle
  omega

/-- Pascal's rule in the form `N(r, d - 1) = N(r - 1, d - 1) + N(r, d - 2)`. -/
private lemma choose_pred_eq {r d : ℕ} (hr : 1 ≤ r) (hd : 2 ≤ d) :
    (r + (d - 1)).choose (d - 1) =
      (r - 1 + (d - 1)).choose (d - 1) + (r + (d - 2)).choose (d - 2) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  rw [show r + 1 + (d + 2 - 1) = r + d + 1 + 1 by omega, show d + 2 - 1 = d + 1 by omega,
    show r + 1 - 1 + (d + 1) = r + d + 1 by omega, show r + 1 + (d + 2 - 2) = r + d + 1 by omega,
    show d + 2 - 2 = d by omega, Nat.choose_succ_succ', add_comm]

/-- With `r = s + 2` and `d = t + 4`, outside `d = 4, r ≤ 4`, the binomial estimate
`d (r³ - r² - r + 2) ≤ (r - 1) (d - 1) N(r - 1, d - 1)`. -/
private lemma horace_trace_key_le {s t : ℕ} (h : ¬(t = 0 ∧ s ≤ 2)) :
    (t + 4) * (s ^ 3 + 5 * s ^ 2 + 7 * s + 4) ≤ (s + 1) * (t + 3) * (s + t + 4).choose (t + 3) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · -- For `d = 4` use `6 N(r - 1, 3) = (r + 2) (r + 1) r` and `r ≥ 5`.
    obtain ⟨w, rfl⟩ : ∃ w, s = w + 3 := ⟨s - 3, by omega⟩
    have h6 : 6 * (w + 3 + 0 + 4).choose (0 + 3) = (w + 7) * (w + 6) * (w + 5) := by
      rw [show (6 : ℕ) = (3 : ℕ).factorial from rfl, ← Nat.descFactorial_eq_factorial_mul_choose]
      simp [Nat.descFactorial_succ, Nat.factorial]
      ring
    have hpoly : 2 * (4 * ((w + 3) ^ 3 + 5 * (w + 3) ^ 2 + 7 * (w + 3) + 4)) ≤
        (w + 4) * ((w + 7) * (w + 6) * (w + 5)) := by
      ring_nf
      omega
    rw [← h6] at hpoly
    nlinarith [hpoly]
  · -- For `d ≥ 5` use `N(r - 1, d - 1) ≥ N(r - 1, 4)` and `4 d ≤ 5 (d - 1)`.
    have h24 := choose_four_le (s := s) (m := t + 3) (by omega)
    rw [show s + 1 + (t + 3) = s + t + 4 by ring] at h24
    have hpoly : 24 * (5 * (s ^ 3 + 5 * s ^ 2 + 7 * s + 4)) ≤
        4 * (s + 1) * ((s + 5) * (s + 4) * (s + 3) * (s + 2)) := by
      ring_nf
      omega
    have h5 : 5 * (s ^ 3 + 5 * s ^ 2 + 7 * s + 4) ≤ 4 * ((s + 1) * (s + t + 4).choose (t + 3)) := by
      refine Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < 24)
      calc 24 * (5 * (s ^ 3 + 5 * s ^ 2 + 7 * s + 4))
          ≤ 4 * (s + 1) * ((s + 5) * (s + 4) * (s + 3) * (s + 2)) := hpoly
        _ ≤ 4 * (s + 1) * (24 * (s + t + 4).choose (t + 3)) := Nat.mul_le_mul_left _ h24
        _ = 24 * (4 * ((s + 1) * (s + t + 4).choose (t + 3))) := by ring
    have h45 : 4 * (t + 4) ≤ 5 * (t + 3) := by omega
    refine Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < 20)
    calc 20 * ((t + 4) * (s ^ 3 + 5 * s ^ 2 + 7 * s + 4))
        = (4 * (t + 4)) * (5 * (s ^ 3 + 5 * s ^ 2 + 7 * s + 4)) := by ring
      _ ≤ (5 * (t + 3)) * (4 * ((s + 1) * (s + t + 4).choose (t + 3))) := Nat.mul_le_mul h45 h5
      _ = 20 * ((s + 1) * (t + 3) * (s + t + 4).choose (t + 3)) := by ring

/-- The core of the trace-size inequality, with `r = s + 2` and `d = t + 4`. -/
private lemma horace_trace_size_le_aux (s t q : ℕ) {u e : ℤ}
    (hq : q * (s + 3) ≤ (s + t + 6).choose (t + 4) + (s + 2))
    (hdiv : ((s : ℤ) + 2) * u + e = q * (s + 3) - ((s + t + 5).choose (t + 3) : ℕ))
    (her : e < s + 2) :
    ((s : ℤ) + 2) * e + u ≤ ((s + t + 4).choose (t + 3) : ℕ) := by
  by_cases hsmall : t = 0 ∧ s ≤ 2
  · -- The pairs `(r, d) = (2, 4), (3, 4), (4, 4)`: compute the binomial coefficients.
    obtain ⟨rfl, hs⟩ := hsmall
    interval_cases s <;> simp [Nat.choose] at hq hdiv her ⊢ <;> omega
  have key := horace_trace_key_le hsmall
  have hpascal : (s + t + 6).choose (t + 4) =
      (s + t + 5).choose (t + 3) + (s + t + 5).choose (t + 4) := Nat.choose_succ_succ' _ _
  -- `d N(r - 1, d) = (r + d - 1) N(r - 1, d - 1)`
  have hmul : (s + t + 5) * (s + t + 4).choose (t + 3) = (s + t + 5).choose (t + 4) * (t + 4) :=
    Nat.add_one_mul_choose_eq _ _
  set A := (s + t + 4).choose (t + 3)
  set B := (s + t + 5).choose (t + 4)
  set C := (s + t + 5).choose (t + 3)
  -- Inserting the ceiling bound into the division relation gives `r u + e ≤ N(r - 1, d) + r`.
  have hdivle : ((s : ℤ) + 2) * u + e ≤ B + (s + 2) := by
    have : ((q * (s + 3) : ℕ) : ℤ) ≤ ((C + B + (s + 2) : ℕ) : ℤ) := by
      exact_mod_cast hpascal ▸ hq
    push_cast at this
    linarith
  -- Hence `N(r - 1, d) + r³ - r² - r + 2 ≤ r N(r - 1, d - 1)`.
  have hBA : B + (s ^ 3 + 5 * s ^ 2 + 7 * s + 4) ≤ (s + 2) * A := by
    refine Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < t + 4)
    nlinarith [hmul, key]
  have hBA' : (B : ℤ) + (s ^ 3 + 5 * s ^ 2 + 7 * s + 4) ≤ (s + 2) * A := by exact_mod_cast hBA
  -- `r (r e + u) ≤ (r² - 1) e + N(r - 1, d) + r ≤ r N(r - 1, d - 1) + r - 1`.
  have h3 : (((s : ℤ) + 2) ^ 2 - 1) * e ≤ ((s + 2) ^ 2 - 1) * (s + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
  have hlt : ((s : ℤ) + 2) * ((s + 2) * e + u) < (s + 2) * (A + 1) := by
    nlinarith [hdivle, h3, hBA']
  have := lt_of_mul_lt_mul_left hlt (by positivity)
  linarith

/-- **Horace trace-size inequality.** Let `r ≥ 2`, `d ≥ 4` and `q ≤ ⌈N(r, d) / (r + 1)⌉`, where
`N(r, d) = (r + d).choose d`, and let the integers `u` and `e < r` satisfy
`r * u + e = q * (r + 1) - N(r, d - 1)`, for instance the Euclidean division. Then
`r * e + u ≤ N(r - 1, d - 1)`: `u` simple points and `e` double points of a hyperplane
`H ≅ ℙ^(r-1)`, each of length `r`, have total length at most the dimension of the forms of
degree `d - 1` on `H`. -/
theorem horace_trace_size_le {r d q : ℕ} (hr : 2 ≤ r) (hd : 4 ≤ d)
    (hq : q ≤ (r + d).choose d ⌈/⌉ (r + 1)) {u e : ℤ}
    (hdiv : r * u + e = q * (r + 1) - ((r + (d - 1)).choose (d - 1) : ℕ)) (her : e < r) :
    r * e + u ≤ ((r - 1 + (d - 1)).choose (d - 1) : ℕ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, d = t + 4 := ⟨d - 4, by omega⟩
  have hq' : q * (s + 3) ≤ (s + t + 6).choose (t + 4) + (s + 2) := by
    have := (Nat.le_ceilDiv_iff_mul_lt (by omega)).1 hq
    rw [show s + 2 + (t + 4) = s + t + 6 by ring, show s + 2 + 1 = s + 3 by ring] at this
    omega
  rw [show s + 2 + (t + 4 - 1) = s + t + 5 by omega, show t + 4 - 1 = t + 3 by omega] at hdiv
  rw [show s + 2 - 1 + (t + 4 - 1) = s + t + 4 by omega, show t + 4 - 1 = t + 3 by omega]
  push_cast at hdiv her ⊢
  exact horace_trace_size_le_aux s t q hq' (by linarith) her

/-- **Horace residual-size inequality.** Under the hypotheses of `horace_trace_size_le`, the
`q - u - e` double points left off the hyperplane, each of length `r + 1`, have total length at
least the dimension of the forms of degree `d - 2`: `N(r, d - 2) ≤ (q - u - e) * (r + 1)`. -/
theorem horace_residual_size_le {r d q : ℕ} (hr : 2 ≤ r) (hd : 4 ≤ d)
    (hq : q ≤ (r + d).choose d ⌈/⌉ (r + 1)) {u e : ℤ}
    (hdiv : r * u + e = q * (r + 1) - ((r + (d - 1)).choose (d - 1) : ℕ)) (her : e < r) :
    (((r + (d - 2)).choose (d - 2) : ℕ) : ℤ) ≤ (q - u - e) * (r + 1) := by
  have htrace := horace_trace_size_le hr hd hq hdiv her
  have hpascal : (((r + (d - 1)).choose (d - 1) : ℕ) : ℤ) =
      ((r - 1 + (d - 1)).choose (d - 1) : ℕ) + ((r + (d - 2)).choose (d - 2) : ℕ) := by
    exact_mod_cast choose_pred_eq (by omega) (by omega)
  -- `(q - u - e) (r + 1) = N(r, d - 1) - (r e + u)`.
  linarith

/-- **Large-dimensional quartic residual bound.** For quartics, `d = 4`, in dimension `r ≥ 10`,
let `q ≤ ⌈N(r, 4) / (r + 1)⌉` and let the integers `u` and `e < r` satisfy
`r * u + e = q * (r + 1) - N(r, 3)`. Then at least `r + 1` double points stay off the hyperplane:
`r + 1 ≤ q - u - e`. -/
theorem horace_quartic_residual_ge {r q : ℕ} (hr : 10 ≤ r)
    (hq : q ≤ (r + 4).choose 4 ⌈/⌉ (r + 1)) {u e : ℤ}
    (hdiv : r * u + e = q * (r + 1) - ((r + 3).choose 3 : ℕ)) (her : e < r) :
    r + 1 ≤ q - u - e := by
  have hq' : q * (r + 1) ≤ (r + 4).choose 4 + r := by
    have := (Nat.le_ceilDiv_iff_mul_lt (by omega)).1 hq
    omega
  -- `N(r, 4) = N(r, 3) + N(r - 1, 4)`, with `24 N(r - 1, 4) = (r + 3) (r + 2) (r + 1) r`.
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hpascal : (s + 1 + 4).choose 4 = (s + 1 + 3).choose 3 + (s + 1 + 3).choose 4 :=
    Nat.choose_succ_succ' _ _
  have hB : 24 * (s + 1 + 3).choose 4 = (s + 4) * (s + 3) * (s + 2) * (s + 1) := by
    rw [show (24 : ℕ) = (4 : ℕ).factorial from rfl, ← Nat.descFactorial_eq_factorial_mul_choose]
    simp [Nat.descFactorial_succ, show s + 1 + 3 - 1 = s + 3 by omega,
      show s + 1 + 3 - 2 = s + 2 by omega, show s + 1 + 3 - 3 = s + 1 by omega]
    ring
  have hC : 6 * (s + 1 + 3).choose 3 = (s + 4) * (s + 3) * (s + 2) := by
    rw [show (6 : ℕ) = (3 : ℕ).factorial from rfl, ← Nat.descFactorial_eq_factorial_mul_choose]
    simp [Nat.descFactorial_succ, show s + 1 + 3 - 1 = s + 3 by omega,
      show s + 1 + 3 - 2 = s + 2 by omega]
    ring
  set B := (s + 1 + 3).choose 4
  set C := (s + 1 + 3).choose 3
  rw [hpascal] at hq'
  have hB' : (24 : ℤ) * B = (s + 4) * (s + 3) * (s + 2) * (s + 1) := by exact_mod_cast hB
  have hC' : (6 : ℤ) * C = (s + 4) * (s + 3) * (s + 2) := by exact_mod_cast hC
  push_cast at hdiv her ⊢
  -- The ceiling bound gives `r u + e ≤ N(r - 1, 4) + r`.
  have h1 : ((s : ℤ) + 1) * u + e ≤ B + (s + 1) := by
    have : ((q * (s + 1 + 1) : ℕ) : ℤ) ≤ ((C + B + (s + 1) : ℕ) : ℤ) := by exact_mod_cast hq'
    push_cast at this
    linarith
  have h2 : (((s : ℤ) + 1) ^ 2 - 1) * e ≤ ((s + 1) ^ 2 - 1) * s :=
    mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
  -- Otherwise `r (r + 1) (q - u - e) = r N(r, 3) - r (r e + u) ≤ r (r + 1) r`, which
  -- contradicts `3 r³ (r - 10) + 33 r² + 18 r - 24 > 0`.
  by_contra! hlt
  have h3 : ((s : ℤ) + 1) * ((s + 2) * (q - u - e)) ≤ (s + 1) * ((s + 2) * (s + 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      (by positivity)
  have hpos : 0 ≤ 3 * ((s : ℤ) + 1) ^ 3 * (s - 9) := by
    have : (9 : ℤ) ≤ s := by exact_mod_cast (by omega : 9 ≤ s)
    have : (0 : ℤ) ≤ s - 9 := by linarith
    positivity
  nlinarith [h1, h2, h3, hB', hC', hpos]

/-- **Nonnegative critical Horace data.** Let `r ≥ 2`, `d ≥ 4` and let `q` be a critical count,
`⌊N(r, d) / (r + 1)⌋ ≤ q ≤ ⌈N(r, d) / (r + 1)⌉`. Then the Euclidean division
`r * u + e = q * (r + 1) - N(r, d - 1)`, `0 ≤ e < r`, satisfies `r - 1 ≤ u ≤ q` and
`0 ≤ q - u - e`. In particular `e ≤ u`. -/
theorem horace_critical_bounds {r d q : ℕ} (hr : 2 ≤ r) (hd : 4 ≤ d)
    (hqf : (r + d).choose d / (r + 1) ≤ q) (hqc : q ≤ (r + d).choose d ⌈/⌉ (r + 1)) {u e : ℤ}
    (hdiv : r * u + e = q * (r + 1) - ((r + (d - 1)).choose (d - 1) : ℕ)) (he : 0 ≤ e)
    (her : e < r) :
    r - 1 ≤ u ∧ u ≤ q ∧ 0 ≤ q - u - e := by
  have hres := horace_residual_size_le hr hd hqc hdiv her
  have hqf' : (r + d).choose d ≤ q * (r + 1) + r := by
    have := (Nat.div_le_iff_le_mul_add_pred (by omega : 0 < r + 1)).1 hqf
    rw [Nat.add_sub_cancel, mul_comm] at this
    exact this
  have hpos : 0 ≤ (q : ℤ) - u - e := by
    by_contra! h
    nlinarith [hres, (by positivity : (0 : ℤ) ≤ ((r + (d - 2)).choose (d - 2) : ℕ))]
  refine ⟨?_, by linarith, hpos⟩
  -- `r u + e ≥ N(r, d) - r - N(r, d - 1) = N(r - 1, d) - r ≥ r² - r`.
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, d = t + 4 := ⟨d - 4, by omega⟩
  have hpascal : (s + 2 + (t + 4)).choose (t + 4) =
      (s + 2 + (t + 4 - 1)).choose (t + 4 - 1) + (s + 1 + (t + 4)).choose (t + 4) := by
    rw [show s + 2 + (t + 4) = s + t + 5 + 1 by ring, show t + 4 = t + 3 + 1 by ring,
      Nat.choose_succ_succ', show s + 2 + (t + 3 + 1 - 1) = s + t + 5 by omega,
      show t + 3 + 1 - 1 = t + 3 by omega, show s + 1 + (t + 3 + 1) = s + t + 5 by ring]
  have h24 := choose_four_le (s := s) (m := t + 4) (by omega)
  have hpoly : 24 * (s + 2) ^ 2 ≤ (s + 5) * (s + 4) * (s + 3) * (s + 2) := by
    ring_nf
    omega
  set B := (s + 1 + (t + 4)).choose (t + 4)
  set C := (s + 2 + (t + 4 - 1)).choose (t + 4 - 1)
  have hB : (s + 2) ^ 2 ≤ B := by omega
  rw [hpascal] at hqf'
  have hqf'' : (C : ℤ) + B ≤ q * (s + 3) + (s + 2) := by
    have : ((C + B : ℕ) : ℤ) ≤ ((q * (s + 2 + 1) + (s + 2) : ℕ) : ℤ) := by exact_mod_cast hqf'
    push_cast at this
    linarith
  have hB' : ((s : ℤ) + 2) ^ 2 ≤ B := by exact_mod_cast hB
  push_cast at hdiv her ⊢
  by_contra! hlt
  have : ((s : ℤ) + 2) * u ≤ (s + 2) * s :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith [hdiv, hqf'', hB', her]

end TauCeti
