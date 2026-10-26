/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Bounds
import TauCeti.Analysis.Polynomial.L1Norm

/-!
# Baker's binomial polynomials

For `k : ℕ`, Baker's binomial polynomial is

`Δ(X; k) = (X + 1) (X + 2) ⋯ (X + k) / k!`,

so that `Δ(n; k) = (n + k choose k)` at natural numbers `n`. In the method of linear forms in
logarithms, archimedean as well as `p`-adic, the auxiliary functions are built from the divided
derivatives

`Δ(x; k, l, m) = (1 / m!) (d / dx) ^ m (Δ(x; k) ^ l)`,

which are written here as `(hasseDeriv m (bakerDelta k ^ l)).eval x`. The estimates on such an
auxiliary function at integral points use two bounds for these numbers: a denominator bound and a
size bound.

* **Denominators.** If `L` is an integer divisible by each of `1, …, k`, for instance
  `L = lcm(1, …, k)`, then `L ^ m Δ(x; k, l, m)` is an integer for every integer `x`. The
  polynomial form of this is that `Δ(a + L X; k)` has integral coefficients for every integer
  `a`. For `a = 0` it is the product of the integral linear polynomials `1 + (L / j) X`, and the
  Pascal recursion `Δ(X + 1; k + 1) = Δ(X; k + 1) + Δ(X + 1; k)` moves `a` up and down. The
  Taylor expansion of `Δ(X; k) ^ l` at `x`, rescaled by `L`, has the numbers `L ^ m Δ(x; k, l, m)`
  as coefficients.
* **Size.** If `x` is rational with `|x| ≤ n`, then `|Δ(x; k, l, m)| ≤ 2 ^ (l (n + k + 1))`,
  because the coefficient length of `Δ(X + x; k)` is at most `(n + k + 1 choose k)`.

Read at a single prime `p`, the denominator bound with `L = lcm(1, …, k)` says that
`v_p(Δ(x; k, l, m)) ≥ -m v_p(lcm(1, …, k))` for every integer `x`.

## Main definitions

* `TauCeti.bakerDelta`: Baker's binomial polynomial `Δ(X; k)` in `ℚ[X]`.

## Main results

* `TauCeti.bakerDelta_succ`: the product recursion
  `Δ(X; k + 1) = Δ(X; k) (X / (k + 1) + 1)`.
* `TauCeti.bakerDelta_succ_comp_X_add_one`: the Pascal recursion.
* `TauCeti.eval_bakerDelta_natCast`: `Δ(n; k) = (n + k choose k)`.
* `TauCeti.bakerDelta_eq_multichoose`: `Δ(X; k)` is `Ring.multichoose (X + 1) k`.
* `TauCeti.bakerDelta_comp_C_add_C_mul_X_mem_lifts`: `Δ(a + L X; k)` has integral coefficients.
* `TauCeti.pow_mul_eval_hasseDeriv_bakerDelta_pow_mem_range_intCast`: Baker's denominator bound,
  `L ^ m Δ(x; k, l, m) ∈ ℤ` for integral `x`.
* `TauCeti.lcm_pow_mul_eval_hasseDeriv_bakerDelta_pow_mem_range_intCast`: its classical form,
  with `L = lcm(1, …, k)`.
* `TauCeti.abs_eval_hasseDeriv_bakerDelta_pow_le`: the size bound.

## References

* A. Baker, *A sharpening of the bounds for linear forms in logarithms*, Acta Arith. **21**
  (1972), 117–129.
* Kunrui Yu, *Linear forms in p-adic logarithms II*, Compositio Math. **74** (1990), 15–113, §1.
-/

public section

open Polynomial
open scoped Nat

namespace TauCeti

/-- **Baker's binomial polynomial** `Δ(X; k) = (X + 1) (X + 2) ⋯ (X + k) / k!`, the rising
factorial of length `k` started at `X + 1`, normalized by `k!`. Its values at natural numbers are
the binomial coefficients `Δ(n; k) = (n + k choose k)` (`TauCeti.eval_bakerDelta_natCast`). -/
noncomputable def bakerDelta (k : ℕ) : ℚ[X] :=
  C ((k ! : ℚ)⁻¹) * (ascPochhammer ℚ k).comp (X + 1)

@[simp]
theorem bakerDelta_zero : bakerDelta 0 = 1 := by
  simp [bakerDelta]

/-- The product recursion: `Δ(X; k + 1) = Δ(X; k) (X / (k + 1) + 1)`. -/
theorem bakerDelta_succ (k : ℕ) :
    bakerDelta (k + 1) = bakerDelta k * (C ((k + 1 : ℚ)⁻¹) * X + 1) := by
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h : C ((k + 1 : ℚ)⁻¹) * (C (k : ℚ) + 1) = 1 := by
    rw [← C_1, ← C_add, ← C_mul, inv_mul_cancel₀ hk, C_1]
  rw [bakerDelta, bakerDelta, ascPochhammer_succ_right, mul_comp, add_comp, X_comp,
    ← C_eq_natCast, C_comp, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_inv, C_mul]
  linear_combination (C ((k ! : ℚ)⁻¹) * (ascPochhammer ℚ k).comp (X + 1)) * h

/-- The Pascal recursion: `Δ(X + 1; k + 1) = Δ(X; k + 1) + Δ(X + 1; k)`. -/
theorem bakerDelta_succ_comp_X_add_one (k : ℕ) :
    (bakerDelta (k + 1)).comp (X + 1) = bakerDelta (k + 1) + (bakerDelta k).comp (X + 1) := by
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hc : C (((k + 1)! : ℚ)⁻¹) * ((k : ℚ[X]) + 1) = C ((k ! : ℚ)⁻¹) := by
    rw [← C_eq_natCast, ← C_1, ← C_add, ← C_mul, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_succ, mul_inv, mul_right_comm, inv_mul_cancel₀ hk, one_mul]
  simp only [bakerDelta, mul_comp, C_comp, natCast_comp, one_comp, add_comp,
    ascPochhammer_succ_comp_X_add_one, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  linear_combination (((ascPochhammer ℚ k).comp (X + 1)).comp (X + 1)) * hc

/-- At a natural number `n`, Baker's binomial polynomial is the binomial coefficient
`Δ(n; k) = (n + k choose k)`. -/
@[simp]
theorem eval_bakerDelta_natCast (k n : ℕ) :
    (bakerDelta k).eval (n : ℚ) = ((n + k).choose k : ℚ) := by
  have hk : (k ! : ℚ) ≠ 0 := by positivity
  rw [bakerDelta, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one, ← Nat.cast_succ,
    ← ascPochhammer_eval_cast, ascPochhammer_nat_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, inv_mul_cancel_left₀ hk]

/-- In the language of binomial rings, `Δ(X; k)` is the multiset coefficient
`multichoose (X + 1) k`, that is, `(X + k choose k)`. -/
theorem bakerDelta_eq_multichoose (k : ℕ) : bakerDelta k = Ring.multichoose (X + 1 : ℚ[X]) k := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (X + 1 : ℚ[X]) k
  rw [ascPochhammer_smeval_eq_eval, ← ascPochhammer_map (algebraMap ℚ ℚ[X]),
    eval_map_algebraMap, ← comp_eq_aeval] at h
  rw [bakerDelta, ← h, nsmul_eq_mul, ← C_eq_natCast, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ (by positivity), C_1, one_mul]

/-- `Δ(L X; k)` has integral coefficients when each of `1, …, k` divides `L`: it is the product of
the integral linear polynomials `1 + (L / j) X` for `1 ≤ j ≤ k`. -/
private theorem bakerDelta_comp_C_mul_X_mem_lifts {k : ℕ} {L : ℤ}
    (hL : ∀ j ∈ Finset.Icc 1 k, (j : ℤ) ∣ L) :
    (bakerDelta k).comp (C (L : ℚ) * X) ∈ lifts (Int.castRingHom ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := hL (k + 1) (by simp)
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hlin : (C ((k + 1 : ℚ)⁻¹) * X + 1).comp (C (L : ℚ) * X) =
        C (Int.castRingHom ℚ c) * X + 1 := by
      simp only [add_comp, mul_comp, C_comp, X_comp, one_comp, ← mul_assoc, ← C_mul, hc,
        eq_intCast]
      push_cast
      rw [inv_mul_cancel_left₀ hk]
    rw [bakerDelta_succ, mul_comp, hlin]
    refine mul_mem (ih fun j hj => hL j ?_) (add_mem (mul_mem (C_mem_lifts _ c) (X_mem_lifts _))
      (one_mem _))
    simp only [Finset.mem_Icc] at hj ⊢
    omega

/-- **Integer translates of Baker's binomial polynomial.** If each of `1, …, k` divides the
integer `L`, then `Δ(a + L X; k)` has integral coefficients for every integer `a`. -/
theorem bakerDelta_comp_C_add_C_mul_X_mem_lifts {k : ℕ} {L : ℤ}
    (hL : ∀ j ∈ Finset.Icc 1 k, (j : ℤ) ∣ L) (a : ℤ) :
    (bakerDelta k).comp (C (a : ℚ) + C (L : ℚ) * X) ∈ lifts (Int.castRingHom ℚ) := by
  rw [lifts_iff_liftsRing]
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have ih' : ∀ a : ℤ, (bakerDelta k).comp (C (a : ℚ) + C (L : ℚ) * X) ∈
        liftsRing (Int.castRingHom ℚ) := ih fun j hj => hL j (by
      simp only [Finset.mem_Icc] at hj ⊢
      omega)
    -- The Pascal recursion evaluated along `a + L X`.
    have hP : ∀ a : ℤ, (bakerDelta (k + 1)).comp (C ((a + 1 : ℤ) : ℚ) + C (L : ℚ) * X) =
        (bakerDelta (k + 1)).comp (C (a : ℚ) + C (L : ℚ) * X) +
          (bakerDelta k).comp (C ((a + 1 : ℤ) : ℚ) + C (L : ℚ) * X) := by
      intro a
      have h := congrArg (fun p => p.comp (C (a : ℚ) + C (L : ℚ) * X))
        (bakerDelta_succ_comp_X_add_one k)
      simp only [add_comp, comp_assoc, X_comp, one_comp] at h
      simpa only [Int.cast_add, Int.cast_one, C_add, C_1, add_right_comm _ (C (L : ℚ) * X)]
        using h
    induction a using Int.induction_on with
    | zero => simpa [← lifts_iff_liftsRing] using bakerDelta_comp_C_mul_X_mem_lifts hL
    | succ n hn =>
      rw [hP]
      exact add_mem hn (ih' _)
    | pred n hn =>
      have h := hP (-(n : ℤ) - 1)
      rw [sub_add_cancel] at h
      rw [eq_sub_of_add_eq h.symm]
      exact sub_mem hn (ih' _)

/-- **Baker's denominator bound.** If each of `1, …, k` divides the integer `L`, then for every
integer `x` and all `l, m`,

`L ^ m Δ(x; k, l, m) = L ^ m (1 / m!) (d / dx) ^ m (Δ(x; k) ^ l)`

is an integer. -/
theorem pow_mul_eval_hasseDeriv_bakerDelta_pow_mem_range_intCast {k : ℕ} {L : ℤ}
    (hL : ∀ j ∈ Finset.Icc 1 k, (j : ℤ) ∣ L) (l m : ℕ) (x : ℤ) :
    (L : ℚ) ^ m * (hasseDeriv m (bakerDelta k ^ l)).eval (x : ℚ) ∈
      Set.range (Int.cast : ℤ → ℚ) := by
  have h := pow_mem (bakerDelta_comp_C_add_C_mul_X_mem_lifts hL x) l
  have e : (bakerDelta k).comp (C (x : ℚ) + C (L : ℚ) * X) ^ l =
      (taylor (x : ℚ) (bakerDelta k ^ l)).comp (C (L : ℚ) * X) := by
    rw [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, add_comm, pow_comp]
  rw [e, lifts_iff_coeff_lifts] at h
  obtain ⟨z, hz⟩ := h m
  rw [comp_C_mul_X_coeff, taylor_coeff, eq_intCast] at hz
  exact ⟨z, hz.trans (mul_comm _ _)⟩

/-- **Baker's denominator bound**, classical form: for every integer `x` and all `l, m`,
`lcm(1, …, k) ^ m Δ(x; k, l, m)` is an integer. -/
theorem lcm_pow_mul_eval_hasseDeriv_bakerDelta_pow_mem_range_intCast (k l m : ℕ) (x : ℤ) :
    (((Finset.Icc 1 k).lcm id : ℕ) : ℚ) ^ m * (hasseDeriv m (bakerDelta k ^ l)).eval (x : ℚ) ∈
      Set.range (Int.cast : ℤ → ℚ) := by
  simpa using pow_mul_eval_hasseDeriv_bakerDelta_pow_mem_range_intCast
    (L := ((Finset.Icc 1 k).lcm id : ℕ)) (fun j hj => Int.natCast_dvd_natCast.mpr
      (Finset.dvd_lcm (f := id) hj)) l m x

/-- The coefficient length of the translate `Δ(X + x; k)` is at most `(n + k + 1 choose k)`
whenever `|x| ≤ n`. -/
private theorem l1Norm_taylor_bakerDelta_le {x : ℚ} {n : ℕ} (hx : |x| ≤ n) (k : ℕ) :
    (taylor x (bakerDelta k)).l1Norm ≤ ((n + k + 1).choose k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (0 : ℚ) < (k : ℚ) + 1 := by positivity
    -- The new linear factor is `X / (k + 1) + (x / (k + 1) + 1)`.
    have hlin : taylor x (C ((k + 1 : ℚ)⁻¹) * X + 1) =
        C ((k + 1 : ℚ)⁻¹) * X + C ((k + 1 : ℚ)⁻¹ * x + 1) := by
      rw [map_add, taylor_mul, taylor_C, taylor_X, taylor_one, C_add, C_mul, C_1]
      ring
    have hlin' : (taylor x (C ((k + 1 : ℚ)⁻¹) * X + 1)).l1Norm ≤ ((n + k + 2 : ℝ)) / (k + 1) := by
      have hk' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hx' : |(x : ℝ)| ≤ n := by exact_mod_cast hx
      rw [hlin, C_mul_X_eq_monomial]
      refine (l1Norm_add_le _ _).trans ?_
      rw [l1Norm_monomial, l1Norm_C, ← Rat.norm_cast_real, ← Rat.norm_cast_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      push_cast
      have h1 : |((k : ℝ) + 1)⁻¹ * x + 1| ≤ ((k : ℝ) + 1)⁻¹ * n + 1 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos (inv_pos.mpr hk'), abs_one]
        gcongr
      rw [abs_of_pos (inv_pos.mpr hk')]
      calc ((k : ℝ) + 1)⁻¹ + |((k : ℝ) + 1)⁻¹ * x + 1|
          ≤ ((k : ℝ) + 1)⁻¹ + (((k : ℝ) + 1)⁻¹ * n + 1) := by gcongr
        _ = (n + k + 2) / (k + 1) := by field_simp; ring
    have hchoose : ((n + (k + 1) + 1).choose (k + 1) : ℝ) * (k + 1) =
        ((n + k + 1).choose k : ℝ) * (n + k + 2) := by
      have := Nat.add_one_mul_choose_eq (n + k + 1) k
      rw [show n + (k + 1) + 1 = n + k + 1 + 1 by ring]
      exact_mod_cast (by linarith [this] : ((n + k + 1 + 1).choose (k + 1)) * (k + 1) =
        (n + k + 1).choose k * (n + k + 2))
    rw [bakerDelta_succ, taylor_mul]
    refine (l1Norm_mul_le _ _).trans ?_
    calc (taylor x (bakerDelta k)).l1Norm * (taylor x (C ((k + 1 : ℚ)⁻¹) * X + 1)).l1Norm
        ≤ ((n + k + 1).choose k : ℝ) * ((n + k + 2 : ℝ) / (k + 1)) :=
          mul_le_mul ih hlin' (l1Norm_nonneg _) (by positivity)
      _ = ((n + (k + 1) + 1).choose (k + 1) : ℝ) := by
          rw [mul_div_assoc', div_eq_iff (by positivity), hchoose]

/-- **The size bound.** If `|x| ≤ n`, then for all `k, l, m`,

`|Δ(x; k, l, m)| = |(1 / m!) (d / dx) ^ m (Δ(x; k) ^ l)| ≤ 2 ^ (l (n + k + 1))`. -/
theorem abs_eval_hasseDeriv_bakerDelta_pow_le {x : ℚ} {n : ℕ} (hx : |x| ≤ n) (k l m : ℕ) :
    |(hasseDeriv m (bakerDelta k ^ l)).eval x| ≤ 2 ^ (l * (n + k + 1)) := by
  have h : ((|(hasseDeriv m (bakerDelta k ^ l)).eval x| : ℚ) : ℝ) ≤ 2 ^ (l * (n + k + 1)) := by
    rw [Rat.cast_abs, ← Real.norm_eq_abs, Rat.norm_cast_real, ← taylor_coeff, taylor_pow]
    refine (norm_coeff_le_l1Norm _ m).trans ((l1Norm_pow_le _ l).trans ?_)
    rw [pow_mul']
    refine pow_le_pow_left₀ (l1Norm_nonneg _) ?_ l
    exact (l1Norm_taylor_bakerDelta_le hx k).trans (by exact_mod_cast Nat.choose_le_two_pow _ _)
  exact_mod_cast h

end TauCeti
