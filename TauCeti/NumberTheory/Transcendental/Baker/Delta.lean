/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Bounds
import TauCeti.Analysis.Polynomial.L1Norm
import TauCeti.RingTheory.Binomial

/-!
# Baker's binomial polynomials

For `k : ℕ`, Baker's binomial polynomial is

`Δ(X; k) = (X + 1) (X + 2) ⋯ (X + k) / k!`,

so that `Δ(n; k) = (n + k choose k)` at natural numbers `n`. In the language of binomial rings this
is the multiset coefficient `Ring.multichoose (X + 1 : ℚ[X]) k`, which is how it is written here;
its Pascal recursion is `Ring.multichoose_succ_succ`, and its translates and values follow from
`Ring.map_multichoose`. In the method of linear forms in logarithms, archimedean as well as
`p`-adic, the auxiliary functions are built from the divided derivatives

`Δ(x; k, l, m) = (1 / m!) (d / dx) ^ m (Δ(x; k) ^ l)`,

which are written here as `(hasseDeriv m (Ring.multichoose (X + 1 : ℚ[X]) k ^ l)).eval x`. The
estimates on such an auxiliary function at integral points use two bounds for these numbers: a
denominator bound and a size bound.

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

## Main results

* `TauCeti.degree_multichoose_X_add_one`: `Δ(X; k)` has degree `k`.
* `TauCeti.multichoose_X_add_one_comp_C_add_C_mul_X_mem_lifts`: `Δ(a + L X; k)` has integral
  coefficients.
* `TauCeti.pow_mul_eval_hasseDeriv_multichoose_X_add_one_pow_mem_range_intCast`: Baker's
  denominator bound, `L ^ m Δ(x; k, l, m) ∈ ℤ` for integral `x`.
* `TauCeti.lcm_pow_mul_eval_hasseDeriv_multichoose_X_add_one_pow_mem_range_intCast`: its classical
  form, with `L = lcm(1, …, k)`.
* `TauCeti.pow_mul_eval_hasseDeriv_map_multichoose_X_add_one_comp_C_mul_X_mem_range_intCast`: the
  denominator bound for `Δ(q X; k)` over a field of characteristic zero, at points `x` with
  `q x` integral.
* `TauCeti.eval_map_multichoose_X_add_one_comp_C_mul_X_mem_range_intCast`: its case `m = 0`,
  `Δ(q x; k) ∈ ℤ`.
* `TauCeti.bakerDeltaSequence`: for `q ≠ 0`, the polynomials `Δ(q X; k)` over a field of
  characteristic zero form a polynomial sequence.
* `TauCeti.abs_eval_hasseDeriv_multichoose_X_add_one_pow_le`: the size bound.

## References

* A. Baker, *A sharpening of the bounds for linear forms in logarithms*, Acta Arith. **21**
  (1972), 117–129.
* Kunrui Yu, *Linear forms in p-adic logarithms II*, Compositio Math. **74** (1990), 15–113, §1.
-/

public section

open Polynomial
open scoped Nat

namespace TauCeti

/-- The product recursion: `Δ(X; k + 1) = Δ(X; k) (X / (k + 1) + 1)`, the case `r = X + 1` of
`TauCeti.Ring.add_one_nsmul_multichoose_add_one`. -/
private theorem multichoose_X_add_one_succ (k : ℕ) :
    Ring.multichoose (X + 1 : ℚ[X]) (k + 1) =
      Ring.multichoose (X + 1 : ℚ[X]) k * (C ((k + 1 : ℚ)⁻¹) * X + 1) := by
  have h : C ((k + 1 : ℚ)⁻¹) * ((k : ℚ[X]) + 1) = 1 := by
    simpa using congrArg C (inv_mul_cancel₀ (by positivity : (k + 1 : ℚ) ≠ 0))
  rw [← nsmul_right_inj k.succ_ne_zero, TauCeti.Ring.add_one_nsmul_multichoose_add_one,
    nsmul_eq_mul]
  push_cast
  linear_combination -(Ring.multichoose (X + 1 : ℚ[X]) k * X) * h

/-- Baker's binomial polynomial `Δ(X; k)` has degree `k`. -/
@[simp]
theorem degree_multichoose_X_add_one (k : ℕ) :
    (Ring.multichoose (X + 1 : ℚ[X]) k).degree = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [multichoose_X_add_one_succ, degree_mul, ih, ← C_1,
      degree_linear (inv_ne_zero (by positivity))]
    norm_cast

/-- Baker's binomial polynomial `Δ(X; k)` has natural degree `k`. -/
@[simp]
theorem natDegree_multichoose_X_add_one (k : ℕ) :
    (Ring.multichoose (X + 1 : ℚ[X]) k).natDegree = k :=
  natDegree_eq_of_degree_eq_some (degree_multichoose_X_add_one k)

/-- Composition with `q` is the binomial-ring specialisation `X ↦ q`: `Δ(q; n)` is
`Ring.multichoose (q + 1) n`. -/
private theorem multichoose_X_add_one_comp (q : ℚ[X]) (n : ℕ) :
    (Ring.multichoose (X + 1 : ℚ[X]) n).comp q = Ring.multichoose (q + 1) n := by
  simpa using Ring.map_multichoose (compRingHom q) (X + 1) n

/-- `Δ(L X; k)` has integral coefficients when each of `1, …, k` divides `L`: it is the product of
the integral linear polynomials `1 + (L / j) X` for `1 ≤ j ≤ k`. -/
private theorem multichoose_X_add_one_comp_C_mul_X_mem_lifts {k : ℕ} {L : ℤ}
    (hL : ∀ j ∈ Finset.Icc 1 k, (j : ℤ) ∣ L) :
    (Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (L : ℚ) * X) ∈
      lifts (Int.castRingHom ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := hL (k + 1) (by simp)
    have hlin : (C ((k + 1 : ℚ)⁻¹) * X + 1).comp (C (L : ℚ) * X) =
        C (Int.castRingHom ℚ c) * X + 1 := by
      have hc' : C ((k + 1 : ℚ)⁻¹) * (L : ℚ[X]) = c := by
        simpa using congrArg C (show (k + 1 : ℚ)⁻¹ * L = c by rw [hc]; push_cast; field_simp)
      simp [← mul_assoc, hc']
    rw [multichoose_X_add_one_succ, mul_comp, hlin]
    refine mul_mem (ih fun j hj => hL j ?_) (add_mem (mul_mem (C_mem_lifts _ c) (X_mem_lifts _))
      (one_mem _))
    simp only [Finset.mem_Icc] at hj ⊢
    omega

/-- **Integer translates of Baker's binomial polynomial.** If each of `1, …, k` divides the
integer `L`, then `Δ(a + L X; k)` has integral coefficients for every integer `a`. -/
theorem multichoose_X_add_one_comp_C_add_C_mul_X_mem_lifts {k : ℕ} {L : ℤ}
    (hL : ∀ j ∈ Finset.Icc 1 k, (j : ℤ) ∣ L) (a : ℤ) :
    (Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (a : ℚ) + C (L : ℚ) * X) ∈
      lifts (Int.castRingHom ℚ) := by
  rw [lifts_iff_liftsRing]
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have ih' : ∀ a : ℤ,
        (Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (a : ℚ) + C (L : ℚ) * X) ∈
          liftsRing (Int.castRingHom ℚ) := ih fun j hj => hL j (by
      simp only [Finset.mem_Icc] at hj ⊢
      omega)
    -- The Pascal recursion `Ring.multichoose_succ_succ` evaluated along `a + L X`.
    have hP : ∀ a : ℤ, (Ring.multichoose (X + 1 : ℚ[X]) (k + 1)).comp
        (C ((a + 1 : ℤ) : ℚ) + C (L : ℚ) * X) =
          (Ring.multichoose (X + 1 : ℚ[X]) (k + 1)).comp (C (a : ℚ) + C (L : ℚ) * X) +
            (Ring.multichoose (X + 1 : ℚ[X]) k).comp
              (C ((a + 1 : ℤ) : ℚ) + C (L : ℚ) * X) := by
      intro a
      convert Ring.multichoose_succ_succ (C (a : ℚ) + C (L : ℚ) * X + 1) k using 2 <;>
        simp only [multichoose_X_add_one_comp, Int.cast_add, Int.cast_one, map_add, map_one] <;>
        congr 1 <;> ring
    induction a using Int.induction_on with
    | zero => simpa [← lifts_iff_liftsRing] using multichoose_X_add_one_comp_C_mul_X_mem_lifts hL
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
theorem pow_mul_eval_hasseDeriv_multichoose_X_add_one_pow_mem_range_intCast {k : ℕ} {L : ℤ}
    (hL : ∀ j ∈ Finset.Icc 1 k, (j : ℤ) ∣ L) (l m : ℕ) (x : ℤ) :
    (L : ℚ) ^ m * (hasseDeriv m (Ring.multichoose (X + 1 : ℚ[X]) k ^ l)).eval (x : ℚ) ∈
      Set.range (Int.cast : ℤ → ℚ) := by
  have h := pow_mem (multichoose_X_add_one_comp_C_add_C_mul_X_mem_lifts hL x) l
  have e : (Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (x : ℚ) + C (L : ℚ) * X) ^ l =
      (taylor (x : ℚ) (Ring.multichoose (X + 1 : ℚ[X]) k ^ l)).comp (C (L : ℚ) * X) := by
    simp [taylor_apply, comp_assoc, add_comm]
  rw [e, lifts_iff_coeff_lifts] at h
  obtain ⟨z, hz⟩ := h m
  rw [comp_C_mul_X_coeff, taylor_coeff, eq_intCast] at hz
  exact ⟨z, hz.trans (mul_comm _ _)⟩

/-- **Baker's denominator bound**, classical form: for every integer `x` and all `l, m`,
`lcm(1, …, k) ^ m Δ(x; k, l, m)` is an integer. -/
theorem lcm_pow_mul_eval_hasseDeriv_multichoose_X_add_one_pow_mem_range_intCast
    (k l m : ℕ) (x : ℤ) :
    (((Finset.Icc 1 k).lcm id : ℕ) : ℚ) ^ m *
        (hasseDeriv m (Ring.multichoose (X + 1 : ℚ[X]) k ^ l)).eval (x : ℚ) ∈
      Set.range (Int.cast : ℤ → ℚ) := by
  simpa using pow_mul_eval_hasseDeriv_multichoose_X_add_one_pow_mem_range_intCast
    (L := ((Finset.Icc 1 k).lcm id : ℕ)) (fun j hj => Int.natCast_dvd_natCast.mpr
      (Finset.dvd_lcm (f := id) hj)) l m x

/-- **Baker's denominator bound at points of a scaled lattice.** Let `K` be a field of
characteristic zero, `q` an integer and `x ∈ K` with `q x` an integer, and let `L` be an integer
divisible by each of `1, …, k`. Then for every `m`,

`L ^ m (1 / m!) (d / dx) ^ m Δ(q x; k)`

is an integer. Here `Δ(q X; k)` is mapped to `K[X]` and differentiated in `X`. For `q = 1` and
`x` integral this is the case `l = 1` of
`TauCeti.pow_mul_eval_hasseDeriv_multichoose_X_add_one_pow_mem_range_intCast`. -/
theorem pow_mul_eval_hasseDeriv_map_multichoose_X_add_one_comp_C_mul_X_mem_range_intCast
    {K : Type*} [Field K] [CharZero K] {k : ℕ} {L : ℤ}
    (hL : ∀ j ∈ Finset.Icc 1 k, (j : ℤ) ∣ L) (q : ℤ) {x : K}
    (hx : (q : K) * x ∈ Set.range (Int.cast : ℤ → K)) (m : ℕ) :
    (L : K) ^ m * (hasseDeriv m (((Ring.multichoose (X + 1 : ℚ[X]) k).comp
      (C (q : ℚ) * X)).map (algebraMap ℚ K))).eval x ∈ Set.range (Int.cast : ℤ → K) := by
  obtain ⟨a, ha⟩ := hx
  -- The Taylor expansion of `Δ(q X; k)` at `x` is `Δ(a + q X; k)`, with `a = q x`.
  have htaylor : taylor x (((Ring.multichoose (X + 1 : ℚ[X]) k).comp
      (C (q : ℚ) * X)).map (algebraMap ℚ K)) =
      ((Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (a : ℚ) + C (q : ℚ) * X)).map
        (algebraMap ℚ K) := by
    rw [taylor_apply, Polynomial.map_comp, Polynomial.map_comp, comp_assoc]
    congr 1
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
      mul_comp, C_comp, X_comp]
    rw [mul_add, ← C_mul, map_intCast (algebraMap ℚ K), map_intCast (algebraMap ℚ K), ha, add_comm]
  -- Rescaling `X` by `L` makes the coefficients integral.
  have hL' : ∀ j ∈ Finset.Icc 1 k, (j : ℤ) ∣ q * L := fun j hj ↦ (hL j hj).mul_left q
  have h := multichoose_X_add_one_comp_C_add_C_mul_X_mem_lifts hL' a
  have e : (Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (a : ℚ) + C ((q * L : ℤ) : ℚ) * X) =
      ((Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (a : ℚ) + C (q : ℚ) * X)).comp
        (C (L : ℚ) * X) := by
    rw [comp_assoc]
    congr 1
    simp only [add_comp, C_comp, mul_comp, X_comp, Int.cast_mul, C_mul]
    ring
  rw [e, lifts_iff_coeff_lifts] at h
  obtain ⟨z, hz⟩ := h m
  rw [comp_C_mul_X_coeff, eq_intCast] at hz
  refine ⟨z, ?_⟩
  rw [← taylor_coeff, htaylor, coeff_map, ← map_intCast (algebraMap ℚ K) L, ← map_pow, ← map_mul,
    mul_comm, ← hz, map_intCast]

/-- **Integer values of Baker's binomial polynomial at points of a scaled lattice.** Let `K` be a
field of characteristic zero, `q` an integer and `x ∈ K` with `q x` an integer. Then `Δ(q x; k)`
is an integer. -/
theorem eval_map_multichoose_X_add_one_comp_C_mul_X_mem_range_intCast {K : Type*} [Field K]
    [CharZero K] (k : ℕ) (q : ℤ) {x : K} (hx : (q : K) * x ∈ Set.range (Int.cast : ℤ → K)) :
    (((Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (q : ℚ) * X)).map (algebraMap ℚ K)).eval x ∈
      Set.range (Int.cast : ℤ → K) := by
  -- This is the case `m = 0` of the denominator bound, with `L = k!`.
  simpa using pow_mul_eval_hasseDeriv_map_multichoose_X_add_one_comp_C_mul_X_mem_range_intCast
    (L := (k.factorial : ℤ)) (fun j hj ↦ Int.natCast_dvd_natCast.2
      (Nat.dvd_factorial (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2)) q hx 0

/-- For an integer `q ≠ 0`, Baker's binomial polynomials `Δ(q X; k)`, mapped to `K[X]` for a
field `K` of characteristic zero, form a polynomial sequence: `Δ(q X; k)` has degree `k`. -/
noncomputable def bakerDeltaSequence (K : Type*) [Field K] [CharZero K] {q : ℤ} (hq : q ≠ 0) :
    Polynomial.Sequence K where
  elems' k := ((Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (q : ℚ) * X)).map (algebraMap ℚ K)
  degree_eq' k := by
    have hlin : (C (q : ℚ) * X).degree = 1 := degree_C_mul_X (Int.cast_ne_zero.2 hq)
    rw [degree_map_eq_of_injective (algebraMap ℚ K).injective,
      degree_comp (by rw [hlin]; exact zero_lt_one), hlin, degree_multichoose_X_add_one, mul_one]

/-- The `k`-th term of `TauCeti.bakerDeltaSequence K hq` is `Δ(q X; k)`. -/
@[simp]
theorem bakerDeltaSequence_apply (K : Type*) [Field K] [CharZero K] {q : ℤ} (hq : q ≠ 0)
    (k : ℕ) :
    bakerDeltaSequence K hq k =
      ((Ring.multichoose (X + 1 : ℚ[X]) k).comp (C (q : ℚ) * X)).map (algebraMap ℚ K) :=
  (rfl)

/-- The leading coefficients of the polynomials `Δ(q X; k)` are units. -/
theorem isUnit_leadingCoeff_bakerDeltaSequence (K : Type*) [Field K] [CharZero K] {q : ℤ}
    (hq : q ≠ 0) (k : ℕ) : IsUnit (bakerDeltaSequence K hq k).leadingCoeff :=
  isUnit_iff_ne_zero.2 (leadingCoeff_ne_zero.2 ((bakerDeltaSequence K hq).ne_zero k))

/-- The coefficient length of the translate `Δ(X + x; k)` is at most `(n + k + 1 choose k)`
whenever `|x| ≤ n`. -/
private theorem l1Norm_taylor_multichoose_X_add_one_le {x : ℚ} {n : ℕ} (hx : |x| ≤ n)
    (k : ℕ) :
    (taylor x (Ring.multichoose (X + 1 : ℚ[X]) k)).l1Norm ≤ ((n + k + 1).choose k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- The new linear factor is `X / (k + 1) + (x / (k + 1) + 1)`.
    have hlin : taylor x (C ((k + 1 : ℚ)⁻¹) * X + 1) =
        C ((k + 1 : ℚ)⁻¹) * X + C ((k + 1 : ℚ)⁻¹ * x + 1) := by
      simp
      ring
    have hlin' : (taylor x (C ((k + 1 : ℚ)⁻¹) * X + 1)).l1Norm ≤ ((n + k + 2 : ℝ)) / (k + 1) := by
      have hx' : ‖x‖ ≤ n := by
        simp only [← Rat.norm_cast_real, Real.norm_eq_abs]
        exact_mod_cast hx
      have hc : ‖(k + 1 : ℚ)⁻¹‖ = ((k : ℝ) + 1)⁻¹ := by
        simp only [← Rat.norm_cast_real, Real.norm_eq_abs]
        push_cast
        exact abs_of_pos (by positivity)
      rw [hlin]
      calc (C ((k + 1 : ℚ)⁻¹) * X + C ((k + 1 : ℚ)⁻¹ * x + 1)).l1Norm
          ≤ ‖(k + 1 : ℚ)⁻¹‖ + (‖(k + 1 : ℚ)⁻¹‖ * ‖x‖ + 1) := by
            refine (l1Norm_C_mul_X_add_C_le _ _).trans ?_
            gcongr
            exact (norm_add_le _ _).trans (by rw [norm_mul, norm_one])
        _ ≤ ((k : ℝ) + 1)⁻¹ + (((k : ℝ) + 1)⁻¹ * n + 1) := by rw [hc]; gcongr
        _ = (n + k + 2) / (k + 1) := by field_simp; ring
    have hchoose : ((n + (k + 1) + 1).choose (k + 1) : ℝ) * (k + 1) =
        ((n + k + 1).choose k : ℝ) * (n + k + 2) := by
      have := congrArg (Nat.cast : ℕ → ℝ) (Nat.add_one_mul_choose_eq (n + k + 1) k)
      rw [show n + (k + 1) + 1 = n + k + 1 + 1 by omega]
      push_cast at this ⊢
      linarith
    rw [multichoose_X_add_one_succ, taylor_mul]
    refine (l1Norm_mul_le _ _).trans ?_
    calc (taylor x (Ring.multichoose (X + 1 : ℚ[X]) k)).l1Norm *
          (taylor x (C ((k + 1 : ℚ)⁻¹) * X + 1)).l1Norm
        ≤ ((n + k + 1).choose k : ℝ) * ((n + k + 2 : ℝ) / (k + 1)) :=
          mul_le_mul ih hlin' (l1Norm_nonneg _) (by positivity)
      _ = ((n + (k + 1) + 1).choose (k + 1) : ℝ) := by
          rw [mul_div_assoc', div_eq_iff (by positivity), hchoose]

/-- **The size bound.** If `|x| ≤ n`, then for all `k, l, m`,

`|Δ(x; k, l, m)| = |(1 / m!) (d / dx) ^ m (Δ(x; k) ^ l)| ≤ 2 ^ (l (n + k + 1))`. -/
theorem abs_eval_hasseDeriv_multichoose_X_add_one_pow_le {x : ℚ} {n : ℕ} (hx : |x| ≤ n)
    (k l m : ℕ) :
    |(hasseDeriv m (Ring.multichoose (X + 1 : ℚ[X]) k ^ l)).eval x| ≤ 2 ^ (l * (n + k + 1)) := by
  have h : ‖(hasseDeriv m (Ring.multichoose (X + 1 : ℚ[X]) k ^ l)).eval x‖ ≤
      2 ^ (l * (n + k + 1)) := by
    rw [← taylor_coeff, taylor_pow]
    refine (norm_coeff_le_l1Norm _ m).trans ((l1Norm_pow_le _ l).trans ?_)
    rw [pow_mul']
    refine pow_le_pow_left₀ (l1Norm_nonneg _) ?_ l
    exact (l1Norm_taylor_multichoose_X_add_one_le hx k).trans
      (by exact_mod_cast Nat.choose_le_two_pow _ _)
  rw [← Rat.cast_le (K := ℝ)]
  simpa [← Rat.norm_cast_real, Real.norm_eq_abs] using h

end TauCeti
