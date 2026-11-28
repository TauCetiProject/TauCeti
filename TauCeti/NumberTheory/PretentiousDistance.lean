/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.PrimeCounting
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.Real.Sqrt

/-!
# The pretentious distance

For functions `f, g : ℕ → ℂ` and a real cutoff `x`, the *pretentious distance* of Granville and
Soundararajan is

  `D(f, g; x) = √(∑_{p ≤ x} (1 - Re (f(p) conj(g(p)))) / p)`,

the sum being over the primes `p ≤ x`. It measures how far the values of `f` at the primes are
from those of `g`, and is the quantity that controls mean values of multiplicative functions in
Halász's theorem. It is used for functions with values in the closed unit disc at the primes,
where every summand is nonnegative.

`D` is a distance on prime data and not a metric: `D(f, f; x)` is positive when `|f(p)| < 1` at
some prime `p ≤ x`. What holds for all functions with values in the unit disc is the triangle
inequality for products, `D(f₁ f₂, g₁ g₂; x) ≤ D(f₁, g₁; x) + D(f₂, g₂; x)`, and the triangle
inequality `D(f, h; x) ≤ D(f, g; x) + D(g, h; x)`. The second is usually deduced from the first
when `|g(p)| = 1`; here it is proved for every `g` with values in the unit disc, from the
three-point inequality `Complex.sqrt_one_sub_re_mul_conj_le`. In all statements the hypotheses
are only required at the primes up to the cutoff, and they are no stronger than each proof uses:
the product inequality needs only `|f₁(p) conj(g₁(p))| ≤ 1` and `|f₂(p) conj(g₂(p))| ≤ 1`, and
monotonicity in the cutoff needs only `Re (f(p) conj(g(p))) ≤ 1` at the new primes.

## Main definitions

* `TauCeti.pretentiousDist f g x`: the pretentious distance `D(f, g; x)`.

## Main results

* `TauCeti.sq_pretentiousDist`: the formula for `D(f, g; x)²` when the sum is nonnegative, as it
  is by `TauCeti.sum_primesLE_one_sub_re_mul_conj_div_nonneg` when `Re (f(p) conj(g(p))) ≤ 1` at
  the primes up to `x`.
* `TauCeti.pretentiousDist_comm`, `TauCeti.pretentiousDist_congr`: symmetry, and dependence on
  the values at the primes up to `x` only.
* `TauCeti.pretentiousDist_mono`, `TauCeti.sq_pretentiousDist_mono`: monotonicity in `x` of the
  distance and of its square.
* `TauCeti.pretentiousDist_eq_zero_iff`, `TauCeti.pretentiousDist_self`: for functions with
  values in the closed unit disc, `D(f, g; x) = 0` exactly when `f(p) = g(p)` has modulus `1` at
  every prime `p ≤ x`; in particular `D(f, f; x) = 0` for `f` of modulus `1` at the primes.
* `TauCeti.pretentiousDist_mul_le`: the triangle inequality for products.
* `TauCeti.pretentiousDist_triangle`: the triangle inequality.

## References

* A. Granville, K. Soundararajan, *Pretentious multiplicative functions and an inequality for the
  zeta-function*, arXiv:math/0608407.
-/

public section

open Finset
open scoped ComplexConjugate

namespace TauCeti

/-- The *pretentious distance* `D(f, g; x) = √(∑_{p ≤ x} (1 - Re (f(p) conj(g(p)))) / p)` of
Granville and Soundararajan, the sum being over the primes `p ≤ x`. It only depends on the values
of `f` and `g` at the primes up to `x`, and is meant for `f` and `g` with values in the closed
unit disc there. -/
noncomputable def pretentiousDist (f g : ℕ → ℂ) (x : ℝ) : ℝ :=
  √(∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (f p * conj (g p)).re) / p)

/-- The defining formula of `pretentiousDist`. -/
theorem pretentiousDist_def (f g : ℕ → ℂ) (x : ℝ) :
    pretentiousDist f g x = √(∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (f p * conj (g p)).re) / p) :=
  (rfl)

variable {f g h f₁ f₂ g₁ g₂ : ℕ → ℂ} {x y : ℝ}

/-- The pretentious distance is nonnegative. -/
theorem pretentiousDist_nonneg (f g : ℕ → ℂ) (x : ℝ) : 0 ≤ pretentiousDist f g x := by
  rw [pretentiousDist_def]
  exact Real.sqrt_nonneg _

/-- The sum under the square root of `D(f, g; x)` is nonnegative when `Re (f(p) conj(g(p))) ≤ 1`
at the primes `p ≤ x`, in particular for `f`, `g` with values in the closed unit disc there. -/
theorem sum_primesLE_one_sub_re_mul_conj_div_nonneg
    (h : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → (f p * conj (g p)).re ≤ 1) :
    0 ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (f p * conj (g p)).re) / p :=
  sum_nonneg fun p hp ↦ div_nonneg
    (sub_nonneg.2 (h p (Nat.prime_of_mem_primesLE hp) (Nat.le_of_mem_primesLE hp)))
    (Nat.cast_nonneg p)

/-- If the sum `∑_{p ≤ x} (1 - Re (f(p) conj(g(p)))) / p` is nonnegative, it is `D(f, g; x)²`. -/
theorem sq_pretentiousDist
    (h : 0 ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (f p * conj (g p)).re) / p) :
    pretentiousDist f g x ^ 2 = ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (f p * conj (g p)).re) / p := by
  rw [pretentiousDist_def]
  exact Real.sq_sqrt h

/-- The pretentious distance is symmetric. -/
theorem pretentiousDist_comm (f g : ℕ → ℂ) (x : ℝ) :
    pretentiousDist f g x = pretentiousDist g f x := by
  rw [pretentiousDist_def, pretentiousDist_def]
  refine congrArg _ (sum_congr rfl fun p _ ↦ ?_)
  rw [← Complex.conj_re (g p * conj (f p)), map_mul, Complex.conj_conj, mul_comm]

/-- The pretentious distance only depends on the values at the primes up to `x`. -/
theorem pretentiousDist_congr (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → f₁ p = f₂ p)
    (hg : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → g₁ p = g₂ p) :
    pretentiousDist f₁ g₁ x = pretentiousDist f₂ g₂ x := by
  rw [pretentiousDist_def, pretentiousDist_def]
  refine congrArg _ (sum_congr rfl fun p hp ↦ ?_)
  obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.1 hp
  rw [hf p hp hpx, hg p hp hpx]

/-- There are no primes below `2`, so the pretentious distance vanishes for `x < 2`. -/
@[simp]
theorem pretentiousDist_of_lt_two (f g : ℕ → ℂ) (hx : x < 2) : pretentiousDist f g x = 0 := by
  have hfloor : ⌊x⌋₊ ≤ 1 := Nat.lt_succ_iff.1 ((Nat.floor_lt' two_ne_zero).2 (by simpa using hx))
  have h : Nat.primesLE ⌊x⌋₊ = ∅ :=
    subset_empty.1 ((Nat.primesLE_mono hfloor).trans_eq Nat.primesLE_one)
  rw [pretentiousDist_def, h, sum_empty, Real.sqrt_zero]

/-- If `Re (f(p) conj(g(p))) ≤ 1` at the primes `p` with `x < p ≤ y`, then the pretentious distance
up to `x ≤ y` is at most the distance up to `y`. -/
theorem pretentiousDist_mono
    (h : ∀ p : ℕ, p.Prime → ⌊x⌋₊ < p → p ≤ ⌊y⌋₊ → (f p * conj (g p)).re ≤ 1) (hxy : x ≤ y) :
    pretentiousDist f g x ≤ pretentiousDist f g y := by
  rw [pretentiousDist_def, pretentiousDist_def]
  refine Real.sqrt_le_sqrt (sum_le_sum_of_subset_of_nonneg
    (Nat.primesLE_mono (Nat.floor_le_floor hxy)) fun p hpy hpx ↦ ?_)
  obtain ⟨hpy', hp⟩ := Nat.mem_primesLE.1 hpy
  have hlt : ⌊x⌋₊ < p := lt_of_not_ge fun hle ↦ hpx (Nat.mem_primesLE.2 ⟨hle, hp⟩)
  exact div_nonneg (sub_nonneg.2 (h p hp hlt hpy')) (Nat.cast_nonneg p)

/-- If `Re (f(p) conj(g(p))) ≤ 1` at the primes `p` with `x < p ≤ y`, then the squared pretentious
distance up to `x ≤ y` is at most the squared distance up to `y`. -/
theorem sq_pretentiousDist_mono
    (h : ∀ p : ℕ, p.Prime → ⌊x⌋₊ < p → p ≤ ⌊y⌋₊ → (f p * conj (g p)).re ≤ 1) (hxy : x ≤ y) :
    pretentiousDist f g x ^ 2 ≤ pretentiousDist f g y ^ 2 :=
  pow_le_pow_left₀ (pretentiousDist_nonneg f g x) (pretentiousDist_mono h hxy) 2

/-- **Vanishing of the pretentious distance.** For `f` and `g` with values in the closed unit disc
at the primes up to `x`, `D(f, g; x) = 0` exactly when `f(p) = g(p)` has modulus `1` at every
prime `p ≤ x`. -/
theorem pretentiousDist_eq_zero_iff (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f p‖ ≤ 1)
    (hg : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖g p‖ ≤ 1) :
    pretentiousDist f g x = 0 ↔ ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → f p = g p ∧ ‖f p‖ = 1 := by
  have hnn : ∀ p ∈ Nat.primesLE ⌊x⌋₊, 0 ≤ (1 - (f p * conj (g p)).re) / p := fun p hp ↦ by
    obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.1 hp
    exact div_nonneg (Complex.one_sub_re_mul_conj_nonneg
      ((mul_le_of_le_one_left (norm_nonneg _) (hf p hp hpx)).trans (hg p hp hpx)))
      (Nat.cast_nonneg p)
  rw [pretentiousDist_def, Real.sqrt_eq_zero (sum_nonneg hnn), sum_eq_zero_iff_of_nonneg hnn]
  refine forall_congr' fun p ↦ ⟨fun h hp hpx ↦ ?_, fun h hp ↦ ?_⟩
  · have h0 := h (Nat.mem_primesLE.2 ⟨hpx, hp⟩)
    rw [div_eq_zero_iff, sub_eq_zero] at h0
    exact (Complex.re_mul_conj_eq_one_iff (hf p hp hpx) (hg p hp hpx)).1
      (h0.resolve_right (Nat.cast_ne_zero.2 hp.ne_zero)).symm
  · obtain ⟨hpx, hp'⟩ := Nat.mem_primesLE.1 hp
    rw [(Complex.re_mul_conj_eq_one_iff (hf p hp' hpx) (hg p hp' hpx)).2 (h hp' hpx), sub_self,
      zero_div]

/-- A function of modulus `1` at the primes up to `x` is at distance `0` from itself. For values
inside the unit disc this fails: `D(0, 0; 2)² = 1 / 2`. -/
@[simp]
theorem pretentiousDist_self (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f p‖ = 1) :
    pretentiousDist f f x = 0 :=
  (pretentiousDist_eq_zero_iff (fun p hp hpx ↦ (hf p hp hpx).le)
    fun p hp hpx ↦ (hf p hp hpx).le).2 fun p hp hpx ↦ ⟨rfl, hf p hp hpx⟩

/-! ### Triangle inequalities -/

/-- **The triangle inequality for products**: if `f₁ conj(g₁)` and `f₂ conj(g₂)` take values in
the closed unit disc at the primes up to `x`, in particular if `f₁`, `f₂`, `g₁`, `g₂` do, then
`D(f₁ f₂, g₁ g₂; x) ≤ D(f₁, g₁; x) + D(f₂, g₂; x)`. -/
theorem pretentiousDist_mul_le
    (h₁ : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f₁ p * conj (g₁ p)‖ ≤ 1)
    (h₂ : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f₂ p * conj (g₂ p)‖ ≤ 1) :
    pretentiousDist (f₁ * f₂) (g₁ * g₂) x ≤ pretentiousDist f₁ g₁ x + pretentiousDist f₂ g₂ x := by
  rw [pretentiousDist_def, pretentiousDist_def, pretentiousDist_def]
  refine Real.sqrt_sum_le_sqrt_sum_add_sqrt_sum (fun p hp ↦ ?_) (fun p hp ↦ ?_) fun p hp ↦ ?_
  · obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.1 hp
    exact div_nonneg (sub_nonneg.2 ((Complex.re_le_norm _).trans (h₁ p hp hpx)))
      (Nat.cast_nonneg p)
  · obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.1 hp
    exact div_nonneg (sub_nonneg.2 ((Complex.re_le_norm _).trans (h₂ p hp hpx)))
      (Nat.cast_nonneg p)
  · obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.1 hp
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, mul_mul_mul_comm]
    exact Real.sqrt_div_le_sqrt_div_add_sqrt_div
      (Complex.sqrt_one_sub_re_mul_le (h₁ p hp hpx) (h₂ p hp hpx)) (Nat.cast_nonneg p)

/-- **The triangle inequality** for the pretentious distance: if `f`, `g` and `h` take values in
the closed unit disc at the primes up to `x`, then `D(f, h; x) ≤ D(f, g; x) + D(g, h; x)`. -/
theorem pretentiousDist_triangle (hf : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖f p‖ ≤ 1)
    (hg : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖g p‖ ≤ 1)
    (hh : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ‖h p‖ ≤ 1) :
    pretentiousDist f h x ≤ pretentiousDist f g x + pretentiousDist g h x := by
  rw [pretentiousDist_def, pretentiousDist_def, pretentiousDist_def]
  refine Real.sqrt_sum_le_sqrt_sum_add_sqrt_sum (fun p hp ↦ ?_) (fun p hp ↦ ?_) fun p hp ↦ ?_
  · obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.1 hp
    exact div_nonneg (Complex.one_sub_re_mul_conj_nonneg
      ((mul_le_of_le_one_left (norm_nonneg _) (hf p hp hpx)).trans (hg p hp hpx)))
      (Nat.cast_nonneg p)
  · obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.1 hp
    exact div_nonneg (Complex.one_sub_re_mul_conj_nonneg
      ((mul_le_of_le_one_left (norm_nonneg _) (hg p hp hpx)).trans (hh p hp hpx)))
      (Nat.cast_nonneg p)
  · obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.1 hp
    exact Real.sqrt_div_le_sqrt_div_add_sqrt_div (Complex.sqrt_one_sub_re_mul_conj_le
      (hf p hp hpx) (hg p hp hpx) (hh p hp hpx)) (Nat.cast_nonneg p)

/-! ### Examples -/

example : pretentiousDist 1 1 x = 0 := pretentiousDist_self (by simp)

example : pretentiousDist f g 1 = 0 := pretentiousDist_of_lt_two f g one_lt_two

example : pretentiousDist 1 (-1) x ^ 2 = 2 * ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 / p : ℝ) := by
  rw [sq_pretentiousDist (sum_primesLE_one_sub_re_mul_conj_div_nonneg fun p _ _ ↦ by simp),
    mul_sum]
  refine sum_congr rfl fun p _ ↦ ?_
  simp
  ring

example : pretentiousDist 0 0 2 ^ 2 = 1 / 2 := by
  have h : Nat.primesLE 2 = {2} := by decide
  rw [sq_pretentiousDist (sum_primesLE_one_sub_re_mul_conj_div_nonneg fun p _ _ ↦ by simp),
    Nat.floor_ofNat, h]
  simp

end TauCeti
