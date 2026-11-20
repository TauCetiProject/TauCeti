/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.NumberTheory.DirichletCharacter.GaussSum

/-!
# The Pólya–Vinogradov inequality

A nonprincipal primitive Dirichlet character `χ` modulo `N` has sums over every interval, and over
every arithmetic progression whose step is prime to `N`, bounded by `√N (1 + log N)`, independently
of the length of the interval.

Writing `e(x) = exp (2 π i x / N)` and `τ = g(χ⁻¹)` for the Gauss sum of `χ⁻¹`, primitivity gives
the finite Fourier expansion `χ(n) τ = ∑_b χ⁻¹(b) e(b n)` at every residue `n`. Summing over an
interval `a + k`, `0 ≤ k < H`, interchanges the sums into incomplete geometric sums
`∑_{k<H} e(b k)`, which are bounded by `ZMod.sum_norm_sum_range_stdAddChar_mul_le`; the term `b = 0`
vanishes because `χ⁻¹(0) = 0`. Dividing by `‖τ‖ = √N` and bounding the harmonic number
`H_{N-1} ≤ 1 + log N` gives the inequality.

The bound is uniform in the starting point and the length, so it applies at once to sums
`∑_{m ≤ k < n} χ(k)` over natural intervals and to sums over residue classes modulo a step prime
to `N`. In particular it applies to primitive quadratic characters, the case used to truncate real
character `L`-series in the arithmetic of quadratic fields.

## Main results

* `DirichletCharacter.IsPrimitive.norm_sum_range_add_le`: `‖∑_{k<H} χ(a + k)‖ ≤ √N (1 + log N)`.
* `DirichletCharacter.IsPrimitive.norm_sum_range_add_mul_le`: the same bound for
  `∑_{k<H} χ(a + k s)` with `s` a unit modulo `N`.
* `DirichletCharacter.IsPrimitive.norm_sum_Ico_le`: the same bound for `∑_{m ≤ k < n} χ(k)`.

## References

* G. Pólya, *Über die Verteilung der quadratischen Reste und Nichtreste*, Nachr. Ges. Wiss.
  Göttingen (1918), 21–29.
* I. M. Vinogradov, *Sur la distribution des résidus et des non-résidus des puissances*, J. Phys.
  Math. Soc. Perm 1 (1918), 94–96.
* H. Davenport, *Multiplicative Number Theory*, Chapter 23.
-/

public section

open Finset Real ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **The Pólya–Vinogradov inequality.** A nonprincipal primitive Dirichlet character modulo `N`
has every sum over `H` consecutive residues `a, a + 1, …, a + H - 1` of norm at most
`√N (1 + log N)`. -/
theorem IsPrimitive.norm_sum_range_add_le (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (a : ZMod N)
    (H : ℕ) : ‖∑ k ∈ range H, χ (a + k)‖ ≤ √N * (1 + log N) := by
  have hN1 : N ≠ 1 := by
    rintro rfl
    exact hχ1 (Subsingleton.elim _ _)
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  set e : AddChar (ZMod N) ℂ := stdAddChar
  set τ := gaussSum χ⁻¹ e
  have hτ : ‖τ‖ = √N := hχ.inv.norm_gaussSum (isPrimitive_stdAddChar N)
  -- The Fourier expansion of `χ` at a residue, from the Gauss sum of the primitive `χ⁻¹`.
  have hexp (n : ZMod N) : χ n * τ = ∑ b, χ⁻¹ b * e (n * b) := by
    simpa [τ, gaussSum, AddChar.mulShift_apply] using
      (gaussSum_mulShift_of_isPrimitive e hχ.inv n).symm
  have hsum : τ * ∑ k ∈ range H, χ (a + k) =
      ∑ b, χ⁻¹ b * e (a * b) * ∑ k ∈ range H, e (b * (k : ZMod N)) := by
    rw [mul_sum]
    simp_rw [mul_comm τ, hexp, mul_sum, add_mul, AddChar.map_add_eq_mul]
    rw [sum_comm]
    refine sum_congr rfl fun b _ ↦ sum_congr rfl fun k _ ↦ ?_
    rw [mul_comm (k : ZMod N) b]
    ring
  have hbound : ‖τ * ∑ k ∈ range H, χ (a + k)‖ ≤ N * (1 + log N) := by
    rw [hsum]
    calc
      _ ≤ ∑ b, ‖χ⁻¹ b * e (a * b) * ∑ k ∈ range H, e (b * (k : ZMod N))‖ := norm_sum_le _ _
      _ = ∑ b ∈ univ.erase 0, ‖χ⁻¹ b * e (a * b) * ∑ k ∈ range H, e (b * (k : ZMod N))‖ :=
        (sum_erase _ (by simp [χ⁻¹.map_zero' hN1])).symm
      _ ≤ ∑ b ∈ univ.erase 0, ‖∑ k ∈ range H, e (b * (k : ZMod N))‖ := by
        refine sum_le_sum fun b _ ↦ ?_
        rw [norm_mul, norm_mul, stdAddChar_apply, Circle.norm_coe, mul_one]
        exact mul_le_of_le_one_left (norm_nonneg _) (χ⁻¹.norm_le_one b)
      _ ≤ N * (harmonic (N - 1) : ℝ) := sum_norm_sum_range_stdAddChar_mul_le H
      _ ≤ N * (1 + log N) := by
        gcongr
        refine (harmonic_le_one_add_log _).trans ?_
        have : 1 ≤ N - 1 := by have := NeZero.pos N; omega
        gcongr
        exact Nat.sub_le N 1
  rw [norm_mul, hτ] at hbound
  have hsqrt : 0 < √(N : ℝ) := sqrt_pos.mpr hN
  rw [← mul_le_mul_iff_of_pos_left hsqrt, ← mul_assoc, mul_self_sqrt hN.le]
  exact hbound

/-- **The Pólya–Vinogradov inequality on arithmetic progressions.** A nonprincipal primitive
Dirichlet character modulo `N` has every sum over `H` consecutive terms `a + k s` of a progression
whose step `s` is a unit modulo `N` of norm at most `√N (1 + log N)`. -/
theorem IsPrimitive.norm_sum_range_add_mul_le (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (a : ZMod N)
    {s : ZMod N} (hs : IsUnit s) (H : ℕ) :
    ‖∑ k ∈ range H, χ (a + k * s)‖ ≤ √N * (1 + log N) := by
  obtain ⟨u, rfl⟩ := hs
  have h (k : ℕ) : a + k * (u : ZMod N) = u * (a * ↑u⁻¹ + k) := by
    rw [mul_add, mul_left_comm, Units.mul_inv, mul_one, mul_comm (u : ZMod N)]
  simp_rw [h, map_mul, ← mul_sum, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
    (hχ.norm_sum_range_add_le hχ1 _ H)

/-- **The Pólya–Vinogradov inequality on intervals of natural numbers.** A nonprincipal primitive
Dirichlet character modulo `N` has every sum `∑_{m ≤ k < n} χ(k)` of norm at most
`√N (1 + log N)`. -/
theorem IsPrimitive.norm_sum_Ico_le (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (m n : ℕ) :
    ‖∑ k ∈ Ico m n, χ k‖ ≤ √N * (1 + log N) := by
  rw [sum_Ico_eq_sum_range]
  push_cast
  exact hχ.norm_sum_range_add_le hχ1 m (n - m)

end DirichletCharacter
