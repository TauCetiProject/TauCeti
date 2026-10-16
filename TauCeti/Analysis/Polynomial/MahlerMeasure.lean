/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Algebra.Polynomial.Homogenize

/-!
# The binary form of a complex polynomial near one of its roots

Let `f ∈ ℂ[X]` have degree `d` and let `F(x, y) = y ^ d f(x / y)` be its homogenization of
degree `d`. If `α` is a root of `f`, then `F` is small at points `(x, y)` close to the line
`x = α y`: writing `f = a ∏ (X - αᵢ)` with `α₁ = α`, every other factor of
`F(x, y) = a ∏ (x - αᵢ y)` is at most `2 max(1, |αᵢ|) max(|x|, |y|)`, which gives
`|F(x, y)| ≤ 2 ^ (d - 1) M(f) max(|x|, |y|) ^ (d - 1) |x - α y|`, where `M(f)` is the Mahler
measure. Dividing by `y` turns this into a bound by the distance `|x / y - α|`.

Applied to a polynomial with integer coefficients at an integer point where `F` does not vanish,
the left-hand side is at least `1`; this is Liouville's inequality.

## Main results

* `Polynomial.norm_eval_homogenize_le_mahlerMeasure_mul`:
  `‖F(x)‖ ≤ 2 ^ (d - 1) M(f) ‖x‖ ^ (d - 1) ‖x 0 - α x 1‖` for every `x : Fin 2 → ℂ`.
* `Polynomial.norm_eval_homogenize_le_mahlerMeasure_mul_norm_div_sub`:
  `‖F(x)‖ ≤ 2 ^ (d - 1) M(f) ‖x‖ ^ d ‖x 0 / x 1 - α‖` when `x 1 ≠ 0`.

Here `‖x‖ = max ‖x 0‖ ‖x 1‖` is the sup norm on `Fin 2 → ℂ`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, proof of Theorem 6.1.
-/

public section

namespace Polynomial

/-- If `α` is a root of `f ∈ ℂ[X]` of degree `d`, the homogenization `F` of `f` in degree `d`
satisfies `‖F(x)‖ ≤ 2 ^ (d - 1) M(f) ‖x‖ ^ (d - 1) ‖x 0 - α x 1‖` at every point
`x : Fin 2 → ℂ`, where `M(f)` is the Mahler measure and `‖x‖` the sup norm. -/
theorem norm_eval_homogenize_le_mahlerMeasure_mul (f : ℂ[X]) {α : ℂ} (hα : f.IsRoot α)
    (x : Fin 2 → ℂ) :
    ‖MvPolynomial.eval x (f.homogenize f.natDegree)‖ ≤
      2 ^ (f.natDegree - 1) * f.mahlerMeasure * ‖x‖ ^ (f.natDegree - 1) * ‖x 0 - α * x 1‖ := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  -- Each linear factor `x 0 - a x 1` is at most `2 max(1, ‖a‖) ‖x‖`.
  have hprod (s : Multiset ℂ) : ‖(s.map fun a ↦ x 0 - a * x 1).prod‖ ≤
      (2 * ‖x‖) ^ Multiset.card s * (s.map fun a ↦ max 1 ‖a‖).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ]
      have h0 := norm_le_pi_norm x 0
      have h1 := norm_le_pi_norm x 1
      have hfac : ‖x 0 - a * x 1‖ ≤ 2 * ‖x‖ * max 1 ‖a‖ := by
        calc ‖x 0 - a * x 1‖ ≤ ‖x 0‖ + ‖a‖ * ‖x 1‖ := (norm_sub_le _ _).trans_eq (by simp)
          _ ≤ max 1 ‖a‖ * ‖x‖ + max 1 ‖a‖ * ‖x‖ := by
            gcongr
            · exact h0.trans (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
            · exact le_max_right _ _
          _ = 2 * ‖x‖ * max 1 ‖a‖ := by ring
      calc ‖x 0 - a * x 1‖ * ‖(s.map fun a ↦ x 0 - a * x 1).prod‖
          ≤ (2 * ‖x‖ * max 1 ‖a‖) * ((2 * ‖x‖) ^ Multiset.card s *
              (s.map fun a ↦ max 1 ‖a‖).prod) := by gcongr
        _ = _ := by ring
  have hroots : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem ((mem_roots hf).2 hα)
  have hd : f.natDegree - 1 = Multiset.card s := by
    rw [← hroots, hs, Multiset.card_cons, Nat.add_sub_cancel]
  rw [eval_homogenize_natDegree_of_card_roots hroots, mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    hs, hd]
  simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
  have hP : 0 ≤ (s.map fun a ↦ max 1 ‖a‖).prod :=
    Multiset.prod_nonneg fun b hb ↦ by
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hb
      positivity
  calc ‖f.leadingCoeff‖ * (‖x 0 - α * x 1‖ * ‖(s.map fun a ↦ x 0 - a * x 1).prod‖)
      ≤ ‖f.leadingCoeff‖ * (‖x 0 - α * x 1‖ *
          ((2 * ‖x‖) ^ Multiset.card s * (max 1 ‖α‖ * (s.map fun a ↦ max 1 ‖a‖).prod))) := by
        gcongr
        exact (hprod s).trans (by gcongr; exact le_mul_of_one_le_left hP (le_max_left _ _))
    _ = _ := by ring

/-- If `α` is a root of `f ∈ ℂ[X]` of degree `d`, the homogenization `F` of `f` in degree `d`
satisfies `‖F(x)‖ ≤ 2 ^ (d - 1) M(f) ‖x‖ ^ d ‖x 0 / x 1 - α‖` at every point `x : Fin 2 → ℂ`
with `x 1 ≠ 0`, where `M(f)` is the Mahler measure and `‖x‖` the sup norm. -/
theorem norm_eval_homogenize_le_mahlerMeasure_mul_norm_div_sub (f : ℂ[X]) {α : ℂ}
    (hα : f.IsRoot α) {x : Fin 2 → ℂ} (hx : x 1 ≠ 0) :
    ‖MvPolynomial.eval x (f.homogenize f.natDegree)‖ ≤
      2 ^ (f.natDegree - 1) * f.mahlerMeasure * ‖x‖ ^ f.natDegree * ‖x 0 / x 1 - α‖ := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one.2
    (natDegree_pos_iff_degree_pos.2 (degree_pos_of_root hf hα))
  have hsub : ‖x 0 - α * x 1‖ = ‖x 1‖ * ‖x 0 / x 1 - α‖ := by
    rw [← norm_mul, mul_sub, mul_div_cancel₀ _ hx, mul_comm]
  have hM := (mahlerMeasure_pos_of_ne_zero hf).le
  calc _ ≤ 2 ^ n * f.mahlerMeasure * ‖x‖ ^ n * (‖x 1‖ * ‖x 0 / x 1 - α‖) := by
        simpa [hn, hsub] using norm_eval_homogenize_le_mahlerMeasure_mul f hα x
    _ ≤ 2 ^ n * f.mahlerMeasure * ‖x‖ ^ n * (‖x‖ * ‖x 0 / x 1 - α‖) := by
        gcongr; exact norm_le_pi_norm x 1
    _ = _ := by rw [hn, Nat.add_sub_cancel, pow_succ]; ring

end Polynomial
