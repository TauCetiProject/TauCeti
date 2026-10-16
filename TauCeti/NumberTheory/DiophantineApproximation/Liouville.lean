/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.Analysis.Polynomial.MahlerMeasure
public import TauCeti.FieldTheory.Minpoly.Primitive

/-!
# Liouville's inequality with an explicit constant

Let `f ∈ ℤ[X]` have degree `d` and a complex root `α`, and let `ξ = p / q` be a rational number,
written in lowest terms with `q > 0`, at which `f` does not vanish. The value of the
homogenization of `f` at `(p, q)` is the nonzero integer `q ^ d f(ξ)`, so it has absolute value
at least `1`. Comparing with the upper bound of
`Polynomial.norm_eval_homogenize_le_mahlerMeasure_mul_norm_div_sub` gives Liouville's inequality
`|ξ - α| ≥ (2 ^ (d - 1) M(f) H(ξ) ^ d)⁻¹`, where `M(f)` is the Mahler measure of `f` and
`H(ξ) = max(|p|, q)` is the height of `ξ`.

For an algebraic number `α` we apply this to its primitive minimal polynomial `F_α`, which
vanishes at no rational number other than `α`.

## Main results

* `Polynomial.inv_le_norm_ratCast_sub`: Liouville's inequality for an integer polynomial `f`
  with root `α` at a rational `ξ` with `f(ξ) ≠ 0`.
* `IsAlgebraic.inv_le_norm_ratCast_sub`: Liouville's inequality for an algebraic
  number `α` of degree `d` and a rational number `ξ ≠ α`, with constant `2 ^ (1 - d) M(F_α)⁻¹`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Theorem 6.1.
-/

public section

open Height

namespace Polynomial

/-- **Liouville's inequality.** Let `f ∈ ℤ[X]` have degree `d` and a complex root `α`. Every
rational number `ξ` with `f(ξ) ≠ 0` satisfies `|ξ - α| ≥ (2 ^ (d - 1) M(f) H(ξ) ^ d)⁻¹`, where
`M(f)` is the Mahler measure of `f` and `H(ξ)` the height of `ξ`. -/
theorem inv_le_norm_ratCast_sub (f : ℤ[X]) {α : ℂ} (hα : (f.map (Int.castRingHom ℂ)).IsRoot α)
    {ξ : ℚ} (hξ : aeval ξ f ≠ 0) :
    (2 ^ (f.natDegree - 1) * (f.map (Int.castRingHom ℂ)).mahlerMeasure *
        mulHeight₁ ξ ^ f.natDegree)⁻¹ ≤ ‖(ξ : ℂ) - α‖ := by
  have hf : f ≠ 0 := by rintro rfl; simp at hξ
  have hg : f.map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hf
  -- The homogenization `F` of `f` at `y = (num ξ, den ξ)` is a nonzero integer `n`, since its
  -- image in `ℚ` is `den ξ ^ d f(ξ)`.
  set y : Fin 2 → ℤ := ![ξ.num, ξ.den]
  set n : ℤ := MvPolynomial.eval y (f.homogenize f.natDegree)
  have hcast {S : Type} [CommRing S] (φ : ℤ →+* S) :
      MvPolynomial.eval (φ ∘ y) ((f.map φ).homogenize f.natDegree) = φ n := by
    rw [homogenize_map, MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]
  have hn : n ≠ 0 := by
    have hq : (Int.castRingHom ℚ ∘ y) 1 ≠ 0 := by simp [y]
    have h := eval_homogenize (p := f.map (Int.castRingHom ℚ)) natDegree_map_le _ hq
    rw [hcast] at h
    have hξ' : (ξ.num : ℚ) / ξ.den = ξ := Rat.num_div_den ξ
    simp only [Function.comp_apply, y, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, eq_intCast, Int.cast_natCast, hξ'] at h
    rw [← algebraMap_int_eq, eval_map_algebraMap] at h
    intro hn0
    rw [hn0, Int.cast_zero, eq_comm, mul_eq_zero] at h
    exact h.elim hξ (pow_ne_zero _ (by simp))
  have hx : (Int.castRingHom ℂ ∘ y) 1 ≠ 0 := by simp [y]
  have hdiv : (Int.castRingHom ℂ ∘ y) 0 / (Int.castRingHom ℂ ∘ y) 1 = ξ := by
    simp [y, Rat.cast_def]
  have hnorm : ‖Int.castRingHom ℂ ∘ y‖ ≤ mulHeight₁ ξ := by
    rw [Rat.mulHeight₁_eq_max]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
    fin_cases i <;> simp [y, Complex.norm_intCast]
  have key := norm_eval_homogenize_le_mahlerMeasure_mul_norm_div_sub _ hα hx
  rw [natDegree_map_eq_of_injective (RingHom.injective_int _), hcast, hdiv] at key
  have h1 : (1 : ℝ) ≤ ‖Int.castRingHom ℂ n‖ := by
    rw [eq_intCast, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hn
  have hM := mahlerMeasure_pos_of_ne_zero hg
  rw [inv_le_iff_one_le_mul₀' (by positivity)]
  calc (1 : ℝ) ≤ _ := h1.trans key
    _ ≤ _ := by gcongr

end Polynomial

namespace TauCeti

open Polynomial

/-- **Liouville's inequality** for an algebraic number. Let `α ∈ ℂ` be algebraic of degree `d`
with primitive minimal polynomial `F_α ∈ ℤ[X]`. Every rational number `ξ ≠ α` satisfies
`|ξ - α| ≥ (2 ^ (d - 1) M(F_α) H(ξ) ^ d)⁻¹`, where `M(F_α)` is the Mahler measure of `F_α` (the
Mahler measure of `α`) and `H(ξ)` the height of `ξ`. -/
theorem _root_.IsAlgebraic.inv_le_norm_ratCast_sub {α : ℂ} (hα : IsAlgebraic ℚ α) {ξ : ℚ}
    (hξ : (ξ : ℂ) ≠ α) :
    (2 ^ ((minpoly ℚ α).natDegree - 1) *
        ((primitiveMinpoly α).map (Int.castRingHom ℂ)).mahlerMeasure *
        mulHeight₁ ξ ^ (minpoly ℚ α).natDegree)⁻¹ ≤ ‖(ξ : ℂ) - α‖ := by
  rw [← natDegree_primitiveMinpoly]
  refine Polynomial.inv_le_norm_ratCast_sub _ ?_ fun h ↦ hξ ?_
  · rw [IsRoot.def, ← algebraMap_int_eq, eval_map_algebraMap]
    exact aeval_primitiveMinpoly hα
  -- `F_α` is a nonzero multiple of `minpoly ℚ α`, so `ξ` is a rational root of `minpoly ℚ α`,
  -- which forces `ξ = α`.
  rw [← eval_map_algebraMap, algebraMap_int_eq, map_primitiveMinpoly hα, eval_mul, eval_C,
    mul_eq_zero, Int.cast_eq_zero] at h
  have hroot : aeval ξ (minpoly ℚ α) = 0 :=
    h.resolve_left (leadingCoeff_primitiveMinpoly_pos α).ne'
  rw [aeval_def, Algebra.algebraMap_self, eval₂_id] at hroot
  simpa using minpoly.root hα.isIntegral hroot

end TauCeti
