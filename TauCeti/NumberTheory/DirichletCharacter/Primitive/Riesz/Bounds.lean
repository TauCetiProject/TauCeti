/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebyshev.RieszRemainder
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz

/-!
# Lipschitz and size bounds for the primitive Riesz remainder

For a primitive Dirichlet character `χ`, `TauCeti.PrimitiveDirichletCharacter.rieszRemainder`
is `R_χ(y) = rieszSum (χ Λ) y + y (L′/L)(1, χ)` for `χ ≠ 1` and the real remainder
`G_1(y) = ∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y + (1 + γ) y` at conductor one
(`TauCeti.PrimitiveDirichletCharacter.rieszRemainder_one_eq_ofReal`). This file states the bounds
of `TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder` and
`TauCeti.NumberTheory.Chebyshev.RieszRemainder` on `R_χ`:
* the bound in the weight, `‖w R_χ(a / w) - w' R_χ(a / w')‖ ≤ 3 (a / min w w') |w - w'|`, for
  every `χ`;
* the Lipschitz and size bounds in the two branches;
* one absolute constant `C` serving in the Lipschitz and size bounds of both branches, the form
  (b′)–(c′) of the roadmap.

## Main results

* `TauCeti.PrimitiveDirichletCharacter.rieszRemainder_one_eq_ofReal`
* `TauCeti.PrimitiveDirichletCharacter.norm_mul_rieszRemainder_div_sub_le`
* `TauCeti.PrimitiveDirichletCharacter.norm_rieszRemainder_sub_le_of_ne_one`,
  `TauCeti.PrimitiveDirichletCharacter.norm_rieszRemainder_le_of_ne_one`
* `TauCeti.PrimitiveDirichletCharacter.norm_rieszRemainder_one_sub_le`,
  `TauCeti.PrimitiveDirichletCharacter.norm_rieszRemainder_one_le`
* `TauCeti.PrimitiveDirichletCharacter.exists_const_norm_rieszRemainder_le`: one absolute
  constant for both branches.

## References

* The existence of one absolute constant in these bounds is the form of the formal proof of the
  Riemann hypothesis for Dirichlet `L`-functions,
  https://github.com/leanprover-community/riemann-hypothesis; the explicit constant
  `2 + γ + (log 4 + 4)` is proved here.
-/

public section

open ArithmeticFunction
open Real (eulerMascheroniConstant)

namespace TauCeti.PrimitiveDirichletCharacter

/-- The Riesz remainder of the primitive character of conductor one is the real remainder
`G_1(y) = ∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y + (1 + γ) y`. -/
theorem rieszRemainder_one_eq_ofReal (y : ℝ) :
    (1 : PrimitiveDirichletCharacter).rieszRemainder y =
      ((∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) - y * Real.log y +
        (1 + eulerMascheroniConstant) * y : ℝ) : ℂ) := by
  rw [rieszRemainder_one, ← ofReal_sum_Ioc_floor_mul_div_sub_one]
  push_cast
  ring

/-- **Lipschitz bound in the weight for the primitive Riesz remainder.** For every primitive
character `χ`, `a ≥ 0` and `w, w' > 0`,
`‖w R_χ(a / w) - w' R_χ(a / w')‖ ≤ 3 (a / min w w') |w - w'|`. -/
theorem norm_mul_rieszRemainder_div_sub_le (χ : PrimitiveDirichletCharacter) {a w w' : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hw' : 0 < w') :
    ‖(w : ℂ) * χ.rieszRemainder (a / w) - (w' : ℂ) * χ.rieszRemainder (a / w')‖ ≤
      3 * (a / min w w') * |w - w'| := by
  by_cases hχ : χ = 1
  · subst hχ
    rw [rieszRemainder_one_eq_ofReal, rieszRemainder_one_eq_ofReal]
    norm_cast
    rw [Real.norm_eq_abs]
    exact Chebyshev.abs_mul_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le ha hw hw'
  · rw [rieszRemainder_of_ne_one hχ, rieszRemainder_of_ne_one hχ]
    exact χ.character.norm_mul_rieszSum_div_add_mul_logDeriv_sub_le ha hw hw'

/-- **Lipschitz bound for a nontrivial primitive Riesz remainder.** For `χ ≠ 1` and
`max y z ≥ 1`, `‖R_χ(y) - R_χ(z)‖ ≤ |y - z| (log (max y z) + log 4 + 4 + ‖(L′/L)(1, χ)‖)`. -/
theorem norm_rieszRemainder_sub_le_of_ne_one {χ : PrimitiveDirichletCharacter} (hχ : χ ≠ 1)
    {y z : ℝ} (h : 1 ≤ max y z) :
    ‖χ.rieszRemainder y - χ.rieszRemainder z‖ ≤
      |y - z| * (Real.log (max y z) + (Real.log 4 + 4) +
        ‖logDeriv χ.character.LFunction 1‖) := by
  rw [rieszRemainder_of_ne_one hχ, rieszRemainder_of_ne_one hχ]
  exact χ.character.norm_rieszSum_add_mul_logDeriv_sub_le h

/-- **Size bound for a nontrivial primitive Riesz remainder.** For `χ ≠ 1` and `y ≥ 1`,
`‖R_χ(y)‖ ≤ y (log y + log 4 + 4 + ‖(L′/L)(1, χ)‖)`. -/
theorem norm_rieszRemainder_le_of_ne_one {χ : PrimitiveDirichletCharacter} (hχ : χ ≠ 1)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖χ.rieszRemainder y‖ ≤
      y * (Real.log y + (Real.log 4 + 4) + ‖logDeriv χ.character.LFunction 1‖) := by
  rw [rieszRemainder_of_ne_one hχ]
  exact χ.character.norm_rieszSum_add_mul_logDeriv_le hy

/-- **Lipschitz bound for the conductor-one Riesz remainder.** For `y, z ≥ 1`,
`‖R_1(y) - R_1(z)‖ ≤ (log 4 + 4 + γ) |y - z|`. -/
theorem norm_rieszRemainder_one_sub_le {y z : ℝ} (hy : 1 ≤ y) (hz : 1 ≤ z) :
    ‖(1 : PrimitiveDirichletCharacter).rieszRemainder y -
        (1 : PrimitiveDirichletCharacter).rieszRemainder z‖ ≤
      (Real.log 4 + 4 + eulerMascheroniConstant) * |y - z| := by
  rw [rieszRemainder_one_eq_ofReal, rieszRemainder_one_eq_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le hy hz

/-- **Size bound for the conductor-one Riesz remainder.** For `y ≥ 1`,
`‖R_1(y)‖ ≤ (log 4 + 4 + γ) y`. -/
theorem norm_rieszRemainder_one_le {y : ℝ} (hy : 1 ≤ y) :
    ‖(1 : PrimitiveDirichletCharacter).rieszRemainder y‖ ≤
      (Real.log 4 + 4 + eulerMascheroniConstant) * y := by
  rw [rieszRemainder_one_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_le hy

/-- **One absolute constant for the Riesz remainders** (the form (b′)–(c′)). There is a constant
`C` (namely `2 + γ + (log 4 + 4)`) such that for every primitive character `χ` and `y, z ≥ 1`:
if `χ ≠ 1`, then `‖R_χ(y) - R_χ(z)‖ ≤ |y - z| (log (max y z) + C + ‖(L′/L)(1, χ)‖)` and
`‖R_χ(y)‖ ≤ y (log y + C + ‖(L′/L)(1, χ)‖)`; if `χ = 1`, then `‖R_1(y) - R_1(z)‖ ≤ C |y - z|`
and `‖R_1(y)‖ ≤ C y`. -/
theorem exists_const_norm_rieszRemainder_le :
    ∃ C : ℝ, ∀ χ : PrimitiveDirichletCharacter, ∀ y z : ℝ, 1 ≤ y → 1 ≤ z →
      (χ ≠ 1 →
        ‖χ.rieszRemainder y - χ.rieszRemainder z‖ ≤
            |y - z| * (Real.log (max y z) + C + ‖logDeriv χ.character.LFunction 1‖) ∧
          ‖χ.rieszRemainder y‖ ≤ y * (Real.log y + C + ‖logDeriv χ.character.LFunction 1‖)) ∧
      (χ = 1 → ‖χ.rieszRemainder y - χ.rieszRemainder z‖ ≤ C * |y - z| ∧
        ‖χ.rieszRemainder y‖ ≤ C * y) := by
  have hγ : 0 < eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  refine ⟨2 + eulerMascheroniConstant + (Real.log 4 + 4), fun χ y z hy hz ↦
    ⟨fun hχ ↦ ⟨?_, ?_⟩, fun hχ ↦ ?_⟩⟩
  · exact (norm_rieszRemainder_sub_le_of_ne_one hχ (le_max_of_le_left hy)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  · exact (norm_rieszRemainder_le_of_ne_one hχ hy).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  · subst hχ
    exact ⟨(norm_rieszRemainder_one_sub_le hy hz).trans
        (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)),
      (norm_rieszRemainder_one_le hy).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith))⟩

end TauCeti.PrimitiveDirichletCharacter
