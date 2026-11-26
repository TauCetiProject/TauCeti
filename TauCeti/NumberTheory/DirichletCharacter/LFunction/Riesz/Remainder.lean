/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.Chebyshev.RieszRemainder
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import TauCeti.NumberTheory.DirichletCharacter.Bounds

/-!
# Lipschitz and size bounds for the Riesz remainder of a Dirichlet character

For a nonprincipal Dirichlet character `χ` the *Riesz remainder* is
`G_χ(y) = ∑_{1 ≤ n ≤ y} χ(n) Λ(n) (y / n - 1) + y (L′/L)(1, χ)`, with the sum written as
`TauCeti.rieszSum (fun n ↦ χ n * Λ n) y` and `(L′/L)(1, χ)` as
`logDeriv (LFunction χ) 1`. Since `‖χ(n) Λ(n)‖ ≤ Λ(n)`
(`DirichletCharacter.norm_mul_vonMangoldt_le`), the bounds of
`TauCeti.NumberTheory.Chebyshev.RieszRemainder` for coefficients dominated by `Λ` give, for
`a ≥ 0`, `w, w' > 0` and `y, z` with `max y z ≥ 1`, resp. `y ≥ 1`,
* `‖w G_χ(a / w) - w' G_χ(a / w')‖ ≤ 3 (a / min w w') |w - w'|`;
* `‖G_χ(y) - G_χ(z)‖ ≤ |y - z| (log (max y z) + log 4 + 4 + ‖(L′/L)(1, χ)‖)`;
* `‖G_χ(y)‖ ≤ y (log y + log 4 + 4 + ‖(L′/L)(1, χ)‖)`.

The statements for `DirichletCharacter` carry no hypothesis on `χ`: for a nonprincipal `χ` they
bound the Riesz remainder, while for a principal `χ` the function `L(·, χ)` has a pole at `1` and
the constant is Mathlib's junk value of `logDeriv (LFunction χ) 1`. For primitive characters the
same bounds are stated on `TauCeti.PrimitiveDirichletCharacter.rieszRemainder`, whose
conductor-one branch is the real remainder `G_1` of `TauCeti.NumberTheory.Chebyshev.RieszRemainder`.
The Mellin side of the Riesz remainder is treated in
`TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin`.

## Main results

* `DirichletCharacter.norm_mul_rieszSum_div_add_mul_logDeriv_sub_le`,
  `DirichletCharacter.norm_rieszSum_add_mul_logDeriv_sub_le`,
  `DirichletCharacter.norm_rieszSum_add_mul_logDeriv_le`: the three bounds for `G_χ`.
* `TauCeti.PrimitiveDirichletCharacter.rieszRemainder_one_eq_ofReal`: the conductor-one remainder
  is the real remainder `G_1`.
* `TauCeti.PrimitiveDirichletCharacter.norm_mul_rieszRemainder_div_sub_le`: the bound in the weight
  for every primitive character.
* `TauCeti.PrimitiveDirichletCharacter.norm_rieszRemainder_sub_le_of_ne_one`,
  `TauCeti.PrimitiveDirichletCharacter.norm_rieszRemainder_le_of_ne_one`,
  `TauCeti.PrimitiveDirichletCharacter.norm_one_rieszRemainder_sub_le`,
  `TauCeti.PrimitiveDirichletCharacter.norm_one_rieszRemainder_le`: the Lipschitz and size bounds
  in the two branches.

## References

* The Riesz remainder `G_χ` and these bounds, in the form with an absolute constant, are those of
  the formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  https://github.com/leanprover-community/riemann-hypothesis.
-/

public section

open ArithmeticFunction TauCeti
open Real (eulerMascheroniConstant)

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- **Lipschitz bound in the weight for the Riesz remainder of a Dirichlet character.**
Let `G_χ(y) = ∑_{1 ≤ n ≤ y} χ(n) Λ(n) (y / n - 1) + y (L′/L)(1, χ)`. For
`a ≥ 0` and `w, w' > 0`, `‖w G_χ(a / w) - w' G_χ(a / w')‖ ≤ 3 (a / min w w') |w - w'|`. For a
nonprincipal `χ`, `G_χ` is the Riesz remainder; for a principal `χ` the constant is Mathlib's junk
value of `logDeriv (LFunction χ) 1` at the pole
(`Chebyshev.norm_mul_rieszSum_div_add_mul_sub_le` holds for every constant). -/
theorem norm_mul_rieszSum_div_add_mul_logDeriv_sub_le {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w)
    (hw' : 0 < w') :
    ‖(w : ℂ) * (rieszSum (fun n ↦ χ n * Λ n) (a / w) +
          ((a / w : ℝ) : ℂ) * logDeriv (LFunction χ) 1) -
        (w' : ℂ) * (rieszSum (fun n ↦ χ n * Λ n) (a / w') +
          ((a / w' : ℝ) : ℂ) * logDeriv (LFunction χ) 1)‖ ≤
      3 * (a / min w w') * |w - w'| :=
  Chebyshev.norm_mul_rieszSum_div_add_mul_sub_le χ.norm_mul_vonMangoldt_le _ ha hw hw'

/-- **Lipschitz bound for the Riesz remainder of a Dirichlet character.**
Let `G_χ(y) = ∑_{1 ≤ n ≤ y} χ(n) Λ(n) (y / n - 1) + y (L′/L)(1, χ)`. If `max y z ≥ 1`, then
`‖G_χ(y) - G_χ(z)‖ ≤ |y - z| (log (max y z) + log 4 + 4 + ‖(L′/L)(1, χ)‖)`. For a principal `χ`
the constant `(L′/L)(1, χ)` is Mathlib's junk value at the pole. -/
theorem norm_rieszSum_add_mul_logDeriv_sub_le {y z : ℝ} (h : 1 ≤ max y z) :
    ‖(rieszSum (fun n ↦ χ n * Λ n) y + y * logDeriv (LFunction χ) 1) -
        (rieszSum (fun n ↦ χ n * Λ n) z + z * logDeriv (LFunction χ) 1)‖ ≤
      |y - z| * (Real.log (max y z) + (Real.log 4 + 4) + ‖logDeriv (LFunction χ) 1‖) :=
  Chebyshev.norm_rieszSum_add_mul_sub_le χ.norm_mul_vonMangoldt_le _ h

/-- **Size bound for the Riesz remainder of a Dirichlet character.** For
`y ≥ 1`, `‖∑_{1 ≤ n ≤ y} χ(n) Λ(n) (y / n - 1) + y (L′/L)(1, χ)‖ ≤
y (log y + log 4 + 4 + ‖(L′/L)(1, χ)‖)`. For a principal `χ` the constant `(L′/L)(1, χ)` is
Mathlib's junk value at the pole. -/
theorem norm_rieszSum_add_mul_logDeriv_le {y : ℝ} (hy : 1 ≤ y) :
    ‖rieszSum (fun n ↦ χ n * Λ n) y + y * logDeriv (LFunction χ) 1‖ ≤
      y * (Real.log y + (Real.log 4 + 4) + ‖logDeriv (LFunction χ) 1‖) :=
  Chebyshev.norm_rieszSum_add_mul_le χ.norm_mul_vonMangoldt_le _ hy

end DirichletCharacter

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
    exact Chebyshev.abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le ha hw hw'
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
theorem norm_one_rieszRemainder_sub_le {y z : ℝ} (hy : 1 ≤ y) (hz : 1 ≤ z) :
    ‖(1 : PrimitiveDirichletCharacter).rieszRemainder y -
        (1 : PrimitiveDirichletCharacter).rieszRemainder z‖ ≤
      (Real.log 4 + 4 + eulerMascheroniConstant) * |y - z| := by
  rw [rieszRemainder_one_eq_ofReal, rieszRemainder_one_eq_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le hy hz

/-- **Size bound for the conductor-one Riesz remainder.** For `y ≥ 1`,
`‖R_1(y)‖ ≤ (log 4 + 4 + γ) y`. -/
theorem norm_one_rieszRemainder_le {y : ℝ} (hy : 1 ≤ y) :
    ‖(1 : PrimitiveDirichletCharacter).rieszRemainder y‖ ≤
      (Real.log 4 + 4 + eulerMascheroniConstant) * y := by
  rw [rieszRemainder_one_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_le hy

end TauCeti.PrimitiveDirichletCharacter
