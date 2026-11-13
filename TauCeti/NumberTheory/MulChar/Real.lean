/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.Finite
public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Real multiplicative characters are quadratic

Let `χ` be a multiplicative character on a commutative monoid with finitely many units, with
values in `ℝ`, `ℂ` or any other `RCLike` field. The value of `χ` at a unit has finite order, so
it has norm one, and a real number of norm one is `1` or `-1`; at a nonunit `χ` vanishes. Hence
`χ` is real-valued exactly when it is quadratic in the sense of `MulChar.IsQuadratic`, that is
when all its values lie in `{0, 1, -1}`. The principal character is included on both sides: it
is real-valued and quadratic. This is the identification of real characters with quadratic ones
in Montgomery–Vaughan, *Multiplicative Number Theory I*, §9.3, p. 295, where "quadratic" means
exact order two and so excludes the principal character.

Dirichlet characters of every level `N`, including `N = 0`, are covered, since `(ZMod N)ˣ` is
finite: for a complex Dirichlet character `χ`, `MulChar.isQuadratic_iff_forall_im_eq_zero` reads
`χ.IsQuadratic ↔ ∀ a, (χ a).im = 0`, as `RCLike.im` on `ℂ` is `Complex.im`.

## Main results

* `MulChar.norm_apply_unit`: the values at units of a character on a monoid with finitely many
  units, with values in a normed field, have norm one.
* `MulChar.isQuadratic_iff_forall_conj_eq`: a character with finitely many units in its domain
  is quadratic iff it is fixed by complex conjugation.
* `MulChar.isQuadratic_iff_forall_im_eq_zero`: the same with the imaginary parts of its values.
-/

public section

open ComplexConjugate

namespace MulChar

variable {R : Type*} [CommMonoid R] [Finite Rˣ]

/-- The value of a multiplicative character at a unit of a monoid with finitely many units, with
values in a normed field, has norm one. -/
@[simp]
theorem norm_apply_unit {F : Type*} [NormedField F] (χ : MulChar R F) (u : Rˣ) : ‖χ u‖ = 1 := by
  rw [← coe_toUnitHom]
  exact (Units.coeHom F).isOfFinOrder (χ.toUnitHom.isOfFinOrder (isOfFinOrder_of_finite u))
    |>.norm_eq_one

variable {K : Type*} [RCLike K]

/-- A multiplicative character on a monoid with finitely many units, with values in an `RCLike`
field, is quadratic iff it is fixed by conjugation. This includes the principal character. -/
theorem isQuadratic_iff_forall_conj_eq {χ : MulChar R K} :
    χ.IsQuadratic ↔ ∀ a, conj (χ a) = χ a := by
  refine ⟨fun hχ a ↦ ?_, fun h a ↦ ?_⟩
  · rcases hχ a with h | h | h <;> simp [h]
  by_cases ha : IsUnit a
  · right
    obtain ⟨r, hr⟩ := RCLike.conj_eq_iff_real.mp (h a)
    have hnorm := χ.norm_apply_unit ha.unit
    rw [IsUnit.unit_spec, hr, RCLike.norm_ofReal] at hnorm
    rcases abs_eq (zero_le_one' ℝ) |>.mp hnorm with rfl | rfl <;> simp [hr]
  · exact Or.inl (map_nonunit χ ha)

/-- A multiplicative character on a monoid with finitely many units, with values in an `RCLike`
field, is quadratic iff all its values have imaginary part zero. This includes the principal
character. -/
theorem isQuadratic_iff_forall_im_eq_zero {χ : MulChar R K} :
    χ.IsQuadratic ↔ ∀ a, RCLike.im (χ a) = 0 := by
  simp_rw [isQuadratic_iff_forall_conj_eq, RCLike.conj_eq_iff_im]

end MulChar
