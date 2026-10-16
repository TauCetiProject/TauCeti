/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.HilbertSymbol.Henselian
public import TauCeti.NumberTheory.LocalField.QuadraticForm.PadicTwo
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.NumberTheory.LocalField.Padic

/-!
# Worked examples: quaternion algebras over `ℚ` and its completions

This file checks the quaternion-algebra layer against the classical examples over `ℚ`, `ℝ`
and `ℚ_p`. Each example is a test that the splitting criterion
`TauCeti.QuaternionAlgebra.nonempty_algEquiv_matrix_tfae` and the norm-equation Hilbert symbol
`TauCeti.hilbertSymbol` carry the intended signs.

**Hamilton's quaternions.** `ℍ[ℚ,-1,-1]` and `ℍ[ℝ,-1,-1]` are division algebras, by Mathlib's
`DivisionRing ℍ[R]` over an ordered field, so `(-1, -1)_ℚ = (-1, -1)_ℝ = -1`. Over `ℚ_p` the
algebra `ℍ[ℚ_p,-1,-1]` splits exactly when `p ≠ 2`: for odd `p` the symbol of two units of
`ℤ_p` is `+1` by Hensel's lemma (`TauCeti.hilbertSymbol_units_map_eq_one`), and
`(-1, -1)_{ℚ_2} = -1` (`TauCeti.hilbertSymbol_neg_one_neg_one_padicTwo`). So among the
completions of `ℚ`, Hamilton's quaternions ramify exactly at `2` and at `∞`.

**Two dyadic symbols.** `ℍ[ℚ_2,2,5]` is a division algebra, since `(2, 5)_{ℚ_2} = -1`
(`TauCeti.hilbertSymbol_two_five_padicTwo`), while `ℍ[ℚ_2,5,5]` splits, with the witness
`5 = 5² - 5 · 2²` of the norm equation. The splitting criterion is five-way: splitting together
with four equivalent norm and isotropy conditions. At `(a, b) = (2, 5)` every one of the five
conditions fails, and at `(a, b) = (5, 5)` every one holds.

**Split algebras over `ℚ`.** `ℍ[ℚ,1,b]` is isomorphic to `M₂(ℚ)` for every `b ∈ ℚˣ`
(`TauCeti.QuaternionAlgebra.oneEquivMatrix`).

## Main results

* `Padic.hilbertSymbol_neg_one_neg_one_of_ne_two`: `(-1, -1)_{ℚ_p} = +1` for an odd prime `p`.
* `Padic.nonempty_algEquiv_matrix_neg_one_neg_one_iff`: `ℍ[ℚ_p,-1,-1] ≃ₐ M₂(ℚ_p)` exactly when
  `p ≠ 2`.
* `TauCeti.hilbertSymbol_neg_one_neg_one_rat`, `TauCeti.hilbertSymbol_neg_one_neg_one_real`:
  `(-1, -1)_ℚ = (-1, -1)_ℝ = -1`.
* `TauCeti.nonempty_algEquiv_matrix_tfae_two_five_padicTwo`,
  `TauCeti.nonempty_algEquiv_matrix_tfae_five_five_padicTwo`: the splitting criterion over `ℚ_2`
  at `(2, 5)` and `(5, 5)`, with the parameters written as literals.
* `TauCeti.isUnit_of_ne_zero_two_five_padicTwo`: `ℍ[ℚ_2,2,5]` is a division algebra.
* `TauCeti.nonempty_algEquiv_matrix_five_five_padicTwo`: `ℍ[ℚ_2,5,5]` splits.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, §2 and Chapter VI, §2.
-/

public section

open TauCeti QuadraticMap ValuativeRel
open scoped Quaternion

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- For an odd prime `p`, the Hilbert symbol `(-1, -1)` over `ℚ_p` is `+1`: by Hensel's lemma,
`-1` is a sum of two squares in `ℚ_p`, since `-1` and `2` are units of `ℤ_p`. -/
theorem hilbertSymbol_neg_one_neg_one_of_ne_two (hp : p ≠ 2) :
    hilbertSymbol (-1 : ℚ_[p]ˣ) (-1) = 1 := by
  have h2 : IsUnit (2 : 𝒪[ℚ_[p]]) :=
    (natCastValuation_eq_zero_iff (K := ℚ_[p]) 2 (by norm_num)).mp (natCastValuation_two p hp)
  have h := hilbertSymbol_units_map_eq_one (K := ℚ_[p]) h2 (-1) (-1)
  have hneg : Units.map (algebraMap 𝒪[ℚ_[p]] ℚ_[p] : 𝒪[ℚ_[p]] →* ℚ_[p]) (-1) = -1 := by
    ext
    simp
  rwa [hneg] at h

/-- **Hamilton's quaternions over `ℚ_p`.** The quaternion algebra `ℍ[ℚ_p,-1,-1]` is isomorphic
to `M₂(ℚ_p)` exactly when `p ≠ 2`. -/
theorem nonempty_algEquiv_matrix_neg_one_neg_one_iff :
    Nonempty (ℍ[ℚ_[p],-1,-1] ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) ↔ p ≠ 2 := by
  have h := hilbertSymbol_eq_one_iff_nonempty_algEquiv_matrix (-1 : ℚ_[p]ˣ) (-1)
  simp only [Units.val_neg, Units.val_one] at h
  rw [← h]
  refine ⟨fun h1 hp ↦ ?_, hilbertSymbol_neg_one_neg_one_of_ne_two p⟩
  subst hp
  rw [hilbertSymbol_neg_one_neg_one_padicTwo] at h1
  exact absurd h1 (by decide)

end Padic

namespace TauCeti

/-! ### Hamilton's quaternions over `ℚ` and `ℝ` -/

/-- `ℍ[ℚ,-1,-1]` is a division algebra. This is `Ne.isUnit` for Mathlib's `DivisionRing ℍ[ℚ]`,
so it is not restated as a named theorem. -/
example : ∀ x : ℍ[ℚ,-1,-1], x ≠ 0 → IsUnit x := fun _ hx ↦ hx.isUnit

/-- `ℍ[ℚ,-1,-1]` does not split. -/
theorem not_nonempty_algEquiv_matrix_neg_one_neg_one_rat :
    ¬Nonempty (ℍ[ℚ,-1,-1] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) := by
  have h := QuaternionAlgebra.nonempty_algEquiv_matrix_iff_not_forall_isUnit (-1 : ℚˣ) (-1)
  simp only [Units.val_neg, Units.val_one] at h
  rw [h, not_not]
  exact fun _ hx ↦ hx.isUnit

/-- `(-1, -1)_ℚ = -1`: `-1` is not a sum of two rational squares. -/
theorem hilbertSymbol_neg_one_neg_one_rat : hilbertSymbol (-1 : ℚˣ) (-1) = -1 := by
  have h := hilbertSymbol_eq_neg_one_iff_forall_isUnit (-1 : ℚˣ) (-1)
  simp only [Units.val_neg, Units.val_one] at h
  exact h.mpr fun _ hx ↦ hx.isUnit

/-- `(-1, -1)_ℝ = -1`, read off the division ring `ℍ[ℝ]`. -/
theorem hilbertSymbol_neg_one_neg_one_real : hilbertSymbol (-1 : ℝˣ) (-1) = -1 := by
  have h := hilbertSymbol_eq_neg_one_iff_forall_isUnit (-1 : ℝˣ) (-1)
  simp only [Units.val_neg, Units.val_one] at h
  exact h.mpr fun _ hx ↦ hx.isUnit

/-- Hamilton's quaternions split over `ℚ_3`: the case `p = 3` of
`Padic.nonempty_algEquiv_matrix_neg_one_neg_one_iff`. -/
example : Nonempty (ℍ[ℚ_[3],-1,-1] ≃ₐ[ℚ_[3]] Matrix (Fin 2) (Fin 2) ℚ_[3]) :=
  (Padic.nonempty_algEquiv_matrix_neg_one_neg_one_iff 3).mpr (by decide)

/-- Hamilton's quaternions do not split over `ℚ_2`. -/
theorem not_nonempty_algEquiv_matrix_neg_one_neg_one_padicTwo :
    ¬Nonempty (ℍ[ℚ_[2],-1,-1] ≃ₐ[ℚ_[2]] Matrix (Fin 2) (Fin 2) ℚ_[2]) :=
  fun h ↦ (Padic.nonempty_algEquiv_matrix_neg_one_neg_one_iff 2).mp h rfl

/-! ### Split algebras over `ℚ` -/

/-- `ℍ[ℚ,1,b]` splits for every `b ∈ ℚˣ`, witnessed by
`TauCeti.QuaternionAlgebra.oneEquivMatrix`. -/
example (b : ℚˣ) : Nonempty (ℍ[ℚ,1,(b : ℚ)] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) :=
  ⟨QuaternionAlgebra.oneEquivMatrix b⟩

/-! ### The five-way splitting criterion over `ℚ_2` at `(2, 5)`: every condition fails -/

section TwoFive

/-- The splitting criterion `TauCeti.QuaternionAlgebra.nonempty_algEquiv_matrix_tfae` at
`(a, b) = (2, 5)` over `ℚ_2`, with the parameters written as literals. -/
theorem nonempty_algEquiv_matrix_tfae_two_five_padicTwo :
    [Nonempty (ℍ[ℚ_[2],2,5] ≃ₐ[ℚ_[2]] Matrix (Fin 2) (Fin 2) ℚ_[2]),
      ∃ z : QuadraticAlgebra ℚ_[2] 2 0, z.norm = 5,
      ∃ x y : ℚ_[2], (5 : ℚ_[2]) = x ^ 2 - 2 * y ^ 2,
      ¬(weightedSumSquares ℚ_[2] ![1, -2, -5]).Anisotropic,
      ¬(_root_.QuaternionAlgebra.normForm (2 : ℚ_[2]) 0 5).Anisotropic].TFAE := by
  have h := QuaternionAlgebra.nonempty_algEquiv_matrix_tfae (Units.mk0 (2 : ℚ_[2]) two_ne_zero)
    (Units.mk0 5 (by norm_num))
  rwa [Units.val_mk0, Units.val_mk0] at h

/-- `ℍ[ℚ_2,2,5]` does not split, because `(2, 5)_{ℚ_2} = -1`. -/
theorem not_nonempty_algEquiv_matrix_two_five_padicTwo :
    ¬Nonempty (ℍ[ℚ_[2],2,5] ≃ₐ[ℚ_[2]] Matrix (Fin 2) (Fin 2) ℚ_[2]) := fun h ↦ by
  have h1 := (hilbertSymbol_eq_one_iff_nonempty_algEquiv_matrix (Units.mk0 (2 : ℚ_[2]) two_ne_zero)
    (Units.mk0 5 (by norm_num))).mpr h
  rw [hilbertSymbol_two_five_padicTwo] at h1
  exact absurd h1 (by decide)

/-- `ℍ[ℚ_2,2,5]` is a division algebra. -/
theorem isUnit_of_ne_zero_two_five_padicTwo {x : ℍ[ℚ_[2],2,5]} (hx : x ≠ 0) : IsUnit x :=
  (hilbertSymbol_eq_neg_one_iff_forall_isUnit _ _).mp hilbertSymbol_two_five_padicTwo x hx

/-- `5` is not a norm from `ℚ_2(√2)`. -/
theorem not_exists_norm_eq_two_five_padicTwo :
    ¬∃ z : QuadraticAlgebra ℚ_[2] 2 0, z.norm = 5 := fun h ↦
  not_nonempty_algEquiv_matrix_two_five_padicTwo
    ((nonempty_algEquiv_matrix_tfae_two_five_padicTwo.out 1 2).mpr h)

/-- `5 = x² - 2 y²` has no solution in `ℚ_2`. -/
theorem not_exists_eq_sq_sub_mul_sq_two_five_padicTwo :
    ¬∃ x y : ℚ_[2], (5 : ℚ_[2]) = x ^ 2 - 2 * y ^ 2 := fun h ↦
  not_nonempty_algEquiv_matrix_two_five_padicTwo
    ((nonempty_algEquiv_matrix_tfae_two_five_padicTwo.out 1 3).mpr h)

/-- `⟨1, -2, -5⟩` is anisotropic over `ℚ_2`. -/
theorem anisotropic_weightedSumSquares_two_five_padicTwo :
    (weightedSumSquares ℚ_[2] ![1, -2, -5]).Anisotropic := not_not.mp fun h ↦
  not_nonempty_algEquiv_matrix_two_five_padicTwo
    ((nonempty_algEquiv_matrix_tfae_two_five_padicTwo.out 1 4).mpr h)

/-- The norm form `⟨⟨2, 5⟩⟩ = ⟨1, -2, -5, 10⟩` of `ℍ[ℚ_2,2,5]` is anisotropic. -/
theorem anisotropic_normForm_two_five_padicTwo :
    (_root_.QuaternionAlgebra.normForm (2 : ℚ_[2]) 0 5).Anisotropic := not_not.mp fun h ↦
  not_nonempty_algEquiv_matrix_two_five_padicTwo
    ((nonempty_algEquiv_matrix_tfae_two_five_padicTwo.out 1 5).mpr h)

end TwoFive

/-! ### The five-way splitting criterion over `ℚ_2` at `(5, 5)`: every condition holds -/

section FiveFive

/-- The splitting criterion `TauCeti.QuaternionAlgebra.nonempty_algEquiv_matrix_tfae` at
`(a, b) = (5, 5)` over `ℚ_2`, with the parameters written as literals. -/
theorem nonempty_algEquiv_matrix_tfae_five_five_padicTwo :
    [Nonempty (ℍ[ℚ_[2],5,5] ≃ₐ[ℚ_[2]] Matrix (Fin 2) (Fin 2) ℚ_[2]),
      ∃ z : QuadraticAlgebra ℚ_[2] 5 0, z.norm = 5,
      ∃ x y : ℚ_[2], (5 : ℚ_[2]) = x ^ 2 - 5 * y ^ 2,
      ¬(weightedSumSquares ℚ_[2] ![1, -5, -5]).Anisotropic,
      ¬(_root_.QuaternionAlgebra.normForm (5 : ℚ_[2]) 0 5).Anisotropic].TFAE := by
  have h := QuaternionAlgebra.nonempty_algEquiv_matrix_tfae (Units.mk0 (5 : ℚ_[2]) (by norm_num))
    (Units.mk0 5 (by norm_num))
  rwa [Units.val_mk0] at h

/-- The witness `5 = 5² - 5 · 2²` of the norm equation of `ℚ_2(√5)`. -/
theorem exists_eq_sq_sub_mul_sq_five_five_padicTwo :
    ∃ x y : ℚ_[2], (5 : ℚ_[2]) = x ^ 2 - 5 * y ^ 2 :=
  ⟨5, 2, by norm_num⟩

/-- `ℍ[ℚ_2,5,5]` splits. -/
theorem nonempty_algEquiv_matrix_five_five_padicTwo :
    Nonempty (ℍ[ℚ_[2],5,5] ≃ₐ[ℚ_[2]] Matrix (Fin 2) (Fin 2) ℚ_[2]) :=
  (nonempty_algEquiv_matrix_tfae_five_five_padicTwo.out 1 3).mpr
    exists_eq_sq_sub_mul_sq_five_five_padicTwo

/-- `(5, 5)_{ℚ_2} = +1`. -/
theorem hilbertSymbol_five_five_padicTwo :
    hilbertSymbol (Units.mk0 (5 : ℚ_[2]) (by norm_num)) (Units.mk0 5 (by norm_num)) = 1 :=
  (hilbertSymbol_eq_one_iff _ _).mpr exists_eq_sq_sub_mul_sq_five_five_padicTwo

/-- `5` is a norm from `ℚ_2(√5)`. -/
theorem exists_norm_eq_five_five_padicTwo : ∃ z : QuadraticAlgebra ℚ_[2] 5 0, z.norm = 5 :=
  (nonempty_algEquiv_matrix_tfae_five_five_padicTwo.out 2 3).mpr
    exists_eq_sq_sub_mul_sq_five_five_padicTwo

/-- `⟨1, -5, -5⟩` is isotropic over `ℚ_2`. -/
theorem not_anisotropic_weightedSumSquares_five_five_padicTwo :
    ¬(weightedSumSquares ℚ_[2] ![1, -5, -5]).Anisotropic :=
  (nonempty_algEquiv_matrix_tfae_five_five_padicTwo.out 4 3).mpr
    exists_eq_sq_sub_mul_sq_five_five_padicTwo

/-- The norm form `⟨⟨5, 5⟩⟩ = ⟨1, -5, -5, 25⟩` of `ℍ[ℚ_2,5,5]` is isotropic. -/
theorem not_anisotropic_normForm_five_five_padicTwo :
    ¬(_root_.QuaternionAlgebra.normForm (5 : ℚ_[2]) 0 5).Anisotropic :=
  (nonempty_algEquiv_matrix_tfae_five_five_padicTwo.out 5 3).mpr
    exists_eq_sq_sub_mul_sq_five_five_padicTwo

end FiveFive

end TauCeti
