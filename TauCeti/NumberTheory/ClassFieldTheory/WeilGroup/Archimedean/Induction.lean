/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Basic

/-!
# Two-dimensional inductions of characters of `W_ℂ` to `W_ℝ`

For a character `χ : W_ℂ = ℂˣ →* ℂˣ`, the representation of the Weil group `W_ℝ = ℂˣ ∪ jℂˣ`
induced from `χ` is two-dimensional. In the basis `(e, j e)` of the induced module it is

* `z ↦ diag(χ z, χ (conj z))` on `ℂˣ`, and
* `j ↦ [[0, χ (-1)], [1, 0]]`,

as follows from `j² = -1` and `j z j⁻¹ = conj z`. This file constructs it as a homomorphism
`WeilGroupReal.induceCharacter χ : W_ℝ →* GL₂(ℂ)` through the universal property
`WeilGroupReal.lift`, proves that it is continuous when `χ` is, and proves that the induction of
the conjugate character `χ ∘ conj` is the conjugate of the induction of `χ` by the matrix of `j`
(`WeilGroupReal.induceCharacter_comp_star`): interchanging the two exponents of a character
does not change its induction up to isomorphism.

## Main definitions

* `TauCeti.ClassFieldTheory.WeilGroupReal.induceCharacter`: the induced representation
  `W_ℝ →* GL₂(ℂ)` of a character of `W_ℂ`.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.induceCharacter_includeComplex`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.induceCharacter_j`: the values on `ℂˣ` and on `j`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.continuous_induceCharacter`: the induction of a
  continuous character is continuous.
* `TauCeti.ClassFieldTheory.WeilGroupReal.induceCharacter_comp_star`: the induction of `χ ∘ conj`
  is the conjugate of the induction of `χ` by the image of `j`.

## References

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in *Motives*,
  Proc. Sympos. Pure Math. 55, Part 2 (1994), §3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

namespace WeilGroupReal

open Matrix

variable (χ : WeilGroupComplex →* ℂˣ)

/-- Conjugation fixes `-1 ∈ ℂˣ`. -/
private theorem star_neg_one_weilGroupComplex : star (-1 : WeilGroupComplex) = -1 := by
  ext; simp

/-- The diagonal part `z ↦ diag(χ z, χ (conj z))` of the induction of `χ`. -/
def induceCharacterDiag : WeilGroupComplex →* GL (Fin 2) ℂ :=
  diagGL.comp (MonoidHom.pi ![χ, χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom])

/-- The matrix of `induceCharacterDiag χ z` is `diag(χ z, χ (conj z))`. -/
@[simp]
theorem coe_induceCharacterDiag (z : WeilGroupComplex) :
    (induceCharacterDiag χ z : Matrix (Fin 2) (Fin 2) ℂ) =
      diagonal ![(χ z : ℂ), (χ (star z) : ℂ)] := by
  rw [induceCharacterDiag, MonoidHom.comp_apply, diagGL_coe]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The diagonal part of the induction of a continuous character is continuous. -/
theorem continuous_induceCharacterDiag (hχ : Continuous χ) :
    Continuous (induceCharacterDiag χ) := by
  have hval : Continuous fun z ↦ (induceCharacterDiag χ z : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [coe_induceCharacterDiag]
    refine Continuous.matrix_diagonal (continuous_pi fun i ↦ ?_)
    fin_cases i
    · exact Units.continuous_val.comp hχ
    · exact Units.continuous_val.comp (hχ.comp continuous_star)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simpa only [Function.comp_def, map_inv] using hval.comp continuous_inv

/-- The image `[[0, χ (-1)], [1, 0]]` of `j` in the induction of `χ`. -/
def induceCharacterJ : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![0, (χ (-1) : ℂ); 1, 0] (by simp)

/-- The matrix of `induceCharacterJ χ` is `[[0, χ (-1)], [1, 0]]`. -/
@[simp]
theorem coe_induceCharacterJ :
    (induceCharacterJ χ : Matrix (Fin 2) (Fin 2) ℂ) = !![0, (χ (-1) : ℂ); 1, 0] := by
  simp [induceCharacterJ, GeneralLinearGroup.mkOfDetNeZero]

/-- The relation `j² = -1` for the induction of `χ`. -/
theorem induceCharacterJ_sq : induceCharacterJ χ ^ 2 = induceCharacterDiag χ (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, star_neg_one_weilGroupComplex]

/-- The relation `j z = conj z j` for the induction of `χ`. -/
theorem induceCharacterJ_mul_induceCharacterDiag (z : WeilGroupComplex) :
    induceCharacterJ χ * induceCharacterDiag χ z =
      induceCharacterDiag χ (star z) * induceCharacterJ χ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_comm]

/-- **The induction of a character of `W_ℂ` to `W_ℝ`.** It sends `z ∈ ℂˣ` to
`diag(χ z, χ (conj z))` and `j` to `[[0, χ (-1)], [1, 0]]`. -/
def induceCharacter : WeilGroupReal →* GL (Fin 2) ℂ :=
  lift (induceCharacterDiag χ) (induceCharacterJ χ) (induceCharacterJ_sq χ)
    (induceCharacterJ_mul_induceCharacterDiag χ)

/-- The induction of `χ` sends `z ∈ ℂˣ` to `induceCharacterDiag χ z = diag(χ z, χ (conj z))`. -/
@[simp]
theorem induceCharacter_includeComplex (z : WeilGroupComplex) :
    induceCharacter χ (includeComplex z) = induceCharacterDiag χ z :=
  lift_includeComplex z

/-- The induction of `χ` sends `j` to `induceCharacterJ χ = [[0, χ (-1)], [1, 0]]`. -/
@[simp]
theorem induceCharacter_j : induceCharacter χ j = induceCharacterJ χ :=
  lift_j

/-- The induction of `χ` restricts to `induceCharacterDiag χ` on `ℂˣ`. -/
@[simp]
theorem induceCharacter_comp_includeComplex :
    (induceCharacter χ).comp includeComplex = induceCharacterDiag χ :=
  lift_comp_includeComplex

/-- **The induction of a continuous character is continuous.** -/
theorem continuous_induceCharacter (hχ : Continuous χ) : Continuous (induceCharacter χ) := by
  rw [continuous_iff_continuous_comp_includeComplex, induceCharacter_comp_includeComplex]
  exact continuous_induceCharacterDiag χ hχ

/-- **Interchanging the exponents does not change the induction.** The induction of the conjugate
character `χ ∘ conj` is the conjugate of the induction of `χ` by the image of `j`. -/
theorem induceCharacter_comp_star (w : WeilGroupReal) :
    induceCharacter (χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom) w =
      induceCharacter χ j * induceCharacter χ w * (induceCharacter χ j)⁻¹ := by
  have h : induceCharacter (χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom) =
      (MulAut.conj (induceCharacter χ j)).toMonoidHom.comp (induceCharacter χ) := by
    refine hom_ext (MonoidHom.ext fun z ↦ eq_mul_inv_of_mul_eq ?_) (eq_mul_inv_of_mul_eq ?_)
    · ext i k
      simp only [Units.val_mul, MonoidHom.comp_apply, induceCharacter_includeComplex,
        coe_induceCharacterDiag, induceCharacter_j, coe_induceCharacterJ]
      fin_cases i <;> fin_cases k <;> simp [mul_comm]
    · ext i k
      simp only [Units.val_mul, induceCharacter_j, coe_induceCharacterJ]
      fin_cases i <;> fin_cases k <;> simp [star_neg_one_weilGroupComplex]
  rw [h, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end WeilGroupReal

end TauCeti.ClassFieldTheory
