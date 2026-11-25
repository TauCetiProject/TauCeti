/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean

/-!
# Two-dimensional inductions of characters of `W_ℂ` to `W_ℝ`

For a character `χ : W_ℂ = ℂˣ →* ℂˣ`, the representation of the Weil group `W_ℝ = ℂˣ ∪ jℂˣ`
induced from `χ` is two-dimensional. In the basis `(e, j⁻¹ e)` of the induced module it is

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

/-- The diagonal part `z ↦ diag(χ z, χ (conj z))` of the induction of `χ`. -/
def induceCharacterDiag : WeilGroupComplex →* GL (Fin 2) ℂ :=
  diagGL.comp (MonoidHom.pi ![χ, χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom])

/-- The matrix of `induceCharacterDiag χ z` is `diag(χ z, χ (conj z))`. -/
theorem coe_induceCharacterDiag (z : WeilGroupComplex) :
    (induceCharacterDiag χ z : Matrix (Fin 2) (Fin 2) ℂ) =
      diagonal ![(χ z : ℂ), (χ (star z) : ℂ)] := by
  rw [induceCharacterDiag, MonoidHom.comp_apply, diagGL_coe]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The image `[[0, χ (-1)], [1, 0]]` of `j` in the induction of `χ`. -/
def induceCharacterJ : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![0, (χ (-1) : ℂ); 1, 0] (by simp)

/-- The matrix of `induceCharacterJ χ` is `[[0, χ (-1)], [1, 0]]`. -/
theorem coe_induceCharacterJ :
    (induceCharacterJ χ : Matrix (Fin 2) (Fin 2) ℂ) = !![0, (χ (-1) : ℂ); 1, 0] := by
  simp [induceCharacterJ, GeneralLinearGroup.mkOfDetNeZero]

/-- The relation `j² = -1` for the induction of `χ`. -/
theorem induceCharacterJ_sq : induceCharacterJ χ ^ 2 = induceCharacterDiag χ (-1) := by
  ext i j
  have h : (star (-1 : WeilGroupComplex)) = -1 := by ext; simp
  fin_cases i <;> fin_cases j <;>
    simp [sq, coe_induceCharacterJ, coe_induceCharacterDiag, h]

/-- The relation `j z = conj z j` for the induction of `χ`. -/
theorem induceCharacterJ_mul (z : WeilGroupComplex) :
    induceCharacterJ χ * induceCharacterDiag χ z =
      induceCharacterDiag χ (star z) * induceCharacterJ χ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_induceCharacterJ, coe_induceCharacterDiag, mul_comm]

/-- **The induction of a character of `W_ℂ` to `W_ℝ`.** It sends `z ∈ ℂˣ` to
`diag(χ z, χ (conj z))` and `j` to `[[0, χ (-1)], [1, 0]]`. -/
def induceCharacter : WeilGroupReal →* GL (Fin 2) ℂ :=
  lift (induceCharacterDiag χ) (induceCharacterJ χ) (induceCharacterJ_sq χ)
    (induceCharacterJ_mul χ)

/-- The induction of `χ` sends `z ∈ ℂˣ` to `diag(χ z, χ (conj z))`. -/
theorem induceCharacter_includeComplex (z : WeilGroupComplex) :
    (induceCharacter χ (includeComplex z) : Matrix (Fin 2) (Fin 2) ℂ) =
      diagonal ![(χ z : ℂ), (χ (star z) : ℂ)] := by
  rw [induceCharacter, lift_includeComplex, coe_induceCharacterDiag]

/-- The induction of `χ` sends `j` to `[[0, χ (-1)], [1, 0]]`. -/
theorem induceCharacter_j :
    (induceCharacter χ j : Matrix (Fin 2) (Fin 2) ℂ) = !![0, (χ (-1) : ℂ); 1, 0] := by
  rw [induceCharacter, lift_j, coe_induceCharacterJ]

/-- **The induction of a continuous character is continuous.** -/
theorem continuous_induceCharacter (hχ : Continuous χ) : Continuous (induceCharacter χ) := by
  refine (continuous_iff_continuous_comp_includeComplex _).mpr ?_
  have hstar : Continuous (star : WeilGroupComplex → WeilGroupComplex) :=
    Units.continuous_iff.mpr ⟨Complex.continuous_conj.comp Units.continuous_val,
      Complex.continuous_conj.comp Units.continuous_coe_inv⟩
  have h1 : Continuous fun z ↦ (χ z : ℂ) := Units.continuous_val.comp hχ
  have h2 : Continuous fun z ↦ (χ (star z) : ℂ) := Units.continuous_val.comp (hχ.comp hstar)
  have h3 : Continuous fun z ↦ (χ z : ℂ)⁻¹ :=
    h1.inv₀ fun z ↦ (χ z).ne_zero
  have h4 : Continuous fun z ↦ (χ (star z) : ℂ)⁻¹ :=
    h2.inv₀ fun z ↦ (χ (star z)).ne_zero
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun i k ↦ ?_, continuous_matrix fun i k ↦ ?_⟩
  · simp only [Function.comp_apply, MonoidHom.coe_comp, induceCharacter, lift_includeComplex,
      coe_induceCharacterDiag]
    fin_cases i <;> fin_cases k <;> simp [h1, h2, continuous_const]
  · simp only [Function.comp_apply, MonoidHom.coe_comp, induceCharacter, lift_includeComplex,
      ← map_inv, coe_induceCharacterDiag]
    fin_cases i <;> fin_cases k <;> simp [h3, h4, continuous_const]

/-- **Interchanging the exponents does not change the induction.** The induction of the conjugate
character `χ ∘ conj` is the conjugate of the induction of `χ` by the image of `j`. -/
theorem induceCharacter_comp_star (w : WeilGroupReal) :
    induceCharacter (χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom) w =
      induceCharacter χ j * induceCharacter χ w * (induceCharacter χ j)⁻¹ := by
  have hstar : (star (-1 : WeilGroupComplex)) = -1 := by ext; simp
  have h : induceCharacter (χ.comp (starMulAut : MulAut WeilGroupComplex).toMonoidHom) =
      (MulAut.conj (induceCharacter χ j)).toMonoidHom.comp (induceCharacter χ) := by
    refine hom_ext (MonoidHom.ext fun z ↦ eq_mul_inv_of_mul_eq ?_) (eq_mul_inv_of_mul_eq ?_)
    · ext i k
      simp only [Units.val_mul, MonoidHom.comp_apply, induceCharacter_includeComplex,
        induceCharacter_j]
      fin_cases i <;> fin_cases k <;> simp [mul_comm]
    · ext i k
      simp only [Units.val_mul, induceCharacter_j]
      fin_cases i <;> fin_cases k <;> simp [hstar]
  rw [h]
  rfl

end WeilGroupReal

end TauCeti.ClassFieldTheory
