/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Probability.FreeProbability.Distribution.Star
public import TauCeti.Probability.FreeProbability.Semicircular.System

/-!
# Circular elements

A standard circular element has just two nonzero joint cumulants in the element and its
adjoint: the second cumulants in the two alternating orders are both one. We express this
using the existing semicircular-system predicate for the doubled family `(c, c*)`; here
semicircular systems are algebraic and their coordinates need not be selfadjoint.

The linear change of coordinates `(x, y) ↦ ((x + iy)/√2, (x - iy)/√2)` turns two free
variance-one selfadjoint semicircular elements into a circular element. Conversely the
normalized real and imaginary parts of a circular element form a free variance-one
semicircular pair. Thus the cumulant definition determines the entire star distribution,
not only its second moments. Positivity and traciality of the ambient functional are not
assumed.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 15.
-/

public section

open Finset Matrix

namespace TauCeti

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [Ring B] [Algebra ℂ B] [StarRing B]
  {φ : A →ₗ[ℂ] ℂ} {ψ : B →ₗ[ℂ] ℂ} {c : A} {d : B}

/-- A standard circular element: the doubled family `(c, c*)` has only second joint
cumulants, with covariance zero on the diagonal and one off the diagonal. -/
abbrev IsCircular (φ : A →ₗ[ℂ] ℂ) (c : A) : Prop :=
  IsSemicircularSystem φ ![c, star c] !![0, 1; 1, 0]

namespace IsCircular

/-- The second cumulant of a circular element and its adjoint is one exactly when the
arguments have different adjoint labels. -/
theorem freeCumulant_two (h : IsCircular φ c) (w : Fin 2 → Fin 2) :
    freeCumulant φ (![c, star c] ∘ w) univ = if w 0 = w 1 then 0 else 1 := by
  rw [IsSemicircularSystem.freeCumulant_two h]
  generalize w 0 = i, w 1 = j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem apply_eq_zero (h : IsCircular φ c) : φ c = 0 :=
  IsSemicircularSystem.apply_eq_zero h 0

@[simp]
theorem apply_star_eq_zero (h : IsCircular φ c) : φ (star c) = 0 :=
  IsSemicircularSystem.apply_eq_zero h 1

@[simp]
theorem apply_mul_star (h : IsCircular φ c) : φ (c * star c) = 1 :=
  IsSemicircularSystem.apply_mul h 0 1

@[simp]
theorem apply_star_mul (h : IsCircular φ c) : φ (star c * c) = 1 :=
  IsSemicircularSystem.apply_mul h 1 0

@[simp]
theorem apply_sq (h : IsCircular φ c) : φ (c ^ 2) = 0 := by
  simpa [pow_two] using IsSemicircularSystem.apply_mul h 0 0

/-- Taking the adjoint preserves circularity. -/
theorem star (h : IsCircular φ c) : IsCircular φ (star c) := by
  have h' := h.comp (fun i : Fin 2 => 1 - i)
  convert h' using 1
  · ext i
    fin_cases i <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The full star distribution of a circular element is independent of its realization. -/
theorem starDistribution_eq [StarModule ℂ A] [StarModule ℂ B]
    (h : IsCircular φ c) (h' : IsCircular ψ d) :
    starDistribution φ (fun _ : Unit => c) = starDistribution ψ (fun _ : Unit => d) := by
  apply starDistribution_eq_iff_jointDistribution_withStar_eq.2
  convert jointDistribution_comp_eq (IsSemicircularSystem.jointDistribution_eq h h')
    (fun p : Unit × Bool => if p.2 then (1 : Fin 2) else 0) using 1 <;>
    congr 1 <;> funext ⟨i, b⟩ <;> cases b <;> simp

end IsCircular

private theorem circular_normalization :
    ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 * 2 = 1 := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  field_simp
  linear_combination -hs

/-- Two free variance-one selfadjoint semicircular coordinates give a circular element
`(x + iy)/√2`. The system hypothesis includes normalization and freeness. -/
theorem IsSemicircularSystem.isCircular [StarModule ℂ A] {s : Fin 2 → A}
    (h : IsSemicircularSystem φ s (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (hs : ∀ i, IsSelfAdjoint (s i)) :
    IsCircular φ ((Real.sqrt 2 : ℂ)⁻¹ • (s 0 + Complex.I • s 1)) := by
  let q : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hq : q ^ 2 * 2 = 1 := circular_normalization
  have hqstar : Star.star q = q := by simp [q]
  have h' := h.sum_smul !![q, q; Complex.I * q, -Complex.I * q]
  have hv : (fun k => ∑ i : Fin 2,
      (!![q, q; Complex.I * q, -Complex.I * q] : Matrix (Fin 2) (Fin 2) ℂ) i k • s i) =
      ![q • (s 0 + Complex.I • s 1), star (q • (s 0 + Complex.I • s 1))] := by
    ext k
    simp only [Fin.sum_univ_two]
    fin_cases k <;> dsimp <;>
      simp only [smul_add, star_smul, star_add,
        (hs 0).star_eq, (hs 1).star_eq, hqstar, Complex.star_def, Complex.conj_I]
    all_goals module
  have hC : (!![q, q; Complex.I * q, -Complex.I * q] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *
      1 * !![q, q; Complex.I * q, -Complex.I * q] = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
      ring_nf <;> simp only [Complex.I_sq] <;> ring_nf <;> exact hq
  rw [hv, hC] at h'
  exact h'

namespace IsCircular

/-- The normalized real and imaginary parts of a circular element are a variance-one
semicircular system. -/
theorem real_imag (h : IsCircular φ c) :
    IsSemicircularSystem φ
      ![(Real.sqrt 2 : ℂ)⁻¹ • (c + Star.star c),
        (-Complex.I * (Real.sqrt 2 : ℂ)⁻¹) • (c - Star.star c)]
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  let q : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hq : q ^ 2 * 2 = 1 := circular_normalization
  have h' := h.sum_smul !![q, -Complex.I * q; q, Complex.I * q]
  have hv : (fun k => ∑ i : Fin 2,
      (!![q, -Complex.I * q; q, Complex.I * q] : Matrix (Fin 2) (Fin 2) ℂ) i k •
        (![c, Star.star c] : Fin 2 → A) i) =
      ![q • (c + Star.star c), (-Complex.I * q) • (c - Star.star c)] := by
    ext k
    fin_cases k <;>
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.of_apply] <;>
      simp [smul_add, sub_eq_add_neg]
  have hC : (!![q, -Complex.I * q; q, Complex.I * q] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *
      !![0, 1; 1, 0] * !![q, -Complex.I * q; q, Complex.I * q] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
      ring_nf <;> (try simp only [Complex.I_sq]) <;> (try ring_nf) <;> exact hq
  rw [hv, hC] at h'
  exact h'

/-- The normalized real and imaginary parts of a circular element are freely independent. -/
theorem real_imag_free (h : IsCircular φ c) :
    IsFreelyIndependentElements φ
      ![(Real.sqrt 2 : ℂ)⁻¹ • (c + Star.star c),
        (-Complex.I * (Real.sqrt 2 : ℂ)⁻¹) • (c - Star.star c)] :=
  h.real_imag.isFreelyIndependentElements_iff.2 fun _ _ hij => Matrix.one_apply_ne hij

end IsCircular

/-- Circularity is equivalent to the variance-one semicircular-system condition on the
normalized real and imaginary parts. Their freeness follows from diagonal covariance. -/
theorem isCircular_iff_real_imag [StarModule ℂ A] :
    IsCircular φ c ↔ IsSemicircularSystem φ
      ![(Real.sqrt 2 : ℂ)⁻¹ • (c + star c),
        (-Complex.I * (Real.sqrt 2 : ℂ)⁻¹) • (c - star c)]
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨IsCircular.real_imag, fun h => ?_⟩
  let q : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hq : q ^ 2 * 2 = 1 := circular_normalization
  have hs : ∀ i : Fin 2,
      IsSelfAdjoint (![q • (c + star c), (-Complex.I * q) • (c - star c)] i) := by
    intro i
    fin_cases i <;> simp [IsSelfAdjoint, star_smul, q, smul_sub, smul_add, add_comm]
  have he : q • (q • (c + star c) + Complex.I • ((-Complex.I * q) • (c - star c))) = c := by
    match_scalars
    · linear_combination hq - q ^ 2 * Complex.I_sq
    · linear_combination q ^ 2 * Complex.I_sq
  have hc := h.isCircular hs
  simp only [cons_val_zero, cons_val_one, cons_val_fin_one] at hc
  rw [he] at hc
  exact hc

end TauCeti
