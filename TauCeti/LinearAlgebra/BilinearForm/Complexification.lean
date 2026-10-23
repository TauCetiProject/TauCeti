/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.Complex.Conjugation

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The sesquilinear complexification of a real bilinear form

A real bilinear form `B` on `V` has two complex extensions to the complexification
`ℂ ⊗[ℝ] V`. Mathlib's `LinearMap.BilinForm.baseChange` is the complex-*bilinear* one, `B_ℂ`.
Composing it in the first argument with the conjugation `TauCeti.tmulConj` of the
complexification gives the *sesquilinear* one,

`h (x, y) = B_ℂ (conj x, y)`, so `h (z ⊗ v, w ⊗ u) = conj z * w * B (v, u)`,

which is conjugate-linear in the first argument and linear in the second, Mathlib's convention
for sesquilinear forms. When `B` is symmetric, `h` is Hermitian; when `B` is moreover positive
definite, so is `h`. This is the positive Hermitian form that a Euclidean metric `g` induces on
`ℂ ⊗[ℝ] V`; it is a different form from the complex-bilinear `g_ℂ`, to which it is related by
`h (conj x, y) = g_ℂ (x, y)`. Real-linear maps preserving `B` complexify to maps preserving `h`.

## Main definitions

* `LinearMap.BilinForm.sesqComplexification`: the form `h (x, y) = B_ℂ (conj x, y)`.

## Main results

* `LinearMap.BilinForm.sesqComplexification_tmul_tmul`: its values on pure tensors.
* `LinearMap.BilinForm.sesqComplexification_tmulConj_left`: `h (conj x, y) = B_ℂ (x, y)`.
* `LinearMap.BilinForm.sesqComplexification_tmulConj_tmulConj`: `h (conj x, conj y)` is the
  conjugate of `h (x, y)`.
* `LinearMap.BilinForm.sesqComplexification_baseChange_baseChange`: complexified maps preserving
  `B` preserve `h`.
* `LinearMap.BilinForm.IsSymm.sesqComplexification`: `h` is Hermitian when `B` is symmetric.
* `LinearMap.BilinForm.sesqComplexification_one_tmul_add_I_tmul_self`: for symmetric `B`,
  `h (a + i b, a + i b) = B (a, a) + B (b, b)`.
* `LinearMap.BilinForm.IsPosSemidef.sesqComplexification` and
  `LinearMap.BilinForm.sesqComplexification_self_pos`: `h` is positive semidefinite, respectively
  positive definite, when `B` is.
-/

public section

open scoped TensorProduct ComplexOrder
open TauCeti
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']

/-! ### The bilinear complexification and conjugation -/

/-- Conjugating both arguments of the complex-bilinear extension of a real form conjugates its
value. -/
@[simp]
theorem baseChange_tmulConj_tmulConj (B : BilinForm ℝ V) (x y : ℂ ⊗[ℝ] V) :
    B.baseChange ℂ (tmulConj V x) (tmulConj V y) = starRingEnd ℂ (B.baseChange ℂ x y) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul z v =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul w u => simp [baseChange_tmul, Complex.real_smul]

/-! ### The sesquilinear complexification -/

variable (B : BilinForm ℝ V)

/-- **The sesquilinear complexification** of a real bilinear form `B`: the form
`h (x, y) = B_ℂ (conj x, y)` on `ℂ ⊗[ℝ] V`, conjugate-linear in the first argument and linear in
the second, with `h (z ⊗ v, w ⊗ u) = conj z * w * B (v, u)`
(`LinearMap.BilinForm.sesqComplexification_tmul_tmul`). For a Euclidean metric it is the
induced positive Hermitian form on the complexification. -/
noncomputable def sesqComplexification : ℂ ⊗[ℝ] V →ₗ⋆[ℂ] ℂ ⊗[ℝ] V →ₗ[ℂ] ℂ :=
  LinearMap.comp (B.baseChange ℂ) (tmulConj V)

theorem sesqComplexification_apply (x y : ℂ ⊗[ℝ] V) :
    B.sesqComplexification x y = B.baseChange ℂ (tmulConj V x) y :=
  (rfl)

/-- The sesquilinear complexification on pure tensors. -/
@[simp]
theorem sesqComplexification_tmul_tmul (z w : ℂ) (v u : V) :
    B.sesqComplexification (z ⊗ₜ v) (w ⊗ₜ u) = starRingEnd ℂ z * w * B v u := by
  rw [sesqComplexification_apply, tmulConj_tmul, baseChange_tmul, Complex.real_smul, mul_comm]

/-- The sesquilinear complexification evaluated at a conjugate is the complex-bilinear
extension: `h (conj x, y) = B_ℂ (x, y)`. -/
@[simp]
theorem sesqComplexification_tmulConj_left (x y : ℂ ⊗[ℝ] V) :
    B.sesqComplexification (tmulConj V x) y = B.baseChange ℂ x y := by
  rw [sesqComplexification_apply, tmulConj_tmulConj]

/-- Conjugating both arguments of the sesquilinear complexification conjugates its value. -/
theorem sesqComplexification_tmulConj_tmulConj (x y : ℂ ⊗[ℝ] V) :
    B.sesqComplexification (tmulConj V x) (tmulConj V y) =
      starRingEnd ℂ (B.sesqComplexification x y) := by
  rw [sesqComplexification_tmulConj_left, sesqComplexification_apply,
    ← baseChange_tmulConj_tmulConj, tmulConj_tmulConj]

/-- **Complexified maps preserving a real bilinear form preserve its sesquilinear
complexification.** In particular the complexification of a real isometry is unitary for the
induced Hermitian form. -/
theorem sesqComplexification_baseChange_baseChange {B' : BilinForm ℝ V'} {f : V →ₗ[ℝ] V'}
    (hf : ∀ v w, B' (f v) (f w) = B v w) (x y : ℂ ⊗[ℝ] V) :
    B'.sesqComplexification (f.baseChange ℂ x) (f.baseChange ℂ y) =
      B.sesqComplexification x y := by
  rw [sesqComplexification_apply, sesqComplexification_apply, tmulConj_baseChange,
    baseChange_baseChange_baseChange hf]

/-! ### Hermitian symmetry and positivity -/

variable {B}

/-- **The sesquilinear complexification of a symmetric form is Hermitian.** -/
theorem IsSymm.sesqComplexification (hB : B.IsSymm) : B.sesqComplexification.IsSymm := by
  refine LinearMap.isSymm_def.mpr fun x y => ?_
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul z v =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul w u =>
      simp only [sesqComplexification_tmul_tmul, map_mul, Complex.conj_conj, Complex.conj_ofReal,
        hB.eq v u]
      ring

/-- **The diagonal of the sesquilinear complexification of a symmetric form**: writing a vector
of the complexification as `a + i b` with `a`, `b` real, `h (a + i b, a + i b)` is the real
number `B (a, a) + B (b, b)`. -/
theorem sesqComplexification_one_tmul_add_I_tmul_self (hB : B.IsSymm) (a b : V) :
    B.sesqComplexification ((1 : ℂ) ⊗ₜ a + Complex.I ⊗ₜ b) ((1 : ℂ) ⊗ₜ a + Complex.I ⊗ₜ b) =
      ((B a a + B b b : ℝ) : ℂ) := by
  have hba : B b a = B a b := hB.eq b a
  simp only [map_add, LinearMap.add_apply, sesqComplexification_tmul_tmul, map_one,
    Complex.conj_I, hba, Complex.ofReal_add]
  linear_combination (-(B b b : ℂ)) * Complex.I_mul_I

/-- The diagonal of the sesquilinear complexification of a symmetric form is the sum of the
values of `B` on the real and imaginary parts. -/
theorem exists_sesqComplexification_self_eq (hB : B.IsSymm) (x : ℂ ⊗[ℝ] V) :
    ∃ a b : V, x = (1 : ℂ) ⊗ₜ a + Complex.I ⊗ₜ b ∧
      B.sesqComplexification x x = ((B a a + B b b : ℝ) : ℂ) := by
  obtain ⟨a, b, rfl⟩ := exists_one_tmul_add_I_tmul x
  exact ⟨a, b, rfl, sesqComplexification_one_tmul_add_I_tmul_self hB a b⟩

/-- **The sesquilinear complexification of a positive semidefinite form is positive
semidefinite.** -/
theorem IsPosSemidef.sesqComplexification (hB : B.IsPosSemidef) :
    B.sesqComplexification.IsPosSemidef where
  isSymm := hB.isSymm.sesqComplexification
  isNonneg := ⟨fun x => by
    obtain ⟨a, b, -, hx⟩ := exists_sesqComplexification_self_eq hB.isSymm x
    rw [hx]
    exact Complex.zero_le_real.mpr (add_nonneg (hB.isNonneg.nonneg a) (hB.isNonneg.nonneg b))⟩

/-- **The sesquilinear complexification of a positive definite symmetric form is positive
definite.** -/
theorem sesqComplexification_self_pos (hB : B.IsSymm) (hpos : B.toQuadraticMap.PosDef)
    {x : ℂ ⊗[ℝ] V} (hx : x ≠ 0) : 0 < B.sesqComplexification x x := by
  obtain ⟨a, b, rfl, hxx⟩ := exists_sesqComplexification_self_eq hB x
  rw [hxx, Complex.zero_lt_real]
  have ha := hpos.nonneg a
  have hb := hpos.nonneg b
  rw [BilinMap.toQuadraticMap_apply] at ha hb
  by_cases ha0 : a = 0
  · have hb0 : b ≠ 0 := by
      rintro rfl
      exact hx (by simp [ha0])
    have := hpos b hb0
    rw [BilinMap.toQuadraticMap_apply] at this
    linarith
  · have := hpos a ha0
    rw [BilinMap.toQuadraticMap_apply] at this
    linarith

end LinearMap.BilinForm
