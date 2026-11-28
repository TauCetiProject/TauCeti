/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Analysis.Complex.Basic

/-!
# Sharp functions on rectangular matrices

Let `J ≤ GL(n, R)`, let `χ` be a complex character of `GL(n, R)`, and let `A` be an
`n × m` matrix. A function `F` on `m × n` matrices is sharp with decoder `A` if it is
nonzero, transforms on the right by `χ` under `J`, and `A * x` belongs to `J` whenever
`F x ≠ 0`. These are the finite algebraic conditions behind sharp theta data.

The decoder separates translates of the support: if both `F x` and `F (x * g)` are
nonzero, then `g` belongs to `J`. Over a finite ring this evaluates the twisted matrix
coefficient as the squared norm of `F` times the indicator of `J`. No positivity or
unitarity assumption on `χ` is needed for this identity.

`sharpMatrixFn` extends `χ` on `J` by zero and pulls it back along `x ↦ A * x`.
It is sharp whenever `A` has a right inverse, providing nonzero examples for every
subgroup and character. For the trivial subgroup it is the indicator of `A * x = 1`.

The support criterion and coefficient calculation follow the algebraic argument for
`New.SiegelWeil.IsSharpFn` and `New.SiegelWeil.IsSharpFn.isSharp` in
`src/Lib/SiegelWeil/RallisInner/SharpData.lean` of grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
The proofs here are independent, and concern functions on matrices over a semiring,
without the adelic or Weil representation constructions.
-/

public section

open Matrix
open scoped ComplexConjugate

namespace TauCeti

variable {R m n : Type*} [Semiring R] [Fintype m] [Fintype n] [DecidableEq n]

/-- A nonzero function on rectangular matrices, equivariant under `J` with character `χ`,
whose support is carried into `J` by the fixed left multiplier `A`. -/
def IsSharpMatrixFn (J : Subgroup (GL n R)) (χ : GL n R →* ℂˣ)
    (A : Matrix n m R) (F : Matrix m n R → ℂ) : Prop :=
  F ≠ 0 ∧
    (∀ g ∈ J, ∀ x, F (x * (g : Matrix n n R)) = (χ g : ℂ) * F x) ∧
    ∀ x, F x ≠ 0 → ∃ g ∈ J, A * x = (g : Matrix n n R)

/-- The three defining conditions for a sharp matrix function. -/
theorem isSharpMatrixFn_iff {J : Subgroup (GL n R)} {χ : GL n R →* ℂˣ}
    {A : Matrix n m R} {F : Matrix m n R → ℂ} :
    IsSharpMatrixFn J χ A F ↔ F ≠ 0 ∧
      (∀ g ∈ J, ∀ x, F (x * (g : Matrix n n R)) = (χ g : ℂ) * F x) ∧
      ∀ x, F x ≠ 0 → ∃ g ∈ J, A * x = (g : Matrix n n R) := Iff.rfl

namespace IsSharpMatrixFn

variable {J : Subgroup (GL n R)} {χ : GL n R →* ℂˣ}
  {A : Matrix n m R} {F : Matrix m n R → ℂ}

/-- A sharp matrix function is nonzero. -/
theorem ne_zero (hF : IsSharpMatrixFn J χ A F) : F ≠ 0 := hF.1

/-- Right translation by the subgroup acts through the character. -/
theorem apply_mul (hF : IsSharpMatrixFn J χ A F) (g : GL n R) (hg : g ∈ J)
    (x : Matrix m n R) : F (x * (g : Matrix n n R)) = (χ g : ℂ) * F x :=
  hF.2.1 g hg x

/-- The decoder sends every point in the support to a matrix in the subgroup. -/
theorem exists_decode (hF : IsSharpMatrixFn J χ A F) (x : Matrix m n R) (hx : F x ≠ 0) :
    ∃ g ∈ J, A * x = (g : Matrix n n R) := hF.2.2 x hx

/-- Every matrix in the support has a left inverse. -/
theorem exists_leftInverse (hF : IsSharpMatrixFn J χ A F)
    (x : Matrix m n R) (hx : F x ≠ 0) : ∃ B : Matrix n m R, B * x = 1 := by
  obtain ⟨g, _, hg⟩ := hF.exists_decode x hx
  exact ⟨(↑g⁻¹ : Matrix n n R) * A, by rw [Matrix.mul_assoc, hg]; simp⟩

/-- Two points of the support related by right multiplication determine an element of `J`.
The translating matrix need not be assumed invertible. -/
theorem exists_mem_of_apply_mul_ne_zero (hF : IsSharpMatrixFn J χ A F)
    (x : Matrix m n R) (g : Matrix n n R) (hx : F x ≠ 0) (hxg : F (x * g) ≠ 0) :
    ∃ k ∈ J, g = (k : Matrix n n R) := by
  obtain ⟨u, hu, hux⟩ := hF.exists_decode x hx
  obtain ⟨v, hv, hvx⟩ := hF.exists_decode (x * g) hxg
  refine ⟨u⁻¹ * v, J.mul_mem (J.inv_mem hu) hv, ?_⟩
  rw [← Matrix.mul_assoc, hux] at hvx
  rw [Units.val_mul, ← hvx]
  simp

/-- Outside `J`, a translate of the support cannot meet the support. -/
theorem apply_mul_eq_zero (hF : IsSharpMatrixFn J χ A F) (g : GL n R) (hg : g ∉ J)
    (x : Matrix m n R) (hx : F x ≠ 0) : F (x * (g : Matrix n n R)) = 0 := by
  by_contra hxg
  obtain ⟨k, hk, heq⟩ := hF.exists_mem_of_apply_mul_ne_zero x g hx hxg
  exact hg (Units.val_injective heq ▸ hk)

/-- Multiplication by a nonzero scalar preserves sharpness with the same decoder. -/
theorem smul (hF : IsSharpMatrixFn J χ A F) (c : ℂ) (hc : c ≠ 0) :
    IsSharpMatrixFn J χ A (c • F) := by
  refine ⟨smul_ne_zero hc hF.ne_zero, ?_, ?_⟩
  · intro g hg x
    simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm] using
      congrArg (c * ·) (hF.apply_mul g hg x)
  · intro x hx
    exact hF.exists_decode x (fun h ↦ hx (by simp [h]))

/-- A nonzero scalar multiple is sharp exactly when the original function is sharp. -/
@[simp]
theorem smul_iff (c : ℂ) (hc : c ≠ 0) :
    IsSharpMatrixFn J χ A (c • F) ↔ IsSharpMatrixFn J χ A F := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul c hc⟩
  simpa [smul_smul, hc] using h.smul c⁻¹ (inv_ne_zero hc)

/-- Sharp functions with the same decoder are closed under addition whenever the sum is nonzero. -/
theorem add {G : Matrix m n R → ℂ} (hF : IsSharpMatrixFn J χ A F)
    (hG : IsSharpMatrixFn J χ A G) (hne : F + G ≠ 0) : IsSharpMatrixFn J χ A (F + G) := by
  refine ⟨hne, ?_, ?_⟩
  · intro g hg x
    simp [hF.apply_mul g hg, hG.apply_mul g hg, mul_add]
  · intro x hx
    by_cases hFx : F x = 0
    · exact hG.exists_decode x (fun hGx ↦ hx (by simp [hFx, hGx]))
    · exact hF.exists_decode x hFx

open Classical in
/-- Pointwise evaluation of the twisted diagonal coefficient. -/
theorem inv_char_mul_conj_mul (hF : IsSharpMatrixFn J χ A F) (g : GL n R)
    (x : Matrix m n R) :
    (χ g : ℂ)⁻¹ * (conj (F x) * F (x * (g : Matrix n n R))) =
      if g ∈ J then (‖F x‖ ^ 2 : ℂ) else 0 := by
  classical
  by_cases hg : g ∈ J
  · rw [ite_eq_left hg, hF.apply_mul g hg x]
    calc
      (χ g : ℂ)⁻¹ * (conj (F x) * ((χ g : ℂ) * F x)) = conj (F x) * F x := by
        field_simp
      _ = (‖F x‖ ^ 2 : ℂ) := Complex.conj_mul' _
  · rw [ite_eq_right hg]
    by_cases hx : F x = 0
    · simp [hx]
    · simp [hF.apply_mul_eq_zero g hg x hx]

section Finite

variable [Fintype (Matrix m n R)]

open Classical in
/-- The twisted matrix coefficient of sharp data is its squared norm times the indicator
of the subgroup. The sum uses counting measure; divide by the number of matrices for the
corresponding probability measure. -/
theorem inv_char_mul_sum_conj_mul (hF : IsSharpMatrixFn J χ A F) (g : GL n R) :
    (χ g : ℂ)⁻¹ * (∑ x, conj (F x) * F (x * (g : Matrix n n R))) =
      if g ∈ J then ((∑ x, ‖F x‖ ^ 2 : ℝ) : ℂ) else 0 := by
  classical
  rw [Finset.mul_sum]
  simp_rw [hF.inv_char_mul_conj_mul]
  split_ifs <;> simp

/-- A sharp function has strictly positive squared norm for counting measure. -/
theorem sum_norm_sq_pos (hF : IsSharpMatrixFn J χ A F) :
    0 < ∑ x, ‖F x‖ ^ 2 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hF.ne_zero
  exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
    ⟨x, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hx) 2⟩

end Finite
end IsSharpMatrixFn

/-- For the trivial subgroup, sharpness means nonvanishing and support on `A * x = 1`.
The character imposes no additional condition. -/
@[simp]
theorem isSharpMatrixFn_bot_iff (χ : GL n R →* ℂˣ) (A : Matrix n m R)
    (F : Matrix m n R → ℂ) :
    IsSharpMatrixFn ⊥ χ A F ↔ F ≠ 0 ∧ ∀ x, F x ≠ 0 → A * x = 1 := by
  constructor
  · intro hF
    refine ⟨hF.ne_zero, fun x hx ↦ ?_⟩
    obtain ⟨g, hg, hAx⟩ := hF.exists_decode x hx
    simpa [Subgroup.mem_bot.mp hg] using hAx
  · rintro ⟨hne, hA⟩
    refine ⟨hne, ?_, fun x hx ↦ ⟨1, by simp, hA x hx⟩⟩
    intro g hg x
    simp [Subgroup.mem_bot.mp hg]

open Classical in
/-- Extend the character on `J` by zero to square matrices and pull it back by `x ↦ A * x`.
This is a canonical source of sharp functions when `A` has a right inverse. -/
noncomputable def sharpMatrixFn (J : Subgroup (GL n R)) (χ : GL n R →* ℂˣ)
    (A : Matrix n m R) : Matrix m n R → ℂ :=
  fun x ↦ Function.extend (fun g : GL n R ↦ (g : Matrix n n R))
    (fun g ↦ if g ∈ J then (χ g : ℂ) else 0) 0 (A * x)

open Classical in
/-- The extension-by-zero formula defining the canonical sharp function. -/
theorem sharpMatrixFn_def (J : Subgroup (GL n R)) (χ : GL n R →* ℂˣ)
    (A : Matrix n m R) :
    sharpMatrixFn J χ A = fun x ↦ Function.extend (fun g : GL n R ↦ (g : Matrix n n R))
      (fun g ↦ if g ∈ J then (χ g : ℂ) else 0) 0 (A * x) := (rfl)

open Classical in
/-- Evaluation of the canonical sharp function at a decoded unit. -/
theorem sharpMatrixFn_apply_of_mul_eq (J : Subgroup (GL n R)) (χ : GL n R →* ℂˣ)
    (A : Matrix n m R) (x : Matrix m n R) (g : GL n R) (hx : A * x = (g : Matrix n n R)) :
    sharpMatrixFn J χ A x = if g ∈ J then (χ g : ℂ) else 0 := by
  classical
  simp only [sharpMatrixFn_def, hx, Function.Injective.extend_apply Units.val_injective]

/-- The canonical sharp function vanishes unless its decoded matrix belongs to `J`. -/
theorem sharpMatrixFn_eq_zero (J : Subgroup (GL n R)) (χ : GL n R →* ℂˣ)
    (A : Matrix n m R) (x : Matrix m n R)
    (hx : ¬∃ g ∈ J, A * x = (g : Matrix n n R)) : sharpMatrixFn J χ A x = 0 := by
  classical
  by_cases hunit : ∃ g : GL n R, (g : Matrix n n R) = A * x
  · obtain ⟨g, hg⟩ := hunit
    rw [sharpMatrixFn_apply_of_mul_eq J χ A x g hg.symm, ite_eq_right]
    exact fun h ↦ hx ⟨g, h, hg.symm⟩
  · exact Function.extend_apply' _ _ _ hunit

/-- The exact nonvanishing locus of the canonical sharp function. -/
@[simp]
theorem sharpMatrixFn_ne_zero_iff (J : Subgroup (GL n R)) (χ : GL n R →* ℂˣ)
    (A : Matrix n m R) (x : Matrix m n R) :
    sharpMatrixFn J χ A x ≠ 0 ↔ ∃ g ∈ J, A * x = (g : Matrix n n R) := by
  classical
  refine ⟨fun h ↦ by_contra fun h' ↦ h (sharpMatrixFn_eq_zero J χ A x h'), ?_⟩
  rintro ⟨g, hg, hx⟩
  simp [sharpMatrixFn_apply_of_mul_eq J χ A x g hx, hg]

/-- A right inverse of the decoder has canonical sharp value one. -/
@[simp]
theorem sharpMatrixFn_apply_of_mul_eq_one (J : Subgroup (GL n R)) (χ : GL n R →* ℂˣ)
    (A : Matrix n m R) (B : Matrix m n R) (hAB : A * B = 1) :
    sharpMatrixFn J χ A B = 1 := by
  simpa using sharpMatrixFn_apply_of_mul_eq J χ A B 1 hAB

open Classical in
/-- At the trivial subgroup, the canonical function is the indicator of the decoder fiber of `1`. -/
@[simp]
theorem sharpMatrixFn_bot_apply (χ : GL n R →* ℂˣ) (A : Matrix n m R)
    (x : Matrix m n R) : sharpMatrixFn ⊥ χ A x = if A * x = 1 then 1 else 0 := by
  classical
  by_cases hx : A * x = 1
  · simp [hx]
  · rw [ite_eq_right hx]
    apply sharpMatrixFn_eq_zero
    rintro ⟨g, hg, hAx⟩
    exact hx (by simpa [Subgroup.mem_bot.mp hg] using hAx)

/-- Equivariance of the canonical sharp function under the subgroup. -/
theorem sharpMatrixFn_apply_mul (J : Subgroup (GL n R)) (χ : GL n R →* ℂˣ)
    (A : Matrix n m R) (g : GL n R) (hg : g ∈ J) (x : Matrix m n R) :
    sharpMatrixFn J χ A (x * (g : Matrix n n R)) = (χ g : ℂ) * sharpMatrixFn J χ A x := by
  classical
  by_cases hx : ∃ k ∈ J, A * x = (k : Matrix n n R)
  · obtain ⟨k, hk, hx⟩ := hx
    have hxg : A * (x * (g : Matrix n n R)) = ↑(k * g) := by
      rw [← Matrix.mul_assoc, hx, Units.val_mul]
    simp [sharpMatrixFn_apply_of_mul_eq J χ A x k hx,
      sharpMatrixFn_apply_of_mul_eq J χ A (x * (g : Matrix n n R)) (k * g) hxg,
      hk, J.mul_mem hk hg, mul_comm]
  · have hxg : ¬∃ k ∈ J, A * (x * (g : Matrix n n R)) = (k : Matrix n n R) := by
      rintro ⟨k, hk, hxg⟩
      apply hx
      refine ⟨k * g⁻¹, J.mul_mem hk (J.inv_mem hg), ?_⟩
      rw [Units.val_mul, ← hxg, ← Matrix.mul_assoc, Units.mul_inv_cancel_right]
    simp [sharpMatrixFn_eq_zero J χ A x hx,
      sharpMatrixFn_eq_zero J χ A (x * (g : Matrix n n R)) hxg]

/-- The canonical function is nonzero exactly when its decoder has a right inverse. -/
theorem sharpMatrixFn_ne_zero_iff_exists_rightInverse (J : Subgroup (GL n R))
    (χ : GL n R →* ℂˣ) (A : Matrix n m R) :
    sharpMatrixFn J χ A ≠ 0 ↔ ∃ B : Matrix m n R, A * B = 1 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Function.ne_iff.mp h
    obtain ⟨g, _, hg⟩ := (sharpMatrixFn_ne_zero_iff J χ A x).1 hx
    exact ⟨x * (↑g⁻¹ : Matrix n n R), by rw [← Matrix.mul_assoc, hg]; simp⟩
  · rintro ⟨B, hAB⟩ h
    have := congrFun h B
    simp [sharpMatrixFn_apply_of_mul_eq_one J χ A B hAB] at this

/-- A split decoder gives nonzero sharp matrix data for every subgroup and character. -/
theorem isSharpMatrixFn_sharpMatrixFn (J : Subgroup (GL n R)) (χ : GL n R →* ℂˣ)
    (A : Matrix n m R) (B : Matrix m n R) (hAB : A * B = 1) :
    IsSharpMatrixFn J χ A (sharpMatrixFn J χ A) := by
  refine ⟨(sharpMatrixFn_ne_zero_iff_exists_rightInverse J χ A).2 ⟨B, hAB⟩,
    fun g hg x ↦ sharpMatrixFn_apply_mul J χ A g hg x, ?_⟩
  intro x hx
  exact (sharpMatrixFn_ne_zero_iff J χ A x).1 hx

end TauCeti
