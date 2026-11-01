/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# Newton's method for Gram matrices over an adically complete ring

Let `R` be `π`-adically complete and let `G` be a symmetric matrix over `R` admitting a matrix
`H = H₀ + H₀ᵀ` with `G * H = π ^ j • 1`. This file proves that a matrix `A` with
`G - A = π ^ (j + 1) • (D + Dᵀ)` is congruent to `G` by a matrix `U ≡ 1` modulo `π`, that is
`Uᵀ * A * U = G` (`Matrix.exists_transpose_mul_mul_eq_of_sub_eq`). This is the matrix form of the
statement that an approximate isometry out of a bilinear form is congruent modulo `π` to an exact
one (`LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`).

## Main results

* `Matrix.exists_transpose_mul_mul_eq_of_sub_eq`: Newton's method for Gram matrices.

## Implementation notes

If `G - Uᵀ A U = π ^ (j + k) • (D + Dᵀ)` with `k ≥ 1`, then replacing `U` by
`U * (1 + π ^ k • (H * D))` cancels the error to first order, and the new error has the same shape
with `k + 1` in place of `k`. The corrections converge `π`-adically. Recording the error as
`D + Dᵀ`, rather than as a symmetric matrix, is what makes the iteration work when `2` is not a
unit.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open scoped Matrix

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **The Newton step.** Let `G` be symmetric with `G * H = π ^ j • 1`, where `H = H₀ + H₀ᵀ`. If a
matrix differs from `G` by `π ^ (j + k) • (D + Dᵀ)`, then its congruence by
`1 + π ^ k • (H * D)` differs from `G` by `π ^ (j + 2 * k) • (P + Pᵀ)` for an explicit `P`. -/
private theorem sub_transpose_one_add_mul_mul_one_add_eq (π : R) (j k : ℕ) {G H₀ D : Matrix n n R}
    (hG : G.IsSymm) (hGH : G * (H₀ + H₀ᵀ) = π ^ j • 1) :
    G - (1 + π ^ k • ((H₀ + H₀ᵀ) * D))ᵀ * (G - π ^ (j + k) • (D + Dᵀ)) *
        (1 + π ^ k • ((H₀ + H₀ᵀ) * D)) =
      π ^ (j + 2 * k) • ((Dᵀ * (H₀ + H₀ᵀ) * (D + Dᵀ) - Dᵀ * H₀ * D +
          π ^ k • (Dᵀ * (H₀ + H₀ᵀ) * D * (H₀ + H₀ᵀ) * D)) +
        (Dᵀ * (H₀ + H₀ᵀ) * (D + Dᵀ) - Dᵀ * H₀ * D +
          π ^ k • (Dᵀ * (H₀ + H₀ᵀ) * D * (H₀ + H₀ᵀ) * D))ᵀ) := by
  set H := H₀ + H₀ᵀ with hHdef
  have hH : Hᵀ = H := by simp [hHdef, add_comm]
  -- The three ways `G` enters the expansion, each rewritten through `G * H = π ^ j • 1`.
  have hGHD : G * (H * D) = π ^ j • D := by rw [← Matrix.mul_assoc, hGH, smul_mul, one_mul]
  have hDHG : Dᵀ * (H * G) = π ^ j • Dᵀ := by
    have : (G * (H * D))ᵀ = Dᵀ * (H * G) := by
      simp [transpose_mul, hH, hG.eq, Matrix.mul_assoc]
    rw [← this, hGHD, transpose_smul]
  have hDHD : Dᵀ * (H * D) = Dᵀ * (H₀ * D) + Dᵀ * (H₀ᵀ * D) := by
    rw [hHdef, Matrix.add_mul, Matrix.mul_add]
  simp only [transpose_add, transpose_sub, transpose_one, transpose_smul, transpose_mul, hH,
    transpose_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hGHD,
    hDHG]
  rw [hDHD]
  module

/-- **Newton's method for Gram matrices.** Let `R` be `π`-adically complete, let `G` be symmetric,
and let `H₀` satisfy `G * (H₀ + H₀ᵀ) = π ^ j • 1`. If `G - A = π ^ (j + 1) • (D + Dᵀ)`, then
`Uᵀ * A * U = G` for some `U ≡ 1` modulo `π`. -/
theorem exists_transpose_mul_mul_eq_of_sub_eq (π : R) [IsAdicComplete (Ideal.span {π}) R]
    {j : ℕ} {G A H₀ D : Matrix n n R} (hG : G.IsSymm) (hGH : G * (H₀ + H₀ᵀ) = π ^ j • 1)
    (hA : G - A = π ^ (j + 1) • (D + Dᵀ)) :
    ∃ V : Matrix n n R, (1 + π • V)ᵀ * A * (1 + π • V) = G := by
  set H := H₀ + H₀ᵀ with hHdef
  -- The Newton iterates `(U m, D m)`, with `G - (U m)ᵀ A (U m) = π ^ (j + m + 1) • (D m + (D m)ᵀ)`.
  let s : ℕ → Matrix n n R × Matrix n n R := fun m ↦ Nat.rec (1, D)
    (fun m p ↦ (p.1 * (1 + π ^ (m + 1) • (H * p.2)), π ^ m • (p.2ᵀ * H * (p.2 + p.2ᵀ) -
      p.2ᵀ * H₀ * p.2 + π ^ (m + 1) • (p.2ᵀ * H * p.2 * H * p.2)))) m
  have hs (m : ℕ) : s (m + 1) = ((s m).1 * (1 + π ^ (m + 1) • (H * (s m).2)),
      π ^ m • ((s m).2ᵀ * H * ((s m).2 + (s m).2ᵀ) - (s m).2ᵀ * H₀ * (s m).2 +
        π ^ (m + 1) • ((s m).2ᵀ * H * (s m).2 * H * (s m).2))) := (rfl)
  have hinv (m : ℕ) : G - (s m).1ᵀ * A * (s m).1 = π ^ (j + m + 1) • ((s m).2 + (s m).2ᵀ) := by
    induction m with
    | zero => simpa [s] using hA
    | succ m ih =>
      have hA' : (s m).1ᵀ * A * (s m).1 = G - π ^ (j + (m + 1)) • ((s m).2 + (s m).2ᵀ) := by
        rw [← add_assoc, ← ih, sub_sub_cancel]
      rw [hs, transpose_mul, show ∀ X Y : Matrix n n R, Xᵀ * Yᵀ * A * (Y * X) =
        Xᵀ * (Yᵀ * A * Y) * X from fun _ _ ↦ by simp only [Matrix.mul_assoc], hA',
        sub_transpose_one_add_mul_mul_one_add_eq π j (m + 1) hG hGH, ← hHdef, transpose_smul,
        ← smul_add, smul_smul, ← pow_add]
      ring_nf
  -- Consecutive iterates are congruent modulo `π ^ (m + 1)`, so the iterates converge to `U`.
  obtain ⟨U, hU⟩ : ∃ U : Matrix n n R, ∀ m i i', π ^ m ∣ U i i' - (s m).1 i i' := by
    obtain ⟨L, hL⟩ := TauCeti.exists_forall_pow_dvd_sub π (fun m (p : n × n) ↦ (s m).1 p.1 p.2)
      fun m p ↦ ⟨((s m).1 * (H * (s m).2)) p.1 p.2, by
        simp only [hs, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, add_apply, smul_apply,
          smul_eq_mul, add_sub_cancel_left]⟩
    exact ⟨Matrix.of fun i i' ↦ L (i, i'), fun m i i' ↦ hL m (i, i')⟩
  -- `U ≡ 1` modulo `π`, since `U ≡ (s 1).1 = 1 + π • (H * D)`.
  obtain ⟨V, hV⟩ : ∃ V : Matrix n n R, U = 1 + π • V := by
    have hs1 : (s 1).1 = 1 + π • (H * D) := by
      rw [show s 1 = s (0 + 1) from rfl, hs]
      simp [s]
    choose V hV using hU 1
    refine ⟨Matrix.of fun i i' ↦ V i i' + (H * D) i i', ?_⟩
    ext i i'
    have := hV i i'
    rw [hs1] at this
    simp only [add_apply, smul_apply, of_apply, smul_eq_mul, pow_one] at this ⊢
    linear_combination this
  refine ⟨V, ?_⟩
  rw [← hV]
  -- `G - Uᵀ A U` vanishes modulo every power of `π`.
  suffices h : (fun p : n × n ↦ (G - Uᵀ * A * U) p.1 p.2) = 0 by
    ext i i'
    simpa [sub_eq_zero, eq_comm] using congrFun h (i, i')
  refine TauCeti.eq_zero_of_forall_pow_dvd π fun m p ↦ ?_
  choose W hW using hU m
  have hUW : U = (s m).1 + π ^ m • Matrix.of W := by
    ext i i'
    simp [← hW i i']
  have hdiff : G - Uᵀ * A * U = π ^ m • (π ^ (j + 1) • ((s m).2 + (s m).2ᵀ) -
      ((Matrix.of W)ᵀ * A * (s m).1 + (s m).1ᵀ * A * Matrix.of W +
        π ^ m • ((Matrix.of W)ᵀ * A * Matrix.of W))) := by
    rw [hUW, ← sub_add_cancel G ((s m).1ᵀ * A * (s m).1), hinv m]
    simp only [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [show j + m + 1 = m + (j + 1) by omega, pow_add]
    module
  rw [hdiff]
  exact ⟨_, rfl⟩

end Matrix
