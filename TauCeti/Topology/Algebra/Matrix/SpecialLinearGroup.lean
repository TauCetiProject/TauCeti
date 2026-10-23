/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Dilation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence in special linear groups

The special linear group `SL(n, R)` carries the topology induced from the matrices, which is the
product topology on the entries. So a sequence, or more generally a function along any filter,
converges in `SL(n, R)` exactly when each of its entries converges.

## Main results

* `Matrix.SpecialLinearGroup.tendsto_iff_tendsto_apply`: convergence in `SL(n, R)` is entrywise
  convergence.
* `Matrix.SpecialLinearGroup.exists_tendsto_dilation_conj`: a sequence in `SL(2, ℝ)` whose diagonal
  entries converge to those of a diagonal matrix `D`, and whose off-diagonal products tend to `0`,
  converges to `D` after conjugating each term by a suitable power of a dilation.
-/

public section

open Filter Topology
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {n R α : Type*} [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]

/-- Convergence in `SL(n, R)` is entrywise convergence. -/
theorem tendsto_iff_tendsto_apply {l : Filter α} {M : α → SpecialLinearGroup n R}
    {D : SpecialLinearGroup n R} :
    Tendsto M l (𝓝 D) ↔ ∀ i j, Tendsto (fun x ↦ M x i j) l (𝓝 (D i j)) := by
  exact (IsInducing.subtypeVal (t := {A : Matrix n n R | A.det = 1})).tendsto_nhds_iff.trans <|
    tendsto_pi_nhds.trans <| forall_congr' fun _ ↦ tendsto_pi_nhds

/-- If the diagonal entries of a sequence of matrices of `SL(2, ℝ)` converge to those of a diagonal
matrix `D` and the products of its off-diagonal entries tend to `0`, then conjugating each term by a
suitable power of `dilation s`, `s > 0`, gives a sequence converging to `D`. -/
theorem exists_tendsto_dilation_conj {s : ℝ} (hs : 0 < s) {M : ℕ → SL(2, ℝ)} {D : SL(2, ℝ)}
    (h00 : Tendsto (fun n ↦ M n 0 0) atTop (𝓝 (D 0 0)))
    (h11 : Tendsto (fun n ↦ M n 1 1) atTop (𝓝 (D 1 1))) (hD01 : D 0 1 = 0) (hD10 : D 1 0 = 0)
    (hβ : Tendsto (fun n ↦ M n 0 1 * M n 1 0) atTop (𝓝 0)) :
    ∃ k : ℕ → ℤ, Tendsto (fun n ↦ dilation (k n * s) * M n * dilation (-(k n * s))) atTop
      (𝓝 D) := by
  -- the radius `ρₙ = √|βₙ| + 1 / (n + 1)` bounds the balanced off-diagonal entries
  set ρ : ℕ → ℝ := fun n ↦ √|M n 0 1 * M n 1 0| + 1 / ((n : ℝ) + 1)
  have hρ0 (n : ℕ) : 0 < ρ n := by positivity
  have hρsq (n : ℕ) : |M n 0 1 * M n 1 0| ≤ ρ n ^ 2 := by
    have h := Real.sq_sqrt (abs_nonneg (M n 0 1 * M n 1 0))
    have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    nlinarith [Real.sqrt_nonneg |M n 0 1 * M n 1 0|]
  have hρ : Tendsto (fun n ↦ Real.exp s * ρ n) atTop (𝓝 0) := by
    have habs := hβ.abs
    rw [abs_zero] at habs
    have h := ((Real.continuous_sqrt.tendsto 0).comp habs).add
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.sqrt_zero, zero_add] at h
    have h' := h.const_mul (Real.exp s)
    rw [mul_zero] at h'
    exact h'
  choose k hk using fun n ↦ exists_dilation_conj_le hs (hρ0 n) (hρsq n)
  set C : ℕ → SL(2, ℝ) := fun n ↦ dilation (k n * s) * M n * dilation (-(k n * s))
  have h01 : Tendsto (fun n ↦ C n 0 1) atTop (𝓝 (D 0 1)) := by
    rw [hD01]
    refine squeeze_zero_norm (fun n ↦ ?_) hρ
    simpa only [C, Real.norm_eq_abs] using (hk n).1
  have h10 : Tendsto (fun n ↦ C n 1 0) atTop (𝓝 (D 1 0)) := by
    rw [hD10]
    refine squeeze_zero_norm (fun n ↦ ?_) hρ
    simpa only [C, Real.norm_eq_abs] using (hk n).2
  refine ⟨k, tendsto_iff_tendsto_apply.mpr (Fin.forall_fin_two.mpr
    ⟨Fin.forall_fin_two.mpr ⟨?_, h01⟩, Fin.forall_fin_two.mpr ⟨h10, ?_⟩⟩)⟩
  · simpa only [C, dilation_conj_apply_zero_zero] using h00
  · simpa only [C, dilation_conj_apply_one_one] using h11

end Matrix.SpecialLinearGroup
