/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Dilation
public import TauCeti.Topology.Instances.Matrix
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence in special linear groups

The special linear group `SL(n, R)` carries the topology induced from the matrices, which is the
product topology on the entries. So a sequence, or more generally a function along any filter,
converges in `SL(n, R)` exactly when each of its entries converges. For the same reason `SL(n, R)`
acts jointly continuously on column vectors, and it is second countable when `R` is; over a
topological ring, so then is its quotient `PSL(n, R)`. Over a `T1` topological ring it is a closed
subset of the matrices, so it is σ-compact when `R` is.

## Main results

* `Matrix.SpecialLinearGroup.tendsto_iff_tendsto_apply`: convergence in `SL(n, R)` is entrywise
  convergence.
* `Matrix.SpecialLinearGroup.instContinuousSMulVec`: `SL(n, R)` acts jointly continuously on
  column vectors.
* `Matrix.SpecialLinearGroup.instSigmaCompactSpace`: over a σ-compact `T1` topological ring,
  `SL(n, R)` is σ-compact.
* `Matrix.SpecialLinearGroup.instSecondCountableTopology`: over a second-countable ring,
  `SL(n, R)` is second countable, and hence so is its quotient `PSL(n, R)`.
* `Matrix.SpecialLinearGroup.exists_tendsto_dilation_conj`: a sequence in `SL(2, ℝ)` whose first
  diagonal entry converges to that of a diagonal matrix `D`, and whose off-diagonal products tend
  to `0`, converges to `D` after conjugating each term by a suitable power of a dilation.
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

/-- When addition and multiplication are continuous on `R`, `SL(n, R)` acts jointly continuously
on column vectors, by restricting the action of all square matrices. -/
instance instContinuousSMulVec [ContinuousAdd R] [ContinuousMul R] :
    ContinuousSMul (SpecialLinearGroup n R) (n → R) :=
  IsInducing.id.continuousSMul (M := Matrix n n R) continuous_subtype_val
    (SpecialLinearGroup.smul_def _ _)

/-- Over a σ-compact `T1` topological ring, `SL(n, R)` is σ-compact, as a closed subset of the
σ-compact space of matrices. -/
instance instSigmaCompactSpace [IsTopologicalRing R] [T1Space R] [SigmaCompactSpace R] :
    SigmaCompactSpace (SpecialLinearGroup n R) :=
  isClosedEmbedding_val.sigmaCompactSpace

/-- Over a second-countable ring, `SL(n, R)` is second countable, as a subspace of the
second-countable space of matrices.

Over a topological ring, `PSL(n, R)` is the quotient of `SL(n, R)` by its centre, so it is then
second countable as well, by `QuotientGroup.instSecondCountableTopology`; in particular `SL(2, ℝ)`
and `PSL(2, ℝ)` are second countable. -/
instance instSecondCountableTopology [SecondCountableTopology R] :
    SecondCountableTopology (SpecialLinearGroup n R) :=
  (IsInducing.subtypeVal (t := {A : Matrix n n R | A.det = 1})).secondCountableTopology

/-- If the first diagonal entry of a sequence of matrices of `SL(2, ℝ)` converges to that of a
diagonal matrix `D` and the products of its off-diagonal entries tend to `0`, then conjugating each
term by a suitable power of `dilation s`, `s > 0`, gives a sequence converging to `D`. The other
diagonal entry then converges too, by the determinant. -/
theorem exists_tendsto_dilation_conj {s : ℝ} (hs : 0 < s) {M : ℕ → SL(2, ℝ)} {D : SL(2, ℝ)}
    (h00 : Tendsto (fun n ↦ M n 0 0) atTop (𝓝 (D 0 0))) (hD01 : D 0 1 = 0) (hD10 : D 1 0 = 0)
    (hβ : Tendsto (fun n ↦ M n 0 1 * M n 1 0) atTop (𝓝 0)) :
    ∃ k : ℕ → ℤ, Tendsto (fun n ↦ dilation (k n * s) * M n * dilation (-(k n * s))) atTop
      (𝓝 D) := by
  -- the other diagonal entry converges as well, by the determinant identities
  have hdetD : D 0 0 * D 1 1 = 1 := by
    have h := D.det_coe
    rw [Matrix.det_fin_two, hD01, hD10] at h
    linarith
  have hD00 : D 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdetD
  have h11 : Tendsto (fun n ↦ M n 1 1) atTop (𝓝 (D 1 1)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)).add hβ).div h00 hD00
    have hD11 : D 1 1 = (1 + 0) / D 0 0 := by field_simp; linarith
    rw [hD11]
    refine h.congr' ((h00.eventually_ne hD00).mono fun n hn ↦ ?_)
    have hdet := (M n).det_coe
    rw [Matrix.det_fin_two] at hdet
    simp only [Pi.div_apply]
    field_simp
    linarith
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
