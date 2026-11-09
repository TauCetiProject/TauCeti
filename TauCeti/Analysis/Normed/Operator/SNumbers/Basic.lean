/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
# Axioms for s-number sequences

An s-number family assigns a nonnegative sequence to every bounded operator between normed
spaces over a fixed field. Pietsch's axioms abstract the common calculus of approximation,
Gelfand, Kolmogorov, Bernstein and Hilbert numbers. The indexing is zero-based: the first
term is the operator norm, and the term at index `n` vanishes on operators of rank at most `n`.

This file defines the ordinary and strict axioms and derives the norm bound, Lipschitz
continuity and scalar homogeneity. Strictness means normalization on every identity below
the dimension, not merely on the finite Euclidean identities.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §1.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
* M. Ullrich, *Inequalities between s-numbers*, Adv. Oper. Theory 9 (2024), art. 82,
  Remark 1, for the strict normalization (S5′) and its implication of (S5).
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Basic.lean`: an earlier Lean formalization of the same axiom API.
-/

public section

open scoped NNReal

universe u

namespace TauCeti.SNumbers

/-- A family of nonnegative sequences on bounded operators between all normed spaces in
one universe over the given field. -/
abbrev SNumberFamily (𝕜 : Type u) [NontriviallyNormedField 𝕜] :=
  ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y], (X →L[𝕜] Y) → ℕ → ℝ≥0

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- Pietsch's five s-number axioms, with zero-based indexing and Euclidean normalization.
The norm and monotonicity clauses together constitute the first axiom. -/
structure IsSNumberSequence (s : SNumberFamily 𝕜) : Prop where
  /-- The zeroth term is the operator norm. -/
  norm : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y), s T 0 = ‖T‖₊
  /-- The terms decrease with the index. -/
  antitone : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y), Antitone (s T)
  /-- Perturbing an operator changes each term by at most the perturbation norm. -/
  add_le : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S T : X →L[𝕜] Y) (n : ℕ),
    s (S + T) n ≤ s S n + ‖T‖₊
  /-- The two-sided ideal inequality. -/
  comp_le : ∀ {W X Y Z : Type u}
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (B : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (A : W →L[𝕜] X) (n : ℕ),
    s (B ∘L T ∘L A) n ≤ ‖B‖₊ * s T n * ‖A‖₊
  /-- Rank at most `n` forces vanishing at index `n`. -/
  eq_zero_of_rank_le : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {T : X →L[𝕜] Y} {n : ℕ},
    T.rank ≤ n → s T n = 0
  /-- The identity on Euclidean space of dimension `n + 1` has term `1` at index `n`. -/
  normalize : ∀ n : ℕ, s (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1

/-- A strict s-number sequence is normalized on the identity of every normed space at
all indices strictly below its cardinal dimension, including infinite dimension
(Ullrich 2024, Remark 1). -/
structure IsStrictSNumberSequence (s : SNumberFamily 𝕜) : Prop
    extends IsSNumberSequence s where
  /-- Identity normalization below the dimension. -/
  normalize_of_lt_rank : ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (n : ℕ), (n : Cardinal) < Module.rank 𝕜 X → s (ContinuousLinearMap.id 𝕜 X) n = 1

/-- Build a strict s-number sequence from the first four axioms and identity normalization
below the dimension. The Euclidean normalization follows, since the Euclidean space of
dimension `n + 1` has rank `n + 1 > n`. -/
theorem IsStrictSNumberSequence.of_normalize_of_lt_rank {s : SNumberFamily 𝕜}
    (norm : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y), s T 0 = ‖T‖₊)
    (antitone : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y), Antitone (s T))
    (add_le : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S T : X →L[𝕜] Y) (n : ℕ),
      s (S + T) n ≤ s S n + ‖T‖₊)
    (comp_le : ∀ {W X Y Z : Type u}
      [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
      (B : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (A : W →L[𝕜] X) (n : ℕ),
      s (B ∘L T ∘L A) n ≤ ‖B‖₊ * s T n * ‖A‖₊)
    (eq_zero_of_rank_le : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {T : X →L[𝕜] Y} {n : ℕ},
      T.rank ≤ n → s T n = 0)
    (normalize_of_lt_rank : ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      (n : ℕ), (n : Cardinal) < Module.rank 𝕜 X → s (ContinuousLinearMap.id 𝕜 X) n = 1) :
    IsStrictSNumberSequence s where
  norm := norm
  antitone := antitone
  add_le := add_le
  comp_le := comp_le
  eq_zero_of_rank_le := eq_zero_of_rank_le
  normalize n := normalize_of_lt_rank n <| by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).rank_eq, rank_fin_fun]
    exact_mod_cast n.lt_succ_self
  normalize_of_lt_rank := normalize_of_lt_rank

namespace IsSNumberSequence

variable {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)

include hs
variable {W X Y Z : Type u}
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- Every term is bounded by the operator norm. -/
theorem le_nnnorm (T : X →L[𝕜] Y) (n : ℕ) : s T n ≤ ‖T‖₊ :=
  (hs.antitone T (Nat.zero_le n)).trans_eq (hs.norm T)

/-- All terms of the zero operator vanish. -/
theorem zero (n : ℕ) : s (0 : X →L[𝕜] Y) n = 0 := by
  simpa using hs.le_nnnorm (0 : X →L[𝕜] Y) n

/-- Each term is `1`-Lipschitz with respect to the operator norm. -/
theorem abs_sub_le (S T : X →L[𝕜] Y) (n : ℕ) :
    |(s S n : ℝ) - s T n| ≤ ‖S - T‖ := by
  have key (S T : X →L[𝕜] Y) : (s S n : ℝ) ≤ s T n + ‖S - T‖ := by
    have h := hs.add_le T (S - T) n
    rw [add_sub_cancel] at h
    exact_mod_cast h
  rw [abs_sub_le_iff]
  exact ⟨sub_le_iff_le_add'.mpr (key S T),
    sub_le_iff_le_add'.mpr (norm_sub_rev T S ▸ key T S)⟩

/-- At each index an s-number sequence is `1`-Lipschitz. -/
theorem lipschitzWith (n : ℕ) : LipschitzWith 1 (fun T : X →L[𝕜] Y ↦ s T n) :=
  LipschitzWith.of_dist_le_mul fun S T ↦ by
    simpa [NNReal.dist_eq, dist_eq_norm] using hs.abs_sub_le S T n

/-- Each term depends continuously on the operator in operator norm. -/
theorem continuous (n : ℕ) : Continuous (fun T : X →L[𝕜] Y ↦ s T n) :=
  (hs.lipschitzWith n).continuous

/-- Postcomposition scales s-numbers by at most the operator norm. -/
theorem comp_le_left (B : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (n : ℕ) :
    s (B ∘L T) n ≤ ‖B‖₊ * s T n := by
  have hid : ‖ContinuousLinearMap.id 𝕜 X‖₊ ≤ 1 := by
    exact_mod_cast ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := X)
  calc
    s (B ∘L T) n ≤ ‖B‖₊ * s T n * ‖ContinuousLinearMap.id 𝕜 X‖₊ := by
      simpa using hs.comp_le B T (ContinuousLinearMap.id 𝕜 X) n
    _ ≤ ‖B‖₊ * s T n := mul_le_of_le_one_right' hid

/-- Precomposition scales s-numbers by at most the operator norm. -/
theorem comp_le_right (T : X →L[𝕜] Y) (A : W →L[𝕜] X) (n : ℕ) :
    s (T ∘L A) n ≤ s T n * ‖A‖₊ := by
  have hid : ‖ContinuousLinearMap.id 𝕜 Y‖₊ ≤ 1 := by
    exact_mod_cast ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := Y)
  calc
    s (T ∘L A) n ≤ ‖ContinuousLinearMap.id 𝕜 Y‖₊ * s T n * ‖A‖₊ := by
      simpa using hs.comp_le (ContinuousLinearMap.id 𝕜 Y) T A n
    _ ≤ s T n * ‖A‖₊ := by gcongr; exact mul_le_of_le_one_left' hid

private theorem smul_le (c : 𝕜) (T : X →L[𝕜] Y) (n : ℕ) :
    s (c • T) n ≤ ‖c‖₊ * s T n := by
  have hid : ‖ContinuousLinearMap.id 𝕜 Y‖₊ ≤ 1 := by
    exact_mod_cast ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := Y)
  calc
    s (c • T) n ≤ ‖c • ContinuousLinearMap.id 𝕜 Y‖₊ * s T n := by
      simpa using hs.comp_le_left (c • ContinuousLinearMap.id 𝕜 Y) T n
    _ ≤ (‖c‖₊ * ‖ContinuousLinearMap.id 𝕜 Y‖₊) * s T n := by
      gcongr
      exact nnnorm_smul_le _ _
    _ ≤ ‖c‖₊ * s T n := by gcongr; exact mul_le_of_le_one_right' hid

/-- Every s-number sequence is absolutely homogeneous. -/
theorem smul (c : 𝕜) (T : X →L[𝕜] Y) (n : ℕ) : s (c • T) n = ‖c‖₊ * s T n := by
  refine (hs.smul_le c T n).antisymm ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hs.zero]
  calc
    ‖c‖₊ * s T n = ‖c‖₊ * s (c⁻¹ • c • T) n := by rw [inv_smul_smul₀ hc]
    _ ≤ ‖c‖₊ * (‖c⁻¹‖₊ * s (c • T) n) := by gcongr; exact hs.smul_le _ _ _
    _ = s (c • T) n := by simp [hc]

/-- Negation leaves every term unchanged. -/
theorem neg (T : X →L[𝕜] Y) (n : ℕ) : s (-T) n = s T n := by
  simpa using hs.smul (-1) T n

end IsSNumberSequence

end TauCeti.SNumbers
