/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# s-number sequences

An *s-number family* assigns to every bounded operator `T : X →L[𝕜] Y` between normed spaces in
one universe a sequence `n ↦ s T n` in `ℝ≥0`. Pietsch's axioms single out the families that
behave like the singular values of Hilbert-space operators:

* (S1) `s T 0 = ‖T‖` and `n ↦ s T n` is antitone;
* (S2) `s (S + T) n ≤ s S n + ‖T‖`;
* (S3) `s (B ∘ T ∘ A) n ≤ ‖B‖ * s T n * ‖A‖`;
* (S4) `s T n = 0` when `rank T ≤ n`;
* (S5) `s (id : ℓ₂^{n+1} → ℓ₂^{n+1}) n = 1`.

A *strict* s-number sequence satisfies, in place of the normalization (S5) alone, the stronger
(S5′): `s (id_X) n = 1` for every normed space `X` with `n < rank X`, including
infinite-dimensional `X`. Classically, the approximation, Gelfand, Kolmogorov and Bernstein
numbers are strict s-number sequences, while the Hilbert numbers are s-number sequences that are
not strict.

The indexing is zero-based, so `s₀(T) = ‖T‖`. This file defines the family type and the two
predicates, and proves the consequences every s-number sequence shares: the bound by the operator
norm, the vanishing on the zero operator, the one-sided ideal inequalities, Lipschitz continuity
in operator norm, and scalar homogeneity.

## Main declarations

* `TauCeti.SNumberFamily`: an `ℝ≥0`-valued sequence for every bounded operator between normed
  `𝕜`-spaces in one universe.
* `TauCeti.IsSNumberSequence`: Pietsch's axioms (S1)–(S5).
* `TauCeti.IsStrictSNumberSequence`: the axioms together with the strict normalization (S5′).
* `TauCeti.IsStrictSNumberSequence.of_id_of_lt_rank`: (S1)–(S4) and (S5′) give a strict s-number
  sequence, with (S5) derived from (S5′).
* `TauCeti.IsSNumberSequence.le_nnnorm`: `s T n ≤ ‖T‖`.
* `TauCeti.IsSNumberSequence.abs_sub_le`: `|s S n - s T n| ≤ ‖S - T‖`.
* `TauCeti.IsSNumberSequence.continuous`: `T ↦ s T n` is continuous in operator norm.
* `TauCeti.IsSNumberSequence.smul`: `s (c • T) n = ‖c‖ * s T n`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. **51** (1974), 201–223, §1.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.2.
* M. Ullrich, *Inequalities between s-numbers*, Adv. Oper. Theory **9** (2024), art. 82,
  Remark 1, for the strict normalization (S5′).
* M. Ullrich, *Lean-SNumbers*, https://github.com/mario-ullrich/Lean-SNumbers (Apache-2.0),
  `SNumbers/Basic.lean`: an earlier Lean formalization of the axioms.
-/

public section

open scoped NNReal

universe u

namespace TauCeti

/-- An s-number family over `𝕜`: one `ℝ≥0`-valued sequence `s T : ℕ → ℝ≥0` for every bounded
linear map `T : X →L[𝕜] Y` between normed `𝕜`-spaces `X`, `Y` in the universe of `𝕜`. -/
abbrev SNumberFamily (𝕜 : Type u) [NontriviallyNormedField 𝕜] :=
  ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y], (X →L[𝕜] Y) → ℕ → ℝ≥0

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- **Pietsch's axioms.** An s-number sequence is an s-number family with
(S1) `s T 0 = ‖T‖` and `n ↦ s T n` antitone; (S2) `s (S + T) n ≤ s S n + ‖T‖`;
(S3) `s (B ∘ T ∘ A) n ≤ ‖B‖ * s T n * ‖A‖`; (S4) `s T n = 0` when `rank T ≤ n`;
(S5) `s (id : ℓ₂^{n+1} → ℓ₂^{n+1}) n = 1`, for the Euclidean space `ℓ₂^{n+1}` over `𝕜`. -/
structure IsSNumberSequence (s : SNumberFamily 𝕜) : Prop where
  /-- (S1) The zeroth term is the operator norm. -/
  apply_zero : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y), s T 0 = ‖T‖₊
  /-- (S1) The sequence is nonincreasing. -/
  antitone : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y), Antitone (s T)
  /-- (S2) Additivity against the operator norm. -/
  add_le : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S T : X →L[𝕜] Y) (n : ℕ),
    s (S + T) n ≤ s S n + ‖T‖₊
  /-- (S3) The two-sided ideal inequality. -/
  comp_comp_le : ∀ {W X Y Z : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (B : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (A : W →L[𝕜] X) (n : ℕ),
    s (B ∘L T ∘L A) n ≤ ‖B‖₊ * s T n * ‖A‖₊
  /-- (S4) The rank property: the terms vanish from the rank onwards. -/
  eq_zero_of_rank_le : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y) {n : ℕ},
    T.rank ≤ n → s T n = 0
  /-- (S5) The normalization on the Euclidean identities. -/
  id_euclideanSpace : ∀ n : ℕ, s (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1

/-- **Strict s-number sequences.** An s-number sequence with the strict normalization (S5′):
`s (id_X) n = 1` for every normed space `X` with `n < rank X`, including infinite-dimensional
`X`. Since `ℓ₂^{n+1}` has rank `n + 1`, (S5′) contains (S5). -/
structure IsStrictSNumberSequence (s : SNumberFamily 𝕜) : Prop
    extends IsSNumberSequence s where
  /-- (S5′) The identity of a space of rank greater than `n` has `n`-th term `1`. -/
  id_of_lt_rank : ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {n : ℕ},
    n < Module.rank 𝕜 X → s (ContinuousLinearMap.id 𝕜 X) n = 1

/-- Build a strict s-number sequence from (S1)–(S4) and the strict normalization (S5′); the
normalization (S5) follows from (S5′) since `ℓ₂^{n+1}` has rank `n + 1`. -/
theorem IsStrictSNumberSequence.of_id_of_lt_rank {s : SNumberFamily 𝕜}
    (apply_zero : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y), s T 0 = ‖T‖₊)
    (antitone : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y), Antitone (s T))
    (add_le : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S T : X →L[𝕜] Y) (n : ℕ),
      s (S + T) n ≤ s S n + ‖T‖₊)
    (comp_comp_le : ∀ {W X Y Z : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
      (B : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (A : W →L[𝕜] X) (n : ℕ),
      s (B ∘L T ∘L A) n ≤ ‖B‖₊ * s T n * ‖A‖₊)
    (eq_zero_of_rank_le : ∀ {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y) {n : ℕ},
      T.rank ≤ n → s T n = 0)
    (id_of_lt_rank : ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {n : ℕ},
      n < Module.rank 𝕜 X → s (ContinuousLinearMap.id 𝕜 X) n = 1) :
    IsStrictSNumberSequence s where
  apply_zero := apply_zero
  antitone := antitone
  add_le := add_le
  comp_comp_le := comp_comp_le
  eq_zero_of_rank_le := eq_zero_of_rank_le
  id_euclideanSpace n := id_of_lt_rank <| by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).rank_eq, rank_fin_fun]
    exact_mod_cast n.lt_succ_self
  id_of_lt_rank := id_of_lt_rank

namespace IsSNumberSequence

variable {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)
variable {X Y Z : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
include hs

/-- Every term of an s-number sequence is bounded by the operator norm. -/
theorem le_nnnorm (T : X →L[𝕜] Y) (n : ℕ) : s T n ≤ ‖T‖₊ :=
  hs.apply_zero T ▸ hs.antitone T (Nat.zero_le n)

/-- The zero operator has vanishing s-numbers. -/
theorem map_zero (n : ℕ) : s (0 : X →L[𝕜] Y) n = 0 :=
  nonpos_iff_eq_zero.mp <| (hs.le_nnnorm 0 n).trans_eq nnnorm_zero

/-- **Left ideal inequality.** `s (B ∘ T) n ≤ ‖B‖ * s T n`. -/
theorem comp_le_left (B : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (n : ℕ) :
    s (B ∘L T) n ≤ ‖B‖₊ * s T n := by
  have h := hs.comp_comp_le B T (ContinuousLinearMap.id 𝕜 X) n
  rw [ContinuousLinearMap.comp_id] at h
  calc s (B ∘L T) n ≤ ‖B‖₊ * s T n * ‖ContinuousLinearMap.id 𝕜 X‖₊ := h
    _ ≤ ‖B‖₊ * s T n * 1 := by gcongr; exact_mod_cast ContinuousLinearMap.norm_id_le
    _ = ‖B‖₊ * s T n := by rw [mul_one]

/-- **Right ideal inequality.** `s (T ∘ A) n ≤ s T n * ‖A‖`. -/
theorem comp_le_right (T : Y →L[𝕜] Z) (A : X →L[𝕜] Y) (n : ℕ) :
    s (T ∘L A) n ≤ s T n * ‖A‖₊ := by
  have h := hs.comp_comp_le (ContinuousLinearMap.id 𝕜 Z) T A n
  rw [ContinuousLinearMap.id_comp] at h
  calc s (T ∘L A) n ≤ ‖ContinuousLinearMap.id 𝕜 Z‖₊ * s T n * ‖A‖₊ := h
    _ ≤ 1 * s T n * ‖A‖₊ := by gcongr; exact_mod_cast ContinuousLinearMap.norm_id_le
    _ = s T n * ‖A‖₊ := by rw [one_mul]

/-- At a fixed index an s-number sequence moves by at most the operator-norm distance:
`s S n ≤ s T n + ‖S - T‖`. -/
theorem le_add_nnnorm_sub (S T : X →L[𝕜] Y) (n : ℕ) : s S n ≤ s T n + ‖S - T‖₊ := by
  simpa using hs.add_le T (S - T) n

/-- **Lipschitz bound.** `|s S n - s T n| ≤ ‖S - T‖`. -/
theorem abs_sub_le (S T : X →L[𝕜] Y) (n : ℕ) : |(s S n : ℝ) - s T n| ≤ ‖S - T‖ := by
  have key (S T : X →L[𝕜] Y) : (s S n : ℝ) ≤ s T n + ‖S - T‖ :=
    mod_cast hs.le_add_nnnorm_sub S T n
  rw [abs_sub_le_iff]
  exact ⟨sub_le_iff_le_add'.mpr (key S T), sub_le_iff_le_add'.mpr (norm_sub_rev T S ▸ key T S)⟩

/-- At each index, `T ↦ s T n` is `1`-Lipschitz in operator norm. -/
theorem lipschitzWith (n : ℕ) : LipschitzWith 1 fun T : X →L[𝕜] Y ↦ s T n :=
  LipschitzWith.of_dist_le_mul fun S T ↦ by
    simpa [NNReal.dist_eq, dist_eq_norm] using hs.abs_sub_le S T n

/-- **Norm continuity.** At each index, `T ↦ s T n` is continuous in operator norm. -/
theorem continuous (n : ℕ) : Continuous fun T : X →L[𝕜] Y ↦ s T n :=
  (hs.lipschitzWith n).continuous

/-- **Homogeneity.** `s (c • T) n = ‖c‖ * s T n`. -/
theorem smul (c : 𝕜) (T : X →L[𝕜] Y) (n : ℕ) : s (c • T) n = ‖c‖₊ * s T n := by
  have hle (c : 𝕜) (T : X →L[𝕜] Y) : s (c • T) n ≤ ‖c‖₊ * s T n := by
    have h := hs.comp_le_left (c • ContinuousLinearMap.id 𝕜 Y) T n
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] at h
    refine h.trans ?_
    gcongr
    exact (nnnorm_smul_le c _).trans (mul_le_of_le_one_right' ContinuousLinearMap.norm_id_le)
  refine (hle c T).antisymm ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ‖c‖₊ * s T n = ‖c‖₊ * s (c⁻¹ • c • T) n := by rw [inv_smul_smul₀ hc]
    _ ≤ ‖c‖₊ * (‖c⁻¹‖₊ * s (c • T) n) := by gcongr; exact hle _ _
    _ = s (c • T) n := by rw [nnnorm_inv, ← mul_assoc, mul_inv_cancel₀ (by simpa), one_mul]

end IsSNumberSequence

end TauCeti
