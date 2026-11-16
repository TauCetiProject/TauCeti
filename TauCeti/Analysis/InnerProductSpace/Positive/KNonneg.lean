/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.KyFan
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Analysis.InnerProductSpace.Trace.Projection
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.Finset.PartialSum

/-!
# `k`-nonnegative and `k`-positive operators

An operator `T` on an inner product space is **`k`-nonnegative** (`LinearMap.IsKNonneg`) when
its diagonal entries along any orthonormal family of `k` vectors have nonnegative sum,
`0 ≤ ∑ᵢ re ⟪T wᵢ, wᵢ⟫`, and **`k`-positive** (`LinearMap.IsKPos`) when that sum is always
positive. For `k = 1` and symmetric `T` this is ordinary positivity. Any operator `T` is
`k`-nonnegative exactly when its compression to every `k`-dimensional subspace has trace with
nonnegative real part (`LinearMap.isKNonneg_iff_forall_re_trace_nonneg`). The condition
interpolates between positivity and nonnegativity of the trace: by Ky Fan's minimum principle a
symmetric `T` on an `n`-dimensional space is `k`-nonnegative, for `k ≤ n`, exactly when the sum of
its `k` smallest eigenvalues is nonnegative
(`LinearMap.IsSymmetric.isKNonneg_iff_sum_eigenvalues_rev_nonneg`).

The case `k = 2` is the curvature condition of Böhm and Wilking: a curvature operator on the
bivectors `Λ²V` of a space `V` of dimension at least `3` is `2`-nonnegative when the sum of its two
smallest eigenvalues is nonnegative.
In dimension three this is nonnegativity of the Ricci curvature. Operators that are
`k`-nonnegative form a closed convex cone, invariant under conjugation by linear isometries,
and `k`-nonnegativity implies `m`-nonnegativity for `1 ≤ k ≤ m`
(`LinearMap.IsKNonneg.mono`): positive operators are `2`-nonnegative.

## Main declarations

* `LinearMap.IsKNonneg`, `LinearMap.IsKPos`: the two conditions.
* `LinearMap.IsKNonneg.mono`, `LinearMap.IsKPos.mono`: monotonicity in `k`.
* `LinearMap.isKNonneg_one_iff`, `LinearMap.isKPos_one_iff`: `1`-nonnegativity and
  `1`-positivity as conditions on the quadratic form.
* `LinearMap.isPositive_iff_isSymmetric_and_isKNonneg_one`: positivity is `1`-nonnegativity of
  a symmetric operator.
* `LinearMap.IsSymmetric.isKNonneg_iff_sum_eigenvalues_rev_nonneg`,
  `LinearMap.IsSymmetric.isKPos_iff_sum_eigenvalues_rev_pos`: the eigenvalue characterizations.
* `LinearMap.IsSymmetric.isKNonneg_two_iff_eigenvalues_add_eigenvalues_nonneg`,
  `LinearMap.IsSymmetric.isKPos_two_iff_eigenvalues_add_eigenvalues_pos`: their form for the two
  smallest eigenvalues.
* `LinearMap.isKNonneg_iff_forall_re_trace_nonneg`,
  `LinearMap.isKPos_iff_forall_re_trace_pos`: the characterizations by traces of compressions,
  computed by `LinearMap.re_trace_orthogonalProjectionOnto_comp_comp_subtype_eq_sum_re_inner`.
* `LinearMap.isKNonneg_conj_iff`, `LinearMap.isKPos_conj_iff`: invariance under conjugation by
  linear isometries.
* `ContinuousLinearMap.isClosed_setOf_isKNonneg`: the `k`-nonnegative bounded operators form a
  closed set.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. **167** (2008), 1079–1097.
* K. Fan, *On a theorem of Weyl concerning eigenvalues of linear transformations. I*,
  Proc. Nat. Acad. Sci. U.S.A. **35** (1949), 652–655.
-/

public section

open Module Finset

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- An operator `T` is **`k`-nonnegative** when along every orthonormal family `(wᵢ)` of `k`
vectors its diagonal entries have nonnegative sum, `0 ≤ ∑ᵢ re ⟪T wᵢ, wᵢ⟫`. -/
def IsKNonneg (T : E →ₗ[𝕜] E) (k : ℕ) : Prop :=
  ∀ w : Fin k → E, Orthonormal 𝕜 w → 0 ≤ ∑ i, RCLike.re ⟪T (w i), w i⟫

/-- An operator `T` is **`k`-positive** when along every orthonormal family `(wᵢ)` of `k`
vectors its diagonal entries have positive sum, `0 < ∑ᵢ re ⟪T wᵢ, wᵢ⟫`. -/
def IsKPos (T : E →ₗ[𝕜] E) (k : ℕ) : Prop :=
  ∀ w : Fin k → E, Orthonormal 𝕜 w → 0 < ∑ i, RCLike.re ⟪T (w i), w i⟫

variable {T S : E →ₗ[𝕜] E} {k m : ℕ}

theorem isKNonneg_iff :
    T.IsKNonneg k ↔ ∀ w : Fin k → E, Orthonormal 𝕜 w → 0 ≤ ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
  Iff.rfl

theorem isKPos_iff :
    T.IsKPos k ↔ ∀ w : Fin k → E, Orthonormal 𝕜 w → 0 < ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
  Iff.rfl

/-- A `k`-nonnegative operator has nonnegative diagonal sum along every orthonormal family indexed
by a type with `k` elements. -/
theorem IsKNonneg.sum_re_inner_nonneg (h : T.IsKNonneg k) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = k) {w : ι → E} (hw : Orthonormal 𝕜 w) :
    0 ≤ ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
  T.forall_orthonormal_fintype_of_fin (0 ≤ ·) h hι hw

/-- A `k`-positive operator has positive diagonal sum along every orthonormal family indexed by a
type with `k` elements. -/
theorem IsKPos.sum_re_inner_pos (h : T.IsKPos k) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = k) {w : ι → E} (hw : Orthonormal 𝕜 w) :
    0 < ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
  T.forall_orthonormal_fintype_of_fin (0 < ·) h hι hw

/-- A `k`-positive operator is `k`-nonnegative. -/
theorem IsKPos.isKNonneg (h : T.IsKPos k) : T.IsKNonneg k :=
  fun w hw ↦ (h w hw).le

/-- Every operator is `0`-nonnegative: the empty sum vanishes. -/
@[simp]
theorem isKNonneg_zero_right (T : E →ₗ[𝕜] E) : T.IsKNonneg 0 :=
  fun _ _ ↦ by simp

/-- No operator is `0`-positive: the empty sum vanishes. -/
@[simp]
theorem not_isKPos_zero_right (T : E →ₗ[𝕜] E) : ¬T.IsKPos 0 :=
  fun h ↦ by simpa using h Fin.elim0 ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩

/-- A nonzero vector `x` is `‖x‖` times a unit vector `u`, so its diagonal entry is `‖x‖ ^ 2` times
the diagonal entry along the orthonormal family consisting of `u`. -/
private theorem exists_orthonormal_re_inner_eq {x : E} (hx : x ≠ 0) :
    ∃ w : Fin 1 → E, Orthonormal 𝕜 w ∧
      RCLike.re ⟪T x, x⟫ = ‖x‖ ^ 2 * RCLike.re ⟪T (w 0), w 0⟫ := by
  set u := (‖x‖⁻¹ : 𝕜) • x
  have hxu : x = (‖x‖ : 𝕜) • u := by
    simp [u, smul_smul, norm_ne_zero_iff.2 hx]
  refine ⟨fun _ ↦ u, ⟨fun _ ↦ norm_smul_inv_norm hx,
    fun i j hij ↦ absurd (Subsingleton.elim i j) hij⟩, ?_⟩
  conv_lhs => rw [hxu]
  simp [inner_smul_left, inner_smul_right]
  ring

/-- `1`-nonnegativity is nonnegativity of the quadratic form `x ↦ re ⟪T x, x⟫`. -/
theorem isKNonneg_one_iff : T.IsKNonneg 1 ↔ ∀ x, 0 ≤ RCLike.re ⟪T x, x⟫ := by
  refine ⟨fun h x ↦ ?_, fun h w _ ↦ by simpa using h (w 0)⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨w, hw, hscale⟩ := exists_orthonormal_re_inner_eq (T := T) hx
  rw [hscale]
  exact mul_nonneg (sq_nonneg _) (by simpa using h w hw)

/-- `1`-positivity is positivity of the quadratic form `x ↦ re ⟪T x, x⟫` on nonzero vectors. -/
theorem isKPos_one_iff : T.IsKPos 1 ↔ ∀ x, x ≠ 0 → 0 < RCLike.re ⟪T x, x⟫ := by
  refine ⟨fun h x hx ↦ ?_, fun h w hw ↦ by simpa using h (w 0) (hw.ne_zero 0)⟩
  obtain ⟨w, hw, hscale⟩ := exists_orthonormal_re_inner_eq (T := T) hx
  rw [hscale]
  exact mul_pos (by positivity) (by simpa using h w hw)

/-- A positive operator is `k`-nonnegative for every `k`. -/
theorem IsPositive.isKNonneg (hT : T.IsPositive) (k : ℕ) : T.IsKNonneg k :=
  fun _ _ ↦ sum_nonneg fun _ _ ↦ hT.re_inner_nonneg_left _

/-- An operator is positive exactly when it is symmetric and `1`-nonnegative. -/
theorem isPositive_iff_isSymmetric_and_isKNonneg_one :
    T.IsPositive ↔ T.IsSymmetric ∧ T.IsKNonneg 1 := by
  rw [isKNonneg_one_iff, IsPositive]

/-- A `k`-nonnegative operator with `k ≠ 0` is `(k + 1)`-nonnegative. -/
theorem IsKNonneg.succ (h : T.IsKNonneg k) (hk : k ≠ 0) : T.IsKNonneg (k + 1) := by
  intro w hw
  -- Average over the `k + 1` ways to drop one vector from the orthonormal family `w`.
  have hsum := Fin.sum_sum_succAbove (k := k) fun i ↦ RCLike.re ⟪T (w i), w i⟫
  rw [nsmul_eq_mul] at hsum
  have hk' : (0 : ℝ) < k := by positivity
  have : 0 ≤ (k : ℝ) * ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
    hsum ▸ sum_nonneg fun j _ ↦ h _ (hw.comp _ (Fin.succAbove_right_injective (p := j)))
  exact (mul_nonneg_iff_of_pos_left hk').1 this

/-- `k`-nonnegativity implies `m`-nonnegativity for `1 ≤ k ≤ m`. -/
theorem IsKNonneg.mono (h : T.IsKNonneg k) (hk : k ≠ 0) (hkm : k ≤ m) : T.IsKNonneg m := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m hkm ih => exact ih.succ (by omega)

/-- A `k`-positive operator is `(k + 1)`-positive. -/
theorem IsKPos.succ (h : T.IsKPos k) : T.IsKPos (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd h (not_isKPos_zero_right T)
  intro w hw
  have hsum := Fin.sum_sum_succAbove (k := k) fun i ↦ RCLike.re ⟪T (w i), w i⟫
  rw [nsmul_eq_mul] at hsum
  have : 0 < (k : ℝ) * ∑ i, RCLike.re ⟪T (w i), w i⟫ :=
    hsum ▸ sum_pos (fun j _ ↦ h _ (hw.comp _ (Fin.succAbove_right_injective (p := j))))
      univ_nonempty
  exact pos_of_mul_pos_right this (by positivity)

/-- `k`-positivity implies `m`-positivity for `k ≤ m`. -/
theorem IsKPos.mono (h : T.IsKPos k) (hkm : k ≤ m) : T.IsKPos m := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih.succ

/-! ### The cone of `k`-nonnegative operators -/

/-- The zero operator is `k`-nonnegative. -/
@[simp]
protected theorem IsKNonneg.zero (k : ℕ) : (0 : E →ₗ[𝕜] E).IsKNonneg k :=
  fun _ _ ↦ by simp

/-- The sum of two `k`-nonnegative operators is `k`-nonnegative. -/
protected theorem IsKNonneg.add (hT : T.IsKNonneg k) (hS : S.IsKNonneg k) : (T + S).IsKNonneg k :=
  fun w hw ↦ by simpa [inner_add_left, sum_add_distrib] using add_nonneg (hT w hw) (hS w hw)

/-- The sum of a `k`-positive and a `k`-nonnegative operator is `k`-positive. -/
theorem IsKPos.add_isKNonneg (hT : T.IsKPos k) (hS : S.IsKNonneg k) : (T + S).IsKPos k :=
  fun w hw ↦ by
    simpa [inner_add_left, sum_add_distrib] using add_pos_of_pos_of_nonneg (hT w hw) (hS w hw)

/-- The sum of two `k`-positive operators is `k`-positive. -/
protected theorem IsKPos.add (hT : T.IsKPos k) (hS : S.IsKPos k) : (T + S).IsKPos k :=
  hT.add_isKNonneg hS.isKNonneg

/-- A nonnegative real multiple of a `k`-nonnegative operator is `k`-nonnegative. -/
theorem IsKNonneg.smul (hT : T.IsKNonneg k) {c : ℝ} (hc : 0 ≤ c) : ((c : 𝕜) • T).IsKNonneg k :=
  fun w hw ↦ by simpa [inner_smul_left, ← mul_sum] using mul_nonneg hc (hT w hw)

/-- A positive real multiple of a `k`-positive operator is `k`-positive. -/
theorem IsKPos.smul (hT : T.IsKPos k) {c : ℝ} (hc : 0 < c) : ((c : 𝕜) • T).IsKPos k :=
  fun w hw ↦ by simpa [inner_smul_left, ← mul_sum] using mul_pos hc (hT w hw)

/-- Conjugating by a linear isometry equivalence preserves `k`-nonnegativity. -/
@[simp]
theorem isKNonneg_conj_iff (U : E ≃ₗᵢ[𝕜] F) :
    (U.toLinearEquiv.conj T).IsKNonneg k ↔ T.IsKNonneg k :=
  U.forall_orthonormal_conj_iff (0 ≤ ·)

/-- Conjugating by a linear isometry equivalence preserves `k`-positivity. -/
@[simp]
theorem isKPos_conj_iff (U : E ≃ₗᵢ[𝕜] F) :
    (U.toLinearEquiv.conj T).IsKPos k ↔ T.IsKPos k :=
  U.forall_orthonormal_conj_iff (0 < ·)

/-! ### Traces of compressions -/

/-- `T` is `k`-nonnegative exactly when its compression to every `k`-dimensional subspace has
trace with nonnegative real part. -/
theorem isKNonneg_iff_forall_re_trace_nonneg :
    T.IsKNonneg k ↔ ∀ (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W], finrank 𝕜 W = k →
      0 ≤ RCLike.re (trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype)) :=
  T.forall_orthonormal_iff_forall_re_trace (0 ≤ ·)

/-- `T` is `k`-positive exactly when its compression to every `k`-dimensional subspace has trace
with positive real part. -/
theorem isKPos_iff_forall_re_trace_pos :
    T.IsKPos k ↔ ∀ (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W], finrank 𝕜 W = k →
      0 < RCLike.re (trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype)) :=
  T.forall_orthonormal_iff_forall_re_trace (0 < ·)

/-! ### Eigenvalues -/

namespace IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ}

/-- A symmetric operator on an `n`-dimensional space is `k`-nonnegative, for `k ≤ n`, exactly
when the sum `λₙ₋₁ + ⋯ + λₙ₋ₖ` of its `k` smallest eigenvalues is nonnegative. -/
theorem isKNonneg_iff_sum_eigenvalues_rev_nonneg (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (hk : k ≤ n) :
    T.IsKNonneg k ↔
      0 ≤ ∑ j ∈ univ.filter fun j : Fin n ↦ (j : ℕ) < k, hT.eigenvalues hn j.rev := by
  obtain ⟨⟨w, hw, hsum⟩, hle⟩ := hT.isLeast_sum_re_inner_apply_self hn hk
  exact ⟨fun h ↦ hsum ▸ h w hw, fun h w' hw' ↦ h.trans (hle ⟨w', hw', rfl⟩)⟩

/-- A symmetric operator on an `n`-dimensional space is `k`-positive, for `k ≤ n`, exactly when
the sum `λₙ₋₁ + ⋯ + λₙ₋ₖ` of its `k` smallest eigenvalues is positive. -/
theorem isKPos_iff_sum_eigenvalues_rev_pos (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (hk : k ≤ n) :
    T.IsKPos k ↔
      0 < ∑ j ∈ univ.filter fun j : Fin n ↦ (j : ℕ) < k, hT.eigenvalues hn j.rev := by
  obtain ⟨⟨w, hw, hsum⟩, hle⟩ := hT.isLeast_sum_re_inner_apply_self hn hk
  exact ⟨fun h ↦ hsum ▸ h w hw, fun h w' hw' ↦ h.trans_le (hle ⟨w', hw', rfl⟩)⟩

/-- A symmetric operator on a space of dimension `n ≥ 2` is `2`-nonnegative exactly when the sum
`λₙ₋₁ + λₙ₋₂` of its two smallest eigenvalues is nonnegative. -/
theorem isKNonneg_two_iff_eigenvalues_add_eigenvalues_nonneg (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (h2 : 2 ≤ n) :
    T.IsKNonneg 2 ↔
      0 ≤ hT.eigenvalues hn ⟨n - 1, by omega⟩ + hT.eigenvalues hn ⟨n - 2, by omega⟩ := by
  rw [hT.isKNonneg_iff_sum_eigenvalues_rev_nonneg hn h2, ← TauCeti.prefixSum_def,
    TauCeti.prefixSum_two_rev h2]

/-- A symmetric operator on a space of dimension `n ≥ 2` is `2`-positive exactly when the sum
`λₙ₋₁ + λₙ₋₂` of its two smallest eigenvalues is positive. -/
theorem isKPos_two_iff_eigenvalues_add_eigenvalues_pos (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (h2 : 2 ≤ n) :
    T.IsKPos 2 ↔
      0 < hT.eigenvalues hn ⟨n - 1, by omega⟩ + hT.eigenvalues hn ⟨n - 2, by omega⟩ := by
  rw [hT.isKPos_iff_sum_eigenvalues_rev_pos hn h2, ← TauCeti.prefixSum_def,
    TauCeti.prefixSum_two_rev h2]

end IsSymmetric

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The `k`-nonnegative bounded operators form a closed subset of `E →L[𝕜] E`. -/
theorem isClosed_setOf_isKNonneg (k : ℕ) :
    IsClosed {T : E →L[𝕜] E | (T : E →ₗ[𝕜] E).IsKNonneg k} := by
  simp only [LinearMap.IsKNonneg, coe_coe, Set.ofPred_forall]
  exact isClosed_iInter fun w ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const (by fun_prop)

end ContinuousLinearMap
