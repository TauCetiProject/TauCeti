/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Elementary inequalities for positive operators

For a positive operator `T` on a possibly infinite-dimensional Hilbert space, `1 + T` is
invertible (`ContinuousLinearMap.IsPositive.isUnit_one_add`), because
`re ⟪(1 + T) x, x⟫ ≥ ‖x‖²` bounds it below. This applies in particular to `T = X†X`, which makes
`(1 + X†X)⁻¹` available in formulas such as the orthogonal projection onto a graph subspace.

The quadratic form of a positive endomorphism `A` controls its off-diagonal entries,
`2 re ⟪x, A y⟫ ≤ re ⟪x, A x⟫ + re ⟪y, A y⟫`
(`LinearMap.IsPositive.two_mul_re_inner_le`), and on a finite-dimensional space the diagonal
entries along any orthonormal family sum to at most the trace
(`LinearMap.IsPositive.sum_re_inner_le_re_trace`). These are the inputs to Ky Fan's maximum
principle for positive operators.

An operator `D` between real or complex Hilbert spaces satisfies `D D† ≤ 1` in the Loewner
order exactly when it is a contraction (`ContinuousLinearMap.self_comp_adjoint_le_one_iff`), so
the defect operator `1 - D D†` of a contraction is positive.

If `0 ≤ D ≤ C` in the Loewner order then `‖D x‖² ≤ ‖C‖ re ⟪D x, x⟫`
(`ContinuousLinearMap.norm_apply_sq_le_of_nonneg_of_le`), obtained without square roots by
expanding `re ⟪D (c x - D x), c x - D x⟫ ≥ 0` with `c = ‖C‖`. Hence the operator norm is monotone
on positive operators (`ContinuousLinearMap.norm_le_norm_of_nonneg_of_le`), for real as well as
complex scalars. Powers of a positive operator are positive
(`ContinuousLinearMap.IsPositive.pow`), and the powers of a positive contraction `0 ≤ T ≤ 1`
decrease (`ContinuousLinearMap.pow_le_pow_of_le_one`), because `T - T²` is the positive sum
`(1 - T) T (1 - T) + T (1 - T) T`. These inequalities drive Vigier's monotone convergence theorem.
-/

public section

namespace LinearMap

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For a positive endomorphism `A`, `2 re ⟪x, A y⟫ ≤ re ⟪x, A x⟫ + re ⟪y, A y⟫`. -/
theorem IsPositive.two_mul_re_inner_le {A : E →ₗ[𝕜] E} (hA : A.IsPositive) (x y : E) :
    2 * RCLike.re ⟪x, A y⟫_𝕜 ≤ RCLike.re ⟪x, A x⟫_𝕜 + RCLike.re ⟪y, A y⟫_𝕜 := by
  have h := hA.re_inner_nonneg_right (x - y)
  have hsymm : RCLike.re ⟪y, A x⟫_𝕜 = RCLike.re ⟪x, A y⟫_𝕜 := by
    rw [← hA.isSymmetric x y, ← inner_conj_symm, RCLike.conj_re]
  simp only [map_sub, inner_sub_left, inner_sub_right] at h
  linarith

/-- For a positive endomorphism `A` of a finite-dimensional space, the diagonal entries of `A` along
an orthonormal family have real parts summing to at most the real part of the trace. -/
theorem IsPositive.sum_re_inner_le_re_trace [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hA : A.IsPositive) {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) :
    ∑ i, RCLike.re ⟪v i, A (v i)⟫_𝕜 ≤ RCLike.re (A.trace 𝕜 E) := by
  classical
  obtain ⟨u, b, hvu, hb⟩ :=
    (orthonormal_subtype_range hv.linearIndependent.injective).2 hv
      |>.exists_orthonormalBasis_extension
  rw [trace_eq_sum_inner A b, map_sum, hb]
  have hsub : Finset.univ.image v ⊆ u := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hvu ⟨i, rfl⟩
  calc ∑ i, RCLike.re ⟪v i, A (v i)⟫_𝕜
      = ∑ x ∈ Finset.univ.image v, RCLike.re ⟪x, A x⟫_𝕜 := by
        rw [Finset.sum_image fun i _ j _ h ↦ hv.linearIndependent.injective h]
    _ ≤ ∑ x ∈ u, RCLike.re ⟪x, A x⟫_𝕜 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ ↦ hA.re_inner_nonneg_right x
    _ = ∑ x : u, RCLike.re ⟪(x : E), A x⟫_𝕜 := (Finset.sum_coe_sort u _).symm

end LinearMap

namespace ContinuousLinearMap

open scoped InnerProductSpace InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A positive operator dominated by `C` in the Loewner order satisfies
`‖D x‖² ≤ ‖C‖ re ⟪D x, x⟫`. -/
theorem norm_apply_sq_le_of_nonneg_of_le {D C : E →L[𝕜] E} (hD : 0 ≤ D) (hDC : D ≤ C)
    (x : E) : ‖D x‖ ^ 2 ≤ ‖C‖ * RCLike.re ⟪D x, x⟫_𝕜 := by
  have hpos := nonneg_iff_isPositive.mp hD
  have hle : ∀ z, RCLike.re ⟪D z, z⟫_𝕜 ≤ ‖C‖ * ‖z‖ ^ 2 := fun z => by
    have h1 := (le_def.mp hDC).re_inner_nonneg_left z
    have h2 := (re_inner_le_norm (𝕜 := 𝕜) (C z) z).trans
      (mul_le_mul_of_nonneg_right (C.le_opNorm z) (norm_nonneg z))
    simp only [sub_apply, inner_sub_left, map_sub, sub_nonneg] at h1
    nlinarith
  rcases (norm_nonneg C).eq_or_lt with hc | hc
  · have hC : C = 0 := norm_eq_zero.mp hc.symm
    subst hC
    simp [le_antisymm hDC hD]
  · have h1 := hpos.re_inner_nonneg_left ((‖C‖ : 𝕜) • x - D x)
    have h2 := hle (D x)
    have hDD : ⟪D (D x), x⟫_𝕜 = ⟪D x, D x⟫_𝕜 := hpos.isSymmetric (D x) x
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, hDD, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      RCLike.ofReal_re] at h1
    nlinarith

/-- On positive operators the operator norm is monotone for the Loewner order. -/
theorem norm_le_norm_of_nonneg_of_le {D C : E →L[𝕜] E} (hD : 0 ≤ D) (hDC : D ≤ C) :
    ‖D‖ ≤ ‖C‖ := by
  refine opNorm_le_bound _ (norm_nonneg C) fun x => ?_
  rcases (norm_nonneg (D x)).eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · have h := norm_apply_sq_le_of_nonneg_of_le hD hDC x
    have h' := re_inner_le_norm (𝕜 := 𝕜) (D x) x
    refine le_of_mul_le_mul_left ?_ h0
    nlinarith [norm_nonneg C]

/-- Rewrites `T ^ k * T * T ^ k` as a single power. -/
private theorem pow_mul_mul_pow (T : E →L[𝕜] E) (k : ℕ) :
    T ^ k * T * T ^ k = T ^ (2 * k + 1) := by
  rw [← pow_succ, ← pow_add]
  congr 1
  ring

variable [CompleteSpace E]

/-- On a complete space, `1 + T` is invertible for every positive operator `T`, since
`re ⟪(1 + T) x, x⟫ = ‖x‖² + re ⟪T x, x⟫ ≥ ‖x‖²`. For instance `1 + X†X` is invertible, by
`ContinuousLinearMap.isPositive_adjoint_comp_self`. -/
theorem IsPositive.isUnit_one_add {T : E →L[𝕜] E} (hT : T.IsPositive) : IsUnit (1 + T) := by
  refine isUnit_of_forall_le_norm_inner_map _ one_pos fun x => ?_
  rw [NNReal.coe_one, mul_one]
  calc ‖x‖ ^ 2 ≤ RCLike.re ⟪(1 + T) x, x⟫_𝕜 := by
        rw [add_apply, one_apply_eq_self, inner_add_left, map_add, inner_self_eq_norm_sq]
        exact le_add_of_nonneg_right (hT.re_inner_nonneg_left x)
    _ ≤ ‖⟪(1 + T) x, x⟫_𝕜‖ := RCLike.re_le_norm _

/-- Conjugating a positive operator by a self-adjoint one gives a positive operator. -/
private theorem isPositive_mul_mul_of_isSelfAdjoint {S A : E →L[𝕜] E} (hS : IsSelfAdjoint S)
    (hA : A.IsPositive) : (S * A * S).IsPositive := by
  simpa [hS.adjoint_eq, mul_def, comp_assoc] using hA.conj_adjoint S

/-- The powers of a positive contraction decrease in the Loewner order, one step at a time. -/
private theorem pow_succ_le_pow {T : E →L[𝕜] E} (h0 : 0 ≤ T) (h1 : T ≤ 1) (n : ℕ) :
    T ^ (n + 1) ≤ T ^ n := by
  have hT := nonneg_iff_isPositive.mp h0
  have hsa : IsSelfAdjoint T := hT.isSelfAdjoint
  have h1' : (1 - T).IsPositive := le_def.mp h1
  rw [le_def]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h : T ^ (2 * k) - T ^ (2 * k + 1) = T ^ k * (1 - T) * T ^ k := by
      rw [mul_sub, sub_mul, mul_one, ← pow_add, pow_mul_mul_pow, two_mul]
    rw [h]
    exact isPositive_mul_mul_of_isSelfAdjoint (hsa.pow k) h1'
  · -- `T - T² = (1 - T) T (1 - T) + T (1 - T) T` is positive.
    have hTT : (T - T * T).IsPositive := by
      have h : T - T * T = (1 - T) * T * (1 - T) + T * (1 - T) * T := by noncomm_ring
      rw [h]
      exact (isPositive_mul_mul_of_isSelfAdjoint ((IsSelfAdjoint.one _).sub hsa) hT).add
        (isPositive_mul_mul_of_isSelfAdjoint hsa h1')
    have h : T ^ (2 * k + 1) - T ^ (2 * k + 1 + 1) = T ^ k * (T - T * T) * T ^ k := by
      have h2 : T ^ k * (T * T) * T ^ k = T ^ (2 * k + 1 + 1) := by
        rw [← mul_assoc, ← pow_succ, ← pow_succ, ← pow_add]
        congr 1
        ring
      rw [mul_sub, sub_mul, pow_mul_mul_pow, h2]
    rw [h]
    exact isPositive_mul_mul_of_isSelfAdjoint (hsa.pow k) hTT

/-- The powers of a positive operator are positive. -/
theorem IsPositive.pow {T : E →L[𝕜] E} (hT : T.IsPositive) (n : ℕ) : (T ^ n).IsPositive := by
  have hsa : IsSelfAdjoint T := hT.isSelfAdjoint
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [two_mul, pow_add, ← mul_one (T ^ k)]
    simpa using isPositive_mul_mul_of_isSelfAdjoint (hsa.pow k) isPositive_one
  · rw [← pow_mul_mul_pow]
    exact isPositive_mul_mul_of_isSelfAdjoint (hsa.pow k) hT

/-- The powers of a positive contraction `0 ≤ T ≤ 1` decrease in the Loewner order. -/
theorem pow_le_pow_of_le_one {T : E →L[𝕜] E} (h0 : 0 ≤ T) (h1 : T ≤ 1) {m n : ℕ}
    (hmn : m ≤ n) : T ^ n ≤ T ^ m :=
  antitone_nat_of_succ_le (pow_succ_le_pow h0 h1) hmn

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- An operator `D` composed with its adjoint is bounded above by the identity in the Loewner
order exactly when `D` is a contraction, `‖D‖ ≤ 1`; that is, the defect operator `1 - D D†` is
positive exactly for contractions. -/
theorem self_comp_adjoint_le_one_iff (D : F →L[𝕜] E) : D ∘L D.adjoint ≤ 1 ↔ ‖D‖ ≤ 1 := by
  have hsa : IsSelfAdjoint (1 - D ∘L D.adjoint) :=
    (IsSelfAdjoint.one _).sub (isPositive_self_comp_adjoint D).isSelfAdjoint
  have hquad (z : E) :
      (1 - D ∘L D.adjoint).reApplyInnerSelf z = ‖z‖ ^ 2 - ‖D.adjoint z‖ ^ 2 := by
    simp only [reApplyInnerSelf, sub_apply, one_apply_eq_self, inner_sub_left, comp_apply,
      ← D.adjoint_inner_right, map_sub, inner_self_eq_norm_sq]
  rw [le_def, isPositive_def', and_iff_right hsa, ← LinearIsometryEquiv.norm_map adjoint D,
    opNorm_le_iff zero_le_one]
  refine forall_congr' fun z ↦ ?_
  rw [hquad, sub_nonneg, one_mul, pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero]

end ContinuousLinearMap
