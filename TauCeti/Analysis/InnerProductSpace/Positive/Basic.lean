/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Center

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

Scaling a nonzero positive bounded operator preserves positivity iff the scalar is nonnegative
(`ContinuousLinearMap.IsPositive.isPositive_smul_iff`, `ContinuousLinearMap.smul_one_nonneg_iff`),
and left multiplication `a ↦ T * a` preserves the positive cone iff `T` is a nonnegative scalar
multiple of `1` (`ContinuousLinearMap.forall_nonneg_mul_nonneg_iff`).

If `0 ≤ D ≤ C` in the Loewner order then `‖D x‖² ≤ ‖C‖ re ⟪D x, x⟫`
(`ContinuousLinearMap.norm_apply_sq_le_of_nonneg_of_le`), obtained without square roots by
expanding `re ⟪D (c x - D x), c x - D x⟫ ≥ 0` with `c = ‖C‖`. Hence the operator norm is monotone
on positive operators (`ContinuousLinearMap.norm_le_norm_of_nonneg_of_le`), for real as well as
complex scalars. Conjugating a positive operator by a symmetric one keeps it positive
(`ContinuousLinearMap.IsPositive.conj_of_isSymmetric`), with no completeness assumption. Powers
of a positive operator are positive (`ContinuousLinearMap.IsPositive.pow`), and the powers of a
positive contraction `0 ≤ T ≤ 1` decrease (`ContinuousLinearMap.pow_le_pow_of_le_one`), because
`T - T²` is the positive sum `(1 - T) T (1 - T) + T (1 - T) T`. These inequalities drive Vigier's
monotone convergence theorem.

A vector on which the quadratic form of a positive endomorphism vanishes lies in its kernel
(`LinearMap.IsPositive.apply_eq_zero_of_inner_map_self_eq_zero`).
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

/-- A vector on which the quadratic form of a positive operator vanishes is in its kernel. -/
theorem IsPositive.apply_eq_zero_of_inner_map_self_eq_zero {T : E →ₗ[𝕜] E} (hT : T.IsPositive)
    {x : E} (hx : ⟪T x, x⟫_𝕜 = 0) : T x = 0 := by
  -- The real part of `⟪T ·, ·⟫` is a positive semidefinite symmetric real bilinear form, so its
  -- radical consists of the vectors on which it vanishes.
  let _ := NormedSpace.restrictScalars ℝ 𝕜 E
  let B : LinearMap.BilinForm ℝ E := LinearMap.mk₂ ℝ (fun u v ↦ RCLike.re ⟪T u, v⟫_𝕜)
    (fun _ _ _ ↦ by simp only [map_add, inner_add_left])
    (fun c u v ↦ by
      rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) c u, map_smul, inner_smul_left,
        RCLike.conj_ofReal, RCLike.re_ofReal_mul, smul_eq_mul])
    (fun _ _ _ ↦ by simp only [inner_add_right, map_add])
    (fun c u v ↦ by
      rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) c v, inner_smul_right, RCLike.re_ofReal_mul,
        smul_eq_mul])
  have hB : LinearMap.IsSymm B := LinearMap.isSymm_def.mpr fun u v ↦ by
    rw [LinearMap.mk₂_apply, LinearMap.mk₂_apply, RingHom.id_apply, hT.isSymmetric,
      ← inner_conj_symm, RCLike.conj_re]
  have hBx := (B.apply_apply_same_eq_zero_iff hT.re_inner_nonneg_left hB (x := x)).mp
    (by rw [LinearMap.mk₂_apply, hx, map_zero])
  -- Evaluate `B x = 0` at `T x`.
  have : RCLike.re ⟪T x, T x⟫_𝕜 = 0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hBx) (T x)
  rwa [inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at this

end LinearMap

namespace ContinuousLinearMap

open scoped InnerProductSpace InnerProduct ComplexOrder

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Scaling a nonzero positive bounded operator by `α : 𝕜` preserves positivity if and only if
`0 ≤ α`. -/
theorem IsPositive.isPositive_smul_iff {T : E →L[𝕜] E} (hT : T.IsPositive) (hT' : T ≠ 0)
    {α : 𝕜} : (α • T).IsPositive ↔ 0 ≤ α :=
  (isPositive_toLinearMap_iff _).symm.trans <|
    hT.toLinearMap.isPositive_smul_iff (ContinuousLinearMap.coe_injective.ne hT')

/-- On a nontrivial inner product space, `c • 1` is nonnegative in the Loewner order if and only if
`0 ≤ c`. -/
@[simp]
theorem smul_one_nonneg_iff [Nontrivial E] {c : 𝕜} :
    0 ≤ c • (1 : E →L[𝕜] E) ↔ 0 ≤ c := by
  simpa only [nonneg_iff_isPositive] using
    isPositive_one.isPositive_smul_iff (E := E) (𝕜 := 𝕜) one_ne_zero (α := c)

/-- Left multiplication `a ↦ T * a` on `E →L[𝕜] E` preserves the Loewner positive cone if and only
if `T = c • 1` for some nonnegative scalar `c : 𝕜`. -/
theorem forall_nonneg_mul_nonneg_iff {T : E →L[𝕜] E} :
    (∀ a : E →L[𝕜] E, 0 ≤ a → 0 ≤ T * a) ↔ ∃ c : 𝕜, 0 ≤ c ∧ T = c • 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases subsingleton_or_nontrivial E with hE | hE
    · exact ⟨0, le_rfl, Subsingleton.elim _ _⟩
    have hT0 : 0 ≤ T := by
      simpa only [mul_one] using h 1 (nonneg_iff_isPositive.mpr isPositive_one)
    have hT : T.IsPositive := nonneg_iff_isPositive.mp hT0
    have hdep (x : E) : ¬ LinearIndependent 𝕜 ![x, T.toLinearMap x] := by
      rw [LinearIndependent.pair_iff]
      intro hlin
      rcases eq_or_ne x 0 with rfl | hx
      · exact one_ne_zero (hlin 1 0 (by simp)).1
      let P : E →L[𝕜] E := InnerProductSpace.rankOne 𝕜 x x
      have hP : P.IsPositive := InnerProductSpace.isPositive_rankOne_self x
      have hTP : (T * P).IsPositive := nonneg_iff_isPositive.mp (h P (nonneg_iff_isPositive.mpr hP))
      have hcomm : T (P x) = P (T x) := ext_inner_right 𝕜 fun z => by
        calc ⟪T (P x), z⟫_𝕜 = ⟪(T * P) x, z⟫_𝕜 := rfl
          _ = ⟪x, (T * P) z⟫_𝕜 := hTP.isSymmetric x z
          _ = ⟪T x, P z⟫_𝕜 := (hT.isSymmetric x (P z)).symm
          _ = ⟪P (T x), z⟫_𝕜 := (hP.isSymmetric (T x) z).symm
      have hmul : ⟪x, x⟫_𝕜 • T x = ⟪x, T x⟫_𝕜 • x := by
        simpa [P, InnerProductSpace.rankOne_apply, map_smul] using hcomm
      have hcomb : (-⟪x, T x⟫_𝕜) • x + ⟪x, x⟫_𝕜 • T.toLinearMap x = 0 := by
        rw [neg_smul, neg_add_eq_zero]
        exact hmul.symm
      exact (inner_self_ne_zero (𝕜 := 𝕜)).mpr hx (hlin (-⟪x, T x⟫_𝕜) ⟪x, x⟫_𝕜 hcomb).2
    obtain ⟨c, hc⟩ := T.toLinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
    have hT_eq : T = c • 1 := ContinuousLinearMap.coe_injective hc
    exact ⟨c, smul_one_nonneg_iff.mp (hT_eq ▸ hT0), hT_eq⟩
  · rintro ⟨c, hc, rfl⟩ a ha
    rw [smul_mul_assoc, one_mul]
    exact smul_nonneg hc ha

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

/-- Conjugating a positive operator by a symmetric one gives a positive operator. Unlike
Mathlib's `ContinuousLinearMap.IsPositive.conj_adjoint`, this needs no completeness of `E`. -/
@[aesop safe apply]
theorem IsPositive.conj_of_isSymmetric {S A : E →L[𝕜] E} (hA : A.IsPositive)
    (hS : (S : E →ₗ[𝕜] E).IsSymmetric) : (S * A * S).IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · calc ⟪S (A (S x)), y⟫_𝕜 = ⟪A (S x), S y⟫_𝕜 := hS _ _
      _ = ⟪S x, A (S y)⟫_𝕜 := hA.isSymmetric _ _
      _ = ⟪x, S (A (S y))⟫_𝕜 := hS _ _
  · rw [reApplyInnerSelf_apply, _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp]
    rw [show ⟪S (A (S x)), x⟫_𝕜 = ⟪A (S x), S x⟫_𝕜 from hS _ _]
    exact hA.re_inner_nonneg_left (S x)

/-- The powers of a positive operator are symmetric. -/
private theorem isSymmetric_pow {T : E →L[𝕜] E} (hT : T.IsPositive) (k : ℕ) :
    ((T ^ k : E →L[𝕜] E) : E →ₗ[𝕜] E).IsSymmetric :=
  toLinearMap_pow T k ▸ hT.isSymmetric.pow k

/-- The powers of a positive contraction decrease in the Loewner order, one step at a time. -/
private theorem pow_succ_le_pow {T : E →L[𝕜] E} (h0 : 0 ≤ T) (h1 : T ≤ 1) (n : ℕ) :
    T ^ (n + 1) ≤ T ^ n := by
  have hT := nonneg_iff_isPositive.mp h0
  have hsa : (T : E →ₗ[𝕜] E).IsSymmetric := hT.isSymmetric
  have h1' : (1 - T).IsPositive := le_def.mp h1
  rw [le_def]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h : T ^ (2 * k) - T ^ (2 * k + 1) = T ^ k * (1 - T) * T ^ k := by
      rw [mul_sub, sub_mul, mul_one, ← pow_add, pow_mul_mul_pow, two_mul]
    rw [h]
    exact h1'.conj_of_isSymmetric (isSymmetric_pow hT k)
  · -- `T - T² = (1 - T) T (1 - T) + T (1 - T) T` is positive.
    have hTT : (T - T * T).IsPositive := by
      have h : T - T * T = (1 - T) * T * (1 - T) + T * (1 - T) * T := by noncomm_ring
      rw [h]
      exact (hT.conj_of_isSymmetric h1'.isSymmetric).add (h1'.conj_of_isSymmetric hsa)
    have h : T ^ (2 * k + 1) - T ^ (2 * k + 1 + 1) = T ^ k * (T - T * T) * T ^ k := by
      have h2 : T ^ k * (T * T) * T ^ k = T ^ (2 * k + 1 + 1) := by
        rw [← mul_assoc, ← pow_succ, ← pow_succ, ← pow_add]
        congr 1
        ring
      rw [mul_sub, sub_mul, pow_mul_mul_pow, h2]
    rw [h]
    exact hTT.conj_of_isSymmetric (isSymmetric_pow hT k)

/-- The powers of a positive operator are positive. -/
@[aesop safe apply]
theorem IsPositive.pow {T : E →L[𝕜] E} (hT : T.IsPositive) (n : ℕ) : (T ^ n).IsPositive := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simpa [← pow_add, ← two_mul] using isPositive_one.conj_of_isSymmetric (isSymmetric_pow hT k)
  · rw [← pow_mul_mul_pow]
    exact hT.conj_of_isSymmetric (isSymmetric_pow hT k)

/-- The powers of a positive contraction `0 ≤ T ≤ 1` decrease in the Loewner order. -/
theorem pow_le_pow_of_le_one {T : E →L[𝕜] E} (h0 : 0 ≤ T) (h1 : T ≤ 1) {m n : ℕ}
    (hmn : m ≤ n) : T ^ n ≤ T ^ m :=
  antitone_nat_of_succ_le (pow_succ_le_pow h0 h1) hmn

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
