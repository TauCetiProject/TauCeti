/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# The squared norm of O'Neill's horizontal tensor

Let `f : M → N` be a Riemannian submersion and let `X_i` be the horizontal lifts at `x` of an
orthonormal basis of `T_(f x) N`. The squared norm of O'Neill's horizontal tensor is
`|A|² = ∑ i j, ‖A_(X_i) X_j‖²` (`IsRiemannianSubmersion.oneillANormSq`). It does not depend on the
horizontal orthonormal frame, vanishes exactly where `A` does, and is bounded on compact sets.
Since `A_X` is skew-adjoint and exchanges horizontal and vertical vectors, also
`∑ i a, ‖A_(X_i) V_a‖² = |A|²` for any orthonormal basis `V_a` of the vertical space `ker (df_x)`.

## Main definitions

* `TauCeti.IsRiemannianSubmersion.oneillANormSq`: the squared norm `|A|²` of O'Neill's horizontal
  tensor.

## Main results

* `TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_sum`: `|A|²` may be computed in any horizontal
  orthonormal frame.
* `TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_zero_iff`: `|A|²` vanishes exactly where `A`
  does.
* `TauCeti.IsRiemannianSubmersion.exists_oneillANormSq_le_of_isCompact`: `|A|²` is bounded on
  compact sets.
* `TauCeti.IsRiemannianSubmersion.sum_sum_norm_oneillA_horizontalLift_vertical`:
  `∑ i a, ‖A_(X_i) V_a‖² = |A|²`.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1 and Theorem 2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C–§D.
-/

public section

open Bundle Manifold
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)
  {ι κ : Type*} [Fintype ι] [Fintype κ]

include h

/-- The squared norm `|A|² = ∑ i j, ‖A_(X_i) X_j‖²` of O'Neill's horizontal tensor at `x`, where
`X_i` are the horizontal lifts of an orthonormal basis of `T_(f x) N`. It does not depend on the
basis (`TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_sum`). -/
def oneillANormSq (x : M) : ℝ :=
  ∑ i, ∑ j, ‖h.oneillA x (h.horizontalLift x (stdOrthonormalBasis ℝ (TangentSpace J (f x)) i))
    (h.horizontalLift x (stdOrthonormalBasis ℝ (TangentSpace J (f x)) j))‖ ^ 2

omit [IsManifold J ∞ N] [IsContMDiffRiemannianBundle J ∞ F fun y : N ↦ TangentSpace J y] in
/-- `|A|²` may be computed in the horizontal lifts of any orthonormal basis of `T_(f x) N`. -/
theorem oneillANormSq_eq_sum (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace J (f x))) :
    h.oneillANormSq x =
      ∑ i, ∑ j, ‖h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j))‖ ^ 2 := by
  simpa only [oneillANormSq, LinearMap.compl₁₂_apply, LinearIsometry.coe_toLinearMap,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using
    LinearMap.sum_sum_norm_apply_apply_sq_eq_sum_sum_norm_apply_apply_sq
      ((h.oneillA x).toLinearMap₁₂.compl₁₂ (h.horizontalLift x).toLinearMap
        (h.horizontalLift x).toLinearMap) (stdOrthonormalBasis ℝ (TangentSpace J (f x))) b

omit [IsManifold J ∞ N] [IsContMDiffRiemannianBundle J ∞ F fun y : N ↦ TangentSpace J y] in
/-- `|A|²` is nonnegative. -/
theorem oneillANormSq_nonneg (x : M) : 0 ≤ h.oneillANormSq x := by
  unfold oneillANormSq
  positivity

/-- `|A|²` vanishes at `x` exactly when O'Neill's horizontal tensor vanishes at `x`. -/
@[simp]
theorem oneillANormSq_eq_zero_iff (x : M) :
    h.oneillANormSq x = 0 ↔ h.oneillA x = 0 := by
  set b := stdOrthonormalBasis ℝ (TangentSpace J (f x))
  rw [h.oneillA_eq_zero_iff_horizontalLift, h.oneillANormSq_eq_sum x b]
  refine ⟨fun h0 u v ↦ ?_, fun h0 ↦ by simp [h0]⟩
  have hij (i j) : h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j)) = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ by positivity).1 h0 i (Finset.mem_univ _)
    simpa using (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ by positivity).1 hi j
      (Finset.mem_univ _)
  exact LinearMap.congr_fun₂ (LinearMap.ext_basis b.toBasis b.toBasis
    (B := (h.oneillA x).toLinearMap₁₂.compl₁₂ (h.horizontalLift x).toLinearMap
      (h.horizontalLift x).toLinearMap) (B' := 0) (by simpa using hij)) u v

/-- `|A|²` is bounded on every compact set. -/
theorem exists_oneillANormSq_le_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ x ∈ K, h.oneillANormSq x ≤ C := by
  obtain ⟨C, -, hC⟩ := h.exists_norm_oneillA_le_of_isCompact hK
  refine ⟨Module.finrank ℝ F ^ 2 * C ^ 2, fun x hx ↦ ?_⟩
  set b := stdOrthonormalBasis ℝ (TangentSpace J (f x))
  have hle (i j) : ‖h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j))‖ ^ 2 ≤
      C ^ 2 := by
    have := hC x hx (h.horizontalLift x (b i)) (h.horizontalLift x (b j))
    simp only [LinearIsometry.norm_map, b.orthonormal.1, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc h.oneillANormSq x ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace J (f x))),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace J (f x))), C ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hle i j
    _ = Module.finrank ℝ F ^ 2 * C ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      -- `TangentSpace J (f x)` is `F` as a real vector space, so the two ranks agree by definition.
      change (Module.finrank ℝ F : ℝ) * ((Module.finrank ℝ F : ℝ) * C ^ 2) = _
      ring

variable {x : M}

/-- In an adapted orthonormal basis, the mixed squared norms of O'Neill's horizontal tensor add up
to `|A|²`: `∑ i a, ‖A_(X_i) V_a‖² = ∑ i j, ‖A_(X_i) X_j‖²`. -/
theorem sum_sum_norm_oneillA_horizontalLift_vertical
    (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) :
    ∑ i, ∑ a, ‖h.oneillA x (h.horizontalLift x (b i)) (c a)‖ ^ 2 = h.oneillANormSq x := by
  rw [h.oneillANormSq_eq_sum x b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  set X := h.horizontalLift x (b i)
  -- `A_X V_a` is horizontal and `A_X X_j` is vertical, and `A_X` is skew-adjoint, so both sides
  -- are `∑ a j, ⟪X_j, A_X V_a⟫²`.
  calc ∑ a, ‖h.oneillA x X (c a)‖ ^ 2
      = ∑ a, ∑ j, ⟪(c a : TangentSpace I x), h.oneillA x X (h.horizontalLift x (b j))⟫_ℝ ^ 2 := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← h.sum_sq_inner_horizontalLift b
          (h.oneillA_apply_mem_orthogonal_ker X (c a).property)]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [real_inner_comm, h.inner_oneillA, neg_sq]
    _ = ∑ j, ‖h.oneillA x X (h.horizontalLift x (b j))‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        exact c.sum_sq_inner_right
          ⟨_, h.oneillA_apply_mem_ker X (h.horizontalLift_mem_orthogonal_ker x (b j))⟩

end TauCeti.IsRiemannianSubmersion
