/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.InnerProductSpace.Spectral.KyFanGap
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Matrix.Eigenvalues.Smooth
import TauCeti.Analysis.Matrix.EntrywiseOpNorm

/-!
# Ky Fan sums of Hermitian matrices are differentiable at a spectral gap

Let `M` be a family of Hermitian matrices over `RCLike 𝕜`, parametrized by a real normed space
`E`, whose entries are differentiable at `x₀`. Write `λ₀ ≥ λ₁ ≥ ⋯` for the ordered eigenvalues
`Matrix.IsHermitian.eigenvalues₀`. If the `k` largest eigenvalues of `M x₀` are separated from the
others, `λⱼ < λᵢ` for `i < k ≤ j`, then the Ky Fan sum `x ↦ λ₀(M x) + ⋯ + λₖ₋₁(M x)` is
differentiable at `x₀`, with derivative

`v ↦ ∑_{j < k} Re ⟪uⱼ, (DM (x₀) v) uⱼ⟫`

for every orthonormal eigenbasis `(uⱼ)` of `M x₀` ordered as its eigenvalues
(`Matrix.hasFDerivAt_prefixSum_eigenvalues₀`). The derivative is the trace of `DM (x₀) v` against
the spectral projection of `M x₀` onto its `k` leading eigenvectors (Lewis 1996, Theorem 2.1). For
`k = 1` it is Hadamard's first variation formula for a simple top eigenvalue
(`Matrix.hasFDerivAt_eigenvalues₀`), but the leading eigenvalues may now be repeated among
themselves. Without a gap the Ky Fan sum need not be differentiable: for `M t = diagonal ![t, -t]`
the top eigenvalue is `|t|`.

The proof applies the quadratic expansion of Ky Fan sums at a spectral gap
(`LinearMap.IsSymmetric.abs_prefixSum_eigenvalues_sub_le`) to the Euclidean operators of `M x` and
`M x₀`. The operator norm of `M x - M x₀` is bounded by a multiple of the sum of the absolute
values of its entries (`Matrix.norm_toEuclideanLin_le_of_entry_le_square`), which is
`O(‖x - x₀‖)`, so the remainder is `O(‖x - x₀‖²)`.

## Main results

* `Matrix.hasFDerivAt_prefixSum_eigenvalues₀`: the derivative of a Ky Fan sum at a spectral gap.
* `Matrix.fderiv_prefixSum_eigenvalues₀_apply`: its value in a direction `v`.

## References

* A. S. Lewis, *Derivatives of spectral functions*, Math. Oper. Res. **21** (1996), 576–588,
  Theorem 2.1.
-/

public section

noncomputable section

open Filter Topology Asymptotics Finset TauCeti

namespace Matrix

variable {𝕜 n E : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {M : E → Matrix n n 𝕜} {x₀ : E}

/-- The quadratic expansion of a Ky Fan sum at a spectral gap, for Hermitian matrices `A` and `B`:
the remainder is at most `k (card n)² / δ` times the square of the sum of the absolute values of the
entries of `B - A`. -/
private theorem abs_prefixSum_eigenvalues₀_sub_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {k : ℕ} (hkn : k ≤ Fintype.card n) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j : Fin (Fintype.card n), i.val < k → k ≤ j.val →
      hA.eigenvalues₀ j + δ ≤ hA.eigenvalues₀ i)
    (u : OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n))
    (hu : ∀ j, A *ᵥ u j = (hA.eigenvalues₀ j : 𝕜) • ⇑(u j)) :
    |prefixSum k hB.eigenvalues₀ - prefixSum k hA.eigenvalues₀ -
        (RCLike.re (∑ j : Fin (Fintype.card n) with j.val < k, ∑ a, ∑ b,
          star (u j a) * u j b * B a b) -
        RCLike.re (∑ j : Fin (Fintype.card n) with j.val < k, ∑ a, ∑ b,
          star (u j a) * u j b * A a b))| ≤
      k * Fintype.card n ^ 2 / δ * (∑ a, ∑ b, ‖B a b - A a b‖) ^ 2 := by
  have hS := isSymmetric_toEuclideanLin_iff.mpr hB
  -- The ordered eigenvalues of `B` are those of its Euclidean operator.
  have heig : hB.eigenvalues₀ = hS.eigenvalues finrank_euclideanSpace := by
    rw [IsHermitian.eigenvalues₀]
  have hb (j : Fin (Fintype.card n)) :
      toEuclideanLin A (u j) = (hA.eigenvalues₀ j : 𝕜) • u j := by
    rw [toLpLin_apply, hu j, WithLp.toLp_smul, WithLp.toLp_ofLp]
  -- The operator norm of `B - A` is bounded by the sum of the absolute values of its entries.
  have hC (y : EuclideanSpace 𝕜 n) : ‖(toEuclideanLin B - toEuclideanLin A) y‖ ≤
      (Fintype.card n * ∑ a, ∑ b, ‖B a b - A a b‖) * ‖y‖ := by
    rw [← map_sub]
    refine norm_toEuclideanLin_le_of_entry_le_square (fun a b ↦ ?_) y
    rw [Matrix.sub_apply]
    exact (single_le_sum (f := fun b ↦ ‖B a b - A a b‖) (fun _ _ ↦ norm_nonneg _)
      (mem_univ b)).trans (single_le_sum (f := fun a ↦ ∑ b, ‖B a b - A a b‖)
        (fun _ _ ↦ sum_nonneg fun _ _ ↦ norm_nonneg _) (mem_univ a))
  have h := hS.abs_prefixSum_eigenvalues_sub_le finrank_euclideanSpace u hb hkn hδ hgap hC
  have hlin : ∑ j : Fin (Fintype.card n) with j.val < k, RCLike.re (inner 𝕜
      ((toEuclideanLin B - toEuclideanLin A) (u j)) (u j)) =
      RCLike.re (∑ j : Fin (Fintype.card n) with j.val < k, ∑ a, ∑ b,
        star (u j a) * u j b * B a b) -
      RCLike.re (∑ j : Fin (Fintype.card n) with j.val < k, ∑ a, ∑ b,
        star (u j a) * u j b * A a b) := by
    -- The quadratic form of a matrix as a sum over its entries.
    have hquad (D : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) : RCLike.re (inner 𝕜
        (toEuclideanLin D v) v) = RCLike.re (∑ a, ∑ b, star (v a) * v b * D a b) := by
      rw [inner_re_symm, EuclideanSpace.inner_eq_star_dotProduct, toLpLin_apply]
      simp only [dotProduct, mulVec, Pi.star_apply, sum_mul]
      exact congrArg RCLike.re (sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by ring)
    simp only [← map_sub, hquad, ← map_sum, ← sum_sub_distrib, ← mul_sub, Matrix.sub_apply]
  rw [hlin] at h
  rw [heig]
  refine h.trans_eq ?_
  rw [mul_pow]
  ring

/-- **Ky Fan sums of Hermitian matrices are differentiable at a spectral gap.** Let `M` be a family
of Hermitian matrices over a real normed space whose entries are differentiable at `x₀`, and
suppose the ordered eigenvalues of `M x₀` satisfy `λⱼ < λᵢ` whenever `i < k ≤ j`. For an
orthonormal eigenbasis `(uⱼ)` of `M x₀` ordered as its eigenvalues, the sum
`x ↦ λ₀(M x) + ⋯ + λₖ₋₁(M x)` of the `k` largest eigenvalues has derivative
`v ↦ ∑_{j < k} Re ⟪uⱼ, (DM (x₀) v) uⱼ⟫` at `x₀`, written in coordinates as
`Re ∑_{j < k} ∑ a b, conj (uⱼ a) * uⱼ b * DM_{ab} (x₀) v`. -/
theorem hasFDerivAt_prefixSum_eigenvalues₀ (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀) {k : ℕ}
    (hkn : k ≤ Fintype.card n)
    (hgap : ∀ i j : Fin (Fintype.card n), i.val < k → k ≤ j.val →
      (hM x₀).eigenvalues₀ j < (hM x₀).eigenvalues₀ i)
    (u : OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n))
    (hu : ∀ j, M x₀ *ᵥ u j = ((hM x₀).eigenvalues₀ j : 𝕜) • ⇑(u j)) :
    HasFDerivAt (fun x ↦ prefixSum k (hM x).eigenvalues₀)
      (RCLike.reCLM.comp (∑ j : Fin (Fintype.card n) with j.val < k, ∑ a, ∑ b,
        (star (u j a) * u j b) • fderiv ℝ (fun x ↦ M x a b) x₀)) x₀ := by
  -- Finitely many strict inequalities hold with a uniform margin `δ > 0`.
  obtain ⟨δ, hδ, hgapδ⟩ : ∃ δ > 0, ∀ i j : Fin (Fintype.card n), i.val < k → k ≤ j.val →
      (hM x₀).eigenvalues₀ j + δ ≤ (hM x₀).eigenvalues₀ i := by
    set P := univ.filter fun ij : Fin (Fintype.card n) × Fin (Fintype.card n) ↦
      ij.1.val < k ∧ k ≤ ij.2.val
    rcases P.eq_empty_or_nonempty with hP | hP
    · refine ⟨1, one_pos, fun i j hi hj ↦ ?_⟩
      have hmem : (i, j) ∈ P := mem_filter.2 ⟨mem_univ _, hi, hj⟩
      rw [hP] at hmem
      exact absurd hmem (notMem_empty _)
    · obtain ⟨ij, hij, hmin⟩ :=
        P.exists_min_image (fun ij ↦ (hM x₀).eigenvalues₀ ij.1 - (hM x₀).eigenvalues₀ ij.2) hP
      refine ⟨_, sub_pos.2 (hgap _ _ (mem_filter.1 hij).2.1 (mem_filter.1 hij).2.2),
        fun i j hi hj ↦ ?_⟩
      have := hmin (i, j) (mem_filter.2 ⟨mem_univ _, hi, hj⟩)
      simp only at this
      linarith
  -- The linear part.
  set ℓ : E → ℝ := fun x ↦ RCLike.re (∑ j : Fin (Fintype.card n) with j.val < k, ∑ a, ∑ b,
    star (u j a) * u j b * M x a b)
  have hℓd : HasFDerivAt ℓ (RCLike.reCLM.comp (∑ j : Fin (Fintype.card n) with j.val < k,
      ∑ a, ∑ b, (star (u j a) * u j b) • fderiv ℝ (fun x ↦ M x a b) x₀)) x₀ :=
    RCLike.reCLM.hasFDerivAt.comp x₀ (HasFDerivAt.fun_sum fun j _ ↦ HasFDerivAt.fun_sum
      fun a _ ↦ HasFDerivAt.fun_sum fun b _ ↦ (hMd a b).hasFDerivAt.const_mul _)
  -- The remainder is quadratic in the entrywise size `ε` of `M x - M x₀`, which is `O(‖x - x₀‖)`.
  set ε : E → ℝ := fun x ↦ ∑ a, ∑ b, ‖M x a b - M x₀ a b‖
  have hR : HasFDerivAt (fun x ↦ prefixSum k (hM x).eigenvalues₀ - ℓ x) (0 : E →L[ℝ] ℝ) x₀ := by
    refine HasFDerivAt.of_isLittleO ?_
    have hεO : ε =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ :=
      IsBigO.fun_sum fun a _ ↦ IsBigO.fun_sum fun b _ ↦
        (hMd a b).hasFDerivAt.isBigO_sub.norm_left.norm_right
    have hsq : (fun x ↦ ‖x - x₀‖ ^ 2) =o[𝓝 x₀] fun x ↦ x - x₀ :=
      (isLittleO_norm_pow_id (E' := E) one_lt_two).comp_tendsto
        (tendsto_sub_nhds_zero_iff.2 tendsto_id)
    refine (IsBigO.trans ?_ (hεO.pow 2)).trans_isLittleO hsq
    refine IsBigO.of_bound (k * Fintype.card n ^ 2 / δ) (Eventually.of_forall fun x ↦ ?_)
    simp only [zero_apply, sub_zero, Real.norm_eq_abs, norm_pow, sq_abs]
    refine le_of_eq_of_le (congrArg _ ?_)
      (abs_prefixSum_eigenvalues₀_sub_le (hM x₀) (hM x) hkn hδ hgapδ u hu)
    ring
  have hsum := hℓd.add hR
  rw [add_zero] at hsum
  exact hsum.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ (add_sub_cancel _ _).symm)

/-- The derivative of a Ky Fan sum at a spectral gap in the direction `v` is
`∑_{j < k} Re ⟪uⱼ, (DM (x₀) v) uⱼ⟫` for any orthonormal eigenbasis `(uⱼ)` of `M x₀` ordered as its
eigenvalues. -/
theorem fderiv_prefixSum_eigenvalues₀_apply (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀) {k : ℕ}
    (hkn : k ≤ Fintype.card n)
    (hgap : ∀ i j : Fin (Fintype.card n), i.val < k → k ≤ j.val →
      (hM x₀).eigenvalues₀ j < (hM x₀).eigenvalues₀ i)
    (u : OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n))
    (hu : ∀ j, M x₀ *ᵥ u j = ((hM x₀).eigenvalues₀ j : 𝕜) • ⇑(u j)) (v : E) :
    fderiv ℝ (fun x ↦ prefixSum k (hM x).eigenvalues₀) x₀ v =
      ∑ j : Fin (Fintype.card n) with j.val < k,
        RCLike.re (star ⇑(u j) ⬝ᵥ (of (fun a b ↦ fderiv ℝ (fun x ↦ M x a b) x₀ v) *ᵥ ⇑(u j))) := by
  rw [(hasFDerivAt_prefixSum_eigenvalues₀ hM hMd hkn hgap u hu).fderiv,
    ContinuousLinearMap.comp_apply, RCLike.reCLM_apply, _root_.sum_apply, map_sum]
  exact sum_congr rfl fun j _ ↦ congrArg RCLike.re (sum_sum_smul_apply _ _ v)

end Matrix
