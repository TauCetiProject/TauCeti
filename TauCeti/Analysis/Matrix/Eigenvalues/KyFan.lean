/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.InnerProductSpace.Spectral.KyFanGap
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Algebra.Order.Group.Finite
import TauCeti.Analysis.Calculus.FDeriv.Matrix
import TauCeti.Analysis.Convex.ContinuousFDeriv
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
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

On the real vector space `selfAdjoint.submodule ℝ (Matrix n n 𝕜)` of Hermitian matrices, normed by
the Frobenius norm, Ky Fan sums are convex (`Matrix.convexOn_prefixSum_eigenvalues₀`), by the
operator form `LinearMap.IsSymmetric.prefixSum_eigenvalues_smul_add_smul_le`. A spectral gap
persists nearby (`Matrix.eventually_eigenvalues₀_lt`), so a Ky Fan sum is differentiable near a
spectral gap, and its derivative, being that of a convex function, is continuous there
(`Matrix.continuousAt_fderiv_prefixSum_eigenvalues₀`, from `ConvexOn.continuousAt_fderiv`).

## Main results

* `Matrix.hasFDerivAt_prefixSum_eigenvalues₀`: the derivative of a Ky Fan sum at a spectral gap.
* `Matrix.fderiv_prefixSum_eigenvalues₀_apply`: its value in a direction `v`.
* `Matrix.convexOn_prefixSum_eigenvalues₀`: Ky Fan sums are convex on Hermitian matrices.
* `Matrix.differentiableAt_prefixSum_eigenvalues₀`,
  `Matrix.fderiv_prefixSum_eigenvalues₀_selfAdjoint_apply`: differentiability and derivative of a
  Ky Fan sum at a spectral gap, on Hermitian matrices.
* `Matrix.continuousAt_fderiv_prefixSum_eigenvalues₀`: the derivative of a Ky Fan sum is
  continuous at a spectral gap.

## References

* A. S. Lewis, *Derivatives of spectral functions*, Math. Oper. Res. **21** (1996), 576–588,
  Theorem 2.1.
* K. Fan, *On a theorem of Weyl concerning eigenvalues of linear transformations I*, Proc. Natl.
  Acad. Sci. USA **35** (1949), 652–655, for the convexity of Ky Fan sums.
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
  obtain ⟨δ, hδ, hgapδ⟩ := exists_pos_forall_add_le_of_forall_lt
    (ι := {ij : Fin (Fintype.card n) × Fin (Fintype.card n) // ij.1.val < k ∧ k ≤ ij.2.val})
    (f := fun ij ↦ (hM x₀).eigenvalues₀ ij.val.2) (g := fun ij ↦ (hM x₀).eigenvalues₀ ij.val.1)
    fun ij ↦ hgap _ _ ij.property.1 ij.property.2
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
      (abs_prefixSum_eigenvalues₀_sub_le (hM x₀) (hM x) hkn hδ
        (fun i j hi hj ↦ hgapδ ⟨(i, j), hi, hj⟩) u hu)
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

section SelfAdjoint

open scoped Matrix.Norms.Frobenius

/-- **Ky Fan sums are convex** on the real vector space of Hermitian matrices: the sum of the `k`
largest eigenvalues is a convex function of the matrix. -/
theorem convexOn_prefixSum_eigenvalues₀ (k : ℕ) :
    ConvexOn ℝ Set.univ (fun A : selfAdjoint.submodule ℝ (Matrix n n 𝕜) ↦
      prefixSum k A.property.isHermitian.eigenvalues₀) := by
  refine ⟨convex_univ, fun A _ B _ a b ha hb _ ↦ ?_⟩
  simp only [smul_eq_mul, eigenvalues₀_smul_add_smul]
  exact LinearMap.IsSymmetric.prefixSum_eigenvalues_smul_add_smul_le _ _ _ ha hb k

/-- A Ky Fan sum is differentiable at a Hermitian matrix with a spectral gap after its `k` largest
eigenvalues, on the real vector space of Hermitian matrices. -/
theorem differentiableAt_prefixSum_eigenvalues₀ {A : selfAdjoint.submodule ℝ (Matrix n n 𝕜)}
    {k : ℕ} (hkn : k ≤ Fintype.card n)
    (hgap : ∀ i j : Fin (Fintype.card n), i.val < k → k ≤ j.val →
      A.property.isHermitian.eigenvalues₀ j < A.property.isHermitian.eigenvalues₀ i) :
    DifferentiableAt ℝ (fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) ↦
      prefixSum k B.property.isHermitian.eigenvalues₀) A := by
  obtain ⟨u, hu⟩ := A.property.isHermitian.exists_orthonormalBasis_mulVec_eq_eigenvalues₀_smul
  exact (hasFDerivAt_prefixSum_eigenvalues₀
    (M := fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) ↦ (B : Matrix n n 𝕜))
    (fun B ↦ B.property.isHermitian)
    (fun a b ↦ (hasFDerivAt_selfAdjoint_apply a b A).differentiableAt) hkn hgap u
    hu).differentiableAt

/-- The derivative of a Ky Fan sum at a Hermitian matrix `A` with a spectral gap after its `k`
largest eigenvalues, in the direction `H`, is `∑_{j < k} Re ⟪uⱼ, H uⱼ⟫` for any orthonormal
eigenbasis `(uⱼ)` of `A` ordered as its eigenvalues. -/
theorem fderiv_prefixSum_eigenvalues₀_selfAdjoint_apply
    {A : selfAdjoint.submodule ℝ (Matrix n n 𝕜)} {k : ℕ} (hkn : k ≤ Fintype.card n)
    (hgap : ∀ i j : Fin (Fintype.card n), i.val < k → k ≤ j.val →
      A.property.isHermitian.eigenvalues₀ j < A.property.isHermitian.eigenvalues₀ i)
    (u : OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n))
    (hu : ∀ j, (A : Matrix n n 𝕜) *ᵥ u j = (A.property.isHermitian.eigenvalues₀ j : 𝕜) • ⇑(u j))
    (H : selfAdjoint.submodule ℝ (Matrix n n 𝕜)) :
    fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) ↦
      prefixSum k B.property.isHermitian.eigenvalues₀) A H =
      ∑ j : Fin (Fintype.card n) with j.val < k,
        RCLike.re (star ⇑(u j) ⬝ᵥ ((H : Matrix n n 𝕜) *ᵥ ⇑(u j))) :=
  -- The goal carries the Frobenius-norm topology, which agrees with the entrywise topology of
  -- `Matrix.of_fderiv_selfAdjoint_apply_eq` only after unfolding instances; cast with `▸`.
  of_fderiv_selfAdjoint_apply_eq A H ▸ fderiv_prefixSum_eigenvalues₀_apply
    (M := fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) ↦ (B : Matrix n n 𝕜))
    (fun B ↦ B.property.isHermitian)
    (fun a b ↦ (hasFDerivAt_selfAdjoint_apply a b A).differentiableAt) hkn hgap u hu H

/-- **The derivative of a Ky Fan sum is continuous at a spectral gap.** At a Hermitian matrix with
a spectral gap after its `k` largest eigenvalues, the derivative of the Ky Fan sum is continuous:
the gap persists nearby, where the convex Ky Fan sum is differentiable, so
`ConvexOn.continuousAt_fderiv` applies. -/
theorem continuousAt_fderiv_prefixSum_eigenvalues₀
    {A : selfAdjoint.submodule ℝ (Matrix n n 𝕜)} {k : ℕ} (hkn : k ≤ Fintype.card n)
    (hgap : ∀ i j : Fin (Fintype.card n), i.val < k → k ≤ j.val →
      A.property.isHermitian.eigenvalues₀ j < A.property.isHermitian.eigenvalues₀ i) :
    ContinuousAt (fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) ↦
      prefixSum k B.property.isHermitian.eigenvalues₀)) A := by
  have hd : ∀ᶠ B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) in 𝓝 A,
      DifferentiableAt ℝ (fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) ↦
        prefixSum k B.property.isHermitian.eigenvalues₀) B := by
    filter_upwards [eventually_eigenvalues₀_lt
      (M := fun B : selfAdjoint.submodule ℝ (Matrix n n 𝕜) ↦ (B : Matrix n n 𝕜))
      (fun B ↦ B.property.isHermitian)
      (fun a b ↦ (hasFDerivAt_selfAdjoint_apply a b A).continuousAt) hgap] with B hB
    exact differentiableAt_prefixSum_eigenvalues₀ hkn hB
  -- The implicit arguments are given explicitly: inferring them by unifying with the goal, whose
  -- instances agree only after unfolding, exhausts the heartbeat budget.
  exact (convexOn_prefixSum_eigenvalues₀ (𝕜 := 𝕜) (n := n) k).continuousAt_fderiv (x := A)
    univ_mem hd

end SelfAdjoint

end Matrix
