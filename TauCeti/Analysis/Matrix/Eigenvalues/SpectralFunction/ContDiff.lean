/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralFunction.Basic
import TauCeti.Analysis.Calculus.FDeriv.Matrix
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.Frobenius

/-!
# Spectral functions of `C¹` functions are `C¹`

For a symmetric function `f : ℝⁿ → ℝ` and an open set `Ω ⊆ ℝⁿ` invariant under permutations of
the coordinates, the spectral function `A ↦ f(λ(A))` on the real vector space of Hermitian
matrices is `C¹` on `{A | λ(A) ∈ Ω}` if and only if `f` is `C¹` on `Ω`
(`Matrix.contDiffOn_spectralFunction_iff`; Lewis 1996, the remark after Corollary 3.15). Here
`λ(A)` is the decreasingly sorted eigenvalue vector and the matrices carry the Frobenius norm.

## The continuity of the gradient

The gradient of the spectral function at `A` is `U diag(∇f(λ(A))) U*` for a unitary `U`
diagonalizing `A` (`Matrix.fderiv_spectralFunction_selfAdjoint_apply`, Lewis 1996, Theorem 1.1),
and `U` does not depend continuously on `A`. Near `A₀` the gradient is compared with that of
`g(A) = ∑ⱼ yⱼ λⱼ(A)` for the fixed weights `yⱼ = ∂ⱼ f(λ(A₀))`. These are constant on the
eigenvalue clusters of `A₀`, so by summation by parts `g` is a combination of the Ky Fan sums
`λ₀ + ⋯ + λₖ₋₁` at the spectral gaps of `A₀`
(`Matrix.IsHermitian.eigenvalues₀_lt_of_extend_sub_ne_zero`). The derivative of a Ky Fan sum is
continuous at a spectral gap, by convexity (`Matrix.continuousAt_fderiv_prefixSum_eigenvalues₀`).
The difference of the two gradients is `∑ⱼ (∂ⱼ f(λ(A)) - yⱼ) Re ⟪uⱼ, · uⱼ⟫`, which tends to zero
with `A - A₀`, by the continuity of `∇f` and of `λ`.

## Main results

* `Matrix.contDiffAt_spectralFunction`: the spectral function is `C¹` at `A` when `f` is `C¹`
  at `λ(A)`.
* `Matrix.contDiffOn_spectralFunction_iff`: the `C¹` form of Lewis's theorem.

## References

* A. S. Lewis, *Derivatives of spectral functions*, Math. Oper. Res. **21** (1996), 576–588,
  the remark after Corollary 3.15 (the `C¹` statement) and Theorem 1.1 (the gradient formula).
-/

public section

noncomputable section

open Filter Topology Finset TauCeti Set
open scoped Matrix.Norms.Frobenius

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  {f : (Fin (Fintype.card ι) → ℝ) → ℝ}

/-- **The gradient estimate.** At a Hermitian matrix `B` where `f` is differentiable at `λ(B)`
and which has a spectral gap at every index where the weights `y`, extended by zero, jump, the
derivative of the spectral function in a direction `H` differs from the combination
`∑ₖ (yₖ - yₖ₊₁) D κₖ₊₁(B) H` of Ky Fan derivatives by at most `‖H‖ ∑ⱼ |∂ⱼ f(λ(B)) - yⱼ|`. -/
private theorem abs_fderiv_spectralFunction_sub_le
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)}
    (hBd : DifferentiableAt ℝ f B.property.isHermitian.eigenvalues₀)
    (y : Fin (Fintype.card ι) → ℝ)
    (hBg : ∀ k : Fin (Fintype.card ι),
      Function.extend Fin.val y 0 k - Function.extend Fin.val y 0 (k + 1) ≠ 0 →
      ∀ i j : Fin (Fintype.card ι), i.val < k + 1 → k + 1 ≤ j.val →
        B.property.isHermitian.eigenvalues₀ j < B.property.isHermitian.eigenvalues₀ i)
    (H : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    |fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        f B.property.isHermitian.eigenvalues₀) B H -
      ∑ k : Fin (Fintype.card ι),
        (Function.extend Fin.val y 0 k - Function.extend Fin.val y 0 (k + 1)) *
        fderiv ℝ (fun B' : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
          prefixSum (k + 1) B'.property.isHermitian.eigenvalues₀) B H| ≤
      ‖H‖ * ∑ j, |fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) - y j| := by
  set Y : ℕ → ℝ := Function.extend Fin.val y 0
  obtain ⟨u, hu⟩ := B.property.isHermitian.exists_orthonormalBasis_mulVec_eq_eigenvalues₀_smul
  set q : Fin (Fintype.card ι) → ℝ :=
    fun j ↦ RCLike.re (star ⇑(u j) ⬝ᵥ ((H : Matrix ι ι 𝕜) *ᵥ ⇑(u j)))
  have hF := fderiv_spectralFunction_selfAdjoint_apply hf B hBd u hu H
  -- Summation by parts identifies the Ky Fan combination with `∑ⱼ yⱼ Re ⟪uⱼ, H uⱼ⟫`.
  have hgB : ∑ k : Fin (Fintype.card ι), (Y k - Y (k + 1)) *
      fderiv ℝ (fun B' : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        prefixSum (k + 1) B'.property.isHermitian.eigenvalues₀) B H = ∑ j, y j * q j := by
    have h₁ : ∑ k : Fin (Fintype.card ι), (Y k - Y (k + 1)) *
        fderiv ℝ (fun B' : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
          prefixSum (k + 1) B'.property.isHermitian.eigenvalues₀) B H =
        ∑ k : Fin (Fintype.card ι), (Y k - Y (k + 1)) * prefixSum (k + 1) q := by
      refine sum_congr rfl fun k _ ↦ ?_
      by_cases hc : Y k - Y (k + 1) = 0
      · simp [hc]
      · rw [prefixSum_def]
        exact congrArg _
          (fderiv_prefixSum_eigenvalues₀_selfAdjoint_apply (by omega) (hBg k hc) u hu H)
    rw [h₁]
    exact (sum_smul_by_parts_prefixSum_extend y q).symm
  have hq (j : Fin (Fintype.card ι)) : |q j| ≤ ‖H‖ :=
    (RCLike.abs_re_le_norm _).trans <| (norm_star_dotProduct_mulVec_le _ _ _).trans_eq <| by
      rw [WithLp.toLp_ofLp, u.orthonormal.1 j, one_mul, mul_one, Submodule.norm_coe]
  rw [hgB, show fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀) B H - ∑ j, y j * q j =
      ∑ j, (fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) * q j - y j * q j) by
    rw [sum_sub_distrib]
    exact congrArg (· - ∑ j, y j * q j) hF]
  calc _ ≤ ∑ j, |fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) - y j| * ‖H‖ := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hq j) (abs_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

/-- **Continuity of the gradient of a spectral function.** If `f` is symmetric, differentiable
near `λ(A)` and its derivative is continuous at `λ(A)`, the derivative of `B ↦ f(λ(B))` is
continuous at `A`. -/
private theorem continuousAt_fderiv_spectralFunction
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)}
    (hfd : ∀ᶠ μ in 𝓝 A.property.isHermitian.eigenvalues₀, DifferentiableAt ℝ f μ)
    (hfc : ContinuousAt (fderiv ℝ f) A.property.isHermitian.eigenvalues₀) :
    ContinuousAt (fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀)) A := by
  set y : Fin (Fintype.card ι) → ℝ :=
    fun j ↦ fderiv ℝ f A.property.isHermitian.eigenvalues₀ (Pi.single j 1)
  set Y : ℕ → ℝ := Function.extend Fin.val y 0
  -- The weights are constant on the eigenvalue clusters of `A`, so they jump only at its gaps.
  have hgap {k : Fin (Fintype.card ι)} (hc : Y k - Y (k + 1) ≠ 0) :=
    A.property.isHermitian.eigenvalues₀_lt_of_extend_sub_ne_zero
      (fun i j hij ↦ fderiv_apply_single_eq_of_comp_swap (fun μ ↦ hf _ μ) hij 1) hc
  have heig : ContinuousAt (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      B.property.isHermitian.eigenvalues₀) A := continuous_eigenvalues₀_selfAdjoint.continuousAt
  -- Near `A`, `f` is differentiable at `λ(B)` and the spectral gaps of `A` persist.
  have hev : ∀ᶠ B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) in 𝓝 A,
      DifferentiableAt ℝ f B.property.isHermitian.eigenvalues₀ ∧
      ∀ k : Fin (Fintype.card ι), Y k - Y (k + 1) ≠ 0 →
        ∀ i j : Fin (Fintype.card ι), i.val < k + 1 → k + 1 ≤ j.val →
          B.property.isHermitian.eigenvalues₀ j < B.property.isHermitian.eigenvalues₀ i := by
    refine (heig.eventually hfd).and (eventually_all.2 fun k ↦ ?_)
    by_cases hc : Y k - Y (k + 1) = 0
    · exact Eventually.of_forall fun _ h ↦ absurd hc h
    · exact (eventually_eigenvalues₀_lt
        (M := fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜))
        (fun B ↦ B.property.isHermitian)
        (fun a b ↦ (hasFDerivAt_selfAdjoint_apply a b A).continuousAt) (hgap hc)).mono
        fun _ hB _ ↦ hB
  refine continuousAt_clm_apply.2 fun H ↦ ?_
  set F : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) → ℝ := fun B ↦ fderiv ℝ
    (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ f B.property.isHermitian.eigenvalues₀) B H
  -- The comparison function `g(B) = ∑ₖ (Yₖ - Yₖ₊₁) D κₖ₊₁(B) H`, continuous at `A`.
  set g : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) → ℝ := fun B ↦
    ∑ k : Fin (Fintype.card ι), (Y k - Y (k + 1)) * fderiv ℝ (fun B' : selfAdjoint.submodule ℝ
      (Matrix ι ι 𝕜) ↦ prefixSum (k + 1) B'.property.isHermitian.eigenvalues₀) B H
  have hg : ContinuousAt g A := by
    refine tendsto_finsetSum _ fun k _ ↦ ?_
    by_cases hc : Y k - Y (k + 1) = 0
    · simpa only [hc, zero_mul] using tendsto_const_nhds
    · exact (continuousAt_clm_apply.1 (continuousAt_fderiv_prefixSum_eigenvalues₀ (k := k + 1)
        (by omega) (hgap hc)) H).const_mul _
  -- `F - g` is bounded by `b`, which tends to zero by the continuity of `∇f` and of `λ`.
  set b : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) → ℝ := fun B ↦
    ‖H‖ * ∑ j, |fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) - y j|
  have hest : ∀ᶠ B in 𝓝 A, |F B - g B| ≤ b B :=
    hev.mono fun B hB ↦ abs_fderiv_spectralFunction_sub_le hf hB.1 y hB.2 H
  have hb0 : b A = 0 := by simp only [b, y, sub_self, abs_zero, sum_const_zero, mul_zero]
  have hb : Tendsto b (𝓝 A) (𝓝 (b A)) := (tendsto_finsetSum _ fun j _ ↦
    ((continuousAt_clm_apply.1 (hfc.comp heig) (Pi.single j 1)).sub continuousAt_const).abs)
      |>.const_mul _
  rw [hb0] at hb
  have hA : F A = g A := sub_eq_zero.1 (abs_nonpos_iff.1 (hb0 ▸ hest.self_of_nhds))
  have h := (squeeze_zero_norm' (hest.mono fun B hB ↦ by rwa [Real.norm_eq_abs]) hb).add hg.tendsto
  simp only [sub_add_cancel, zero_add, ← hA] at h
  exact h

/-- **Spectral functions of `C¹` functions are `C¹`** (Lewis 1996, the remark after
Corollary 3.15). If `f` is symmetric and `C¹` at the sorted eigenvalue vector `λ(A)`, the spectral
function `B ↦ f(λ(B))` on the real vector space of Hermitian matrices is `C¹` at `A`. -/
theorem contDiffAt_spectralFunction
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)}
    (hfA : ContDiffAt ℝ 1 f A.property.isHermitian.eigenvalues₀) :
    ContDiffAt ℝ 1 (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀) A := by
  have hev : ∀ᶠ B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) in 𝓝 A,
      ContDiffAt ℝ 1 f B.property.isHermitian.eigenvalues₀ :=
    continuous_eigenvalues₀_selfAdjoint.continuousAt.eventually (hfA.eventually (by simp))
  rw [contDiffAt_one_iff]
  refine ⟨fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
    f B.property.isHermitian.eigenvalues₀), _, hev, fun B hB ↦ ?_, fun B hB ↦ ?_⟩
  · exact (continuousAt_fderiv_spectralFunction hf
      ((hB.eventually (by simp)).mono fun μ hμ ↦ hμ.differentiableAt one_ne_zero)
      (hB.fderiv_right (m := 0) le_rfl).continuousAt).continuousWithinAt
  · exact ((differentiableAt_spectralFunction_iff hf B).2
      (hB.differentiableAt one_ne_zero)).hasFDerivAt

/-- **Lewis's `C¹` theorem.** For a symmetric function `f` and an open set `Ω` invariant under
permutations of the coordinates, the spectral function `A ↦ f(λ(A))` is `C¹` on the Hermitian
matrices `A` with `λ(A) ∈ Ω` if and only if `f` is `C¹` on `Ω`. -/
theorem contDiffOn_spectralFunction_iff
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {Ω : Set (Fin (Fintype.card ι) → ℝ)} (hΩ : IsOpen Ω)
    (hΩσ : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ ∈ Ω, μ ∘ σ ∈ Ω) :
    ContDiffOn ℝ 1 (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀)
      {B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) | B.property.isHermitian.eigenvalues₀ ∈ Ω} ↔
      ContDiffOn ℝ 1 f Ω := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- `f` is the spectral function along the linear map `μ ↦ diag(μ)`.
    set Φ := conjDiagonalSelfAdjoint (1 : Matrix ι ι 𝕜)
    -- The sorted eigenvalues of `diag(μ)` are a rearrangement of `μ`.
    have hΦ (μ : Fin (Fintype.card ι) → ℝ) :
        (Φ μ).property.isHermitian.eigenvalues₀ = μ ∘ Tuple.sortDesc μ :=
      eigenvalues₀_conjDiagonalSelfAdjoint (one_mem _) μ
    have hmaps : MapsTo Φ Ω
        {B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) | B.property.isHermitian.eigenvalues₀ ∈ Ω} :=
      fun μ hμ ↦ by
        rw [mem_ofPred_eq, hΦ]
        exact hΩσ _ μ hμ
    exact (h.comp (LinearMap.toContinuousLinearMap Φ).contDiff.contDiffOn hmaps).congr
      fun μ _ ↦ ((congrArg f (hΦ μ)).trans (hf _ μ)).symm
  · exact (isOpen_setOf_eigenvalues₀_mem hΩ).contDiffOn_iff.2 fun B hB ↦
      contDiffAt_spectralFunction hf ((h _ hB).contDiffAt (hΩ.mem_nhds hB))

end Matrix
