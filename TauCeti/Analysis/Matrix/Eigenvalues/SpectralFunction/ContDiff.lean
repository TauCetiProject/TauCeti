/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralFunction
import TauCeti.Analysis.Calculus.FDeriv.Matrix
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Convex.ContinuousFDeriv
import TauCeti.Analysis.InnerProductSpace.KyFan
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.Frobenius

/-!
# Spectral functions of `C¹` functions are `C¹`

For a symmetric function `f : ℝⁿ → ℝ` and an open set `Ω ⊆ ℝⁿ` invariant under permutations of
the coordinates, the spectral function `A ↦ f(λ(A))` on the real vector space of Hermitian
matrices is `C¹` on `{A | λ(A) ∈ Ω}` if and only if `f` is `C¹` on `Ω`
(`Matrix.contDiffOn_spectralFunction_iff`; Lewis 1996, the `C¹` clause of Theorem 1.1). Here
`λ(A)` is the decreasingly sorted eigenvalue vector and the matrices carry the Frobenius norm.

## The continuity of the gradient

The gradient of the spectral function at `A` is `U diag(∇f(λ(A))) U*` for a unitary `U`
diagonalizing `A` (`Matrix.fderiv_spectralFunction_selfAdjoint_apply`), and `U` does not depend
continuously on `A`. Near `A₀` the gradient is compared with that of `g(A) = ∑ⱼ yⱼ λⱼ(A)` for the
fixed weights `yⱼ = ∂ⱼ f(λ(A₀))`. These are constant on the eigenvalue clusters of `A₀`, so by
summation by parts `g` is a combination of the Ky Fan sums `λ₀ + ⋯ + λₖ₋₁` at the spectral gaps
of `A₀`. A Ky Fan sum is convex, and differentiable near a spectral gap, so its derivative is
continuous there (`ConvexOn.continuousAt_fderiv`). The difference of the two gradients is
`∑ⱼ (∂ⱼ f(λ(A)) - yⱼ) Re ⟪uⱼ, · uⱼ⟫`, which tends to zero with `A - A₀`, by the continuity of
`∇f` and of `λ`.

## Main results

* `Matrix.convexOn_prefixSum_eigenvalues₀`: Ky Fan sums are convex on Hermitian matrices.
* `Matrix.contDiffAt_spectralFunction`: the spectral function is `C¹` at `A` when `f` is `C¹`
  at `λ(A)`.
* `Matrix.contDiffOn_spectralFunction_iff`: the `C¹` clause of Lewis's theorem.

## References

* A. S. Lewis, *Derivatives of spectral functions*, Math. Oper. Res. **21** (1996), 576–588,
  Theorem 1.1.
-/

public section

noncomputable section

open Filter Topology Finset TauCeti Set
open scoped Matrix.Norms.Frobenius

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- **Ky Fan sums are convex** on the real vector space of Hermitian matrices: the sum of the `k`
largest eigenvalues is a convex function of the matrix. -/
theorem convexOn_prefixSum_eigenvalues₀ (k : ℕ) :
    ConvexOn ℝ univ (fun A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      prefixSum k A.property.isHermitian.eigenvalues₀) := by
  refine ⟨convex_univ, fun A _ B _ a b ha hb _ ↦ ?_⟩
  -- The sorted eigenvalues of a combination of Hermitian matrices are those of the same
  -- combination of their Euclidean operators.
  have key : (a • A + b • B).property.isHermitian.eigenvalues₀ =
      (((isSymmetric_toEuclideanLin_iff.mpr A.property.isHermitian).smul
        (RCLike.conj_ofReal a)).add
        ((isSymmetric_toEuclideanLin_iff.mpr B.property.isHermitian).smul
          (RCLike.conj_ofReal b))).eigenvalues finrank_euclideanSpace := by
    rw [IsHermitian.eigenvalues₀]
    refine LinearMap.IsSymmetric.eigenvalues_congr ?_ _ _ _
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      RCLike.real_smul_eq_coe_smul (K := 𝕜) a, RCLike.real_smul_eq_coe_smul (K := 𝕜) b, map_add,
      map_smul, map_smul]
  simp only [smul_eq_mul, key]
  exact LinearMap.IsSymmetric.prefixSum_eigenvalues_smul_add_smul_le _ _ _ ha hb k

/-- The quadratic form of a matrix at a unit vector is bounded by `n²` times its Frobenius
norm, for `n` the size of the matrix. -/
private theorem norm_star_dotProduct_mulVec_le (H : Matrix ι ι 𝕜) {u : EuclideanSpace 𝕜 ι}
    (hu : ‖u‖ = 1) : ‖star ⇑u ⬝ᵥ (H *ᵥ ⇑u)‖ ≤ Fintype.card ι ^ 2 * ‖H‖ := by
  have hua (a : ι) : ‖u a‖ ≤ 1 := hu ▸ PiLp.norm_apply_le u a
  have hH (a b : ι) : ‖H a b‖ ≤ ‖H‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [frobenius_norm_sq_eq_sum_norm_sq]
    exact (single_le_sum (f := fun j ↦ ‖H a j‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ b)).trans
      (single_le_sum (f := fun i ↦ ∑ j, ‖H i j‖ ^ 2)
        (fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (mem_univ a))
  simp only [dotProduct, mulVec, Pi.star_apply]
  calc ‖∑ a, star (u a) * ∑ b, H a b * u b‖ ≤ ∑ _a : ι, ∑ _b : ι, ‖H‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun a _ ↦ ?_)
        rw [norm_mul, norm_star]
        refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
        rw [mul_sum]
        refine sum_le_sum fun b _ ↦ ?_
        rw [norm_mul]
        calc ‖u a‖ * (‖H a b‖ * ‖u b‖) ≤ 1 * (‖H‖ * 1) := by
              gcongr
              exacts [hua a, hH a b, hua b]
          _ = ‖H‖ := by ring
    _ = Fintype.card ι ^ 2 * ‖H‖ := by simp [sq, mul_assoc]

/-- A Ky Fan sum is differentiable at a Hermitian matrix with a spectral gap after the `k` largest
eigenvalues, with derivative `H ↦ ∑_{j < k} Re ⟪uⱼ, H uⱼ⟫`. -/
private theorem prefixSum_eigenvalues₀_selfAdjoint_fderiv
    {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)} {k : ℕ} (hkn : k ≤ Fintype.card ι)
    (hgap : ∀ i j : Fin (Fintype.card ι), i.val < k → k ≤ j.val →
      A.property.isHermitian.eigenvalues₀ j < A.property.isHermitian.eigenvalues₀ i)
    (u : OrthonormalBasis (Fin (Fintype.card ι)) 𝕜 (EuclideanSpace 𝕜 ι))
    (hu : ∀ j, (A : Matrix ι ι 𝕜) *ᵥ u j = (A.property.isHermitian.eigenvalues₀ j : 𝕜) • ⇑(u j))
    (H : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    DifferentiableAt ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      prefixSum k B.property.isHermitian.eigenvalues₀) A ∧
    fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      prefixSum k B.property.isHermitian.eigenvalues₀) A H =
      ∑ j : Fin (Fintype.card ι) with j.val < k,
        RCLike.re (star ⇑(u j) ⬝ᵥ ((H : Matrix ι ι 𝕜) *ᵥ ⇑(u j))) :=
  -- The matrix of entrywise derivatives in the direction `H` is `H`.
  have hH (A H : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
      (of fun a b ↦ fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        (B : Matrix ι ι 𝕜) a b) A H) = H :=
    ext fun a b ↦ by
      simp only [of_apply, (hasFDerivAt_selfAdjoint_apply a b A).fderiv,
        LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Submodule.coe_subtype,
        Function.comp_apply, entryLinearMap_apply]
  ⟨(hasFDerivAt_prefixSum_eigenvalues₀
      (M := fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜))
      (fun B ↦ B.property.isHermitian)
      (fun a b ↦ (hasFDerivAt_selfAdjoint_apply a b A).differentiableAt) hkn hgap u
      hu).differentiableAt,
    hH A H ▸ fderiv_prefixSum_eigenvalues₀_apply
      (M := fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜))
      (fun B ↦ B.property.isHermitian)
      (fun a b ↦ (hasFDerivAt_selfAdjoint_apply a b A).differentiableAt) hkn hgap u hu H⟩


/-! ### Continuity of the derivative -/

/-- The sorted eigenvalues are continuous on Hermitian matrices with the Frobenius norm. -/
private theorem continuousAt_eigenvalues₀_selfAdjoint
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) (i : Fin (Fintype.card ι)) :
    ContinuousAt (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      B.property.isHermitian.eigenvalues₀ i) A :=
  continuousAt_eigenvalues₀ (M := fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
    (B : Matrix ι ι 𝕜)) (fun B ↦ B.property.isHermitian)
    (fun a b ↦ (LinearMap.continuous_of_finiteDimensional
      (entryLinearMap ℝ 𝕜 a b ∘ₗ (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)).subtype)).continuousAt)
    i

private theorem continuousAt_eigenvalues₀_selfAdjoint'
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    ContinuousAt (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      B.property.isHermitian.eigenvalues₀) A :=
  continuousAt_pi.2 (continuousAt_eigenvalues₀_selfAdjoint A)

/-- A spectral gap persists near a Hermitian matrix. -/
private theorem eventually_eigenvalues₀_lt {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)} {k : ℕ}
    (hgap : ∀ i j : Fin (Fintype.card ι), i.val < k → k ≤ j.val →
      A.property.isHermitian.eigenvalues₀ j < A.property.isHermitian.eigenvalues₀ i) :
    ∀ᶠ B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) in 𝓝 A,
      ∀ i j : Fin (Fintype.card ι), i.val < k → k ≤ j.val →
        B.property.isHermitian.eigenvalues₀ j < B.property.isHermitian.eigenvalues₀ i := by
  refine eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ ?_
  by_cases hij : i.val < k ∧ k ≤ j.val
  · filter_upwards [(continuousAt_eigenvalues₀_selfAdjoint A j).eventually_lt
      (continuousAt_eigenvalues₀_selfAdjoint A i) (hgap i j hij.1 hij.2)] with B hB
    exact fun _ _ ↦ hB
  · exact Eventually.of_forall fun _ hi hj ↦ absurd ⟨hi, hj⟩ hij

/-- The derivative of a Ky Fan sum is continuous at a Hermitian matrix with a spectral gap after
the `k` largest eigenvalues. -/
private theorem continuousAt_fderiv_prefixSum_eigenvalues₀
    {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)} {k : ℕ} (hkn : k ≤ Fintype.card ι)
    (hgap : ∀ i j : Fin (Fintype.card ι), i.val < k → k ≤ j.val →
      A.property.isHermitian.eigenvalues₀ j < A.property.isHermitian.eigenvalues₀ i) :
    ContinuousAt (fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      prefixSum k B.property.isHermitian.eigenvalues₀)) A := by
  have hd : ∀ᶠ B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) in 𝓝 A,
      DifferentiableAt ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        prefixSum k B.property.isHermitian.eigenvalues₀) B := by
    filter_upwards [eventually_eigenvalues₀_lt hgap] with B hB
    obtain ⟨u, hu⟩ := B.property.isHermitian.exists_orthonormalBasis_mulVec_eq_eigenvalues₀_smul
    exact (prefixSum_eigenvalues₀_selfAdjoint_fderiv hkn hB u hu 0).1
  have h := (convexOn_prefixSum_eigenvalues₀ (𝕜 := 𝕜) (ι := ι) k).continuousAt_fderiv (x := A)
    univ_mem hd
  exact h

variable {f : (Fin (Fintype.card ι) → ℝ) → ℝ}

/-- A vector of weights extended by zero to `ℕ`. -/
private def extendWeights {n : ℕ} (y : Fin n → ℝ) (m : ℕ) : ℝ :=
  if h : m < n then y ⟨m, h⟩ else 0

private theorem extendWeights_fin {n : ℕ} (y : Fin n → ℝ) (j : Fin n) :
    extendWeights y j = y j := by
  simp [extendWeights]

private theorem extendWeights_self {n : ℕ} (y : Fin n → ℝ) : extendWeights y n = 0 := by
  simp [extendWeights]

/-- The weights `yⱼ = ∂ⱼ f(λ(A))` of a symmetric `f` are constant on the eigenvalue clusters of
`A`, so a nonzero coefficient `yₖ - yₖ₊₁` forces a spectral gap after `k + 1` eigenvalues. -/
private theorem eigenvalues₀_lt_of_extendWeights_sub_ne_zero
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) {k : Fin (Fintype.card ι)}
    (hc : extendWeights (fun j ↦ fderiv ℝ f A.property.isHermitian.eigenvalues₀ (Pi.single j 1))
      k - extendWeights (fun j ↦ fderiv ℝ f A.property.isHermitian.eigenvalues₀
        (Pi.single j 1)) (k + 1) ≠ 0)
    (i j : Fin (Fintype.card ι)) (hi : i.val < k + 1) (hj : k + 1 ≤ j.val) :
    A.property.isHermitian.eigenvalues₀ j < A.property.isHermitian.eigenvalues₀ i := by
  set μ₀ := A.property.isHermitian.eigenvalues₀
  have hk : k.val + 1 < Fintype.card ι := lt_of_le_of_lt hj j.isLt
  have hne : μ₀ ⟨k + 1, hk⟩ ≠ μ₀ k := fun heq ↦ hc <| by
    rw [sub_eq_zero, extendWeights_fin, show (k.val + 1 : ℕ) = (⟨k + 1, hk⟩ : Fin _).val from rfl,
      extendWeights_fin]
    exact fderiv_apply_single_eq_of_comp_swap (fun μ ↦ hf _ μ) heq.symm 1
  have hanti := A.property.isHermitian.eigenvalues₀_antitone
  calc μ₀ j ≤ μ₀ ⟨k + 1, hk⟩ := hanti (Fin.le_def.2 hj)
    _ < μ₀ k := lt_of_le_of_ne (hanti (Fin.le_def.2 (Nat.le_succ _))) hne
    _ ≤ μ₀ i := hanti (Fin.le_def.2 (by omega))

/-- **The gradient estimate.** At a Hermitian matrix `B` where `f` is differentiable at `λ(B)`
and which has a spectral gap at every index where the weights `y` jump, the derivative of the
spectral function in a direction `H` differs from the combination
`∑ₖ (yₖ - yₖ₊₁) D κₖ₊₁(B) H` of Ky Fan derivatives by at most
`n² ‖H‖ ∑ⱼ |∂ⱼ f(λ(B)) - yⱼ|`. -/
private theorem abs_fderiv_spectralFunction_sub_le
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)}
    (hBd : DifferentiableAt ℝ f B.property.isHermitian.eigenvalues₀)
    (y : Fin (Fintype.card ι) → ℝ)
    (hBg : ∀ k : Fin (Fintype.card ι), extendWeights y k - extendWeights y (k + 1) ≠ 0 →
      ∀ i j : Fin (Fintype.card ι), i.val < k + 1 → k + 1 ≤ j.val →
        B.property.isHermitian.eigenvalues₀ j < B.property.isHermitian.eigenvalues₀ i)
    (H : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    |fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        f B.property.isHermitian.eigenvalues₀) B H -
      ∑ k : Fin (Fintype.card ι), (extendWeights y k - extendWeights y (k + 1)) *
        fderiv ℝ (fun B' : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
          prefixSum (k + 1) B'.property.isHermitian.eigenvalues₀) B H| ≤
      (Fintype.card ι : ℝ) ^ 2 * ‖H‖ *
        ∑ j, |fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) - y j| := by
  set Y := extendWeights y
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
          (prefixSum_eigenvalues₀_selfAdjoint_fderiv (by omega) (hBg k hc) u hu H).2
    have h₂ := sum_smul_by_parts_prefixSum Y q
    simp only [Y, extendWeights_fin, extendWeights_self, smul_eq_mul, zero_mul, add_zero] at h₂
    rw [h₁, h₂]
    exact sum_congr rfl fun k _ ↦ by simp only [Y, extendWeights_fin]
  have hq (j : Fin (Fintype.card ι)) : |q j| ≤ (Fintype.card ι : ℝ) ^ 2 * ‖H‖ :=
    (RCLike.abs_re_le_norm _).trans (norm_star_dotProduct_mulVec_le _ (u.orthonormal.1 j))
  rw [hgB, show fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀) B H - ∑ j, y j * q j =
      ∑ j, (fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) * q j - y j * q j) by
    rw [sum_sub_distrib]
    exact congrArg (· - ∑ j, y j * q j) hF]
  calc _ ≤ ∑ j, |fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) - y j| *
        ((Fintype.card ι : ℝ) ^ 2 * ‖H‖) := by
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
  set Y := extendWeights y
  have hgap {k : Fin (Fintype.card ι)} (hc : Y k - Y (k + 1) ≠ 0) :=
    eigenvalues₀_lt_of_extendWeights_sub_ne_zero hf A hc
  -- Near `A`, `f` is differentiable at `λ(B)` and the spectral gaps of `A` persist.
  have hev : ∀ᶠ B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) in 𝓝 A,
      DifferentiableAt ℝ f B.property.isHermitian.eigenvalues₀ ∧
      ∀ k : Fin (Fintype.card ι), Y k - Y (k + 1) ≠ 0 →
        ∀ i j : Fin (Fintype.card ι), i.val < k + 1 → k + 1 ≤ j.val →
          B.property.isHermitian.eigenvalues₀ j < B.property.isHermitian.eigenvalues₀ i := by
    refine ((continuousAt_eigenvalues₀_selfAdjoint' A).eventually hfd).and
      (eventually_all.2 fun k ↦ ?_)
    by_cases hc : Y k - Y (k + 1) = 0
    · exact Eventually.of_forall fun _ h ↦ absurd hc h
    · exact (eventually_eigenvalues₀_lt (hgap hc)).mono fun _ hB _ ↦ hB
  refine continuousAt_clm_apply.2 fun H ↦ ?_
  -- The comparison function `g(B) = ∑ₖ (Yₖ - Yₖ₊₁) D κₖ₊₁(B) H`, continuous at `A`.
  set g : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) → ℝ := fun B ↦
    ∑ k : Fin (Fintype.card ι), (Y k - Y (k + 1)) * fderiv ℝ (fun B' : selfAdjoint.submodule ℝ
      (Matrix ι ι 𝕜) ↦ prefixSum (k + 1) B'.property.isHermitian.eigenvalues₀) B H
  have hg : ContinuousAt g A := by
    refine tendsto_finsetSum _ fun k _ ↦ ?_
    by_cases hc : Y k - Y (k + 1) = 0
    · simp only [hc, zero_mul]
      exact tendsto_const_nhds
    · exact (continuousAt_clm_apply.1 (continuousAt_fderiv_prefixSum_eigenvalues₀ (k := k + 1)
        (by omega) (hgap hc)) H).const_mul _
  set C : ℝ := (Fintype.card ι : ℝ) ^ 2 * ‖H‖
  have hest : ∀ᶠ B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) in 𝓝 A,
      |fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        f B.property.isHermitian.eigenvalues₀) B H - g B| ≤
        C * ∑ j, |fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) - y j| :=
    hev.mono fun B hB ↦ abs_fderiv_spectralFunction_sub_le hf hB.1 y hB.2 H
  -- The bound tends to zero, by the continuity of `∇f` and of `λ`.
  have hlim : Tendsto (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      C * ∑ j, |fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) - y j|)
      (𝓝 A) (𝓝 0) := by
    have hcont : ContinuousAt (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        fderiv ℝ f B.property.isHermitian.eigenvalues₀) A :=
      hfc.comp (continuousAt_eigenvalues₀_selfAdjoint' A)
    have h : Tendsto (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        C * ∑ j, |fderiv ℝ f B.property.isHermitian.eigenvalues₀ (Pi.single j 1) - y j|) (𝓝 A)
        (𝓝 (C * ∑ j, |fderiv ℝ f A.property.isHermitian.eigenvalues₀ (Pi.single j 1) -
          y j|)) := by
      refine (tendsto_finsetSum Finset.univ fun j _ ↦ ?_).const_mul C
      exact ((continuousAt_clm_apply.1 hcont (Pi.single j 1)).sub continuousAt_const).abs
    simpa [y] using h
  have hA : fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀) A H = g A := by
    have h := hest.self_of_nhds
    simp only [y, sub_self, abs_zero, sum_const_zero, mul_zero] at h
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' ?_
    (by simpa using hlim.add (tendsto_iff_norm_sub_tendsto_zero.1 hg.tendsto)))
  filter_upwards [hest] with B hB
  rw [norm_norm, Real.norm_eq_abs]
  -- Restate the goal in the syntactic form of `hA`.
  change |fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀) B H - fderiv ℝ (fun B : selfAdjoint.submodule ℝ
      (Matrix ι ι 𝕜) ↦ f B.property.isHermitian.eigenvalues₀) A H| ≤ _
  rw [hA]
  calc _ = |(fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
        f B.property.isHermitian.eigenvalues₀) B H - g B) + (g B - g A)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans ((add_le_add_iff_right _).2 hB)

/-- **Spectral functions of `C¹` functions are `C¹`** (Lewis 1996, Theorem 1.1). If `f` is
symmetric and `C¹` at the sorted eigenvalue vector `λ(A)`, the spectral function `B ↦ f(λ(B))` on
the real vector space of Hermitian matrices is `C¹` at `A`. -/
theorem contDiffAt_spectralFunction
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)}
    (hfA : ContDiffAt ℝ 1 f A.property.isHermitian.eigenvalues₀) :
    ContDiffAt ℝ 1 (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀) A := by
  have hev : ∀ᶠ B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) in 𝓝 A,
      ContDiffAt ℝ 1 f B.property.isHermitian.eigenvalues₀ :=
    (continuousAt_eigenvalues₀_selfAdjoint' A).eventually (hfA.eventually (by simp))
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
    set e := Fintype.equivOfCardEq (α := Fin (Fintype.card ι)) (β := ι) (Fintype.card_fin _)
    have hD (μ : Fin (Fintype.card ι) → ℝ) :
        (diagonal fun k ↦ (μ (e.symm k) : 𝕜)).IsHermitian :=
      isHermitian_diagonal_of_self_adjoint _ (funext fun _ ↦ RCLike.conj_ofReal _)
    let Φ : (Fin (Fintype.card ι) → ℝ) →ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) :=
      { toFun μ := ⟨diagonal fun k ↦ (μ (e.symm k) : 𝕜), (hD μ).isSelfAdjoint⟩
        map_add' μ ν := Subtype.ext <| by
          simp only [Submodule.coe_add, diagonal_add, Pi.add_apply, RCLike.ofReal_add]
        map_smul' c μ := Subtype.ext <| by
          simp only [RingHom.id_apply, Submodule.coe_smul, ← diagonal_smul, Pi.smul_apply,
            smul_eq_mul, RCLike.ofReal_mul]
          congr 1
          funext k
          simp [RCLike.real_smul_eq_coe_mul] }
    have hval {α : Type} (g : (Fin (Fintype.card ι) → ℝ) → α)
        (hg : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, g (μ ∘ σ) = g μ)
        (μ : Fin (Fintype.card ι) → ℝ) : g (Φ μ).property.isHermitian.eigenvalues₀ = g μ := by
      have h := (hD μ).apply_eigenvalues₀_diagonal (d := fun k ↦ μ (e.symm k)) e
        (f := g) fun σ ↦ by simpa [Function.comp_def] using hg σ μ
      simpa [Function.comp_def] using h
    have hmaps : MapsTo Φ Ω
        {B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) | B.property.isHermitian.eigenvalues₀ ∈ Ω} :=
      fun μ hμ ↦ by
        have h := hval (· ∈ Ω) (fun σ ν ↦ propext ⟨fun h ↦ by
          simpa [Function.comp_def] using hΩσ σ⁻¹ _ h, hΩσ σ ν⟩) μ
        exact Eq.mpr h hμ
    exact (h.comp (LinearMap.toContinuousLinearMap Φ).contDiff.contDiffOn hmaps).congr
      fun μ _ ↦ (hval f hf μ).symm
  · have hU : IsOpen
        {B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) | B.property.isHermitian.eigenvalues₀ ∈ Ω} :=
      hΩ.preimage (continuous_iff_continuousAt.2 continuousAt_eigenvalues₀_selfAdjoint')
    exact hU.contDiffOn_iff.2 fun B hB ↦
      contDiffAt_spectralFunction hf ((h _ hB).contDiffAt (hΩ.mem_nhds hB))
end Matrix
