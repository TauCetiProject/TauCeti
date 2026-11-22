/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.Analysis.Matrix.Eigenvalues.KyFan
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.Eigenvalues.Smooth

/-!
# Lewis's theorem: the derivative of spectral functions

Let `f : ℝⁿ → ℝ` be symmetric, that is, invariant under permutations of the coordinates. Its
*spectral function* sends a Hermitian `n × n` matrix `A` over `RCLike 𝕜` to `f(λ(A))`, where
`λ(A)` is the decreasingly sorted eigenvalue vector `Matrix.IsHermitian.eigenvalues₀`. Lewis's
theorem says that the spectral function is differentiable at `A` exactly when `f` is
differentiable at `λ(A)`, with derivative

`H ↦ ∑ⱼ ∂ⱼ f(λ(A)) Re ⟪uⱼ, H uⱼ⟫`

for every orthonormal eigenbasis `(uⱼ)` of `A` ordered as `λ(A)`. Equivalently, the gradient is
`U diag(∇f(λ(A))) U*` for the unitary `U` with columns `uⱼ`. The eigenvalue vector itself is not
differentiable at a repeated eigenvalue; the symmetry of `f` is what makes the composite
differentiable there.

The derivative is computed along a family `x ↦ M x` of Hermitian matrices over a real normed
space whose entries are differentiable at `x₀` (`Matrix.hasFDerivAt_spectralFunction`), as for
the Ky Fan sums in `TauCeti.Analysis.Matrix.Eigenvalues.KyFan`. On the real vector space
`selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)` of Hermitian matrices, normed by the Frobenius norm,
this gives the differentiability criterion (`Matrix.differentiableAt_spectralFunction_iff`) and
the gradient formula (`Matrix.fderiv_spectralFunction_selfAdjoint_apply`).

The proof follows Lewis. A symmetric `f` has `∂ᵢ f(μ) = ∂ⱼ f(μ)` whenever `μᵢ = μⱼ`
(`TauCeti.fderiv_apply_single_eq_of_comp_swap`), so the weights `yⱼ = ∂ⱼ f(λ(M x₀))` are constant
on the eigenvalue clusters of `M x₀`. Summation by parts writes `∑ⱼ yⱼ λⱼ` as a combination of the
Ky Fan sums `λ₀ + ⋯ + λₖ₋₁` whose coefficient `yₖ₋₁ - yₖ` vanishes unless `λₖ < λₖ₋₁`. Ky Fan
sums are differentiable at such a spectral gap (`Matrix.hasFDerivAt_prefixSum_eigenvalues₀`), so
`x ↦ ∑ⱼ yⱼ λⱼ(M x)` is differentiable (`Matrix.hasFDerivAt_sum_mul_eigenvalues₀`). Weyl's
perturbation bound makes `x ↦ λ(M x)` Lipschitz at `x₀`, so composing the first-order expansion of
`f` at `λ(M x₀)` with it leaves a remainder `o(‖x - x₀‖)`. Conversely, `f(μ) = f(λ(U diag(μ) U*))`
for a unitary `U` diagonalizing `A`, so `f` is the spectral function composed with a linear map.

## Main results

* `Matrix.hasFDerivAt_sum_mul_eigenvalues₀`: a weighted sum of sorted eigenvalues whose weights
  are constant on eigenvalue clusters is differentiable.
* `Matrix.hasFDerivAt_spectralFunction`, `Matrix.fderiv_spectralFunction_apply`: the derivative of
  `x ↦ f(λ(M x))` for a symmetric `f` differentiable at `λ(M x₀)`.
* `Matrix.differentiableAt_spectralFunction_iff`: Lewis's differentiability criterion on Hermitian
  matrices.
* `Matrix.fderiv_spectralFunction_selfAdjoint_apply`: the gradient formula on Hermitian matrices.

## References

* A. S. Lewis, *Derivatives of spectral functions*, Math. Oper. Res. **21** (1996), 576–588,
  Theorem 1.1 and Lemmas 2.2–2.3.
-/

public section

noncomputable section

open Filter Topology Asymptotics Finset TauCeti

namespace Matrix

variable {𝕜 n E : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {M : E → Matrix n n 𝕜} {x₀ : E}

/-- The sorted eigenvalues of a family of Hermitian matrices whose entries are differentiable at
`x₀` move by `O(‖x - x₀‖)`. -/
private theorem isBigO_eigenvalues₀_sub (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀) :
    (fun x ↦ (hM x).eigenvalues₀ - (hM x₀).eigenvalues₀) =O[𝓝 x₀] fun x ↦ x - x₀ := by
  set ε : E → ℝ := fun x ↦ ∑ a, ∑ b, ‖M x a b - M x₀ a b‖
  have hεO : ε =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ :=
    IsBigO.fun_sum fun a _ ↦ IsBigO.fun_sum fun b _ ↦
      (hMd a b).hasFDerivAt.isBigO_sub.norm_left.norm_right
  refine IsBigO.of_norm_right (IsBigO.trans ?_ hεO)
  refine IsBigO.of_bound (Fintype.card n) (Eventually.of_forall fun x ↦ ?_)
  have hε : 0 ≤ ε x := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ norm_nonneg _
  rw [Real.norm_of_nonneg hε]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  -- Each entry of `M x - M x₀` is bounded by the sum `ε x` of all of them.
  refine (hM x).abs_eigenvalues₀_sub_le_of_entry_le (hM x₀) (fun a b ↦ ?_) i
  exact (single_le_sum (f := fun b ↦ ‖M x a b - M x₀ a b‖) (fun _ _ ↦ norm_nonneg _)
    (mem_univ b)).trans (single_le_sum (f := fun a ↦ ∑ b, ‖M x a b - M x₀ a b‖)
      (fun _ _ ↦ sum_nonneg fun _ _ ↦ norm_nonneg _) (mem_univ a))

/-- **Weighted sums of sorted eigenvalues are differentiable when the weights are constant on
eigenvalue clusters** (Lewis 1996, Lemma 2.2). Let `M` be a family of Hermitian matrices whose
entries are differentiable at `x₀`, and let the weights satisfy `yᵢ = yⱼ` whenever
`λᵢ(M x₀) = λⱼ(M x₀)`. Then `x ↦ ∑ⱼ yⱼ λⱼ(M x)` has derivative
`v ↦ ∑ⱼ yⱼ Re ⟪uⱼ, (DM (x₀) v) uⱼ⟫` at `x₀`, for any orthonormal eigenbasis `(uⱼ)` of `M x₀`
ordered as its eigenvalues. -/
theorem hasFDerivAt_sum_mul_eigenvalues₀ (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀) {y : Fin (Fintype.card n) → ℝ}
    (hy : ∀ i j, (hM x₀).eigenvalues₀ i = (hM x₀).eigenvalues₀ j → y i = y j)
    (u : OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n))
    (hu : ∀ j, M x₀ *ᵥ u j = ((hM x₀).eigenvalues₀ j : 𝕜) • ⇑(u j)) :
    HasFDerivAt (fun x ↦ ∑ j, y j * (hM x).eigenvalues₀ j)
      (∑ j, y j • RCLike.reCLM.comp
        (∑ a, ∑ b, (star (u j a) * u j b) • fderiv ℝ (fun x ↦ M x a b) x₀)) x₀ := by
  set D : Fin (Fintype.card n) → E →L[ℝ] ℝ := fun j ↦ RCLike.reCLM.comp
    (∑ a, ∑ b, (star (u j a) * u j b) • fderiv ℝ (fun x ↦ M x a b) x₀)
  -- Extend the weights by zero to `ℕ` and sum by parts into Ky Fan sums.
  set Y : ℕ → ℝ := fun m ↦ if h : m < Fintype.card n then y ⟨m, h⟩ else 0
  have hY (j : Fin (Fintype.card n)) : Y j = y j := by simp [Y]
  have hYN : Y (Fintype.card n) = 0 := by simp [Y]
  have hsum (x : E) : ∑ j, y j * (hM x).eigenvalues₀ j =
      ∑ k : Fin (Fintype.card n), (Y k - Y (k + 1)) * prefixSum (k + 1) (hM x).eigenvalues₀ := by
    simpa [hY, hYN] using sum_smul_by_parts_prefixSum Y (hM x).eigenvalues₀
  have hsumD : ∑ j, y j • D j =
      ∑ k : Fin (Fintype.card n), (Y k - Y (k + 1)) • prefixSum (k + 1) D := by
    simpa [hY, hYN] using sum_smul_by_parts_prefixSum Y D
  rw [hsumD, funext hsum]
  refine HasFDerivAt.fun_sum fun k _ ↦ ?_
  by_cases hc : Y k - Y (k + 1) = 0
  · simp only [hc, zero_mul, zero_smul]
    exact hasFDerivAt_const 0 x₀
  -- A nonzero coefficient `Yₖ - Yₖ₊₁` forces a spectral gap after the `k + 1` largest eigenvalues.
  set μ₀ := (hM x₀).eigenvalues₀
  have hgap (i j : Fin (Fintype.card n)) (hi : i.val < k + 1) (hj : k + 1 ≤ j.val) :
      μ₀ j < μ₀ i := by
    have hk : k.val + 1 < Fintype.card n := lt_of_le_of_lt hj j.isLt
    have hne : μ₀ ⟨k + 1, hk⟩ ≠ μ₀ k := fun heq ↦ hc <| by
      rw [sub_eq_zero, hY k, show Y (k + 1) = y ⟨k + 1, hk⟩ by simp [Y, hk]]
      exact hy _ _ heq.symm
    have hanti := (hM x₀).eigenvalues₀_antitone
    calc μ₀ j ≤ μ₀ ⟨k + 1, hk⟩ := hanti (Fin.le_def.2 hj)
      _ < μ₀ k := lt_of_le_of_ne (hanti (Fin.le_def.2 (Nat.le_succ _))) hne
      _ ≤ μ₀ i := hanti (Fin.le_def.2 (by omega))
  convert (hasFDerivAt_prefixSum_eigenvalues₀ hM hMd (k := k + 1) (by omega) hgap u
    hu).const_mul (Y k - Y (k + 1)) using 2
  rw [prefixSum_def, ← ContinuousLinearMap.comp_finsetSum]

/-- **Lewis's theorem**, the derivative of a spectral function (Lewis 1996, Theorem 1.1). Let `M`
be a family of Hermitian matrices whose entries are differentiable at `x₀`, and let `f` be a
symmetric function differentiable at the sorted eigenvalue vector `λ(M x₀)`. For an orthonormal
eigenbasis `(uⱼ)` of `M x₀` ordered as its eigenvalues, `x ↦ f(λ(M x))` has derivative
`v ↦ ∑ⱼ ∂ⱼ f(λ(M x₀)) Re ⟪uⱼ, (DM (x₀) v) uⱼ⟫` at `x₀`. -/
theorem hasFDerivAt_spectralFunction (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀)
    {f : (Fin (Fintype.card n) → ℝ) → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card n)), ∀ μ, f (μ ∘ σ) = f μ)
    (hfd : DifferentiableAt ℝ f (hM x₀).eigenvalues₀)
    (u : OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n))
    (hu : ∀ j, M x₀ *ᵥ u j = ((hM x₀).eigenvalues₀ j : 𝕜) • ⇑(u j)) :
    HasFDerivAt (fun x ↦ f (hM x).eigenvalues₀)
      (∑ j, fderiv ℝ f (hM x₀).eigenvalues₀ (Pi.single j 1) • RCLike.reCLM.comp
        (∑ a, ∑ b, (star (u j a) * u j b) • fderiv ℝ (fun x ↦ M x a b) x₀)) x₀ := by
  set μ₀ := (hM x₀).eigenvalues₀
  set y : Fin (Fintype.card n) → ℝ := fun j ↦ fderiv ℝ f μ₀ (Pi.single j 1)
  -- The linear part: the partial derivatives of the symmetric `f` agree on eigenvalue clusters.
  have hg := hasFDerivAt_sum_mul_eigenvalues₀ hM hMd (y := y)
    (fun i j hij ↦ fderiv_apply_single_eq_of_comp_swap (fun μ ↦ hf _ μ) hij 1) u hu
  -- The remainder `f(λ(M x)) - ∑ⱼ yⱼ λⱼ(M x)` has vanishing derivative, since `λ ∘ M` is
  -- `O(‖x - x₀‖)` and `f` is differentiable at `λ(M x₀)`.
  have hR : HasFDerivAt (fun x ↦ f (hM x).eigenvalues₀ - ∑ j, y j * (hM x).eigenvalues₀ j)
      (0 : E →L[ℝ] ℝ) x₀ := by
    refine HasFDerivAt.of_isLittleO ?_
    have hlin (μ : Fin (Fintype.card n) → ℝ) : fderiv ℝ f μ₀ μ = ∑ j, y j * μ j := by
      conv_lhs => rw [← univ_sum_single μ]
      refine (map_sum _ _ _).trans (sum_congr rfl fun j _ ↦ ?_)
      rw [show (Pi.single j (μ j) : Fin (Fintype.card n) → ℝ) = μ j • Pi.single j 1 by
        ext k; simp [Pi.single_apply], map_smul, smul_eq_mul, mul_comm]
    have htend : Tendsto (fun x ↦ (hM x).eigenvalues₀) (𝓝 x₀) (𝓝 μ₀) :=
      tendsto_pi_nhds.2 fun i ↦
        continuousAt_eigenvalues₀ hM (fun a b ↦ (hMd a b).continuousAt) i
    refine ((hfd.hasFDerivAt.isLittleO.comp_tendsto htend).trans_isBigO
      (isBigO_eigenvalues₀_sub hM hMd)).congr_left fun x ↦ ?_
    simp only [Function.comp_apply, hlin, Pi.sub_apply, zero_apply, sub_zero, mul_sub,
      sum_sub_distrib]
    ring
  have hsum := hg.add hR
  rw [add_zero] at hsum
  exact hsum.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ (add_sub_cancel _ _).symm)

/-- **Lewis's theorem**, the gradient formula. The derivative at `x₀` in the direction `v` of
`x ↦ f(λ(M x))` is `∑ⱼ ∂ⱼ f(λ(M x₀)) Re ⟪uⱼ, (DM (x₀) v) uⱼ⟫` for any orthonormal eigenbasis
`(uⱼ)` of `M x₀` ordered as its eigenvalues. -/
theorem fderiv_spectralFunction_apply (hM : ∀ x, (M x).IsHermitian)
    (hMd : ∀ a b, DifferentiableAt ℝ (fun x ↦ M x a b) x₀)
    {f : (Fin (Fintype.card n) → ℝ) → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card n)), ∀ μ, f (μ ∘ σ) = f μ)
    (hfd : DifferentiableAt ℝ f (hM x₀).eigenvalues₀)
    (u : OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n))
    (hu : ∀ j, M x₀ *ᵥ u j = ((hM x₀).eigenvalues₀ j : 𝕜) • ⇑(u j)) (v : E) :
    fderiv ℝ (fun x ↦ f (hM x).eigenvalues₀) x₀ v =
      ∑ j, fderiv ℝ f (hM x₀).eigenvalues₀ (Pi.single j 1) *
        RCLike.re (star ⇑(u j) ⬝ᵥ (of (fun a b ↦ fderiv ℝ (fun x ↦ M x a b) x₀ v) *ᵥ ⇑(u j))) := by
  rw [(hasFDerivAt_spectralFunction hM hMd hf hfd u hu).fderiv, sum_apply]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [smul_apply, ContinuousLinearMap.comp_apply, RCLike.reCLM_apply, sum_sum_smul_apply,
    smul_eq_mul]

section SelfAdjoint

open scoped Matrix.Norms.Frobenius

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (Fin (Fintype.card ι) → ℝ) → ℝ}

omit [Fintype ι] [DecidableEq ι] in
/-- The entries of a Hermitian matrix depend linearly, hence differentiably, on the matrix. -/
private theorem differentiableAt_selfAdjoint_apply [Finite ι] (a b : ι)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    DifferentiableAt ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜) a b) A ∧
      ∀ H : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜), fderiv ℝ
        (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜) a b) A H =
          (H : Matrix ι ι 𝕜) a b := by
  let := Fintype.ofFinite ι
  have h : HasFDerivAt
      (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜) a b)
      (LinearMap.toContinuousLinearMap
        (entryLinearMap ℝ 𝕜 a b ∘ₗ (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)).subtype)) A :=
    (LinearMap.toContinuousLinearMap
      (entryLinearMap ℝ 𝕜 a b ∘ₗ (selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)).subtype)).hasFDerivAt
  exact ⟨h.differentiableAt, fun H ↦ by simp [h.fderiv]⟩

/-- **Lewis's theorem**, differentiability (Lewis 1996, Theorem 1.1). For a symmetric function `f`
on `ℝⁿ`, the spectral function `A ↦ f(λ(A))` on the real vector space of Hermitian matrices is
differentiable at `A` if and only if `f` is differentiable at the sorted eigenvalue vector
`λ(A)`. -/
theorem differentiableAt_spectralFunction_iff
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    DifferentiableAt ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀) A ↔
      DifferentiableAt ℝ f A.property.isHermitian.eigenvalues₀ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- `f` is the spectral function along the linear map `μ ↦ U diag(μ) U*`, for a unitary `U`
    -- diagonalizing `A`.
    set e := Fintype.equivOfCardEq (α := Fin (Fintype.card ι)) (β := ι) (Fintype.card_fin _)
    set U : Matrix ι ι 𝕜 := (A.property.isHermitian.eigenvectorUnitary : Matrix ι ι 𝕜)
    have hD (μ : Fin (Fintype.card ι) → ℝ) :
        (diagonal fun k ↦ (μ (e.symm k) : 𝕜)).IsHermitian :=
      isHermitian_diagonal_of_self_adjoint _ (funext fun _ ↦ RCLike.conj_ofReal _)
    let Φ : (Fin (Fintype.card ι) → ℝ) →ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) :=
      { toFun μ := ⟨U * diagonal (fun k ↦ (μ (e.symm k) : 𝕜)) * star U,
          (hD μ).isSelfAdjoint.conjugate U⟩
        map_add' μ ν := Subtype.ext <| by
          rw [Submodule.coe_add, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
          simp only [Pi.add_apply, RCLike.ofReal_add]
        map_smul' c μ := Subtype.ext <| by
          rw [RingHom.id_apply, Submodule.coe_smul, ← Matrix.smul_mul, ← Matrix.mul_smul,
            ← diagonal_smul]
          rw [show (c • fun k ↦ (μ (e.symm k) : 𝕜)) = fun k ↦ ((c • μ) (e.symm k) : 𝕜) from
            funext fun k ↦ by simp [RCLike.real_smul_eq_coe_mul]] }
    have hΦ (μ : Fin (Fintype.card ι) → ℝ) : f (Φ μ).property.isHermitian.eigenvalues₀ = f μ := by
      have hU : U ∈ unitaryGroup ι 𝕜 := A.property.isHermitian.eigenvectorUnitary.property
      rw [(hD μ).eigenvalues₀_mul_mul_star hU (Φ μ).property.isHermitian,
        IsHermitian.eigenvalues₀_diagonal_eq_comp_sortDesc, hf]
    have hΦA : Φ A.property.isHermitian.eigenvalues₀ = A := by
      refine Subtype.ext ?_
      conv_rhs => rw [A.property.isHermitian.spectral_theorem]
      simp [Φ, U, Unitary.conjStarAlgAut_apply, IsHermitian.eigenvalues, e, Function.comp_def]
    have hc := (hΦA ▸ h).comp _ (LinearMap.toContinuousLinearMap Φ).differentiableAt
    simpa [Function.comp_def, hΦ] using hc
  · obtain ⟨u, hu⟩ := A.property.isHermitian.exists_orthonormalBasis_mulVec_eq_eigenvalues₀_smul
    exact (hasFDerivAt_spectralFunction
      (M := fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜))
      (fun B ↦ B.property.isHermitian)
      (fun a b ↦ (differentiableAt_selfAdjoint_apply a b A).1) hf h u hu).differentiableAt

/-- **Lewis's theorem**, the gradient formula on Hermitian matrices. If `f` is symmetric and
differentiable at `λ(A)`, the derivative of the spectral function `B ↦ f(λ(B))` at `A` in the
direction `H` is `∑ⱼ ∂ⱼ f(λ(A)) Re ⟪uⱼ, H uⱼ⟫` for any orthonormal eigenbasis `(uⱼ)` of `A`
ordered as its eigenvalues. Equivalently, the gradient is `U diag(∇f(λ(A))) U*` for the unitary
`U` with columns `uⱼ`. -/
theorem fderiv_spectralFunction_selfAdjoint_apply
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜))
    (hfA : DifferentiableAt ℝ f A.property.isHermitian.eigenvalues₀)
    (u : OrthonormalBasis (Fin (Fintype.card ι)) 𝕜 (EuclideanSpace 𝕜 ι))
    (hu : ∀ j, (A : Matrix ι ι 𝕜) *ᵥ u j = (A.property.isHermitian.eigenvalues₀ j : 𝕜) • ⇑(u j))
    (H : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀) A H =
      ∑ j, fderiv ℝ f A.property.isHermitian.eigenvalues₀ (Pi.single j 1) *
        RCLike.re (star ⇑(u j) ⬝ᵥ ((H : Matrix ι ι 𝕜) *ᵥ ⇑(u j))) := by
  refine (fderiv_spectralFunction_apply
    (M := fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜))
    (fun B ↦ B.property.isHermitian)
    (fun a b ↦ (differentiableAt_selfAdjoint_apply a b A).1) hf hfA u hu H).trans ?_
  -- The matrix of entrywise derivatives in the direction `H` is `H`. Rewriting does not fire on
  -- the entrywise derivatives of this goal, so descend to the matrix with `congr`.
  refine sum_congr rfl fun j _ ↦ ?_
  congr 4
  exact Matrix.ext fun a b ↦ (differentiableAt_selfAdjoint_apply a b A).2 H

end SelfAdjoint

end Matrix
