/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.Analysis.Matrix.Eigenvalues.Basic
public import TauCeti.Analysis.Matrix.Eigenvalues.KyFan
import TauCeti.Analysis.Calculus.FDeriv.Matrix
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.Eigenvalues.Smooth
import TauCeti.Analysis.Matrix.Spectrum

/-!
# Spectral functions of Hermitian matrices: values and Lewis's derivative theorem

For a function `f : ℝⁿ → ℝ` the *spectral function* of `f` sends a Hermitian matrix `A` to
`f(λ(A))`, where `λ(A)` is the decreasingly sorted eigenvalue vector
`Matrix.IsHermitian.eigenvalues₀`. This file computes its values and, by Lewis's theorem, its
derivative.

The sorted eigenvalue vector is determined by the characteristic polynomial: if
`A.charpoly = ∏ k, (X - μ k)`, then `λ(A)` is a rearrangement `μ ∘ σ` of `μ`, and equals `μ` when
`μ` is antitone (`Matrix.IsHermitian.eigenvalues₀_eq_of_charpoly_eq`). So a function `f`
invariant under the rearrangements of `μ` takes the value `f μ` at `λ(A)`: the eigenvalues may
be listed in any order. In particular the spectral function of a real diagonal matrix `diag μ` is
`f μ`.

The general facts about sorted eigenvalues that spectral functions build on live in
`TauCeti.Analysis.Matrix.Eigenvalues.Basic`: the sum of the sorted eigenvalues is the real part of
the trace (`Matrix.IsHermitian.sum_eigenvalues₀_eq_re_trace`), their product is the determinant
(`Matrix.IsHermitian.det_eq_prod_eigenvalues₀`), and shifting `A` by `t • 1` shifts every sorted
eigenvalue by `t` (`Matrix.IsHermitian.eigenvalues₀_add_smul_one`), so that the spectral function
of `μ ↦ f (μ + t)` at `A` is that of `f` at `A + t • 1`.

## Lewis's theorem

Let `f : ℝⁿ → ℝ` be symmetric, that is, invariant under permutations of the coordinates, and
consider its spectral function on Hermitian `n × n` matrices over `RCLike 𝕜`. Lewis's theorem
says that the spectral function is differentiable at `A` exactly when `f` is differentiable at
`λ(A)`, with derivative

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

* `Matrix.IsHermitian.exists_perm_eigenvalues₀_eq_comp`: if `A.charpoly = ∏ k, (X - μ k)`, the
  sorted eigenvalue vector is a rearrangement of `μ`.
* `Matrix.IsHermitian.apply_eigenvalues₀_of_charpoly_eq`,
  `Matrix.IsHermitian.apply_eigenvalues₀_diagonal`: the value of a symmetric function at the
  sorted eigenvalues may be computed from any listing of the eigenvalues, and at `diag μ` it is
  `f μ`.
* `Matrix.IsHermitian.eigenvalues₀_lt_of_extend_sub_ne_zero`: weights constant on eigenvalue
  clusters, extended by zero, jump only at spectral gaps.
* `Matrix.hasFDerivAt_sum_mul_eigenvalues₀`: a weighted sum of sorted eigenvalues whose weights
  are constant on eigenvalue clusters is differentiable.
* `Matrix.hasFDerivAt_spectralFunction`, `Matrix.fderiv_spectralFunction_apply`: the derivative of
  `x ↦ f(λ(M x))` for a symmetric `f` differentiable at `λ(M x₀)`.
* `Matrix.conjDiagonalSelfAdjoint`, `Matrix.eigenvalues₀_conjDiagonalSelfAdjoint`: the real-linear
  map `μ ↦ U diag(μ) U*` into the Hermitian matrices, whose sorted eigenvalues for a unitary `U`
  are a rearrangement of `μ`.
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

section Values

open Polynomial

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] {A : Matrix ι ι 𝕜}

namespace IsHermitian

/-- **The sorted eigenvalues are a rearrangement of any listing of the eigenvalues.** If the
characteristic polynomial of a Hermitian matrix `A` is `∏ k, (X - μ k)` for a real vector `μ`,
then the sorted eigenvalue vector of `A` is `μ ∘ σ` for a permutation `σ`. -/
theorem exists_perm_eigenvalues₀_eq_comp (hA : A.IsHermitian) {μ : Fin (Fintype.card ι) → ℝ}
    (h : A.charpoly = ∏ k, (X - C (μ k : 𝕜))) :
    ∃ σ : Equiv.Perm (Fin (Fintype.card ι)), hA.eigenvalues₀ = μ ∘ σ :=
  ⟨Tuple.sortDesc μ, hA.eigenvalues₀_eq_of_charpoly_eq (Tuple.antitone_sortDesc μ) <| by
    rw [h]
    exact (Equiv.prod_comp (Tuple.sortDesc μ) fun k ↦ X - C (μ k : 𝕜)).symm⟩

/-- **Values of a spectral function from any listing of the eigenvalues.** If the characteristic
polynomial of a Hermitian matrix `A` is `∏ k, (X - μ k)` and `f` is invariant under the
rearrangements of `μ`, then `f` takes the value `f μ` at the sorted eigenvalue vector of `A`. -/
theorem apply_eigenvalues₀_of_charpoly_eq {α : Type*} (hA : A.IsHermitian)
    {μ : Fin (Fintype.card ι) → ℝ} (h : A.charpoly = ∏ k, (X - C (μ k : 𝕜)))
    {f : (Fin (Fintype.card ι) → ℝ) → α} (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)),
      f (μ ∘ σ) = f μ) :
    f hA.eigenvalues₀ = f μ := by
  obtain ⟨σ, hσ⟩ := hA.exists_perm_eigenvalues₀_eq_comp h
  rw [hσ, hf]

/-- **The spectral function of a real diagonal matrix.** For a real vector `d` indexed by `ι`,
listed along any equivalence `e : Fin n ≃ ι`, a function `f` invariant under the rearrangements of
`d ∘ e` takes the value `f (d ∘ e)` at the sorted eigenvalue vector of `diagonal d`. -/
theorem apply_eigenvalues₀_diagonal {α : Type*} {d : ι → ℝ}
    (hd : (diagonal fun i ↦ (d i : 𝕜)).IsHermitian) (e : Fin (Fintype.card ι) ≃ ι)
    {f : (Fin (Fintype.card ι) → ℝ) → α}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), f (d ∘ e ∘ σ) = f (d ∘ e)) :
    f hd.eigenvalues₀ = f (d ∘ e) :=
  hd.apply_eigenvalues₀_of_charpoly_eq (by
    rw [charpoly_diagonal]
    exact (Equiv.prod_comp e fun i ↦ X - C (d i : 𝕜)).symm) hf

end IsHermitian

end Values

section Derivative

variable {𝕜 n E : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {M : E → Matrix n n 𝕜} {x₀ : E}

/-- **Weights constant on eigenvalue clusters jump only at spectral gaps.** Let the weights `y`
satisfy `yᵢ = yⱼ` whenever `λᵢ(A) = λⱼ(A)`, and extend them by zero to `ℕ`. If the extended
weights differ at `k` and `k + 1`, then `A` has a spectral gap after its `k + 1` largest
eigenvalues. -/
theorem IsHermitian.eigenvalues₀_lt_of_extend_sub_ne_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {y : Fin (Fintype.card n) → ℝ} (hy : ∀ i j, hA.eigenvalues₀ i = hA.eigenvalues₀ j → y i = y j)
    {k : Fin (Fintype.card n)}
    (hc : Function.extend Fin.val y 0 k - Function.extend Fin.val y 0 (k + 1) ≠ 0)
    (i j : Fin (Fintype.card n)) (hi : i.val < k + 1) (hj : k + 1 ≤ j.val) :
    hA.eigenvalues₀ j < hA.eigenvalues₀ i := by
  have hk : k.val + 1 < Fintype.card n := lt_of_le_of_lt hj j.isLt
  have hne : hA.eigenvalues₀ ⟨k + 1, hk⟩ ≠ hA.eigenvalues₀ k := fun heq ↦ hc <| by
    rw [sub_eq_zero, Fin.val_injective.extend_apply,
      Fin.val_injective.extend_apply y 0 ⟨k + 1, hk⟩]
    exact hy _ _ heq.symm
  have hanti := hA.eigenvalues₀_antitone
  calc hA.eigenvalues₀ j ≤ hA.eigenvalues₀ ⟨k + 1, hk⟩ := hanti (Fin.le_def.2 hj)
    _ < hA.eigenvalues₀ k := lt_of_le_of_ne (hanti (Fin.le_def.2 (Nat.le_succ _))) hne
    _ ≤ hA.eigenvalues₀ i := hanti (Fin.le_def.2 (by omega))

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
  set Y : ℕ → ℝ := Function.extend Fin.val y 0
  have hsum (x : E) : ∑ j, y j * (hM x).eigenvalues₀ j =
      ∑ k : Fin (Fintype.card n), (Y k - Y (k + 1)) * prefixSum (k + 1) (hM x).eigenvalues₀ :=
    sum_smul_by_parts_prefixSum_extend y (hM x).eigenvalues₀
  have hsumD : ∑ j, y j • D j =
      ∑ k : Fin (Fintype.card n), (Y k - Y (k + 1)) • prefixSum (k + 1) D :=
    sum_smul_by_parts_prefixSum_extend y D
  rw [hsumD, funext hsum]
  refine HasFDerivAt.fun_sum fun k _ ↦ ?_
  by_cases hc : Y k - Y (k + 1) = 0
  · simp only [hc, zero_mul, zero_smul]
    exact hasFDerivAt_const 0 x₀
  -- A nonzero coefficient `Yₖ - Yₖ₊₁` forces a spectral gap after the `k + 1` largest eigenvalues.
  convert (hasFDerivAt_prefixSum_eigenvalues₀ hM hMd (k := k + 1) (by omega)
    ((hM x₀).eigenvalues₀_lt_of_extend_sub_ne_zero hy hc) u hu).const_mul (Y k - Y (k + 1))
    using 2
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
      conv_lhs => rw [pi_eq_sum_univ' μ, map_sum]
      exact sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
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

/-- The real-linear map `μ ↦ U diag(μ) U*` from `ℝⁿ` to the Hermitian matrices, for a square
matrix `U`. The entries of `μ` are transported to the index type `ι` along the equivalence used by
`Matrix.IsHermitian.eigenvalues`. For a unitary `U` the sorted eigenvalues of `U diag(μ) U*` are a
rearrangement of `μ` (`Matrix.eigenvalues₀_conjDiagonalSelfAdjoint`), so a symmetric function `f`
equals its spectral function composed with this map. -/
def conjDiagonalSelfAdjoint (U : Matrix ι ι 𝕜) :
    (Fin (Fintype.card ι) → ℝ) →ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) where
  toFun μ := ⟨U * diagonal (fun k ↦
      (μ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k) : 𝕜)) * star U,
    (isHermitian_diagonal_of_self_adjoint _
      (funext fun _ ↦ RCLike.conj_ofReal _)).isSelfAdjoint.conjugate U⟩
  map_add' μ ν := Subtype.ext <| by
    rw [Submodule.coe_add, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    simp only [Pi.add_apply, RCLike.ofReal_add]
  map_smul' c μ := Subtype.ext <| by
    rw [RingHom.id_apply, Submodule.coe_smul, ← Matrix.smul_mul, ← Matrix.mul_smul,
      ← diagonal_smul,
      show (c • fun k ↦ (μ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k) : 𝕜)) =
        fun k ↦ ((c • μ) ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k) : 𝕜) from
        funext fun k ↦ by simp [RCLike.real_smul_eq_coe_mul]]

/-- The matrix `U diag(μ) U*` underlying `Matrix.conjDiagonalSelfAdjoint U μ`. -/
@[simp]
theorem coe_conjDiagonalSelfAdjoint_apply (U : Matrix ι ι 𝕜) (μ : Fin (Fintype.card ι) → ℝ) :
    (conjDiagonalSelfAdjoint U μ : Matrix ι ι 𝕜) = U * diagonal (fun k ↦
      (μ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k) : 𝕜)) * star U :=
  (rfl)

/-- **The sorted eigenvalues of `U diag(μ) U*`** for a unitary `U` are the entries of `μ`, sorted
decreasingly by `Tuple.sortDesc`. -/
theorem eigenvalues₀_conjDiagonalSelfAdjoint {U : Matrix ι ι 𝕜} (hU : U ∈ unitaryGroup ι 𝕜)
    (μ : Fin (Fintype.card ι) → ℝ) :
    (conjDiagonalSelfAdjoint U μ).property.isHermitian.eigenvalues₀ = μ ∘ Tuple.sortDesc μ :=
  (IsHermitian.eigenvalues₀_mul_mul_star
    (isHermitian_diagonal_of_self_adjoint _ (funext fun _ ↦ RCLike.conj_ofReal _)) hU _).trans
    (IsHermitian.eigenvalues₀_diagonal_eq_comp_sortDesc μ _)

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
    set U : Matrix ι ι 𝕜 := (A.property.isHermitian.eigenvectorUnitary : Matrix ι ι 𝕜)
    set Φ := conjDiagonalSelfAdjoint U
    have hΦ (μ : Fin (Fintype.card ι) → ℝ) : f (Φ μ).property.isHermitian.eigenvalues₀ = f μ := by
      rw [eigenvalues₀_conjDiagonalSelfAdjoint
        A.property.isHermitian.eigenvectorUnitary.property, hf]
    have hΦA : Φ A.property.isHermitian.eigenvalues₀ = A := by
      refine Subtype.ext ?_
      conv_rhs => rw [A.property.isHermitian.spectral_theorem]
      simp [Φ, U, Unitary.conjStarAlgAut_apply,
        A.property.isHermitian.eigenvalues₀_equivOfCardEq_symm, Function.comp_def]
    have hc := (hΦA ▸ h).comp _ (LinearMap.toContinuousLinearMap Φ).differentiableAt
    simpa [Function.comp_def, hΦ] using hc
  · obtain ⟨u, hu⟩ := A.property.isHermitian.exists_orthonormalBasis_mulVec_eq_eigenvalues₀_smul
    exact (hasFDerivAt_spectralFunction
      (M := fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜))
      (fun B ↦ B.property.isHermitian)
      (fun a b ↦ (hasFDerivAt_selfAdjoint_apply a b A).differentiableAt) hf h u hu).differentiableAt

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
  -- The matrix of entrywise derivatives in the direction `H` is `H`. The goal carries the
  -- Frobenius-norm topology, which agrees with the entrywise topology of
  -- `Matrix.of_fderiv_selfAdjoint_apply_eq` only after unfolding instances, so `rw` and `simp` do
  -- not match it; cast along it with `▸`, which checks the match by unfolding.
  exact of_fderiv_selfAdjoint_apply_eq A H ▸ fderiv_spectralFunction_apply
    (M := fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦ (B : Matrix ι ι 𝕜))
    (fun B ↦ B.property.isHermitian)
    (fun a b ↦ (hasFDerivAt_selfAdjoint_apply a b A).differentiableAt) hf hfA u hu H

end SelfAdjoint

end Derivative


end Matrix
