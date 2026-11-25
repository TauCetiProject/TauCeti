/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.KyFan
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family

/-!
# Ky Fan sums of eigenvalues at a spectral gap

Let `T` be a symmetric operator on an `n`-dimensional inner product space over `RCLike 𝕜`, with an
orthonormal eigenbasis `b` and eigenvalues `μ`, so `T bⱼ = μⱼ bⱼ`. Suppose the first `k` eigenvalues
are separated from the others by a gap `δ > 0`: `μⱼ + δ ≤ μᵢ` whenever `i < k ≤ j`. Then the Ky Fan
sum `κₖ = λ₀ + ⋯ + λₖ₋₁` of the `k` largest eigenvalues, which at `T` is `μ₀ + ⋯ + μₖ₋₁`, has a
first-order expansion at `T` with a quadratic remainder: for every symmetric `S` with
`‖(S - T) x‖ ≤ C ‖x‖`,

`0 ≤ κₖ(S) - κₖ(T) - ∑_{j < k} re ⟪(S - T) bⱼ, bⱼ⟫ ≤ k C² / δ`.

This is the quantitative form of the differentiability of `κₖ` at `T` (Lewis 1996, Theorem 2.1):
the derivative `H ↦ ∑_{j < k} re ⟪H bⱼ, bⱼ⟫` is the trace of `H` against the spectral projection
onto the span of the leading eigenvectors, and the remainder is quadratic in the operator norm of
`S - T`. For Hermitian matrices the derivative statement is
`Matrix.hasFDerivAt_prefixSum_eigenvalues₀`. Without a gap `κₖ` need not be differentiable:
`κ₁ = λ₀` is not differentiable at the identity of a space of dimension at least two.

The lower bound is Ky Fan's maximum principle for `S`, evaluated on `b₀, …, bₖ₋₁`. For the upper
bound, let `w₀, …, wₖ₋₁` be leading eigenvectors of `S`, so that `κₖ(S) = ∑ᵢ re ⟪S wᵢ, wᵢ⟫`, and let
`d = ∑ᵢ ∑_{j ≥ k} ‖⟪bⱼ, wᵢ⟫‖²` be the mass that the family `w` places outside the leading block of
`T`. The gap sharpens Ky Fan's maximum principle to

`∑ᵢ re ⟪T wᵢ, wᵢ⟫ + δ d ≤ κₖ(T)`

(`LinearMap.sum_re_inner_apply_self_add_mul_le_prefixSum`), so a family that nearly attains `κₖ(T)`
nearly spans the leading eigenspace; at `d = 0` this is the uniqueness of the maximizing subspace
(`LinearMap.inner_eq_zero_of_sum_re_inner_apply_self_eq_prefixSum`). On the other hand, the diagonal
sums of `H = S - T` along `w` and along `b₀, …, bₖ₋₁` differ by inner products against the
components of the two families orthogonal to each other's span, whose squared norms add up to `d`
on each side; with `2 C x ≤ δ x² + C² / δ` the difference is at most `δ d + k C² / δ`. The two
`δ d` terms cancel.

## Main results

* `LinearMap.sum_re_inner_apply_self_add_mul_le_prefixSum`: Ky Fan's maximum principle sharpened
  by a spectral gap.
* `LinearMap.inner_eq_zero_of_sum_re_inner_apply_self_eq_prefixSum`: an orthonormal family attaining
  the sum of the `k` leading eigenvalues lies in the span of the leading eigenvectors.
* `LinearMap.IsSymmetric.prefixSum_add_sum_re_inner_apply_self_le_prefixSum_eigenvalues`: the
  lower bound `μ₀ + ⋯ + μₖ₋₁ + ∑_{j < k} re ⟪(S - T) bⱼ, bⱼ⟫ ≤ κₖ(S)`, which needs no gap.
* `LinearMap.IsSymmetric.prefixSum_eigenvalues_le_prefixSum_add_sum_re_inner_apply_self_add`:
  the upper bound with the quadratic remainder `k C² / δ`.
* `LinearMap.IsSymmetric.abs_prefixSum_eigenvalues_sub_le`: both bounds together.

## References

* A. S. Lewis, *Derivatives of spectral functions*, Math. Oper. Res. **21** (1996), 576–588,
  Theorem 2.1.
* K. Fan, *On a theorem of Weyl concerning eigenvalues of linear transformations I*, Proc. Nat.
  Acad. Sci. U.S.A. **35** (1949), 652–655.
-/

public section

open Module Finset TauCeti

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- An orthonormal family with `k` members in a space with an orthonormal basis indexed by `Fin n`
has `k ≤ n`. -/
private theorem le_of_orthonormal (b : OrthonormalBasis (Fin n) 𝕜 E) {k : ℕ} {w : Fin k → E}
    (hw : Orthonormal 𝕜 w) : k ≤ n := by
  simpa using (hw.sum_sum_sq_norm_inner_eq_card b).symm.trans_le
    (sum_le_card_nsmul _ _ 1 fun j _ ↦ hw.sum_sq_norm_inner_left_le_one (b.orthonormal.1 j))

/-- For `k ≤ n`, exactly `k` indices `j : Fin n` satisfy `j < k`. -/
private theorem card_filter_val_lt_eq {k : ℕ} (hkn : k ≤ n) :
    (#{j : Fin n | j.val < k} : ℝ) = k := by
  simp [Fin.card_filter_val_lt, hkn]

/-- **Ky Fan's maximum principle sharpened by a spectral gap.** Let `b` be an orthonormal eigenbasis
of `T` with eigenvalues `μ`, whose first `k` eigenvalues exceed the others by at least `δ`. For an
orthonormal family `w` with `k` members, the diagonal sum `∑ᵢ re ⟪T wᵢ, wᵢ⟫` falls short of
`μ₀ + ⋯ + μₖ₋₁` by at least `δ` times the mass `∑ᵢ ∑_{j ≥ k} ‖⟪bⱼ, wᵢ⟫‖²` of `w` outside the
leading eigenvectors. -/
theorem sum_re_inner_apply_self_add_mul_le_prefixSum (T : E →ₗ[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ} (hb : ∀ j, T (b j) = (μ j : 𝕜) • b j)
    {k : ℕ} {δ : ℝ} (hgap : ∀ i j : Fin n, (i : ℕ) < k → k ≤ (j : ℕ) → μ j + δ ≤ μ i)
    {w : Fin k → E} (hw : Orthonormal 𝕜 w) :
    ∑ i, RCLike.re ⟪T (w i), w i⟫ + δ * ∑ i, ∑ j : Fin n with k ≤ j.val, ‖⟪b j, w i⟫‖ ^ 2 ≤
      prefixSum k μ := by
  have hkn := le_of_orthonormal b hw
  have hc1 (j : Fin n) : ∑ i, ‖⟪b j, w i⟫‖ ^ 2 ≤ 1 :=
    hw.sum_sq_norm_inner_left_le_one (b.orthonormal.1 j)
  have hmass := hw.sum_sum_sq_norm_inner_eq_card b
  rw [Fintype.card_fin] at hmass
  set c : Fin n → ℝ := fun j ↦ ∑ i, ‖⟪b j, w i⟫‖ ^ 2 with hc
  have hc0 (j : Fin n) : 0 ≤ c j := by positivity
  have hsum : ∑ i, RCLike.re ⟪T (w i), w i⟫ = ∑ j, μ j * c j := by
    simp_rw [re_inner_apply_self_eq_sum_of_eigenbasis T b hb, OrthonormalBasis.repr_apply_apply,
      hc, mul_sum]
    exact sum_comm
  rw [hsum, sum_comm, prefixSum_def,
    ← sum_filter_add_sum_filter_not univ (fun j : Fin n ↦ (j : ℕ) < k) (fun j ↦ μ j * c j)]
  simp only [not_lt]
  rw [← sum_filter_add_sum_filter_not univ (fun j : Fin n ↦ (j : ℕ) < k) c] at hmass
  simp only [not_lt] at hmass
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [hc]
  obtain ⟨i₀, hi₀, hmin⟩ := (univ.filter fun j : Fin n ↦ (j : ℕ) < k).exists_min_image μ
    ⟨⟨0, hk0.trans_le hkn⟩, by simpa using hk0⟩
  have h₁ : ∑ j : Fin n with j.val < k, μ i₀ * (1 - c j) ≤
      ∑ j : Fin n with j.val < k, μ j * (1 - c j) :=
    sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_right (hmin j hj) (sub_nonneg.2 (hc1 j))
  have h₂ : ∑ j : Fin n with k ≤ j.val, (μ j + δ) * c j ≤
      ∑ j : Fin n with k ≤ j.val, μ i₀ * c j :=
    sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_right
      (hgap i₀ j (mem_filter.1 hi₀).2 (mem_filter.1 hj).2) (hc0 j)
  have hconst : ∑ j : Fin n with j.val < k, μ i₀ = μ i₀ * k := by
    rw [sum_const, nsmul_eq_mul, card_filter_val_lt_eq hkn, mul_comm]
  simp only [mul_sub, mul_one, sum_sub_distrib, add_mul, sum_add_distrib, ← mul_sum, hconst]
    at h₁ h₂
  have hm := congrArg (fun t ↦ μ i₀ * t) hmass
  simp only [mul_add] at hm
  simp only [hc] at h₁ h₂ hm ⊢
  linarith

/-- **Uniqueness of the maximizing subspace at a spectral gap.** If the first `k` eigenvalues `μ`
of `T` along an orthonormal eigenbasis `b` exceed the others by some `δ > 0`, then an orthonormal
family `w` with `k` members whose diagonal sum `∑ᵢ re ⟪T wᵢ, wᵢ⟫` attains `μ₀ + ⋯ + μₖ₋₁` is
orthogonal to every `bⱼ` with `j ≥ k`, that is, it lies in the span of the leading eigenvectors
`b₀, …, bₖ₋₁`. -/
theorem inner_eq_zero_of_sum_re_inner_apply_self_eq_prefixSum (T : E →ₗ[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ} (hb : ∀ j, T (b j) = (μ j : 𝕜) • b j)
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j : Fin n, (i : ℕ) < k → k ≤ (j : ℕ) → μ j + δ ≤ μ i)
    {w : Fin k → E} (hw : Orthonormal 𝕜 w)
    (hmax : ∑ i, RCLike.re ⟪T (w i), w i⟫ = prefixSum k μ) (i : Fin k) {j : Fin n}
    (hj : k ≤ (j : ℕ)) : ⟪b j, w i⟫ = 0 := by
  have h := sum_re_inner_apply_self_add_mul_le_prefixSum T b hb hgap hw
  rw [hmax, add_le_iff_nonpos_right] at h
  have hd : ∑ i, ∑ j : Fin n with k ≤ j.val, ‖⟪b j, w i⟫‖ ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h hδ) (by positivity)
  rw [sum_eq_zero_iff_of_nonneg fun _ _ ↦ by positivity] at hd
  have hd' := hd i (mem_univ i)
  rw [sum_eq_zero_iff_of_nonneg fun _ _ ↦ by positivity] at hd'
  simpa using hd' j (mem_filter.2 ⟨mem_univ j, hj⟩)

/-- Exchanging the diagonal sum of `H` along a family `w` for its diagonal sum along the members
`vⱼ`, `j ∈ s`, of another family: the error consists of `H` paired with the component
`wᵢ - ∑_{j ∈ s} ⟪vⱼ, wᵢ⟫ vⱼ` of each `wᵢ` off the `vⱼ`, and with the component
`vⱼ - ∑ᵢ ⟪wᵢ, vⱼ⟫ wᵢ` of each `vⱼ` off the `wᵢ`. -/
private theorem sum_inner_apply_eq {ι κ : Type*} [Fintype ι] (H : E →ₗ[𝕜] E) (w : ι → E)
    (v : κ → E) (s : Finset κ) :
    ∑ i, ⟪H (w i), w i⟫ = ∑ j ∈ s, ⟪H (v j), v j⟫ -
      ∑ j ∈ s, ⟪H (v j), v j - ∑ i, ⟪w i, v j⟫ • w i⟫ +
      ∑ i, ⟪H (w i - ∑ j ∈ s, ⟪v j, w i⟫ • v j), w i⟫ := by
  have hswap : ∑ i, ⟪H (∑ j ∈ s, ⟪v j, w i⟫ • v j), w i⟫ =
      ∑ j ∈ s, ⟪H (v j), ∑ i, ⟪w i, v j⟫ • w i⟫ := by
    simp only [map_sum, map_smul, sum_inner, inner_smul_left, inner_conj_symm, inner_sum,
      inner_smul_right]
    rw [sum_comm]
  simp only [map_sub, inner_sub_left, inner_sub_right, sum_sub_distrib, hswap]
  abel

/-- The components of the members of an orthonormal family `w` with `k` members off the first `k`
members of an orthonormal basis `b`, and the components of those `bⱼ` off the `wᵢ`, both have total
squared norm `∑ᵢ ∑_{j ≥ k} ‖⟪bⱼ, wᵢ⟫‖²`. -/
private theorem sum_sq_norm_components_eq (b : OrthonormalBasis (Fin n) 𝕜 E) {k : ℕ}
    {w : Fin k → E} (hw : Orthonormal 𝕜 w) :
    ∑ i, ‖w i - ∑ j : Fin n with j.val < k, ⟪b j, w i⟫ • b j‖ ^ 2 =
        ∑ i, ∑ j : Fin n with k ≤ j.val, ‖⟪b j, w i⟫‖ ^ 2 ∧
      ∑ j : Fin n with j.val < k, ‖b j - ∑ i, ⟪w i, b j⟫ • w i‖ ^ 2 =
        ∑ i, ∑ j : Fin n with k ≤ j.val, ‖⟪b j, w i⟫‖ ^ 2 := by
  refine ⟨sum_congr rfl fun i _ ↦ ?_, ?_⟩
  · rw [b.orthonormal.norm_sub_sum_inner_smul_sq, ← b.sum_sq_norm_inner_right (w i),
      ← sum_filter_add_sum_filter_not univ (fun j : Fin n ↦ (j : ℕ) < k)]
    simp
  · have hmass := hw.sum_sum_sq_norm_inner_eq_card b
    rw [Fintype.card_fin] at hmass
    have h₁ (j : Fin n) : ‖b j - ∑ i, ⟪w i, b j⟫ • w i‖ ^ 2 = 1 - ∑ i, ‖⟪b j, w i⟫‖ ^ 2 := by
      simp only [hw.norm_sub_sum_inner_smul_sq, b.orthonormal.1 j, one_pow, norm_inner_symm]
    rw [sum_congr rfl fun j _ ↦ h₁ j, sum_sub_distrib, sum_const, nsmul_one,
      card_filter_val_lt_eq (le_of_orthonormal b hw)]
    conv_rhs => rw [sum_comm]
    rw [← sum_filter_add_sum_filter_not univ (fun j : Fin n ↦ (j : ℕ) < k)] at hmass
    simp only [not_lt] at hmass
    linarith

/-- A pairing `z = ⟪p, q⟫` with `‖p‖ ‖q‖ ≤ a C` satisfies `2 |re z| ≤ δ a² + C² / δ`: the
per-component bound in the exchange estimate. -/
private theorem two_mul_abs_re_inner_le {p q : E} {a C δ : ℝ} (hδ : 0 < δ)
    (h : ‖p‖ * ‖q‖ ≤ a * C) : 2 * |RCLike.re ⟪p, q⟫| ≤ δ * a ^ 2 + δ⁻¹ * C ^ 2 := by
  refine le_trans ?_ (two_mul_le_add_mul_sq hδ)
  rw [mul_assoc]
  gcongr
  exact ((RCLike.abs_re_le_norm _).trans (norm_inner_le_norm _ _)).trans h

/-- The diagonal sums of `H` along an orthonormal family `w` with `k` members and along the first
`k` members of an orthonormal basis `b` differ by at most `δ d + k C² / δ`, where `C` bounds `H` and
`d = ∑ᵢ ∑_{j ≥ k} ‖⟪bⱼ, wᵢ⟫‖²` is the mass of `w` outside the span of `b₀, …, bₖ₋₁`. -/
private theorem sum_re_inner_apply_self_le_add (H : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E)
    {k : ℕ} {w : Fin k → E} (hw : Orthonormal 𝕜 w) {C δ : ℝ} (hδ : 0 < δ)
    (hC : ∀ x, ‖H x‖ ≤ C * ‖x‖) :
    ∑ i, RCLike.re ⟪H (w i), w i⟫ ≤ ∑ j : Fin n with j.val < k, RCLike.re ⟪H (b j), b j⟫ +
      δ * ∑ i, ∑ j : Fin n with k ≤ j.val, ‖⟪b j, w i⟫‖ ^ 2 + k * C ^ 2 / δ := by
  obtain ⟨hnr, hns⟩ := sum_sq_norm_components_eq b hw
  set L := univ.filter fun j : Fin n ↦ (j : ℕ) < k
  -- `rᵢ` is the component of `wᵢ` off `b₀, …, bₖ₋₁`, and `sⱼ` the component of `bⱼ` off the `wᵢ`.
  set r : Fin k → E := fun i ↦ w i - ∑ j ∈ L, ⟪b j, w i⟫ • b j
  set s : Fin n → E := fun j ↦ b j - ∑ i, ⟪w i, b j⟫ • w i
  -- Restate the norm identities in terms of the named components.
  rw [show (fun i ↦ ‖w i - ∑ j ∈ L, ⟪b j, w i⟫ • b j‖ ^ 2) = fun i ↦ ‖r i‖ ^ 2 from rfl] at hnr
  rw [show (fun j ↦ ‖b j - ∑ i, ⟪w i, b j⟫ • w i‖ ^ 2) = fun j ↦ ‖s j‖ ^ 2 from rfl] at hns
  -- Each component `x` contributes at most `C ‖x‖ ≤ (δ ‖x‖² + δ⁻¹ C²) / 2`.
  have hri (i : Fin k) : 2 * RCLike.re ⟪H (r i), w i⟫ ≤ δ * ‖r i‖ ^ 2 + δ⁻¹ * C ^ 2 :=
    le_trans (by gcongr; exact le_abs_self _) <| two_mul_abs_re_inner_le hδ <| by
      rw [hw.1 i, mul_one, mul_comm]; exact hC _
  have hsj (j : Fin n) : 2 * -RCLike.re ⟪H (b j), s j⟫ ≤ δ * ‖s j‖ ^ 2 + δ⁻¹ * C ^ 2 :=
    le_trans (by gcongr; exact neg_le_abs _) <| two_mul_abs_re_inner_le hδ <| by
      rw [mul_comm]
      gcongr
      simpa [b.orthonormal.1 j] using hC (b j)
  have hcardL : (#L : ℝ) = k := card_filter_val_lt_eq (le_of_orthonormal b hw)
  have hR := sum_le_sum fun i (_ : i ∈ univ) ↦ hri i
  have hS := sum_le_sum fun j (_ : j ∈ L) ↦ hsj j
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_neg_distrib, hnr, hns, hcardL] at hR hS
  have hre := congrArg RCLike.re (sum_inner_apply_eq H w b L)
  rw [map_add, map_sub] at hre
  simp only [map_sum] at hre
  rw [hre]
  have hfin : (k : ℝ) * (δ⁻¹ * C ^ 2) = k * C ^ 2 / δ := by ring
  linarith

namespace IsSymmetric

variable [FiniteDimensional 𝕜 E] {S T : E →ₗ[𝕜] E}

/-- **The tangent lower bound for Ky Fan sums.** If `b` is an orthonormal eigenbasis of `T` with
eigenvalues `μ`, then for every symmetric `S` the sum of the `k` largest eigenvalues of `S` is at
least `μ₀ + ⋯ + μₖ₋₁ + ∑_{j < k} re ⟪(S - T) bⱼ, bⱼ⟫`. No spectral gap is needed. -/
theorem prefixSum_add_sum_re_inner_apply_self_le_prefixSum_eigenvalues (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ}
    (hb : ∀ j, T (b j) = (μ j : 𝕜) • b j) {k : ℕ} (hkn : k ≤ n) :
    prefixSum k μ + ∑ j : Fin n with j.val < k, RCLike.re ⟪(S - T) (b j), b j⟫ ≤
      prefixSum k (hS.eigenvalues hn) := by
  have h := hS.sum_re_inner_apply_self_le_sum_eigenvalues hn
    (b.orthonormal.comp _ (Fin.castLE_injective hkn))
  rw [Fintype.card_fin, ← prefixSum_def] at h
  refine le_trans (le_of_eq ?_) h
  have hdiag (j : Fin n) : RCLike.re ⟪S (b j), b j⟫ = μ j + RCLike.re ⟪(S - T) (b j), b j⟫ := by
    rw [LinearMap.sub_apply, inner_sub_left, map_sub, hb, inner_smul_left,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1 j]
    simp
  calc prefixSum k μ + ∑ j : Fin n with j.val < k, RCLike.re ⟪(S - T) (b j), b j⟫
      = prefixSum k fun j ↦ RCLike.re ⟪S (b j), b j⟫ := by
        rw [prefixSum_def, prefixSum_def, ← sum_add_distrib]
        exact sum_congr rfl fun j _ ↦ (hdiag j).symm
    _ = _ := prefixSum_eq_sum_castLE hkn _

/-- **The quadratic upper bound for Ky Fan sums at a spectral gap.** Let `b` be an orthonormal
eigenbasis of `T` with eigenvalues `μ`, whose first `k` eigenvalues exceed the others by at least
`δ > 0`. If `S` is symmetric and `‖(S - T) x‖ ≤ C ‖x‖` for all `x`, then the sum of the `k` largest
eigenvalues of `S` is at most `μ₀ + ⋯ + μₖ₋₁ + ∑_{j < k} re ⟪(S - T) bⱼ, bⱼ⟫ + k C² / δ`. -/
theorem prefixSum_eigenvalues_le_prefixSum_add_sum_re_inner_apply_self_add (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ}
    (hb : ∀ j, T (b j) = (μ j : 𝕜) • b j) {k : ℕ} (hkn : k ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j : Fin n, (i : ℕ) < k → k ≤ (j : ℕ) → μ j + δ ≤ μ i) {C : ℝ}
    (hC : ∀ x, ‖(S - T) x‖ ≤ C * ‖x‖) :
    prefixSum k (hS.eigenvalues hn) ≤
      prefixSum k μ + ∑ j : Fin n with j.val < k, RCLike.re ⟪(S - T) (b j), b j⟫ +
        k * C ^ 2 / δ := by
  -- The leading eigenvectors of `S` attain its Ky Fan sum.
  set w : Fin k → E := fun i ↦ hS.eigenvectorBasis hn (Fin.castLE hkn i) with hw
  have hwo : Orthonormal 𝕜 w := (hS.eigenvectorBasis hn).orthonormal.comp _
    (Fin.castLE_injective hkn)
  have hκ : prefixSum k (hS.eigenvalues hn) =
      ∑ i, RCLike.re ⟪T (w i), w i⟫ + ∑ i, RCLike.re ⟪(S - T) (w i), w i⟫ := by
    rw [prefixSum_eq_sum_castLE hkn, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← map_add, ← inner_add_left, ← LinearMap.add_apply, add_sub_cancel, hw,
      hS.re_inner_apply_eigenvectorBasis hn]
  have hA := sum_re_inner_apply_self_add_mul_le_prefixSum T b hb hgap hwo
  have hB := sum_re_inner_apply_self_le_add (S - T) b hwo hδ hC
  rw [hκ]
  linarith

/-- **First-order expansion of Ky Fan sums at a spectral gap.** Let `b` be an orthonormal
eigenbasis of `T` with eigenvalues `μ`, whose first `k` eigenvalues exceed the others by at least
`δ > 0`. If `S` is symmetric and `‖(S - T) x‖ ≤ C ‖x‖` for all `x`, then the sum of the `k` largest
eigenvalues of `S` differs from its tangent approximation
`μ₀ + ⋯ + μₖ₋₁ + ∑_{j < k} re ⟪(S - T) bⱼ, bⱼ⟫` by at most `k C² / δ`. -/
theorem abs_prefixSum_eigenvalues_sub_le (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ} (hb : ∀ j, T (b j) = (μ j : 𝕜) • b j)
    {k : ℕ} (hkn : k ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j : Fin n, (i : ℕ) < k → k ≤ (j : ℕ) → μ j + δ ≤ μ i) {C : ℝ}
    (hC : ∀ x, ‖(S - T) x‖ ≤ C * ‖x‖) :
    |prefixSum k (hS.eigenvalues hn) - prefixSum k μ -
        ∑ j : Fin n with j.val < k, RCLike.re ⟪(S - T) (b j), b j⟫| ≤ k * C ^ 2 / δ := by
  have h₁ := hS.prefixSum_add_sum_re_inner_apply_self_le_prefixSum_eigenvalues hn b hb hkn
  have h₂ :=
    hS.prefixSum_eigenvalues_le_prefixSum_add_sum_re_inner_apply_self_add hn b hb hkn hδ hgap hC
  rw [abs_le]
  constructor <;> linarith [show 0 ≤ k * C ^ 2 / δ by positivity]

end IsSymmetric

end LinearMap
