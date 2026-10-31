/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.InnerProductSup
import TauCeti.Probability.Distributions.Gaussian.L2

/-!
# Grothendieck's inequality for matrices

Let `a` be a finite scalar matrix with `|∑ i, ∑ j, a i j * s i * t j| ≤ C` whenever all scalars
`s i`, `t j` have absolute value at most one. Grothendieck's inequality bounds
`|∑ i, ∑ j, a i j * ⟪u i, v j⟫|` by a universal constant times `C`, for all families of vectors of
norm at most one in any inner product space. We prove it with the constants `κ_ℝ = 8` over the
reals and `κ_𝕜 = 16` over any `RCLike` field; these constants are not optimal.

## The real case

The proof is the Gaussian truncation argument. By `Matrix.innerProductSup_le_iff` it suffices to
treat a finite-dimensional real inner product space `E`. Its vectors embed isometrically into
`L²` of the standard Gaussian measure on `E` by `TauCeti.Probability.gaussianL2`; write `uᴹ` for
the observable of `u` clipped at height `M > 0`. Splitting
`⟪u, v⟫ = ⟪uᴹ, vᴹ⟫ + ⟪uᴹ, v - vᴹ⟫ + ⟪u - uᴹ, v⟫` in `L²`:

* the first part is the integral of `∑ i, ∑ j, a i j * uᵢᴹ(y) * vⱼᴹ(y)`, which is at most
  `C * M ^ 2` pointwise because the clipped observables are bounded by `M`;
* the clipping errors have `L²` norm at most `√3 / (4 * M)`, so the other two parts are bounded
  through `Γ(a) = Matrix.innerProductSup a`, which applies in every real inner product space.

This gives the absorption inequality `Γ(a) ≤ C * M ^ 2 + Γ(a) * √3 / (2 * M)`
(`Matrix.innerProductSup_le_mul_sq_add`); at `M = 2` it yields `Γ(a) ≤ 8 * C`.

## The `RCLike` case

Over an `RCLike` field, rotate the sum by a scalar `ω` of norm at most one to make it real and
nonnegative, and regard the space as a real inner product space via
`InnerProductSpace.rclikeToReal`. The real part of the rotated sum is the sum of two real
bilinear expressions, with coefficient matrices `re (ω * a i j)` and `im (ω * a i j)`, both of
which inherit the scalar bound `C`. Applying the real inequality twice gives `16 * C`.

## Main declarations

* `Matrix.abs_sum_sum_mul_mul_le_mul_sq`: the scalar bound rescaled to scalars bounded by `M`.
* `Matrix.innerProductSup_le_mul_sq_add`: the absorption inequality.
* `Matrix.innerProductSup_le_eight_mul`: `Γ(a) ≤ 8 * C`.
* `Matrix.abs_sum_sum_mul_inner_le_eight_mul`: the real Grothendieck inequality in any real inner
  product space.
* `Matrix.abs_sum_sum_map_mul_mul_mul_le`: real-linear images of a rotated `RCLike` matrix inherit
  its scalar bound.
* `Matrix.norm_sum_sum_mul_inner_le_sixteen_mul`: the Grothendieck inequality over `RCLike`
  scalars, in any inner product space.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped InnerProductSpace

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A bound `C` on `|∑ i, ∑ j, a i j * s i * t j|` for scalars of absolute value at most one
rescales to the bound `C * M ^ 2` for scalars of absolute value at most `M > 0`. -/
theorem abs_sum_sum_mul_mul_le_mul_sq (a : Matrix ι κ ℝ) {C : ℝ}
    (h : ∀ (s : ι → ℝ) (t : κ → ℝ), (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) →
      |∑ i, ∑ j, a i j * s i * t j| ≤ C)
    {M : ℝ} (hM : 0 < M) {s : ι → ℝ} {t : κ → ℝ} (hs : ∀ i, |s i| ≤ M)
    (ht : ∀ j, |t j| ≤ M) :
    |∑ i, ∑ j, a i j * s i * t j| ≤ C * M ^ 2 := by
  have hdiv {x : ℝ} (hx : |x| ≤ M) : |x / M| ≤ 1 := by
    rwa [abs_div, abs_of_pos hM, div_le_one hM]
  have key := h (fun i ↦ s i / M) (fun j ↦ t j / M) (fun i ↦ hdiv (hs i)) (fun j ↦ hdiv (ht j))
  have hsum : ∑ i, ∑ j, a i j * (s i / M) * (t j / M) =
      (∑ i, ∑ j, a i j * s i * t j) / M ^ 2 := by
    simp only [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      field_simp
  rw [hsum, abs_div, abs_of_pos (pow_pos hM 2), div_le_iff₀ (pow_pos hM 2)] at key
  exact key

/-- The Gaussian truncation estimate in a finite-dimensional real inner product space. -/
private theorem abs_sum_sum_mul_inner_le_mul_sq_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : Matrix ι κ ℝ) {C : ℝ}
    (h : ∀ (s : ι → ℝ) (t : κ → ℝ), (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) →
      |∑ i, ∑ j, a i j * s i * t j| ≤ C)
    {M : ℝ} (hM : 0 < M) {u : ι → E} {v : κ → E} (hu : ∀ i, ‖u i‖ ≤ 1)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ| ≤ C * M ^ 2 + a.innerProductSup * √3 / (2 * M) := by
  borelize E
  set f : ι → Lp ℝ 2 (stdGaussian E) := fun i ↦ clippedGaussianL2 (u i) M
  set g : κ → Lp ℝ 2 (stdGaussian E) := fun j ↦ clippedGaussianL2 (v j) M
  set G : E →ₗᵢ[ℝ] Lp ℝ 2 (stdGaussian E) := gaussianL2
  -- Split each inner product along the clipping.
  have hsplit : ∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ =
      ∑ i, ∑ j, a i j * ⟪f i, g j⟫_ℝ + ∑ i, ∑ j, a i j * ⟪f i, G (v j) - g j⟫_ℝ +
        ∑ i, ∑ j, a i j * ⟪G (u i) - f i, G (v j)⟫_ℝ := by
    simp only [← Finset.sum_add_distrib, ← mul_add, inner_sub_left, inner_sub_right,
      LinearIsometry.inner_map_map]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- The clipped part is the integral of a scalar bilinear sum bounded by `C * M ^ 2`.
  have hmain : |∑ i, ∑ j, a i j * ⟪f i, g j⟫_ℝ| ≤ C * M ^ 2 := by
    have hint (i : ι) (j : κ) :
        Integrable (fun y ↦ a i j * ⟪f i y, g j y⟫_ℝ) (stdGaussian E) :=
      (L2.integrable_inner (f i) (g j)).const_mul _
    have heq : ∑ i, ∑ j, a i j * ⟪f i, g j⟫_ℝ =
        ∫ y, ∑ i, ∑ j, a i j * ⟪f i y, g j y⟫_ℝ ∂stdGaussian E := by
      rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_finsetSum _ fun j _ ↦ hint i j]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [L2.inner_def, integral_const_mul]
    rw [heq, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := C * M ^ 2) ?_).trans_eq (by simp)
    filter_upwards [ae_all_iff.2 fun i ↦ ae_abs_clippedGaussianL2_le (u i) M hM.le,
      ae_all_iff.2 fun j ↦ ae_abs_clippedGaussianL2_le (v j) M hM.le] with y hfy hgy
    simpa only [Real.norm_eq_abs, Real.inner_apply, mul_assoc] using
      a.abs_sum_sum_mul_mul_le_mul_sq h hM hfy hgy
  -- The two error parts are controlled by `Γ(a)` and the clipping error.
  have hδ : 0 ≤ √3 / (4 * M) := by positivity
  have herr₁ := a.abs_sum_sum_mul_inner_le_innerProductSup_mul_mul zero_le_one hδ
    (u := f) (v := fun j ↦ G (v j) - g j)
    (fun i ↦ (norm_clippedGaussianL2_le (u i) M hM.le).trans (hu i))
    (fun j ↦ norm_sub_clippedGaussianL2_le_of_norm_le_one (hv j) hM)
  have herr₂ := a.abs_sum_sum_mul_inner_le_innerProductSup_mul_mul hδ zero_le_one
    (u := fun i ↦ G (u i) - f i) (v := fun j ↦ G (v j))
    (fun i ↦ norm_sub_clippedGaussianL2_le_of_norm_le_one (hu i) hM)
    (fun j ↦ (G.norm_map (v j)).trans_le (hv j))
  rw [hsplit]
  refine (abs_add_le _ _).trans <| (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  have hΓ : a.innerProductSup * √3 / (2 * M) =
      a.innerProductSup * 1 * (√3 / (4 * M)) + a.innerProductSup * (√3 / (4 * M)) * 1 := by
    field_simp
    ring
  rw [hΓ]
  linarith

/-- The absorption inequality of the Gaussian truncation proof of Grothendieck's inequality: if
`|∑ i, ∑ j, a i j * s i * t j| ≤ C` for all scalars of absolute value at most one, then
`Γ(a) ≤ C * M ^ 2 + Γ(a) * √3 / (2 * M)` for every clipping height `M > 0`. -/
theorem innerProductSup_le_mul_sq_add (a : Matrix ι κ ℝ) {C : ℝ}
    (h : ∀ (s : ι → ℝ) (t : κ → ℝ), (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) →
      |∑ i, ∑ j, a i j * s i * t j| ≤ C)
    {M : ℝ} (hM : 0 < M) :
    a.innerProductSup ≤ C * M ^ 2 + a.innerProductSup * √3 / (2 * M) :=
  innerProductSup_le_iff.2 fun _ _ hu hv ↦ a.abs_sum_sum_mul_inner_le_mul_sq_add h hM hu hv

/-- **Grothendieck's inequality** in terms of `Γ(a) = Matrix.innerProductSup a`: if
`|∑ i, ∑ j, a i j * s i * t j| ≤ C` for all real scalars of absolute value at most one, then
`Γ(a) ≤ 8 * C`. -/
theorem innerProductSup_le_eight_mul (a : Matrix ι κ ℝ) {C : ℝ}
    (h : ∀ (s : ι → ℝ) (t : κ → ℝ), (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) →
      |∑ i, ∑ j, a i j * s i * t j| ≤ C) :
    a.innerProductSup ≤ 8 * C := by
  have habs := a.innerProductSup_le_mul_sq_add h two_pos
  have hsqrt : √3 ≤ 2 := Real.sqrt_le_iff.2 ⟨zero_le_two, by norm_num⟩
  nlinarith [mul_le_mul_of_nonneg_left hsqrt a.innerProductSup_nonneg]

/-- **Grothendieck's inequality** over the reals, with constant `κ_ℝ = 8`: if
`|∑ i, ∑ j, a i j * s i * t j| ≤ C` for all real scalars of absolute value at most one, then
`|∑ i, ∑ j, a i j * ⟪u i, v j⟫| ≤ 8 * C` for all families of vectors of norm at most one in any
real inner product space. -/
theorem abs_sum_sum_mul_inner_le_eight_mul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : Matrix ι κ ℝ) {C : ℝ}
    (h : ∀ (s : ι → ℝ) (t : κ → ℝ), (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) →
      |∑ i, ∑ j, a i j * s i * t j| ≤ C)
    {u : ι → E} {v : κ → E} (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ| ≤ 8 * C :=
  (a.abs_sum_sum_mul_inner_le_innerProductSup hu hv).trans (a.innerProductSup_le_eight_mul h)

variable {𝕜 : Type*} [RCLike 𝕜]

/-- If `‖∑ i, ∑ j, a i j * s i * t j‖ ≤ C` for all scalars of norm at most one, then for every
`ω` of norm at most one and every real-linear functional `φ` with `|φ z| ≤ ‖z‖` (such as `re` or
`im`), the real matrix `φ (ω * a i j)` satisfies the same bound `C` on real scalars of absolute
value at most one. -/
theorem abs_sum_sum_map_mul_mul_mul_le (a : Matrix ι κ 𝕜) {C : ℝ}
    (h : ∀ (s : ι → 𝕜) (t : κ → 𝕜), (∀ i, ‖s i‖ ≤ 1) → (∀ j, ‖t j‖ ≤ 1) →
      ‖∑ i, ∑ j, a i j * s i * t j‖ ≤ C)
    {ω : 𝕜} (hω : ‖ω‖ ≤ 1) (φ : 𝕜 →L[ℝ] ℝ) (hφ : ∀ z, |φ z| ≤ ‖z‖) {s : ι → ℝ}
    {t : κ → ℝ} (hs : ∀ i, |s i| ≤ 1) (ht : ∀ j, |t j| ≤ 1) :
    |∑ i, ∑ j, φ (ω * a i j) * s i * t j| ≤ C := by
  have heq : ∑ i, ∑ j, φ (ω * a i j) * s i * t j =
      φ (ω * ∑ i, ∑ j, a i j * (s i : 𝕜) * (t j : 𝕜)) := by
    simp only [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    -- Write the summand as a real scalar action, so that the real-linearity of `φ` applies.
    rw [show ω * (a i j * (s i : 𝕜) * (t j : 𝕜)) = (s i * t j) • (ω * a i j) by
      simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_mul]; ring, map_smul, smul_eq_mul]
    ring
  rw [heq]
  refine (hφ _).trans <| (norm_mul_le _ _).trans <| (mul_le_mul hω
    (h _ _ (fun i ↦ by simpa using hs i) (fun j ↦ by simpa using ht j)) (norm_nonneg _)
    zero_le_one).trans_eq (one_mul C)

/-- **Grothendieck's inequality** over an `RCLike` field, with constant `κ_𝕜 = 16`: if
`‖∑ i, ∑ j, a i j * s i * t j‖ ≤ C` for all scalars of norm at most one, then
`‖∑ i, ∑ j, a i j * ⟪u i, v j⟫‖ ≤ 16 * C` for all families of vectors of norm at most one in any
inner product space over `𝕜`. Over `ℝ`, `Matrix.abs_sum_sum_mul_inner_le_eight_mul` gives the
constant `8`. -/
theorem norm_sum_sum_mul_inner_le_sixteen_mul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (a : Matrix ι κ 𝕜) {C : ℝ}
    (h : ∀ (s : ι → 𝕜) (t : κ → 𝕜), (∀ i, ‖s i‖ ≤ 1) → (∀ j, ‖t j‖ ≤ 1) →
      ‖∑ i, ∑ j, a i j * s i * t j‖ ≤ C)
    {u : ι → E} {v : κ → E} (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    ‖∑ i, ∑ j, a i j * ⟪u i, v j⟫_𝕜‖ ≤ 16 * C := by
  set z := ∑ i, ∑ j, a i j * ⟪u i, v j⟫_𝕜
  -- Rotate `z` onto the nonnegative real axis by a unit scalar `ω`.
  obtain ⟨ω, hω₁, hz⟩ := RCLike.exists_norm_eq_mul_self z
  have hω : ‖ω‖ ≤ 1 := hω₁.le
  have hωz : ‖z‖ = RCLike.re (ω * z) := by
    rw [← hz, RCLike.ofReal_re]
  -- Regard `E` as a real inner product space and split the real part of the rotated sum.
  let _ : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  have hre (x y : E) : ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜 := real_inner_eq_re_inner 𝕜 x y
  have hsplit : RCLike.re (ω * z) =
      ∑ i, ∑ j, RCLike.re (ω * a i j) * ⟪u i, v j⟫_ℝ +
        ∑ i, ∑ j, RCLike.im (ω * a i j) * ⟪u i, (RCLike.I : 𝕜) • v j⟫_ℝ := by
    simp only [z, Finset.mul_sum, map_sum, ← Finset.sum_add_distrib, hre, inner_smul_right,
      RCLike.I_mul_re]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_assoc, RCLike.mul_re]
    ring
  have hIv (j : κ) : ‖(RCLike.I : 𝕜) • v j‖ ≤ 1 := by
    rw [norm_smul]
    have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
      rw [RCLike.norm_I]
      split_ifs <;> norm_num
    exact (mul_le_mul hI (hv j) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have h₁ := abs_sum_sum_mul_inner_le_eight_mul (fun i j ↦ RCLike.re (ω * a i j))
    (fun s t hs ht ↦ by
      simpa using a.abs_sum_sum_map_mul_mul_mul_le h hω RCLike.reCLM RCLike.abs_re_le_norm
        hs ht) hu hv
  have h₂ := abs_sum_sum_mul_inner_le_eight_mul (fun i j ↦ RCLike.im (ω * a i j))
    (fun s t hs ht ↦ by
      simpa using a.abs_sum_sum_map_mul_mul_mul_le h hω RCLike.imCLM RCLike.abs_im_le_norm
        hs ht) hu hIv
  rw [hωz, hsplit]
  linarith [le_abs_self (∑ i, ∑ j, RCLike.re (ω * a i j) * ⟪u i, v j⟫_ℝ),
    le_abs_self (∑ i, ∑ j, RCLike.im (ω * a i j) * ⟪u i, (RCLike.I : 𝕜) • v j⟫_ℝ)]

end Matrix
