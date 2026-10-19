/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.QuadraticForm.TwoVector
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.InnerProductSpace.Semisimple

/-!
# Per-eigenvector Davis sin 2θ and off-diagonal tan 2θ bounds

Let `T` and `H` be symmetric operators on a real or complex inner-product space. Suppose
`U` is invariant under `T`, and `T` has two separated quadratic-form bounds: at least
`b * ‖u‖²` on `U` and at most `a * ‖z‖²` on `Uᗮ`. For a unit eigenvector `x` of `T + H`,
write `x = y + z` with `y ∈ U` and `z ∈ Uᗮ`.

The sharp **per-eigenvector** double-angle product estimate is
`(b-a) * ‖y‖ * ‖z‖ ≤ ε` when `‖H v‖ ≤ ε * ‖v‖`.
With an orthogonal projection onto `U`, `θ = arccos ‖P_U x‖` gives the angle form
`(b-a) * sin (2θ) ≤ 2ε`. If `b > a`, these imply the usual divided
bound `sin (2θ) ≤ 2ε / (b-a)`; positivity of the gap is required for division.

If the two diagonal blocks of `H` with respect to `U ⊕ Uᗮ` vanish, the sharper,
**homogeneous** off-diagonal product estimate is
`(b-a) * ‖y‖ * ‖z‖ ≤ |‖y‖² - ‖z‖²| * ε`.
For a *unit* vector, `b > a`, and `cos (2θ) ≠ 0`, this implies the absolute tangent
bound `|tan (2θ)| ≤ 2ε / (b-a)`. The product estimate itself requires neither
unit normalization nor a tangent pole restriction.

These are eigenvector bounds, **not** the finite-dimensional unitarily invariant
subspace `sin 2Θ` theorem or the general `sin Θ` theorems.
They do not require finite-dimensionality. The proof uses a phase-free block-energy
identity and real two-vector quadratic-form identities.

## Main declarations

* `LinearMap.IsSymmetric.sin_two_theta_le_of_mem` and
  `LinearMap.IsSymmetric.sin_two_theta_le`.
* `LinearMap.IsSymmetric.sin_two_arccos_le`.
* `LinearMap.IsSymmetric.tan_two_theta_le_of_mem` and `LinearMap.IsSymmetric.tan_two_theta_le`.

## References and provenance

* C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl.
  **6** (1963), 159–173.
* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* Adapted from `ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/Vector.lean` in the
  [AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
  (Apache-2.0); attribution retained in the source header.
-/

public section

namespace LinearMap.IsSymmetric
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {T H : E →ₗ[𝕜] E}

/-- **The block energy identity** (phase-free form of Davis's 2×2 compression).  If
`y ∈ U`, `z ∈ Uᗮ` for a `T`-invariant subspace `U` of a symmetric operator,
and `y + z` is an eigenvector of `T + H` with real eigenvalue `μ`, then

`‖z‖² re ⟪y, T y⟫ - ‖y‖² re ⟪z, T z⟫ + ‖z‖² re ⟪y, H y⟫ - ‖y‖² re ⟪z, H z⟫
+ (‖z‖² - ‖y‖²) re ⟪y, H z⟫ = 0`.

The eigenvalue `μ` is eliminated; no location assumption on it is ever used.
This identity is the shared engine of both the sin 2θ and the tan 2θ theorem
below. -/
private theorem eigenvector_block_energy_identity (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} (hUinv : ∀ u ∈ U, T u ∈ U)
    {y z : E} (hyU : y ∈ U) (hzU : z ∈ Uᗮ) {μ : ℝ}
    (hμ : T (y + z) + H (y + z) = (μ : 𝕜) • (y + z)) :
    ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜
      + ‖z‖ ^ 2 * RCLike.re ⟪y, H y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, H z⟫_𝕜
      + (‖z‖ ^ 2 - ‖y‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜 = 0 := by
  have hyz : ⟪y, z⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hyU hzU
  have hzy : ⟪z, y⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hyU hzU
  have hTy : T y ∈ U := hUinv y hyU
  have hTz : T z ∈ Uᗮ :=
    hT.orthogonalComplement_mem_invtSubmodule (p := U) hUinv hzU
  -- Pair the eigenvector equation with `y`.
  have e1 : RCLike.re ⟪y, T y⟫_𝕜 + RCLike.re ⟪y, H y⟫_𝕜 + RCLike.re ⟪y, H z⟫_𝕜
      = μ * ‖y‖ ^ 2 := by
    have h0 : ⟪y, T (y + z) + H (y + z)⟫_𝕜 = ⟪y, (μ : 𝕜) • (y + z)⟫_𝕜 := by rw [hμ]
    simp only [map_add, inner_add_right, inner_smul_right] at h0
    rw [Submodule.inner_right_of_mem_orthogonal hyU hTz, hyz, add_zero, add_zero] at h0
    have h1 := congrArg RCLike.re h0
    simp only [map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq] at h1
    linarith
  -- Pair the eigenvector equation with `z`.
  have e2 : RCLike.re ⟪z, T z⟫_𝕜 + RCLike.re ⟪z, H y⟫_𝕜 + RCLike.re ⟪z, H z⟫_𝕜
      = μ * ‖z‖ ^ 2 := by
    have h0 : ⟪z, T (y + z) + H (y + z)⟫_𝕜 = ⟪z, (μ : 𝕜) • (y + z)⟫_𝕜 := by rw [hμ]
    simp only [map_add, inner_add_right, inner_smul_right] at h0
    rw [Submodule.inner_left_of_mem_orthogonal hTy hzU, hzy, zero_add, zero_add] at h0
    have h1 := congrArg RCLike.re h0
    simp only [map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq] at h1
    linarith
  -- `‖z‖² · e1 - ‖y‖² · e2` eliminates `μ`; the mixed terms combine by symmetry
  -- of `H` at the level of real parts.
  have hW := hH.re_inner_map_symm y z
  set c₂ : ℝ := ‖y‖ ^ 2
  set s₂ : ℝ := ‖z‖ ^ 2
  linear_combination s₂ * e1 - c₂ * e2 + c₂ * hW

/-- **Davis's sin 2θ theorem, orthogonal-decomposition form.**  Let `T`, `H`
be symmetric, `U` a `T`-invariant subspace with the quadratic form of `T` at
least `b * ‖·‖ ^ 2` on `U` and at most `a * ‖·‖ ^ 2` on `Uᗮ`, and let
`y + z` (`y ∈ U`, `z ∈ Uᗮ`) be a unit eigenvector of `T + H` with real
eigenvalue `μ` — **no location assumption on `μ`**.  If `‖H v‖ ≤ ε * ‖v‖` for
all `v`, then

`(b - a) * (‖y‖ * ‖z‖) ≤ ε`.

For the angle `θ` of the unit eigenvector with `U`, `2 * ‖y‖ * ‖z‖ = sin (2θ)`.
**Only when `b > a`** can the product inequality be divided by the spectral gap to
obtain `sin (2θ) ≤ 2ε / (b-a)`. The product statement also holds for `b ≤ a` and
does not require an orthogonal projection onto `U`. -/
theorem sin_two_theta_le_of_mem (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    {y z : E} (hyU : y ∈ U) (hzU : z ∈ Uᗮ) (hx : ‖y + z‖ = 1) {μ : ℝ}
    (hμ : T (y + z) + H (y + z) = (μ : 𝕜) • (y + z)) :
    (b - a) * (‖y‖ * ‖z‖) ≤ ε := by
  have hε0 : 0 ≤ ε := by
    have h := hε (y + z)
    rw [hx, mul_one] at h
    exact (norm_nonneg _).trans h
  have hyz : ⟪y, z⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hyU hzU
  -- Pythagoras: `‖y‖² + ‖z‖² = 1`.
  have hpyth : ‖y‖ ^ 2 + ‖z‖ ^ 2 = 1 := by
    have h := norm_add_sq (𝕜 := 𝕜) y z
    rw [hx, hyz, map_zero, mul_zero, add_zero, one_pow] at h
    linarith
  -- Degenerate cases: the product vanishes.
  rcases eq_or_ne ‖y‖ 0 with hc0 | hc0
  · rw [hc0, zero_mul, mul_zero]; exact hε0
  rcases eq_or_ne ‖z‖ 0 with hs0 | hs0
  · rw [hs0, mul_zero, mul_zero]; exact hε0
  have hc : 0 < ‖y‖ := (norm_nonneg y).lt_of_ne' hc0
  have hs : 0 < ‖z‖ := (norm_nonneg z).lt_of_ne' hs0
  have hcs : 0 < ‖y‖ * ‖z‖ := mul_pos hc hs
  -- The block energy identity and the two quadratic-form bounds.
  have key := eigenvector_block_energy_identity hT hH hUinv hyU hzU hμ
  have hby : b * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, T y⟫_𝕜 := by
    have h := hb y hyU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have haz : RCLike.re ⟪z, T z⟫_𝕜 ≤ a * ‖z‖ ^ 2 := by
    have h := ha z hzU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have hquad : ∀ u : E, |RCLike.re ⟪u, H u⟫_𝕜| ≤ ε * ‖u‖ ^ 2 := fun u =>
    calc |RCLike.re ⟪u, H u⟫_𝕜| ≤ ‖⟪u, H u⟫_𝕜‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖u‖ * ‖H u‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖ * (ε * ‖u‖) := by gcongr; exact hε u
      _ = ε * ‖u‖ ^ 2 := by ring
  -- Test the quadratic form of `H` against the two rotation vectors
  -- `s(c-s) • y + c(c+s) • z` and `-s(c+s) • y + c(c-s) • z`
  -- (the polynomial realization of the classical half-angle rotation:
  -- `1 - 2cs = (c-s)²`, `1 + 2cs = (c+s)²`).
  have hW := hH.re_inner_map_symm y z
  have hre_yz : RCLike.re ⟪y, z⟫_𝕜 = 0 := by simp [hyz]
  have hb1 := hquad ((((‖z‖ * (‖y‖ - ‖z‖)) : ℝ) : 𝕜) • y
    + (((‖y‖ * (‖y‖ + ‖z‖)) : ℝ) : 𝕜) • z)
  rw [LinearMap.re_inner_smul_add_smul_map, TauCeti.norm_smul_add_smul_sq hre_yz, hW] at hb1
  have hb2 := hquad ((((-(‖z‖ * (‖y‖ + ‖z‖))) : ℝ) : 𝕜) • y
    + (((‖y‖ * (‖y‖ - ‖z‖)) : ℝ) : 𝕜) • z)
  rw [LinearMap.re_inner_smul_add_smul_map, TauCeti.norm_smul_add_smul_sq hre_yz, hW] at hb2
  -- Both rotation vectors have squared norm `2‖y‖²‖z‖²`.
  have hN1 : (‖z‖ * (‖y‖ - ‖z‖)) ^ 2 * ‖y‖ ^ 2 + (‖y‖ * (‖y‖ + ‖z‖)) ^ 2 * ‖z‖ ^ 2
      = 2 * (‖y‖ ^ 2 * ‖z‖ ^ 2) := by
    linear_combination (2 * ‖y‖ ^ 2 * ‖z‖ ^ 2) * hpyth
  have hN2 : (-(‖z‖ * (‖y‖ + ‖z‖))) ^ 2 * ‖y‖ ^ 2 + (‖y‖ * (‖y‖ - ‖z‖)) ^ 2 * ‖z‖ ^ 2
      = 2 * (‖y‖ ^ 2 * ‖z‖ ^ 2) := by
    linear_combination (2 * ‖y‖ ^ 2 * ‖z‖ ^ 2) * hpyth
  rw [hN1] at hb1
  rw [hN2] at hb2
  have habs1 := abs_le.mp hb1
  have habs2 := abs_le.mp hb2
  -- The difference of the two tested forms is `4cs (s² re⟪y,Ty⟫ - c² re⟪z,Tz⟫)`
  -- by the block energy identity; multiply it by `4cs` to keep everything
  -- linear over monomials.
  have key4 : 4 * (‖y‖ * ‖z‖)
      * (‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜
        + ‖z‖ ^ 2 * RCLike.re ⟪y, H y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, H z⟫_𝕜
        + (‖z‖ ^ 2 - ‖y‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜) = 0 := by
    rw [key, mul_zero]
  have hstep1 : 4 * (‖y‖ * ‖z‖)
      * (‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜)
      ≤ ε * (4 * (‖y‖ ^ 2 * ‖z‖ ^ 2)) := by
    linarith [habs1.2, habs2.1, key4]
  -- Insert the two form bounds and divide by `4c²s² > 0`.
  have hmid : ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
      ≤ ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜 :=
    have h1 := mul_le_mul_of_nonneg_left hby (sq_nonneg ‖z‖)
    have h2 := mul_le_mul_of_nonneg_left haz (sq_nonneg ‖y‖)
    by linarith
  have hstep2 : 4 * (‖y‖ ^ 2 * ‖z‖ ^ 2) * ((b - a) * (‖y‖ * ‖z‖))
      ≤ 4 * (‖y‖ * ‖z‖)
        * (‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜) :=
    have h3 := mul_le_mul_of_nonneg_left hmid (by positivity : (0 : ℝ) ≤ 4 * (‖y‖ * ‖z‖))
    by linarith
  have hfinal : 4 * (‖y‖ ^ 2 * ‖z‖ ^ 2) * ((b - a) * (‖y‖ * ‖z‖))
      ≤ 4 * (‖y‖ ^ 2 * ‖z‖ ^ 2) * ε := by linarith
  have h4 : (0 : ℝ) < 4 * (‖y‖ ^ 2 * ‖z‖ ^ 2) := by
    have := mul_pos hcs hcs
    nlinarith [this]
  exact le_of_mul_le_mul_left hfinal h4

/-- **Davis's sin 2θ theorem, per-eigenvector product form.**  Under the
hypotheses of `sin_two_theta_le_of_mem`, for a unit eigenvector `x` of
`T + H` and `P = U.starProjection`,

`(b - a) * (‖P x‖ * ‖x - P x‖) ≤ ε`,

When `b > a`, this implies the divided `sin (2θ) ≤ 2ε / (b-a)` bound for
the angle `θ` between `x` and `U`. -/
theorem sin_two_theta_le (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    {x : E} (hx : ‖x‖ = 1) {μ : ℝ} (hμ : T x + H x = (μ : 𝕜) • x) :
    (b - a) * (‖U.starProjection x‖ * ‖x - U.starProjection x‖) ≤ ε := by
  have hxsum : U.starProjection x + (x - U.starProjection x) = x := by abel
  exact hT.sin_two_theta_le_of_mem hH hUinv hb ha hε
    (U.starProjection_apply_mem x) (U.sub_starProjection_mem_orthogonal x)
    (by rw [hxsum]; exact hx) (by rw [hxsum]; exact hμ)

/-- **Davis's sin 2θ theorem, angle form.**  Under the hypotheses of
`sin_two_theta_le`, with `θ = arccos ‖P x‖` the angle between the unit
eigenvector `x` and the invariant subspace `U`,

`(b - a) * sin (2θ) ≤ 2 * ε`, with no division by `b-a`. -/
theorem sin_two_arccos_le (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    {x : E} (hx : ‖x‖ = 1) {μ : ℝ} (hμ : T x + H x = (μ : 𝕜) • x) :
    (b - a) * Real.sin (2 * Real.arccos ‖U.starProjection x‖) ≤ 2 * ε := by
  have hmain := hT.sin_two_theta_le hH hUinv hb ha hε hx hμ
  set y := U.starProjection x with hy
  set z := x - y with hzdef
  have hyU : y ∈ U := U.starProjection_apply_mem x
  have hzU : z ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hyz : ⟪y, z⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hyU hzU
  have hxsum : y + z = x := by rw [hzdef]; abel
  have hpyth : ‖y‖ ^ 2 + ‖z‖ ^ 2 = 1 := by
    have h := norm_add_sq (𝕜 := 𝕜) y z
    simp only [hxsum, hx, hyz, map_zero, mul_zero, add_zero, one_pow] at h
    linarith
  have hc1 : ‖y‖ ≤ 1 := by nlinarith [norm_nonneg y, sq_nonneg ‖z‖, sq_nonneg (‖y‖ - 1)]
  rw [Real.sin_two_mul, Real.cos_arccos (by linarith [norm_nonneg y]) hc1, Real.sin_arccos]
  have hradicand : (1 : ℝ) - ‖y‖ ^ 2 = ‖z‖ ^ 2 := by linarith
  have hsqrt : Real.sqrt (1 - ‖y‖ ^ 2) = ‖z‖ := by
    rw [hradicand]
    exact Real.sqrt_sq (norm_nonneg z)
  rw [hsqrt]
  nlinarith [hmain]

/-- **Off-diagonal double-angle product bound**. Suppose the diagonal
blocks of `H` relative to `U ⊕ Uᗮ` vanish. For any (possibly nonunit) eigenvector
`y+z` of `T+H`, with `y ∈ U` and `z ∈ Uᗮ`,

`(b-a) * ‖y‖ * ‖z‖ ≤ |‖y‖² - ‖z‖²| * ε`.

The result is homogeneous and has no positivity-of-gap or transversality side conditions.
For unit eigenvectors, with `b>a` and `cos (2θ) ≠ 0`, it yields
`|tan (2θ)| ≤ 2ε/(b-a)`; the absolute value and the pole exclusion are essential.
The proof uses the same block-energy identity as the sine estimate. -/
theorem tan_two_theta_le_of_mem (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    (hHU : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0)
    (hHUperp : ∀ w ∈ Uᗮ, ∀ w' ∈ Uᗮ, ⟪w, H w'⟫_𝕜 = 0)
    {y z : E} (hyU : y ∈ U) (hzU : z ∈ Uᗮ) {μ : ℝ}
    (hμ : T (y + z) + H (y + z) = (μ : 𝕜) • (y + z)) :
    (b - a) * (‖y‖ * ‖z‖) ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * ε := by
  -- The completely degenerate case gives `0 ≤ 0` even if `ε` is negative.
  by_cases hzero : y = 0 ∧ z = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp
  -- Otherwise a nonzero vector forces `ε ≥ 0` from the operator bound.
  have hε0 : 0 ≤ ε := by
    by_cases hy : y = 0
    · have hz : z ≠ 0 := fun hz => hzero ⟨hy, hz⟩
      exact nonneg_of_mul_nonneg_left
        ((norm_nonneg (H z)).trans (hε z)) (norm_pos_iff.mpr hz)
    · exact nonneg_of_mul_nonneg_left
        ((norm_nonneg (H y)).trans (hε y)) (norm_pos_iff.mpr hy)
  have key := eigenvector_block_energy_identity hT hH hUinv hyU hzU hμ
  have hyH : RCLike.re ⟪y, H y⟫_𝕜 = 0 := by rw [hHU y hyU y hyU]; simp
  have hzH : RCLike.re ⟪z, H z⟫_𝕜 = 0 := by rw [hHUperp z hzU z hzU]; simp
  have hby : b * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, T y⟫_𝕜 := by
    have h := hb y hyU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have haz : RCLike.re ⟪z, T z⟫_𝕜 ≤ a * ‖z‖ ^ 2 := by
    have h := ha z hzU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have hmix : |RCLike.re ⟪y, H z⟫_𝕜| ≤ ‖y‖ * ‖z‖ * ε :=
    calc |RCLike.re ⟪y, H z⟫_𝕜| ≤ ‖⟪y, H z⟫_𝕜‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖y‖ * ‖H z‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (ε * ‖z‖) := by gcongr; exact hε z
      _ = ‖y‖ * ‖z‖ * ε := by ring
  -- The vanishing diagonal blocks collapse the block energy identity.
  have hcollapse : ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜
      = (‖y‖ ^ 2 - ‖z‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜 := by
    rw [hyH, hzH] at key
    linear_combination key
  -- The two quadratic-form bounds give the lower bound on the collapsed LHS.
  have hlow : ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
      ≤ ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜 := by
    nlinarith [mul_le_mul_of_nonneg_left hby (sq_nonneg ‖z‖),
      mul_le_mul_of_nonneg_left haz (sq_nonneg ‖y‖)]
  -- Chain: `‖y‖²‖z‖²(b-a) ≤ (Y-Z)·W ≤ |Y-Z|·‖y‖‖z‖·ε`.
  have hchain : ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
      ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * (‖y‖ * ‖z‖ * ε) :=
    calc ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
        ≤ ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜 := hlow
      _ = (‖y‖ ^ 2 - ‖z‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜 := hcollapse
      _ ≤ |(‖y‖ ^ 2 - ‖z‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜| := le_abs_self _
      _ = |‖y‖ ^ 2 - ‖z‖ ^ 2| * |RCLike.re ⟪y, H z⟫_𝕜| := abs_mul _ _
      _ ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * (‖y‖ * ‖z‖ * ε) := by gcongr
  -- Divide by `‖y‖‖z‖`; degenerate case handled by nonnegativity.
  rcases (mul_nonneg (norm_nonneg y) (norm_nonneg z)).eq_or_lt with hn | hn
  · rw [← hn, mul_zero]
    exact mul_nonneg (abs_nonneg _) hε0
  · have hh : (‖y‖ * ‖z‖) * ((b - a) * (‖y‖ * ‖z‖))
        ≤ (‖y‖ * ‖z‖) * (|‖y‖ ^ 2 - ‖z‖ ^ 2| * ε) := by
      linear_combination hchain
    exact le_of_mul_le_mul_left hh hn

/-- **Off-diagonal double-angle product bound, projection form**.
Under the hypotheses of `tan_two_theta_le_of_mem`, for any eigenvector `x` of
`T+H` and `P=U.starProjection`,

`(b-a) * ‖P x‖ * ‖x-P x‖ ≤ |‖P x‖² - ‖x-P x‖²| * ε`.

The statement is homogeneous: `‖x‖=1` is not required. For unit `x`, `b>a`,
and away from `cos (2θ)=0`, this gives the absolute `tan (2θ)` bound. -/
theorem tan_two_theta_le (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    (hHU : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0)
    (hHUperp : ∀ w ∈ Uᗮ, ∀ w' ∈ Uᗮ, ⟪w, H w'⟫_𝕜 = 0)
    {x : E} {μ : ℝ} (hμ : T x + H x = (μ : 𝕜) • x) :
    (b - a) * (‖U.starProjection x‖ * ‖x - U.starProjection x‖)
      ≤ |‖U.starProjection x‖ ^ 2 - ‖x - U.starProjection x‖ ^ 2| * ε := by
  have hxsum : U.starProjection x + (x - U.starProjection x) = x := by abel
  exact hT.tan_two_theta_le_of_mem hH hUinv hb ha hε hHU hHUperp
    (U.starProjection_apply_mem x) (U.sub_starProjection_mem_orthogonal x)
    (by rw [hxsum]; exact hμ)

end LinearMap.IsSymmetric
