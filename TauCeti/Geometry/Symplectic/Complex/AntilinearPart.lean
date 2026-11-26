/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.Complex.LinearPart
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

/-!
# The antilinear part of a complex-valued functional on an orthogonal complex structure

Let `J` be an orthogonal complex structure on a finite-dimensional real inner product space `E`,
`e` an orthonormal basis and `L : E → ℂ` a real-linear map. Its complex-antilinear part
`∂bar L v = (L v + i L (J v)) / 2` (`TauCeti.complexAntilinearPart`, for `J` on `E` and
multiplication by `i` on `ℂ`) has Hilbert–Schmidt norm `|∂bar L|² = ∑ᵢ |∂bar L eᵢ|²`. Writing the
real and imaginary parts of `L` as `⟪g₁, ·⟫` and `⟪p, ·⟫`, the vector `d = g₁ + J p` represents
the real part of `2 ∂bar L`, and `|∂bar L|² = ‖d‖² / 2`
(`TauCeti.AlmostComplexStructure.sum_norm_sq_complexAntilinearPart`), while its operator norm is
`‖g₁ + J p‖ / 2` (`TauCeti.AlmostComplexStructure.norm_eq_norm_add_apply_div_two`).

For `a ∈ ℂ`, the real functional `v ↦ 2 Re (conj a · L v)` is the differential of `|α|²` when
`L = ∇α` and `a = α`. When `L` is complex-linear, its squared norm is `2 |a|² |L|²`. In general,
for every `ε > 0`,

`2 |a|² ((1 - ε) |L|² - (2 + 18 / ε) |∂bar L|²) ≤ ∑ᵢ (2 Re (conj a · L eᵢ))²`

(`TauCeti.AlmostComplexStructure.two_mul_norm_sq_mul_sub_le_sum_sq_re`). The defect is bounded by
`‖d‖` through Cauchy–Schwarz for the Hermitian metric of `J`, applied to the orthogonal pair
`p`, `J p` (`TauCeti.AlmostComplexStructure.inner_sq_add_inner_sq_le`).

## Main results

* `TauCeti.AlmostComplexStructure.sum_norm_sq_complexAntilinearPart`: `|∂bar L|² = ‖g₁ + J p‖² / 2`.
* `TauCeti.AlmostComplexStructure.norm_eq_norm_add_apply_div_two`: the operator norm of `∂bar L` is
  `‖g₁ + J p‖ / 2`.
* `TauCeti.AlmostComplexStructure.two_mul_norm_sq_mul_sub_le_sum_sq_re`: the lower bound on
  `∑ᵢ (2 Re (conj a · L eᵢ))²` in terms of `|L|²` and `|∂bar L|²`.
-/

public section

open Complex InnerProductSpace
open scoped ComplexConjugate RealInnerProductSpace

namespace TauCeti.AlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real inequality behind `two_mul_norm_sq_mul_sub_le_sum_sq_re`, in the coordinates
`D = ‖d‖²`, `P = ‖p‖²`, `m = ⟪d, J p⟫`, `n = ⟪d, p⟫` and `a = x + i y`. -/
private theorem two_mul_mul_sub_le {x y D P m n ε : ℝ} (hε : 0 < ε) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hmn : m ^ 2 + n ^ 2 ≤ D * P) :
    2 * (x ^ 2 + y ^ 2) * ((1 - ε) * (D - 2 * m + P + P) - (2 + 18 / ε) * (D / 2)) ≤
      4 * (x ^ 2 * D + (x ^ 2 + y ^ 2) * P - 2 * x ^ 2 * m + 2 * x * y * n) := by
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = x ^ 2 + y ^ 2 := ⟨_, rfl⟩
  have hρ : 0 ≤ ρ := by rw [hρdef]; positivity
  rw [← hρdef]
  -- The cross term `X = (4 (y² - x²) - 4 ε ρ) m + 8 x y n` has `X² ≤ 16 ρ² (1 + ε)² D P`.
  set X := (4 * (y ^ 2 - x ^ 2) - 4 * ε * ρ) * m + 8 * x * y * n with hXdef
  have hcoef : (4 * (y ^ 2 - x ^ 2) - 4 * ε * ρ) ^ 2 + (8 * x * y) ^ 2 ≤
      (4 * ρ * (1 + ε)) ^ 2 := by
    have hA : 0 ≤ 4 * ρ + 4 * (y ^ 2 - x ^ 2) := by rw [hρdef]; nlinarith [sq_nonneg y]
    have hid : (4 * ρ * (1 + ε)) ^ 2 -
        ((4 * (y ^ 2 - x ^ 2) - 4 * ε * ρ) ^ 2 + (8 * x * y) ^ 2) =
          8 * ε * ρ * (4 * ρ + 4 * (y ^ 2 - x ^ 2)) := by
      rw [hρdef]
      ring
    have : 0 ≤ 8 * ε * ρ * (4 * ρ + 4 * (y ^ 2 - x ^ 2)) := by positivity
    linarith
  have hX : X ^ 2 ≤ (4 * ρ * (1 + ε)) ^ 2 * (D * P) := by
    have hcs : X ^ 2 ≤ ((4 * (y ^ 2 - x ^ 2) - 4 * ε * ρ) ^ 2 + (8 * x * y) ^ 2) *
        (m ^ 2 + n ^ 2) := by
      nlinarith [sq_nonneg ((4 * (y ^ 2 - x ^ 2) - 4 * ε * ρ) * n - 8 * x * y * m)]
    exact hcs.trans (mul_le_mul hcoef hmn (by positivity) (by positivity))
  -- Hence `X ≥ -(4 ε ρ P + ρ (1 + ε)² D / ε)`, by `X² ≤ 4 t₁ t₂ ≤ (t₁ + t₂)²`.
  have hXlow : -(4 * ε * ρ * P + ρ * (1 + ε) ^ 2 * D / ε) ≤ X := by
    have hT : 0 ≤ 4 * ε * ρ * P + ρ * (1 + ε) ^ 2 * D / ε := by positivity
    have hprod : (4 * ρ * (1 + ε)) ^ 2 * (D * P) =
        4 * (4 * ε * ρ * P) * (ρ * (1 + ε) ^ 2 * D / ε) := by
      field_simp
    have hsq' : X ^ 2 ≤ (4 * ε * ρ * P + ρ * (1 + ε) ^ 2 * D / ε) ^ 2 := by
      rw [hprod] at hX
      nlinarith [sq_nonneg (4 * ε * ρ * P - ρ * (1 + ε) ^ 2 * D / ε)]
    exact (abs_le_of_sq_le_sq' hsq' hT).1
  -- Conclude, using `(1 + ε)² / ε = 1 / ε + 2 + ε ≤ 18 / ε + 2 ε`.
  have hε' : ρ * (1 + ε) ^ 2 * D / ε ≤ 18 * ρ * D / ε + 2 * ε * ρ * D := by
    have hid : 18 * ρ * D / ε + 2 * ε * ρ * D - ρ * (1 + ε) ^ 2 * D / ε =
        ρ * D * ((ε - 1) ^ 2 + 16) / ε := by
      field_simp
      ring
    have : 0 ≤ ρ * D * ((ε - 1) ^ 2 + 16) / ε := by positivity
    linarith
  have hxD : 0 ≤ x ^ 2 * D := by positivity
  have hkey : 4 * (x ^ 2 * D + ρ * P - 2 * x ^ 2 * m + 2 * x * y * n) -
      2 * ρ * ((1 - ε) * (D - 2 * m + P + P) - (2 + 18 / ε) * (D / 2)) =
        4 * x ^ 2 * D + 4 * ε * ρ * P + 2 * ε * ρ * D + 18 * ρ * D / ε + X := by
    rw [hXdef, hρdef]
    ring
  linarith

/-- The complex-antilinear part of `L : E → ℂ`, for `J` on `E` and multiplication by `I` on `ℂ`,
is `v ↦ (L v + I L (J v)) / 2`. -/
private theorem complexAntilinearPart_apply_eq (J : AlmostComplexStructure E) (L : E →L[ℝ] ℂ)
    (v : E) :
    complexAntilinearPart J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ I) (L : E →ₗ[ℝ] ℂ) v =
      (L v + I * L (J v)) / 2 := by
  simp only [complexAntilinearPart_apply, ContinuousLinearMap.coe_coe,
    DistribSMul.toLinearMap_apply, smul_eq_mul, real_smul, ofReal_inv, ofReal_ofNat]
  ring

/-- **The Hilbert–Schmidt norm of the antilinear part.** If `g₁` and `p` represent the real and
imaginary parts of `L : E → ℂ`, then the complex-antilinear part `∂bar L v = (L v + i L (J v)) / 2`
satisfies `∑ᵢ |∂bar L eᵢ|² = ‖g₁ + J p‖² / 2`: the vector `g₁ + J p` represents the real part of
`2 ∂bar L`, and `p - J g₁ = -J (g₁ + J p)` its imaginary part. -/
theorem sum_norm_sq_complexAntilinearPart {ι : Type*} [Fintype ι] {J : AlmostComplexStructure E}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (e : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℂ) {g₁ p : E}
    (h₁ : ∀ v, ⟪g₁, v⟫ = (L v).re) (h₂ : ∀ v, ⟪p, v⟫ = (L v).im) :
    ∑ i, ‖complexAntilinearPart J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ I)
        (L : E →ₗ[ℝ] ℂ) (e i)‖ ^ 2 = ‖g₁ + J p‖ ^ 2 / 2 := by
  have hd' : p - J g₁ = -J (g₁ + J p) := by
    simp only [J.apply_add, J.apply_apply]
    abel
  have hsum : ∑ i, ‖complexAntilinearPart J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ I)
      (L : E →ₗ[ℝ] ℂ) (e i)‖ ^ 2 =
        (∑ i, ⟪g₁ + J p, e i⟫ ^ 2 + ∑ i, ⟪p - J g₁, e i⟫ ^ 2) / 4 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hJ₁ : ⟪J g₁, e i⟫ = -(L (J (e i))).re := by rw [inner_apply_left hJ, h₁]
    have hJ₂ : ⟪J p, e i⟫ = -(L (J (e i))).im := by rw [inner_apply_left hJ, h₂]
    rw [complexAntilinearPart_apply_eq, Complex.sq_norm, Complex.normSq_apply]
    simp only [inner_add_left, inner_sub_left, h₁, h₂, hJ₁, hJ₂, div_ofNat_re, div_ofNat_im,
      add_re, add_im, mul_re, mul_im, I_re, I_im]
    ring
  rw [hsum, e.sum_sq_inner_left, e.sum_sq_inner_left, hd', norm_neg, norm_apply hJ]
  ring

/-- **The operator norm of the antilinear part.** If `g₁` and `p` represent the real and imaginary
parts of `L : E → ℂ`, then a continuous real-linear map `D` with
`D v = (L v + i L (J v)) / 2`, the complex-antilinear part of `L`, has operator norm
`‖D‖ = ‖g₁ + J p‖ / 2`. By `TauCeti.AlmostComplexStructure.sum_norm_sq_complexAntilinearPart`, its
Hilbert–Schmidt norm is therefore `√2` times its operator norm. -/
theorem norm_eq_norm_add_apply_div_two {J : AlmostComplexStructure E}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) {L : E → ℂ} {g₁ p : E} (h₁ : ∀ v, ⟪g₁, v⟫ = (L v).re)
    (h₂ : ∀ v, ⟪p, v⟫ = (L v).im) {D : E →L[ℝ] ℂ} (hD : ∀ v, D v = (L v + I * L (J v)) / 2) :
    ‖D‖ = ‖g₁ + J p‖ / 2 := by
  set d := g₁ + J p
  -- In terms of `d`, the real and imaginary parts of `D v` are `⟪d, v⟫ / 2` and `⟪d, J v⟫ / 2`.
  have hsq (v : E) : ‖D v‖ ^ 2 = (⟪d, J v⟫ ^ 2 + ⟪d, v⟫ ^ 2) / 4 := by
    have hre : (D v).re = ⟪d, v⟫ / 2 := by
      rw [hD, div_ofNat_re, add_re, mul_re, I_re, I_im, inner_add_left,
        inner_apply_left_eq_neg_swap hJ, real_inner_comm p (J v), h₁, h₂]
      ring
    have him : (D v).im = ⟪d, J v⟫ / 2 := by
      rw [hD, div_ofNat_im, add_im, mul_im, I_re, I_im, inner_add_left, hJ, h₁, h₂]
      ring
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  refine le_antisymm (D.opNorm_le_bound (by positivity) fun v ↦ ?_) ?_
  · -- Cauchy–Schwarz for the Hermitian metric of `J` bounds `‖D v‖` by `‖d‖ ‖v‖ / 2`.
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [hsq, mul_pow, div_pow]
    linarith [inner_sq_add_inner_sq_le hJ d v]
  · -- The bound is attained at `v = d`, where `D d = ‖d‖² / 2`.
    have hd : ‖D d‖ = ‖d‖ ^ 2 / 2 := by
      refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
      rw [hsq, inner_self_apply hJ, real_inner_self_eq_norm_sq]
      ring
    rcases (norm_nonneg d).eq_or_lt with h | h
    · rw [← h, zero_div]
      exact norm_nonneg D
    · have := D.le_opNorm d
      rw [hd] at this
      rw [div_le_iff₀ two_pos]
      nlinarith

variable [FiniteDimensional ℝ E]

/-- **`2 Re (conj a · L)` against the antilinear part of `L`.** Let `J` be an orthogonal complex
structure on `E`, `e` an orthonormal basis, `L : E → ℂ` real-linear and `a ∈ ℂ`. Write
`|L|² = ∑ᵢ |L eᵢ|²` and `|∂bar L|² = ∑ᵢ |∂bar L eᵢ|²`, where `∂bar L v = (L v + i L (J v)) / 2` is
the complex-antilinear part `TauCeti.complexAntilinearPart`. Then for every `ε > 0`,

`2 |a|² ((1 - ε) |L|² - (2 + 18 / ε) |∂bar L|²) ≤ ∑ᵢ (2 Re (conj a · L eᵢ))²`.

For `L = ∇_a α` and `a = α` at a point, the right side is `|∇ |α|²|²`. -/
theorem two_mul_norm_sq_mul_sub_le_sum_sq_re {ι : Type*} [Fintype ι]
    (J : AlmostComplexStructure E) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (e : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℂ) (a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    2 * ‖a‖ ^ 2 * ((1 - ε) * ∑ i, ‖L (e i)‖ ^ 2 -
        (2 + 18 / ε) * ∑ i, ‖complexAntilinearPart J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ I)
          (L : E →ₗ[ℝ] ℂ) (e i)‖ ^ 2) ≤
      ∑ i, (2 * (conj a * L (e i)).re) ^ 2 := by
  -- The real and imaginary parts of `L` are represented by vectors `g₁` and `p`.
  set g₁ := (toDual ℝ E).symm (reCLM.comp L)
  set p := (toDual ℝ E).symm (imCLM.comp L)
  have h₁ (v : E) : ⟪g₁, v⟫ = (L v).re := by simp [g₁, toDual_symm_apply]
  have h₂ (v : E) : ⟪p, v⟫ = (L v).im := by simp [p, toDual_symm_apply]
  -- The three sums are squared norms of vectors, with `d = g₁ + J p` representing `2 ∂bar L`.
  set d := g₁ + J p
  have hL : ∑ i, ‖L (e i)‖ ^ 2 = ‖g₁‖ ^ 2 + ‖p‖ ^ 2 := by
    rw [← e.sum_sq_inner_left g₁, ← e.sum_sq_inner_left p, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h₁, h₂, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hre : ∑ i, (2 * (conj a * L (e i)).re) ^ 2 = 4 * ‖a.re • g₁ + a.im • p‖ ^ 2 := by
    rw [← e.sum_sq_inner_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [inner_add_left, real_inner_smul_left, h₁, h₂, mul_re, conj_re, conj_im]
    ring
  rw [hL, sum_norm_sq_complexAntilinearPart hJ e L h₁ h₂, hre, Complex.sq_norm,
    Complex.normSq_apply, ← sq, ← sq]
  -- Write `g₁ = d - J p` and expand in the inner products `⟪d, J p⟫` and `⟪d, p⟫`.
  have hg₁ : g₁ = d - J p := (add_sub_cancel_right g₁ (J p)).symm
  have hpJp : ⟪J p, p⟫ = 0 := inner_apply_self hJ p
  have hnorm₁ : ‖g₁‖ ^ 2 = ‖d‖ ^ 2 - 2 * ⟪d, J p⟫ + ‖p‖ ^ 2 := by
    rw [hg₁, norm_sub_sq_real, norm_apply hJ]
  have hnorm₂ : ‖a.re • g₁ + a.im • p‖ ^ 2 = a.re ^ 2 * ‖d‖ ^ 2 +
      (a.re ^ 2 + a.im ^ 2) * ‖p‖ ^ 2 - 2 * a.re ^ 2 * ⟪d, J p⟫ + 2 * a.re * a.im * ⟪d, p⟫ := by
    simp only [hg₁, norm_add_sq_real, norm_smul, mul_pow, norm_sub_sq_real, norm_apply hJ,
      real_inner_smul_left, real_inner_smul_right, inner_sub_left, hpJp, Real.norm_eq_abs, sq_abs]
    ring
  rw [hnorm₁, hnorm₂]
  exact two_mul_mul_sub_le hε (by positivity) (by positivity) (inner_sq_add_inner_sq_le hJ d p)

end TauCeti.AlmostComplexStructure
