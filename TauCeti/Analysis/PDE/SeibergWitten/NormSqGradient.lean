/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

/-!
# The gradient of `|α|²` against the `∂bar`-part of `∇_a α`

For a section `α` of a trivial Hermitian line with connection form `a = i b`, the differential of
`|α|²` is `2 Re (conj α ∇_a α)`, so `|∇ |α|²| ≤ 2 |α| |∇_a α|`
(`TauCeti.SeibergWitten.norm_fderiv_norm_sq_le_mul_norm_covariantDeriv`). When `∇_a α` is
complex-linear for an orthogonal complex structure `J`, the identity
`|∇ |α|²|² = 2 |α|² |∇_a α|²` holds instead, with Hilbert–Schmidt norms. This file proves a lower
bound on `|∇ |α|²|²` that keeps the factor `2` and pays for it with the `J`-antilinear part
`∂bar_a α` (`TauCeti.SeibergWitten.covariantDBar`): for every `ε > 0`,

`2 |α|² ((1 - ε) |∇_a α|² - (2 + 18 / ε) |∂bar_a α|²) ≤ |∇ |α|²|²`

(`TauCeti.SeibergWitten.two_mul_norm_sq_mul_sub_le_norm_gradient_norm_sq`). This is linear algebra
for one real-linear map `L : E → ℂ` and one value `a ∈ ℂ`
(`TauCeti.SeibergWitten.two_mul_norm_sq_mul_sub_le_sum_sq_re`): writing the real and imaginary
parts of `L` as `⟪g₁, ·⟫` and `⟪p, ·⟫`, the antilinear part is represented by `d = g₁ + J p`, and
the defect is bounded by `|d|` through Bessel's inequality for the orthogonal pair `p`, `J p`
(`TauCeti.AlmostComplexStructure.inner_sq_add_inner_sq_le`).

The factor `2` is what cancels the gradient term of `Δ log |α|²`, so that `-log |α|²` satisfies a
screened inequality where `|α|` is bounded below; see
`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.VacuumDecay`.

## Main results

* `TauCeti.SeibergWitten.two_mul_norm_sq_mul_sub_le_sum_sq_re`: the pointwise linear algebra.
* `TauCeti.SeibergWitten.two_mul_norm_sq_mul_sub_le_norm_gradient_norm_sq`: the gradient of
  `|α|²` against `∂bar_a α`.
-/

public section

open Complex InnerProductSpace
open scoped ComplexConjugate RealInnerProductSpace Gradient

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

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

omit [FiniteDimensional ℝ E] in
/-- If `g₁` and `p` represent the real and imaginary parts of `L : E → ℂ`, then
`∑ᵢ |(L eᵢ + i L (J eᵢ)) / 2|² = ‖g₁ + J p‖² / 2`: the vector `g₁ + J p` represents the real part
of `2 ∂bar L`, and `p - J g₁ = -J (g₁ + J p)` its imaginary part. -/
private theorem sum_norm_sq_div_two_eq {ι : Type*} [Fintype ι] {J : AlmostComplexStructure E}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (e : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℂ) {g₁ p : E}
    (h₁ : ∀ v, ⟪g₁, v⟫ = (L v).re) (h₂ : ∀ v, ⟪p, v⟫ = (L v).im) :
    ∑ i, ‖(L (e i) + I * L (J (e i))) / 2‖ ^ 2 = ‖g₁ + J p‖ ^ 2 / 2 := by
  have hd' : p - J g₁ = -J (g₁ + J p) := by
    simp only [J.apply_add, J.apply_apply]
    abel
  have hsum : ∑ i, ‖(L (e i) + I * L (J (e i))) / 2‖ ^ 2 =
      (∑ i, ⟪g₁ + J p, e i⟫ ^ 2 + ∑ i, ⟪p - J g₁, e i⟫ ^ 2) / 4 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hJ₁ : ⟪J g₁, e i⟫ = -(L (J (e i))).re := by
      rw [AlmostComplexStructure.inner_apply_left hJ, h₁]
    have hJ₂ : ⟪J p, e i⟫ = -(L (J (e i))).im := by
      rw [AlmostComplexStructure.inner_apply_left hJ, h₂]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [inner_add_left, inner_sub_left, h₁, h₂, hJ₁, hJ₂, div_re, div_im, add_re,
      add_im, mul_re, mul_im, I_re, I_im]
    norm_num
    ring
  rw [hsum, e.sum_sq_inner_left, e.sum_sq_inner_left, hd', norm_neg,
    AlmostComplexStructure.norm_apply hJ]
  ring

/-- **The gradient of `|α|²` against the `∂bar`-part of `∇α`, pointwise.** Let `J` be an
orthogonal complex structure on `E`, `e` an orthonormal basis, `L : E → ℂ` real-linear (the
covariant derivative `∇_a α` at a point) and `a ∈ ℂ` (the value `α` there). Write
`|L|² = ∑ᵢ |L eᵢ|²` and `|∂bar L|² = ∑ᵢ |∂bar L eᵢ|²` with `∂bar L v = (L v + i L (J v)) / 2`.
Then the differential `v ↦ 2 Re (conj a · L v)` of `|α|²` satisfies, for every `ε > 0`,

`2 |a|² ((1 - ε) |L|² - (2 + 18 / ε) |∂bar L|²) ≤ ∑ᵢ (2 Re (conj a · L eᵢ))²`. -/
theorem two_mul_norm_sq_mul_sub_le_sum_sq_re {ι : Type*} [Fintype ι]
    (J : AlmostComplexStructure E) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (e : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℂ) (a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    2 * ‖a‖ ^ 2 * ((1 - ε) * ∑ i, ‖L (e i)‖ ^ 2 -
        (2 + 18 / ε) * ∑ i, ‖(L (e i) + I * L (J (e i))) / 2‖ ^ 2) ≤
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
  have hQ : ∑ i, ‖(L (e i) + I * L (J (e i))) / 2‖ ^ 2 = ‖d‖ ^ 2 / 2 :=
    sum_norm_sq_div_two_eq hJ e L h₁ h₂
  have hre : ∑ i, (2 * (conj a * L (e i)).re) ^ 2 = 4 * ‖a.re • g₁ + a.im • p‖ ^ 2 := by
    rw [← e.sum_sq_inner_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [inner_add_left, real_inner_smul_left, h₁, h₂, mul_re, conj_re, conj_im]
    ring
  rw [hL, hQ, hre, Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq]
  -- Write `g₁ = d - J p` and expand in the inner products `⟪d, J p⟫` and `⟪d, p⟫`.
  have hg₁ : g₁ = d - J p := (add_sub_cancel_right g₁ (J p)).symm
  have hpJp : ⟪J p, p⟫ = 0 := AlmostComplexStructure.inner_apply_self hJ p
  have hJpJp : ⟪J p, J p⟫ = ‖p‖ ^ 2 := by rw [hJ, real_inner_self_eq_norm_sq]
  have hnorm₁ : ‖g₁‖ ^ 2 = ‖d‖ ^ 2 - 2 * ⟪d, J p⟫ + ‖p‖ ^ 2 := by
    rw [hg₁, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [hJpJp, real_inner_self_eq_norm_sq, real_inner_comm d (J p)]
    ring
  have hnorm₂ : ‖a.re • g₁ + a.im • p‖ ^ 2 = a.re ^ 2 * ‖d‖ ^ 2 +
      (a.re ^ 2 + a.im ^ 2) * ‖p‖ ^ 2 - 2 * a.re ^ 2 * ⟪d, J p⟫ + 2 * a.re * a.im * ⟪d, p⟫ := by
    rw [hg₁, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hJpJp, hpJp, real_inner_comm (J p) p, hpJp, real_inner_comm d (J p),
      real_inner_comm d p, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  rw [hnorm₁, hnorm₂]
  exact two_mul_mul_sub_le hε (by positivity) (by positivity)
    (AlmostComplexStructure.inner_sq_add_inner_sq_le hJ d p)

/-- **The gradient of `|α|²` against `∂bar_a α`.** For a section `α` of the trivial line,
differentiable at `x`, a connection form `b`, an orthogonal complex structure `J` and an
orthonormal basis `e`, write `|∇_a α|² = ∑ᵢ |∇_a α (eᵢ)|²` and `|∂bar_a α|² = ∑ᵢ |∂bar_a α (eᵢ)|²`
at `x`. Then for every `ε > 0`

`2 |α|² ((1 - ε) |∇_a α|² - (2 + 18 / ε) |∂bar_a α|²) ≤ |∇ |α|²|²`.

The factor `2` in front of `|α|² |∇_a α|²` is what cancels the gradient term of
`Δ log |α|²`. -/
theorem two_mul_norm_sq_mul_sub_le_norm_gradient_norm_sq {ι : Type*} [Fintype ι]
    (J : AlmostComplexStructure E) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (e : OrthonormalBasis ι ℝ E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) {α : E → ℂ} {x : E}
    (hα : DifferentiableAt ℝ α x) {ε : ℝ} (hε : 0 < ε) :
    2 * ‖α x‖ ^ 2 * ((1 - ε) * ∑ i, ‖covariantDeriv b α x (e i)‖ ^ 2 -
        (2 + 18 / ε) * ∑ i, ‖covariantDBar J b α x (e i)‖ ^ 2) ≤
      ‖∇ (fun y ↦ ‖α y‖ ^ 2) x‖ ^ 2 := by
  have h := two_mul_norm_sq_mul_sub_le_sum_sq_re J hJ e (covariantDeriv b α x) (α x) hε
  simp only [← covariantDBar_apply] at h
  rw [← e.sum_sq_inner_left]
  simpa only [inner_gradient_left,
    fderiv_norm_sq_apply_eq_re_conj_mul_covariantDeriv (b := b) hα] using h

end TauCeti.SeibergWitten
