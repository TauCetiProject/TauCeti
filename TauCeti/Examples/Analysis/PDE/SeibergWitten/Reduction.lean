/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowSubstitution
public import TauCeti.Analysis.Complex.Wirtinger.FlatTorus.SmoothInverse
public import TauCeti.Analysis.Normed.Operator.QuadraticCorrection.FiniteModel
public import TauCeti.RingTheory.Polynomial.PrescribedPowerSums

/-!
# Examples: normalizations of the reduction near a pseudoholomorphic curve

Taubes's construction of Seiberg–Witten solutions near an embedded pseudoholomorphic curve `C`
inserts vortices along `C` and reduces the equations to finitely many dimensions. Several of its
normalizations can be tested on explicit data: the Newton recursion that turns the normal moments
of the curvature current into the coefficients of a monic polynomial, the exponent margins of the
coefficient estimates, the tolerance of the forcing, and the flat normal line of a covered torus.
This file checks each of them on an example, and shows how the competing convention would fail.

**Newton coefficients of two points.** The coefficients `b_j` of the moments `M_k` are defined by
`b₀ = 1` and `j b_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} M_k` (`TauCeti.newtonCoeff`). For the
counting measure of two points `V₁, V₂`, `M_k = V₁ᵏ + V₂ᵏ`, the recursion gives `b₁ = V₁ + V₂`
(`newtonCoeff_one_pair`) and `2 b₂ = b₁ M₁ - M₂ = 2 V₁ V₂` (`two_mul_newtonCoeff_two_pair`,
`newtonCoeff_one_pair_mul_sub`), so
`b₂ = V₁ V₂` (`newtonCoeff_two_pair`) and the polynomial `W² - b₁ W + b₂` is `(W - V₁) (W - V₂)`
(`newtonPolynomial_pair`). The recursion without the factor `j` would give `b₂ = b₁ M₁ - M₂`,
which is `2 V₁ V₂` and differs from the elementary symmetric function `V₁ V₂` as soon as
`V₁ V₂ ≠ 0` (`newtonCoeff_one_pair_mul_sub_ne`).

**The exponent margins.** For `m` sheets the coefficient estimates use `p_m = 2 + 2 / m`. Against
the branch exponent `1 - 1 / m` the margin is `p_m (1 - 1 / m) = 2 - 2 / m² < 2`
(`TauCeti.two_add_two_div_mul_one_sub_inv`, `TauCeti.two_add_two_div_mul_one_sub_inv_lt_two`),
and at `m = 1` the exponent is `0`, the nonsingular case
(`two_add_two_div_one_mul_one_sub_inv_one`). Against `1 - 2 / k` for `0 < k ≤ m` it is
`p_m (1 - 2 / k) ≤ p_m (1 - 2 / m) = 2 - 2 / m - 4 / m² < 2`
(`TauCeti.two_add_two_div_mul_one_sub_two_div`,
`TauCeti.two_add_two_div_mul_one_sub_two_div_lt_two`). The Morrey exponent `1 - 2 / p_m` of
`W^{1, p_m}` in the plane is `1 / (m + 1)`, the Hölder exponent of the limit coefficients in
`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_esymm_of_eq`.

**The forcing tolerance.** A tolerance `τ` for the forcing must satisfy
`16 C² L (1 + B) τ ≤ 1` (`TauCeti.IsForcingTolerance`); with the unforced residual
`2 C² L ε < 1 / 4` this keeps the forced contraction constant `2 C² L (ε + B τ)` below `3 / 8`
(`TauCeti.IsForcingTolerance.two_mul_sq_mul_mul_add_mul_lt`). For `C = L = 1` and `B = 8`,
`τ = 1 / 144` is a tolerance (`isForcingTolerance_one_one_eight_one_div_one_hundred_forty_four`),
and the contraction constant stays below `3 / 8` (`two_mul_add_eight_mul_lt`). The budget without
the factor `1 + B`, `16 C² L τ ≤ 1`, admits `τ = 1 / 16`, which is not a tolerance
(`sixteen_mul_le_one_and_not_isForcingTolerance_one_one_eight_one_div_sixteen`): there the forcing
term alone makes the contraction constant at least `1` (`one_le_two_mul_add_eight_mul`).

**A covered torus with a flat normal line of irrational holonomy.** On the square torus
`ℂ / (ℤ + ℤ i)` take the flat line `N` with holonomy `exp (2πi √2)` along `1` and trivial
holonomy along `i`. Every nonzero power `N ^ j`, pulled back to every finite cover, is a
nontrivial flat line, so its smooth sections `u` with `∂bar u = 0` vanish
(`eq_zero_of_conjWirtingerDeriv_eq_zero_sqrt_two`): the summands `N ^ j` of the divisor bundles
`N ⊕ N² ⊕ ⋯ ⊕ Nᵐ` have no holomorphic sections. Irrationality is needed: for the line of
holonomy `exp (2πi / 2) = -1` along `1`, the square has trivial holonomy and the constant section
is holomorphic (`not_injective_flatLineConjWirtingerDerivₗ_two_mul_half`).

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

noncomputable section

open Complex Polynomial
open scoped ComplexConjugate ContDiff

namespace TauCeti.Examples.Reduction

/-! ### Newton coefficients of the counting measure of two points -/

section Newton

variable {K : Type*} [Field K] (V₁ V₂ : K)

/-- The moments `M_k = V₁ᵏ + V₂ᵏ` of the counting measure of `V₁, V₂` are the power sums of the
multiset `{V₁, V₂}`. -/
private theorem pow_add_pow_eq_sum_map (k : ℕ) :
    V₁ ^ k + V₂ ^ k = (({V₁, V₂} : Multiset K).map (· ^ k)).sum := by
  simp

variable [CharZero K]

/-- The Newton recursion at `j = 1`: `b₁ = M₁ = V₁ + V₂`. -/
theorem newtonCoeff_one_pair : newtonCoeff (fun k ↦ V₁ ^ k + V₂ ^ k) 1 = V₁ + V₂ := by
  simp_rw [pow_add_pow_eq_sum_map, newtonCoeff_sum_map_pow]
  simp [Multiset.esymm, Multiset.powersetCard_one, add_comm]

/-- The Newton recursion at `j = 2`: `2 b₂ = b₁ M₁ - M₂`. -/
theorem two_mul_newtonCoeff_two_pair :
    2 * newtonCoeff (fun k ↦ V₁ ^ k + V₂ ^ k) 2 =
      newtonCoeff (fun k ↦ V₁ ^ k + V₂ ^ k) 1 * (V₁ ^ 1 + V₂ ^ 1) - (V₁ ^ 2 + V₂ ^ 2) := by
  have h := mul_newtonCoeff_eq_sum (fun k ↦ V₁ ^ k + V₂ ^ k) 2
  have hsum : ((Finset.antidiagonal 2).filter fun a : ℕ × ℕ ↦ a.1 < 2) = {(0, 2), (1, 1)} := by
    decide
  rw [hsum, Finset.sum_pair (by decide), newtonCoeff_zero] at h
  push_cast at h
  linear_combination h

/-- For two points, `b₁ M₁ - M₂ = (V₁ + V₂)² - (V₁² + V₂²) = 2 V₁ V₂`. This is also the value
of `b₂` that the recursion without the factor `j` would give. -/
theorem newtonCoeff_one_pair_mul_sub :
    newtonCoeff (fun k ↦ V₁ ^ k + V₂ ^ k) 1 * (V₁ ^ 1 + V₂ ^ 1) - (V₁ ^ 2 + V₂ ^ 2) =
      2 * (V₁ * V₂) := by
  rw [newtonCoeff_one_pair]
  ring

/-- **The second Newton coefficient of two points** is their product `V₁ V₂`. -/
theorem newtonCoeff_two_pair : newtonCoeff (fun k ↦ V₁ ^ k + V₂ ^ k) 2 = V₁ * V₂ :=
  mul_left_cancel₀ two_ne_zero <|
    (two_mul_newtonCoeff_two_pair V₁ V₂).trans (newtonCoeff_one_pair_mul_sub V₁ V₂)

/-- **The Newton polynomial of two points** is `(W - V₁) (W - V₂)`. -/
theorem newtonPolynomial_pair :
    newtonPolynomial (fun k ↦ V₁ ^ k + V₂ ^ k) 2 = (X - C V₁) * (X - C V₂) := by
  simp_rw [pow_add_pow_eq_sum_map]
  have h := newtonPolynomial_sum_map_pow ({V₁, V₂} : Multiset K)
  simpa using h

/-- **The recursion without the factor `j` is wrong.** Unless `V₁ V₂ = 0`, the value `b₁ M₁ - M₂`
is not the second Newton coefficient `V₁ V₂` of two points. -/
theorem newtonCoeff_one_pair_mul_sub_ne (h : V₁ * V₂ ≠ 0) :
    newtonCoeff (fun k ↦ V₁ ^ k + V₂ ^ k) 1 * (V₁ ^ 1 + V₂ ^ 1) - (V₁ ^ 2 + V₂ ^ 2) ≠
      newtonCoeff (fun k ↦ V₁ ^ k + V₂ ^ k) 2 := by
  rw [newtonCoeff_one_pair_mul_sub, newtonCoeff_two_pair]
  intro h'
  exact h (by linear_combination h')

end Newton

/-! ### The exponent margin at one sheet -/

/-- At `m = 1` the margin exponent `p_m (1 - 1 / m) = 2 - 2 / m²` is `0`: a single sheet is
nonsingular. This is `TauCeti.two_add_two_div_mul_one_sub_inv` at `m = 1`. -/
theorem two_add_two_div_one_mul_one_sub_inv_one : (2 + 2 / (1 : ℝ)) * (1 - 1⁻¹) = 0 := by
  rw [two_add_two_div_mul_one_sub_inv one_ne_zero]
  norm_num

/-! ### The forcing tolerance -/

section Forcing

open scoped NNReal

variable {ε : ℝ}

/-- For `C = L = 1` and `B = 8`, `τ = 1 / 144` is a forcing tolerance, with `δ = b = 1`. -/
theorem isForcingTolerance_one_one_eight_one_div_one_hundred_forty_four :
    IsForcingTolerance 1 1 8 1 1 (1 / 144) where
  nonneg := by norm_num
  sixteen_mul_sq_mul_mul_one_add_mul_le_one := by norm_num
  eight_mul_mul_one_add_mul_le := by norm_num
  four_mul_one_add_mul_le := by norm_num

/-- With the tolerance `1 / 144` and an unforced residual `2 ε < 1 / 4`, the forced contraction
constant `2 (ε + 8 τ)` stays below `3 / 8`. -/
theorem two_mul_add_eight_mul_lt (hε : 2 * ε < 1 / 4) :
    2 * (ε + 8 * (1 / 144)) < 3 / 8 := by
  have h := isForcingTolerance_one_one_eight_one_div_one_hundred_forty_four
    |>.two_mul_sq_mul_mul_add_mul_lt (ε := ε) (by simpa using hε)
  simpa using h

/-- **The budget without the factor `1 + B` is not a tolerance.** For `C = L = 1` and `B = 8`,
`τ = 1 / 16` meets `16 C² L τ ≤ 1` but not `16 C² L (1 + B) τ ≤ 1`. -/
theorem sixteen_mul_le_one_and_not_isForcingTolerance_one_one_eight_one_div_sixteen
    {δ b : ℝ} :
    16 * (1 : ℝ) ^ 2 * 1 * (1 / 16) ≤ 1 ∧ ¬ IsForcingTolerance 1 1 8 δ b (1 / 16) := by
  refine ⟨by norm_num, fun h ↦ ?_⟩
  have h₁ := h.sixteen_mul_sq_mul_mul_one_add_mul_le_one
  norm_num at h₁

/-- With `τ = 1 / 16` and `B = 8` the forcing term alone makes the contraction constant
`2 (ε + B τ)` at least `1`, for every residual `ε ≥ 0`. -/
theorem one_le_two_mul_add_eight_mul (hε : 0 ≤ ε) : 1 ≤ 2 * (ε + 8 * (1 / 16)) := by
  linarith

end Forcing

/-! ### Flat normal lines of a covered torus -/

section FlatLine

/-- The square lattice `ℤ + ℤ i` is a lattice: `Im (conj 1 · i) ≠ 0`. -/
private theorem im_conj_one_mul_I_ne_zero : (conj (1 : ℂ) * I).im ≠ 0 := by
  simp

/-- **A flat line of irrational holonomy has no holomorphic sections on any power or cover.** Let
`N` be the flat line over `ℂ / (ℤ + ℤ i)` with holonomy `exp (2πi √2)` along `1` and trivial
holonomy along `i`. For `j ≠ 0` and a finite cover with lattice basis `a + b i, c + d i`,
`a d - b c ≠ 0`, every smooth section `u` of `N ^ j` pulled back to the cover with `∂bar u = 0`
vanishes. -/
theorem eq_zero_of_conjWirtingerDeriv_eq_zero_sqrt_two {j a b c d : ℤ} (hj : j ≠ 0)
    (hdet : a * d - b * c ≠ 0) {u : ℂ → ℂ}
    (hu : u ∈ flatLineSections ∞ (a + b * I) (c + d * I) (j * a * √2) (j * c * √2))
    (h : ∀ z, conjWirtingerDeriv u z 1 = 0) : u = 0 := by
  have hinj := (bijective_flatLineConjWirtingerDerivₗ_of_irrational (θ₂ := 0)
    (Or.inl irrational_sqrt_two) im_conj_one_mul_I_ne_zero hj hdet).1
  refine congrArg Subtype.val (@hinj ⟨u, by convert hu using 2 <;> ring⟩ 0 ?_)
  rw [map_zero]
  exact Subtype.ext <| by rw [coe_flatLineConjWirtingerDerivₗ_apply]; exact funext h

/-- **Irrationality is needed.** For the flat line over `ℂ / (ℤ + ℤ i)` with holonomy
`exp (2πi / 2) = -1` along `1` and trivial holonomy along `i`, the square has trivial holonomy,
and `∂bar` has the constant section in its kernel. -/
theorem not_injective_flatLineConjWirtingerDerivₗ_two_mul_half :
    ¬ Function.Injective (flatLineConjWirtingerDerivₗ 1 I (2 * (1 / 2)) 0) := by
  have hconst : (fun _ : ℂ ↦ (1 : ℂ)) ∈ flatLineSections ∞ 1 I (2 * (1 / 2)) 0 := by
    refine mem_flatLineSections.2 ⟨contDiff_const, fun _ ↦ ?_, fun _ ↦ by simp⟩
    have : (2 : ℂ) * Real.pi * ((2 * (1 / 2) : ℝ) : ℂ) * I = 2 * Real.pi * I := by
      push_cast; ring
    rw [this, exp_two_pi_mul_I, mul_one]
  intro hinj
  have h0 : flatLineConjWirtingerDerivₗ 1 I (2 * (1 / 2)) 0 ⟨_, hconst⟩ =
      flatLineConjWirtingerDerivₗ 1 I (2 * (1 / 2)) 0 0 := by
    rw [map_zero]
    refine Subtype.ext ?_
    rw [coe_flatLineConjWirtingerDerivₗ_apply]
    funext z
    simp
  have := congrArg (fun v : flatLineSections ∞ 1 I (2 * (1 / 2)) 0 ↦ (v : ℂ → ℂ) 0) (hinj h0)
  simp at this

end FlatLine

end TauCeti.Examples.Reduction
