/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Plumbing
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The path of input configurations joining the two compositions of a product

A sphere with three moving input ends has input punctures at centers `c i ∈ ℂ`, with end lifts
`z ↦ c i + a i φ₀(z)` of nonzero scales `a i`, and its output puncture at `∞`. Its input end `i`
occupies the disc `‖w - c i‖ < ‖a i‖ / 2`. Composing two pair-of-pants products by plumbing gives
such a sphere for each of the two ways of bracketing three inputs `x₁, x₂, x₃`. With the plumbing
radius `f = e^{-2πL} / 4` of neck length `L`:

* `(x₁ x₂) x₃`, inserting a pair of pants into the input `0` of another, has centers `0, f, 1` and
  scales `f, -f, -1`: the two inserted inputs sit at `c₀ = 0` and `ψ₀(1) = f`, and `x₃` at the
  input `1` of the receiving pair of pants;
* `x₁ (x₂ x₃)`, inserting into the input `1`, has the input `x₁` at the input `0` of the receiving
  pair of pants, so at center `0` with scale `1`, and the inserted inputs at `c₁ = 1` and
  `ψ₁(1) = 1 - f`, with scales `-f` and `f`, since the plumbing factor at `1` is `-f`.

This file constructs a smooth path `τ ↦ (associativityCenters f τ, associativityScales f τ)` from
the first configuration, for `τ ≤ 0`, to the second, for `τ ≥ 4`, along which the end discs stay
pairwise disjoint and bounded, for every radius `0 < f ≤ 1 / 3`. In the order of the inputs
`x₁, x₂, x₃`, the inputs `x₂` and `x₃` have exchanged their positions on the real line, and the
asymptotic marker of `x₃` has turned by a half-turn. The path runs in four steps, each driven by
one smooth transition `β_k(τ) = smoothTransition (τ - k)`, `0 ≤ k ≤ 3`:

1. `x₃` shrinks its disc from radius `1 / 2` to `f / 2` while its scale turns from `-1` to `f`;
2. `x₂` moves up from `f` to `f + i`;
3. `x₂` moves across to `1 + i` over `x₃`, while `x₃` moves from `1` to `1 - f` and the disc of
   `x₁` grows from radius `f / 2` to `1 / 2`;
4. `x₂` moves down to `1`.

Since `β_k` is constant outside `[k, k + 1]`, the path is the sum of these four motions and is
smooth on all of `ℝ`, jointly in `f` and `τ`.

## Main definitions and results

In the namespace `TauCeti.ThricePuncturedSphere`:

* `associativityCenters f τ` and `associativityScales f τ`: the centers and scales of the path.
* `associativityCenters_of_nonpos`, `associativityScales_of_nonpos`,
  `associativityCenters_of_four_le` and `associativityScales_of_four_le`: its two ends, which for
  the radius `e^{-2πL} / 4` are the configurations of the two plumbed spheres
  (`associativityCenters_eq_plumbingMap_zero`, `associativityScales_eq_plumbingFactor_zero`,
  `associativityCenters_eq_plumbingMap_one`, `associativityScales_eq_plumbingFactor_one`).
* `associativityScales_ne_zero`: the scales never vanish.
* `pairwise_norm_associativityScales_add_le`: the end discs are pairwise disjoint.
* `norm_associativityCenters_add_le`: the end discs lie in the disc `‖w‖ ≤ 3`.
* `contDiff_associativityCenters` and `contDiff_associativityScales`: smoothness.

## References

* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 12, on
  families of punctured discs and spheres over the associahedra and their ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product.
-/

public noncomputable section

open Complex Real

namespace TauCeti.ThricePuncturedSphere

variable {f τ : ℝ}

/-- **The centers of the input ends along the associativity path.** For the plumbing radius `f`,
the centers `0`, `f + (1 - f) β₂(τ) + i (β₁(τ) - β₃(τ))` and `1 - f β₂(τ)` of the inputs
`x₁, x₂, x₃`, where `β_k(τ) = smoothTransition (τ - k)`. -/
def associativityCenters (f τ : ℝ) : Fin 3 → ℂ :=
  ![0, ((f + (1 - f) * smoothTransition (τ - 2) : ℝ) : ℂ) +
      ((smoothTransition (τ - 1) - smoothTransition (τ - 3) : ℝ) : ℂ) * I,
    ((1 - f * smoothTransition (τ - 2) : ℝ) : ℂ)]

/-- **The scales of the input ends along the associativity path.** For the plumbing radius `f`,
the scales `f + (1 - f) β₂(τ)`, `-f` and `-(1 - (1 - f) β₀(τ)) e^{iπ β₀(τ)}` of the inputs
`x₁, x₂, x₃`, where `β_k(τ) = smoothTransition (τ - k)`. -/
def associativityScales (f τ : ℝ) : Fin 3 → ℂ :=
  ![((f + (1 - f) * smoothTransition (τ - 2) : ℝ) : ℂ), -(f : ℂ),
    -((1 - (1 - f) * smoothTransition τ : ℝ) : ℂ) * Complex.exp ((π * smoothTransition τ : ℝ) * I)]

@[simp]
theorem associativityCenters_zero (f τ : ℝ) : associativityCenters f τ 0 = 0 :=
  (rfl)

theorem associativityCenters_one (f τ : ℝ) :
    associativityCenters f τ 1 = ((f + (1 - f) * smoothTransition (τ - 2) : ℝ) : ℂ) +
      ((smoothTransition (τ - 1) - smoothTransition (τ - 3) : ℝ) : ℂ) * I :=
  (rfl)

theorem associativityCenters_two (f τ : ℝ) :
    associativityCenters f τ 2 = ((1 - f * smoothTransition (τ - 2) : ℝ) : ℂ) :=
  (rfl)

theorem associativityScales_zero (f τ : ℝ) :
    associativityScales f τ 0 = ((f + (1 - f) * smoothTransition (τ - 2) : ℝ) : ℂ) :=
  (rfl)

@[simp]
theorem associativityScales_one (f τ : ℝ) : associativityScales f τ 1 = -(f : ℂ) :=
  (rfl)

theorem associativityScales_two (f τ : ℝ) :
    associativityScales f τ 2 = -((1 - (1 - f) * smoothTransition τ : ℝ) : ℂ) *
      Complex.exp ((π * smoothTransition τ : ℝ) * I) :=
  (rfl)

/-! ### The ends of the path -/

/-- **The start of the path is the composition `(x₁ x₂) x₃`.** For `τ ≤ 0` the centers are
`0, f, 1`. -/
theorem associativityCenters_of_nonpos (hτ : τ ≤ 0) :
    associativityCenters f τ = ![0, (f : ℂ), 1] := by
  funext i
  fin_cases i <;>
    simp [associativityCenters_one, associativityCenters_two,
      smoothTransition.zero_of_nonpos (by linarith : τ - 1 ≤ 0),
      smoothTransition.zero_of_nonpos (by linarith : τ - 2 ≤ 0),
      smoothTransition.zero_of_nonpos (by linarith : τ - 3 ≤ 0)]

/-- **The start of the path is the composition `(x₁ x₂) x₃`.** For `τ ≤ 0` the scales are
`f, -f, -1`. -/
theorem associativityScales_of_nonpos (hτ : τ ≤ 0) :
    associativityScales f τ = ![(f : ℂ), -(f : ℂ), -1] := by
  funext i
  fin_cases i <;>
    simp [associativityScales_zero, associativityScales_two, smoothTransition.zero_of_nonpos hτ,
      smoothTransition.zero_of_nonpos (by linarith : τ - 2 ≤ 0)]

/-- **The end of the path is the composition `x₁ (x₂ x₃)`.** For `τ ≥ 4` the centers are
`0, 1, 1 - f`. -/
theorem associativityCenters_of_four_le (hτ : 4 ≤ τ) :
    associativityCenters f τ = ![0, 1, ((1 - f : ℝ) : ℂ)] := by
  funext i
  fin_cases i <;>
    simp [associativityCenters_one, associativityCenters_two,
      smoothTransition.one_of_one_le (by linarith : 1 ≤ τ - 1),
      smoothTransition.one_of_one_le (by linarith : 1 ≤ τ - 2),
      smoothTransition.one_of_one_le (by linarith : 1 ≤ τ - 3)]

/-- **The end of the path is the composition `x₁ (x₂ x₃)`.** For `τ ≥ 4` the scales are
`1, -f, f`. -/
theorem associativityScales_of_four_le (hτ : 4 ≤ τ) :
    associativityScales f τ = ![1, -(f : ℂ), (f : ℂ)] := by
  funext i
  fin_cases i <;>
    simp [associativityScales_zero, associativityScales_two,
      smoothTransition.one_of_one_le (by linarith : 1 ≤ τ),
      smoothTransition.one_of_one_le (by linarith : 1 ≤ τ - 2)]

open Puncture in
/-- **The start of the path is the plumbed sphere at the input `0`.** For the plumbing radius
`e^{-2πL} / 4` of neck length `L` and `τ ≤ 0`, the centers are those of the plumbed sphere
`ℂ ∖ {c₀, ψ₀(1), c₁}`. -/
theorem associativityCenters_eq_plumbingMap_zero (L : ℝ) (hτ : τ ≤ 0) :
    associativityCenters (Real.exp (-(2 * π * L)) / 4) τ =
      ![zero.endCenter, zero.plumbingMap L 1, one.endCenter] := by
  rw [associativityCenters_of_nonpos hτ, plumbingMap_apply, plumbingFactor_zero]
  simp

open Puncture in
/-- **The start of the path is the plumbed sphere at the input `0`.** For the plumbing radius
`e^{-2πL} / 4` of neck length `L` and `τ ≤ 0`, the scales are those of the plumbed sphere: the
plumbing factor `f₀` at the two inserted inputs, with signs, and `2 b₁` at the input `1`. -/
theorem associativityScales_eq_plumbingFactor_zero (L : ℝ) (hτ : τ ≤ 0) :
    associativityScales (Real.exp (-(2 * π * L)) / 4) τ =
      ![zero.plumbingFactor L, -zero.plumbingFactor L, 2 * one.endScale] := by
  rw [associativityScales_of_nonpos hτ, plumbingFactor_zero, endScale_one]
  norm_num

open Puncture in
/-- **The end of the path is the plumbed sphere at the input `1`.** For the plumbing radius
`e^{-2πL} / 4` of neck length `L` and `τ ≥ 4`, the centers are those of the plumbed sphere
`ℂ ∖ {c₀, c₁, ψ₁(1)}`, listing the uninserted input first. -/
theorem associativityCenters_eq_plumbingMap_one (L : ℝ) (hτ : 4 ≤ τ) :
    associativityCenters (Real.exp (-(2 * π * L)) / 4) τ =
      ![zero.endCenter, one.endCenter, one.plumbingMap L 1] := by
  rw [associativityCenters_of_four_le hτ, plumbingMap_apply, plumbingFactor_one,
    plumbingFactor_zero]
  simp [sub_eq_add_neg]

open Puncture in
/-- **The end of the path is the plumbed sphere at the input `1`.** For the plumbing radius
`e^{-2πL} / 4` of neck length `L` and `τ ≥ 4`, the scales are those of the plumbed sphere: `2 b₀`
at the uninserted input `0`, and the plumbing factor `f₁ = -f₀` at the two inserted inputs, with
signs. -/
theorem associativityScales_eq_plumbingFactor_one (L : ℝ) (hτ : 4 ≤ τ) :
    associativityScales (Real.exp (-(2 * π * L)) / 4) τ =
      ![2 * zero.endScale, one.plumbingFactor L, -one.plumbingFactor L] := by
  rw [associativityScales_of_four_le hτ, plumbingFactor_one, plumbingFactor_zero, endScale_zero]
  norm_num

/-! ### The end discs along the path -/

/-- The scale of `x₁` has norm `f + (1 - f) β₂(τ)`. -/
theorem norm_associativityScales_zero (hf₀ : 0 ≤ f) (τ : ℝ) :
    ‖associativityScales f τ 0‖ = f + (1 - f) * smoothTransition (τ - 2) := by
  rw [associativityScales_zero, Complex.norm_real, Real.norm_of_nonneg]
  nlinarith [smoothTransition.nonneg (τ - 2), smoothTransition.le_one (τ - 2)]

/-- The scale of `x₂` has norm `f`. -/
theorem norm_associativityScales_one (hf₀ : 0 ≤ f) (τ : ℝ) :
    ‖associativityScales f τ 1‖ = f := by
  rw [associativityScales_one, norm_neg, Complex.norm_real, Real.norm_of_nonneg hf₀]

/-- The scale of `x₃` has norm `1 - (1 - f) β₀(τ)`. -/
theorem norm_associativityScales_two (hf₀ : 0 ≤ f) (τ : ℝ) :
    ‖associativityScales f τ 2‖ = 1 - (1 - f) * smoothTransition τ := by
  rw [associativityScales_two, norm_mul, norm_neg, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_of_nonneg]
  nlinarith [smoothTransition.nonneg τ, smoothTransition.le_one τ]

/-- The scales of the path never vanish. -/
theorem associativityScales_ne_zero (hf : 0 < f) (τ : ℝ) (i : Fin 3) :
    associativityScales f τ i ≠ 0 := by
  -- `f + (1 - f) β = (1 - β) f + β` is a convex combination of `f` and `1`.
  have hpos (β : ℝ) (h₀ : 0 ≤ β) (h₁ : β ≤ 1) : 0 < f + (1 - f) * β := by
    rcases le_or_gt β (1 / 2) with h | h <;> nlinarith
  fin_cases i
  · rw [Fin.zero_eta, associativityScales_zero, Complex.ofReal_ne_zero]
    exact (hpos _ (smoothTransition.nonneg _) (smoothTransition.le_one _)).ne'
  · simpa using hf.ne'
  · refine mul_ne_zero (neg_ne_zero.2 (Complex.ofReal_ne_zero.2 ?_)) (Complex.exp_ne_zero _)
    have h := hpos _ (sub_nonneg.2 (smoothTransition.le_one τ))
      (sub_le_self _ (smoothTransition.nonneg τ))
    exact (by linarith : 0 < 1 - (1 - f) * smoothTransition τ).ne'

/-- The second center lies to the right of the end disc of `x₁`. -/
private theorem norm_associativityScales_add_le_zero_one (hf₀ : 0 ≤ f) (hf : f ≤ 1 / 3)
    (τ : ℝ) :
    ‖associativityScales f τ 0‖ / 2 + ‖associativityScales f τ 1‖ / 2 ≤
      ‖associativityCenters f τ 0 - associativityCenters f τ 1‖ := by
  have h₂ := smoothTransition.nonneg (τ - 2)
  rw [associativityCenters_zero, zero_sub, norm_neg, norm_associativityScales_zero hf₀,
    norm_associativityScales_one hf₀]
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  simp only [associativityCenters_one, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero,
    I_im, mul_one, sub_self, add_zero]
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith

/-- Before `x₃` moves, its end disc has the other two on its left; once it moves, its disc has
shrunk. -/
private theorem norm_associativityScales_add_le_zero_two (hf₀ : 0 ≤ f) (hf : f ≤ 1 / 3)
    (τ : ℝ) :
    ‖associativityScales f τ 0‖ / 2 + ‖associativityScales f τ 2‖ / 2 ≤
      ‖associativityCenters f τ 0 - associativityCenters f τ 2‖ := by
  have h₀ := smoothTransition.nonneg τ
  have h₀' := smoothTransition.le_one τ
  have h₂' := smoothTransition.le_one (τ - 2)
  rw [associativityCenters_zero, zero_sub, norm_neg, associativityCenters_two,
    Complex.norm_real, Real.norm_of_nonneg (by nlinarith), norm_associativityScales_zero hf₀,
    norm_associativityScales_two hf₀]
  rcases le_or_gt τ 2 with hτ | hτ
  · rw [smoothTransition.zero_of_nonpos (by linarith : τ - 2 ≤ 0)]
    nlinarith
  · rw [smoothTransition.one_of_one_le (by linarith : 1 ≤ τ)]
    nlinarith

/-- `x₂` passes `x₃` above it, at height `1`, after `x₃` has shrunk its end disc. -/
private theorem norm_associativityScales_add_le_one_two (hf₀ : 0 ≤ f) (hf : f ≤ 1 / 3)
    (τ : ℝ) :
    ‖associativityScales f τ 1‖ / 2 + ‖associativityScales f τ 2‖ / 2 ≤
      ‖associativityCenters f τ 1 - associativityCenters f τ 2‖ := by
  have h₀ := smoothTransition.nonneg τ
  rw [norm_associativityScales_one hf₀, norm_associativityScales_two hf₀]
  have hre := Complex.abs_re_le_norm (associativityCenters f τ 1 - associativityCenters f τ 2)
  have him := Complex.abs_im_le_norm (associativityCenters f τ 1 - associativityCenters f τ 2)
  have hre' : (associativityCenters f τ 1 - associativityCenters f τ 2).re =
      f - 1 + smoothTransition (τ - 2) := by
    simp only [associativityCenters_one, associativityCenters_two, sub_re, add_re, ofReal_re,
      mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self, add_zero]
    ring
  have him' : (associativityCenters f τ 1 - associativityCenters f τ 2).im =
      smoothTransition (τ - 1) - smoothTransition (τ - 3) := by
    simp [associativityCenters_one, associativityCenters_two]
  rw [hre'] at hre
  rw [him'] at him
  rcases le_or_gt τ 1 with hτ | hτ
  · rw [smoothTransition.zero_of_nonpos (by linarith : τ - 2 ≤ 0),
      abs_of_nonpos (by linarith)] at hre
    nlinarith
  rw [smoothTransition.one_of_one_le (by linarith : 1 ≤ τ)]
  rcases le_or_gt τ 2 with hτ₂ | hτ₂
  · rw [smoothTransition.zero_of_nonpos (by linarith : τ - 2 ≤ 0),
      abs_of_nonpos (by linarith)] at hre
    linarith
  rcases le_or_gt τ 3 with hτ₃ | hτ₃
  · rw [smoothTransition.one_of_one_le (by linarith : 1 ≤ τ - 1),
      smoothTransition.zero_of_nonpos (by linarith : τ - 3 ≤ 0), sub_zero, abs_one] at him
    linarith
  · rw [smoothTransition.one_of_one_le (by linarith : 1 ≤ τ - 2),
      abs_of_nonneg (by linarith)] at hre
    linarith

/-- **The end discs stay pairwise disjoint along the path.** For a plumbing radius
`0 ≤ f ≤ 1 / 3`, the discs `‖w - c i‖ < ‖a i‖ / 2` of the three input ends are pairwise disjoint
for every `τ`. -/
theorem pairwise_norm_associativityScales_add_le (hf₀ : 0 ≤ f) (hf : f ≤ 1 / 3) (τ : ℝ) :
    Pairwise fun i j : Fin 3 =>
      ‖associativityScales f τ i‖ / 2 + ‖associativityScales f τ j‖ / 2 ≤
        ‖associativityCenters f τ i - associativityCenters f τ j‖ := by
  have h01 := norm_associativityScales_add_le_zero_one hf₀ hf τ
  have h02 := norm_associativityScales_add_le_zero_two hf₀ hf τ
  have h12 := norm_associativityScales_add_le_one_two hf₀ hf τ
  intro i j hij
  match i, j with
  | 0, 0 | 1, 1 | 2, 2 => exact absurd rfl hij
  | 0, 1 => exact h01
  | 0, 2 => exact h02
  | 1, 2 => exact h12
  | 1, 0 => rw [add_comm, norm_sub_rev]; exact h01
  | 2, 0 => rw [add_comm, norm_sub_rev]; exact h02
  | 2, 1 => rw [add_comm, norm_sub_rev]; exact h12

/-- **The end discs stay bounded along the path.** For a plumbing radius `0 ≤ f ≤ 1`, the disc
`‖w - c i‖ < ‖a i‖ / 2` of each input end lies in the disc `‖w‖ ≤ 3` for every `τ`. -/
theorem norm_associativityCenters_add_le (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (τ : ℝ) (i : Fin 3) :
    ‖associativityCenters f τ i‖ + ‖associativityScales f τ i‖ / 2 ≤ 3 := by
  have h₀ : 0 ≤ smoothTransition τ ∧ smoothTransition τ ≤ 1 :=
    ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  have h₂ : 0 ≤ smoothTransition (τ - 2) ∧ smoothTransition (τ - 2) ≤ 1 :=
    ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  have h₁ := smoothTransition.nonneg (τ - 1)
  have h₁' := smoothTransition.le_one (τ - 1)
  have h₃ := smoothTransition.nonneg (τ - 3)
  have h₃' := smoothTransition.le_one (τ - 3)
  fin_cases i
  · rw [Fin.zero_eta, associativityCenters_zero, norm_zero,
      norm_associativityScales_zero hf₀]
    nlinarith
  · rw [Fin.mk_one, norm_associativityScales_one hf₀, associativityCenters_one]
    have hc := norm_add_le ((f + (1 - f) * smoothTransition (τ - 2) : ℝ) : ℂ)
      (((smoothTransition (τ - 1) - smoothTransition (τ - 3) : ℝ) : ℂ) * I)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith), Real.norm_eq_abs] at hc
    have hd : |smoothTransition (τ - 1) - smoothTransition (τ - 3)| ≤ 1 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith
  · simp only [Fin.reduceFinMk]
    rw [associativityCenters_two, norm_associativityScales_two hf₀, Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith)]
    nlinarith

/-! ### Smoothness -/

/-- The centers of the path are smooth jointly in the plumbing radius and the parameter. -/
theorem contDiff_associativityCenters {n : ℕ∞} :
    ContDiff ℝ n fun p : ℝ × ℝ => associativityCenters p.1 p.2 := by
  have hβ (k : ℝ) : ContDiff ℝ n fun p : ℝ × ℝ => smoothTransition (p.2 - k) :=
    smoothTransition.contDiff.comp (contDiff_snd.sub contDiff_const)
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const
  · exact (ofRealCLM.contDiff.comp (contDiff_fst.add ((contDiff_const.sub contDiff_fst).mul
      (hβ 2)))).add ((ofRealCLM.contDiff.comp ((hβ 1).sub (hβ 3))).mul contDiff_const)
  · exact ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_fst.mul (hβ 2)))

/-- The scales of the path are smooth jointly in the plumbing radius and the parameter. -/
theorem contDiff_associativityScales {n : ℕ∞} :
    ContDiff ℝ n fun p : ℝ × ℝ => associativityScales p.1 p.2 := by
  have hβ (k : ℝ) : ContDiff ℝ n fun p : ℝ × ℝ => smoothTransition (p.2 - k) :=
    smoothTransition.contDiff.comp (contDiff_snd.sub contDiff_const)
  have hβ₀ : ContDiff ℝ n fun p : ℝ × ℝ => smoothTransition p.2 := by
    simpa using hβ 0
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact ofRealCLM.contDiff.comp (contDiff_fst.add ((contDiff_const.sub contDiff_fst).mul
      (hβ 2)))
  · exact (ofRealCLM.contDiff.comp contDiff_fst).neg
  · exact (ofRealCLM.contDiff.comp (contDiff_const.sub ((contDiff_const.sub contDiff_fst).mul
      hβ₀))).neg.mul (Complex.contDiff_exp.comp ((ofRealCLM.contDiff.comp
        (contDiff_const.mul hβ₀)).mul contDiff_const))

end TauCeti.ThricePuncturedSphere
