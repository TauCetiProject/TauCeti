/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.LowerParameterPole
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Parameters

/-!
# Tricomi's bracket

Tricomi's confluent hypergeometric function `U(a, b, z)` is the solution of Kummer's equation
`z w'' + (b - z) w' - a w = 0` that is recessive as `z → +∞`. In terms of the two Frobenius
solutions `𝐌(a, b, z)` and `z^{1 - b} 𝐌(a - b + 1, 2 - b, z)` at the regular singular point
`z = 0`, with exponents `0` and `1 - b`, where
`𝐌(a, b, z) = Complex.regularizedHGFun {a} {b} z` is Olver's regularized Kummer function, it is
`U(a, b, z) = (π / sin πb) F(a, b, log z)` for `b ∉ ℤ` (DLMF 13.2.42), with the bracket

`F(a, b, w) = 𝐌(a, b, e^w) / Γ(a - b + 1) - e^{(1 - b) w} 𝐌(a - b + 1, 2 - b, e^w) / Γ(a)`.

This file defines the bracket as `Complex.kummerUBracket a b w`, in the logarithmic coordinate
`w`, where `z^{1 - b}` becomes the entire function `e^{(1 - b) w}`. With Mathlib's convention
`(Γ(-n))⁻¹ = 0`, the bracket is defined and jointly holomorphic in `(a, b, w)` on all of `ℂ³`.

At an integer `b = n` the factor `π / sin πb` has a pole, and the bracket vanishes for all `a` and
`w`: for `n ≤ 0` by DLMF 13.2.5 applied to `𝐌(a, n, ·)`, for `n ≥ 2` by DLMF 13.2.5 applied to
`𝐌(a - n + 1, 2 - n, ·)`, and at `n = 1` because its two terms coincide. This is what makes the
singularity of `U` in `b` at the integers removable, so that `U(a, n, z)` is the derivative
`(-1)ⁿ ∂_b F(a, b, log z)` at `b = n`. The case `n ≥ 2` follows from the case `n ≤ 0` through the
symmetry `F(a - b + 1, 2 - b, w) = -e^{(b - 1) w} F(a, b, w)`, which is the bracket form of Kummer's
second transformation `U(a, b, z) = z^{1 - b} U(a - b + 1, 2 - b, z)` (DLMF 13.2.40).

## Main definitions

* `Complex.kummerUBracket a b w` — the bracket `F(a, b, w)`.

## Main results

* `Complex.kummerUBracket_intCast` — `F(a, n, w) = 0` for every integer `n`.
* `Complex.differentiable_kummerUBracket` — `F` is holomorphic in `(a, b, w)` on `ℂ³`.
* `Differentiable.kummerUBracket` and its `At`, `On` and `WithinAt` variants — `fun_prop`
  composition lemmas for `F`.
* `Complex.kummerUBracket_sub_add_one_two_sub` —
  `F(a - b + 1, 2 - b, w) = -e^{(b - 1) w} F(a, b, w)`.
* `Complex.kummerUBracket_zero_left` — `F(0, b, w) = sin(πb) / π`, so that
  `(π / sin πb) F(0, b, w) = 1` for `b ∉ ℤ` (DLMF 13.6.3, `U(0, b, z) = 1`).

## References

* NIST Digital Library of Mathematical Functions, 13.2.5, 13.2.40 and 13.2.42,
  <https://dlmf.nist.gov/13.2>.
* R. Beals and R. Wong, *Special Functions: A Graduate Text*, Cambridge University Press, 2010,
  (6.3.1)–(6.3.2).
* N. N. Lebedev, *Special Functions and Their Applications*, Prentice-Hall, 1965, (9.10.3)–(9.10.5).
-/

public section

noncomputable section

open scoped Real

namespace Complex

/-- **Tricomi's bracket**
`F(a, b, w) = 𝐌(a, b, e^w) / Γ(a - b + 1) - e^{(1 - b) w} 𝐌(a - b + 1, 2 - b, e^w) / Γ(a)`, with
`𝐌` Olver's regularized Kummer function. For `b ∉ ℤ`, Tricomi's function is
`U(a, b, e^w) = (π / sin πb) F(a, b, w)` (DLMF 13.2.42). Division by `Γ` at its poles gives `0`,
which is the value of the entire function `1 / Γ` there. -/
def kummerUBracket (a b w : ℂ) : ℂ :=
  regularizedHGFun {a} {b} (exp w) / Gamma (a - b + 1) -
    exp ((1 - b) * w) * regularizedHGFun {a - b + 1} {2 - b} (exp w) / Gamma a

/-- The defining formula of `kummerUBracket`. -/
theorem kummerUBracket_def (a b w : ℂ) :
    kummerUBracket a b w =
      regularizedHGFun {a} {b} (exp w) / Gamma (a - b + 1) -
        exp ((1 - b) * w) * regularizedHGFun {a - b + 1} {2 - b} (exp w) / Gamma a := (rfl)

/-- Tricomi's bracket is holomorphic in `(a, b, w)` on all of `ℂ³`. -/
theorem differentiable_kummerUBracket :
    Differentiable ℂ fun p : ℂ × ℂ × ℂ => kummerUBracket p.1 p.2.1 p.2.2 := by
  have hG : ∀ {f : ℂ × ℂ × ℂ → ℂ}, Differentiable ℂ f →
      Differentiable ℂ fun p => (Gamma (f p))⁻¹ :=
    fun hf => differentiable_one_div_Gamma.comp hf
  simp only [kummerUBracket_def, div_eq_mul_inv]
  refine Differentiable.sub (Differentiable.mul ?_ (hG (by fun_prop)))
    (Differentiable.mul (Differentiable.mul (by fun_prop) ?_) (hG (by fun_prop))) <;>
    exact Differentiable.regularizedHGFun_singleton (by fun_prop) (by fun_prop) (by fun_prop)

section Comp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g h : E → ℂ} {s : Set E}
  {x : E}

/-- For `f`, `g` and `h` differentiable at `x` within `s`, so is `y ↦ F(f y, g y, h y)`. -/
@[fun_prop]
theorem _root_.DifferentiableWithinAt.kummerUBracket
    (hf : DifferentiableWithinAt ℂ f s x) (hg : DifferentiableWithinAt ℂ g s x)
    (hh : DifferentiableWithinAt ℂ h s x) :
    DifferentiableWithinAt ℂ (fun y => kummerUBracket (f y) (g y) (h y)) s x := by
  have H := (differentiable_kummerUBracket (f x, g x, h x)).comp_differentiableWithinAt x
    (hf.prodMk (hg.prodMk hh))
  exact H

/-- For `f`, `g` and `h` differentiable at `x`, so is `y ↦ F(f y, g y, h y)`. -/
@[fun_prop]
theorem _root_.DifferentiableAt.kummerUBracket (hf : DifferentiableAt ℂ f x)
    (hg : DifferentiableAt ℂ g x) (hh : DifferentiableAt ℂ h x) :
    DifferentiableAt ℂ (fun y => kummerUBracket (f y) (g y) (h y)) x := by
  have H := (differentiable_kummerUBracket (f x, g x, h x)).comp x (hf.prodMk (hg.prodMk hh))
  exact H

/-- For `f`, `g` and `h` differentiable on `s`, so is `y ↦ F(f y, g y, h y)`. -/
@[fun_prop]
theorem _root_.DifferentiableOn.kummerUBracket (hf : DifferentiableOn ℂ f s)
    (hg : DifferentiableOn ℂ g s) (hh : DifferentiableOn ℂ h s) :
    DifferentiableOn ℂ (fun y => kummerUBracket (f y) (g y) (h y)) s := fun x hx =>
  (hf x hx).kummerUBracket (hg x hx) (hh x hx)

/-- For differentiable `f`, `g` and `h`, the function `y ↦ F(f y, g y, h y)` is differentiable. -/
@[fun_prop]
theorem _root_.Differentiable.kummerUBracket (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hh : Differentiable ℂ h) :
    Differentiable ℂ fun y => kummerUBracket (f y) (g y) (h y) := fun x =>
  (hf x).kummerUBracket (hg x) (hh x)

end Comp

/-- The bracket form of Kummer's second transformation (DLMF 13.2.40):
`F(a - b + 1, 2 - b, w) = -e^{(b - 1) w} F(a, b, w)`. The parameter map
`(a, b) ↦ (a - b + 1, 2 - b)` is an involution that exchanges the two terms of the bracket. -/
theorem kummerUBracket_sub_add_one_two_sub (a b w : ℂ) :
    kummerUBracket (a - b + 1) (2 - b) w = -(exp ((b - 1) * w) * kummerUBracket a b w) := by
  have h₁ : a - b + 1 - (2 - b) + 1 = a := by ring
  have h₂ : (2 : ℂ) - (2 - b) = b := by ring
  have h₃ : (1 : ℂ) - (2 - b) = b - 1 := by ring
  have he : exp ((b - 1) * w) * exp ((1 - b) * w) = 1 := by
    rw [← exp_add, ← exp_zero]
    congr 1
    ring
  rw [kummerUBracket_def, kummerUBracket_def, h₁, h₂, h₃]
  linear_combination -(regularizedHGFun {a - b + 1} {2 - b} (exp w) / Gamma a) * he

/-- Tricomi's bracket vanishes at every nonpositive integer `b = -n`: `F(a, -n, w) = 0`. -/
@[simp]
theorem kummerUBracket_neg_natCast (a w : ℂ) (n : ℕ) : kummerUBracket a (-n) w = 0 := by
  have h₁ : a - -(n : ℂ) + 1 = a + n + 1 := by ring
  have h₂ : (2 : ℂ) - -(n : ℂ) = n + 2 := by ring
  have h₃ : exp ((1 - -(n : ℂ)) * w) = exp w ^ (n + 1) := by
    rw [← exp_natCast_mul]
    push_cast
    ring_nf
  have hΓ := inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add a (n + 1)
  rw [Nat.cast_succ, ← add_assoc] at hΓ
  rw [kummerUBracket_def, h₁, h₂, h₃, regularizedHGFun_singleton_neg_natCast_right, div_eq_mul_inv,
    div_eq_mul_inv, hΓ]
  ring

/-- Tricomi's bracket vanishes at every natural number `b = n`. -/
@[simp]
theorem kummerUBracket_natCast (a w : ℂ) (n : ℕ) : kummerUBracket a n w = 0 := by
  match n with
  | 0 => simpa using kummerUBracket_neg_natCast a w 0
  | 1 =>
    rw [kummerUBracket_def]
    norm_num
  | n + 2 =>
    -- `(a, n + 2)` is the image of `(a - n - 1, -n)` under `(a, b) ↦ (a - b + 1, 2 - b)`.
    have h := kummerUBracket_sub_add_one_two_sub (a - n - 1) (-n) w
    rw [kummerUBracket_neg_natCast, mul_zero, neg_zero,
      show a - n - 1 - -(n : ℂ) + 1 = a by ring] at h
    rwa [show (2 : ℂ) - -(n : ℂ) = ((n + 2 : ℕ) : ℂ) by push_cast; ring] at h

/-- Tricomi's bracket vanishes at every numeral `b ≥ 2`. -/
@[simp]
theorem kummerUBracket_ofNat (a w : ℂ) (n : ℕ) [n.AtLeastTwo] :
    kummerUBracket a ofNat(n) w = 0 :=
  kummerUBracket_natCast a w n

/-- Tricomi's bracket vanishes at `b = 0`. -/
@[simp]
theorem kummerUBracket_zero_middle (a w : ℂ) : kummerUBracket a 0 w = 0 := by
  simpa using kummerUBracket_natCast a w 0

/-- Tricomi's bracket vanishes at `b = 1`. -/
@[simp]
theorem kummerUBracket_one_middle (a w : ℂ) : kummerUBracket a 1 w = 0 := by
  simpa using kummerUBracket_natCast a w 1

/-- Tricomi's bracket vanishes at `b = -1`. -/
@[simp]
theorem kummerUBracket_neg_one (a w : ℂ) : kummerUBracket a (-1) w = 0 := by
  simpa using kummerUBracket_neg_natCast a w 1

/-- Tricomi's bracket vanishes at every negative numeral `b ≤ -2`. -/
@[simp]
theorem kummerUBracket_neg_ofNat (a w : ℂ) (n : ℕ) [n.AtLeastTwo] :
    kummerUBracket a (-ofNat(n)) w = 0 :=
  kummerUBracket_neg_natCast a w n

/-- **Tricomi's bracket vanishes at the integers**: `F(a, n, w) = 0` for every integer `n` and all
complex `a` and `w`. This is the removable singularity of `U(a, b, z) = (π / sin πb) F(a, b, log z)`
at integer `b`. -/
@[simp]
theorem kummerUBracket_intCast (a w : ℂ) (n : ℤ) : kummerUBracket a n w = 0 := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp

/-- At `a = 0`, Tricomi's bracket is `F(0, b, w) = sin(πb) / π` for all complex `b` and `w`, so
that `(π / sin πb) F(0, b, w) = 1` for `b ∉ ℤ`; this is `U(0, b, z) = 1` (DLMF 13.6.3). -/
theorem kummerUBracket_zero_left (b w : ℂ) : kummerUBracket 0 b w = sin (π * b) / π := by
  have hM : regularizedHGFun {0} {b} (exp w) = (Gamma b)⁻¹ := by
    simp [regularizedHGFun_of_zero_mem]
  simp [kummerUBracket_def, hM, neg_add_eq_sub, div_eq_mul_inv, ← mul_inv,
    Gamma_mul_Gamma_one_sub]

end Complex
