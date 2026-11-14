/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic
public import TauCeti.KnotTheory.Hecke.Homfly
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Hyperbolic specialization of the Hecke Markov braid invariant

Over `ℂ`, `TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic` sets the Hecke parameter to
`q = exp (-θ)` (`hyperbolicHeckeParam θ`) and rescales the Hecke generators to
`γ i = I * exp (-α) • T i` (`InfiniteTypeAHeckeAlgebra.hyperbolicGen α θ i`), which satisfy the
operator skein identity

`exp α • γ i + exp (-α) • (γ i)⁻¹ + 2 * I * sinh θ = 0`.

For a Markov trace `τ` with projection parameter `η` (so `z = exp (-θ) * η - exp θ * (1 - η)`),
passing from `γ i` to the standard Hecke braid representation `σ i ↦ T i` absorbs the rescaling
into the writhe unit `l = I * exp (-α)` (`hyperbolicWritheUnit α`). When
`cosh α ≠ 0`, `cosh θ ≠ 0`, `sinh θ ≠ 0`, and `η = (1 - tanh α * tanh θ) / 2`, the positive and
negative stabilization constants agree, and setting `C = I * cosh α / sinh θ` solves both Markov
normalization equations for `MarkovBraid.heckeTrace`.

Consequently:
* `MarkovBraid.heckeTrace` satisfies the three-parameter skein relation with parameters
  `(exp α, exp (-α), 2 * I * sinh θ)` (with a **plus** sign on `exp (-α)`),
* it agrees with the specialization of `MarkovBraid.reducedHomfly` at outer variable
  `l⁻¹ = -I * exp α` and inner variable `q - q⁻¹ = -2 * sinh θ`, and
* on the two-strand unlink `⟨1, 1⟩`, its value is
  `I * cosh α / sinh θ = -(exp α + exp (-α)) / (2 * I * sinh θ)`, which is strictly unequal to the
  minus-sign expression `-(exp α - exp (-α)) / (2 * I * sinh θ)` whenever `sinh θ ≠ 0`.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388, Section 6.
* V. F. R. Jones, *Subfactors and Knots*, CBMS Regional Conference Series in Mathematics 80, AMS
  (1991), p. 88. In that source's hyperbolic specialization formula, the second skein argument is
  printed with a minus sign (`-exp (-α)`) and the parameter constraint with `tan θ`; under the
  two-eigenvalue operator convention `exp α • γ + exp (-α) • γ⁻¹ + 2 * I * sinh θ = 0` and
  stabilization equations proved in `TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic`, the compatible
  parameters are `+exp (-α)` and `η = (1 - tanh α * tanh θ) / 2`, whereas `-exp (-α)` gives a
  different two-strand unlink value (`heckeTrace_hyperbolic_two_strand_unlink_ne_neg_param`).
-/

public noncomputable section

open Complex

namespace TauCeti

open InfiniteTypeAHeckeAlgebra (IsMarkovTrace)
open LaurentPolynomial (eval₂)

/-- The writhe unit `l = I * exp (-α)` translating between the rescaled hyperbolic generators
`γ i = I * exp (-α) • T i` and the standard Hecke braid representation `σ i ↦ T i`. -/
def hyperbolicWritheUnit (α : ℂ) : ℂˣ :=
  Units.mk0 (I * exp (-α)) (mul_ne_zero I_ne_zero (exp_ne_zero _))

/-- Coercing `hyperbolicWritheUnit α` gives `I * exp (-α)`. -/
@[simp]
theorem val_hyperbolicWritheUnit (α : ℂ) :
    (hyperbolicWritheUnit α : ℂ) = I * exp (-α) :=
  (rfl)

/-- The inverse of `hyperbolicWritheUnit α` is `-I * exp α`. -/
theorem val_inv_hyperbolicWritheUnit (α : ℂ) :
    (↑(hyperbolicWritheUnit α)⁻¹ : ℂ) = -I * exp α := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [val_hyperbolicWritheUnit, mul_mul_mul_comm, ← exp_add, neg_add_cancel, exp_zero, mul_one,
    mul_neg, I_mul_I, neg_neg]

/-- Multiplying the Markov parameter `z = exp (-θ) * η - exp θ * (1 - η)` by
`hyperbolicWritheUnit α` gives `hyperbolicStabilization α θ η`. -/
theorem hyperbolicWritheUnit_mul_eq_hyperbolicStabilization {α θ z η : ℂ}
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) :
    (hyperbolicWritheUnit α : ℂ) * z = hyperbolicStabilization α θ η := by
  rw [val_hyperbolicWritheUnit, hz, hyperbolicStabilization_def, exp_sub, exp_add, exp_neg, exp_neg]
  ring

/-- Multiplying the negative Hecke stabilization factor `z - (q - q⁻¹)` at
`q = hyperbolicHeckeParam θ` by `(hyperbolicWritheUnit α)⁻¹` gives
`hyperbolicStabilizationInv α θ η`. -/
theorem inv_hyperbolicWritheUnit_mul_sub_eq_hyperbolicStabilizationInv {α θ z η : ℂ}
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) :
    (↑(hyperbolicWritheUnit α)⁻¹ : ℂ) *
        (z - ((hyperbolicHeckeParam θ : ℂ) - ↑(hyperbolicHeckeParam θ)⁻¹)) =
      hyperbolicStabilizationInv α θ η := by
  rw [val_inv_hyperbolicWritheUnit, val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, hz,
    hyperbolicStabilizationInv_def, exp_sub, exp_add, exp_neg]
  ring

/-- **Hyperbolic Markov normalization equations for `MarkovBraid.heckeTrace`.** At projection
parameter `η = (1 - tanh α * tanh θ) / 2` (with `cosh α ≠ 0`, `cosh θ ≠ 0`, and `sinh θ ≠ 0`),
`C = I * cosh α / sinh θ` and `l = hyperbolicWritheUnit α` solve both positive and negative Markov
normalization equations for `z = exp (-θ) * η - exp θ * (1 - η)`. -/
theorem hyperbolicHeckeNormalization {α θ z η : ℂ}
    (hz : z = exp (-θ) * η - exp θ * (1 - η))
    (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0) (hθ' : sinh θ ≠ 0)
    (hη : η = (1 - tanh α * tanh θ) / 2) :
    (I * cosh α / sinh θ) * (hyperbolicWritheUnit α : ℂ) * z = 1 ∧
      (I * cosh α / sinh θ) * (↑(hyperbolicWritheUnit α)⁻¹ : ℂ) *
        (z - ((hyperbolicHeckeParam θ : ℂ) - ↑(hyperbolicHeckeParam θ)⁻¹)) = 1 := by
  rw [mul_assoc, hyperbolicWritheUnit_mul_eq_hyperbolicStabilization hz,
    mul_assoc, inv_hyperbolicWritheUnit_mul_sub_eq_hyperbolicStabilizationInv hz]
  exact hyperbolicStabilization_normalization hα hθ hθ' hη

namespace MarkovBraid

/-- **Three-parameter hyperbolic skein relation for `MarkovBraid.heckeTrace`.** At Hecke parameter
`q = exp (-θ)` and writhe unit `l = I * exp (-α)`, the normalized Hecke trace satisfies
`exp α * F(L₊) + exp (-α) * F(L₋) + (2 * I * sinh θ) * F(L₀) = 0`, with a plus sign on
`exp (-α)`. -/
theorem heckeTrace_hyperbolic_skein {α θ C : ℂ}
    (τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ)
    {n : ℕ} (b c : BraidGroup (n + 1)) (i : Fin n) :
    exp α * heckeTrace ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩
          τ C (hyperbolicWritheUnit α) +
        exp (-α) * heckeTrace ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩
          τ C (hyperbolicWritheUnit α) +
        (2 * I * sinh θ) * heckeTrace ⟨n, b * c⟩ τ C (hyperbolicWritheUnit α) = 0 := by
  have hs := heckeTrace_skein (τ := τ) C (hyperbolicWritheUnit α) b c i
  have hsinh : exp (-θ) - exp θ = -2 * sinh θ := by
    rw [Complex.sinh]
    ring
  rw [val_inv_hyperbolicWritheUnit, val_hyperbolicWritheUnit, val_hyperbolicHeckeParam,
    val_inv_hyperbolicHeckeParam, hsinh] at hs
  have hI : I * I = -1 := I_mul_I
  linear_combination I * hs +
    (exp α * heckeTrace ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩
        τ C (hyperbolicWritheUnit α) +
      exp (-α) * heckeTrace ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩
        τ C (hyperbolicWritheUnit α)) * hI

/-- **Comparison between the hyperbolic Hecke braid invariant and `reducedHomfly`.** Under the
compatibility relation `η = (1 - tanh α * tanh θ) / 2` with `cosh α ≠ 0`, `cosh θ ≠ 0`, and
`sinh θ ≠ 0`, the normalized Hecke trace equals the specialization of `β.reducedHomfly K` at outer
variable `(hyperbolicWritheUnit α)⁻¹ = -I * exp α` and inner variable `-2 * sinh θ`. -/
theorem heckeTrace_hyperbolic_eq_eval₂_reducedHomfly {K : Type*} [Field K] (φ : K →+* ℂ)
    {α θ z η : ℂ} {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ}
    (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * η - exp θ * (1 - η))
    (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0) (hθ' : sinh θ ≠ 0)
    (hη : η = (1 - tanh α * tanh θ) / 2) (β : MarkovBraid) :
    β.heckeTrace τ (I * cosh α / sinh θ) (hyperbolicWritheUnit α) =
      eval₂
        (eval₂ φ (Units.mk0 (-2 * sinh θ) (mul_ne_zero (by norm_num) hθ')))
        (hyperbolicWritheUnit α)⁻¹ (β.reducedHomfly K) := by
  obtain ⟨hpos, hneg⟩ := hyperbolicHeckeNormalization hz hα hθ hθ' hη
  have hu : ((Units.mk0 (-2 * sinh θ) (mul_ne_zero (by norm_num) hθ') : ℂˣ) : ℂ) =
      (hyperbolicHeckeParam θ : ℂ) - ↑(hyperbolicHeckeParam θ)⁻¹ := by
    rw [Units.val_mk0, val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, Complex.sinh]
    ring
  exact (β.eval₂_reducedHomfly_eq_heckeTrace φ hτ hu hpos hneg).symm

/-- On the two-strand unlink `⟨1, 1⟩`, the hyperbolic normalized Hecke trace equals
`-(exp α + exp (-α)) / (2 * I * sinh θ) = I * cosh α / sinh θ`, matching the plus-sign skein
parameters `(exp α, exp (-α), 2 * I * sinh θ)`. -/
theorem heckeTrace_hyperbolic_two_strand_unlink {α θ : ℂ}
    {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ}
    (h₁ : τ 1 = 1) (hθ' : sinh θ ≠ 0) :
    heckeTrace ⟨1, 1⟩ τ (I * cosh α / sinh θ) (hyperbolicWritheUnit α) =
      -(exp α + exp (-α)) / (2 * I * sinh θ) := by
  rw [heckeTrace_one h₁, pow_one, Complex.cosh]
  have hI : I ≠ 0 := I_ne_zero
  field_simp
  linear_combination (exp α + exp (-α)) * I_mul_I

/-- **Disproof of the minus-sign second skein parameter on the two-strand unlink.** Whenever
`sinh θ ≠ 0` and `τ 1 = 1`, the hyperbolic normalized Hecke trace of the two-strand unlink is
strictly unequal to the value `-(exp α - exp (-α)) / (2 * I * sinh θ)` predicted by the minus-sign
triple `(exp α, -exp (-α), 2 * I * sinh θ)`. -/
theorem heckeTrace_hyperbolic_two_strand_unlink_ne_neg_param {α θ : ℂ}
    {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ}
    (h₁ : τ 1 = 1) (hθ' : sinh θ ≠ 0) :
    heckeTrace ⟨1, 1⟩ τ (I * cosh α / sinh θ) (hyperbolicWritheUnit α) ≠
      -(exp α - exp (-α)) / (2 * I * sinh θ) := by
  rw [heckeTrace_hyperbolic_two_strand_unlink h₁ hθ']
  intro h
  have hden : (2 * I * sinh θ : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hθ'
  have hnum : -(exp α + exp (-α)) = -(exp α - exp (-α)) :=
    (div_left_inj₀ hden).mp h
  have hexp : (2 : ℂ) * exp (-α) = 0 := by
    linear_combination -hnum
  exact mul_ne_zero two_ne_zero (exp_ne_zero (-α)) hexp

end MarkovBraid

end TauCeti
