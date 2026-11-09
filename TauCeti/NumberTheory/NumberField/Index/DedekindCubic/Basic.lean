/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# The extra integer in Dedekind's cubic field

For an algebraic integer `θ` satisfying `θ³ - θ² - 2θ - 8 = 0`, the element
`β = (θ² - θ)/2` is integral. Its monic equation and the multiplication relations among
`1`, `θ`, and `β` are the first ingredients in the integral order with basis `(1, θ, β)`.
The factor of `2` in its denominator is why reduction of the polynomial modulo `2` does not
describe the splitting of `2` in this field.

The calculation follows the standard Dedekind cubic example in Neukirch, *Algebraic Number
Theory*, III §2, Exercise 1.
-/

public section
noncomputable section

open Polynomial NumberField
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K]
variable {θ : 𝓞 K}

/-- The defining cubic relation, expressed inside the ring of integers. -/
theorem dedekindCubic_relation
    (hθ : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8) :
    θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0 := by
  simpa only [hθ, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_ofNat] using
    minpoly.aeval ℤ θ

private theorem dedekindCubic_relation_in_field
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    (θ : K) ^ 3 - (θ : K) ^ 2 - 2 * (θ : K) - 8 = 0 := by
  simpa only [map_sub, map_mul, map_pow, map_ofNat, map_zero] using
    congrArg (algebraMap (𝓞 K) K) hθ

variable [CharZero K]

/-- A field generated over `ℚ` by a root of Dedekind's cubic has degree three. -/
theorem dedekindCubic_finrank_eq_three
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Module.finrank ℚ K = 3 := by
  rw [(PowerBasis.ofAdjoinEqTop' (θ.isIntegral_coe.tower_top (A := ℚ)) hgen).finrank,
    PowerBasis.ofAdjoinEqTop'_dim,
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ θ.isIntegral_coe,
    _root_.NumberField.RingOfIntegers.minpoly_coe,
    (minpoly.monic θ.isIntegral).natDegree_map, hmin]
  compute_degree <;> norm_num

private theorem beta_relation_in_field
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    (((θ : K) ^ 2 - θ) / 2) ^ 3 - 2 * (((θ : K) ^ 2 - θ) / 2) ^ 2 +
      3 * (((θ : K) ^ 2 - θ) / 2) - 10 = 0 := by
  linear_combination (((θ : K) ^ 3 - 2 * (θ : K) ^ 2 - θ + 10) / 8) *
    dedekindCubic_relation_in_field hθ

/-- The half-integral element used in the integral basis of Dedekind's cubic field. Its
equation is `β³ - 2β² + 3β - 10 = 0`. -/
def dedekindBeta (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) : 𝓞 K :=
  ⟨((θ : K) ^ 2 - θ) / 2, X ^ 3 - C 2 * X ^ 2 + C 3 * X - C 10, by monicity!,
    by simpa using beta_relation_in_field hθ⟩

/-- The extra algebraic integer is `(θ² - θ)/2` in the ambient field. -/
@[simp] theorem coe_dedekindBeta
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    (dedekindBeta hθ : K) = ((θ : K) ^ 2 - θ) / 2 :=
  (rfl)

/-- The defining monic equation of the extra integer. -/
theorem dedekindBeta_relation
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    (dedekindBeta hθ) ^ 3 - 2 * (dedekindBeta hθ) ^ 2 +
      3 * dedekindBeta hθ - 10 = 0 :=
  RingOfIntegers.ext <| by
    simpa only [map_sub, map_add, map_pow, map_mul, map_ofNat, map_zero, coe_dedekindBeta] using
      beta_relation_in_field hθ

/-- The relation `θ² = θ + 2β` in the integral order. It is not a `simp` lemma, because its
left-hand side does not determine the hypothesis `hθ`. -/
theorem dedekindCubic_theta_sq
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    θ ^ 2 = θ + 2 * dedekindBeta hθ :=
  RingOfIntegers.ext <| by
    simp only [map_pow, map_add, map_mul, map_ofNat, coe_dedekindBeta]
    ring

/-- The product `θβ` in the integral order. -/
@[simp] theorem dedekindCubic_theta_mul_beta
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    θ * dedekindBeta hθ = θ + 4 :=
  RingOfIntegers.ext <| by
    simp only [map_mul, map_add, map_ofNat, coe_dedekindBeta]
    linear_combination (1 / 2 : K) * dedekindCubic_relation_in_field hθ

/-- The square `β²` in the integral order. -/
@[simp] theorem dedekindCubic_beta_sq
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    dedekindBeta hθ ^ 2 = dedekindBeta hθ + 2 * θ - 2 :=
  RingOfIntegers.ext <| by
    simp only [map_pow, map_sub, map_add, map_mul, map_ofNat, coe_dedekindBeta]
    linear_combination (((θ : K) - 1) / 4) * dedekindCubic_relation_in_field hθ

end TauCeti.NumberField

end
end
