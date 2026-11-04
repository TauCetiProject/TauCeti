/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection
public import TauCeti.Algebra.TypeAHeckeAlgebra.Complement
public import Mathlib.Analysis.Complex.Trigonometric
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Hyperbolic parameters and the stabilization constants of the Ocneanu trace

Let `s = q + q⁻¹` be a unit. The generator `T i` of the infinite type-A Hecke algebra has the
two eigenvalues `q` and `-q⁻¹`, and
`P i = s⁻¹ • (T i + q⁻¹)` is the idempotent eigenprojection for `q`, so that
`T i = q • P i - q⁻¹ • (1 - P i)` and `T i⁻¹ = q⁻¹ • P i - q • (1 - P i)`. A Markov trace with
parameter `z` multiplies by the projection parameter `η` when the last projection is appended,
where `z = q * η - q⁻¹ * (1 - η)`, that is `η = (z + q⁻¹) / (q + q⁻¹)`. These general facts are in
`TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection`.

Over `ℂ`, put `q = exp (-θ)` (`TauCeti.hyperbolicHeckeParam`) and rescale the braid generators to
`γ i = I * exp (-α) • T i` (`TauCeti.InfiniteTypeAHeckeAlgebra.hyperbolicGen`). In terms of the
eigenprojection,

`γ i = I • (exp (-α - θ) • P i - exp (-α + θ) • (1 - P i))`,

and `γ i` satisfies the skein identity `exp α • γ + exp (-α) • γ⁻¹ + 2 I sinh θ = 0`. The positive
and negative stabilization constants of a Markov trace, `a = τ (γ n)` and `b = τ (γ n⁻¹)`, are

`a = I * (exp (-α - θ) * η - exp (-α + θ) * (1 - η))` and
`b = -I * (exp (α + θ) * η - exp (α - θ) * (1 - η))`,

and they also govern the stabilization `x ↦ x * γ n` of every `x` in the stage of the first
`n + 1` strands. When `cosh α * cosh θ ≠ 0`, the two constants are equal exactly when

`η = cosh (α - θ) / (2 * cosh α * cosh θ) = (1 - tanh α * tanh θ) / 2`,

and their common value is then `-I * sinh θ / cosh α`. If moreover `sinh θ ≠ 0`, the
normalization `C * λ * a = 1 = C * λ⁻¹ * b` of the braid-closure invariant is solved by `λ = 1`
and `C = I * cosh α / sinh θ`. Precomposing the trace with the complement automorphism, which
exchanges the two eigenprojections, replaces `η` by `1 - η`, and the condition becomes
`η = (1 + tanh α * tanh θ) / 2`.

The parameter `η` is free here: the statements identify which Markov traces have equal
stabilization constants, and assert nothing about positivity.

## Main definitions

* `TauCeti.hyperbolicHeckeParam`: the Hecke parameter `q = exp (-θ)` as a unit.
* `TauCeti.InfiniteTypeAHeckeAlgebra.hyperbolicGen`: the rescaled generator `I * exp (-α) • T i`,
  as a unit.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.val_hyperbolicGen_eq_eigenprojection` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.hyperbolicGen_skein`: the two-eigenvalue form of `γ i` and its
  skein identity.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_hyperbolicGen` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_val_inv_hyperbolicGen`: the two
  stabilization constants.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_eq_map_inv_iff`: **the two
  stabilization constants agree exactly when `η = (1 - tanh α * tanh θ) / 2`.**
* `TauCeti.hyperbolicStabilization_eq_neg_I_mul_sinh_div_cosh` and
  `TauCeti.hyperbolicStabilization_normalization`:
  the common value and the normalization constants.
* The same condition for the complementary eigenprojection:
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_complementEquiv_hyperbolicGen_eq_map_inv_iff`

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 6, for the normalization of the Ocneanu trace by
  the two stabilization constants.
* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett and A. Ocneanu, *A new
  polynomial invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246, for the
  skein convention.
-/

public section

open Complex

namespace TauCeti

/-! ### Hyperbolic parameters -/

/-- The Hecke parameter `q = exp (-θ)`, as a unit of `ℂ`. -/
noncomputable def hyperbolicHeckeParam (θ : ℂ) : ℂˣ :=
  Units.mk0 (exp (-θ)) (exp_ne_zero _)

/-- The value of the hyperbolic Hecke parameter is `exp (-θ)`. -/
@[simp]
theorem val_hyperbolicHeckeParam (θ : ℂ) : (hyperbolicHeckeParam θ : ℂ) = exp (-θ) := (rfl)

/-- The inverse of the hyperbolic Hecke parameter is `exp θ`. -/
theorem val_inv_hyperbolicHeckeParam (θ : ℂ) : (↑(hyperbolicHeckeParam θ)⁻¹ : ℂ) = exp θ := by
  simp [hyperbolicHeckeParam, ← exp_neg]

/-- The hyperbolic Hecke parameter satisfies `q + q⁻¹ = 2 * cosh θ`. -/
theorem two_mul_cosh_eq_hyperbolicHeckeParam_add_inv (θ : ℂ) :
    2 * cosh θ = (hyperbolicHeckeParam θ : ℂ) + ↑(hyperbolicHeckeParam θ)⁻¹ := by
  rw [val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, two_cosh, add_comm]

/-- The positive stabilization constant `I * (exp (-α - θ) * η - exp (-α + θ) * (1 - η))` of a
Markov trace with projection parameter `η`, for the generators `γ = I * exp (-α) • T`. -/
noncomputable def hyperbolicStabilization (α θ η : ℂ) : ℂ :=
  I * (exp (-α - θ) * η - exp (-α + θ) * (1 - η))

/-- The negative stabilization constant `-I * (exp (α + θ) * η - exp (α - θ) * (1 - η))` of a
Markov trace with projection parameter `η`, for the inverse generators `γ⁻¹`. -/
noncomputable def hyperbolicStabilizationInv (α θ η : ℂ) : ℂ :=
  -I * (exp (α + θ) * η - exp (α - θ) * (1 - η))

/-- The defining formula of the positive stabilization constant. -/
theorem hyperbolicStabilization_def (α θ η : ℂ) :
    hyperbolicStabilization α θ η = I * (exp (-α - θ) * η - exp (-α + θ) * (1 - η)) := (rfl)

/-- The defining formula of the negative stabilization constant. -/
theorem hyperbolicStabilizationInv_def (α θ η : ℂ) :
    hyperbolicStabilizationInv α θ η = -I * (exp (α + θ) * η - exp (α - θ) * (1 - η)) := (rfl)

/-- The difference of the two stabilization constants is
`2 * I * (2 * cosh α * cosh θ * η - cosh (α - θ))`. -/
theorem hyperbolicStabilization_sub_hyperbolicStabilizationInv (α θ η : ℂ) :
    hyperbolicStabilization α θ η - hyperbolicStabilizationInv α θ η =
      2 * I * (2 * cosh α * cosh θ * η - cosh (α - θ)) := by
  simp only [hyperbolicStabilization, hyperbolicStabilizationInv, cosh, exp_add, exp_sub, exp_neg]
  have ha := exp_ne_zero α
  have hb := exp_ne_zero θ
  field_simp
  ring

/-- **Equality of the stabilization constants.** For `cosh α * cosh θ ≠ 0`, the positive and
negative stabilization constants agree exactly when
`η = cosh (α - θ) / (2 * cosh α * cosh θ)`. -/
theorem hyperbolicStabilization_eq_hyperbolicStabilizationInv_iff {α θ η : ℂ} (hα : cosh α ≠ 0)
    (hθ : cosh θ ≠ 0) :
    hyperbolicStabilization α θ η = hyperbolicStabilizationInv α θ η ↔
      η = cosh (α - θ) / (2 * cosh α * cosh θ) := by
  rw [← sub_eq_zero, hyperbolicStabilization_sub_hyperbolicStabilizationInv,
    eq_div_iff (by simp [hα, hθ])]
  simp [I_ne_zero, sub_eq_zero, mul_comm]

/-- **Equality of the stabilization constants, in hyperbolic tangents.** For
`cosh α * cosh θ ≠ 0`, the positive and negative stabilization constants agree exactly when
`η = (1 - tanh α * tanh θ) / 2`. -/
theorem hyperbolicStabilization_eq_hyperbolicStabilizationInv_iff_tanh {α θ η : ℂ} (hα : cosh α ≠ 0)
    (hθ : cosh θ ≠ 0) :
    hyperbolicStabilization α θ η = hyperbolicStabilizationInv α θ η ↔
      η = (1 - tanh α * tanh θ) / 2 := by
  rw [hyperbolicStabilization_eq_hyperbolicStabilizationInv_iff hα hθ,
    cosh_sub_div_eq_one_sub_tanh_mul_tanh_div_two hα hθ]

/-- **Exchanging the eigenprojections.** For `cosh α * cosh θ ≠ 0`, the stabilization constants
at the complementary projection parameter `1 - η` agree exactly when
`η = (1 + tanh α * tanh θ) / 2`. -/
theorem hyperbolicStabilization_one_sub_eq_hyperbolicStabilizationInv_one_sub_iff {α θ η : ℂ}
    (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0) :
    hyperbolicStabilization α θ (1 - η) = hyperbolicStabilizationInv α θ (1 - η) ↔
      η = (1 + tanh α * tanh θ) / 2 := by
  rw [hyperbolicStabilization_eq_hyperbolicStabilizationInv_iff_tanh hα hθ]
  constructor <;> intro h <;> linear_combination -h

/-- **The common stabilization constant.** At `η = (1 - tanh α * tanh θ) / 2`, the positive
stabilization constant is `-I * sinh θ / cosh α`. -/
theorem hyperbolicStabilization_eq_neg_I_mul_sinh_div_cosh {α θ η : ℂ} (hα : cosh α ≠ 0)
    (hθ : cosh θ ≠ 0) (hη : η = (1 - tanh α * tanh θ) / 2) :
    hyperbolicStabilization α θ η = -I * sinh θ / cosh α := by
  have h1 : exp (-α) * (cosh α + sinh α) = 1 := by
    rw [cosh_add_sinh, ← exp_add, neg_add_cancel, exp_zero]
  have key : hyperbolicStabilization α θ η = I * exp (-α) * (2 * cosh θ * η - exp θ) := by
    rw [hyperbolicStabilization, two_cosh]
    simp only [exp_sub, exp_add, exp_neg]
    ring
  rw [← cosh_sub_div_eq_one_sub_tanh_mul_tanh_div_two hα hθ] at hη
  rw [key, hη, eq_div_iff hα]
  calc I * exp (-α) * (2 * cosh θ * (cosh (α - θ) / (2 * cosh α * cosh θ)) - exp θ) * cosh α
      = I * exp (-α) * (cosh (α - θ) - exp θ * cosh α) := by field_simp
    _ = -I * sinh θ := by
      rw [cosh_sub, ← cosh_add_sinh θ]
      linear_combination (-I * sinh θ) * h1

/-- **The normalization constants.** At `η = (1 - tanh α * tanh θ) / 2`, if moreover
`sinh θ ≠ 0`, then `λ = 1` and `C = I * cosh α / sinh θ` solve the normalization
`C * λ * a = 1 = C * λ⁻¹ * b` for the positive and negative stabilization constants `a` and `b`. -/
theorem hyperbolicStabilization_normalization {α θ η : ℂ} (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0)
    (hθ' : sinh θ ≠ 0) (hη : η = (1 - tanh α * tanh θ) / 2) :
    I * cosh α / sinh θ * hyperbolicStabilization α θ η = 1 ∧
      I * cosh α / sinh θ * hyperbolicStabilizationInv α θ η = 1 := by
  have h : I * cosh α / sinh θ * hyperbolicStabilization α θ η = 1 := by
    rw [hyperbolicStabilization_eq_neg_I_mul_sinh_div_cosh hα hθ hη]
    field_simp
    simp
  exact ⟨h, ((hyperbolicStabilization_eq_hyperbolicStabilizationInv_iff_tanh hα hθ).2 hη) ▸ h⟩

namespace InfiniteTypeAHeckeAlgebra

/-- The rescaled braid generator `γ i = I * exp (-α) • T i` of the Hecke algebra with parameter
`q = exp (-θ)`, as a unit. It has the eigenvalues `I * exp (-α - θ)` and `-I * exp (-α + θ)`. -/
noncomputable def hyperbolicGen (α θ : ℂ) (i : ℕ) :
    (InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ))ˣ :=
  Units.map (algebraMap ℂ (InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ))).toMonoidHom
    (Units.mk0 (I * exp (-α)) (mul_ne_zero I_ne_zero (exp_ne_zero _))) *
    unitT (hyperbolicHeckeParam θ) i

variable {α θ : ℂ}

/-- The value of `γ i` is `I * exp (-α) • T i`. -/
@[simp]
theorem val_hyperbolicGen (i : ℕ) :
    (hyperbolicGen α θ i : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)) =
      (I * exp (-α)) • T _ i := by
  simp [hyperbolicGen, Algebra.smul_def]

/-- The inverse of `γ i` is `-I * exp α • (T i - (exp (-θ) - exp θ))`. -/
@[simp]
theorem val_inv_hyperbolicGen (i : ℕ) :
    (↑(hyperbolicGen α θ i)⁻¹ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)) =
      (-I * exp α) • (T _ i - algebraMap ℂ _ (exp (-θ) - exp θ)) := by
  apply Units.inv_eq_of_mul_eq_one_right
  have h : I * exp (-α) * (-I * exp α) = 1 := by
    rw [mul_mul_mul_comm, ← exp_add]
    simp
  simp only [val_hyperbolicGen, smul_mul_smul_comm, h, one_smul]
  simpa [exp_neg] using Units.mul_inv (unitT (hyperbolicHeckeParam θ) i)

/-- **The two-eigenvalue form of `γ i`.** With `P` the eigenprojection
`(2 * cosh θ)⁻¹ • (T i + exp θ)` of `T i`,
`γ i = I • (exp (-α - θ) • P - exp (-α + θ) • (1 - P))`. -/
theorem val_hyperbolicGen_eq_eigenprojection (hθ : cosh θ ≠ 0) (i : ℕ) :
    (hyperbolicGen α θ i : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)) =
      I • (exp (-α - θ) • ((2 * cosh θ)⁻¹ • (T _ i + algebraMap ℂ _ (exp θ))) -
        exp (-α + θ) • (1 - (2 * cosh θ)⁻¹ • (T _ i + algebraMap ℂ _ (exp θ)))) := by
  have hT := T_eq_smul_eigenprojection_sub_smul (Units.mk0 _ (mul_ne_zero two_ne_zero hθ))
    (two_mul_cosh_eq_hyperbolicHeckeParam_add_inv θ) i
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, val_hyperbolicHeckeParam, exp_neg,
    inv_inv] at hT
  set P := (2 * cosh θ)⁻¹ • (T (hyperbolicHeckeParam θ) i + algebraMap ℂ _ (exp θ))
  rw [val_hyperbolicGen, hT]
  simp only [exp_sub, exp_add, exp_neg]
  module

/-- **The two-eigenvalue form of `γ i⁻¹`.** With `P` the eigenprojection
`(2 * cosh θ)⁻¹ • (T i + exp θ)` of `T i`,
`γ i⁻¹ = -I • (exp (α + θ) • P - exp (α - θ) • (1 - P))`. -/
theorem val_inv_hyperbolicGen_eq_eigenprojection (hθ : cosh θ ≠ 0) (i : ℕ) :
    (↑(hyperbolicGen α θ i)⁻¹ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)) =
      -I • (exp (α + θ) • ((2 * cosh θ)⁻¹ • (T _ i + algebraMap ℂ _ (exp θ))) -
        exp (α - θ) • (1 - (2 * cosh θ)⁻¹ • (T _ i + algebraMap ℂ _ (exp θ)))) := by
  have hT := val_inv_unitT_eq_smul_eigenprojection_sub_smul
    (Units.mk0 _ (mul_ne_zero two_ne_zero hθ)) (two_mul_cosh_eq_hyperbolicHeckeParam_add_inv θ) i
  rw [val_inv_unitT] at hT
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, val_hyperbolicHeckeParam, exp_neg,
    inv_inv] at hT
  set P := (2 * cosh θ)⁻¹ • (T (hyperbolicHeckeParam θ) i + algebraMap ℂ _ (exp θ))
  rw [val_inv_hyperbolicGen]
  simp only [exp_neg]
  rw [hT]
  simp only [exp_sub, exp_add]
  module

/-- **The skein identity of `γ i`.** `exp α • γ + exp (-α) • γ⁻¹ + 2 I sinh θ = 0`. This is the
relation `x γ + y γ⁻¹ + z = 0` with skein parameters `(exp α, exp (-α), 2 I sinh θ)`; note the
plus sign on the second parameter. -/
theorem hyperbolicGen_skein (i : ℕ) :
    exp α • (hyperbolicGen α θ i : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)) +
        exp (-α) • (↑(hyperbolicGen α θ i)⁻¹ : InfiniteTypeAHeckeAlgebra ℂ _) +
        algebraMap ℂ _ (2 * I * sinh θ) = 0 := by
  simp only [val_hyperbolicGen, val_inv_hyperbolicGen, Algebra.algebraMap_eq_smul_one, sinh,
    exp_neg]
  have ha := exp_ne_zero α
  match_scalars <;> field_simp <;> ring

variable {z η : ℂ} {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ}

/-- **The positive stabilization constant.** For a Markov trace with projection parameter `η`,
`τ (x * γ n) = hyperbolicStabilization α θ η * τ x` for `x` in the stage of the first `n + 1`
strands. -/
theorem IsMarkovTrace.map_mul_hyperbolicGen (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)}
    (hx : x ∈ stage ℂ (hyperbolicHeckeParam θ) (n + 1)) :
    τ (x * hyperbolicGen α θ n) = hyperbolicStabilization α θ η * τ x := by
  rw [val_hyperbolicGen, mul_smul_comm, map_smul, hτ.map_mul_T hx, hz, smul_eq_mul,
    hyperbolicStabilization, exp_sub, exp_add, exp_neg, exp_neg]
  ring

/-- **The negative stabilization constant.** For a Markov trace with projection parameter `η`,
`τ (x * γ n⁻¹) = hyperbolicStabilizationInv α θ η * τ x` for `x` in the stage of the first `n + 1`
strands. -/
theorem IsMarkovTrace.map_mul_val_inv_hyperbolicGen (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)}
    (hx : x ∈ stage ℂ (hyperbolicHeckeParam θ) (n + 1)) :
    τ (x * ↑(hyperbolicGen α θ n)⁻¹) = hyperbolicStabilizationInv α θ η * τ x := by
  have hγ : (↑(hyperbolicGen α θ n)⁻¹ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)) =
      (-I * exp α) • ↑(unitT (hyperbolicHeckeParam θ) n)⁻¹ := by
    rw [val_inv_hyperbolicGen, val_inv_unitT, val_hyperbolicHeckeParam,
      val_inv_hyperbolicHeckeParam]
  rw [hγ, mul_smul_comm, map_smul, hτ.map_mul_val_inv_unitT hx, hz, smul_eq_mul,
    val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, hyperbolicStabilizationInv, exp_sub,
    exp_add, exp_neg]
  ring

/-- **The stabilization constants of a Markov trace agree exactly at
`η = (1 - tanh α * tanh θ) / 2`.** For a Markov trace with projection parameter `η` on the Hecke
algebra with parameter `q = exp (-θ)`, and `cosh α * cosh θ ≠ 0`, the traces of `γ n` and of
`γ n⁻¹` agree exactly when `η = (1 - tanh α * tanh θ) / 2`. -/
theorem IsMarkovTrace.map_hyperbolicGen_eq_map_inv_iff (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0) (n : ℕ) :
    τ (hyperbolicGen α θ n) = τ ↑(hyperbolicGen α θ n)⁻¹ ↔ η = (1 - tanh α * tanh θ) / 2 := by
  have h1 := hτ.map_mul_hyperbolicGen (α := α) hz (one_mem (stage ℂ _ (n + 1)))
  have h2 := hτ.map_mul_val_inv_hyperbolicGen (α := α) hz (one_mem (stage ℂ _ (n + 1)))
  rw [one_mul, hτ.map_one, mul_one] at h1 h2
  rw [h1, h2, hyperbolicStabilization_eq_hyperbolicStabilizationInv_iff_tanh hα hθ]

/-- **The complementary eigenprojection.** Precomposing a Markov trace with projection parameter
`η` with the complement automorphism, which exchanges the eigenprojections of the generators,
the traces of `γ n` and of `γ n⁻¹` agree exactly when `η = (1 + tanh α * tanh θ) / 2`. -/
theorem IsMarkovTrace.map_complementEquiv_hyperbolicGen_eq_map_inv_iff (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0) (n : ℕ) :
    τ (complementEquiv _ (hyperbolicGen α θ n)) =
        τ (complementEquiv _ ↑(hyperbolicGen α θ n)⁻¹) ↔
      η = (1 + tanh α * tanh θ) / 2 := by
  have h := (hτ.comp_complementEquiv).map_hyperbolicGen_eq_map_inv_iff (η := 1 - η)
    (by simp only [val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, hz]; ring) hα hθ n
  rw [← hyperbolicStabilization_one_sub_eq_hyperbolicStabilizationInv_one_sub_iff hα hθ,
    hyperbolicStabilization_eq_hyperbolicStabilizationInv_iff_tanh hα hθ]
  simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] using h

end InfiniteTypeAHeckeAlgebra

end TauCeti
