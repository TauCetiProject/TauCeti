/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.RingTheory.PowerSeries.Expand
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Congruence
import TauCeti.NumberTheory.ModularForms.QExpansion.Order

/-!
# Low-order `q`-expansion coefficients at level one

Mathlib records the constant and linear `q`-coefficients of `E₄`, `E₆` and `Δ`.  This file
continues them to the `q²` and `q³` terms,
`E₄ = 1 + 240 q + 2160 q² + 6720 q³ + ⋯`, `E₆ = 1 - 504 q - 16632 q² - 122976 q³ + ⋯` and
`Δ = q - 24 q² + 252 q³ + ⋯`, proves that every coefficient of `Δ` is an integer, reads off its
expansion at every period `N`, and records that `Δ` is asymptotic to `q` at `i∞`.  These are
the coefficients the `q`-expansion of the modular invariant `j = E₄³ / Δ` is computed from.

The Eisenstein coefficients are `240 σ₃(n)` and `-504 σ₅(n)` (Mathlib's
`EisensteinSeries.E_qExpansion_coeff`).  The coefficients of `Δ` are read off the identity
`1728 Δ = E₄³ - E₆²` in the graded ring, transported to `q`-expansions.

## Main results

* `TauCeti.ModularForm.qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq`: the `q`-expansion of `Δ`
  is `(E₄³ - E₆²) / 1728`, computed on power series.
* `TauCeti.ModularForm.discriminant_qExpansion_coeff_two`,
  `TauCeti.ModularForm.discriminant_qExpansion_coeff_three`: `τ(2) = -24` and `τ(3) = 252`.
* `TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast`: every `q`-coefficient
  of `Δ` is an integer.
* `TauCeti.ModularForm.qExpansion_natCast_discriminant`: at period `N`, the expansion of `Δ` is
  its expansion at period `1` in the variable `qᴺ`, so it is `qᴺ + ⋯` with integer coefficients.
* `TauCeti.ModularForm.tendsto_discriminant_div_qParam_atImInfty`: `Δ / q → 1` at `i∞`.

## References

* J.-P. Serre, *A Course in Arithmetic*, VII.4 — the expansions of `E₄`, `E₆` and `Δ`.
-/

public noncomputable section

open UpperHalfPlane ModularForm EisensteinSeries Filter Topology
open scoped ArithmeticFunction.sigma MatrixGroups

namespace TauCeti.ModularForm

/- `bernoulli` is computed through `bernoulli'`, which is defined by well-founded recursion, so
neither `norm_num` nor elaborator-side `decide` can evaluate it; the kernel can. -/

private theorem bernoulli_four : bernoulli 4 = -1 / 30 := by decide +kernel

private theorem bernoulli_six : bernoulli 6 = 1 / 42 := by decide +kernel

/-- The `q²`-coefficient of `E₄` is `240 σ₃(2) = 2160`. -/
theorem E₄_qExpansion_coeff_two : (qExpansion 1 E₄).coeff 2 = 2160 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, bernoulli_four, ArithmeticFunction.sigma_apply,
    Nat.prime_two.divisors]

/-- The `q³`-coefficient of `E₄` is `240 σ₃(3) = 6720`. -/
theorem E₄_qExpansion_coeff_three : (qExpansion 1 E₄).coeff 3 = 6720 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, bernoulli_four, ArithmeticFunction.sigma_apply,
    Nat.prime_three.divisors]

/-- The `q²`-coefficient of `E₆` is `-504 σ₅(2) = -16632`. -/
theorem E₆_qExpansion_coeff_two : (qExpansion 1 E₆).coeff 2 = -16632 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, bernoulli_six, ArithmeticFunction.sigma_apply,
    Nat.prime_two.divisors]

/-- The `q³`-coefficient of `E₆` is `-504 σ₅(3) = -122976`. -/
theorem E₆_qExpansion_coeff_three : (qExpansion 1 E₆).coeff 3 = -122976 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, bernoulli_six, ArithmeticFunction.sigma_apply,
    Nat.prime_three.divisors]

/-- The `q`-expansion of the discriminant is `(E₄³ - E₆²) / 1728`, the image of Mathlib's
`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded` under the `q`-expansion algebra
homomorphism `ModularForm.qExpansionAlgHom`. -/
theorem qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq :
    qExpansion 1 discriminant = (1728 : ℂ)⁻¹ • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
  simpa [CuspForm.coe_discriminant] using congr(ModularForm.qExpansionAlgHom 1 one_pos
    one_mem_strictPeriods_SL $discriminant_eq_E₄_cube_sub_E₆_sq_graded)

/-- The constant coefficient of the discriminant vanishes: `Δ` is a cusp form. -/
theorem discriminant_qExpansion_coeff_zero : (qExpansion 1 discriminant).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL

/-- The `q²`-coefficient of the discriminant is Ramanujan's `τ(2) = -24`. -/
theorem discriminant_qExpansion_coeff_two : (qExpansion 1 discriminant).coeff 2 = -24 := by
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₆_qExpansion_coeff_two,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

/-- The `q³`-coefficient of the discriminant is Ramanujan's `τ(3) = 252`. -/
theorem discriminant_qExpansion_coeff_three : (qExpansion 1 discriminant).coeff 3 = 252 := by
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₆_qExpansion_coeff_two,
    E₄_qExpansion_coeff_three, E₆_qExpansion_coeff_three,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

/-- **The `q`-expansion of the discriminant has integer coefficients.** -/
theorem exists_discriminant_qExpansion_coeff_eq_intCast (n : ℕ) :
    ∃ m : ℤ, (qExpansion 1 discriminant).coeff n = m := by
  -- With `E₄ = 1 + 240 A`, `E₆ = 1 - 504 B`, `A = ∑ σ₃(n) qⁿ` and `B = ∑ σ₅(n) qⁿ`, one has
  -- `(E₄³ - E₆²) / 1728 = (5 A + 7 B) / 12 + 100 A² + 8000 A³ - 147 B²`, and `C = (5 A + 7 B) / 12`
  -- is integral by the congruence `12 ∣ 5 σ₃(n) + 7 σ₅(n)`
  -- (`TauCeti.twelve_dvd_five_mul_sigma_three_add_seven_mul_sigma_five`).
  let A : PowerSeries ℤ := PowerSeries.mk fun n ↦ (σ 3 n : ℤ)
  let B : PowerSeries ℤ := PowerSeries.mk fun n ↦ (σ 5 n : ℤ)
  let C : PowerSeries ℤ := PowerSeries.mk fun n ↦ ((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ)
  have hC : 12 * C = 5 * A + 7 * B := by
    ext n
    have := Nat.mul_div_cancel' (twelve_dvd_five_mul_sigma_three_add_seven_mul_sigma_five n)
    simp only [PowerSeries.coeff_ofNat_mul, map_add, PowerSeries.coeff_mk, C, A, B]
    exact_mod_cast this
  let φ := PowerSeries.map (Int.castRingHom ℂ)
  have hE₄ : qExpansion 1 E₄ = 1 + 240 * φ A := by
    ext m
    rw [E_qExpansion_coeff _ ⟨2, rfl⟩]
    simp only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_map,
      PowerSeries.coeff_mk, φ, A]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp [hm, bernoulli_four]
      norm_num
  have hE₆ : qExpansion 1 E₆ = 1 - 504 * φ B := by
    ext m
    rw [E_qExpansion_coeff _ ⟨3, rfl⟩]
    simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_map,
      PowerSeries.coeff_mk, φ, B]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp [hm, bernoulli_six]
      norm_num
  set P := C + 100 * A ^ 2 + 8000 * A ^ 3 - 147 * B ^ 2
  have hP : (1 + 240 * φ A) ^ 3 - (1 - 504 * φ B) ^ 2 = 1728 * φ P := by
    have : (1 + 240 * A) ^ 3 - (1 - 504 * B) ^ 2 = 1728 * P := by
      linear_combination (-144) * hC
    simpa only [map_sub, map_pow, map_add, map_mul, map_one, map_ofNat] using congrArg φ this
  refine ⟨P.coeff n, ?_⟩
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq, hE₄, hE₆, hP, PowerSeries.coeff_smul,
    PowerSeries.coeff_ofNat_mul, smul_eq_mul, inv_mul_cancel_left₀ (by norm_num)]
  simp [φ]

section Period

variable {N : ℕ} [NeZero N]

/-- The expansion of `Δ` at period `N` is its expansion at period `1` in the variable `qᴺ`. -/
theorem qExpansion_natCast_discriminant :
    qExpansion N discriminant =
      PowerSeries.expand N (NeZero.ne N) (qExpansion 1 discriminant) := by
  simpa using TauCeti.qExpansion_nat_mul one_pos (Nat.pos_of_ne_zero (NeZero.ne N))
    (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL)
    (ModularFormClass.bdd_at_infty CuspForm.discriminant) CuspForm.discriminant.holo'

/-- The coefficients of `Δ` at period `N` vanish below `N`. -/
@[simp]
theorem qExpansion_natCast_discriminant_coeff_of_lt {i : ℕ} (hi : i < N) :
    (qExpansion N discriminant).coeff i = 0 := by
  rw [qExpansion_natCast_discriminant, PowerSeries.coeff_expand]
  split_ifs with h
  · obtain rfl : i = 0 := Nat.eq_zero_of_dvd_of_lt h hi
    simpa using discriminant_qExpansion_coeff_zero
  · rfl

/-- The coefficient of `qᴺ` in the expansion of `Δ` at period `N` is `1`. -/
@[simp]
theorem qExpansion_natCast_discriminant_coeff_self :
    (qExpansion N discriminant).coeff N = 1 := by
  simpa [qExpansion_natCast_discriminant, discriminant_qExpansion_coeff_one] using
    PowerSeries.coeff_expand_mul N (NeZero.ne N) (qExpansion 1 discriminant) 1

/-- The coefficients of `Δ` at period `N` lie in every subring of `ℂ`. -/
theorem qExpansion_natCast_discriminant_coeff_mem {R : Subring ℂ} (i : ℕ) :
    (qExpansion N discriminant).coeff i ∈ R := by
  rw [qExpansion_natCast_discriminant, PowerSeries.coeff_expand]
  split_ifs
  · obtain ⟨m, hm⟩ := exists_discriminant_qExpansion_coeff_eq_intCast (i / N)
    rw [hm]
    exact intCast_mem R m
  · exact R.zero_mem

end Period

/-- The discriminant is asymptotic to `q` at `i∞`: `Δ / q → 1`. -/
theorem tendsto_discriminant_div_qParam_atImInfty :
    Tendsto (fun τ ↦ discriminant τ / Function.Periodic.qParam 1 τ) atImInfty (𝓝 1) := by
  simpa [discriminant_qExpansion_coeff_one] using
    TauCeti.UpperHalfPlane.tendsto_div_qParam_atImInfty one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL)
      (ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
        one_mem_strictPeriods_SL).differentiableAt
      discriminant_qExpansion_coeff_zero

end TauCeti.ModularForm
