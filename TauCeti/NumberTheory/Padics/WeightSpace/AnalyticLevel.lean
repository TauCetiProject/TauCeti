/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Character
public import TauCeti.NumberTheory.Padics.WeightSpace.LocallyAlgebraic
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# The analytic level of a weight

Put `q = p ^ k` with `k = TauCeti.padicUnitsDepth p`, let `γ = exp q` be the generator of
`1 + qℤ_p`, and let `r_j = p ^ (-1 / ((p - 1) pʲ))` be the radii `TauCeti.amiceRadius p j`, so that
`r_0 = p ^ (-1 / (p - 1))` is the radius of convergence of the `p`-adic exponential. A weight
`κ : ℤ_pˣ → Kˣ` has coordinate `T_κ = κ(γ) - 1`, and on `1 + qℤ_p` it is the binomial character
`exp (q s) ↦ (1 + T_κ) ^ s` of the logarithmic coordinate `s ∈ ℤ_p`
(`TauCeti.WeightSpace.principalChar`).

For `h = k + j`, analyticity of `κ` on the discs of level `h` of `ℤ_pˣ` is governed by
the condition `‖κ(exp (p ^ h)) - 1‖ < r_0`; this file studies that condition. Here
`exp (p ^ h) = γ ^ (p ^ j)` (`TauCeti.coe_padicUnitsGenerator_pow_prime_pow`). For a
multiplicative ultrametric norm the following are equivalent:

* `‖κ(exp (p ^ h)) - 1‖ < r_0`;
* `‖T_κ‖ < r_j = p ^ (-q / (pʰ (p - 1)))`
  (`TauCeti.WeightSpace.norm_apply_padicUnitsGenerator_pow_sub_one_lt_iff`);
* when the coefficients are complete, the character `s ↦ κ(exp (q s))` is analytic on the discs of
  level `j` of the logarithmic coordinate `s ∈ ℤ_p`
  (`TauCeti.WeightSpace.exists_eval_eq_principalChar_iff`).

The first equivalence is `TauCeti.norm_one_add_pow_sub_one_lt_iff` applied to `t = T_κ`, since
`κ(γ ^ (p ^ j)) = (1 + T_κ) ^ (p ^ j)`; the second is Amice's criterion
`TauCeti.AnalyticStage.exists_eval_eq_addChar_iff` for additive characters. The results here are
stated in the logarithmic coordinate; the expansion of `κ` itself on the discs `a + pʰℤ_p` of
`ℤ_pˣ` is not constructed in this file.

For field-valued weights, `‖T_κ‖ < 1` and `r_j → 1`, so every weight satisfies these conditions at
all large levels (`TauCeti.WeightSpace.eventually_norm_coord_lt_amiceRadius`). For locally algebraic
weights the level is controlled by the conductor:

* if `ψ` is trivial on `1 + p ^ (k + j) ℤ_p`, then the weight `x ↦ x ^ m ψ(x)` satisfies the
  condition at level `k + j`, for every `m ∈ ℤ`
  (`TauCeti.WeightSpace.norm_coord_inclusion_zpow_mul_lt_amiceRadius`). This includes the trivial
  finite-order character and the smallest level `h = k`;
* if `κ` has exact conductor `p ^ (k + j + 1)`, then `‖T_κ‖ = r_j`
  (`TauCeti.WeightSpace.norm_coord_eq_rpow`), so the condition holds at level `k + i`
  exactly when `j < i` (`TauCeti.WeightSpace.norm_coord_lt_amiceRadius_iff`): the conductor bound
  is sharp.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §§I.3–I.4.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3–4.
-/

public section

open Filter Topology

namespace TauCeti.WeightSpace

variable {p : ℕ} [hp : Fact p.Prime]

section NormMulClass

variable {K : Type*} [NormedRing K] [NormMulClass K] [NormOneClass K] [Module ℚ_[p] K]
  [NormSMulClass ℚ_[p] K] [IsUltrametricDist K]

/-- **The analytic level of a weight in terms of its coordinate.** For a multiplicative
ultrametric norm, `‖κ(γ ^ (p ^ j)) - 1‖ < r_0` exactly when `‖T_κ‖ < r_j`. Here
`γ ^ (p ^ j) = exp (p ^ (k + j))`, where `q = p ^ k`, and `r_j = p ^ (-q / (p ^ (k + j) (p - 1)))`.
-/
theorem norm_apply_padicUnitsGenerator_pow_sub_one_lt_iff (κ : WeightSpace p K) (j : ℕ) :
    ‖(κ (padicUnitsGenerator p ^ p ^ j) : K) - 1‖ < amiceRadius p 0 ↔
      ‖κ.coord‖ < amiceRadius p j := by
  rw [apply_padicUnitsGenerator_pow, norm_one_add_pow_sub_one_lt_iff]

variable [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K] [CompleteSpace K]
  (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K] [SMulCommClass ℤ_[p] S K]

/-- **Analyticity of the principal part of a weight.** For complete coefficients with a
multiplicative ultrametric norm, the character `s ↦ κ(exp (q s))` of `ℤ_p` is the evaluation of a
coefficient vector in the analytic stage `LA_j(K)` exactly when `‖T_κ‖ < r_j`. -/
theorem exists_eval_eq_principalChar_iff (κ : WeightSpace p K) {j : ℕ} :
    (∃ f : AnalyticStage p j K, ⇑(AnalyticStage.eval S f) = κ.principalChar) ↔
      ‖κ.coord‖ < amiceRadius p j := by
  rw [principalChar_eq_addChar_of_value_at_one]
  exact AnalyticStage.exists_eval_eq_addChar_iff S κ.tendsto_coord_pow

end NormMulClass

/-- **Every field-valued weight has an analytic level.** Over a normed division ring that is a
normed `ℚ_p`-algebra, `‖T_κ‖ < r_j` for all large `j`. -/
theorem eventually_norm_coord_lt_amiceRadius {K : Type*} [NormedDivisionRing K]
    [NormedAlgebra ℚ_[p] K] (κ : WeightSpace p K) :
    ∀ᶠ j in atTop, ‖κ.coord‖ < amiceRadius p j :=
  tendsto_amiceRadius.eventually (lt_mem_nhds (norm_coord_lt_one_of_normedAlgebra κ))

section Field

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]

/-- The modulus `q = p ^ k` lies in the disc of convergence of the exponential:
`p ^ (-k) < r_0 = p ^ (-1 / (p - 1))`. -/
private theorem zpow_neg_padicUnitsDepth_lt_amiceRadius_zero :
    (p : ℝ) ^ (-(padicUnitsDepth p : ℤ)) < amiceRadius p 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsub : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp1
  have hk : (1 : ℝ) < ((p : ℝ) - 1) * padicUnitsDepth p := by
    have := (Nat.one_lt_cast (α := ℝ)).mpr (one_lt_sub_one_mul_padicUnitsDepth (p := p))
    rwa [Nat.cast_mul, Nat.cast_sub hp.out.one_le, Nat.cast_one] at this
  rw [amiceRadius_def, ← Real.rpow_intCast]
  refine Real.rpow_lt_rpow_of_exponent_lt hp1 ?_
  rw [pow_zero, mul_one, Int.cast_neg, Int.cast_natCast, neg_lt_neg_iff, div_lt_iff₀ hsub]
  linarith

/-- **The conductor bound for locally algebraic weights.** If `ψ` is trivial on
`1 + p ^ (k + j) ℤ_p`, where `q = p ^ k`, then for every `m ∈ ℤ` the coordinate of the weight
`x ↦ x ^ m ψ(x)` satisfies `‖T‖ < r_j`: the weight satisfies the analyticity condition at every
level `h ≥ k` at which `ψ` is trivial on `1 + pʰℤ_p`. -/
theorem norm_coord_inclusion_zpow_mul_lt_amiceRadius (m : ℤ) {ψ : WeightSpace p K} {j : ℕ}
    (hψ : unitsPrincipal p (padicUnitsDepth p + j) ≤ ψ.toMonoidHom.ker) :
    ‖(inclusion K ^ m * ψ).coord‖ < amiceRadius p j := by
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := K)
  have hu : padicUnitsGenerator p ^ p ^ j ∈ unitsPrincipal p (padicUnitsDepth p + j) :=
    pow_pow_mem_unitsPrincipal (padicUnitsDepth_pos p) padicUnitsGenerator_mem_unitsPrincipal j
  have hum := Subgroup.zpow_mem _ hu m
  -- `ψ` is trivial at `γ ^ (p ^ j)`, so the weight takes the value `(γ ^ (p ^ j)) ^ m` there,
  -- which is congruent to `1` modulo `p ^ (k + j)`.
  have hψu : ψ (padicUnitsGenerator p ^ p ^ j) = 1 := hψ hu
  rw [← norm_apply_padicUnitsGenerator_pow_sub_one_lt_iff, ContinuousMonoidHom.mul_apply, hψu,
    mul_one, ContinuousMonoidHom.zpow_apply, ← map_zpow, norm_coe_inclusion_apply_sub_one]
  refine (mem_unitsPrincipal_iff_norm.mp hum).trans_lt
    (lt_of_le_of_lt ?_ zpow_neg_padicUnitsDepth_lt_amiceRadius_zero)
  exact zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega)

/-- **The analytic level of a weight of exact conductor `p ^ (k + j + 1)`**, where `q = p ^ k`:
`‖T_κ‖ < r_i` exactly when `j < i`, so the weight satisfies the analyticity condition at level
`k + i` exactly when `k + i` is at least the exponent `k + j + 1` of its conductor. -/
theorem norm_coord_lt_amiceRadius_iff (κ : WeightSpace p K) {i j : ℕ}
    (h : unitsPrincipal p (padicUnitsDepth p + j + 1) ≤ κ.toMonoidHom.ker)
    (h' : ¬unitsPrincipal p (padicUnitsDepth p + j) ≤ κ.toMonoidHom.ker) :
    ‖κ.coord‖ < amiceRadius p i ↔ j < i := by
  -- `norm_coord_eq_rpow` in radius notation: `‖T_κ‖ = r_j`.
  have hr : ‖κ.coord‖ = amiceRadius p j := by
    rw [norm_coord_eq_rpow κ h h', amiceRadius_def]
    push_cast [Nat.cast_sub hp.out.one_le]
    ring_nf
  rw [hr, strictMono_amiceRadius.lt_iff_lt]

end Field

end TauCeti.WeightSpace
