/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.Dagger.OneVariable.Basic
import TauCeti.RingTheory.PowerSeries.Exp.Padic

/-!
# Examples separating entire, overconvergent, restricted, and open-disc power series

These examples witness that every inclusion in the univariate chain

```text
Polynomial R ⊆ IsEntire.subring R ⊆ washnitzerAlgebra Unit R
  ⊆ IsRestricted.subring 1 ⊆ OnOpenDisc.subring R 1
```

is strict over `ℚ_p`, and verify the exact `p`-adic convergence radius of the exponential series:

* Over any nontrivial ultrametric normed commutative ring `R`, the geometric series `∑ Xⁿ` lies on
  the open unit disc (`OnOpenDisc 1`), is not restricted at radius `1`, and is not overconvergent.
* Over `ℚ_p`, `∑ p^(⌊√n⌋) Xⁿ` lies in `IsRestricted.subring 1`, yet is not overconvergent.
* Over `ℚ_p`, `∑ pⁿ Xⁿ` is overconvergent (`washnitzerAlgebra Unit ℚ_p`) and lies on the open disc
  of radius `p`, yet fails to be restricted at radius `p` (and hence at every scalar-norm radius
  `‖a‖ > 1` with `a ∈ ℚ_p`), and is not entire.
* Over `ℚ_p`, `∑ p^(n²) Xⁿ` is entire (hence overconvergent and on the open unit disc), yet is not
  the image of any polynomial.
* Every polynomial over `R` belongs to all three analytic classes (`IsEntire`,
  `washnitzerAlgebra Unit R`, and `OnOpenDisc 1`).
* Over `ℚ_p`, the exponential series `∑ Xⁿ / n!` lies on the open disc of finite radius
  `p ^ (-1 / (p - 1))` and fails to be restricted at that boundary radius; since
  `p ^ (-1 / (p - 1)) < 1`, it is neither open-unit-disc analytic, nor overconvergent, nor entire.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §§I.4, II.1.
* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.
-/

open Filter Topology PowerSeries TauCeti.Dagger
open scoped Nat

namespace TauCeti.Examples

section CommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

-- Polynomials belong to all three analytic power-series constructions: entire, overconvergent, and
-- open-unit-disc analytic.
example (q : Polynomial R) :
    (q : PowerSeries R).IsEntire ∧
      (q : PowerSeries R) ∈ washnitzerAlgebra Unit R ∧
      (q : PowerSeries R).OnOpenDisc 1 :=
  ⟨isEntire_coe q, (isEntire_coe q).mem_washnitzerAlgebra, onOpenDisc_coe q⟩

-- Over a nontrivial ultrametric normed commutative ring, `∑ Xⁿ` is analytic on the open unit disc
-- but neither restricted at radius `1` nor overconvergent.
example [Nontrivial R] :
    (mk 1 : PowerSeries R).OnOpenDisc 1 ∧
      ¬(mk 1 : PowerSeries R).IsRestricted 1 ∧
      (mk 1 : PowerSeries R) ∉ washnitzerAlgebra Unit R :=
  ⟨onOpenDisc_mk_one, TauCeti.PowerSeries.not_isRestricted_mk_one, fun h ↦
    TauCeti.PowerSeries.not_isRestricted_mk_one
      (isRestricted_of_mem_washnitzerAlgebra h zero_le_one le_rfl)⟩

end CommRing

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

-- Over `ℚ_p`, `∑ p^(⌊√n⌋) Xⁿ` lies in `IsRestricted.subring 1`, yet is not overconvergent: along
-- `n = k²`, its weighted coefficient norms at any radius `ρ > 1` equal `(‖p‖ ρᵏ)ᵏ`.
example :
    (mk fun n ↦ (p : ℚ_[p]) ^ n.sqrt) ∈ IsRestricted.subring 1 ∧
      (mk fun n ↦ (p : ℚ_[p]) ^ n.sqrt) ∉ washnitzerAlgebra Unit ℚ_[p] := by
  have hp0 : 0 < ‖(p : ℚ_[p])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hp1 : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.out.one_lt)
  refine ⟨IsRestricted.mem_subring.mpr ((isRestricted_iff' 1 _).mpr ?_), fun hf ↦ ?_⟩
  · have hsqrt : Tendsto Nat.sqrt atTop atTop :=
      tendsto_atTop.mpr fun b ↦ eventually_atTop.mpr
        ⟨b * b, fun n hn ↦ by simpa only [Nat.sqrt_eq] using Nat.sqrt_le_sqrt hn⟩
    simpa only [Function.comp_def, coeff_mk, norm_pow, one_pow, mul_one] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hp0.le hp1).comp hsqrt
  · obtain ⟨ρ, hρ, hfρ⟩ := mem_washnitzerAlgebra_unit_iff.mp hf
    have hlim := ((isRestricted_iff' ρ _).mp hfρ).comp
      (tendsto_atTop_mono Nat.le_mul_self tendsto_id)
    obtain ⟨k, hk1, hkρ⟩ :=
      (((hlim.eventually (gt_mem_nhds one_pos)).and
        ((tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_ge_atTop ‖(p : ℚ_[p])‖⁻¹))).exists
    simp only [Function.comp_def, coeff_mk, Nat.sqrt_eq, norm_pow, pow_mul, ← mul_pow] at hk1
    have hge : 1 ≤ ‖(p : ℚ_[p])‖ * ρ ^ k := (inv_le_iff_one_le_mul₀' hp0).mp hkρ
    exact (one_le_pow₀ hge).not_gt hk1

-- Over `ℚ_p`, `∑ pⁿ Xⁿ` is overconvergent and analytic on the open disc of radius `p`, yet fails
-- to be restricted at radius `p` and is not entire.
example :
    (mk fun n ↦ (p : ℚ_[p]) ^ n) ∈ washnitzerAlgebra Unit ℚ_[p] ∧
      (mk fun n ↦ (p : ℚ_[p]) ^ n).OnOpenDisc p ∧
      ¬(mk fun n ↦ (p : ℚ_[p]) ^ n).IsRestricted p ∧
      ¬(mk fun n ↦ (p : ℚ_[p]) ^ n).IsEntire := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp1 : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.out.one_lt)
  exact ⟨mk_pow_mem_washnitzerAlgebra hp1,
    by simpa [Padic.norm_p] using onOpenDisc_mk_pow (p : ℚ_[p]),
    by simpa [Padic.norm_p] using TauCeti.PowerSeries.not_isRestricted_mk_pow hp0,
    not_isEntire_mk_pow hp0⟩

-- Over `ℚ_p`, `∑ pⁿ Xⁿ` is overconvergent yet fails to be restricted at every scalar-norm radius
-- `‖a‖ > 1` with `a ∈ ℚ_p`: every such norm is at least `p`.
example (a : ℚ_[p]) (ha : 1 < ‖a‖) :
    ¬(mk fun n ↦ (p : ℚ_[p]) ^ n).IsRestricted ‖a‖ := by
  intro h
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have ha0 : a ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans ha)
  have hval : 1 ≤ -a.valuation := by
    by_contra! hlt
    have hle0 : -a.valuation ≤ 0 := by omega
    have hle1 : ‖a‖ ≤ 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation ha0]
      exact zpow_le_one_of_nonpos₀ (mod_cast hp.out.one_le) hle0
    exact ha.not_ge hle1
  have hpa : (p : ℝ) ≤ ‖a‖ := by
    rw [Padic.norm_eq_zpow_neg_valuation ha0]
    simpa using zpow_le_zpow_right₀ (a := (p : ℝ)) (mod_cast hp.out.one_le) hval
  have hp_res : (mk fun n ↦ (p : ℚ_[p]) ^ n).IsRestricted p :=
    TauCeti.PowerSeries.isRestricted_of_abs_le h (by
      rw [abs_of_nonneg (Nat.cast_nonneg p), abs_norm]
      exact hpa)
  have hnot : ¬(mk fun n ↦ (p : ℚ_[p]) ^ n).IsRestricted p := by
    simpa [Padic.norm_p] using TauCeti.PowerSeries.not_isRestricted_mk_pow hp0
  exact hnot hp_res

-- Over `ℚ_p`, `∑ p^(n²) Xⁿ` is entire (hence overconvergent), yet is not a polynomial.
example :
    (mk fun n ↦ (p : ℚ_[p]) ^ (n ^ 2)).IsEntire ∧
      (mk fun n ↦ (p : ℚ_[p]) ^ (n ^ 2)) ∈ washnitzerAlgebra Unit ℚ_[p] ∧
      ∀ q : Polynomial ℚ_[p], (q : PowerSeries ℚ_[p]) ≠ mk fun n ↦ (p : ℚ_[p]) ^ (n ^ 2) := by
  have hent : (mk fun n ↦ (p : ℚ_[p]) ^ (n ^ 2)).IsEntire :=
    isEntire_mk_pow_sq (by rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (mod_cast hp.out.one_lt))
  refine ⟨hent, hent.mem_washnitzerAlgebra, fun q hq ↦ ?_⟩
  have h := congrArg (PowerSeries.coeff (q.natDegree + 1)) hq
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _),
    coeff_mk] at h
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero) h.symm

-- Over `ℚ_p`, the exponential series `∑ Xⁿ / n!` lies on the open disc of radius
-- `p ^ (-1 / (p - 1))`.
example : (PowerSeries.exp ℚ_[p]).OnOpenDisc ((p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) := by
  have hp_pos : (0 : ℝ) < p := mod_cast hp.out.pos
  refine onOpenDisc_iff.mpr fun r hr hrR ↦ (isRestricted_iff' r _).mpr ?_
  set c : ℝ := (p : ℝ) ^ (1 / ((p : ℝ) - 1))
  have : 0 < c := Real.rpow_pos_of_pos hp_pos _
  have hrc0 : 0 ≤ r * c := by positivity
  have hrc1 : r * c < 1 := by
    calc r * c < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) * c := by gcongr
      _ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1)) :=
          (Real.rpow_add hp_pos _ _).symm
      _ = 1 := by simp
  refine squeeze_zero (fun _ ↦ by positivity) (fun n ↦ ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hrc0 hrc1)
  have hfn_pos : 0 < (p : ℝ) ^ (-((n : ℝ) / ((p : ℝ) - 1))) := Real.rpow_pos_of_pos hp_pos _
  have hinv : ‖(n ! : ℚ_[p])‖⁻¹ ≤ c ^ n := by
    calc ‖(n ! : ℚ_[p])‖⁻¹ ≤ ((p : ℝ) ^ (-((n : ℝ) / ((p : ℝ) - 1))))⁻¹ :=
          inv_anti₀ hfn_pos (Padic.rpow_neg_div_le_norm_factorial n)
      _ = (p : ℝ) ^ ((n : ℝ) / ((p : ℝ) - 1)) := by
          rw [← Real.rpow_neg hp_pos.le, neg_neg]
      _ = c ^ n := by
          rw [← Real.rpow_natCast c, ← Real.rpow_mul hp_pos.le, one_div_mul_eq_div]
  calc ‖coeff n (PowerSeries.exp ℚ_[p])‖ * r ^ n
      = ‖(n ! : ℚ_[p])‖⁻¹ * r ^ n := by simp [PowerSeries.coeff_exp]
    _ ≤ c ^ n * r ^ n := mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = (r * c) ^ n := by rw [mul_comm, mul_pow]

-- Over `ℚ_p`, `∑ Xⁿ / n!` fails to be restricted at its convergence radius `p ^ (-1 / (p - 1))`
-- (along `n = p ^ k`, every weighted coefficient norm equals `p ^ (-1 / (p - 1)) ≠ 0`), and hence
-- is neither open-unit-disc analytic, nor overconvergent, nor entire.
example :
    ¬(PowerSeries.exp ℚ_[p]).IsRestricted ((p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) ∧
      ¬(PowerSeries.exp ℚ_[p]).OnOpenDisc 1 ∧
      PowerSeries.exp ℚ_[p] ∉ washnitzerAlgebra Unit ℚ_[p] ∧
      ¬(PowerSeries.exp ℚ_[p]).IsEntire := by
  have hp_pos : (0 : ℝ) < p := mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := mod_cast hp.out.one_lt
  have hp_sub : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp1
  set R₀ : ℝ := (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))
  have hR₀_pos : 0 < R₀ := Real.rpow_pos_of_pos hp_pos _
  have hR₀_lt : R₀ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1
    (neg_neg_of_pos (one_div_pos.mpr hp_sub))
  have hnot : ¬(PowerSeries.exp ℚ_[p]).IsRestricted R₀ := fun hf ↦
    ((PowerSeries.isRestricted_exp_iff (p := p) hR₀_pos.le).mp hf).ne (by simp only [R₀, one_div])
  have hnot_open : ¬(PowerSeries.exp ℚ_[p]).OnOpenDisc 1 := fun h ↦
    hnot ((onOpenDisc_iff.mp h) R₀ hR₀_pos hR₀_lt)
  exact ⟨hnot, hnot_open,
    fun h ↦ hnot_open (onOpenDisc_one_of_mem_washnitzerAlgebra h),
    fun h ↦ hnot (h.isRestricted R₀)⟩

end Padic

end TauCeti.Examples
