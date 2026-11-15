/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne
import TauCeti.Analysis.Complex.ExtractZeros
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability

/-!
# Hadamard factorization at order at most one with a zero at the origin

For a nonzero entire function `f : ℂ → ℂ` of order at most one that may vanish at the origin, let
`m = (analyticOrderAt f 0).toNat` be its finite order of vanishing at `0`. By
`Differentiable.exists_eq_pow_mul` and `TauCeti.OrderLE.of_eq_pow_mul`, `f` factors globally on `ℂ`
as `f z = z ^ m * g z`, where `g` is entire, `g 0 = iteratedDeriv m f 0 / m! ≠ 0`, and
`OrderLE g 1`.

Applying `TauCeti.OrderLE.exists_eq_cexp_mul_divisorProductOne` to `g` yields
`f z = z ^ m * exp (a + b * z) * divisorProductOne f z`: away from `0` the whole-plane divisor of
`g` coincides with that of `f` (`AnalyticOnNhd.divisor_eq_of_eq_sub_pow_smul_of_ne`), while at
`ρ = 0` the totalized factor `E₁(0⁻¹ * z) = E₁(0) = 1` leaves
`divisorProductOne f = divisorProductOne g` unchanged. Equivalently, the canonical genus-one product
runs over the nonzero complex plane `{ρ : ℂ // ρ ≠ 0}` (or over the nonzero divisor support
`{ρ : (MeromorphicOn.divisor f Set.univ).support // (ρ : ℂ) ≠ 0}`) with pointwise and locally
uniform convergence on `ℂ`.

## Main results

* `TauCeti.divisorProductOne_eq_tprod_ne_zero` and `TauCeti.divisorProductOne_eq_of_eq_pow_mul`:
  restriction of `divisorProductOne` to `{ρ : ℂ // ρ ≠ 0}` and invariance under factoring out
  `z ^ m`.
* `TauCeti.OrderLE.hasProd_divisorProductOne_ne_zero` and
  `TauCeti.OrderLE.hasProdLocallyUniformlyOn_divisorProductOne_ne_zero`: pointwise and locally
  uniform convergence of the nonzero genus-one divisor product for entire functions of order less
  than two.
* `TauCeti.OrderLE.exists_eq_pow_mul_cexp_mul_divisorProductOne`: Hadamard factorization for any
  nonzero entire function of order at most one, allowing a zero at the origin.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Theorem 8.7 and Exercise 8.4.10.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 11 and 12.
-/

public section

open Complex Filter Metric Topology
open scoped BigOperators

namespace TauCeti

variable {f g : ℂ → ℂ}

private theorem mulSupport_weierstrassFactorOne_pow_subset_ne_zero (f : ℂ → ℂ) (z : ℂ) :
    Function.mulSupport (fun ρ : ℂ ↦
      weierstrassFactorOne (ρ⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat) ⊆
      {ρ : ℂ | ρ ≠ 0} := by
  intro ρ hρ
  rw [Set.mem_ofPred_eq]
  rintro rfl
  exact hρ (by simp)

/-- Extending the genus-one divisor product over `{ρ : ℂ // ρ ≠ 0}` leaves `divisorProductOne f`
unchanged, because the totalized factor at `ρ = 0` is `E₁(0⁻¹ * z) = 1`. -/
theorem divisorProductOne_eq_tprod_ne_zero (f : ℂ → ℂ) (z : ℂ) :
    divisorProductOne f z = ∏' ρ : {ρ : ℂ // ρ ≠ 0},
      weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := by
  rw [divisorProductOne_eq_tprod]
  exact (tprod_subtype_eq_of_mulSupport_subset
    (mulSupport_weierstrassFactorOne_pow_subset_ne_zero f z)).symm

/-- Factoring out `z ^ m` from an entire function leaves `divisorProductOne` unchanged. -/
theorem divisorProductOne_eq_of_eq_pow_mul (hg : Differentiable ℂ g)
    {m : ℕ} (hfg : ∀ z : ℂ, f z = z ^ m * g z) :
    divisorProductOne f = divisorProductOne g := by
  have hga : AnalyticOnNhd ℂ g Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  funext z
  rw [divisorProductOne_eq_tprod_ne_zero, divisorProductOne_eq_tprod_ne_zero]
  refine tprod_congr fun ρ ↦ ?_
  rw [hga.divisor_eq_of_eq_sub_pow_smul_of_ne
    (fun w ↦ by simpa only [sub_zero, smul_eq_mul] using hfg w) ρ.2]

/-- Pointwise convergence on `ℂ` of the genus-one canonical product over `{ρ : ℂ // ρ ≠ 0}` for any
entire function `f` of order less than two. -/
theorem OrderLE.hasProd_divisorProductOne_ne_zero {A : ℝ}
    (h : OrderLE f A) (hf : Differentiable ℂ f) (hA : A < 2) (z : ℂ) :
    HasProd (fun ρ : {ρ : ℂ // ρ ≠ 0} ↦
      weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^
        (MeromorphicOn.divisor f Set.univ ρ).toNat)
      (divisorProductOne f z) :=
  (hasProd_subtype_iff_of_mulSupport_subset
    (mulSupport_weierstrassFactorOne_pow_subset_ne_zero f z)).mpr
    (hasProd_divisorProductOne (h.summable_divisor_toNat_mul_norm_inv_sq hf hA) z)

/-- Locally uniform convergence on `ℂ` of the genus-one canonical product over the nonzero divisor
support `{ρ : (MeromorphicOn.divisor f Set.univ).support // (ρ : ℂ) ≠ 0}` for any entire function
`f` of order less than two. -/
theorem OrderLE.hasProdLocallyUniformlyOn_divisorProductOne_ne_zero {A : ℝ}
    (h : OrderLE f A) (hf : Differentiable ℂ f) (hA : A < 2) :
    HasProdLocallyUniformlyOn
      (fun (ρ : {ρ : (MeromorphicOn.divisor f Set.univ).support // (ρ : ℂ) ≠ 0}) z ↦
        weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^
          (MeromorphicOn.divisor f Set.univ ρ.1).toNat)
      (divisorProductOne f) Set.univ := by
  have hsum_full := h.summable_divisor_toNat_mul_norm_inv_sq hf hA
  have hsum : Summable
      (fun ρ : {ρ : (MeromorphicOn.divisor f Set.univ).support // (ρ : ℂ) ≠ 0} ↦
        ((MeromorphicOn.divisor f Set.univ ρ.1).toNat : ℝ) * ‖((ρ : ℂ))⁻¹‖ ^ 2) :=
    hsum_full.subtype _
  refine (hasProdLocallyUniformlyOn_weierstrassFactorOne_pow
    (fun ρ : {ρ : (MeromorphicOn.divisor f Set.univ).support // (ρ : ℂ) ≠ 0} ↦ ((ρ : ℂ))⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ.1).toNat) hsum).congr_right fun z _ ↦ ?_
  dsimp only
  rw [divisorProductOne_eq_tprod_ne_zero]
  let j : {ρ : (MeromorphicOn.divisor f Set.univ).support // (ρ : ℂ) ≠ 0} → {ρ : ℂ // ρ ≠ 0} :=
    fun ρ ↦ ⟨ρ.1.1, ρ.2⟩
  have hj : Function.Injective j := fun r t hrt ↦
    Subtype.ext (Subtype.ext (congrArg (Subtype.val : {ρ : ℂ // ρ ≠ 0} → ℂ) hrt))
  exact hj.tprod_eq (f := fun ρ : {ρ : ℂ // ρ ≠ 0} ↦
    weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat) fun ρ hρ ↦ by
      by_contra hnot
      have hnot_supp : ρ.1 ∉ (MeromorphicOn.divisor f Set.univ).support := fun hs ↦
        hnot ⟨⟨⟨ρ.1, hs⟩, ρ.2⟩, rfl⟩
      rw [Function.notMem_support] at hnot_supp
      exact hρ (by simp [hnot_supp])

/-- **Hadamard factorization at order at most one, allowing a zero at the origin.** Every nonzero
entire function `f` with `OrderLE f 1` has the form
`f z = z ^ m * exp (a + b * z) * divisorProductOne f z`, where `m = (analyticOrderAt f 0).toNat`
and `exp a = iteratedDeriv m f 0 / m!`. -/
theorem OrderLE.exists_eq_pow_mul_cexp_mul_divisorProductOne (h : OrderLE f 1)
    (hf : Differentiable ℂ f) (hf0 : f ≠ 0) :
    ∃ a b : ℂ,
      exp a = iteratedDeriv (analyticOrderAt f 0).toNat f 0 /
        ((analyticOrderAt f 0).toNat.factorial : ℂ) ∧
      ∀ z : ℂ, f z = z ^ (analyticOrderAt f 0).toNat * exp (a + b * z) *
        divisorProductOne f z := by
  obtain ⟨g, hg, hg0, hg_der, hfg⟩ := hf.exists_eq_pow_mul hf0
  have hg_ord : OrderLE g 1 := h.of_eq_pow_mul hfg
  obtain ⟨a, ha, hga⟩ := hg_ord.exists_eq_cexp_mul_divisorProductOne hg hg0
  have hprod : divisorProductOne f = divisorProductOne g :=
    divisorProductOne_eq_of_eq_pow_mul hg hfg
  refine ⟨a, logDeriv g 0, ha.trans hg_der, fun z ↦ ?_⟩
  rw [hfg z, hga z, hprod, mul_assoc]

/-! ### Examples -/

/-- For `f = 1`, both the origin order `m` and the nonzero divisor product are trivial. -/
example :
    (analyticOrderAt (fun _ : ℂ ↦ (1 : ℂ)) 0).toNat = 0 ∧
      divisorProductOne (fun _ : ℂ ↦ (1 : ℂ)) = fun _ ↦ 1 := by
  refine ⟨by simp, ?_⟩
  simpa using divisorProductOne_cexp_mul 0

/-- For `f z = z ^ 2 * exp z`, the origin order is `2` and the nonzero-zero product is `1`. -/
example :
    (analyticOrderAt (fun z : ℂ ↦ z ^ 2 * exp z) 0).toNat = 2 ∧
      divisorProductOne (fun z : ℂ ↦ z ^ 2 * exp z) = fun _ ↦ 1 := by
  constructor
  · have hpow : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2) 0 := by fun_prop
    have hexp : AnalyticAt ℂ exp 0 := by fun_prop
    have hmul : (fun z : ℂ ↦ z ^ 2 * exp z) = (fun z : ℂ ↦ z ^ 2) * exp := rfl
    rw [hmul, analyticOrderAt_mul hpow hexp, hexp.analyticOrderAt_eq_zero.mpr (exp_ne_zero 0),
      add_zero]
    have hmono : analyticOrderAt (fun z : ℂ ↦ (z - 0) ^ 2) 0 = 2 :=
      analyticOrderAt_centeredMonomial
    simpa only [sub_zero, ENat.toNat_ofNat] using congrArg ENat.toNat hmono
  · rw [divisorProductOne_eq_of_eq_pow_mul differentiable_exp fun _ ↦ rfl]
    simpa using divisorProductOne_cexp_mul 1

/-- For `f z = 1 - z ^ 2`, the origin order is `0` and pairing `±1` gives
`divisorProductOne (fun z ↦ 1 - z ^ 2) z = E₁(z) * E₁(-z) = 1 - z ^ 2`. -/
example (z : ℂ) :
    (analyticOrderAt (fun w : ℂ ↦ 1 - w ^ 2) 0).toNat = 0 ∧
      divisorProductOne (fun w : ℂ ↦ 1 - w ^ 2) z = 1 - z ^ 2 := by
  have ha : AnalyticOnNhd ℂ (fun w : ℂ ↦ 1 - w ^ 2) Set.univ := fun _ _ ↦ by fun_prop
  refine ⟨by rw [(ha 0 trivial).analyticOrderAt_eq_zero.mpr (by norm_num), ENat.toNat_zero], ?_⟩
  have h1 : MeromorphicOn.divisor (fun w : ℂ ↦ 1 - w ^ 2) Set.univ 1 = 1 := by
    rw [MeromorphicOn.divisor_eq_analyticOrderNatAt ha.meromorphicOn (ha 1 trivial)
      (Set.mem_univ 1), analyticOrderNatAt,
      (ha 1 trivial).analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by norm_num)
        (by rw [deriv_const_sub, deriv_pow_field]; norm_num), ENat.toNat_one, Nat.cast_one]
  have hm1 : MeromorphicOn.divisor (fun w : ℂ ↦ 1 - w ^ 2) Set.univ (-1) = 1 := by
    rw [MeromorphicOn.divisor_eq_analyticOrderNatAt ha.meromorphicOn (ha (-1) trivial)
      (Set.mem_univ (-1)), analyticOrderNatAt,
      (ha (-1) trivial).analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by norm_num)
        (by rw [deriv_const_sub, deriv_pow_field]; norm_num), ENat.toNat_one, Nat.cast_one]
  have hout (ρ : ℂ) (hρ1 : ρ ≠ 1) (hρm1 : ρ ≠ -1) :
      MeromorphicOn.divisor (fun w : ℂ ↦ 1 - w ^ 2) Set.univ ρ = 0 := by
    refine AnalyticAt.divisor_apply_eq_zero (ha ρ trivial) fun hzero ↦ ?_
    have hsq : ρ ^ 2 = 1 := (sub_eq_zero.mp hzero).symm
    rcases sq_eq_one_iff.mp hsq with rfl | rfl
    · exact hρ1 rfl
    · exact hρm1 rfl
  classical
  rw [divisorProductOne_eq_tprod, tprod_eq_prod (s := ({1, -1} : Finset ℂ)) fun ρ hρ ↦ ?_]
  · rw [Finset.prod_pair (by norm_num : (1 : ℂ) ≠ -1), h1, hm1]
    simp
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ
    rw [hout ρ hρ.1 hρ.2]
    simp

end TauCeti
