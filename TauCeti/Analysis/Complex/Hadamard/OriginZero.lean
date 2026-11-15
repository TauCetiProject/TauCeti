/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability

/-!
# Hadamard factorization at order at most one with a zero at the origin

For a nonzero entire function `f : ℂ → ℂ` of order at most one that may vanish at the origin, let
`m = (analyticOrderAt f 0).toNat` be its finite order of vanishing at `0`. Iterated divided
differences `dslope` factor `f` globally on `ℂ` as `f z = z ^ m * g z`, where `g` is entire,
`g 0 = iteratedDeriv m f 0 / m! ≠ 0`, and `OrderLE g 1` holds because `‖g z‖ ≤ ‖f z‖` for
`‖z‖ ≥ 1`.

Applying `TauCeti.OrderLE.exists_eq_cexp_mul_divisorProductOne` to `g` yields
`f z = z ^ m * exp (a + b * z) * divisorProductOne f z`: away from `0` the whole-plane divisor of
`g` coincides with that of `f`, while at `ρ = 0` the totalized factor `E₁(0⁻¹ * z) = E₁(0) = 1`
leaves `divisorProductOne f = divisorProductOne g` unchanged. Equivalently, the canonical genus-one
product runs over the nonzero complex plane `{ρ : ℂ // ρ ≠ 0}` (or over the nonzero divisor support
`{ρ : (MeromorphicOn.divisor f Set.univ).support // (ρ : ℂ) ≠ 0}`) with locally uniform convergence
on `ℂ`.

## Main results

* `Differentiable.exists_eq_sub_pow_smul` and `Differentiable.exists_eq_sub_pow_mul`: global entire
  factorization `f z = (z - z₀) ^ m • g z` with `g` entire and `g z₀ ≠ 0` at any finite-order point
  `z₀ : ℂ`.
* `TauCeti.OrderLE.of_eq_sub_pow_mul`: dividing an entire function by `(z - z₀) ^ m` preserves
  `OrderLE · A` at every real exponent `A`.
* `TauCeti.divisorProductOne_eq_of_eq_pow_mul` and `TauCeti.divisorProductOne_eq_tprod_ne_zero`:
  invariance of `divisorProductOne` under factoring out `z ^ m`, and restriction of the product to
  nonzero points.
* `TauCeti.OrderLE.exists_eq_pow_mul_cexp_mul_divisorProductOne` and
  `TauCeti.hadamard_of_orderLE_one_of_ne_zero`: Hadamard factorization for any nonzero entire
  function of order at most one, allowing a zero at the origin.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Theorem 8.7 and Exercise 8.4.10.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 11 and 12.
-/

public section

open Complex Filter Metric Topology Bornology Asymptotics
open scoped BigOperators

section EntireZeroExtraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The divided difference `dslope f z₀` of an entire function `f : ℂ → E` is entire. -/
theorem Differentiable.dslope {f : ℂ → E} (hf : Differentiable ℂ f) (z₀ : ℂ) :
    Differentiable ℂ (_root_.dslope f z₀) :=
  differentiableOn_univ.mp ((Complex.differentiableOn_dslope Filter.univ_mem).mpr
    hf.differentiableOn)

/-- An entire function `f : ℂ → E` of finite analytic order `m` at `z₀` factors globally on `ℂ` as
`f z = (z - z₀) ^ m • g z`, where `g` is entire, `g z₀ ≠ 0`, and
`m! • g z₀ = iteratedDeriv m f z₀`. -/
theorem Differentiable.exists_eq_sub_pow_smul {f : ℂ → E} (hf : Differentiable ℂ f) {z₀ : ℂ}
    {m : ℕ} (hm : analyticOrderAt f z₀ = (m : ℕ∞)) :
    ∃ g : ℂ → E, Differentiable ℂ g ∧ g z₀ ≠ 0 ∧ m.factorial • g z₀ = iteratedDeriv m f z₀ ∧
      ∀ z : ℂ, f z = (z - z₀) ^ m • g z := by
  suffices h : ∃ g : ℂ → E, Differentiable ℂ g ∧ g z₀ ≠ 0 ∧
      ∀ z : ℂ, f z = (z - z₀) ^ m • g z by
    obtain ⟨g, hg, hg0, hfg⟩ := h
    refine ⟨g, hg, hg0, ?_, hfg⟩
    have hfun : f = fun z ↦ (z - z₀) ^ m • g z := funext hfg
    rw [hfun, TauCeti.iteratedDeriv_pow_sub_smul_self (hg.analyticAt z₀).contDiffAt]
  induction m generalizing f with
  | zero =>
    have hf0 : f z₀ ≠ 0 := (hf.analyticAt z₀).analyticOrderAt_eq_zero.mp (by simpa using hm)
    exact ⟨f, hf, hf0, fun z ↦ by simp⟩
  | succ m ih =>
    have hfz : f z₀ = 0 := by
      by_contra hne
      have h0 : analyticOrderAt f z₀ = 0 := (hf.analyticAt z₀).analyticOrderAt_eq_zero.mpr hne
      rw [h0] at hm
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m) hm.symm
    have hd : Differentiable ℂ (_root_.dslope f z₀) := hf.dslope z₀
    have hord_add : analyticOrderAt (_root_.dslope f z₀) z₀ + 1 = ((m + 1 : ℕ) : ℕ∞) :=
      ((hf.analyticAt z₀).analyticOrderAt_dslope_add_one hfz).trans hm
    have hord : analyticOrderAt (_root_.dslope f z₀) z₀ = (m : ℕ∞) := by
      cases ho : analyticOrderAt (_root_.dslope f z₀) z₀ with
      | top =>
        rw [ho, top_add] at hord_add
        exact absurd hord_add (ENat.top_ne_natCast (m + 1))
      | coe k =>
        rw [ho] at hord_add
        have hk : k + 1 = m + 1 := by exact_mod_cast hord_add
        exact congrArg Nat.cast (Nat.succ.inj hk)
    obtain ⟨g, hg, hg0, hfg⟩ := ih hd hord
    refine ⟨g, hg, hg0, fun z ↦ ?_⟩
    calc f z = (z - z₀) • _root_.dslope f z₀ z := (sub_smul_dslope_of_zero hfz z).symm
      _ = (z - z₀) • ((z - z₀) ^ m • g z) := by rw [hfg z]
      _ = (z - z₀) ^ (m + 1) • g z := by rw [pow_succ', mul_smul]

end EntireZeroExtraction

/-- A scalar entire function `f : ℂ → ℂ` of finite analytic order `m` at `z₀` factors globally on
`ℂ` as `f z = (z - z₀) ^ m * g z`, with `g` entire, `g z₀ ≠ 0`, and
`g z₀ = iteratedDeriv m f z₀ / m!`. -/
theorem Differentiable.exists_eq_sub_pow_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    {m : ℕ} (hm : analyticOrderAt f z₀ = (m : ℕ∞)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g z₀ ≠ 0 ∧
      g z₀ = iteratedDeriv m f z₀ / (m.factorial : ℂ) ∧
      ∀ z : ℂ, f z = (z - z₀) ^ m * g z := by
  obtain ⟨g, hg, hg0, hder, hfg⟩ := hf.exists_eq_sub_pow_smul hm
  refine ⟨g, hg, hg0, ?_, fun z ↦ by simpa only [smul_eq_mul] using hfg z⟩
  have hfac : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  rw [← hder, nsmul_eq_mul, mul_div_cancel_left₀ _ hfac]

/-- A nonzero entire function `f : ℂ → ℂ` has finite analytic order at every point `z₀ : ℂ`. -/
theorem Differentiable.analyticOrderAt_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f ≠ 0) (z₀ : ℂ) : analyticOrderAt f z₀ ≠ ⊤ :=
  (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀ (fun z ↦ hf.analyticAt z)).not.mpr hf0

/-- A nonzero entire function `f : ℂ → ℂ` factors at the origin as
`f z = z ^ (analyticOrderAt f 0).toNat * g z`, with `g` entire and `g 0 ≠ 0`. -/
theorem Differentiable.exists_eq_pow_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
      g 0 = iteratedDeriv (analyticOrderAt f 0).toNat f 0 /
        ((analyticOrderAt f 0).toNat.factorial : ℂ) ∧
      ∀ z : ℂ, f z = z ^ (analyticOrderAt f 0).toNat * g z := by
  have htop : analyticOrderAt f 0 ≠ ⊤ := hf.analyticOrderAt_ne_top hf0 0
  obtain ⟨g, hg, hg0, hder, hfg⟩ :=
    hf.exists_eq_sub_pow_mul (z₀ := 0) (m := (analyticOrderAt f 0).toNat)
      (ENat.natCast_toNat htop).symm
  exact ⟨g, hg, hg0, hder, fun z ↦ by simpa only [sub_zero] using hfg z⟩

namespace TauCeti

variable {f g : ℂ → ℂ}

/-- Dividing a function of order at most `A` by `(z - z₀) ^ m` preserves `OrderLE · A`, because
`‖g z‖ ≤ ‖f z‖` whenever `‖z - z₀‖ ≥ 1`. -/
theorem OrderLE.of_eq_sub_pow_mul {A : ℝ} (h : OrderLE f A) {z₀ : ℂ} {m : ℕ}
    (hfg : ∀ z : ℂ, f z = (z - z₀) ^ m * g z) : OrderLE g A := by
  refine (IsBigO.of_bound 1 ?_).orderLE h
  filter_upwards [eventually_cobounded_le_norm (‖z₀‖ + 1)] with z hz
  have hsub : 1 ≤ ‖z - z₀‖ := by
    have htri := norm_sub_norm_le z z₀
    linarith
  have hpow : 1 ≤ ‖z - z₀‖ ^ m := one_le_pow₀ hsub
  rw [one_mul, hfg z, norm_mul, norm_pow]
  exact le_mul_of_one_le_left (norm_nonneg _) hpow

/-- Dividing a function of order at most `A` by `z ^ m` preserves `OrderLE · A`. -/
theorem OrderLE.of_eq_pow_mul {A : ℝ} (h : OrderLE f A) {m : ℕ}
    (hfg : ∀ z : ℂ, f z = z ^ m * g z) : OrderLE g A :=
  h.of_eq_sub_pow_mul (z₀ := 0) fun z ↦ by simpa only [sub_zero] using hfg z

/-- If `f z = (z - z₀) ^ m * g z` with `g` entire and `g z₀ ≠ 0`, the whole-plane divisor of `g`
agrees with that of `f` away from `z₀` and vanishes at `z₀`. -/
theorem divisor_eq_update_of_eq_sub_pow_mul (hg : Differentiable ℂ g) {z₀ : ℂ} (hg0 : g z₀ ≠ 0)
    {m : ℕ} (hfg : ∀ z : ℂ, f z = (z - z₀) ^ m * g z) (w : ℂ) :
    MeromorphicOn.divisor g Set.univ w =
      if w = z₀ then 0 else MeromorphicOn.divisor f Set.univ w := by
  split_ifs with hw
  · subst hw
    exact (hg.analyticAt w).divisor_apply_eq_zero hg0
  · have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ by
      rw [funext hfg]
      exact (((analyticAt_id.sub analyticAt_const).pow m).mul (hg.analyticAt z))
    have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ ↦ hg.analyticAt z
    rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hga.meromorphicOn (hga w trivial)
      (Set.mem_univ w),
      MeromorphicOn.divisor_eq_analyticOrderNatAt hfa.meromorphicOn (hfa w trivial)
      (Set.mem_univ w), analyticOrderNatAt, analyticOrderNatAt]
    have hpow_an : AnalyticAt ℂ (fun z : ℂ ↦ (z - z₀) ^ m) w := by fun_prop
    have hpow_ne : (w - z₀) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hw)
    have hmul_eq : f = (fun z ↦ (z - z₀) ^ m) * g := funext hfg
    have hord : analyticOrderAt f w = analyticOrderAt g w := by
      rw [hmul_eq, analyticOrderAt_mul hpow_an (hg.analyticAt w),
        hpow_an.analyticOrderAt_eq_zero.mpr hpow_ne, zero_add]
    rw [hord]

/-- Extending the genus-one divisor product over `{ρ : ℂ // ρ ≠ 0}` leaves `divisorProductOne f`
unchanged, because the totalized factor at `ρ = 0` is `E₁(0⁻¹ * z) = 1`. -/
theorem divisorProductOne_eq_tprod_ne_zero (f : ℂ → ℂ) (z : ℂ) :
    divisorProductOne f z = ∏' ρ : {ρ : ℂ // ρ ≠ 0},
      weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := by
  rw [divisorProductOne_eq_tprod]
  refine (tprod_subtype_eq_of_mulSupport_subset (s := {ρ : ℂ | ρ ≠ 0}) ?_).symm
  intro ρ hρ
  rw [Set.mem_ofPred_eq]
  rintro rfl
  exact hρ (by simp)

/-- Factoring out `z ^ m` from an entire function leaves `divisorProductOne` unchanged. -/
theorem divisorProductOne_eq_of_eq_pow_mul (hg : Differentiable ℂ g) (hg0 : g 0 ≠ 0)
    {m : ℕ} (hfg : ∀ z : ℂ, f z = z ^ m * g z) :
    divisorProductOne f = divisorProductOne g := by
  funext z
  rw [divisorProductOne_eq_tprod_ne_zero, divisorProductOne_eq_tprod_ne_zero]
  refine tprod_congr fun ρ ↦ ?_
  have hd := divisor_eq_update_of_eq_sub_pow_mul hg hg0
    (fun w ↦ by simpa only [sub_zero] using hfg w) ρ.1
  rw [hd, ite_eq_right ρ.2]

/-- Locally uniform convergence on `ℂ` of the genus-one canonical product over the nonzero divisor
support `{ρ : (MeromorphicOn.divisor f Set.univ).support // (ρ : ℂ) ≠ 0}` for any nonzero entire
function `f` of order less than two. -/
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
    divisorProductOne_eq_of_eq_pow_mul hg hg0 hfg
  refine ⟨a, logDeriv g 0, ha.trans hg_der, fun z ↦ ?_⟩
  rw [hfg z, hga z, hprod, mul_assoc]

/-- **Hadamard's theorem at order at most one for any nonzero entire function**, expressed over the
nonzero complex plane `{ρ : ℂ // ρ ≠ 0}` together with locally uniform convergence of the nonzero
divisor product on `ℂ`. -/
theorem hadamard_of_orderLE_one_of_ne_zero (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f ≠ 0) :
    ∃ a b : ℂ,
      exp a = iteratedDeriv (analyticOrderAt f 0).toNat f 0 /
        ((analyticOrderAt f 0).toNat.factorial : ℂ) ∧
      HasProdLocallyUniformlyOn
        (fun (ρ : {ρ : (MeromorphicOn.divisor f Set.univ).support // (ρ : ℂ) ≠ 0}) z ↦
          weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^
            (MeromorphicOn.divisor f Set.univ ρ.1).toNat)
        (divisorProductOne f) Set.univ ∧
      ∀ s : ℂ,
        Multipliable (fun ρ : {ρ : ℂ // ρ ≠ 0} ↦
          weierstrassFactorOne ((ρ : ℂ)⁻¹ * s) ^
            (MeromorphicOn.divisor f Set.univ ρ).toNat) ∧
        f s = s ^ (analyticOrderAt f 0).toNat * exp (a + b * s) *
          ∏' ρ : {ρ : ℂ // ρ ≠ 0},
            weierstrassFactorOne ((ρ : ℂ)⁻¹ * s) ^
              (MeromorphicOn.divisor f Set.univ ρ).toNat := by
  obtain ⟨g, hg, hg0, hg_der, hfg⟩ := hf.exists_eq_pow_mul hf0
  have hg_ord : OrderLE g 1 := h.of_eq_pow_mul hfg
  have hg_sum := hg_ord.summable_divisor_toNat_mul_norm_inv_sq hg (by norm_num)
  obtain ⟨a, ha, hga⟩ := hg_ord.exists_eq_cexp_mul_divisorProductOne hg hg0
  have hprod_eq : divisorProductOne f = divisorProductOne g :=
    divisorProductOne_eq_of_eq_pow_mul hg hg0 hfg
  refine ⟨a, logDeriv g 0, ha.trans hg_der,
    h.hasProdLocallyUniformlyOn_divisorProductOne_ne_zero hf (by norm_num), fun s ↦ ?_⟩
  refine ⟨?_, ?_⟩
  · have hsupp : Function.mulSupport
        (fun ρ : ℂ ↦ weierstrassFactorOne (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor g Set.univ ρ).toNat) ⊆ {ρ : ℂ | ρ ≠ 0} := by
      intro ρ hρ
      rw [Set.mem_ofPred_eq]
      rintro rfl
      exact hρ (by simp)
    have hhp := (hasProd_subtype_iff_of_mulSupport_subset hsupp).mpr
      (hasProd_divisorProductOne hg_sum s)
    refine hhp.multipliable.congr fun ρ ↦ ?_
    dsimp only [Function.comp_apply]
    have hd := divisor_eq_update_of_eq_sub_pow_mul hg hg0
      (fun w ↦ by simpa only [sub_zero] using hfg w) ρ.1
    rw [hd, ite_eq_right ρ.2]
  · rw [hfg s, hga s, ← hprod_eq, divisorProductOne_eq_tprod_ne_zero, mul_assoc]

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
  · rw [divisorProductOne_eq_of_eq_pow_mul differentiable_exp (exp_ne_zero 0) fun _ ↦ rfl]
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
