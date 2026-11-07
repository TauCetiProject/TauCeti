/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# The genus-one product of a native zero divisor

The product `TauCeti.divisorProductOne f` uses Mathlib's whole-plane divisor support as
its index type and the divisor's natural values as multiplicities. For an entire `f` with
`f 0 ≠ 0` and weighted inverse-square summability of its zeros, it is entire, normalized at
zero, and has exactly the divisor of `f`.

Its logarithmic derivative is the classical paired sum
`∑' ρ, mρ * (1 / (z - ρ) + 1 / ρ)`. The series is absolutely convergent at every point
off the divisor support and locally uniformly convergent on its complement. This constructs
the product and logarithmic-derivative ingredients of Hadamard factorization; it does not
assume an enumeration of the zeros or choose a representative for the divisor.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Complex Filter Metric Topology
open scoped BigOperators

namespace TauCeti

/-- The genus-one product over the support of the native whole-plane divisor,
with its natural multiplicities. -/
noncomputable def divisorProductOne (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏' ρ : (MeromorphicOn.divisor f Set.univ).support,
    weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat

/-- The defining native-support product formula. -/
theorem divisorProductOne_def (f : ℂ → ℂ) (z : ℂ) :
    divisorProductOne f z = ∏' ρ : (MeromorphicOn.divisor f Set.univ).support,
      weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := (rfl)

private theorem mulSupport_divisor_factor_subset (f : ℂ → ℂ) (z : ℂ) :
    Function.mulSupport (fun ρ : ℂ ↦ weierstrassFactorOne (ρ⁻¹ * z) ^
      (MeromorphicOn.divisor f Set.univ ρ).toNat) ⊆
        (MeromorphicOn.divisor f Set.univ).support := by
  intro ρ hρ
  by_contra hD
  have hz : MeromorphicOn.divisor f Set.univ ρ = 0 := by
    simpa only [Function.mem_support, not_not] using hD
  exact hρ (by simp [hz])

/-- Extending the index to all complex numbers leaves the product unchanged:
all factors off the native support have exponent zero. -/
theorem divisorProductOne_eq_tprod (f : ℂ → ℂ) (z : ℂ) :
    divisorProductOne f z = ∏' ρ : ℂ,
      weierstrassFactorOne (ρ⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := by
  exact tprod_subtype_eq_of_mulSupport_subset (mulSupport_divisor_factor_subset f z)

/-- The native divisor product is normalized to one at the origin. -/
@[simp]
theorem divisorProductOne_zero (f : ℂ → ℂ) : divisorProductOne f 0 = 1 := by
  simp [divisorProductOne_def]

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
  (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
    ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))

include hsum in
/-- Weighted inverse-square summability makes the native divisor product entire. -/
@[fun_prop]
theorem differentiable_divisorProductOne : Differentiable ℂ (divisorProductOne f) :=
  differentiable_tprod_weierstrassFactorOne_pow _ _ hsum

include hsum in
/-- The genus-one divisor product has zero first derivative at the origin. -/
theorem deriv_divisorProductOne_zero : deriv (divisorProductOne f) 0 = 0 := by
  have h := logDeriv_tprod_weierstrassFactorOne_pow
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum (z := 0) (by simp)
  have hfun : (fun w ↦ ∏' ρ : (MeromorphicOn.divisor f Set.univ).support,
      weierstrassFactorOne ((ρ : ℂ)⁻¹ * w) ^
        (MeromorphicOn.divisor f Set.univ ρ).toNat) = divisorProductOne f :=
    funext fun w ↦ (divisorProductOne_def f w).symm
  rw [hfun, logDeriv_apply, divisorProductOne_zero, div_one] at h
  simpa using h

include hsum in
/-- The full complex-indexed product converges to the native divisor product at each point. -/
theorem hasProd_divisorProductOne (z : ℂ) :
    HasProd (fun ρ : ℂ ↦ weierstrassFactorOne (ρ⁻¹ * z) ^
      (MeromorphicOn.divisor f Set.univ ρ).toNat) (divisorProductOne f z) := by
  have h := (hasProdLocallyUniformlyOn_weierstrassFactorOne_pow
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum).hasProd (Set.mem_univ z)
  exact (hasProd_subtype_iff_of_mulSupport_subset
    (mulSupport_divisor_factor_subset f z)).mp h

include hf hf0 in
private theorem divisor_support_ne_zero (ρ : (MeromorphicOn.divisor f Set.univ).support) :
    (ρ : ℂ) ≠ 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ hf.analyticAt z
  have h0 : MeromorphicOn.divisor f Set.univ 0 = 0 := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ 0),
      (hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0]
    rfl
  intro hρ
  have hρmem : MeromorphicOn.divisor f Set.univ ρ ≠ 0 := ρ.property
  exact hρmem (hρ ▸ h0)

include hf hf0 hsum in
/-- The native genus-one product has exactly the zeros of an entire function nonzero at zero. -/
theorem divisorProductOne_eq_zero_iff (z : ℂ) : divisorProductOne f z = 0 ↔ f z = 0 := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  rw [divisorProductOne_def, tprod_weierstrassFactorOne_pow_eq_zero_iff _ _ hsum]
  constructor
  · rintro ⟨ρ, _, hρ⟩
    have hzρ : z = (ρ : ℂ) := ((inv_mul_eq_one₀ (divisor_support_ne_zero hf hf0 ρ)).mp hρ).symm
    rw [hzρ]
    by_contra hn
    apply ρ.property
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfa (Set.mem_univ ρ),
      (hf.analyticAt ρ).analyticOrderAt_eq_zero.mpr hn]
    simp
  · intro hz
    have hz0 : z ≠ 0 := by rintro rfl; exact hf0 hz
    have hfin := hfa.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 0) (y := z) (Set.mem_univ 0) (Set.mem_univ z)
      (by rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0]; simp)
    have hn0 := (hf.analyticAt z).analyticOrderAt_ne_zero.mpr hz
    cases ho : analyticOrderAt f z with
    | top => exact (hfin ho).elim
    | coe n =>
      have hn : n ≠ 0 := by simpa [ho] using hn0
      have hd : MeromorphicOn.divisor f Set.univ z = (n : ℤ) := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfa (Set.mem_univ z), ho]
        simp
      have hmem : z ∈ (MeromorphicOn.divisor f Set.univ).support := by
        rw [Function.mem_support, hd]
        exact_mod_cast hn
      refine ⟨⟨z, hmem⟩, ?_, inv_mul_cancel₀ hz0⟩
      simpa only [hd, Int.toNat_natCast] using hn

include hf hf0 hsum in
/-- For an entire function nonzero at zero, the product has exactly its native divisor. -/
theorem divisor_divisorProductOne :
    MeromorphicOn.divisor (divisorProductOne f) Set.univ = MeromorphicOn.divisor f Set.univ := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ hf.analyticAt z
  have hpa : AnalyticOnNhd ℂ (divisorProductOne f) Set.univ :=
    fun z _ ↦ (differentiable_divisorProductOne hsum).analyticAt z
  ext z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hpa (Set.mem_univ z)]
  by_cases hz : z ∈ (MeromorphicOn.divisor f Set.univ).support
  · let ρ : (MeromorphicOn.divisor f Set.univ).support := ⟨z, hz⟩
    have hρ0 := divisor_support_ne_zero hf hf0 ρ
    have hinj : Function.Injective
        (fun r : (MeromorphicOn.divisor f Set.univ).support ↦ (r : ℂ)⁻¹) := by
      intro r t h
      apply Subtype.ext
      exact inv_inj.mp h
    have ho := analyticOrderAt_tprod_weierstrassFactorOne_pow_of_injective
      (fun r : (MeromorphicOn.divisor f Set.univ).support ↦ (r : ℂ)⁻¹)
      (fun r ↦ (MeromorphicOn.divisor f Set.univ r).toNat) hsum (z := z) (i := ρ)
      hinj (inv_mul_cancel₀ hρ0)
    have hfun : (fun w ↦ ∏' r : (MeromorphicOn.divisor f Set.univ).support,
        weierstrassFactorOne ((r : ℂ)⁻¹ * w) ^
          (MeromorphicOn.divisor f Set.univ r).toNat) = divisorProductOne f :=
      funext fun w ↦ (divisorProductOne_def f w).symm
    rw [hfun] at ho
    rw [ho]
    simpa only [ENat.map_natCast, WithTop.untop₀_coe] using
      Int.toNat_of_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa z)
  · have hdz : MeromorphicOn.divisor f Set.univ z = 0 := by
      simpa only [Function.mem_support, not_not] using hz
    have hpz : divisorProductOne f z ≠ 0 := by
      rw [divisorProductOne, ne_eq, tprod_weierstrassFactorOne_pow_eq_zero_iff _ _ hsum z]
      rintro ⟨ρ, _, hρ⟩
      have hρ0 := divisor_support_ne_zero hf hf0 ρ
      have heq : z = (ρ : ℂ) := by
        calc
          z = ((ρ : ℂ) * (ρ : ℂ)⁻¹) * z := by rw [mul_inv_cancel₀ hρ0, one_mul]
          _ = (ρ : ℂ) * ((ρ : ℂ)⁻¹ * z) := mul_assoc _ _ _
          _ = (ρ : ℂ) := by rw [hρ, mul_one]
      exact hz (heq ▸ ρ.property)
    rw [(hpa z trivial).analyticOrderAt_eq_zero.mpr hpz, hdz]
    rfl

end TauCeti

namespace TauCeti

variable {f : ℂ → ℂ} (h0 : (0 : ℂ) ∉ (MeromorphicOn.divisor f Set.univ).support)
  (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
    ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))

include h0 hsum

/-- The classical paired divisor series is absolutely convergent off the divisor support. -/
theorem summable_norm_logDeriv_divisorProductOne {z : ℂ}
    (hz : z ∉ (MeromorphicOn.divisor f Set.univ).support) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ‖((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ)‖) := by
  have hs := summable_norm_natCast_mul_logDerivWeierstrassFactorOneMul
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum z
  apply hs.congr
  intro ρ
  rw [logDerivWeierstrassFactorOneMul_def,
    neg_inv_sq_mul_div_one_sub_inv_mul (fun heq ↦ h0 (heq ▸ ρ.property))
    (by intro h; exact hz (h ▸ ρ.property))]

/-- The classical paired divisor series converges locally uniformly off the divisor support. -/
theorem hasSumLocallyUniformlyOn_logDeriv_divisorProductOne :
    HasSumLocallyUniformlyOn
      (fun (ρ : (MeromorphicOn.divisor f Set.univ).support) z ↦
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ))
      (fun z ↦ ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ))
      ((MeromorphicOn.divisor f Set.univ).support)ᶜ := by
  apply hasSumLocallyUniformlyOn_of_forall_compact
    ((MeromorphicOn.divisor f Set.univ).closedSupport isClosed_univ).isOpen_compl
  intro K hKS hK
  have hseries := hasSumUniformlyOn_natCast_mul_logDerivWeierstrassFactorOneMul
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum hK
  have hpair : HasSumUniformlyOn
      (fun (ρ : (MeromorphicOn.divisor f Set.univ).support) z ↦
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ))
      (fun z ↦ ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) *
          logDerivWeierstrassFactorOneMul ((ρ : ℂ)⁻¹) z) K := by
    apply hseries.congr
    apply Eventually.of_forall
    intro s z hz
    apply Finset.sum_congr rfl
    intro ρ _
    rw [logDerivWeierstrassFactorOneMul_def,
      neg_inv_sq_mul_div_one_sub_inv_mul (fun heq ↦ h0 (heq ▸ ρ.property))
      (by intro heq; exact hKS hz (heq ▸ ρ.property))]
  exact hpair.congr_right (fun z hz ↦ (hpair.tsum_eqOn hz).symm)

/-- The logarithmic derivative of the native divisor product is its paired divisor series. -/
theorem logDeriv_divisorProductOne {z : ℂ}
    (hz : z ∉ (MeromorphicOn.divisor f Set.univ).support) :
    logDeriv (divisorProductOne f) z =
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ) := by
  have hroot (ρ : (MeromorphicOn.divisor f Set.univ).support)
      (_ : (MeromorphicOn.divisor f Set.univ ρ).toNat ≠ 0) : (ρ : ℂ)⁻¹ * z ≠ 1 := by
    intro heq
    have hρz := (inv_mul_eq_one₀ (fun heq ↦ h0 (heq ▸ ρ.property))).mp heq
    exact hz (hρz ▸ ρ.property)
  have ht := logDeriv_tprod_weierstrassFactorOne_pow
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum hroot
  have hfun : (fun w ↦ ∏' r : (MeromorphicOn.divisor f Set.univ).support,
      weierstrassFactorOne ((r : ℂ)⁻¹ * w) ^
        (MeromorphicOn.divisor f Set.univ r).toNat) = divisorProductOne f :=
    funext fun w ↦ (divisorProductOne_def f w).symm
  rw [hfun] at ht
  rw [ht]
  apply tsum_congr
  intro ρ
  rw [logDerivWeierstrassFactorOneMul_def,
    neg_inv_sq_mul_div_one_sub_inv_mul (fun heq ↦ h0 (heq ▸ ρ.property))
    (by intro h; exact hz (h ▸ ρ.property))]

end TauCeti
