/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.LogDeriv
public import TauCeti.Analysis.Complex.CanonicalProduct.Weighted
public import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.Analysis.Complex.Basic

/-!
# The genus-one product of a native zero divisor

The product `TauCeti.divisorProductOne f` uses Mathlib's whole-plane divisor support as
its index type and the divisor's natural values as multiplicities. For an entire `f` with
`f 0 ≠ 0` and weighted inverse-square summability of its zeros, it is entire, normalized at
zero, and has exactly the divisor of `f`.

Its logarithmic derivative is the classical paired sum
`∑' ρ, mρ * (1 / (z - ρ) + 1 / ρ)`. Under total division, the paired series is absolutely
convergent at every point `z : ℂ` from weighted inverse-square summability alone; when `0` is
off the divisor support, it converges locally uniformly on the complement of the support to the
logarithmic derivative of the product (for an entire `f` with `f 0 ≠ 0`, `0` lies off the support
by `AnalyticAt.notMem_divisor_support_of_ne_zero`). Consequently, for every `s : ℂ`, summability of
`mρ * Re (1 / (s - ρ))` is equivalent to summability of `mρ * Re (1 / ρ)`
(`summable_divisor_toNat_mul_re_one_div_sub_iff`); when all positive-multiplicity support points
have bounded real part (`|Re ρ| ≤ B`), `Re (1 / ρ) = Re ρ / ‖ρ‖ ^ 2` gains an extra factor of
`‖ρ‖⁻¹`, so both real-part series converge separately. When `ρ.re ≤ s.re` on positive-multiplicity
support points (or outside a finite set `S`), the corresponding summands `mρ * Re (1 / (s - ρ))`
are nonnegative, so the full `tsum` `∑' ρ, mρ * Re (1 / (s - ρ))` is nonnegative and, when
summable, dominates the finite subsum over `S`. This constructs the product and
logarithmic-derivative ingredients of Hadamard
factorization without assuming an enumeration of the zeros or choosing a representative for the
divisor.

A function with zero divisor, such as `exp (c s)`, has product `1`, and the product of `1 - s` is
the single factor `E₁(s)`.

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
    weierstrassFactor 1 ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat

/-- The defining native-support product formula. -/
theorem divisorProductOne_def (f : ℂ → ℂ) (z : ℂ) :
    divisorProductOne f z = ∏' ρ : (MeromorphicOn.divisor f Set.univ).support,
      weierstrassFactor 1 ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := (rfl)

/-- The native divisor product as a function, in the form used by the generic product lemmas. -/
theorem divisorProductOne_eq (f : ℂ → ℂ) :
    divisorProductOne f = fun z ↦ ∏' ρ : (MeromorphicOn.divisor f Set.univ).support,
      weierstrassFactor 1 ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat :=
  funext (divisorProductOne_def f)

/-- Points of the divisor support are nonzero when `0` is off the support. -/
private theorem coe_ne_zero_of_mem_divisor_support {f : ℂ → ℂ}
    (h0 : (0 : ℂ) ∉ (MeromorphicOn.divisor f Set.univ).support)
    (ρ : (MeromorphicOn.divisor f Set.univ).support) : (ρ : ℂ) ≠ 0 :=
  fun heq ↦ h0 (heq ▸ ρ.property)

/-- Off the divisor support, no slope `ρ⁻¹` of the product is a root at `z`. -/
private theorem inv_mul_ne_one_of_notMem_divisor_support {f : ℂ → ℂ}
    (h0 : (0 : ℂ) ∉ (MeromorphicOn.divisor f Set.univ).support) {z : ℂ}
    (hz : z ∉ (MeromorphicOn.divisor f Set.univ).support)
    (ρ : (MeromorphicOn.divisor f Set.univ).support) : (ρ : ℂ)⁻¹ * z ≠ 1 := by
  intro heq
  rw [inv_mul_eq_one₀ (coe_ne_zero_of_mem_divisor_support h0 ρ)] at heq
  exact hz (heq ▸ ρ.property)

/-- Off the divisor support, the paired term is the logarithmic derivative of its factor. -/
private theorem logDerivWeierstrassFactorOneMul_inv_eq {f : ℂ → ℂ}
    (h0 : (0 : ℂ) ∉ (MeromorphicOn.divisor f Set.univ).support) {z : ℂ}
    (hz : z ∉ (MeromorphicOn.divisor f Set.univ).support)
    (ρ : (MeromorphicOn.divisor f Set.univ).support) :
    logDerivWeierstrassFactorOneMul ((ρ : ℂ)⁻¹) z = 1 / (z - ρ) + 1 / ρ :=
  logDerivWeierstrassFactorOneMul_inv (coe_ne_zero_of_mem_divisor_support h0 ρ)
    (by intro h; exact hz (h ▸ ρ.property))

private theorem mulSupport_divisor_factor_subset (f : ℂ → ℂ) (z : ℂ) :
    Function.mulSupport (fun ρ : ℂ ↦ weierstrassFactor 1 (ρ⁻¹ * z) ^
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
      weierstrassFactor 1 (ρ⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := by
  exact tprod_subtype_eq_of_mulSupport_subset (mulSupport_divisor_factor_subset f z)

/-- The native divisor product is normalized to one at the origin. -/
@[simp]
theorem divisorProductOne_zero (f : ℂ → ℂ) : divisorProductOne f 0 = 1 := by
  simp [divisorProductOne_def]

/-- The genus-one product of a function with zero whole-plane divisor is `1`. -/
theorem divisorProductOne_eq_one_of_divisor_eq_zero {f : ℂ → ℂ}
    (hf : MeromorphicOn.divisor f Set.univ = 0) : divisorProductOne f = fun _ ↦ 1 := by
  funext z
  rw [divisorProductOne_eq_tprod]
  exact (tprod_congr fun ρ ↦ by simp [hf]).trans tprod_one

/-- The genus-one product of the zero-free function `exp (c s)` is `1`. -/
theorem divisorProductOne_cexp_mul (c : ℂ) :
    divisorProductOne (fun s ↦ exp (c * s)) = fun _ ↦ 1 := by
  refine divisorProductOne_eq_one_of_divisor_eq_zero ?_
  ext ρ
  exact AnalyticAt.divisor_apply_eq_zero (f := fun s ↦ exp (c * s)) (by fun_prop) (exp_ne_zero _)

/-- The genus-one product of `1 - s` is the single factor `E₁(s)`. -/
theorem divisorProductOne_one_sub :
    divisorProductOne (fun s ↦ 1 - s) = weierstrassFactor 1 := by
  funext s
  have ha : AnalyticOnNhd ℂ (fun s : ℂ ↦ 1 - s) Set.univ := fun _ _ ↦ by fun_prop
  have h1 : MeromorphicOn.divisor (fun s : ℂ ↦ 1 - s) Set.univ 1 = 1 := by
    rw [MeromorphicOn.divisor_eq_analyticOrderNatAt ha.meromorphicOn (ha 1 trivial)
      (Set.mem_univ 1), analyticOrderNatAt,
      (ha 1 trivial).analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) (by
        rw [deriv_const_sub, deriv_id'']; norm_num), ENat.toNat_one, Nat.cast_one]
  rw [divisorProductOne_eq_tprod, tprod_eq_mulSingle 1 fun ρ hρ ↦ ?_, h1]
  · simp
  · rw [AnalyticAt.divisor_apply_eq_zero (ha ρ trivial) (sub_ne_zero.mpr (Ne.symm hρ))]
    simp

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
  (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
    ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))

include hsum in
/-- Weighted inverse-square summability makes the native divisor product entire. -/
@[fun_prop]
theorem differentiable_divisorProductOne : Differentiable ℂ (divisorProductOne f) :=
  differentiable_tprod_weierstrassFactor_one_pow _ _ hsum

include hsum in
/-- The genus-one divisor product has zero first derivative at the origin. -/
theorem deriv_divisorProductOne_zero : deriv (divisorProductOne f) 0 = 0 := by
  have h := logDeriv_tprod_weierstrassFactor_one_pow
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum (z := 0) (by simp)
  rw [← divisorProductOne_eq, logDeriv_apply, divisorProductOne_zero, div_one] at h
  simpa [logDerivWeierstrassFactorOneMul_def] using h

include hsum in
/-- The full complex-indexed product converges to the native divisor product at each point. -/
theorem hasProd_divisorProductOne (z : ℂ) :
    HasProd (fun ρ : ℂ ↦ weierstrassFactor 1 (ρ⁻¹ * z) ^
      (MeromorphicOn.divisor f Set.univ ρ).toNat) (divisorProductOne f z) := by
  have h := (hasProdLocallyUniformlyOn_weierstrassFactor_one_pow
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum).hasProd (Set.mem_univ z)
  exact (hasProd_subtype_iff_of_mulSupport_subset
    (mulSupport_divisor_factor_subset f z)).mp h

include hsum in
/-- The genus-one product is nonzero at the origin and wherever the divisor is nonpositive. -/
theorem divisorProductOne_ne_zero {z : ℂ}
    (hz : z ≠ 0 → MeromorphicOn.divisor f Set.univ z ≤ 0) : divisorProductOne f z ≠ 0 := by
  rw [divisorProductOne_def, ne_eq, tprod_weierstrassFactor_one_pow_eq_zero_iff _ _ hsum]
  rintro ⟨ρ, hm, hρ⟩
  have hρ0 : (ρ : ℂ) ≠ 0 := by
    intro h
    simp [h] at hρ
  have hzρ : z = (ρ : ℂ) := ((inv_mul_eq_one₀ hρ0).mp hρ).symm
  have hz0 : z ≠ 0 := by rwa [hzρ]
  have hle := hz hz0
  rw [hzρ] at hle
  exact hm (Int.toNat_eq_zero.mpr hle)

include hf hf0 hsum in
/-- The native genus-one product has exactly the zeros of an entire function nonzero at zero. -/
theorem divisorProductOne_eq_zero_iff (z : ℂ) : divisorProductOne f z = 0 ↔ f z = 0 := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  constructor
  · intro hz
    by_contra hn
    exact divisorProductOne_ne_zero hsum
      (fun _ ↦ le_of_eq ((hf.analyticAt z).divisor_apply_eq_zero hn)) hz
  · rw [divisorProductOne_def, tprod_weierstrassFactor_one_pow_eq_zero_iff _ _ hsum]
    intro hz
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
  have h0 := (hf.analyticAt 0).notMem_divisor_support_of_ne_zero (U := Set.univ) hf0
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ hf.analyticAt z
  ext z
  rw [divisorProductOne_eq, divisor_tprod_weierstrassFactor_one_inv_mul_pow
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat)
    (by simpa only [norm_inv, inv_pow, div_eq_mul_inv] using hsum) h0 z]
  split_ifs with hz
  · exact Int.toNat_of_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa z)
  · exact (Function.notMem_support.mp hz).symm

end TauCeti

namespace TauCeti

/-- The classical paired divisor series is absolutely convergent at every point, using total
division at `ρ = 0` and `ρ = z`. -/
theorem summable_norm_natCast_divisor_mul_one_div_sub_add_one_div {f : ℂ → ℂ}
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2)) (z : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ‖((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ)‖) := by
  have hs := summable_norm_natCast_mul_logDerivWeierstrassFactorOneMul
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum z
  refine hs.congr_cofinite ?_
  rw [Filter.EventuallyEq, Filter.eventually_cofinite]
  refine (((Set.finite_singleton (0 : ℂ)).union (Set.finite_singleton z)).preimage
    Subtype.coe_injective.injOn).subset fun ρ hρ ↦ ?_
  by_contra hnot
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff, not_or] at hnot
  exact hρ (by rw [logDerivWeierstrassFactorOneMul_inv hnot.1 (Ne.symm hnot.2)])

section

variable {f : ℂ → ℂ} (h0 : (0 : ℂ) ∉ (MeromorphicOn.divisor f Set.univ).support)
  (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
    ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))

include h0 hsum

/-- The logarithmic derivative of the native divisor product is its paired divisor series. -/
theorem logDeriv_divisorProductOne {z : ℂ}
    (hz : z ∉ (MeromorphicOn.divisor f Set.univ).support) :
    logDeriv (divisorProductOne f) z =
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ) := by
  have ht := logDeriv_tprod_weierstrassFactor_one_pow
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum
    (fun ρ _ ↦ inv_mul_ne_one_of_notMem_divisor_support h0 hz ρ)
  rw [← divisorProductOne_eq] at ht
  rw [ht]
  exact tsum_congr fun ρ ↦ by rw [logDerivWeierstrassFactorOneMul_inv_eq h0 hz]

/-- The classical paired divisor series converges locally uniformly off the divisor support to
the logarithmic derivative of the native divisor product. -/
theorem hasSumLocallyUniformlyOn_logDeriv_divisorProductOne :
    HasSumLocallyUniformlyOn
      (fun (ρ : (MeromorphicOn.divisor f Set.univ).support) z ↦
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ))
      (logDeriv (divisorProductOne f))
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
    refine hseries.congr (Eventually.of_forall fun s z hz ↦ Finset.sum_congr rfl fun ρ _ ↦ ?_)
    rw [logDerivWeierstrassFactorOneMul_inv_eq h0 (hKS hz)]
  exact hpair.congr_right fun z hz ↦
    (hpair.tsum_eqOn hz).symm.trans (logDeriv_divisorProductOne h0 hsum (hKS hz)).symm

end

/-! ### Vertical-strip real-part summability and positivity -/

/-- Under weighted inverse-square summability, if all positive-multiplicity points of the
whole-plane divisor have bounded real part (`|ρ.re| ≤ B`), then the real-part series
`ρ ↦ m_ρ * Re (1 / ρ)` is summable on the divisor support. -/
theorem summable_divisor_toNat_mul_re_one_div {f : ℂ → ℂ}
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))
    {B : ℝ} (hre : ∀ ρ : ℂ, 0 < MeromorphicOn.divisor f Set.univ ρ → |ρ.re| ≤ B) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) := by
  refine Summable.of_norm_bounded (hsum.mul_left (max B 0)) fun ρ ↦ ?_
  set m : ℕ := (MeromorphicOn.divisor f Set.univ ρ).toNat
  rcases eq_or_ne m 0 with hm | hm
  · simp [hm]
  · have hpos : 0 < MeromorphicOn.divisor f Set.univ ρ := by omega
    have hρ := (hre ρ hpos).trans (le_max_left B 0)
    calc ‖(m : ℝ) * (1 / (ρ : ℂ)).re‖
        = (m : ℝ) * (|(ρ : ℂ).re| / ‖(ρ : ℂ)‖ ^ 2) := by simp [inv_re, normSq_eq_norm_sq]
      _ ≤ (m : ℝ) * (max B 0 / ‖(ρ : ℂ)‖ ^ 2) := by gcongr
      _ = max B 0 * ((m : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by
          simp only [norm_inv, inv_pow]
          ring

/-- Under weighted inverse-square summability, for every `s : ℂ` the unsubtracted real-part series
`ρ ↦ m_ρ * Re (1 / (s - ρ))` is summable on the divisor support if and only if
`ρ ↦ m_ρ * Re (1 / ρ)` is summable. -/
theorem summable_divisor_toNat_mul_re_one_div_sub_iff {f : ℂ → ℂ}
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2)) (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re) ↔
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) := by
  have hpair := (Complex.hasSum_re
    (summable_norm_natCast_divisor_mul_one_div_sub_add_one_div hsum s).of_norm.hasSum).summable
  exact ⟨fun hsub ↦ (hpair.sub hsub).congr fun ρ ↦ by simp; ring,
    fun hinv ↦ (hpair.sub hinv).congr fun ρ ↦ by simp; ring⟩

/-- Under weighted inverse-square summability, if all positive-multiplicity points of the
whole-plane divisor have bounded real part (`|ρ.re| ≤ B`), then the unsubtracted real-part series
`ρ ↦ m_ρ * Re (1 / (s - ρ))` is summable on the divisor support for every `s : ℂ`. -/
theorem summable_divisor_toNat_mul_re_one_div_sub {f : ℂ → ℂ}
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))
    {B : ℝ} (hre : ∀ ρ : ℂ, 0 < MeromorphicOn.divisor f Set.univ ρ → |ρ.re| ≤ B) (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re) :=
  (summable_divisor_toNat_mul_re_one_div_sub_iff hsum s).mpr
    (summable_divisor_toNat_mul_re_one_div hsum hre)

private theorem divisor_toNat_mul_re_one_div_sub_nonneg {f : ℂ → ℂ} {s ρ : ℂ}
    (hle : 0 < MeromorphicOn.divisor f Set.univ ρ → ρ.re ≤ s.re) :
    0 ≤ ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
  rcases le_or_gt (MeromorphicOn.divisor f Set.univ ρ) 0 with hd | hd
  · simp [Int.toNat_of_nonpos hd]
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    rw [one_div, Complex.inv_re_nonneg, sub_re, sub_nonneg]
    exact hle hd

/-- At any `s : ℂ` whose real part is at least that of every positive-multiplicity point of the
whole-plane divisor of `f`, the `tsum` `∑' ρ, m_ρ * Re (1 / (s - ρ))` over the divisor support is
nonnegative. -/
theorem tsum_divisor_toNat_mul_re_one_div_sub_nonneg {f : ℂ → ℂ} {s : ℂ}
    (hle : ∀ ρ : ℂ, 0 < MeromorphicOn.divisor f Set.univ ρ → ρ.re ≤ s.re) :
    0 ≤ ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re :=
  tsum_nonneg fun ρ ↦ divisor_toNat_mul_re_one_div_sub_nonneg (hle ρ)

/-- When `ρ ↦ m_ρ * Re (1 / (s - ρ))` is summable on the whole-plane divisor support of `f` and
every positive-multiplicity point outside `S : Finset ℂ` has real part at most `Re s`, the finite
subsum over `S` is bounded above by the full support `tsum` `∑' ρ, m_ρ * Re (1 / (s - ρ))`. -/
theorem sum_divisor_toNat_mul_re_one_div_sub_le_tsum {f : ℂ → ℂ} {s : ℂ}
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re))
    (S : Finset ℂ)
    (hle : ∀ ρ ∉ S, 0 < MeromorphicOn.divisor f Set.univ ρ → ρ.re ≤ s.re) :
    ∑ ρ ∈ S, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re ≤
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
  let d := MeromorphicOn.divisor f Set.univ
  let F : ℂ → ℝ := fun ρ ↦ ((d ρ).toNat : ℝ) * (1 / (s - ρ)).re
  have hF_supp : Function.support F ⊆ d.support := fun ρ hρ ↦
    Function.mem_support.mpr fun h0 ↦ hρ (by simp [F, h0])
  have hF_sum : HasSum F (∑' ρ : d.support, F ρ) :=
    (hasSum_subtype_iff_of_support_subset hF_supp).mp hsum.hasSum
  rw [← hF_sum.tsum_eq]
  exact hF_sum.summable.sum_le_tsum S fun ρ hρS ↦
    divisor_toNat_mul_re_one_div_sub_nonneg (hle ρ hρS)

end TauCeti
