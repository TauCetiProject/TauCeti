/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.LogDeriv
public import TauCeti.Analysis.Meromorphic.Divisor

/-!
# The genus-one product of a native zero divisor

Let `S ⊆ ℂ ∖ {0}` carry natural multiplicities `m` with `∑ ρ, m ρ * ‖ρ⁻¹‖ ^ 2 < ∞`. The product
`∏' ρ : S, E₁(ρ⁻¹ * z) ^ m ρ` is entire, has analytic order exactly `m ρ` at each `ρ ∈ S` and
order zero elsewhere, and is also the locally uniform limit of the repeated-index product with
one factor per unit of multiplicity. No countability, enumeration or compact-finiteness
hypothesis on `S` is needed: the summability makes the support of `m` meet each compact set in
finitely many points. In particular every nonnegative whole-plane divisor `D` with `D 0 = 0`
and weighted inverse-square summable support is the native divisor of the normalized entire
product over its support (`TauCeti.exists_entire_genusOne_product_of_divisor`).

The product `TauCeti.divisorProductOne f` uses Mathlib's whole-plane divisor support as
its index type and the divisor's natural values as multiplicities. For an entire `f` with
`f 0 ≠ 0` and weighted inverse-square summability of its zeros, it is entire, normalized at
zero, and has exactly the divisor of `f`.

Its logarithmic derivative is the classical paired sum
`∑' ρ, mρ * (1 / (z - ρ) + 1 / ρ)`. The series is absolutely convergent at every point
off the divisor support and converges locally uniformly on its complement to the logarithmic
derivative of the product. These series results assume only the weighted inverse-square
summability of the zeros and that `0` is off the divisor support, rather than that `f` is entire
with `f 0 ≠ 0`; for an entire `f` with `f 0 ≠ 0` the latter condition is
`AnalyticAt.divisor_apply_eq_zero`. This constructs
the product and logarithmic-derivative ingredients of Hadamard factorization; it does not
assume an enumeration of the zeros or choose a representative for the divisor.

A function with zero divisor, such as `exp (c s)`, has product `1`, and the product of `1 - s` is
the single factor `E₁(s)`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
* A. Rainer, *Advanced Complex Analysis*, lecture notes, TU Wien, Theorem 14.3.
-/

public section

open Complex Filter Metric Topology
open scoped BigOperators

namespace TauCeti

section Weighted

variable {S : Set ℂ} (m : S → ℕ) (hsum : Summable (fun ρ : S ↦ (m ρ : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))

include hsum

/-- At a point `ρ` of a set `S` of nonzero points, the genus-one product over `S` with natural
multiplicities `m` has analytic order exactly `m ρ`. -/
theorem analyticOrderAt_tprod_weierstrassFactorOne_inv_mul_pow_of_mem (hS : (0 : ℂ) ∉ S)
    (ρ : S) :
    analyticOrderAt (fun w ↦ ∏' σ : S, weierstrassFactorOne ((σ : ℂ)⁻¹ * w) ^ m σ) ρ = m ρ :=
  analyticOrderAt_tprod_weierstrassFactorOne_pow_of_injective (fun σ : S ↦ (σ : ℂ)⁻¹) m hsum
    (fun _ _ h ↦ Subtype.ext (inv_inj.mp h)) (inv_mul_cancel₀ fun h ↦ hS (h ▸ ρ.property))

/-- Off `S`, the genus-one product over `S` with natural multiplicities `m` has analytic order
zero. -/
theorem analyticOrderAt_tprod_weierstrassFactorOne_inv_mul_pow_of_notMem {z : ℂ} (hz : z ∉ S) :
    analyticOrderAt (fun w ↦ ∏' ρ : S, weierstrassFactorOne ((ρ : ℂ)⁻¹ * w) ^ m ρ) z = 0 := by
  rw [analyticOrderAt_tprod_weierstrassFactorOne_pow (fun ρ : S ↦ (ρ : ℂ)⁻¹) m hsum z]
  have hempty : {p : Σ ρ : S, Fin (m ρ) | (p.1 : ℂ)⁻¹ * z = 1} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun p hp ↦ hz ?_
    have hp0 : (p.1 : ℂ) ≠ 0 := by
      rintro h
      simp [h] at hp
    exact (inv_mul_eq_one₀ hp0).mp hp ▸ p.1.property
  simp [hempty]

/-- The genus-one product over `S` with natural multiplicities `m` is analytic on the plane. -/
private theorem analyticOnNhd_tprod_weierstrassFactorOne_inv_mul_pow :
    AnalyticOnNhd ℂ (fun w ↦ ∏' ρ : S, weierstrassFactorOne ((ρ : ℂ)⁻¹ * w) ^ m ρ) Set.univ :=
  fun w _ ↦ (differentiable_tprod_weierstrassFactorOne_pow _ m hsum).analyticAt w

/-- At a point `ρ` of a set `S` of nonzero points, the native divisor of the genus-one product
over `S` with natural multiplicities `m` is `m ρ`. -/
theorem divisor_tprod_weierstrassFactorOne_inv_mul_pow_of_mem (hS : (0 : ℂ) ∉ S) (ρ : S) :
    MeromorphicOn.divisor (fun w ↦ ∏' σ : S, weierstrassFactorOne ((σ : ℂ)⁻¹ * w) ^ m σ)
      Set.univ ρ = m ρ := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    (analyticOnNhd_tprod_weierstrassFactorOne_inv_mul_pow m hsum) (Set.mem_univ _),
    analyticOrderAt_tprod_weierstrassFactorOne_inv_mul_pow_of_mem m hsum hS ρ]
  simp

/-- Off `S`, the native divisor of the genus-one product over `S` with natural multiplicities
`m` vanishes. -/
theorem divisor_tprod_weierstrassFactorOne_inv_mul_pow_of_notMem {z : ℂ} (hz : z ∉ S) :
    MeromorphicOn.divisor (fun w ↦ ∏' ρ : S, weierstrassFactorOne ((ρ : ℂ)⁻¹ * w) ^ m ρ)
      Set.univ z = 0 := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    (analyticOnNhd_tprod_weierstrassFactorOne_inv_mul_pow m hsum) (Set.mem_univ _),
    analyticOrderAt_tprod_weierstrassFactorOne_inv_mul_pow_of_notMem m hsum hz]
  simp

open scoped Classical in
/-- **Genus-one products over weighted zero sets.** For a set `S` of nonzero points with natural
multiplicities `m` and `∑ ρ, m ρ * ‖ρ⁻¹‖ ^ 2 < ∞`, the products of the powers
`E₁(ρ⁻¹ * z) ^ m ρ` over `S` and of the single factors over the repeated index
`Σ ρ : S, Fin (m ρ)` converge locally uniformly on `ℂ` to the same entire function `F`, with
`F 0 = 1`, analytic order and divisor `m ρ` at each `ρ ∈ S`, and order zero off `S`. Zero
multiplicities are allowed, and `S` need not be countable. -/
theorem exists_entire_genusOne_product (hS : (0 : ℂ) ∉ S) :
    ∃ F : ℂ → ℂ,
      HasProdLocallyUniformlyOn
        (fun (ρ : S) z ↦ weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ m ρ) F Set.univ ∧
      HasProdLocallyUniformlyOn
        (fun (p : Σ ρ : S, Fin (m ρ)) z ↦ weierstrassFactorOne ((p.1 : ℂ)⁻¹ * z)) F Set.univ ∧
      Differentiable ℂ F ∧ F 0 = 1 ∧
      ∀ z, analyticOrderAt F z = (if hz : z ∈ S then (m ⟨z, hz⟩ : ℕ∞) else 0) ∧
        MeromorphicOn.divisor F Set.univ z = if hz : z ∈ S then (m ⟨z, hz⟩ : ℤ) else 0 :=
  ⟨_, hasProdLocallyUniformlyOn_weierstrassFactorOne_pow _ m hsum,
    hasProdLocallyUniformlyOn_weierstrassFactorOne_sigma _ m hsum,
    differentiable_tprod_weierstrassFactorOne_pow _ m hsum, by simp, fun z ↦ by
      by_cases hz : z ∈ S
      · simpa only [hz, ↓reduceDIte] using
          ⟨analyticOrderAt_tprod_weierstrassFactorOne_inv_mul_pow_of_mem m hsum hS ⟨z, hz⟩,
            divisor_tprod_weierstrassFactorOne_inv_mul_pow_of_mem m hsum hS ⟨z, hz⟩⟩
      · simpa only [hz, ↓reduceDIte] using
          ⟨analyticOrderAt_tprod_weierstrassFactorOne_inv_mul_pow_of_notMem m hsum hz,
            divisor_tprod_weierstrassFactorOne_inv_mul_pow_of_notMem m hsum hz⟩⟩

end Weighted

section OfDivisor

variable (D : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) (hD : 0 ≤ D) (hD0 : D 0 = 0)
  (hsum : Summable (fun ρ : D.support ↦ ((D ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))

include hD hD0 hsum

/-- A nonnegative whole-plane divisor `D` with `D 0 = 0` and weighted inverse-square summable
support is the native divisor of the genus-one product over its support. -/
theorem divisor_tprod_weierstrassFactorOne_inv_mul_pow_toNat :
    MeromorphicOn.divisor
      (fun z ↦ ∏' ρ : D.support, weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (D ρ).toNat)
      Set.univ = D := by
  ext z
  by_cases hz : z ∈ D.support
  · rw [divisor_tprod_weierstrassFactorOne_inv_mul_pow_of_mem (fun ρ : D.support ↦ (D ρ).toNat)
      hsum (by simp [hD0]) ⟨z, hz⟩]
    exact Int.toNat_of_nonneg (by simpa using Function.locallyFinsuppWithin.le_def.1 hD z)
  · rw [divisor_tprod_weierstrassFactorOne_inv_mul_pow_of_notMem
      (fun ρ : D.support ↦ (D ρ).toNat) hsum hz]
    exact (Function.notMem_support.mp hz).symm

/-- **Realization of a divisor by a genus-one product.** A nonnegative whole-plane divisor `D`
with `D 0 = 0` and `∑ ρ, D ρ * ‖ρ⁻¹‖ ^ 2 < ∞` over its support is the native divisor of an
entire function `F` with `F 0 = 1`, namely the locally uniform limit of the products of
`E₁(ρ⁻¹ * z) ^ D ρ` over the support of `D`. -/
theorem exists_entire_genusOne_product_of_divisor :
    ∃ F : ℂ → ℂ,
      HasProdLocallyUniformlyOn
        (fun (ρ : D.support) z ↦ weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (D ρ).toNat)
        F Set.univ ∧
      Differentiable ℂ F ∧ F 0 = 1 ∧ MeromorphicOn.divisor F Set.univ = D :=
  ⟨_, hasProdLocallyUniformlyOn_weierstrassFactorOne_pow _ _ hsum,
    differentiable_tprod_weierstrassFactorOne_pow _ _ hsum, by simp,
    divisor_tprod_weierstrassFactorOne_inv_mul_pow_toNat D hD hD0 hsum⟩

end OfDivisor

/-- The genus-one product over the support of the native whole-plane divisor,
with its natural multiplicities. -/
noncomputable def divisorProductOne (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏' ρ : (MeromorphicOn.divisor f Set.univ).support,
    weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat

/-- The defining native-support product formula. -/
theorem divisorProductOne_def (f : ℂ → ℂ) (z : ℂ) :
    divisorProductOne f z = ∏' ρ : (MeromorphicOn.divisor f Set.univ).support,
      weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat := (rfl)

/-- The native divisor product as a function, in the form used by the generic product lemmas. -/
theorem divisorProductOne_eq (f : ℂ → ℂ) :
    divisorProductOne f = fun z ↦ ∏' ρ : (MeromorphicOn.divisor f Set.univ).support,
      weierstrassFactorOne ((ρ : ℂ)⁻¹ * z) ^ (MeromorphicOn.divisor f Set.univ ρ).toNat :=
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
    divisorProductOne (fun s ↦ 1 - s) = weierstrassFactorOne := by
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
  differentiable_tprod_weierstrassFactorOne_pow _ _ hsum

include hsum in
/-- The genus-one divisor product has zero first derivative at the origin. -/
theorem deriv_divisorProductOne_zero : deriv (divisorProductOne f) 0 = 0 := by
  have h := logDeriv_tprod_weierstrassFactorOne_pow
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum (z := 0) (by simp)
  rw [← divisorProductOne_eq, logDeriv_apply, divisorProductOne_zero, div_one] at h
  simpa [logDerivWeierstrassFactorOneMul_def] using h

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

include hsum in
/-- When `0` is off the divisor support, the product is nonzero off the divisor support. -/
theorem divisorProductOne_ne_zero (h0 : (0 : ℂ) ∉ (MeromorphicOn.divisor f Set.univ).support)
    {z : ℂ} (hz : z ∉ (MeromorphicOn.divisor f Set.univ).support) : divisorProductOne f z ≠ 0 := by
  rw [divisorProductOne_def, ne_eq, tprod_weierstrassFactorOne_pow_eq_zero_iff _ _ hsum]
  rintro ⟨ρ, _, hρ⟩
  exact inv_mul_ne_one_of_notMem_divisor_support h0 hz ρ hρ

include hf hf0 hsum in
/-- The native genus-one product has exactly the zeros of an entire function nonzero at zero. -/
theorem divisorProductOne_eq_zero_iff (z : ℂ) : divisorProductOne f z = 0 ↔ f z = 0 := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  constructor
  · intro hz
    by_contra hn
    exact divisorProductOne_ne_zero hsum ((hf.analyticAt 0).notMem_divisor_support_of_ne_zero hf0)
      ((hf.analyticAt z).notMem_divisor_support_of_ne_zero hn) hz
  · rw [divisorProductOne_def, tprod_weierstrassFactorOne_pow_eq_zero_iff _ _ hsum]
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
  rw [divisorProductOne_eq]
  exact divisor_tprod_weierstrassFactorOne_inv_mul_pow_toNat _
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg fun z _ ↦ hf.analyticAt z)
    ((hf.analyticAt 0).divisor_apply_eq_zero hf0) hsum

end TauCeti

namespace TauCeti

variable {f : ℂ → ℂ} (h0 : (0 : ℂ) ∉ (MeromorphicOn.divisor f Set.univ).support)
  (hsum : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
    ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))

include h0 hsum

/-- The classical paired divisor series is absolutely convergent off the divisor support. -/
theorem summable_norm_natCast_divisor_mul_one_div_sub_add_one_div {z : ℂ}
    (hz : z ∉ (MeromorphicOn.divisor f Set.univ).support) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ‖((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ)‖) := by
  have hs := summable_norm_natCast_mul_logDerivWeierstrassFactorOneMul
    (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦ (ρ : ℂ)⁻¹)
    (fun ρ ↦ (MeromorphicOn.divisor f Set.univ ρ).toNat) hsum z
  exact hs.congr fun ρ ↦ by rw [logDerivWeierstrassFactorOneMul_inv_eq h0 hz]

/-- The logarithmic derivative of the native divisor product is its paired divisor series. -/
theorem logDeriv_divisorProductOne {z : ℂ}
    (hz : z ∉ (MeromorphicOn.divisor f Set.univ).support) :
    logDeriv (divisorProductOne f) z =
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ) := by
  have ht := logDeriv_tprod_weierstrassFactorOne_pow
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

end TauCeti
