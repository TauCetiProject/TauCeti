/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Supports of convolution-type parametric integrals over a group

Convolutions over a group `G` are parametric integrals `s ↦ ∫ r, F s r ∂μ` whose integrand
vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L`, where `K` and `L` are the supports of the two factors.
This file records the resulting support bounds, for any normed-space valued integrand: the
parametric integral is supported in `K * L`, and for compact `K` and `L` both the integrand on
`G × G` and the parametric integral are compactly supported. For a left-invariant measure finite on
compacts, Fubini's theorem for compactly supported continuous functions then evaluates the iterated
`ℝ≥0∞`-norm convolution integral of two compactly supported continuous functions as the product of
their `L¹` seminorms without σ-finiteness.

## Main statements

* `TauCeti.support_integral_subset_mul`: the parametric integral is supported in `K * L`.
* `TauCeti.hasCompactSupport_uncurry_of_inv_mul_mem`: the integrand is compactly supported on
  `G × G`.
* `TauCeti.hasCompactSupport_integral_of_inv_mul_mem`: the parametric integral is compactly
  supported.
* `TauCeti.lintegral_lintegral_eNorm_mul_inv_mul`: iterated `ℝ≥0∞`-norm convolution identity for
  `u : C_c(G, E)` and `v : C_c(G, F)` against a left-invariant measure finite on compacts.
-/

public section

open MeasureTheory Function
open scoped CompactlySupported ENNReal Pointwise

namespace TauCeti

variable {G E : Type*} [Group G] [NormedAddCommGroup E] {F : G → G → E} {K L : Set G}

/-- A two-variable integrand which vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L` has its parametric
integral `s ↦ ∫ r, F s r` supported in `K * L`. -/
theorem support_integral_subset_mul [NormedSpace ℝ E] [MeasurableSpace G] (μ : Measure G)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) :
    support (fun s => ∫ r, F s r ∂μ) ⊆ K * L := by
  intro s hs
  by_contra h
  refine hs (integral_eq_zero_of_ae (.of_forall fun r => ?_))
  by_contra hr
  obtain ⟨hrK, hrL⟩ := hF s r hr
  exact h ⟨r, hrK, r⁻¹ * s, hrL, mul_inv_cancel_left r s⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [NormedAddCommGroup E] in
/-- A two-variable integrand which vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L`, for compact `K`
and `L`, is compactly supported on `G × G`. -/
theorem hasCompactSupport_uncurry_of_inv_mul_mem [Zero E] (hK : IsCompact K) (hL : IsCompact L)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) : HasCompactSupport (uncurry F) := by
  refine ((hK.mul hL).prod hK).closure_of_subset fun p hp => ?_
  obtain ⟨hrK, hrL⟩ := hF p.1 p.2 hp
  exact ⟨⟨p.2, hrK, p.2⁻¹ * p.1, hrL, mul_inv_cancel_left p.2 p.1⟩, hrK⟩

/-- The parametric integral `s ↦ ∫ r, F s r` of an integrand which vanishes unless `r ∈ K` and
`r⁻¹ * s ∈ L`, for compact `K` and `L`, is compactly supported. -/
theorem hasCompactSupport_integral_of_inv_mul_mem [NormedSpace ℝ E] [MeasurableSpace G]
    (μ : Measure G) (hK : IsCompact K) (hL : IsCompact L)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) :
    HasCompactSupport (fun s => ∫ r, F s r ∂μ) :=
  (hK.mul hL).closure_of_subset (support_integral_subset_mul μ hF)

/-- Iterated `ℝ≥0∞`-norm convolution identity for two compactly supported continuous functions over
a topological group with a left-invariant measure finite on compacts, proved without σ-finiteness
via `integral_integral_swap_of_hasCompactSupport`. -/
theorem lintegral_lintegral_eNorm_mul_inv_mul {E' : Type*} [NormedAddCommGroup E']
    [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] (u : C_c(G, E)) (v : C_c(G, E')) :
    (∫⁻ s, (∫⁻ r, ‖u r‖ₑ * ‖v (r⁻¹ * s)‖ₑ ∂μ) ∂μ) =
      (∫⁻ r, ‖u r‖ₑ ∂μ) * ∫⁻ s, ‖v s‖ₑ ∂μ := by
  have hsupp : ∀ s r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ≠ 0 → r ∈ tsupport u ∧ r⁻¹ * s ∈ tsupport v :=
    fun s r hsr => ⟨subset_tsupport _ (mem_support.2 fun hu => hsr (by simp [hu])),
      subset_tsupport _ (mem_support.2 fun hv => hsr (by simp [hv]))⟩
  have hcont : Continuous (uncurry fun s r => ‖u r‖ * ‖v (r⁻¹ * s)‖) := by
    rw [uncurry_def]; fun_prop
  have hNcont := continuous_integral_of_compact_support μ u.hasCompactSupport hcont
    fun s r h => (hsupp s r h).1
  have hNsupp := hasCompactSupport_integral_of_inv_mul_mem μ u.hasCompactSupport
    v.hasCompactSupport hsupp
  have hinner (s : G) : (∫⁻ r, ‖u r‖ₑ * ‖v (r⁻¹ * s)‖ₑ ∂μ) =
      ENNReal.ofReal (∫ r, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ) := by
    have hint_s : Integrable (fun r => ‖u r‖ * ‖v (r⁻¹ * s)‖) μ :=
      (hcont.comp (.prodMk_right s)).integrable_of_hasCompactSupport
        (u.hasCompactSupport.mono' fun r hr => (hsupp s r hr).1)
    rw [ofReal_integral_eq_lintegral_ofReal hint_s
      (.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    congr 1 with r
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal (hNcont.integrable_of_hasCompactSupport hNsupp)
      (.of_forall fun _ => integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    integral_integral_swap_of_hasCompactSupport hcont
      (hasCompactSupport_uncurry_of_inv_mul_mem u.hasCompactSupport v.hasCompactSupport hsupp)]
  have hswap : (∫ r, ∫ s, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ ∂μ) =
      (∫ r, ‖u r‖ ∂μ) * ∫ s, ‖v s‖ ∂μ := by
    calc (∫ r, ∫ s, ‖u r‖ * ‖v (r⁻¹ * s)‖ ∂μ ∂μ)
        = ∫ r, ‖u r‖ * ∫ s, ‖v s‖ ∂μ ∂μ := by
          congr 1 with r
          rw [integral_const_mul, integral_mul_left_eq_self (fun s => ‖v s‖) r⁻¹]
      _ = (∫ r, ‖u r‖ ∂μ) * ∫ s, ‖v s‖ ∂μ := integral_mul_const _ _
  rw [hswap, ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _),
    ofReal_integral_norm_eq_lintegral_eNorm u.integrable,
    ofReal_integral_norm_eq_lintegral_eNorm v.integrable]

end TauCeti
