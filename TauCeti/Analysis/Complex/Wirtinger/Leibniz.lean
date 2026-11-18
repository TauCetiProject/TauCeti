/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder

/-!
# The Leibniz rule for the weak conjugate Wirtinger derivative

Let `A` be a continuous family of complex-linear maps and `ξ` a continuous map on an open set
`Ω ⊆ ℂ`, with finite-dimensional values, whose distributional derivatives `\bar∂A = G` and
`\bar∂ξ = h` are locally `Lᵖ` for some `p > 1`. Then `\bar∂ (A ξ) = G ξ + A h`
distributionally (`TauCeti.HasWeakConjWirtingerDerivOn.clm_apply`).

Only the conjugate Wirtinger derivatives are assumed, not the full weak derivatives. Interior
regularity for `\bar∂` (`TauCeti.HasWeakConjWirtingerDerivOn.memWkpLoc_one`) supplies those:
both factors lie in `W^{1,p}_loc`, after lowering an infinite `p` to a finite one. Being
continuous, they are locally in every finite `Lᵃ`, so the bilinear weak Leibniz rule
`TauCeti.HasWeakFDerivOn.bilin_of_memLp` applies, with an exponent `a ≥ 2` for the factors with
`1/a + 1/p ≤ 1`. The weak derivative of the product along `1` and `I` assembles into its
conjugate Wirtinger derivative, in which the complex linearity of `A` turns
`A (∂ₛξ) + i A (∂ₜξ)` into `2 A (\bar∂ξ)`.

This is the product rule through which a solution of a linear Cauchy–Riemann equation is
multiplied by an integrating factor, as in the similarity principle.

## Main results

* `TauCeti.HasWeakConjWirtingerDerivOn.clm_apply`: `\bar∂ (A ξ) = (\bar∂A) ξ + A (\bar∂ξ)` for
  continuous factors with locally `Lᵖ` conjugate Wirtinger derivatives, `p > 1`.
-/

public section

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {p : ℝ≥0∞} {Ω : Opens ℂ}

/-- **The Leibniz rule for `\bar∂`.** Let `1 < p ≤ ∞`. On an open set `Ω`, if a continuous
family `A` of complex-linear maps has distributional `\bar∂A = G` and a continuous map `ξ` has
`\bar∂ξ = h`, with `G` and `h` locally `Lᵖ`, then `\bar∂ (A ξ) = G ξ + A h` distributionally. -/
theorem HasWeakConjWirtingerDerivOn.clm_apply (hp : 1 < p)
    {A G : ℂ → V →L[ℂ] W} {ξ h : ℂ → V} (hA : HasWeakConjWirtingerDerivOn volume Ω A G)
    (hξ : HasWeakConjWirtingerDerivOn volume Ω ξ h) (hAc : ContinuousOn A Ω)
    (hξc : ContinuousOn ξ Ω) (hG : MemLpLoc p Ω G) (hh : MemLpLoc p Ω h) :
    HasWeakConjWirtingerDerivOn volume Ω (fun z ↦ A z (ξ z)) (fun z ↦ G z (ξ z) + A z (h z)) := by
  -- the exponent may be lowered to a finite one
  wlog hp_top : p ≠ ⊤ generalizing p
  · have h12 : (1 : ℝ≥0∞) < 2 := by norm_num
    exact this (lt_min hp h12) (hG.mono_exponent (min_le_left p 2))
      (hh.mono_exponent (min_le_left p 2)) ((min_le_right p 2).trans_lt ENNReal.ofNat_lt_top).ne
  have := FiniteDimensional.completeSpace ℂ W
  -- both factors have weak derivatives in `L^p_loc`
  obtain ⟨-, DA, hDA, hDAp⟩ :=
    memWkpLoc_succ_iff_of_isOpen.1 (hA.memWkpLoc_one hp hp_top hAc.memLpLoc hG)
  obtain ⟨-, Dξ, hDξ, hDξp⟩ :=
    memWkpLoc_succ_iff_of_isOpen.1 (hξ.memWkpLoc_one hp hp_top hξc.memLpLoc hh)
  rw [memWkpLoc_zero_iff] at hDAp hDξp
  -- the factors are measured in `Lᵃ`, with `a ≥ 2` and `1 / a + 1 / p ≤ 1`
  set a : ℝ≥0∞ := max (1 - p⁻¹)⁻¹ 2
  have hp1 : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp.le
  have ha_top : a ≠ ⊤ := max_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt
    (ENNReal.inv_lt_one.2 hp)).ne') ENNReal.ofNat_ne_top
  have ha2 : a⁻¹ ≤ 2⁻¹ := ENNReal.inv_le_inv.2 (le_max_right _ _)
  have hap : a⁻¹ ≤ 1 - p⁻¹ := by
    simpa using ENNReal.inv_le_inv.2 (le_max_left (1 - p⁻¹)⁻¹ 2)
  have : Fact (1 ≤ a) := ⟨le_max_of_le_right one_le_two⟩
  have : Fact (1 ≤ p) := ⟨hp.le⟩
  have haa : a⁻¹ + a⁻¹ ≤ 1 :=
    (add_le_add ha2 ha2).trans_eq ENNReal.inv_two_add_inv_two
  have hpa : p⁻¹ + a⁻¹ ≤ 1 :=
    (add_le_add le_rfl hap).trans_eq (add_tsub_cancel_of_le hp1)
  have hap' : a⁻¹ + p⁻¹ ≤ 1 := by rwa [add_comm]
  let B : (V →L[ℂ] W) →L[ℝ] V →L[ℝ] W :=
    (ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℂ).restrictScalars ℝ
  refine ((hDA.bilin_of_memLp B ha_top hp_top ha_top hp_top haa hpa hap' hDξ
    (fun K hK hKΩ ↦ memLpLoc_iff.1 hAc.memLpLoc K hKΩ hK)
    (fun K hK hKΩ ↦ memLpLoc_iff.1 hDAp K hKΩ hK)
    (fun K hK hKΩ ↦ memLpLoc_iff.1 hξc.memLpLoc K hKΩ hK)
    (fun K hK hKΩ ↦ memLpLoc_iff.1 hDξp K hKΩ hK)).hasWeakConjWirtingerDerivOn).congr_ae_deriv ?_
  -- the conjugate Wirtinger derivatives of the factors are `G` and `h` almost everywhere
  filter_upwards [hDA.hasWeakConjWirtingerDerivOn.ae_eq hA,
    hDξ.hasWeakConjWirtingerDerivOn.ae_eq hξ] with z hAz hξz
  rw [← hAz, ← hξz]
  simp only [smul_apply, add_apply, map_smul, map_add, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, B, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.coe_restrict_scalarsL']
  module

end TauCeti
