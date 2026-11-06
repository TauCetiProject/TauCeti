/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Adjoints and compositions of integral operators on `L²`

Let `K : α → β → (F →L[𝕜] G)` be a kernel between Hilbert spaces whose operator-norm row and
column integrals are bounded, so that by Schur's test `TauCeti.integralOperatorLp K 2` is a bounded
operator `T : L²(ν; F) → L²(μ; G)`. This file identifies the Hilbert space adjoint of `T`, and the
composition of one such operator with the adjoint of another, as integral operators.

* The adjoint `T†` is the integral operator with the adjoint kernel `(y, x) ↦ (K x y)†`
  (`TauCeti.adjoint_integralOperatorLp`).
* For kernels `K₁ : α → β → (F →L[𝕜] G)` and `K₂ : α → γ → (E →L[𝕜] G)` with the same target
  space, `T₂† ∘ T₁` is the integral operator with the kernel
  `(z, y) ↦ ∫ x, (K₂ x z)† ∘ K₁ x y ∂μ`, whenever that kernel again has bounded row and column
  integrals (`TauCeti.adjoint_comp_integralOperatorLp`). Symmetrically, for kernels with the same
  source space, `T₁ ∘ T₂†` has the kernel `(x, z) ↦ ∫ y, K₁ x y ∘ (K₂ z y)† ∂ν`
  (`TauCeti.integralOperatorLp_comp_adjoint`).

The composed kernels are integrals of operators, not of their norms, so cancellation inside them
can make them much smaller than the products of `‖K₁‖` and `‖K₂‖`. Combined with Schur's test
`TauCeti.norm_integralOperatorLp_le`, these identities bound the two quantities `‖Tᵢ† ∘ Tⱼ‖` and
`‖Tᵢ ∘ Tⱼ†‖` entering the Cotlar–Stein almost-orthogonality lemma
`TauCeti.norm_sum_le_of_almost_orthogonal` in terms of the kernels of the pieces `Tᵢ`. This is
how the phase-space pieces of a pseudodifferential operator are shown to be almost orthogonal in
the proof of the Calderón–Vaillancourt theorem.

## Main declarations

* `TauCeti.integrable_inner_apply_kernel`, `TauCeti.inner_integralOperatorLp`: the pairing
  `⟪T u, v⟫` is the absolutely convergent double integral `∫∫ ⟪K x y (u y), v x⟫`.
* `TauCeti.adjoint_integralOperatorLp`: the adjoint is the integral operator of the adjoint kernel.
* `TauCeti.adjoint_comp_integralOperatorLp`, `TauCeti.integralOperatorLp_comp_adjoint`: the
  kernels of `T₂† ∘ T₁` and `T₁ ∘ T₂†`.

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VII, §2.
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.18.
-/

public section

noncomputable section

open MeasureTheory Function ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate

namespace TauCeti

variable {α β γ 𝕜 E F G : Type*} [RCLike 𝕜]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section AdjointKernel

variable [CompleteSpace F] [CompleteSpace G] {K : α → β → F →L[𝕜] G}

/-- The adjoint kernel `(y, x) ↦ (K x y)†` of an a.e. strongly measurable kernel is a.e. strongly
measurable for the swapped product measure. -/
theorem aestronglyMeasurable_uncurry_adjoint [SFinite ν]
    (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν)) :
    AEStronglyMeasurable (uncurry fun y x ↦ adjoint (K x y)) (ν.prod μ) :=
  (adjoint (𝕜 := 𝕜) (E := F) (F := G)).continuous.comp_aestronglyMeasurable hK.prod_swap

/-- Taking adjoints does not change the operator-norm integrals of a kernel. -/
theorem ae_lintegral_enorm_adjoint_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μX : Measure X} {μY : Measure Y} {k : X → Y → F →L[𝕜] G} {C : ℝ≥0∞}
    (h : ∀ᵐ x ∂μX, ∫⁻ y, ‖k x y‖ₑ ∂μY ≤ C) :
    ∀ᵐ x ∂μX, ∫⁻ y, ‖adjoint (k x y)‖ₑ ∂μY ≤ C := by
  simpa only [enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map] using h

end AdjointKernel

section Pairing

variable [SFinite μ] [SFinite ν] {K : α → β → F →L[𝕜] G}

/-- For a kernel with bounded row and column integrals and `u ∈ L²(ν)`, `v ∈ L²(μ)`, the function
`(x, y) ↦ ⟪K x y (u y), v x⟫` is integrable on `μ.prod ν`. -/
theorem integrable_inner_apply_kernel (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν))
    {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B)
    {u : β → F} {v : α → G} (hu : MemLp u 2 ν) (hv : MemLp v 2 μ) :
    Integrable (fun p : α × β ↦ ⟪K p.1 p.2 (u p.2), v p.1⟫) (μ.prod ν) := by
  refine ⟨(isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hK
    hu.aestronglyMeasurable.comp_snd).inner hv.aestronglyMeasurable.comp_fst, ?_⟩
  -- Bound `‖K‖ ‖u‖ ‖v‖ ≤ ‖K‖ ‖u‖ ^ 2 + ‖K‖ ‖v‖ ^ 2` and integrate each term by Tonelli.
  have hu2 : ∫⁻ y, ‖u y‖ₑ ^ 2 ∂ν < ∞ := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero (by simp) hu
  have hv2 : ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ < ∞ := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero (by simp) hv
  have hKm : AEMeasurable (fun p : α × β ↦ ‖K p.1 p.2‖ₑ) (μ.prod ν) := hK.enorm
  have hum : AEMeasurable (fun y ↦ ‖u y‖ₑ ^ 2) ν := hu.aestronglyMeasurable.enorm.pow_const 2
  have hvm : AEMeasurable (fun x ↦ ‖v x‖ₑ ^ 2) μ := hv.aestronglyMeasurable.enorm.pow_const 2
  have hKum : AEMeasurable (fun p : α × β ↦ ‖K p.1 p.2‖ₑ * ‖u p.2‖ₑ ^ 2) (μ.prod ν) :=
    hKm.mul hum.comp_snd
  -- The `u`-part, integrated first in `x`.
  have hU : ∫⁻ p : α × β, ‖K p.1 p.2‖ₑ * ‖u p.2‖ₑ ^ 2 ∂μ.prod ν ≤ B * ∫⁻ y, ‖u y‖ₑ ^ 2 ∂ν := by
    rw [lintegral_prod_symm _ hKum, ← lintegral_const_mul'' _ hum]
    refine lintegral_mono_ae ?_
    filter_upwards [hB] with y hy
    rw [lintegral_mul_const' _ _ (by finiteness)]
    gcongr
  -- The `v`-part, integrated first in `y`.
  have hV : ∫⁻ p : α × β, ‖K p.1 p.2‖ₑ * ‖v p.1‖ₑ ^ 2 ∂μ.prod ν ≤ A * ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ := by
    rw [lintegral_prod (fun p : α × β ↦ ‖K p.1 p.2‖ₑ * ‖v p.1‖ₑ ^ 2) (hKm.mul hvm.comp_fst),
      ← lintegral_const_mul'' _ hvm]
    refine lintegral_mono_ae ?_
    filter_upwards [hA] with x hx
    rw [lintegral_mul_const' _ _ (by finiteness)]
    gcongr
  calc ∫⁻ p, ‖⟪K p.1 p.2 (u p.2), v p.1⟫‖ₑ ∂μ.prod ν
      ≤ ∫⁻ p : α × β, ‖K p.1 p.2‖ₑ * ‖u p.2‖ₑ ^ 2 + ‖K p.1 p.2‖ₑ * ‖v p.1‖ₑ ^ 2 ∂μ.prod ν := by
        refine lintegral_mono fun p ↦ ?_
        calc ‖⟪K p.1 p.2 (u p.2), v p.1⟫‖ₑ ≤ ‖K p.1 p.2‖ₑ * ‖u p.2‖ₑ * ‖v p.1‖ₑ :=
              (enorm_inner_le_enorm _ _).trans (by gcongr; exact le_opENorm _ _)
          _ ≤ ‖K p.1 p.2‖ₑ * (‖u p.2‖ₑ ^ 2 + ‖v p.1‖ₑ ^ 2) := by
              rw [mul_assoc]
              gcongr
              rcases le_total ‖u p.2‖ₑ ‖v p.1‖ₑ with h | h
              · calc ‖u p.2‖ₑ * ‖v p.1‖ₑ ≤ ‖v p.1‖ₑ ^ 2 := by rw [sq]; gcongr
                  _ ≤ _ := le_add_self
              · calc ‖u p.2‖ₑ * ‖v p.1‖ₑ ≤ ‖u p.2‖ₑ ^ 2 := by rw [sq]; gcongr
                  _ ≤ _ := le_self_add
          _ = _ := mul_add _ _ _
    _ = ∫⁻ p : α × β, ‖K p.1 p.2‖ₑ * ‖u p.2‖ₑ ^ 2 ∂μ.prod ν +
          ∫⁻ p : α × β, ‖K p.1 p.2‖ₑ * ‖v p.1‖ₑ ^ 2 ∂μ.prod ν :=
        lintegral_add_left' hKum _
    _ < ∞ := ENNReal.add_lt_top.2
        ⟨hU.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu2),
          hV.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hv2)⟩

variable [CompleteSpace G] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G]

/-- The pairing of `T u` with `v` for the integral operator `T` with kernel `K` is the double
integral `∫∫ ⟪K x y (u y), v x⟫`, which converges absolutely by
`TauCeti.integrable_inner_apply_kernel`. -/
theorem inner_integralOperatorLp (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν))
    {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B)
    (u : Lp F 2 ν) (v : Lp G 2 μ) :
    ⟪integralOperatorLp K 2 hK hA hB u, v⟫ = ∫ p, ⟪K p.1 p.2 (u p.2), v p.1⟫ ∂μ.prod ν := by
  rw [MeasureTheory.L2.inner_def,
    integral_prod _ (integrable_inner_apply_kernel hK hA hB (Lp.memLp u) (Lp.memLp v))]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_integralOperatorLp (hK := hK) (hA := hA) (hB := hB) u,
    ae_integrable_apply_of_memLp hK (Lp.memLp u) one_le_two hA hB] with x hx hint
  rw [hx]
  simpa only [← integral_conj, inner_conj_symm] using
    (congrArg (conj : 𝕜 → 𝕜) (integral_inner hint (v x))).symm

end Pairing

section Adjoint

variable [SFinite μ] [SFinite ν] [CompleteSpace F] [CompleteSpace G] [NormedSpace ℝ F]
  [SMulCommClass ℝ 𝕜 F] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] {K : α → β → F →L[𝕜] G}

/-- The adjoint of the integral operator with kernel `K : α → β → (F →L[𝕜] G)` on `L²` is the
integral operator with the adjoint kernel `(y, x) ↦ (K x y)†`. The row and column bounds swap
roles. -/
theorem adjoint_integralOperatorLp (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν))
    {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B) :
    adjoint (integralOperatorLp K 2 hK hA hB) =
      integralOperatorLp (fun y x ↦ adjoint (K x y)) 2 (aestronglyMeasurable_uncurry_adjoint hK)
        (ae_lintegral_enorm_adjoint_le hB) (ae_lintegral_enorm_adjoint_le hA) := by
  refine ((eq_adjoint_iff _ _).2 fun v u ↦ ?_).symm
  rw [inner_integralOperatorLp, ← inner_conj_symm, inner_integralOperatorLp, ← integral_conj,
    ← integral_prod_swap]
  refine integral_congr_ae (.of_forall fun q ↦ ?_)
  simp only [Prod.fst_swap, Prod.snd_swap, adjoint_inner_left, inner_conj_symm]

end Adjoint

section Composition

variable [SFinite μ] [SFinite ν] [SFinite ρ] [CompleteSpace E] [CompleteSpace G]

section AdjointComp

variable {K₁ : α → β → F →L[𝕜] G} {K₂ : α → γ → E →L[𝕜] G}

/-- The integrand `((z, y), x) ↦ (K₂ x z)† ∘ K₁ x y` of the kernel of `T₂† ∘ T₁` is a.e.
strongly measurable. -/
private theorem aestronglyMeasurable_adjoint_comp
    (hK₁ : AEStronglyMeasurable (uncurry K₁) (μ.prod ν))
    (hK₂ : AEStronglyMeasurable (uncurry K₂) (μ.prod ρ)) :
    AEStronglyMeasurable (fun p : (γ × β) × α ↦ adjoint (K₂ p.2 p.1.1) ∘L K₁ p.2 p.1.2)
      ((ρ.prod ν).prod μ) := by
  have h₁ : AEStronglyMeasurable (fun p : (γ × β) × α ↦ K₁ p.2 p.1.2) ((ρ.prod ν).prod μ) :=
    (hK₁.prod_swap.comp_snd (μ := ρ)).comp_measurePreserving (measurePreserving_prodAssoc ρ ν μ)
  have h₂ : AEStronglyMeasurable (fun p : (γ × β) × α ↦ adjoint (K₂ p.2 p.1.1))
      ((ρ.prod ν).prod μ) :=
    (((aestronglyMeasurable_uncurry_adjoint hK₂).comp_fst (ν := ν)).comp_measurePreserving
      (MeasurePreserving.symm _ (measurePreserving_prodAssoc ρ μ ν))).comp_measurePreserving
      (((MeasurePreserving.id ρ).prod Measure.measurePreserving_swap).comp
        (measurePreserving_prodAssoc ρ ν μ))
  exact isBoundedBilinearMap_comp.continuous.comp_aestronglyMeasurable₂ h₂ h₁

/-- For `u ∈ L²(ν)`, the function `x ↦ ∫⁻ y, ‖K₁ x y‖ ‖u y‖` is in `L²(μ)` by Schur's test, and
then so is `z ↦ ∫⁻ x, ‖(K₂ x z)†‖ ∫⁻ y, ‖K₁ x y‖ ‖u y‖` in `L²(ρ)`. In particular the latter is
finite almost everywhere. -/
private theorem ae_lintegral_enorm_adjoint_mul_lt_top
    (hK₁ : AEStronglyMeasurable (uncurry K₁) (μ.prod ν)) {A₁ B₁ : ℝ≥0}
    (hA₁ : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₁ x y‖ₑ ∂ν ≤ A₁) (hB₁ : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₁ x y‖ₑ ∂μ ≤ B₁)
    (hK₂ : AEStronglyMeasurable (uncurry K₂) (μ.prod ρ)) {A₂ B₂ : ℝ≥0}
    (hA₂ : ∀ᵐ x ∂μ, ∫⁻ z, ‖K₂ x z‖ₑ ∂ρ ≤ A₂) (hB₂ : ∀ᵐ z ∂ρ, ∫⁻ x, ‖K₂ x z‖ₑ ∂μ ≤ B₂)
    {u : β → F} (hu : MemLp u 2 ν) :
    ∀ᵐ z ∂ρ, ∫⁻ x, ‖adjoint (K₂ x z)‖ₑ * ∫⁻ y, ‖K₁ x y‖ₑ * ‖u y‖ₑ ∂ν ∂μ < ∞ := by
  have hum := hu.aestronglyMeasurable
  have hSm : AEMeasurable (fun x ↦ ∫⁻ y, ‖K₁ x y‖ₑ * ‖u y‖ₑ ∂ν) μ :=
    (hK₁.enorm.mul hum.enorm.comp_snd).lintegral_prod_right'
  have hS : eLpNorm (fun x ↦ ∫⁻ y, ‖K₁ x y‖ₑ * ‖u y‖ₑ ∂ν) 2 μ < ∞ := by
    refine (eLpNorm_lintegral_mul_le (k := fun x y ↦ ‖K₁ x y‖ₑ) hK₁.enorm hum.enorm one_le_two
      hA₁ hB₁).trans_lt ?_
    rw [eLpNorm_enorm _ hum]
    exact ENNReal.mul_lt_top (rpow_one_sub_toReal_inv_mul_rpow_toReal_inv_lt_top one_le_two A₁ B₁)
      hu.eLpNorm_lt_top
  have hfin : MemLp (fun z ↦ ∫⁻ x, ‖adjoint (K₂ x z)‖ₑ * ∫⁻ y, ‖K₁ x y‖ₑ * ‖u y‖ₑ ∂ν ∂μ) 2 ρ :=
    (eLpNorm_lintegral_mul_le (aestronglyMeasurable_uncurry_adjoint hK₂).enorm hSm one_le_two
      (ae_lintegral_enorm_adjoint_le hB₂) (ae_lintegral_enorm_adjoint_le hA₂)).trans_lt
      (ENNReal.mul_lt_top (rpow_one_sub_toReal_inv_mul_rpow_toReal_inv_lt_top one_le_two B₂ A₂) hS)
  simpa only [enorm_eq_self] using hfin.ae_enorm_lt_top two_ne_zero

variable [NormedSpace ℝ E]

/-- The kernel `(z, y) ↦ ∫ x, (K₂ x z)† ∘ K₁ x y ∂μ` of `T₂† ∘ T₁` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_integral_adjoint_comp
    (hK₁ : AEStronglyMeasurable (uncurry K₁) (μ.prod ν))
    (hK₂ : AEStronglyMeasurable (uncurry K₂) (μ.prod ρ)) :
    AEStronglyMeasurable (uncurry fun z y ↦ ∫ x, adjoint (K₂ x z) ∘L K₁ x y ∂μ) (ρ.prod ν) :=
  (aestronglyMeasurable_adjoint_comp hK₁ hK₂).integral_prod_right'

variable [NormedSpace ℝ G]

omit [MeasurableSpace γ] in
/-- Fubini's theorem for `(x, y) ↦ (K₂ x z)† (K₁ x y (u y))` at a single `z` at which the
dominating integral `∫⁻ x, ‖(K₂ x z)†‖ ∫⁻ y, ‖K₁ x y‖ ‖u y‖` is finite: integrating first in `x`
or first in `y` gives the same result. -/
private theorem integral_adjoint_comp_apply_of_lt_top {z : γ} {u : β → F}
    (hint : ∀ᵐ x ∂μ, Integrable (fun y ↦ K₁ x y (u y)) ν)
    (hΦ : AEStronglyMeasurable (fun q : α × β ↦ adjoint (K₂ q.1 z) (K₁ q.1 q.2 (u q.2)))
      (μ.prod ν))
    (hN : AEMeasurable (fun q : α × β ↦ ‖adjoint (K₂ q.1 z)‖ₑ * (‖K₁ q.1 q.2‖ₑ * ‖u q.2‖ₑ))
      (μ.prod ν))
    (hΨ : ∀ᵐ y ∂ν, AEStronglyMeasurable (fun x ↦ adjoint (K₂ x z) ∘L K₁ x y) μ)
    (hH : ∫⁻ x, ‖adjoint (K₂ x z)‖ₑ * ∫⁻ y, ‖K₁ x y‖ₑ * ‖u y‖ₑ ∂ν ∂μ < ∞) :
    ∫ y, (∫ x, adjoint (K₂ x z) ∘L K₁ x y ∂μ) (u y) ∂ν =
      ∫ x, adjoint (K₂ x z) (∫ y, K₁ x y (u y) ∂ν) ∂μ := by
  have hlin : ∫⁻ q : α × β, ‖adjoint (K₂ q.1 z)‖ₑ * (‖K₁ q.1 q.2‖ₑ * ‖u q.2‖ₑ) ∂μ.prod ν =
      ∫⁻ x, ‖adjoint (K₂ x z)‖ₑ * ∫⁻ y, ‖K₁ x y‖ₑ * ‖u y‖ₑ ∂ν ∂μ := by
    rw [lintegral_prod _ hN]
    exact lintegral_congr fun x ↦ lintegral_const_mul' ‖adjoint (K₂ x z)‖ₑ _ enorm_ne_top
  -- The integrand is integrable on `μ × ν`.
  have hprod : Integrable (uncurry fun x y ↦ adjoint (K₂ x z) (K₁ x y (u y))) (μ.prod ν) := by
    refine ⟨hΦ, hasFiniteIntegral_iff_enorm.2 ?_⟩
    refine (lintegral_mono fun q ↦ ?_).trans_lt (hlin ▸ hH)
    exact (le_opENorm _ _).trans (by gcongr; exact le_opENorm _ _)
  -- For almost every `y` with `u y ≠ 0`, the composed kernel is integrable in `x`.
  have hfin : ∀ᵐ y ∂ν, u y ≠ 0 → ∫⁻ x, ‖adjoint (K₂ x z)‖ₑ * ‖K₁ x y‖ₑ ∂μ < ∞ := by
    filter_upwards [ae_lt_top' hN.lintegral_prod_left'
      ((lintegral_prod_symm _ hN).symm.trans hlin ▸ hH.ne)] with y hy huy
    simp_rw [← mul_assoc] at hy
    rw [lintegral_mul_const' _ _ enorm_ne_top] at hy
    exact (ENNReal.mul_lt_top_iff.1 hy).elim And.left fun h ↦ h.elim (fun h ↦ h ▸ by simp)
      fun h ↦ absurd (enorm_eq_zero.1 h) huy
  calc ∫ y, (∫ x, adjoint (K₂ x z) ∘L K₁ x y ∂μ) (u y) ∂ν
      = ∫ y, ∫ x, adjoint (K₂ x z) (K₁ x y (u y)) ∂μ ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hfin, hΨ] with y hy hΨy
        by_cases huy : u y = 0
        · simp [huy]
        · exact integral_apply ⟨hΨy, hasFiniteIntegral_iff_enorm.2 <|
            (lintegral_mono fun x ↦ opENorm_comp_le _ _).trans_lt (hy huy)⟩ (u y)
    _ = ∫ x, ∫ y, adjoint (K₂ x z) (K₁ x y (u y)) ∂ν ∂μ := (integral_integral_swap hprod).symm
    _ = ∫ x, adjoint (K₂ x z) (∫ y, K₁ x y (u y) ∂ν) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hint] with x hx
        exact (adjoint (K₂ x z)).integral_comp_comm hx

/-- The pointwise identity behind `TauCeti.adjoint_comp_integralOperatorLp`: for `u ∈ L²(ν)` and
almost every `z`, integrating `(K₂ x z)† (K₁ x y (u y))` first in `x` or first in `y` gives the
same result. -/
private theorem ae_integral_adjoint_comp_apply
    (hK₁ : AEStronglyMeasurable (uncurry K₁) (μ.prod ν)) {A₁ B₁ : ℝ≥0}
    (hA₁ : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₁ x y‖ₑ ∂ν ≤ A₁) (hB₁ : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₁ x y‖ₑ ∂μ ≤ B₁)
    (hK₂ : AEStronglyMeasurable (uncurry K₂) (μ.prod ρ)) {A₂ B₂ : ℝ≥0}
    (hA₂ : ∀ᵐ x ∂μ, ∫⁻ z, ‖K₂ x z‖ₑ ∂ρ ≤ A₂) (hB₂ : ∀ᵐ z ∂ρ, ∫⁻ x, ‖K₂ x z‖ₑ ∂μ ≤ B₂)
    {u : β → F} (hu : MemLp u 2 ν) :
    ∀ᵐ z ∂ρ, ∫ y, (∫ x, adjoint (K₂ x z) ∘L K₁ x y ∂μ) (u y) ∂ν =
      ∫ x, adjoint (K₂ x z) (∫ y, K₁ x y (u y) ∂ν) ∂μ := by
  have hum := hu.aestronglyMeasurable
  -- Joint measurability on `ρ × (μ × ν)`, to be sliced at almost every `z`.
  have h₂ : AEStronglyMeasurable (fun p : γ × α × β ↦ adjoint (K₂ p.2.1 p.1))
      (ρ.prod (μ.prod ν)) :=
    ((aestronglyMeasurable_uncurry_adjoint hK₂).comp_fst (ν := ν)).comp_measurePreserving
      (MeasurePreserving.symm _ (measurePreserving_prodAssoc ρ μ ν))
  have h₁ : AEStronglyMeasurable (fun p : γ × α × β ↦ K₁ p.2.1 p.2.2 (u p.2.2))
      (ρ.prod (μ.prod ν)) :=
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hK₁ hum.comp_snd).comp_snd
  have hN : AEStronglyMeasurable
      (fun p : γ × α × β ↦ ‖adjoint (K₂ p.2.1 p.1)‖ₑ * (‖K₁ p.2.1 p.2.2‖ₑ * ‖u p.2.2‖ₑ))
      (ρ.prod (μ.prod ν)) :=
    (h₂.enorm.mul ((hK₁.enorm.mul hum.enorm.comp_snd).comp_snd)).aestronglyMeasurable
  filter_upwards [ae_lintegral_enorm_adjoint_mul_lt_top hK₁ hA₁ hB₁ hK₂ hA₂ hB₂ hu,
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ h₂ h₁).prodMk_left,
    hN.prodMk_left,
    Measure.ae_ae_of_ae_prod (aestronglyMeasurable_adjoint_comp hK₁ hK₂).prodMk_left]
    with z hH hΦ hNz hΨ
  exact integral_adjoint_comp_apply_of_lt_top
    (ae_integrable_apply_of_memLp hK₁ hu one_le_two hA₁ hB₁) hΦ hNz.aemeasurable hΨ hH

variable [SMulCommClass ℝ 𝕜 E] [SMulCommClass ℝ 𝕜 G]

/-- For kernels `K₁ : α → β → (F →L[𝕜] G)` and `K₂ : α → γ → (E →L[𝕜] G)` with bounded row and
column integrals, the composition `T₂† ∘ T₁` of the integral operators on `L²` is the integral
operator with the kernel `(z, y) ↦ ∫ x, (K₂ x z)† ∘ K₁ x y ∂μ`, provided this kernel again has
bounded row and column integrals. In particular `‖T₂† ∘ T₁‖` is bounded by Schur's test for this
kernel, which can be much smaller than the product of the bounds for `K₁` and `K₂`. -/
theorem adjoint_comp_integralOperatorLp
    (hK₁ : AEStronglyMeasurable (uncurry K₁) (μ.prod ν)) {A₁ B₁ : ℝ≥0}
    (hA₁ : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₁ x y‖ₑ ∂ν ≤ A₁) (hB₁ : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₁ x y‖ₑ ∂μ ≤ B₁)
    (hK₂ : AEStronglyMeasurable (uncurry K₂) (μ.prod ρ)) {A₂ B₂ : ℝ≥0}
    (hA₂ : ∀ᵐ x ∂μ, ∫⁻ z, ‖K₂ x z‖ₑ ∂ρ ≤ A₂) (hB₂ : ∀ᵐ z ∂ρ, ∫⁻ x, ‖K₂ x z‖ₑ ∂μ ≤ B₂)
    {A B : ℝ≥0} (hA : ∀ᵐ z ∂ρ, ∫⁻ y, ‖∫ x, adjoint (K₂ x z) ∘L K₁ x y ∂μ‖ₑ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ z, ‖∫ x, adjoint (K₂ x z) ∘L K₁ x y ∂μ‖ₑ ∂ρ ≤ B) :
    adjoint (integralOperatorLp K₂ 2 hK₂ hA₂ hB₂) ∘L integralOperatorLp K₁ 2 hK₁ hA₁ hB₁ =
      integralOperatorLp (fun z y ↦ ∫ x, adjoint (K₂ x z) ∘L K₁ x y ∂μ) 2
        (aestronglyMeasurable_integral_adjoint_comp hK₁ hK₂) hA hB := by
  refine ContinuousLinearMap.ext fun u ↦ ?_
  rw [ContinuousLinearMap.comp_apply, adjoint_integralOperatorLp hK₂ hA₂ hB₂, eq_comm,
    integralOperatorLp_eq_iff]
  filter_upwards [coeFn_integralOperatorLp (hK := aestronglyMeasurable_uncurry_adjoint hK₂)
      (hA := ae_lintegral_enorm_adjoint_le hB₂) (hB := ae_lintegral_enorm_adjoint_le hA₂)
      (integralOperatorLp K₁ 2 hK₁ hA₁ hB₁ u),
    ae_integral_adjoint_comp_apply hK₁ hA₁ hB₁ hK₂ hA₂ hB₂ (Lp.memLp u)] with z hz hkey
  rw [hz, hkey]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_integralOperatorLp (hK := hK₁) (hA := hA₁) (hB := hB₁) u] with x hx
  rw [hx]

end AdjointComp

section CompAdjoint

variable [CompleteSpace F] [NormedSpace ℝ G] {K₁ : α → β → F →L[𝕜] G} {K₂ : γ → β → F →L[𝕜] E}

/-- The kernel `(x, z) ↦ ∫ y, K₁ x y ∘ (K₂ z y)† ∂ν` of `T₁ ∘ T₂†` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_integral_comp_adjoint
    (hK₁ : AEStronglyMeasurable (uncurry K₁) (μ.prod ν))
    (hK₂ : AEStronglyMeasurable (uncurry K₂) (ρ.prod ν)) :
    AEStronglyMeasurable (uncurry fun x z ↦ ∫ y, K₁ x y ∘L adjoint (K₂ z y) ∂ν) (μ.prod ρ) := by
  simpa only [adjoint_adjoint] using aestronglyMeasurable_integral_adjoint_comp
    (aestronglyMeasurable_uncurry_adjoint hK₂) (aestronglyMeasurable_uncurry_adjoint hK₁)

variable [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E] [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F]
  [SMulCommClass ℝ 𝕜 G]

/-- For kernels `K₁ : α → β → (F →L[𝕜] G)` and `K₂ : γ → β → (F →L[𝕜] E)` with bounded row and
column integrals, the composition `T₁ ∘ T₂†` of the integral operators on `L²` is the integral
operator with the kernel `(x, z) ↦ ∫ y, K₁ x y ∘ (K₂ z y)† ∂ν`, provided this kernel again has
bounded row and column integrals. -/
theorem integralOperatorLp_comp_adjoint
    (hK₁ : AEStronglyMeasurable (uncurry K₁) (μ.prod ν)) {A₁ B₁ : ℝ≥0}
    (hA₁ : ∀ᵐ x ∂μ, ∫⁻ y, ‖K₁ x y‖ₑ ∂ν ≤ A₁) (hB₁ : ∀ᵐ y ∂ν, ∫⁻ x, ‖K₁ x y‖ₑ ∂μ ≤ B₁)
    (hK₂ : AEStronglyMeasurable (uncurry K₂) (ρ.prod ν)) {A₂ B₂ : ℝ≥0}
    (hA₂ : ∀ᵐ z ∂ρ, ∫⁻ y, ‖K₂ z y‖ₑ ∂ν ≤ A₂) (hB₂ : ∀ᵐ y ∂ν, ∫⁻ z, ‖K₂ z y‖ₑ ∂ρ ≤ B₂)
    {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ z, ‖∫ y, K₁ x y ∘L adjoint (K₂ z y) ∂ν‖ₑ ∂ρ ≤ A)
    (hB : ∀ᵐ z ∂ρ, ∫⁻ x, ‖∫ y, K₁ x y ∘L adjoint (K₂ z y) ∂ν‖ₑ ∂μ ≤ B) :
    integralOperatorLp K₁ 2 hK₁ hA₁ hB₁ ∘L adjoint (integralOperatorLp K₂ 2 hK₂ hA₂ hB₂) =
      integralOperatorLp (fun x z ↦ ∫ y, K₁ x y ∘L adjoint (K₂ z y) ∂ν) 2
        (aestronglyMeasurable_integral_comp_adjoint hK₁ hK₂) hA hB := by
  have h₁ : integralOperatorLp K₁ 2 hK₁ hA₁ hB₁ =
      adjoint (integralOperatorLp (fun y x ↦ adjoint (K₁ x y)) 2
        (aestronglyMeasurable_uncurry_adjoint hK₁) (ae_lintegral_enorm_adjoint_le hB₁)
        (ae_lintegral_enorm_adjoint_le hA₁)) := by
    rw [← adjoint_integralOperatorLp, adjoint_adjoint]
  rw [h₁, adjoint_integralOperatorLp hK₂ hA₂ hB₂, adjoint_comp_integralOperatorLp _ _ _ _ _ _
    (by simpa only [adjoint_adjoint] using hA) (by simpa only [adjoint_adjoint] using hB)]
  simp only [adjoint_adjoint]

end CompAdjoint

end Composition

end TauCeti
