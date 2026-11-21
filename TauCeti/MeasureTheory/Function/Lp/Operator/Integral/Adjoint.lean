/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Basic
import TauCeti.MeasureTheory.Function.L1Space.Integrable
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
* More generally, on a proper metric measure space, let `T : L²(V; H) → L²(V; K)` be a bounded
  operator that is integration against a kernel `k` only away from the support of its argument.
  If `k` is bounded away from the diagonal, then `T†` is integration against the adjoint kernel
  `(x, z) ↦ (k z x)†` away from the support of its argument
  (`ContinuousLinearMap.ae_adjoint_apply_eq_integral`). No integral bound on `k` is needed, so
  this applies to singular integral operators.

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
* `ContinuousLinearMap.ae_adjoint_apply_eq_integral`: the kernel of the adjoint of an operator
  given by a kernel only away from the support of its argument.

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
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section AdjointKernel

variable [InnerProductSpace 𝕜 F] [CompleteSpace F] [CompleteSpace G] {K : α → β → F →L[𝕜] G}

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
  simpa only [eNorm_eq_nnNorm, LinearIsometryEquiv.nnNorm_map] using h

end AdjointKernel

section Pairing

variable [NormedSpace 𝕜 F] [SFinite μ] [SFinite ν] {K : α → β → F →L[𝕜] G}

/-- For a kernel with bounded row and column integrals and `u ∈ L²(ν)`, `v ∈ L²(μ)`, the function
`(x, y) ↦ ⟪K x y (u y), v x⟫` is integrable on `μ.prod ν`. -/
theorem integrable_inner_apply_kernel (hK : AEStronglyMeasurable (uncurry K) (μ.prod ν))
    {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ B)
    {u : β → F} {v : α → G} (hu : MemLp u 2 ν) (hv : MemLp v 2 μ) :
    Integrable (fun p : α × β ↦ ⟪K p.1 p.2 (u p.2), v p.1⟫) (μ.prod ν) := by
  refine ⟨(isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hK
    hu.aestronglyMeasurable.comp_snd).inner hv.aestronglyMeasurable.comp_fst, ?_⟩
  -- Bound the integrand by `‖v x‖ * ‖K x y‖ ‖u y‖`; integrating in `y` gives `‖v x‖ * S x`, where
  -- `S ∈ L²` by Schur's test, and Hölder's inequality finishes.
  have hS : MemLp (fun x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) 2 μ :=
    memLp_lintegral_mul (k := fun x y ↦ ‖K x y‖ₑ) hK.eNorm hu.eNorm one_le_two hA hB
  calc ∫⁻ p, ‖⟪K p.1 p.2 (u p.2), v p.1⟫‖ₑ ∂μ.prod ν
      ≤ ∫⁻ p : α × β, ‖v p.1‖ₑ * (‖K p.1 p.2‖ₑ * ‖u p.2‖ₑ) ∂μ.prod ν :=
        lintegral_mono fun p ↦ (eNorm_inner_le_eNorm _ _).trans
          (by rw [mul_comm]; gcongr; exact le_opENorm _ _)
    _ = ∫⁻ x, ‖v x‖ₑ * ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν ∂μ := by
        rw [lintegral_prod (fun p : α × β ↦ ‖v p.1‖ₑ * (‖K p.1 p.2‖ₑ * ‖u p.2‖ₑ))
          (hv.aestronglyMeasurable.eNorm.comp_fst.mul
            (hK.eNorm.mul hu.aestronglyMeasurable.eNorm.comp_snd))]
        exact lintegral_congr fun x ↦ lintegral_const_mul' ‖v x‖ₑ _ eNorm_ne_top
    _ ≤ eLpNorm (‖v ·‖ₑ) 2 μ * eLpNorm (fun x ↦ ∫⁻ y, ‖K x y‖ₑ * ‖u y‖ₑ ∂ν) 2 μ := by
        refine Eq.trans_le ?_ (eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal (p := 2) (q := 2) (r := 1)
          hv.eNorm.aestronglyMeasurable hS.aestronglyMeasurable)
        rw [eLpNorm_one_eq_lintegral_eNorm (hv.aestronglyMeasurable.eNorm.mul
          hS.aestronglyMeasurable.aemeasurable).aestronglyMeasurable]
        simp only [Pi.mul_apply, eNorm_eq_self]
    _ < ∞ := ENNReal.mul_lt_top hv.eNorm.eLpNorm_lt_top hS.eLpNorm_lt_top

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

variable [InnerProductSpace 𝕜 F] [SFinite μ] [SFinite ν] [CompleteSpace F] [CompleteSpace G]
  [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G]
  {K : α → β → F →L[𝕜] G}

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

variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [SFinite μ] [SFinite ν] [SFinite ρ]
  [CompleteSpace E] [CompleteSpace G]

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
  have hS : MemLp (fun x ↦ ∫⁻ y, ‖K₁ x y‖ₑ * ‖u y‖ₑ ∂ν) 2 μ :=
    memLp_lintegral_mul (k := fun x y ↦ ‖K₁ x y‖ₑ) hK₁.eNorm hu.eNorm one_le_two hA₁ hB₁
  have hfin : MemLp (fun z ↦ ∫⁻ x, ‖adjoint (K₂ x z)‖ₑ * ∫⁻ y, ‖K₁ x y‖ₑ * ‖u y‖ₑ ∂ν ∂μ) 2 ρ :=
    memLp_lintegral_mul (aestronglyMeasurable_uncurry_adjoint hK₂).eNorm hS one_le_two
      (ae_lintegral_enorm_adjoint_le hB₂) (ae_lintegral_enorm_adjoint_le hA₂)
  simpa only [eNorm_eq_self] using hfin.ae_enorm_lt_top two_ne_zero

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
    exact lintegral_congr fun x ↦ lintegral_const_mul' ‖adjoint (K₂ x z)‖ₑ _ eNorm_ne_top
  -- The integrand is integrable on `μ × ν`.
  have hprod : Integrable (uncurry fun x y ↦ adjoint (K₂ x z) (K₁ x y (u y))) (μ.prod ν) := by
    refine ⟨hΦ, hasFiniteIntegral_iff_eNorm.2 ?_⟩
    refine (lintegral_mono fun q ↦ ?_).trans_lt (hlin ▸ hH)
    exact (le_opENorm _ _).trans (by gcongr; exact le_opENorm _ _)
  -- For almost every `y` with `u y ≠ 0`, the composed kernel is integrable in `x`.
  have hfin : ∀ᵐ y ∂ν, u y ≠ 0 → ∫⁻ x, ‖adjoint (K₂ x z)‖ₑ * ‖K₁ x y‖ₑ ∂μ < ∞ := by
    filter_upwards [ae_lt_top' hN.lintegral_prod_left'
      ((lintegral_prod_symm _ hN).symm.trans hlin ▸ hH.ne)] with y hy huy
    simp_rw [← mul_assoc] at hy
    rw [lintegral_mul_const' _ _ eNorm_ne_top] at hy
    exact (ENNReal.mul_lt_top_iff.1 hy).elim And.left fun h ↦ h.elim (fun h ↦ h ▸ by simp)
      fun h ↦ absurd (eNorm_eq_zero.1 h) huy
  calc ∫ y, (∫ x, adjoint (K₂ x z) ∘L K₁ x y ∂μ) (u y) ∂ν
      = ∫ y, ∫ x, adjoint (K₂ x z) (K₁ x y (u y)) ∂μ ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hfin, hΨ] with y hy hΨy
        by_cases huy : u y = 0
        · simp [huy]
        · exact integral_apply ⟨hΨy, hasFiniteIntegral_iff_eNorm.2 <|
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
    (h₂.eNorm.mul ((hK₁.eNorm.mul hum.eNorm.comp_snd).comp_snd)).aestronglyMeasurable
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

/-! ### Kernels known off the support

The rest of the file concerns a bounded operator `T` on `L²` of a proper metric measure space that
is integration against a kernel `k` only away from the support of its argument, as singular
integral operators are. The kernel need not satisfy any integral bound, only boundedness away from
the diagonal. -/

namespace TauCeti

section OffSupport

open Metric Set
open scoped InnerProductSpace

variable {𝕜 α β H K : Type*} [RCLike 𝕜] [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- The integrand `⟪g x, k x y (φ y)⟫` of the double integral pairing `g` with `T φ` is integrable
on the product when `g` and `φ` are integrable and vanish outside sets on whose product `k` is
bounded. This is the counterpart of `TauCeti.integrable_inner_apply_kernel` for kernels bounded
on the product of the supports rather than having bounded row and column integrals. -/
theorem integrable_inner_apply_kernel_of_norm_le {k : α → β → H →L[𝕜] K}
    (hkm : AEStronglyMeasurable (uncurry k) (μ.prod ν)) {s : Set α} {t : Set β} {M : ℝ}
    (hM : ∀ x ∈ s, ∀ y ∈ t, ‖k x y‖ ≤ M) {g : α → K} (hgi : Integrable g μ)
    (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0) {φ : β → H} (hφi : Integrable φ ν)
    (hφ : ∀ᵐ y ∂ν, y ∉ t → φ y = 0) :
    Integrable (fun p : α × β ↦ ⟪g p.1, k p.1 p.2 (φ p.2)⟫_𝕜) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : α × β ↦ k p.1 p.2 (φ p.2)) (μ.prod ν) :=
    (isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
      (hkm.prodMk
        (hφi.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
  refine ((hgi.norm.mul_prod hφi.norm).const_mul M).mono'
    ((hgi.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).inner hm) ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hg,
    Measure.quasiMeasurePreserving_snd.ae hφ] with p hp₁ hp₂
  by_cases h₁ : p.1 ∈ s
  · by_cases h₂ : p.2 ∈ t
    · calc ‖⟪g p.1, k p.1 p.2 (φ p.2)⟫_𝕜‖ ≤ ‖g p.1‖ * (‖k p.1 p.2‖ * ‖φ p.2‖) :=
            (norm_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _))
        _ ≤ ‖g p.1‖ * (M * ‖φ p.2‖) := by
            gcongr
            exact hM _ h₁ _ h₂
        _ = M * (‖g p.1‖ * ‖φ p.2‖) := by ring
    · simp [hp₂ h₂]
  · simp [hp₁ h₁]

end OffSupport

end TauCeti

namespace ContinuousLinearMap

open Metric Set Filter
open scoped InnerProductSpace

variable {𝕜 V H K : Type*} [RCLike 𝕜] [MetricSpace V] [ProperSpace V] [MeasurableSpace V]
  [BorelSpace V] {μ : Measure V} [IsFiniteMeasureOnCompacts μ]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K] [NormedSpace ℝ K]

omit [BorelSpace V] in
/-- The pairing identity behind `ContinuousLinearMap.ae_adjoint_apply_eq_integral`: against a test
function `φ` vanishing outside a compact set `t` disjoint from the compact set `s` outside which
`g` vanishes, `T† g` pairs like the integral of the transposed kernel. -/
private theorem integral_inner_adjoint_apply_eq (T : Lp H 2 μ →L[𝕜] Lp K 2 μ)
    {k : V → V → H →L[𝕜] K} (hkm : StronglyMeasurable (Function.uncurry k))
    (hrep : ∀ (f : Lp H 2 μ) (s : Set V), IsCompact s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = ∫ z, k x z (f z) ∂μ)
    {s t : Set V} (hs : IsCompact s) (ht : IsCompact t) (hst : Disjoint s t) {M : ℝ}
    (hM : ∀ x ∈ s, ∀ y ∈ t, ‖k x y‖ ≤ M) {g : Lp K 2 μ} (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0)
    {φ : Lp H 2 μ} (hφ : ∀ᵐ x ∂μ, x ∉ t → φ x = 0) :
    ∫ y, ⟪adjoint T g y, φ y⟫_𝕜 ∂μ = ∫ y, ⟪∫ z, adjoint (k z y) (g z) ∂μ, φ y⟫_𝕜 ∂μ := by
  have hgi := (Lp.memLp g).integrable_of_ae_notMem_eq_zero one_le_two hs.measure_lt_top.ne hg
  have hφi := (Lp.memLp φ).integrable_of_ae_notMem_eq_zero one_le_two ht.measure_lt_top.ne hφ
  calc ∫ y, ⟪adjoint T g y, φ y⟫_𝕜 ∂μ = ⟪adjoint T g, φ⟫_𝕜 := (L2.inner_def _ _).symm
    _ = ⟪g, T φ⟫_𝕜 := adjoint_inner_left _ _ _
    _ = ∫ z, ⟪g z, T φ z⟫_𝕜 ∂μ := L2.inner_def _ _
    _ = ∫ z, ∫ y, ⟪g z, k z y (φ y)⟫_𝕜 ∂μ ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hg, hrep φ t ht hφ] with z hgz hTz
      by_cases hz : z ∈ s
      · rw [hTz (disjoint_left.1 hst hz)]
        exact (integral_inner (hφi.apply_of_norm_le
          (hkm.comp_measurable measurable_prodMk_left).aestronglyMeasurable (hM z hz) hφ)
          (g z)).symm
      · simp [hgz hz]
    _ = ∫ y, ∫ z, ⟪g z, k z y (φ y)⟫_𝕜 ∂μ ∂μ := integral_integral_swap
      (TauCeti.integrable_inner_apply_kernel_of_norm_le hkm.aestronglyMeasurable hM hgi hg hφi hφ)
    _ = ∫ y, ⟪∫ z, adjoint (k z y) (g z) ∂μ, φ y⟫_𝕜 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hφ] with y hy
      by_cases hyt : y ∈ t
      · have hint : Integrable (fun z ↦ adjoint (k z y) (g z)) μ :=
          hgi.apply_of_norm_le
            ((adjoint : (H →L[𝕜] K) ≃ₗᵢ⋆[𝕜] (K →L[𝕜] H)).continuous.comp_stronglyMeasurable
              (hkm.comp_measurable measurable_prodMk_right)).aestronglyMeasurable
            (fun z hz ↦ (LinearIsometryEquiv.norm_map _ _).trans_le (hM z hz y hyt)) hg
        simp_rw [← adjoint_inner_left (k _ y)]
        rw [← inner_conj_symm, ← integral_inner hint, ← integral_conj]
        simp_rw [inner_conj_symm]
      · simp [hy hyt]

omit [NormedSpace ℝ K] in
/-- On a compact set `t` such that `k` is bounded on `s × t`, where `g` vanishes outside `s`, the
transposed kernel integral `x ↦ ∫ (k z x)† (g z) dz` is bounded, so its restriction to `t` lies in
`L²`. -/
private theorem memLp_indicator_integral_adjoint_apply {k : V → V → H →L[𝕜] K}
    (hkm : StronglyMeasurable (Function.uncurry k)) {s t : Set V} (hs : IsCompact s)
    (ht : IsCompact t) {M : ℝ} (hM : ∀ x ∈ s, ∀ y ∈ t, ‖k x y‖ ≤ M) {g : Lp K 2 μ}
    (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0) :
    MemLp (t.indicator fun x ↦ ∫ z, adjoint (k z x) (g z) ∂μ) 2 μ := by
  have : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.2 ht.measure_lt_top.ne
  refine (memLp_indicator_iff_restrict ht.measurableSet.nullMeasurableSet).2 ?_
  refine MemLp.of_bound (C := M * ∫ z, ‖g z‖ ∂μ) (AEStronglyMeasurable.restrict ?_)
    ((ae_restrict_iff' ht.measurableSet).2 (.of_forall fun x hx ↦ ?_))
  · exact AEStronglyMeasurable.integral_prod_right'
      (f := fun p : V × V ↦ adjoint (k p.2 p.1) (g p.2))
      ((isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
        (((adjoint : (H →L[𝕜] K) ≃ₗᵢ⋆[𝕜] (K →L[𝕜] H)).continuous.comp_stronglyMeasurable
          (hkm.comp_measurable measurable_swap)).aestronglyMeasurable.prodMk
          ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_snd)))
  · rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le
      (((Lp.memLp g).integrable_of_ae_notMem_eq_zero one_le_two hs.measure_lt_top.ne
        hg).norm.const_mul M) ?_
    filter_upwards [hg] with z hz
    by_cases hzs : z ∈ s
    · refine (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact (LinearIsometryEquiv.norm_map _ _).trans_le (hM z hzs x hx)
    · simp [hz hzs]

/-- The local form of `ContinuousLinearMap.ae_adjoint_apply_eq_integral`: the identity holds almost
everywhere on every compact set `t` disjoint from `s`. -/
private theorem ae_adjoint_apply_eq_integral_of_disjoint (T : Lp H 2 μ →L[𝕜] Lp K 2 μ)
    {k : V → V → H →L[𝕜] K} (hkm : StronglyMeasurable (Function.uncurry k))
    (hrep : ∀ (f : Lp H 2 μ) (s : Set V), IsCompact s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = ∫ z, k x z (f z) ∂μ)
    {s t : Set V} (hs : IsCompact s) (ht : IsCompact t) (hst : Disjoint s t) {M : ℝ}
    (hM : ∀ x ∈ s, ∀ y ∈ t, ‖k x y‖ ≤ M) {g : Lp K 2 μ} (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0) :
    ∀ᵐ x ∂μ, x ∈ t → adjoint T g x = ∫ z, adjoint (k z x) (g z) ∂μ := by
  have hψ := memLp_indicator_integral_adjoint_apply hkm hs ht hM hg
  -- `w = T† g - ψ` is orthogonal to its restriction `φ` to `t`, so `φ = 0`.
  set w := adjoint T g - hψ.toLp _
  have hφ := (Lp.memLp w).indicator (s := t) ht.measurableSet.nullMeasurableSet
  have hφt : ∀ᵐ x ∂μ, x ∉ t → hφ.toLp _ x = 0 := by
    filter_upwards [hφ.coeFn_toLp] with x hx hxt
    rw [hx, indicator_of_notMem hxt]
  -- Pairing against `φ`, which vanishes off `t`, only sees values on `t`.
  have hpair {a b : V → H} (hab : ∀ᵐ x ∂μ, x ∈ t → a x = b x) :
      ∫ x, ⟪a x, hφ.toLp _ x⟫_𝕜 ∂μ = ∫ x, ⟪b x, hφ.toLp _ x⟫_𝕜 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hab, hφt] with x hx hxφ
    by_cases hxt : x ∈ t
    · rw [hx hxt]
    · rw [hxφ hxt, inner_zero_right, inner_zero_right]
  have hwφ : ⟪w, hφ.toLp _⟫_𝕜 = 0 := by
    rw [inner_sub_left, L2.inner_def, L2.inner_def,
      integral_inner_adjoint_apply_eq T hkm hrep hs ht hst hM hg hφt, sub_eq_zero]
    refine hpair ?_
    filter_upwards [hψ.coeFn_toLp] with x hx hxt
    rw [hx, indicator_of_mem hxt]
  have hφ0 : ∀ᵐ x ∂μ, hφ.toLp _ x = 0 := by
    have : hφ.toLp _ = 0 := by
      refine (inner_self_eq_zero (𝕜 := 𝕜)).1 ?_
      rw [← hwφ, L2.inner_def, L2.inner_def]
      refine hpair ?_
      filter_upwards [hφ.coeFn_toLp] with x hx hxt
      rw [hx, indicator_of_mem hxt]
    rw [this]
    filter_upwards [Lp.coeFn_zero H 2 μ] with x hx
    rw [hx, Pi.zero_apply]
  have hw : ∀ᵐ x ∂μ, w x = adjoint T g x - hψ.toLp _ x := Lp.coeFn_sub _ _
  filter_upwards [hφ.coeFn_toLp, hφ0, hψ.coeFn_toLp, hw]
    with x hxφ hx0 hxψ hxw hxt
  simpa [hx0, hxw, hxψ, indicator_of_mem hxt, sub_eq_zero] using hxφ.symm

/-- **The kernel of the adjoint.** Let `T` be a bounded operator `L²(V, H) → L²(V, K)` given by a
kernel `k` away from the support of its argument: if `f` vanishes outside a compact set `s`, then
`T f x = ∫ k x z (f z) dz` for almost every `x ∉ s`. If `k` is bounded on the pairs of points at
distance at least `r`, for every `r > 0`, then the adjoint is given in the same way by the
transposed kernel `(x, z) ↦ (k z x)†`: if `g` vanishes outside a compact set `s`, then
`T† g x = ∫ (k z x)† (g z) dz` for almost every `x ∉ s`.

For scalar kernels this is the familiar statement that the adjoint of an integral operator with
kernel `K (x, y)` has the kernel `conj (K (y, x))`. Only the kernel of `T` enters, and no size or
smoothness estimate beyond boundedness away from the diagonal. -/
theorem ae_adjoint_apply_eq_integral (T : Lp H 2 μ →L[𝕜] Lp K 2 μ)
    {k : V → V → H →L[𝕜] K} (hkm : StronglyMeasurable (Function.uncurry k))
    (hk : ∀ r > 0, ∃ M, ∀ x y, r ≤ dist x y → ‖k x y‖ ≤ M)
    (hrep : ∀ (f : Lp H 2 μ) (s : Set V), IsCompact s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = ∫ z, k x z (f z) ∂μ)
    (g : Lp K 2 μ) {s : Set V} (hs : IsCompact s) (hg : ∀ᵐ x ∂μ, x ∉ s → g x = 0) :
    ∀ᵐ x ∂μ, x ∉ s → adjoint T g x = ∫ z, adjoint (k z x) (g z) ∂μ := by
  -- The complement of `s` is covered by the compact sets `t m` at distance at least `1 / (m + 1)`
  -- from `s`, and the identity holds almost everywhere on each of them.
  set t : ℕ → Set V := fun m ↦ compactCovering V m ∩ {x | ∀ y ∈ s, ((m : ℝ) + 1)⁻¹ ≤ dist x y}
  have hloc : ∀ m, ∀ᵐ x ∂μ, x ∈ t m → adjoint T g x = ∫ z, adjoint (k z x) (g z) ∂μ := by
    intro m
    have hc : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
    have ht : IsCompact (t m) := by
      refine (isCompact_compactCovering V m).inter_right ?_
      simp only [ofPred_forall]
      exact isClosed_biInter fun y _ ↦ isClosed_le continuous_const
        (continuous_id.dist continuous_const)
    have hst : Disjoint s (t m) := disjoint_left.2 fun x hxs hxt ↦
      (hc.trans_le (hxt.2 x hxs)).ne' (dist_self x)
    obtain ⟨M, hM⟩ := hk _ hc
    exact ae_adjoint_apply_eq_integral_of_disjoint T hkm hrep hs ht hst
      (fun x hx y hy ↦ hM x y (by rw [dist_comm]; exact hy.2 x hx)) hg
  filter_upwards [ae_all_iff.2 hloc] with x hx hxs
  obtain ⟨m₁, hm₁⟩ := exists_mem_compactCovering x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hs.isClosed.isOpen_compl x hxs
  obtain ⟨m₂, hm₂⟩ := exists_nat_one_div_lt hε
  refine hx (max m₁ m₂) ⟨compactCovering_subset V (le_max_left _ _) hm₁, fun y hy ↦ ?_⟩
  refine le_trans ?_ (not_lt.1 fun hlt ↦ hball (mem_ball'.2 hlt) hy)
  rw [← one_div]
  refine hm₂.le.trans' (one_div_le_one_div_of_le (by positivity) ?_)
  exact_mod_cast Nat.succ_le_succ (le_max_right m₁ m₂)

end ContinuousLinearMap
