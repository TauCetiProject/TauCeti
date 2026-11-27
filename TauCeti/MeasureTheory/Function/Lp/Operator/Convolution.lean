/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Function.Lp.Operator.Compact
import TauCeti.Topology.UrysohnsLemma

/-!
# Compactness of convolution after multiplication on `Lᵖ`

Let `E` be a finite-dimensional real inner product space, `g : E → ℂ` integrable and `ψ : E → ℂ`
continuous. The operator `w ↦ g ⋆ (ψ w)` on `Lᵖ(E, F)` is the integral operator with kernel
`(x, y) ↦ g (x - y) ψ y` (`TauCeti.convMulKernel`). When `ψ` is bounded by `C` and `∫ ‖g‖ ≤ I`,
the row and column integrals of this kernel are at most `C * I`, so by Schur's test it is bounded
with norm at most `C * I`. When `F` is finite-dimensional and `ψ` tends to `0` at infinity, it is a
**compact operator**.

The proof of compactness approximates in Schur norm. For `ψ` compactly supported, continuous
compactly supported `gₙ → g` in `L¹` give continuous compactly supported kernels
`gₙ (x - y) ψ y`, which give compact operators
(`TauCeti.isCompactOperator_integralOperatorLp_of_continuousOn`). For `ψ` tending to `0` at
infinity, the compactly supported multipliers `χₙ ψ` of
`Continuous.exists_hasCompactSupport_norm_sub_le` tend to `ψ` uniformly.

Such operators appear in Rellich-type compactness statements: for `r < 0` the Bessel potential
`J^r` is convolution with an integrable kernel, so multiplication by a Schwartz function followed
by `J^r` has this form.

## Main declarations

* `TauCeti.convMulKernel`: the kernel `g (x - y) ψ y` of `w ↦ g ⋆ (ψ w)`, acting on `w` by
  `TauCeti.convMulKernel_apply`.
* `TauCeti.ae_lintegral_enorm_convMulKernel_le`: its row and column integrals are at most
  `C * I`.
* `TauCeti.isCompactOperator_integralOperatorLp_convMulKernel`: `w ↦ g ⋆ (ψ w)` is compact for
  `ψ` continuous and compactly supported.
* `TauCeti.isCompactOperator_integralOperatorLp_convMulKernel_of_tendsto`: `w ↦ g ⋆ (ψ w)` is
  compact for `ψ` continuous, bounded and tending to `0` at infinity.
-/

public section

noncomputable section

open MeasureTheory Filter Set Function
open scoped ENNReal NNReal Topology Pointwise

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (F) in
/-- The kernel `(x, y) ↦ g (x - y) ψ y` of `w ↦ g ⋆ (ψ w)`, acting on `F` by scalars. -/
def convMulKernel (g ψ : E → ℂ) (x y : E) : F →L[ℂ] F :=
  (g (x - y) * ψ y) • ContinuousLinearMap.id ℂ F

/-- The kernel of `w ↦ g ⋆ (ψ w)` at `(x, y)` multiplies by the scalar `g (x - y) ψ y`. -/
@[simp]
theorem convMulKernel_apply (g ψ : E → ℂ) (x y : E) (w : F) :
    convMulKernel F g ψ x y w = (g (x - y) * ψ y) • w := by
  simp [convMulKernel]

/-- The kernel of `w ↦ g ⋆ (ψ w)` is bounded by `‖g (x - y)‖ ‖ψ y‖`. -/
theorem enorm_convMulKernel_le (g ψ : E → ℂ) (x y : E) :
    ‖convMulKernel F g ψ x y‖ₑ ≤ ‖g (x - y)‖ₑ * ‖ψ y‖ₑ := by
  have h : ‖convMulKernel F g ψ x y‖ ≤ ‖g (x - y)‖ * ‖ψ y‖ := calc
    ‖convMulKernel F g ψ x y‖ ≤ ‖g (x - y) * ψ y‖ * ‖ContinuousLinearMap.id ℂ F‖ := by
      rw [convMulKernel]
      exact norm_smul_le (g (x - y) * ψ y) (ContinuousLinearMap.id ℂ F)
    _ ≤ ‖g (x - y) * ψ y‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
    _ = ‖g (x - y)‖ * ‖ψ y‖ := by rw [mul_one, norm_mul]
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

/-- The kernel of `w ↦ g ⋆ (ψ w)` is linear in `g`: the difference of the kernels for `g₁` and
`g₂` is the kernel for `g₁ - g₂`. -/
theorem convMulKernel_sub_left (g₁ g₂ ψ : E → ℂ) :
    convMulKernel F (g₁ - g₂) ψ =
      fun x y ↦ convMulKernel F g₁ ψ x y - convMulKernel F g₂ ψ x y := by
  funext x y
  simp only [convMulKernel, Pi.sub_apply, sub_mul, sub_smul]

/-- The kernel of `w ↦ g ⋆ (ψ w)` is linear in `ψ`: the difference of the kernels for `ψ₁` and
`ψ₂` is the kernel for `ψ₁ - ψ₂`. -/
theorem convMulKernel_sub_right (g ψ₁ ψ₂ : E → ℂ) :
    convMulKernel F g (ψ₁ - ψ₂) =
      fun x y ↦ convMulKernel F g ψ₁ x y - convMulKernel F g ψ₂ x y := by
  funext x y
  simp only [convMulKernel, Pi.sub_apply, mul_sub, sub_smul]

/-- The kernel of `w ↦ g ⋆ (ψ w)` vanishes at `(x, y)` unless `y ∈ tsupport ψ` and
`x ∈ tsupport g + tsupport ψ`. -/
theorem convMulKernel_eq_zero {g ψ : E → ℂ} {x y : E}
    (h : (x, y) ∉ (tsupport g + tsupport ψ) ×ˢ tsupport ψ) : convMulKernel F g ψ x y = 0 := by
  by_cases hy : y ∈ tsupport ψ
  · have hx : x - y ∉ tsupport g := fun hx ↦ h ⟨by simpa using add_mem_add hx hy, hy⟩
    simp [convMulKernel, image_eq_zero_of_notMem_tsupport hx]
  · simp [convMulKernel, image_eq_zero_of_notMem_tsupport hy]

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The kernel of `w ↦ g ⋆ (ψ w)` is a.e. strongly measurable for `g` a.e. strongly measurable and
`ψ` continuous. -/
theorem aestronglyMeasurable_convMulKernel {g ψ : E → ℂ} (hg : AEStronglyMeasurable g volume)
    (hψ : Continuous ψ) :
    AEStronglyMeasurable (uncurry (convMulKernel F g ψ)) (volume.prod volume) := by
  have h₁ : AEStronglyMeasurable (fun z : E × E ↦ g (z.1 - z.2)) (volume.prod volume) :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)
  have h₂ : AEStronglyMeasurable (fun z : E × E ↦ ψ z.2) (volume.prod volume) :=
    (hψ.comp continuous_snd).aestronglyMeasurable
  exact (h₁.mul h₂).smul aestronglyMeasurable_const

/-- **Schur bounds for `w ↦ g ⋆ (ψ w)`.** If `‖ψ‖ ≤ C` and `∫ ‖g‖ ≤ I`, the row and the column
integrals of the kernel `g (x - y) ψ y` are at most `C * I`, by translation invariance. -/
theorem ae_lintegral_enorm_convMulKernel_le {g ψ : E → ℂ} {C I : ℝ≥0}
    (hψ : ∀ y, ‖ψ y‖ ≤ C) (hg : ∫⁻ z, ‖g z‖ₑ ≤ I) :
    (∀ᵐ x ∂(volume : Measure E), ∫⁻ y, ‖convMulKernel F g ψ x y‖ₑ ≤ ((C * I : ℝ≥0) : ℝ≥0∞)) ∧
      ∀ᵐ y ∂(volume : Measure E), ∫⁻ x, ‖convMulKernel F g ψ x y‖ₑ ≤ ((C * I : ℝ≥0) : ℝ≥0∞) := by
  -- Both integrals are bounded by `C` times a translate of `∫ ‖g‖`.
  have hbd (f : E → E × E) (hf : ∫⁻ z, ‖g ((f z).1 - (f z).2)‖ₑ = ∫⁻ z, ‖g z‖ₑ) :
      ∫⁻ z, ‖convMulKernel F g ψ (f z).1 (f z).2‖ₑ ≤ ((C * I : ℝ≥0) : ℝ≥0∞) := calc
    ∫⁻ z, ‖convMulKernel F g ψ (f z).1 (f z).2‖ₑ ≤ ∫⁻ z, ‖g ((f z).1 - (f z).2)‖ₑ * C :=
      lintegral_mono fun z ↦ (enorm_convMulKernel_le g ψ _ _).trans
        (mul_le_mul_right (eNorm_le_coe.2 (by exact_mod_cast hψ _)) _)
    _ = (∫⁻ z, ‖g z‖ₑ) * C := by rw [lintegral_mul_const' _ _ ENNReal.coe_ne_top, hf]
    _ ≤ I * C := by gcongr
    _ = ((C * I : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
  exact ⟨.of_forall fun x ↦ hbd (fun y ↦ (x, y)) (lintegral_sub_left_eq_self (‖g ·‖ₑ) x),
    .of_forall fun y ↦ hbd (fun x ↦ (x, y)) (lintegral_sub_right_eq_self (‖g ·‖ₑ) y)⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two integral operators whose kernels differ by the kernel of `w ↦ g ⋆ (ψ w)`, with `‖ψ‖ ≤ C`
and `∫ ‖g‖ ≤ I`, are at distance at most `C * I`. -/
private theorem norm_integralOperatorLp_sub_le {K₁ K₂ : E → E → F →L[ℂ] F} {g ψ : E → ℂ}
    {C I : ℝ≥0} (hK : convMulKernel F g ψ = fun x y ↦ K₁ x y - K₂ x y)
    (hg : AEStronglyMeasurable g volume) (hψc : Continuous ψ) (hψ : ∀ y, ‖ψ y‖ ≤ C)
    (hgI : ∫⁻ z, ‖g z‖ₑ ≤ I) {hK₁ : AEStronglyMeasurable (uncurry K₁) (volume.prod volume)}
    {A₁ B₁ : ℝ≥0} {hA₁ : ∀ᵐ x ∂(volume : Measure E), ∫⁻ y, ‖K₁ x y‖ₑ ≤ A₁}
    {hB₁ : ∀ᵐ y ∂(volume : Measure E), ∫⁻ x, ‖K₁ x y‖ₑ ≤ B₁}
    {hK₂ : AEStronglyMeasurable (uncurry K₂) (volume.prod volume)} {A₂ B₂ : ℝ≥0}
    {hA₂ : ∀ᵐ x ∂(volume : Measure E), ∫⁻ y, ‖K₂ x y‖ₑ ≤ A₂}
    {hB₂ : ∀ᵐ y ∂(volume : Measure E), ∫⁻ x, ‖K₂ x y‖ₑ ≤ B₂} :
    ‖integralOperatorLp K₁ p hK₁ hA₁ hB₁ - integralOperatorLp K₂ p hK₂ hA₂ hB₂‖ ≤ C * I := by
  have hK' := aestronglyMeasurable_convMulKernel (F := F) hg hψc
  have hAB := ae_lintegral_enorm_convMulKernel_le (F := F) hψ hgI
  rw [hK] at hK' hAB
  rw [integralOperatorLp_sub (hK := hK') (hA := hAB.1) (hB := hAB.2)]
  exact norm_integralOperatorLp_le_max.trans_eq (by simp)

/-- **Convolution after multiplication is compact on `Lᵖ`.** For an integrable `g` and a continuous
compactly supported `ψ`, the operator `w ↦ g ⋆ (ψ w)` on `Lᵖ(E, F)`, with kernel `g (x - y) ψ y`,
is compact. Its kernel is the limit in Schur norm of the continuous compactly supported kernels
`gₙ (x - y) ψ y`, for continuous compactly supported `gₙ → g` in `L¹`. -/
theorem isCompactOperator_integralOperatorLp_convMulKernel [FiniteDimensional ℂ F]
    {g ψ : E → ℂ} (hg : Integrable g) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {hK : AEStronglyMeasurable (uncurry (convMulKernel F g ψ)) (volume.prod volume)} {A B : ℝ≥0}
    {hA : ∀ᵐ x ∂(volume : Measure E), ∫⁻ y, ‖convMulKernel F g ψ x y‖ₑ ≤ A}
    {hB : ∀ᵐ y ∂(volume : Measure E), ∫⁻ x, ‖convMulKernel F g ψ x y‖ₑ ≤ B} :
    IsCompactOperator (integralOperatorLp (convMulKernel F g ψ) p hK hA hB) := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  obtain ⟨C₀, hC₀⟩ := hψ.bounded_above_of_compact_support hψc
  have hC : ∀ y, ‖ψ y‖ ≤ C₀.toNNReal := fun y ↦ (hC₀ y).trans (Real.le_coe_toNNReal C₀)
  -- Continuous compactly supported approximations `gₙ` of `g` in `L¹`.
  have happrox (n : ℕ) := hg.exists_hasCompactSupport_lintegral_sub_le
    (ε := (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0)) (by simp)
  choose g' hg'c hg'g hg'cont hg'int using happrox
  have hfin (n : ℕ) : ∫⁻ z, ‖g' n z‖ₑ ≤ (∫⁻ z, ‖g' n z‖ₑ).toNNReal :=
    (ENNReal.coe_toNNReal (hg'int n).hasFiniteIntegral.ne).ge
  have hsub (n : ℕ) : ∫⁻ z, ‖(g - g' n) z‖ₑ ≤ (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) := hg'g n
  -- The approximating operators are compact, and converge to the given one in norm.
  refine isCompactOperator_of_tendsto (l := atTop)
    (F := fun n ↦ integralOperatorLp (convMulKernel F (g' n) ψ) p
      (aestronglyMeasurable_convMulKernel (hg'cont n).aestronglyMeasurable hψ)
      (ae_lintegral_enorm_convMulKernel_le hC (hfin n)).1
      (ae_lintegral_enorm_convMulKernel_le hC (hfin n)).2) ?_ (Eventually.of_forall fun n ↦ ?_)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (C₀.toNNReal : ℝ))
    rw [norm_sub_rev]
    exact_mod_cast norm_integralOperatorLp_sub_le (convMulKernel_sub_left g (g' n) ψ)
      (hg.sub (hg'int n)).aestronglyMeasurable hψ hC (hsub n)
  · exact isCompactOperator_integralOperatorLp_of_continuousOn
      ((hg'c n).isCompact.add hψc.isCompact) hψc.isCompact
      (((((hg'cont n).comp continuous_sub).mul (hψ.comp continuous_snd)).smul
        continuous_const).continuousOn) fun x y h ↦ convMulKernel_eq_zero h

/-- **Convolution after multiplication is compact on `Lᵖ`**, for a multiplier vanishing at
infinity: for an integrable `g` and a bounded continuous `ψ` tending to `0` at infinity, the
operator `w ↦ g ⋆ (ψ w)` on `Lᵖ(E, F)` is compact. It is the limit in Schur norm of the operators
for the compactly supported multipliers `χₙ ψ`, where `χₙ` is a continuous cutoff equal to `1`
where `‖ψ‖ ≥ 1 / (n + 1)`. -/
theorem isCompactOperator_integralOperatorLp_convMulKernel_of_tendsto
    [FiniteDimensional ℂ F] {g ψ : E → ℂ} (hg : Integrable g) (hψ : Continuous ψ) {C : ℝ≥0}
    (hC : ∀ y, ‖ψ y‖ ≤ C) (hψ0 : Tendsto ψ (cocompact E) (𝓝 0))
    {hK : AEStronglyMeasurable (uncurry (convMulKernel F g ψ)) (volume.prod volume)} {A B : ℝ≥0}
    {hA : ∀ᵐ x ∂(volume : Measure E), ∫⁻ y, ‖convMulKernel F g ψ x y‖ₑ ≤ A}
    {hB : ∀ᵐ y ∂(volume : Measure E), ∫⁻ x, ‖convMulKernel F g ψ x y‖ₑ ≤ B} :
    IsCompactOperator (integralOperatorLp (convMulKernel F g ψ) p hK hA hB) := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  set I : ℝ≥0 := (∫⁻ z, ‖g z‖ₑ).toNNReal
  have hfin : ∫⁻ z, ‖g z‖ₑ ≤ I := (ENNReal.coe_toNNReal hg.hasFiniteIntegral.ne).ge
  have happrox (n : ℕ) := hψ.exists_hasCompactSupport_norm_sub_le hψ0
    (by positivity : (0 : ℝ) < (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0))
  choose ψ' hψ'cont hψ'c hψ'ψ hsub using happrox
  have hψ'le (n : ℕ) (y : E) : ‖ψ' n y‖ ≤ C := (hψ'ψ n y).trans (hC y)
  refine isCompactOperator_of_tendsto (l := atTop)
    (F := fun n ↦ integralOperatorLp (convMulKernel F g (ψ' n)) p
      (aestronglyMeasurable_convMulKernel hg.aestronglyMeasurable (hψ'cont n))
      (ae_lintegral_enorm_convMulKernel_le (hψ'le n) hfin).1
      (ae_lintegral_enorm_convMulKernel_le (hψ'le n) hfin).2) ?_ (Eventually.of_forall fun n ↦
        isCompactOperator_integralOperatorLp_convMulKernel hg (hψ'cont n) (hψ'c n))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const (I : ℝ))
  rw [norm_sub_rev]
  exact_mod_cast norm_integralOperatorLp_sub_le (convMulKernel_sub_right g ψ (ψ' n))
    hg.aestronglyMeasurable (hψ.sub (hψ'cont n)) (hsub n) hfin

end TauCeti
