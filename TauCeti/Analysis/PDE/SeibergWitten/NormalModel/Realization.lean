/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Frequency
public import TauCeti.Analysis.PDE.Vortex.Sobolev.Adjoint
public import TauCeti.Analysis.Fredholm.ContinuousFamily
public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Fredholm.SemiFredholm
public import TauCeti.Analysis.Fredholm.Criteria
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The frozen normal model at a base frequency on `H¹`

Near a pseudoholomorphic curve, Taubes's rescaled large-parameter Seiberg–Witten solutions are
modelled on `ℂ_base × ℂ_normal` by a plane vortex `x` in the normal factor. At a base frequency
`ξ ∈ ℂ` the linearized equations act on a pair `(u, v)` of plane fields through the two rows
(`TauCeti.SeibergWitten.frequencyNormalRow`, `TauCeti.SeibergWitten.frequencyPairedRow`)

`N_ξ(u, v) = L_x u - b_N(ξ) v`,  `P_ξ(u, v) = L_x* v + b_P(ξ) u`,

where `L_x` is the gauge-fixed vortex operator, `L_x*` its formal adjoint, and the base couplings
`b_N(ξ) v = Re ξ • v - Im ξ • J' v` and `b_P(ξ) u = Re ξ • u + Im ξ • J u` multiply norms by
`|ξ|` (`TauCeti.SeibergWitten.normalFrequencyCoupling`,
`TauCeti.SeibergWitten.pairedFrequencyCoupling`). On compactly supported `C¹` fields it satisfies
the energy identity `‖(N_ξ, P_ξ)‖² = ‖L_x u‖² + ‖L_x* v‖² + |ξ|² (‖u‖² + ‖v‖²)`
(`TauCeti.SeibergWitten.integral_norm_sq_add_norm_sq_frequencyNormalModel`). This file realizes
the family as a bounded operator

`T_ξ = sobolevFrequencyNormalModel a ξ : H¹(ℂ)⁴ × H¹(ℂ)⁴ → L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)`,

built from the realizations `TauCeti.Vortex.sobolevGaugeFixedOperator` of `L_x` and
`TauCeti.Vortex.sobolevGaugeFixedAdjoint` of `L_x*` at the `L∞` class `a` of `x`, and inverts it.

* **The energy identity on `H¹`.** For a continuous field `x` it holds for every pair in
  `H¹(ℂ)⁴ × H¹(ℂ)⁴` (`TauCeti.SeibergWitten.norm_sobolevFrequencyNormalModel_sq`), by density of
  test fields. So `|ξ| ‖(u, v)‖_{L²} ≤ ‖T_ξ (u, v)‖`, and `T_ξ` is injective when `ξ ≠ 0`
  (`TauCeti.SeibergWitten.injective_sobolevFrequencyNormalModel`).
* **Coercivity.** At a `C¹` vortex `x` with `|α| → 1` and `∇₁ α → 0` at infinity, the coercive
  estimates of `L_x` and `L_x*` on `H¹` upgrade this, for `ξ ≠ 0`, to
  `‖(u, v)‖_{H¹} ≤ C ‖T_ξ (u, v)‖`
  (`TauCeti.SeibergWitten.exists_norm_le_mul_norm_sobolevFrequencyNormalModel`), so `T_ξ` has
  closed range.
* **Index zero.** At `ξ = 0` the operator is the block sum of `L_x` and `L_x*`, of indices
  `dim ker L_x` and `-dim ker L_x`, so it is Fredholm of index `0`. The family `ξ ↦ T_ξ` is
  continuous in operator norm, and each member has a finite-dimensional kernel and a closed range,
  so every member is Fredholm of index `0`
  (`TauCeti.SeibergWitten.isFredholm_sobolevFrequencyNormalModel`,
  `TauCeti.SeibergWitten.index_sobolevFrequencyNormalModel`).
* **The inverse.** For `ξ ≠ 0`, `T_ξ` is injective of index zero, hence bijective
  (`TauCeti.SeibergWitten.bijective_sobolevFrequencyNormalModel`), and its inverse
  `TauCeti.SeibergWitten.sobolevFrequencyNormalModelEquiv` satisfies
  `|ξ|² ‖(u, v)‖²_{L²} ≤ ‖f‖²` for `(u, v) = T_ξ⁻¹ f`
  (`TauCeti.SeibergWitten.mul_norm_sq_add_norm_sq_sobolevFrequencyNormalModelEquiv_symm_le`).

A stability inequality alone does not give surjectivity: it is the index count at `ξ = 0`, where
the kernel of `L_x` and the cokernel of `L_x*` cancel, that makes `T_ξ` onto. Here `T_ξ` is the
full frozen-coefficient model at frequency `ξ`, with no compression or projection applied.

## Main definitions

* `TauCeti.SeibergWitten.normalFrequencyCoupling`, `TauCeti.SeibergWitten.pairedFrequencyCoupling`:
  the base couplings at frequency `ξ`, as linear maps of `ℝ⁴`.
* `TauCeti.SeibergWitten.sobolevFrequencyNormalModel`: the realization `T_ξ` on `H¹`.
* `TauCeti.SeibergWitten.sobolevFrequencyNormalModelEquiv`: its inverse for `ξ ≠ 0`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open Complex MeasureTheory Filter TopologicalSpace Module
open scoped ENNReal Topology RealInnerProductSpace Distributions

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### The base couplings -/

/-- The base coupling of the normal row at frequency `ξ`, `v ↦ Re ξ • v - Im ξ • J' v`, as a
linear map of `ℝ⁴`. -/
def normalFrequencyCoupling (ξ : ℂ) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ξ.re • ContinuousLinearMap.id ℝ _ -
    ξ.im • (Vortex.targetComplexStructure.toContinuousLinearEquiv :
      EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))

/-- The base coupling of the paired row at frequency `ξ`, `u ↦ Re ξ • u + Im ξ • J u`, as a
linear map of `ℝ⁴`. -/
def pairedFrequencyCoupling (ξ : ℂ) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ξ.re • ContinuousLinearMap.id ℝ _ +
    ξ.im • (Vortex.variationComplexStructure.toContinuousLinearEquiv :
      EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))

/-- The value of the normal coupling: `b_N(ξ) v = Re ξ • v - Im ξ • J' v`. -/
@[simp]
theorem normalFrequencyCoupling_apply (ξ : ℂ) (v : EuclideanSpace ℝ (Fin 4)) :
    normalFrequencyCoupling ξ v = ξ.re • v - ξ.im • Vortex.targetComplexStructure v := by
  simp [normalFrequencyCoupling]

/-- The value of the paired coupling: `b_P(ξ) u = Re ξ • u + Im ξ • J u`. -/
@[simp]
theorem pairedFrequencyCoupling_apply (ξ : ℂ) (u : EuclideanSpace ℝ (Fin 4)) :
    pairedFrequencyCoupling ξ u = ξ.re • u + ξ.im • Vortex.variationComplexStructure u := by
  simp [pairedFrequencyCoupling]

/-- The normal coupling is the base coupling of the normal rows on the rank-one derivative
`w ↦ ⟪ξ, w⟫ v`. -/
theorem normalFrequencyCoupling_eq_normalBaseCoupling (ξ : ℂ) (v : EuclideanSpace ℝ (Fin 4)) :
    normalFrequencyCoupling ξ v = normalBaseCoupling ((innerSL ℝ ξ).smulRight v) := by
  rw [normalBaseCoupling_smulRight_innerSL, normalFrequencyCoupling_apply]

/-- The paired coupling is the base coupling of the paired rows on the rank-one derivative
`w ↦ ⟪ξ, w⟫ u`. -/
theorem pairedFrequencyCoupling_eq_pairedBaseCoupling (ξ : ℂ) (u : EuclideanSpace ℝ (Fin 4)) :
    pairedFrequencyCoupling ξ u = pairedBaseCoupling ((innerSL ℝ ξ).smulRight u) := by
  rw [pairedBaseCoupling_smulRight_innerSL, pairedFrequencyCoupling_apply]

/-- The normal coupling vanishes at frequency zero. -/
@[simp]
theorem normalFrequencyCoupling_zero : normalFrequencyCoupling 0 = 0 := by
  simp [normalFrequencyCoupling]

/-- The paired coupling vanishes at frequency zero. -/
@[simp]
theorem pairedFrequencyCoupling_zero : pairedFrequencyCoupling 0 = 0 := by
  simp [pairedFrequencyCoupling]

/-- The normal coupling depends continuously on the frequency. -/
theorem continuous_normalFrequencyCoupling : Continuous normalFrequencyCoupling := by
  unfold normalFrequencyCoupling
  fun_prop

/-- The paired coupling depends continuously on the frequency. -/
theorem continuous_pairedFrequencyCoupling : Continuous pairedFrequencyCoupling := by
  unfold pairedFrequencyCoupling
  fun_prop

/-! ### The realization -/

/-- **The frozen normal model at frequency `ξ` on `H¹`.** The bounded operator
`(u, v) ↦ (L_x u - b_N(ξ) v, L_x* v + b_P(ξ) u)` from `H¹(ℂ)⁴ × H¹(ℂ)⁴` to the `L²` product
`L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)`, whose zeroth-order coefficients are given by the `L∞` class `a` of the
field `x`. -/
def sobolevFrequencyNormalModel (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (ξ : ℂ) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ]
      WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((Vortex.sobolevGaugeFixedOperator a).comp (.fst ℝ _ _) -
        ((normalFrequencyCoupling ξ).compLpL 2 μ⊤).comp
          (Vortex.sobolevFieldValues.comp (.snd ℝ _ _))).prod
      ((Vortex.sobolevGaugeFixedAdjoint a).comp (.snd ℝ _ _) +
        ((pairedFrequencyCoupling ξ).compLpL 2 μ⊤).comp
          (Vortex.sobolevFieldValues.comp (.fst ℝ _ _))))

variable (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (ξ : ℂ)

/-- The first row of the realization: `L_x u - b_N(ξ) v`. -/
theorem fst_sobolevFrequencyNormalModel
    (y : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) :
    (sobolevFrequencyNormalModel a ξ y).fst = Vortex.sobolevGaugeFixedOperator a y.1 -
      (normalFrequencyCoupling ξ).compLpL 2 μ⊤ (Vortex.sobolevFieldValues y.2) := by
  simp [sobolevFrequencyNormalModel]

/-- The second row of the realization: `L_x* v + b_P(ξ) u`. -/
theorem snd_sobolevFrequencyNormalModel
    (y : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) :
    (sobolevFrequencyNormalModel a ξ y).snd = Vortex.sobolevGaugeFixedAdjoint a y.2 +
      (pairedFrequencyCoupling ξ).compLpL 2 μ⊤ (Vortex.sobolevFieldValues y.1) := by
  simp [sobolevFrequencyNormalModel]

/-! ### The energy identity -/

variable {a} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The coordinates of the element of `H¹(ℂ)⁴` given by a quadruple of test functions are the
coordinates of their field. -/
private theorem value_ofTestFunctionₗ_ae_eq_testField (χ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ))
    (j : Fin 4) :
    W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (χ j)) =ᵐ[μ⊤] fun z ↦ Vortex.testField χ z j :=
  (W1p.value_ofTestFunctionₗ_ae (p := 2) (χ j)).mono fun z hz ↦ by simp [hz]

/-- On a pair of test fields `(U, V)`, the first row of the realization is the classical normal row
`L_x U - b_N(ξ) V` almost everywhere. -/
theorem fst_sobolevFrequencyNormalModel_ofTestFunctionₗ_ae_eq (hax : a =ᵐ[μ⊤] x)
    (φ ψ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ)) :
    (sobolevFrequencyNormalModel a ξ (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j),
        fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (ψ j))).fst =ᵐ[μ⊤]
      frequencyNormalRow x ξ (Vortex.testField φ) (Vortex.testField ψ) := by
  rw [fst_sobolevFrequencyNormalModel]
  filter_upwards [Lp.coeFn_sub (Vortex.sobolevGaugeFixedOperator a _)
      ((normalFrequencyCoupling ξ).compLpL 2 μ⊤ (Vortex.sobolevFieldValues _)),
    Vortex.sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hax
      ((Vortex.contDiff_testField φ).of_le (by simp)) (value_ofTestFunctionₗ_ae_eq_testField φ),
    (normalFrequencyCoupling ξ).coeFn_compLpL (Vortex.sobolevFieldValues
      (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (ψ j))),
    Vortex.sobolevFieldValues_ofTestFunctionₗ_ae ψ] with z h₁ h₂ h₃ h₄
  rw [h₁, Pi.sub_apply, h₂, h₃, h₄, frequencyNormalRow_apply, normalFrequencyCoupling_apply]

/-- On a pair of test fields `(U, V)`, the second row of the realization is the classical paired
row `L_x* V + b_P(ξ) U` almost everywhere. -/
theorem snd_sobolevFrequencyNormalModel_ofTestFunctionₗ_ae_eq (hax : a =ᵐ[μ⊤] x)
    (φ ψ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ)) :
    (sobolevFrequencyNormalModel a ξ (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j),
        fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (ψ j))).snd =ᵐ[μ⊤]
      frequencyPairedRow x ξ (Vortex.testField φ) (Vortex.testField ψ) := by
  rw [snd_sobolevFrequencyNormalModel]
  filter_upwards [Lp.coeFn_add (Vortex.sobolevGaugeFixedAdjoint a _)
      ((pairedFrequencyCoupling ξ).compLpL 2 μ⊤ (Vortex.sobolevFieldValues _)),
    Vortex.sobolevGaugeFixedAdjoint_ae_eq_gaugeFixedAdjoint hax
      ((Vortex.contDiff_testField ψ).of_le (by simp)) (value_ofTestFunctionₗ_ae_eq_testField ψ),
    (pairedFrequencyCoupling ξ).coeFn_compLpL (Vortex.sobolevFieldValues
      (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j))),
    Vortex.sobolevFieldValues_ofTestFunctionₗ_ae φ] with z h₁ h₂ h₃ h₄
  rw [h₁, Pi.add_apply, h₂, h₃, h₄, frequencyPairedRow_apply, pairedFrequencyCoupling_apply]

/-- **The energy identity of the frozen normal model on `H¹`.** For a continuous field `x` with
`L∞` class `a` and every pair `(u, v) ∈ H¹(ℂ)⁴ × H¹(ℂ)⁴`,

`‖T_ξ (u, v)‖² = ‖L_x u‖² + ‖L_x* v‖² + |ξ|² (‖u‖²_{L²} + ‖v‖²_{L²})`. -/
theorem norm_sobolevFrequencyNormalModel_sq (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) :
    ‖sobolevFrequencyNormalModel a ξ y‖ ^ 2 =
      ‖Vortex.sobolevGaugeFixedOperator a y.1‖ ^ 2 + ‖Vortex.sobolevGaugeFixedAdjoint a y.2‖ ^ 2 +
        ‖ξ‖ ^ 2 * (‖Vortex.sobolevFieldValues y.1‖ ^ 2 + ‖Vortex.sobolevFieldValues y.2‖ ^ 2) := by
  -- Both sides are continuous in `y`, and agree on the dense set of pairs of test fields.
  have hd := W1p.denseRange_ofTestFunctionₗ_top (mu := (volume : Measure ℂ)) (p := 2)
    (by norm_num)
  induction y using ((DenseRange.piMap fun _ : Fin 4 ↦ hd).prodMap
    (DenseRange.piMap fun _ : Fin 4 ↦ hd)).induction_on with
  | hp =>
    refine isClosed_eq ((sobolevFrequencyNormalModel a ξ).continuous.norm.pow 2) ?_
    fun_prop
  | ih χ =>
    obtain ⟨φ, ψ⟩ := χ
    have hU : ContDiff ℝ 1 (Vortex.testField φ) := (Vortex.contDiff_testField φ).of_le (by simp)
    have hV : ContDiff ℝ 1 (Vortex.testField ψ) := (Vortex.contDiff_testField ψ).of_le (by simp)
    have hUc := Vortex.hasCompactSupport_testField φ
    have hVc := Vortex.hasCompactSupport_testField ψ
    have iN := (continuous_frequencyNormalRow (ξ := ξ) hx hU
      hV.continuous).integrable_norm_sq_of_hasCompactSupport (μ := volume)
        (hasCompactSupport_frequencyNormalRow hUc hVc)
    have iP := (continuous_frequencyPairedRow (ξ := ξ) hx hU.continuous
      hV).integrable_norm_sq_of_hasCompactSupport (μ := volume)
        (hasCompactSupport_frequencyPairedRow hUc hVc)
    have hmap (χ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ)) :
        Pi.map (fun _ ↦ ⇑(W1p.ofTestFunctionₗ (volume : Measure ℂ) ⊤ 2)) χ =
          fun j ↦ W1p.ofTestFunctionₗ (volume : Measure ℂ) ⊤ 2 (χ j) :=
      funext fun j ↦ Pi.map_apply _ _ j
    simp only [Prod.map_apply, hmap]
    -- Every norm is the integral of the squared norm of the corresponding classical field.
    rw [WithLp.prod_norm_sq_eq_of_L2,
      Lp.norm_sq_eq_integral_of_ae_eq
        (fst_sobolevFrequencyNormalModel_ofTestFunctionₗ_ae_eq ξ hax φ ψ),
      Lp.norm_sq_eq_integral_of_ae_eq
        (snd_sobolevFrequencyNormalModel_ofTestFunctionₗ_ae_eq ξ hax φ ψ),
      Lp.norm_sq_eq_integral_of_ae_eq (Vortex.sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator
        hax hU (value_ofTestFunctionₗ_ae_eq_testField φ)),
      Lp.norm_sq_eq_integral_of_ae_eq (Vortex.sobolevGaugeFixedAdjoint_ae_eq_gaugeFixedAdjoint
        hax hV (value_ofTestFunctionₗ_ae_eq_testField ψ)),
      Lp.norm_sq_eq_integral_of_ae_eq (Vortex.sobolevFieldValues_ofTestFunctionₗ_ae φ),
      Lp.norm_sq_eq_integral_of_ae_eq (Vortex.sobolevFieldValues_ofTestFunctionₗ_ae ψ)]
    simp only [Opens.coe_top, Measure.restrict_univ]
    rw [← integral_add iN iP, integral_norm_sq_add_norm_sq_frequencyNormalModel hx hU hV hUc hVc]

/-- **Clifford coercivity on `H¹`.** For a continuous field `x` with `L∞` class `a`,
`|ξ|² (‖u‖²_{L²} + ‖v‖²_{L²}) ≤ ‖T_ξ (u, v)‖²`. -/
theorem mul_norm_sq_add_norm_sq_le_norm_sobolevFrequencyNormalModel_sq (hx : Continuous x)
    (hax : a =ᵐ[μ⊤] x)
    (y : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) :
    ‖ξ‖ ^ 2 * (‖Vortex.sobolevFieldValues y.1‖ ^ 2 + ‖Vortex.sobolevFieldValues y.2‖ ^ 2) ≤
      ‖sobolevFrequencyNormalModel a ξ y‖ ^ 2 := by
  rw [norm_sobolevFrequencyNormalModel_sq ξ hx hax]
  nlinarith [sq_nonneg ‖Vortex.sobolevGaugeFixedOperator a y.1‖,
    sq_nonneg ‖Vortex.sobolevGaugeFixedAdjoint a y.2‖]

/-- **The frozen normal model is injective at every nonzero frequency**, for a continuous field
`x` with `L∞` class `a`. -/
theorem injective_sobolevFrequencyNormalModel (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (hξ : ξ ≠ 0) : Function.Injective (sobolevFrequencyNormalModel a ξ) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
  have h := mul_norm_sq_add_norm_sq_le_norm_sobolevFrequencyNormalModel_sq ξ hx hax y
  rw [hy, norm_zero] at h
  have hξ₂ : 0 < ‖ξ‖ ^ 2 := by positivity
  have h₁ : ‖Vortex.sobolevFieldValues y.1‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖Vortex.sobolevFieldValues y.1‖,
      sq_nonneg ‖Vortex.sobolevFieldValues y.2‖]
  have h₂ : ‖Vortex.sobolevFieldValues y.2‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖Vortex.sobolevFieldValues y.1‖,
      sq_nonneg ‖Vortex.sobolevFieldValues y.2‖]
  refine Prod.ext (Vortex.sobolevFieldValues_injective ?_) (Vortex.sobolevFieldValues_injective ?_)
  · rw [Prod.fst_zero, map_zero]
    simpa using h₁
  · rw [Prod.snd_zero, map_zero]
    simpa using h₂

/-! ### Coercivity at a vortex -/

/-- The integrals over a disc of the squared values of the four coordinates of a variation are
at most its squared `L²` norm. -/
private theorem sum_setIntegral_ball_value_sq_le (R : ℝ)
    (u : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∑ j, ∫ z in Metric.ball (0 : ℂ) R, W1p.value (u j) z ^ 2 ≤
      ‖Vortex.sobolevFieldValues u‖ ^ 2 := by
  rw [Lp.norm_sq_eq_integral_of_ae_eq (Vortex.sobolevFieldValues_ae_eq u)]
  simp only [Opens.coe_top, Measure.restrict_univ]
  have hi (j : Fin 4) : Integrable (fun z ↦ W1p.value (u j) z ^ 2) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (Lp.memLp (W1p.value (u j))).integrable_sq
  calc ∑ j, ∫ z in Metric.ball (0 : ℂ) R, W1p.value (u j) z ^ 2
      ≤ ∑ j, ∫ z, W1p.value (u j) z ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ setIntegral_le_integral (hi j)
          (.of_forall fun z ↦ sq_nonneg _)
    _ = ∫ z, ∑ j, W1p.value (u j) z ^ 2 := (integral_finsetSum _ fun j _ ↦ hi j).symm
    _ = ∫ z, ‖(WithLp.toLp 2 fun j ↦ W1p.value (u j) z : EuclideanSpace ℝ (Fin 4))‖ ^ 2 :=
        integral_congr_ae (.of_forall fun z ↦ by simp [EuclideanSpace.real_norm_sq_eq])

/-- **The coercive estimate of the frozen normal model at a nonzero frequency.** At a `C¹` vortex
`x` with `|α| → 1` and `∇₁ α → 0` at infinity and with `L∞` class `a`, for `ξ ≠ 0` there is `C`
with `‖(u, v)‖_{H¹} ≤ C ‖T_ξ (u, v)‖` for every pair in `H¹(ℂ)⁴ × H¹(ℂ)⁴`. -/
theorem exists_norm_le_mul_norm_sobolevFrequencyNormalModel (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, Vortex.equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ Vortex.covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) (hξ : ξ ≠ 0) :
    ∃ C ≥ 0, ∀ y, ‖y‖ ≤ C * ‖sobolevFrequencyNormalModel a ξ y‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ := Vortex.exists_norm_le_mul_norm_sobolevGaugeFixedAdjoint hx hsol hlim hax
  obtain ⟨R, -, C₂, hC₂, h₂⟩ :=
    Vortex.exists_norm_sq_le_mul_norm_sobolevGaugeFixedOperator_sq_add hx hsol hlim hcov hax
  have hξ₂ : 0 < ‖ξ‖ ^ 2 := by positivity
  set K := C₂ * (1 + (‖ξ‖ ^ 2)⁻¹)
  have hK : 0 ≤ K := by positivity
  refine ⟨max (√K) C₁, le_max_of_le_right hC₁.le, fun y ↦ ?_⟩
  set T := ‖sobolevFrequencyNormalModel a ξ y‖
  set N₁ := ‖Vortex.sobolevFieldValues y.1‖
  set N₂ := ‖Vortex.sobolevFieldValues y.2‖
  have hE := norm_sobolevFrequencyNormalModel_sq ξ hx.continuous hax y
  have hN : 0 ≤ ‖ξ‖ ^ 2 * (N₁ ^ 2 + N₂ ^ 2) := by positivity
  have hL : ‖Vortex.sobolevGaugeFixedOperator a y.1‖ ^ 2 ≤ T ^ 2 := by
    nlinarith [sq_nonneg ‖Vortex.sobolevGaugeFixedAdjoint a y.2‖]
  have hA : ‖Vortex.sobolevGaugeFixedAdjoint a y.2‖ ≤ T :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by
      nlinarith [sq_nonneg ‖Vortex.sobolevGaugeFixedOperator a y.1‖])
  have hV : N₁ ^ 2 ≤ (‖ξ‖ ^ 2)⁻¹ * T ^ 2 := by
    rw [le_inv_mul_iff₀ hξ₂]
    nlinarith [sq_nonneg ‖Vortex.sobolevGaugeFixedOperator a y.1‖,
      sq_nonneg ‖Vortex.sobolevGaugeFixedAdjoint a y.2‖, sq_nonneg N₂, hξ₂]
  -- The first component, by the coercive estimate of `L_x` and the Clifford coercivity.
  have hy₁ : ‖y.1‖ ≤ √K * T := by
    have h := (h₂ y.1).trans (mul_le_mul_of_nonneg_left
      (add_le_add_right (sum_setIntegral_ball_value_sq_le R y.1) _) hC₂)
    have hsq : ‖y.1‖ ^ 2 ≤ K * T ^ 2 := by
      refine h.trans ?_
      have : ‖Vortex.sobolevGaugeFixedOperator a y.1‖ ^ 2 + N₁ ^ 2 ≤
          (1 + (‖ξ‖ ^ 2)⁻¹) * T ^ 2 := by nlinarith [hL, hV]
      calc C₂ * (‖Vortex.sobolevGaugeFixedOperator a y.1‖ ^ 2 + N₁ ^ 2)
          ≤ C₂ * ((1 + (‖ξ‖ ^ 2)⁻¹) * T ^ 2) := mul_le_mul_of_nonneg_left this hC₂
        _ = K * T ^ 2 := by ring
    calc ‖y.1‖ = √(‖y.1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(K * T ^ 2) := Real.sqrt_le_sqrt hsq
      _ = √K * T := by rw [Real.sqrt_mul hK, Real.sqrt_sq (norm_nonneg _)]
  -- The second component, by the coercive estimate of `L_x*`.
  have hy₂ : ‖y.2‖ ≤ C₁ * T := (h₁ y.2).trans (mul_le_mul_of_nonneg_left hA hC₁.le)
  rw [Prod.norm_def]
  exact max_le (hy₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    (hy₂.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))

/-! ### Continuity in the frequency and the block sum at frequency zero -/

/-- The realization depends continuously on the frequency, in operator norm. -/
theorem continuous_sobolevFrequencyNormalModel : Continuous (sobolevFrequencyNormalModel a) := by
  -- Composition `L ↦ L.compLpL 2 μ⊤` is a bounded linear map of `L`.
  have hc := ((ContinuousLinearMap.id ℝ
    (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))).compLpL₂ 2 μ⊤).continuous
  have hN := hc.comp continuous_normalFrequencyCoupling
  have hP := hc.comp continuous_pairedFrequencyCoupling
  -- The instance search for the operator space is slow; supply its topological group structure.
  have hG : IsTopologicalAddGroup ((Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) ×
      (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :=
    ContinuousLinearMap.isTopologicalAddGroup
  have := hG.toContinuousAdd
  have := hG.to_continuousSub
  have h₁ : Continuous fun ξ ↦ (Vortex.sobolevGaugeFixedOperator a).comp
      (.fst ℝ (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) -
        ((normalFrequencyCoupling ξ).compLpL 2 μ⊤).comp (Vortex.sobolevFieldValues.comp
          (.snd ℝ (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))) :=
    continuous_const.sub (hN.clm_comp continuous_const)
  have h₂ : Continuous fun ξ ↦ (Vortex.sobolevGaugeFixedAdjoint a).comp
      (.snd ℝ (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) +
        ((pairedFrequencyCoupling ξ).compLpL 2 μ⊤).comp (Vortex.sobolevFieldValues.comp
          (.fst ℝ (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))) :=
    continuous_const.add (hP.clm_comp continuous_const)
  exact continuous_const.clm_comp ((ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
    (h₁.prodMk h₂))

/-- At frequency zero the realization is the block sum of the realizations of `L_x` and
`L_x*`. -/
theorem sobolevFrequencyNormalModel_zero :
    sobolevFrequencyNormalModel a 0 =
      (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
        ((Vortex.sobolevGaugeFixedOperator a).prodMap (Vortex.sobolevGaugeFixedAdjoint a)) := by
  have h0 (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      (0 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)).compLp f = 0 := by
    exact congrArg (fun T ↦ T f) (map_zero ((ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))).compLpL₂ 2 μ⊤))
  refine ContinuousLinearMap.ext fun y ↦ ?_
  simp [sobolevFrequencyNormalModel, h0, Prod.map_def]

/-! ### Fredholm property, index and inverse -/

section Vortex

variable (hx : ContDiff ℝ 1 x) (hsol : ∀ z, Vortex.equation x z = 0)
  (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hcov : Tendsto (fun z ↦ Vortex.covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
  (hax : a =ᵐ[μ⊤] x)
include hx hsol hlim hcov hax

/-- At frequency zero, at a vortex, the realization is Fredholm of index `0`: the index
`dim ker L_x` of `L_x` and the index `-dim ker L_x` of `L_x*` cancel. -/
private theorem isFredholm_sobolevFrequencyNormalModel_zero :
    (sobolevFrequencyNormalModel a 0).IsFredholm ∧ (sobolevFrequencyNormalModel a 0).index = 0 := by
  have := Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator hx hsol hlim hcov hax
  have hsurj := Vortex.sobolevGaugeFixedOperator_surjective hx hsol hlim hax
  have hL : (Vortex.sobolevGaugeFixedOperator a).IsFredholm :=
    ContinuousLinearMap.IsFredholm.of_surjective hsurj
  have hA := Vortex.isFredholm_sobolevGaugeFixedAdjoint hx hsol hlim hax
  rw [sobolevFrequencyNormalModel_zero]
  refine ⟨(hL.prodMap hA).equiv_comp _, ?_⟩
  rw [ContinuousLinearMap.index_equiv_comp, hL.index_prodMap hA,
    (Vortex.sobolevGaugeFixedOperator a).index_of_surjective hsurj,
    Vortex.index_sobolevGaugeFixedAdjoint_eq_neg_finrank_ker_sobolevGaugeFixedOperator hx hsol
      hlim hax]
  ring

/-- **The frozen normal model is Fredholm at every frequency**, at a `C¹` vortex `x` with
`|α| → 1` and `∇₁ α → 0` at infinity. -/
theorem isFredholm_sobolevFrequencyNormalModel : (sobolevFrequencyNormalModel a ξ).IsFredholm := by
  have h0 := isFredholm_sobolevFrequencyNormalModel_zero hx hsol hlim hcov hax
  refine ContinuousOn.isFredholm_of_isPreconnected
    (continuous_sobolevFrequencyNormalModel (a := a)).continuousOn (fun ζ _ ↦ ?_) (fun ζ _ ↦ ?_)
    isPreconnected_univ (Set.mem_univ 0) h0.1 (Set.mem_univ ξ)
  · rcases eq_or_ne ζ 0 with rfl | hζ
    · exact h0.1.finite_ker
    · rw [LinearMap.ker_eq_bot.2 (injective_sobolevFrequencyNormalModel ζ hx.continuous hax hζ)]
      infer_instance
  · rcases eq_or_ne ζ 0 with rfl | hζ
    · exact h0.1.isClosed_range
    · obtain ⟨C, hC, h⟩ := exists_norm_le_mul_norm_sobolevFrequencyNormalModel ζ hx hsol hlim hcov
        hax hζ
      exact (((sobolevFrequencyNormalModel a ζ).antilipschitz_of_bound (K := C.toNNReal) fun y ↦ by
        rw [Real.coe_toNNReal _ hC]; exact h y).isClosedEmbedding
          (sobolevFrequencyNormalModel a ζ).uniformContinuous).isClosed_range

/-- **The frozen normal model has index `0` at every frequency**, at a `C¹` vortex `x` with
`|α| → 1` and `∇₁ α → 0` at infinity. -/
theorem index_sobolevFrequencyNormalModel : (sobolevFrequencyNormalModel a ξ).index = 0 := by
  rw [← (isFredholm_sobolevFrequencyNormalModel_zero hx hsol hlim hcov hax).2]
  exact ContinuousOn.index_eq_of_isPreconnected
    (continuous_sobolevFrequencyNormalModel (a := a)).continuousOn
    (fun ζ _ ↦ isFredholm_sobolevFrequencyNormalModel ζ hx hsol hlim hcov hax) isPreconnected_univ
    (Set.mem_univ ξ) (Set.mem_univ 0)

/-- **The frozen normal model is invertible at every nonzero frequency**, at a `C¹` vortex `x`
with `|α| → 1` and `∇₁ α → 0` at infinity: it is injective of index `0`. -/
theorem bijective_sobolevFrequencyNormalModel (hξ : ξ ≠ 0) :
    Function.Bijective (sobolevFrequencyNormalModel a ξ) := by
  have := (isFredholm_sobolevFrequencyNormalModel ξ hx hsol hlim hcov hax).finite_coker
  exact (sobolevFrequencyNormalModel a ξ).bijective_of_injective_of_index_eq_zero
    (injective_sobolevFrequencyNormalModel ξ hx.continuous hax hξ)
    (index_sobolevFrequencyNormalModel ξ hx hsol hlim hcov hax)

/-- **The inverse of the frozen normal model** at a nonzero frequency `ξ`, at a `C¹` vortex `x`
with `|α| → 1` and `∇₁ α → 0` at infinity: the realization as an isomorphism
`H¹(ℂ)⁴ × H¹(ℂ)⁴ ≃ L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)`. -/
def sobolevFrequencyNormalModelEquiv (hξ : ξ ≠ 0) :
    ((Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) ≃L[ℝ]
      WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :=
  ContinuousLinearEquiv.ofBijective (sobolevFrequencyNormalModel a ξ)
    (LinearMap.ker_eq_bot.2 (bijective_sobolevFrequencyNormalModel ξ hx hsol hlim hcov hax hξ).1)
    (LinearMap.range_eq_top.2 (bijective_sobolevFrequencyNormalModel ξ hx hsol hlim hcov hax hξ).2)

/-- The isomorphism is the realization. -/
theorem coe_sobolevFrequencyNormalModelEquiv (hξ : ξ ≠ 0) :
    ⇑(sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ) =
      sobolevFrequencyNormalModel a ξ :=
  ContinuousLinearEquiv.coeFn_ofBijective _ _ _

/-- **The `L²` bound of the inverse**: for `(u, v) = T_ξ⁻¹ f`,
`|ξ|² (‖u‖²_{L²} + ‖v‖²_{L²}) ≤ ‖f‖²`. -/
theorem mul_norm_sq_add_norm_sq_sobolevFrequencyNormalModelEquiv_symm_le (hξ : ξ ≠ 0)
    (f : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)) :
    ‖ξ‖ ^ 2 * (‖Vortex.sobolevFieldValues
        ((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f).1‖ ^ 2 +
      ‖Vortex.sobolevFieldValues
        ((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f).2‖ ^ 2) ≤
      ‖f‖ ^ 2 := by
  have h := mul_norm_sq_add_norm_sq_le_norm_sobolevFrequencyNormalModel_sq ξ hx.continuous hax
    ((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f)
  rwa [← coe_sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ,
    ContinuousLinearEquiv.apply_symm_apply] at h

end Vortex

end TauCeti.SeibergWitten
