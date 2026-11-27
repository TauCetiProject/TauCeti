/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Realization
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication

/-!
# The slow and fast blocks of the inverse of the frozen normal model

Near a pseudoholomorphic curve, Taubes's rescaled large-parameter Seiberg–Witten solutions are
modelled on `ℂ_base × ℂ_normal` by a plane vortex `x` in the normal factor. At a base frequency
`ξ ∈ ℂ` the frozen normal model is the bounded operator
(`TauCeti.SeibergWitten.sobolevFrequencyNormalModel`)

`T_ξ (u, v) = (L_x u - b_N(ξ) v, L_x* v + b_P(ξ) u) : H¹(ℂ)⁴ × H¹(ℂ)⁴ → L² ⊕₂ L²`,

where `L_x` is the gauge-fixed vortex operator and `b_P(ξ) u = Re ξ • u + Im ξ • J u` is
multiplication by `ξ` in the complex structure `J` of variations
(`TauCeti.SeibergWitten.pairedFrequencyCoupling`). At a vortex it is invertible for every
`ξ ≠ 0` (`TauCeti.SeibergWitten.sobolevFrequencyNormalModelEquiv`), with
`|ξ| ‖T_ξ⁻¹ f‖_{L²} ≤ ‖f‖`. That bound degenerates as `ξ → 0`, because `L_x` has a kernel. This
file splits the inverse into a *slow* part, which carries the whole degeneration and is computed
exactly, and a *fast* part, bounded uniformly in `ξ`.

Let `K ⊆ L²(ℂ; ℝ⁴)` be the values of the kernel of `L_x : H¹(ℂ)⁴ → L²` and `Π` the orthogonal
projection onto `K`, the slow variables of the model.

* **The slow block is multiplication by `ξ`.** `K` is preserved by `J`
  (`TauCeti.Vortex.sobolevVariationAlmostComplexStructure_mem_ker_sobolevGaugeFixedOperator`), so
  by `b_P(ξ)` (`pairedFrequencyCoupling_compLpL_mem_map_ker_sobolevGaugeFixedOperator`), and so is
  its orthogonal complement, since `b_P(ξ)† = b_P(conj ξ)`. Hence `Π` commutes with `b_P(ξ)`
  (`starProjection_pairedFrequencyCoupling_compLpL`). The range of `L_x*` is orthogonal to `K`
  (`TauCeti.Vortex.starProjection_sobolevGaugeFixedAdjoint_eq_zero`), so the slow component of
  the paired row only sees the slow component of `u`:
  `Π (L_x* v + b_P(ξ) u) = b_P(ξ) (Π u)` (`starProjection_snd_sobolevFrequencyNormalModel`).
* **The band estimate on `H¹`.** If `c ∫ |η|² ≤ ∫ |L_x* η|²` on test fields, as at every vortex by
  the spectral gap of `L_x L_x*`, then `c ‖η‖² ≤ ‖L_x* η‖²` on `H¹` and
  `c ‖u - Π u‖² ≤ ‖L_x u‖²`
  (`TauCeti.Vortex.mul_norm_sub_starProjection_sq_le_norm_sobolevGaugeFixedOperator_sq`), so the
  energy identity of the model gives, for all `(u, v)` and all `ξ`,
  `c (‖u - Π u‖² + ‖v‖²) + |ξ|² (‖u‖² + ‖v‖²) ≤ ‖T_ξ (u, v)‖²`
  (`mul_add_add_le_norm_sobolevFrequencyNormalModel_sq`), the `H¹` form of
  `TauCeti.SeibergWitten.mul_add_add_le_integral_norm_sq_add_norm_sq_frequencyNormalModel`.
* **The compressed inverse.** For `ξ ≠ 0` and `(u, v) = T_ξ⁻¹ f`, the slow component of `u` is
  `Π u = b_P(ξ⁻¹) (Π f₂)` (`starProjection_fst_sobolevFrequencyNormalModelEquiv_symm`), of norm
  `|ξ|⁻¹ ‖Π f₂‖` (`norm_starProjection_fst_sobolevFrequencyNormalModelEquiv_symm`): the inverse of
  the slow block is multiplication by `ξ⁻¹`. The fast components satisfy
  `c (‖u - Π u‖² + ‖v‖²) ≤ ‖f‖²`
  (`mul_norm_sub_starProjection_sq_add_norm_sq_sobolevFrequencyNormalModelEquiv_symm_le`).
  In `H¹`, there is a constant `C`, independent of `ξ`, such that `u = k + w` with `k` in the
  kernel of `L_x` and with values `b_P(ξ⁻¹) (Π f₂)`, `‖w‖_{H¹} ≤ C ‖f‖` and `‖v‖_{H¹} ≤ C ‖f‖`
  (`exists_forall_exists_mem_ker_norm_sobolevFrequencyNormalModelEquiv_symm_sub_le`); here
  `w = Q (L_x u)` for the right inverse `Q` of `L_x` with values orthogonal to its kernel.

So the inverse of the frozen model is `ξ⁻¹` on the slow block plus a family of operators bounded
uniformly in the frequency. The model is frozen: along a curve the vortex moves with a divisor,
and the moving projections contribute commutator terms, which are not treated here.

## Main results

* `starProjection_snd_sobolevFrequencyNormalModel`: the slow component of the paired row.
* `mul_add_add_le_norm_sobolevFrequencyNormalModel_sq`: the band estimate on `H¹`.
* `starProjection_fst_sobolevFrequencyNormalModelEquiv_symm`,
  `norm_starProjection_fst_sobolevFrequencyNormalModelEquiv_symm`: the slow part of the inverse.
* `mul_norm_sub_starProjection_sq_add_norm_sq_sobolevFrequencyNormalModelEquiv_symm_le`,
  `exists_forall_exists_mem_ker_norm_sobolevFrequencyNormalModelEquiv_symm_sub_le`: the fast part
  of the inverse is bounded uniformly in the frequency.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open Complex MeasureTheory Filter TopologicalSpace Module
open scoped ENNReal Topology RealInnerProductSpace ComplexConjugate

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### The paired coupling on `L²` -/

section Coupling

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- On `L²`, the paired coupling is `g ↦ Re ξ • g + Im ξ • J g`. -/
private theorem pairedFrequencyCoupling_compLpL_apply (ξ : ℂ)
    (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    (pairedFrequencyCoupling ξ).compLpL 2 μ g = ξ.re • g + ξ.im •
      Vortex.variationComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap.compLp g := by
  set J := Vortex.variationComplexStructure.toContinuousLinearEquiv.toContinuousLinearMap
  have h : pairedFrequencyCoupling ξ = ξ.re • ContinuousLinearMap.id ℝ _ + ξ.im • J := by
    ext1 u
    simp [pairedFrequencyCoupling_apply, J]
  rw [h, ContinuousLinearMap.add_compLpL, ContinuousLinearMap.smul_compLpL,
    ContinuousLinearMap.smul_compLpL, ContinuousLinearMap.id_compLpL,
    add_apply, smul_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.compLpL_apply]

/-- On `L²`, the paired coupling at `ξ⁻¹` inverts the paired coupling at `ξ ≠ 0`. -/
private theorem pairedFrequencyCoupling_inv_compLpL_apply {ξ : ℂ} (hξ : ξ ≠ 0)
    (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    (pairedFrequencyCoupling ξ⁻¹).compLpL 2 μ ((pairedFrequencyCoupling ξ).compLpL 2 μ g) = g := by
  rw [ContinuousLinearMap.compLpL_compLpL, pairedFrequencyCoupling_inv_comp hξ,
    ContinuousLinearMap.id_compLpL, ContinuousLinearMap.id_apply]

/-- On `L²`, the paired coupling multiplies norms by `|ξ|`. -/
theorem norm_pairedFrequencyCoupling_compLpL_apply (ξ : ℂ)
    (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    ‖(pairedFrequencyCoupling ξ).compLpL 2 μ g‖ = ‖ξ‖ * ‖g‖ := by
  have h : ‖(pairedFrequencyCoupling ξ).compLpL 2 μ g‖ ^ 2 = (‖ξ‖ * ‖g‖) ^ 2 := by
    rw [Lp.norm_sq_eq_integral_of_ae_eq ((pairedFrequencyCoupling ξ).coeFn_compLpL g),
      mul_pow, Lp.norm_sq_eq_integral_of_ae_eq (EventuallyEq.refl _ _), ← integral_const_mul]
    simp only [norm_pairedFrequencyCoupling_apply, mul_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

end Coupling

variable {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-- **The paired coupling preserves the values of the kernel of `L_x`.** For every `L∞`
coefficient `a` and frequency `ξ`, postcomposition by `b_P(ξ)` maps the values of the kernel of
the realization of `L_x` on `H¹` to themselves, since that kernel is preserved by `J`. -/
theorem pairedFrequencyCoupling_compLpL_mem_map_ker_sobolevGaugeFixedOperator (ξ : ℂ)
    {g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    (hg : g ∈ (Vortex.sobolevGaugeFixedOperator a).ker.map Vortex.sobolevFieldValues.toLinearMap) :
    (pairedFrequencyCoupling ξ).compLpL 2 μ⊤ g ∈
      (Vortex.sobolevGaugeFixedOperator a).ker.map Vortex.sobolevFieldValues.toLinearMap := by
  obtain ⟨y, hy, rfl⟩ := hg
  refine ⟨ξ.re • y + ξ.im • Vortex.sobolevVariationAlmostComplexStructure y,
    Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _
      (Vortex.sobolevVariationAlmostComplexStructure_mem_ker_sobolevGaugeFixedOperator hy)), ?_⟩
  simp only [ContinuousLinearMap.coe_coe, map_add, map_smul,
    Vortex.sobolevFieldValues_sobolevVariationAlmostComplexStructure]
  rw [pairedFrequencyCoupling_compLpL_apply]

/-- **The projection onto the slow variables commutes with the paired coupling.** For every `L∞`
coefficient `a` and frequency `ξ`, the orthogonal projection `Π` onto the values of the kernel of
the realization of `L_x` commutes with postcomposition by `b_P(ξ)`: the kernel is preserved by
`b_P(ξ)` and by its adjoint `b_P(conj ξ)`, so it reduces `b_P(ξ)`. -/
theorem starProjection_pairedFrequencyCoupling_compLpL (ξ : ℂ)
    [((Vortex.sobolevGaugeFixedOperator a).ker.map
      Vortex.sobolevFieldValues.toLinearMap).HasOrthogonalProjection]
    (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    ((Vortex.sobolevGaugeFixedOperator a).ker.map
        Vortex.sobolevFieldValues.toLinearMap).starProjection
        ((pairedFrequencyCoupling ξ).compLpL 2 μ⊤ g) =
      (pairedFrequencyCoupling ξ).compLpL 2 μ⊤
        (((Vortex.sobolevGaugeFixedOperator a).ker.map
          Vortex.sobolevFieldValues.toLinearMap).starProjection g) := by
  set K := (Vortex.sobolevGaugeFixedOperator a).ker.map Vortex.sobolevFieldValues.toLinearMap
  have hred : K.IsReducing ((pairedFrequencyCoupling ξ).compLpL 2 μ⊤ :
      Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) := by
    refine ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint.2
      ⟨fun g hg ↦ pairedFrequencyCoupling_compLpL_mem_map_ker_sobolevGaugeFixedOperator ξ hg,
        fun g hg ↦ ?_⟩
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, ContinuousLinearMap.adjoint_compLpL,
      adjoint_pairedFrequencyCoupling]
    exact pairedFrequencyCoupling_compLpL_mem_map_ker_sobolevGaugeFixedOperator (conj ξ) hg
  exact congr($((Submodule.isReducing_coe_iff_commute_starProjection.1 hred).eq) g)

/-! ### The slow component of the model -/

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **The slow component of the paired row.** For a continuous field `x` with `L∞` class `a`, let
`Π` be the orthogonal projection onto the values of the kernel of `L_x` on `H¹`. Then the slow
component of the paired row of the frozen normal model only sees the slow component of the normal
slot: `Π (L_x* v + b_P(ξ) u) = b_P(ξ) (Π u)`. -/
theorem starProjection_snd_sobolevFrequencyNormalModel (ξ : ℂ) (hx : Continuous x)
    (hax : a =ᵐ[μ⊤] x)
    [((Vortex.sobolevGaugeFixedOperator a).ker.map
      Vortex.sobolevFieldValues.toLinearMap).HasOrthogonalProjection]
    (y : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) :
    ((Vortex.sobolevGaugeFixedOperator a).ker.map
        Vortex.sobolevFieldValues.toLinearMap).starProjection
        (sobolevFrequencyNormalModel a ξ y).snd =
      (pairedFrequencyCoupling ξ).compLpL 2 μ⊤
        (((Vortex.sobolevGaugeFixedOperator a).ker.map
          Vortex.sobolevFieldValues.toLinearMap).starProjection
          (Vortex.sobolevFieldValues y.1)) := by
  rw [snd_sobolevFrequencyNormalModel, map_add,
    Vortex.starProjection_sobolevGaugeFixedAdjoint_eq_zero hx hax, zero_add,
    starProjection_pairedFrequencyCoupling_compLpL]

/-! ### The band estimate on `H¹` -/

section Band

variable (hx : ContDiff ℝ 1 x) (hsol : ∀ z, Vortex.equation x z = 0)
  (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hax : a =ᵐ[μ⊤] x)
  [((Vortex.sobolevGaugeFixedOperator a).ker.map
    Vortex.sobolevFieldValues.toLinearMap).HasOrthogonalProjection]
  {c : ℝ} (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
    c * ∫ z, ‖η z‖ ^ 2 ≤ ∫ z, ‖Vortex.gaugeFixedAdjoint x η z‖ ^ 2)
include hx hsol hlim hax hgap

/-- **The band estimate of the frozen normal model on `H¹`.** Let `x` be a `C¹` vortex with
`|α| → 1` at infinity and with `L∞` class `a`, and suppose that `L_x*` is bounded below,
`c ∫ |η|² ≤ ∫ |L_x* η|²` for every compactly supported `C²` field `η`. Let `Π` be the orthogonal
projection onto the values of the kernel of `L_x` on `H¹`. Then for every frequency `ξ` and every
pair `(u, v) ∈ H¹(ℂ)⁴ × H¹(ℂ)⁴`, with `L²` norms on the left,

`c (‖u - Π u‖² + ‖v‖²) + |ξ|² (‖u‖² + ‖v‖²) ≤ ‖T_ξ (u, v)‖²`.

The fast components `u - Π u` and `v` are controlled uniformly in `ξ`, and the slow component at
the rate `|ξ|`. -/
theorem mul_add_add_le_norm_sobolevFrequencyNormalModel_sq (ξ : ℂ)
    (y : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) :
    c * (‖Vortex.sobolevFieldValues y.1 - ((Vortex.sobolevGaugeFixedOperator a).ker.map
          Vortex.sobolevFieldValues.toLinearMap).starProjection
          (Vortex.sobolevFieldValues y.1)‖ ^ 2 +
        ‖Vortex.sobolevFieldValues y.2‖ ^ 2) +
      ‖ξ‖ ^ 2 * (‖Vortex.sobolevFieldValues y.1‖ ^ 2 + ‖Vortex.sobolevFieldValues y.2‖ ^ 2) ≤
      ‖sobolevFrequencyNormalModel a ξ y‖ ^ 2 := by
  rw [norm_sobolevFrequencyNormalModel_sq ξ hx.continuous hax]
  have h₁ := Vortex.mul_norm_sub_starProjection_sq_le_norm_sobolevGaugeFixedOperator_sq hx hsol
    hlim hax hgap y.1
  have h₂ := Vortex.mul_norm_sobolevFieldValues_sq_le_norm_sobolevGaugeFixedAdjoint_sq hax hgap y.2
  linarith

end Band

/-! ### The slow and fast parts of the inverse -/

/-- Each row of the frozen normal model is bounded by the whole:
`‖L_x u‖ ≤ ‖T_ξ (u, v)‖` and `‖L_x* v‖ ≤ ‖T_ξ (u, v)‖`. -/
private theorem norm_sobolevGaugeFixedOperator_le_and_norm_sobolevGaugeFixedAdjoint_le (ξ : ℂ)
    (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) :
    ‖Vortex.sobolevGaugeFixedOperator a y.1‖ ≤ ‖sobolevFrequencyNormalModel a ξ y‖ ∧
      ‖Vortex.sobolevGaugeFixedAdjoint a y.2‖ ≤ ‖sobolevFrequencyNormalModel a ξ y‖ := by
  have h := norm_sobolevFrequencyNormalModel_sq ξ hx hax y
  have h₀ : 0 ≤ ‖ξ‖ ^ 2 *
      (‖Vortex.sobolevFieldValues y.1‖ ^ 2 + ‖Vortex.sobolevFieldValues y.2‖ ^ 2) := by
    positivity
  constructor <;> refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_ <;>
    nlinarith [sq_nonneg ‖Vortex.sobolevGaugeFixedOperator a y.1‖,
      sq_nonneg ‖Vortex.sobolevGaugeFixedAdjoint a y.2‖]

section Inverse

variable (hx : ContDiff ℝ 1 x) (hsol : ∀ z, Vortex.equation x z = 0)
  (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hcov : Tendsto (fun z ↦ Vortex.covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
  (hax : a =ᵐ[μ⊤] x)
  [((Vortex.sobolevGaugeFixedOperator a).ker.map
    Vortex.sobolevFieldValues.toLinearMap).HasOrthogonalProjection]
include hx hsol hlim hcov hax

/-- **The slow part of the inverse of the frozen normal model is multiplication by `ξ⁻¹`.** At a
`C¹` vortex `x` with `|α| → 1` and `∇₁ α → 0` at infinity and with `L∞` class `a`, let `Π` be the
orthogonal projection onto the values of the kernel of `L_x` on `H¹`. For `ξ ≠ 0` and
`(u, v) = T_ξ⁻¹ f`, the slow component of `u` is `Π u = b_P(ξ⁻¹) (Π f₂)`, where `f₂` is the
paired component of `f`. -/
theorem starProjection_fst_sobolevFrequencyNormalModelEquiv_symm {ξ : ℂ} (hξ : ξ ≠ 0)
    (f : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)) :
    ((Vortex.sobolevGaugeFixedOperator a).ker.map
        Vortex.sobolevFieldValues.toLinearMap).starProjection
        (Vortex.sobolevFieldValues
          ((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f).1) =
      (pairedFrequencyCoupling ξ⁻¹).compLpL 2 μ⊤
        (((Vortex.sobolevGaugeFixedOperator a).ker.map
          Vortex.sobolevFieldValues.toLinearMap).starProjection f.snd) := by
  set y := (sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f
  rw [← sobolevFrequencyNormalModel_sobolevFrequencyNormalModelEquiv_symm_apply ξ hx hsol hlim hcov
    hax hξ f, starProjection_snd_sobolevFrequencyNormalModel ξ hx.continuous hax,
    pairedFrequencyCoupling_inv_compLpL_apply hξ]

/-- **The size of the slow part of the inverse.** In the setting of
`starProjection_fst_sobolevFrequencyNormalModelEquiv_symm`, for `ξ ≠ 0` and `(u, v) = T_ξ⁻¹ f`,
`‖Π u‖ = |ξ|⁻¹ ‖Π f₂‖`. -/
theorem norm_starProjection_fst_sobolevFrequencyNormalModelEquiv_symm {ξ : ℂ} (hξ : ξ ≠ 0)
    (f : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)) :
    ‖((Vortex.sobolevGaugeFixedOperator a).ker.map
        Vortex.sobolevFieldValues.toLinearMap).starProjection
        (Vortex.sobolevFieldValues
          ((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f).1)‖ =
      ‖ξ‖⁻¹ * ‖((Vortex.sobolevGaugeFixedOperator a).ker.map
        Vortex.sobolevFieldValues.toLinearMap).starProjection f.snd‖ := by
  rw [starProjection_fst_sobolevFrequencyNormalModelEquiv_symm hx hsol hlim hcov hax hξ,
    norm_pairedFrequencyCoupling_compLpL_apply, norm_inv]

/-- **The fast part of the inverse is bounded uniformly in the frequency.** At a `C¹` vortex `x`
with `|α| → 1` and `∇₁ α → 0` at infinity and with `L∞` class `a`, suppose that
`c ∫ |η|² ≤ ∫ |L_x* η|²` for every compactly supported `C²` field `η`, and let `Π` be the
orthogonal projection onto the values of the kernel of `L_x` on `H¹`. For every `ξ ≠ 0` and
`(u, v) = T_ξ⁻¹ f`, with `L²` norms on the left, `c (‖u - Π u‖² + ‖v‖²) ≤ ‖f‖²`. -/
theorem mul_norm_sub_starProjection_sq_add_norm_sq_sobolevFrequencyNormalModelEquiv_symm_le
    {ξ : ℂ} (hξ : ξ ≠ 0) {c : ℝ}
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ≤ ∫ z, ‖Vortex.gaugeFixedAdjoint x η z‖ ^ 2)
    (f : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)) :
    c * (‖Vortex.sobolevFieldValues
          ((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f).1 -
        ((Vortex.sobolevGaugeFixedOperator a).ker.map
          Vortex.sobolevFieldValues.toLinearMap).starProjection
          (Vortex.sobolevFieldValues
            ((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f).1)‖ ^ 2 +
        ‖Vortex.sobolevFieldValues
          ((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f).2‖ ^ 2) ≤
      ‖f‖ ^ 2 := by
  set y := (sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f
  have h := mul_add_add_le_norm_sobolevFrequencyNormalModel_sq hx hsol hlim hax hgap ξ y
  rw [sobolevFrequencyNormalModel_sobolevFrequencyNormalModelEquiv_symm_apply] at h
  nlinarith [sq_nonneg ‖ξ‖, sq_nonneg ‖Vortex.sobolevFieldValues y.1‖,
    sq_nonneg ‖Vortex.sobolevFieldValues y.2‖]

/-- **The compressed inverse of the frozen normal model.** At a `C¹` vortex `x` with `|α| → 1`
and `∇₁ α → 0` at infinity and with `L∞` class `a`, let `Π` be the orthogonal projection onto the
values of the kernel of `L_x` on `H¹`. There is a constant `C`, independent of the frequency,
such that for every `ξ ≠ 0` and `(u, v) = T_ξ⁻¹ f` the normal component splits as `u = k + w`,
where `k` lies in the kernel of `L_x` with values `b_P(ξ⁻¹) (Π f₂)`, and
`‖w‖_{H¹} ≤ C ‖f‖`, `‖v‖_{H¹} ≤ C ‖f‖`. So `T_ξ⁻¹` is `ξ⁻¹` on the slow block plus an operator
bounded uniformly in `ξ`. -/
theorem exists_forall_exists_mem_ker_norm_sobolevFrequencyNormalModelEquiv_symm_sub_le :
    ∃ C ≥ 0, ∀ (ξ : ℂ) (hξ : ξ ≠ 0)
      (f : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)),
      ∃ k ∈ (Vortex.sobolevGaugeFixedOperator a).ker,
        Vortex.sobolevFieldValues k = (pairedFrequencyCoupling ξ⁻¹).compLpL 2 μ⊤
          (((Vortex.sobolevGaugeFixedOperator a).ker.map
            Vortex.sobolevFieldValues.toLinearMap).starProjection f.snd) ∧
        ‖((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f).1 - k‖ ≤
          C * ‖f‖ ∧
        ‖((sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f).2‖ ≤
          C * ‖f‖ := by
  set K := (Vortex.sobolevGaugeFixedOperator a).ker.map Vortex.sobolevFieldValues.toLinearMap
  -- `P` is the projection onto the kernel of `L_x` with `L²`-orthogonal fibres, and `Q` the right
  -- inverse of `L_x` with values `L²`-orthogonal to its kernel, so that `u - P u = Q (L_x u)`.
  have := Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator hx hsol hlim hcov hax
  have hsurj := Vortex.sobolevGaugeFixedOperator_surjective hx hsol hlim hax
  have hP := ContinuousLinearMap.isOrthogonalKerProjection_orthogonalKerProjection
    Vortex.sobolevFieldValues_injective (Vortex.sobolevGaugeFixedOperator a)
  have hPQ := (ContinuousLinearMap.IsFredholm.of_surjective hsurj).sub_orthogonalKerProjection_apply
    Vortex.sobolevFieldValues_injective hsurj
  set P := ContinuousLinearMap.orthogonalKerProjection Vortex.sobolevFieldValues
    (Vortex.sobolevGaugeFixedOperator a)
  set Q := ContinuousLinearMap.orthogonalRightInverse Vortex.sobolevFieldValues
    (Vortex.sobolevGaugeFixedOperator a)
  obtain ⟨C₁, hC₁, h₁⟩ := Vortex.exists_norm_le_mul_norm_sobolevGaugeFixedAdjoint hx hsol hlim hax
  refine ⟨max ‖Q‖ C₁, le_max_of_le_right hC₁.le, fun ξ hξ f ↦ ?_⟩
  set y := (sobolevFrequencyNormalModelEquiv ξ hx hsol hlim hcov hax hξ).symm f
  obtain ⟨hL, hA⟩ := norm_sobolevGaugeFixedOperator_le_and_norm_sobolevGaugeFixedAdjoint_le ξ
    hx.continuous hax y
  rw [sobolevFrequencyNormalModel_sobolevFrequencyNormalModelEquiv_symm_apply] at hL hA
  -- The values of `P u` are the slow component `Π u`.
  have hPv :
      Vortex.sobolevFieldValues (P y.1) = K.starProjection (Vortex.sobolevFieldValues y.1) := by
    refine (K.eq_starProjection_of_mem_orthogonal ⟨P y.1, hP.mem_ker y.1, rfl⟩ ?_).symm
    refine (K.mem_orthogonal _).2 ?_
    rintro _ ⟨k', hk', rfl⟩
    simp only [ContinuousLinearMap.coe_coe]
    rw [← map_sub, real_inner_comm]
    exact hP.inner_sub_eq_zero _ k' hk'
  refine ⟨P y.1, hP.mem_ker y.1, hPv.trans (starProjection_fst_sobolevFrequencyNormalModelEquiv_symm
    hx hsol hlim hcov hax hξ f), ?_, ?_⟩
  · -- `u - P u = Q (L_x u)`, and `‖L_x u‖ ≤ ‖f‖`.
    calc ‖y.1 - P y.1‖ = ‖Q (Vortex.sobolevGaugeFixedOperator a y.1)‖ := by rw [hPQ]
      _ ≤ ‖Q‖ * ‖f‖ := Q.le_opNorm_of_le hL
      _ ≤ max ‖Q‖ C₁ * ‖f‖ := by gcongr; exact le_max_left _ _
  · -- `‖v‖_{H¹} ≤ C₁ ‖L_x* v‖ ≤ C₁ ‖f‖`.
    calc ‖y.2‖ ≤ C₁ * ‖Vortex.sobolevGaugeFixedAdjoint a y.2‖ := h₁ y.2
      _ ≤ C₁ * ‖f‖ := by gcongr
      _ ≤ max ‖Q‖ C₁ * ‖f‖ := by gcongr; exact le_max_right _ _

end Inverse

end TauCeti.SeibergWitten
