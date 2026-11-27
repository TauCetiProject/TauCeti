/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact
import TauCeti.MeasureTheory.Group.Convolution.Fubini
import TauCeti.MeasureTheory.Group.Measure

/-!
# Pointwise Bochner formulas for twisted `L¹` convolution and involution

For a locally compact group `G`, a possibly nonunital (or zero) C⋆-algebra `A`, and a left-invariant
Borel measure `μ` finite on compact sets and inner regular on sets of finite measure with
`μ.inv ≪ μ` (in particular any inner regular or regular Haar measure via
`MeasureTheory.Measure.inv_absolutelyContinuous_of_innerRegular` and
`MeasureTheory.Measure.inv_absolutelyContinuous_of_regular`, without any σ-finiteness, second
countability, or Hausdorff separation assumption), the abstract twisted `L¹` convolution
`TauCeti.CStarAction.convolutionL1` and twisted `L¹` involution
`TauCeti.CStarAction.twistedInvolutionL1` on `Lp A 1 μ` are represented almost everywhere on
integrable functions `f, g : G → A` by the pointwise Bochner formulas

* `(α.bochnerConvolution μ f g) s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ`, and
* `(α.bochnerInvolution f) s = c(s) • α s (star (f s⁻¹))`,

where `c = MeasureTheory.Measure.modularCharacter` is Mathlib's modular character
(`g ↦ μ(· * g⁻¹) / μ`, equal to `Δ⁻¹` in Williams' normalization). No global Fubini or
second-countability hypotheses are required on non-σ-compact groups.

## Main definitions

* `TauCeti.CStarAction.bochnerConvolution`: the pointwise Bochner twisted convolution of two
  functions `G → A`.
* `TauCeti.CStarAction.bochnerInvolution`: the pointwise twisted involution of a function `G → A`.

## Main statements

* `TauCeti.CStarAction.ae_integrable_bochnerConvolution_integrand`,
  `TauCeti.CStarAction.integrable_bochnerConvolution`,
  `TauCeti.CStarAction.convolutionL1_toL1_eq_bochnerConvolution`, and
  `TauCeti.CStarAction.coeFn_convolutionL1`: for any left-invariant measure finite on compact sets,
  inner regular on finite-measure sets, and satisfying `μ.inv ≪ μ` (with no second-countability
  assumption on `G`), the twisted convolution integrand is a.e. integrable, `bochnerConvolution` is
  integrable, and it represents `convolutionL1` almost everywhere.
* `TauCeti.CStarAction.lintegral_eNorm_twistedInvolution`,
  `TauCeti.CStarAction.integrable_bochnerInvolution`,
  `TauCeti.CStarAction.twistedInvolutionL1_toL1_eq_bochnerInvolution`,
  `TauCeti.CStarAction.coeFn_twistedInvolutionL1`, and
  `TauCeti.CStarAction.twistedInvolutionL1_trivial`: twisted involution preserves the `ℝ≥0∞` `L¹`
  norm on `C_c(G, A)`, sends integrable functions to integrable functions with the same `L¹` norm,
  represents `twistedInvolutionL1` almost everywhere whenever `μ.inv ≪ μ` (without `[μ.Regular]`),
  and specializes to `star ∘ MeasureTheory.Lp.modularInversion` for the trivial action on a regular
  Haar measure.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs **134**,
  American Mathematical Society (2007), Chapter 2.
-/

public section

noncomputable section

open Filter Function MeasureTheory Topology
open scoped CompactlySupported ENNReal NNReal

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

/-! ### Pointwise Bochner twisted convolution and twisted involution -/

section BochnerConvolutionDef

variable [MeasurableSpace G]

/-- Pointwise Bochner twisted convolution `(f ⋆ g) s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ` of two
coefficient functions `f g : G → A`. -/
def bochnerConvolution (α : CStarAction G A) (μ : Measure G) (f g : G → A) (s : G) : A :=
  ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ

/-- Evaluation of `bochnerConvolution` at a group element. -/
theorem bochnerConvolution_apply (α : CStarAction G A) (μ : Measure G) (f g : G → A) (s : G) :
    α.bochnerConvolution μ f g s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ :=
  (rfl)

/-- Left zero law for `bochnerConvolution`. -/
@[simp]
theorem bochnerConvolution_zero_left (α : CStarAction G A) (μ : Measure G) (g : G → A) :
    α.bochnerConvolution μ 0 g = 0 := by
  ext s
  simp [bochnerConvolution_apply]

/-- Right zero law for `bochnerConvolution`. -/
@[simp]
theorem bochnerConvolution_zero_right (α : CStarAction G A) (μ : Measure G) (f : G → A) :
    α.bochnerConvolution μ f 0 = 0 := by
  ext s
  simp [bochnerConvolution_apply]

/-- Left scalar law for `bochnerConvolution`. -/
@[simp]
theorem bochnerConvolution_smul_left (α : CStarAction G A) (μ : Measure G)
    (c : ℂ) (f g : G → A) :
    α.bochnerConvolution μ (c • f) g = c • α.bochnerConvolution μ f g := by
  ext s
  simp [bochnerConvolution_apply, smul_mul_assoc, integral_smul]

/-- Right scalar law for `bochnerConvolution`. -/
@[simp]
theorem bochnerConvolution_smul_right (α : CStarAction G A) (μ : Measure G)
    (c : ℂ) (f g : G → A) :
    α.bochnerConvolution μ f (c • g) = c • α.bochnerConvolution μ f g := by
  ext s
  simp [bochnerConvolution_apply, mul_smul_comm, integral_smul]

/-- Pointwise left additivity for `bochnerConvolution` at `s` when both integrands are integrable
there. -/
theorem bochnerConvolution_add_left_apply (α : CStarAction G A) (μ : Measure G)
    {f₁ f₂ g : G → A} {s : G}
    (hf₁ : Integrable (fun r => f₁ r * α r (g (r⁻¹ * s))) μ)
    (hf₂ : Integrable (fun r => f₂ r * α r (g (r⁻¹ * s))) μ) :
    α.bochnerConvolution μ (f₁ + f₂) g s =
      α.bochnerConvolution μ f₁ g s + α.bochnerConvolution μ f₂ g s := by
  simp only [bochnerConvolution_apply, Pi.add_apply, add_mul]
  exact integral_add hf₁ hf₂

/-- Left additivity almost everywhere for `bochnerConvolution` under a.e.-integrability of the
integrands. -/
theorem bochnerConvolution_add_left (α : CStarAction G A) (μ : Measure G) {f₁ f₂ g : G → A}
    (hf₁ : ∀ᵐ s ∂μ, Integrable (fun r => f₁ r * α r (g (r⁻¹ * s))) μ)
    (hf₂ : ∀ᵐ s ∂μ, Integrable (fun r => f₂ r * α r (g (r⁻¹ * s))) μ) :
    α.bochnerConvolution μ (f₁ + f₂) g =ᵐ[μ]
      α.bochnerConvolution μ f₁ g + α.bochnerConvolution μ f₂ g := by
  filter_upwards [hf₁, hf₂] with s hs₁ hs₂
  exact α.bochnerConvolution_add_left_apply μ hs₁ hs₂

/-- Pointwise right additivity for `bochnerConvolution` at `s` when both integrands are integrable
there. -/
theorem bochnerConvolution_add_right_apply (α : CStarAction G A) (μ : Measure G)
    {f g₁ g₂ : G → A} {s : G}
    (hg₁ : Integrable (fun r => f r * α r (g₁ (r⁻¹ * s))) μ)
    (hg₂ : Integrable (fun r => f r * α r (g₂ (r⁻¹ * s))) μ) :
    α.bochnerConvolution μ f (g₁ + g₂) s =
      α.bochnerConvolution μ f g₁ s + α.bochnerConvolution μ f g₂ s := by
  simp only [bochnerConvolution_apply, Pi.add_apply, map_add, mul_add]
  exact integral_add hg₁ hg₂

/-- Right additivity almost everywhere for `bochnerConvolution` under a.e.-integrability of the
integrands. -/
theorem bochnerConvolution_add_right (α : CStarAction G A) (μ : Measure G) {f g₁ g₂ : G → A}
    (hg₁ : ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g₁ (r⁻¹ * s))) μ)
    (hg₂ : ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g₂ (r⁻¹ * s))) μ) :
    α.bochnerConvolution μ f (g₁ + g₂) =ᵐ[μ]
      α.bochnerConvolution μ f g₁ + α.bochnerConvolution μ f g₂ := by
  filter_upwards [hg₁, hg₂] with s hs₁ hs₂
  exact α.bochnerConvolution_add_right_apply μ hs₁ hs₂

/-- On compactly supported continuous functions, `bochnerConvolution` agrees with `convolution`. -/
theorem bochnerConvolution_coe [IsTopologicalGroup G] [OpensMeasurableSpace G]
    (α : CStarAction G A) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f g : C_c(G, A)) :
    α.bochnerConvolution μ f g = α.convolution μ f g := by
  ext s
  rw [bochnerConvolution_apply, convolution_apply]

end BochnerConvolutionDef

section BochnerInvolutionDef

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Pointwise twisted involution `(f*) s = c(s) • α s (star (f s⁻¹))` of an arbitrary coefficient
function `f : G → A`, where `c` is `MeasureTheory.Measure.modularCharacter`. -/
def bochnerInvolution (α : CStarAction G A) (f : G → A) (s : G) : A :=
  ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (f s⁻¹))

/-- Evaluation of `bochnerInvolution` at a group element. -/
theorem bochnerInvolution_apply (α : CStarAction G A) (f : G → A) (s : G) :
    α.bochnerInvolution f s = ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (f s⁻¹)) :=
  (rfl)

/-- `bochnerInvolution` maps `0` to `0`. -/
@[simp]
theorem bochnerInvolution_zero (α : CStarAction G A) :
    α.bochnerInvolution 0 = 0 := by
  ext s
  simp [bochnerInvolution_apply]

/-- `bochnerInvolution` is additive. -/
@[simp]
theorem bochnerInvolution_add (α : CStarAction G A) (f g : G → A) :
    α.bochnerInvolution (f + g) = α.bochnerInvolution f + α.bochnerInvolution g := by
  ext s
  simp [bochnerInvolution_apply, smul_add]

/-- `bochnerInvolution` is conjugate-linear over `ℂ`. -/
@[simp]
theorem bochnerInvolution_smul (α : CStarAction G A) (c : ℂ) (f : G → A) :
    α.bochnerInvolution (c • f) = star c • α.bochnerInvolution f := by
  ext s
  simp only [bochnerInvolution_apply, Pi.smul_apply, star_smul, map_smul]
  exact smul_comm _ _ _

/-- On compactly supported continuous functions, `bochnerInvolution` agrees with
`twistedInvolution`. -/
theorem bochnerInvolution_coe (α : CStarAction G A) (f : C_c(G, A)) :
    α.bochnerInvolution f = α.twistedInvolution f := by
  ext s
  rw [bochnerInvolution_apply, twistedInvolution_apply]

/-- Applying `bochnerInvolution` twice recovers the original function pointwise. -/
@[simp]
theorem bochnerInvolution_bochnerInvolution (α : CStarAction G A) (f : G → A) :
    α.bochnerInvolution (α.bochnerInvolution f) = f := by
  ext s
  have hc : Measure.modularCharacter s * Measure.modularCharacter s⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hc' : ((Measure.modularCharacter s : ℝ) : ℂ) *
      ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hc
  simp only [bochnerInvolution_apply, inv_inv, star_smul, map_star, star_star, map_smul,
    Complex.star_def, Complex.conj_ofReal, apply_inv_apply, smul_smul, hc', one_smul]

/-- The norm of `bochnerInvolution f s` is weighted by the modular character at `s`. -/
@[simp]
theorem norm_bochnerInvolution_apply (α : CStarAction G A) (f : G → A) (s : G) :
    ‖α.bochnerInvolution f s‖ = (Measure.modularCharacter s : ℝ) * ‖f s⁻¹‖ := by
  simp [bochnerInvolution_apply, norm_smul, StarAlgEquiv.norm_map]

end BochnerInvolutionDef

/-! ### Bochner twisted convolution and involution for left-invariant measures with `μ.inv ≪ μ` -/

/-- Pointwise `ℝ≥0∞`-norm bound `‖a * α r b‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ` for a C⋆-action. -/
private theorem eNorm_mul_apply_le (α : CStarAction G A) (a b : A) (r : G) :
    ‖a * α r b‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm a, ← ofReal_norm b, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal ((norm_mul_le _ _).trans_eq (by rw [StarAlgEquiv.norm_map]))

section InvAbsolutelyContinuous

variable [MeasurableSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  (α : CStarAction G A) {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

omit [Group G] [MeasurableSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [μ.InnerRegularCompactLTTop] in
private theorem eNorm_partial_sum_le_tsum {u φ : ℕ → C_c(G, A)}
    (hsum : ∀ n, ∑ i ∈ Finset.range (n + 1), u i = φ n) (n : ℕ) (x : G) :
    ‖φ n x‖ₑ ≤ ∑' i, ‖u i x‖ₑ := by
  rw [← hsum n, CompactlySupportedContinuousMap.coe_sum, Finset.sum_apply]
  exact (eNorm_sum_le _ _).trans (sum_le_tsum (Finset.range (n + 1)))

omit [LocallyCompactSpace G] [μ.InnerRegularCompactLTTop] in
/-- Construct the convolved `L¹` majorant `W` for telescopic `C_c(G, A)` series `u` and `v` with
partial sums `φ` and `ψ`, bounding `‖α.convolution μ (φ n) (ψ n) s‖ₑ ≤ W s` everywhere. -/
private theorem exists_bochnerConvolution_majorant {φ u ψ v : ℕ → C_c(G, A)}
    (hsum_u : ∀ n, ∑ i ∈ Finset.range (n + 1), u i = φ n)
    (hsum_v : ∀ n, ∑ j ∈ Finset.range (n + 1), v j = ψ n)
    (hu_fin : (∑' k, ∫⁻ r, ‖u k r‖ₑ ∂μ) ≠ ∞)
    (hv_fin : (∑' k, ∫⁻ s, ‖v k s‖ₑ ∂μ) ≠ ∞) :
    ∃ W : G → ℝ≥0∞, Measurable W ∧ ∫⁻ s, W s ∂μ ≠ ∞ ∧
      (∀ s, W s = ∫⁻ r, (∑' i, ‖u i r‖ₑ) * (∑' j, ‖v j (r⁻¹ * s)‖ₑ) ∂μ) ∧
      (∀ n s, ‖α.convolution μ (φ n) (ψ n) s‖ₑ ≤ W s) := by
  let W : G → ℝ≥0∞ := fun s => ∑' p : ℕ × ℕ, ∫⁻ r, ‖u p.1 r‖ₑ * ‖v p.2 (r⁻¹ * s)‖ₑ ∂μ
  have hW_meas_term (p : ℕ × ℕ) :
      Measurable fun s => ∫⁻ r, ‖u p.1 r‖ₑ * ‖v p.2 (r⁻¹ * s)‖ₑ ∂μ := by
    simp_rw [lintegral_eNorm_mul_inv_mul_eq_ofReal_integral μ (map_continuous (u p.1))
      (u p.1).hasCompactSupport (map_continuous (v p.2))]
    exact ENNReal.measurable_ofReal.comp (continuous_integral_norm_mul_inv_mul μ
      (map_continuous (u p.1)) (u p.1).hasCompactSupport (map_continuous (v p.2))).measurable
  have hW_fin : ∫⁻ s, W s ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun p => (hW_meas_term p).aemeasurable]
    simp_rw [fun p : ℕ × ℕ => lintegral_lintegral_eNorm_mul_inv_mul μ μ
      (map_continuous (u p.1)) (u p.1).hasCompactSupport
      (map_continuous (v p.2)) (v p.2).hasCompactSupport]
    rw [tsum_prod' (f := fun p : ℕ × ℕ => (∫⁻ r, ‖u p.1 r‖ₑ ∂μ) * ∫⁻ s, ‖v p.2 s‖ₑ ∂μ)]
    simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    exact (ENNReal.mul_lt_top hu_fin.lt_top hv_fin.lt_top).ne
  have hW_eq (s : G) : W s = ∫⁻ r, (∑' i, ‖u i r‖ₑ) * (∑' j, ‖v j (r⁻¹ * s)‖ₑ) ∂μ := by
    have hterm_meas (p : ℕ × ℕ) : AEMeasurable (fun r => ‖u p.1 r‖ₑ * ‖v p.2 (r⁻¹ * s)‖ₑ) μ :=
      ((u p.1).continuous.eNorm.measurable.mul
        ((v p.2).continuous.eNorm.measurable.comp (measurable_inv.mul_const s))).aemeasurable
    dsimp only [W]
    rw [← lintegral_tsum hterm_meas]
    congr 1 with r
    rw [tsum_prod' (f := fun p : ℕ × ℕ => ‖u p.1 r‖ₑ * ‖v p.2 (r⁻¹ * s)‖ₑ)]
    simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  refine ⟨W, Measurable.tsum hW_meas_term, hW_fin, hW_eq, fun n s => ?_⟩
  rw [convolution_apply, hW_eq s]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun r => ?_)
  exact (α.eNorm_mul_apply_le _ _ _).trans
    (mul_le_mul' (eNorm_partial_sum_le_tsum hsum_u n r)
      (eNorm_partial_sum_le_tsum hsum_v n (r⁻¹ * s)))

omit [LocallyCompactSpace G] [μ.InnerRegularCompactLTTop] in
/-- For `μ`-almost every `s`, finiteness of the convolved majorant `W s` yields integrability of
the limit integrand `r ↦ f r * α r (g (r⁻¹ * s))` and pointwise convergence of
`α.convolution μ (φ n) (ψ n) s` to `α.bochnerConvolution μ f g s`. -/
private theorem ae_integrable_and_tendsto_convolution (hinv : μ.inv ≪ μ)
    {f g : G → A} {φ u ψ v : ℕ → C_c(G, A)} {W : G → ℝ≥0∞}
    (hsum_u : ∀ n, ∑ i ∈ Finset.range (n + 1), u i = φ n)
    (hsum_v : ∀ n, ∑ j ∈ Finset.range (n + 1), v j = ψ n)
    (hW_meas : Measurable W) (hW_fin : ∫⁻ s, W s ∂μ ≠ ∞)
    (hW_eq : ∀ s, W s = ∫⁻ r, (∑' i, ‖u i r‖ₑ) * (∑' j, ‖v j (r⁻¹ * s)‖ₑ) ∂μ)
    (hφ_ae : ∀ᵐ r ∂μ, Tendsto (fun n => φ n r) atTop (𝓝 (f r)))
    (hψ_ae : ∀ᵐ t ∂μ, Tendsto (fun n => ψ n t) atTop (𝓝 (g t))) :
    ∀ᵐ s ∂μ,
      Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ ∧
        Tendsto (fun n => α.convolution μ (φ n) (ψ n) s) atTop
          (𝓝 (α.bochnerConvolution μ f g s)) := by
  have hU_meas : Measurable fun r => ∑' i, ‖u i r‖ₑ :=
    Measurable.tsum fun i => (u i).continuous.eNorm.measurable
  have hV_meas : Measurable fun t => ∑' j, ‖v j t‖ₑ :=
    Measurable.tsum fun j => (v j).continuous.eNorm.measurable
  filter_upwards [ae_lt_top hW_meas hW_fin] with s hs
  let D : G → ℝ≥0∞ := fun r => (∑' i, ‖u i r‖ₑ) * ∑' j, ‖v j (r⁻¹ * s)‖ₑ
  have hDs_meas : Measurable D := hU_meas.mul (hV_meas.comp (measurable_inv.mul_const s))
  have hDs_fin : ∫⁻ r, D r ∂μ ≠ ∞ := hW_eq s ▸ hs.ne
  have hDs_int : Integrable (fun r => (D r).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hDs_meas.aemeasurable hDs_fin
  have hψ_s := (μ.quasiMeasurePreserving_inv_mul_of_inv_absolutelyContinuous hinv s).ae hψ_ae
  have hr_lim : ∀ᵐ r ∂μ,
      Tendsto (fun n => φ n r * α r (ψ n (r⁻¹ * s))) atTop (𝓝 (f r * α r (g (r⁻¹ * s)))) := by
    filter_upwards [hφ_ae, hψ_s] with r hfr hgr
    exact hfr.mul (((StarAlgEquiv.isometry (α r)).continuous.tendsto _).comp hgr)
  have hr_bound (n : ℕ) : ∀ᵐ r ∂μ, ‖φ n r * α r (ψ n (r⁻¹ * s))‖ ≤ (D r).toReal := by
    filter_upwards [ae_lt_top hDs_meas hDs_fin] with r hr
    rw [← ENNReal.ofReal_le_iff_le_toReal hr.ne, ofReal_norm]
    exact (α.eNorm_mul_apply_le _ _ _).trans
      (mul_le_mul' (eNorm_partial_sum_le_tsum hsum_u n r)
        (eNorm_partial_sum_le_tsum hsum_v n (r⁻¹ * s)))
  have hr_meas : AEStronglyMeasurable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (α.integrable_integrand (φ n) (ψ n) μ s).aestronglyMeasurable) hr_lim
  have hr_le : ∀ᵐ r ∂μ, ‖f r * α r (g (r⁻¹ * s))‖ ≤ (D r).toReal := by
    filter_upwards [hr_lim, ae_all_iff.2 hr_bound] with r hlim hb
    exact le_of_tendsto' hlim.norm hb
  refine ⟨hDs_int.mono' hr_meas hr_le, ?_⟩
  simpa only [convolution_apply, bochnerConvolution_apply] using
    tendsto_integral_of_dominated_convergence (fun r => (D r).toReal)
      (fun n => (α.integrable_integrand (φ n) (ψ n) μ s).aestronglyMeasurable)
      hDs_int hr_bound hr_lim

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.InnerRegularCompactLTTop]
  [μ.IsMulLeftInvariant] in
private theorem toL1_eq_integrable_toL1 (f : ConvolutionAlgebra α μ) :
    ConvolutionAlgebra.toL1 f = f.ofConv.integrable.toL1 f.ofConv :=
  Lp.ext ((ConvolutionAlgebra.coeFn_toL1 f).trans f.ofConv.integrable.coeFn_toL1.symm)

-- Expand `L¹` approximations into telescopic series in `C_c(G, A)` and exchange integration on
-- each compactly supported term to avoid global Fubini or second-countability assumptions.
private theorem bochnerConvolution_core (hinv : μ.inv ≪ μ) {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ) ∧
      ∃ hh : Integrable (α.bochnerConvolution μ f g) μ,
        α.convolutionL1 μ (hf.toL1 f) (hg.toL1 g) =
          hh.toL1 (α.bochnerConvolution μ f g) := by
  -- 1. Approximate `f` and `g` in `L¹` and a.e. by telescopic `C_c` series, and build the
  -- convolved `L¹` majorant `W`.
  obtain ⟨φ, u, hsum_u, hφ_L1, hφ_ae, hu_fin⟩ := hf.exists_sum_compactlySupported_tendsto
  obtain ⟨ψ, v, hsum_v, hψ_L1, hψ_ae, hv_fin⟩ := hg.exists_sum_compactlySupported_tendsto
  obtain ⟨W, hW_meas, hW_fin, hW_eq, hconv_le⟩ :=
    α.exists_bochnerConvolution_majorant hsum_u hsum_v hu_fin hv_fin
  -- 2. Apply dominated convergence in `r` for a.e. `s`, then dominated `L¹` convergence in `s`.
  have hconv_ae :=
    α.ae_integrable_and_tendsto_convolution hinv hsum_u hsum_v hW_meas hW_fin hW_eq hφ_ae hψ_ae
  have hW_memLp : MemLp W 1 μ :=
    (eLpNorm_one_eq_lintegral_eNorm hW_meas.aestronglyMeasurable).trans_lt hW_fin.lt_top
  have hh_memLp : MemLp (α.bochnerConvolution μ f g) 1 μ :=
    memLp_of_ae_tendsto
      (.of_forall fun n => (α.convolution μ (φ n) (ψ n)).integrable.aestronglyMeasurable)
      hW_memLp (.of_forall fun n => .of_forall fun s => hconv_le n s)
      (hconv_ae.mono fun _ h => h.2)
  have hh : Integrable (α.bochnerConvolution μ f g) μ := memLp_one_iff_integrable.1 hh_memLp
  have hh_tendsto :
      Tendsto (fun n => (α.convolution μ (φ n) (ψ n)).integrable.toL1
          (α.convolution μ (φ n) (ψ n)))
        atTop (𝓝 (hh.toL1 (α.bochnerConvolution μ f g))) := by
    simpa only [Integrable.toL1] using tendsto_toLp_of_ae_tendsto ENNReal.one_ne_top
      (fun n => memLp_one_iff_integrable.2 (α.convolution μ (φ n) (ψ n)).integrable)
      hh_memLp hW_memLp (.of_forall fun n => .of_forall fun s => hconv_le n s)
      (hconv_ae.mono fun _ h => h.2)
  refine ⟨hconv_ae.mono fun _ h => h.1, hh, ?_⟩
  -- 3. Identify the `L¹` limit with `convolutionL1` by joint continuity.
  have hmul_tendsto :
      Tendsto (fun n => α.convolutionL1 μ ((φ n).integrable.toL1 (φ n))
          ((ψ n).integrable.toL1 (ψ n))) atTop
        (𝓝 (α.convolutionL1 μ (hf.toL1 f) (hg.toL1 g))) :=
    ((α.convolutionL1 μ).continuous₂.tendsto (hf.toL1 f, hg.toL1 g)).comp
      (hφ_L1.prodMk_nhds hψ_L1)
  have hmul_eq (n : ℕ) :
      α.convolutionL1 μ ((φ n).integrable.toL1 (φ n)) ((ψ n).integrable.toL1 (ψ n)) =
        (α.convolution μ (φ n) (ψ n)).integrable.toL1 (α.convolution μ (φ n) (ψ n)) := by
    simpa only [toL1_eq_integrable_toL1, ConvolutionAlgebra.ofConv_toConv,
      ConvolutionAlgebra.ofConv_mul] using
      (ConvolutionAlgebra.toL1_mul (α := α) (μ := μ)
        (ConvolutionAlgebra.toConv (φ n)) (ConvolutionAlgebra.toConv (ψ n))).symm
  simp_rw [hmul_eq] at hmul_tendsto
  exact tendsto_nhds_unique hmul_tendsto hh_tendsto

/-- When `μ` is left-invariant and `μ.inv ≪ μ` (for instance via
`Measure.inv_absolutelyContinuous_of_innerRegular` or
`Measure.inv_absolutelyContinuous_of_regular`), the twisted convolution integrand
`r ↦ f r * α r (g (r⁻¹ * s))` is `μ`-integrable for `μ`-almost every `s`. -/
theorem ae_integrable_bochnerConvolution_integrand
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
  (α.bochnerConvolution_core hinv hf hg).1

/-- When `μ` is left-invariant and `μ.inv ≪ μ`, the Bochner twisted convolution of two integrable
functions is integrable. -/
theorem integrable_bochnerConvolution
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (α.bochnerConvolution μ f g) μ :=
  (α.bochnerConvolution_core hinv hf hg).2.choose

/-- Twisted `L¹` convolution `convolutionL1` of the `L¹` classes of integrable functions agrees
with the `L¹` class of their pointwise `bochnerConvolution`, whenever `μ.inv ≪ μ`. -/
theorem convolutionL1_toL1_eq_bochnerConvolution
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    α.convolutionL1 μ (hf.toL1 f) (hg.toL1 g) =
      (α.integrable_bochnerConvolution hinv hf hg).toL1 (α.bochnerConvolution μ f g) :=
  (α.bochnerConvolution_core hinv hf hg).2.choose_spec

/-- Submultiplicativity of the `L¹` norm for `bochnerConvolution` of integrable functions when
`μ.inv ≪ μ`. -/
theorem integral_norm_bochnerConvolution_le
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ s, ‖α.bochnerConvolution μ f g s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := by
  have hint := α.integrable_bochnerConvolution hinv hf hg
  rw [← L1.norm_of_fun_eq_integral_norm hint, ← L1.norm_of_fun_eq_integral_norm hf,
    ← L1.norm_of_fun_eq_integral_norm hg, ← α.convolutionL1_toL1_eq_bochnerConvolution hinv hf hg]
  exact α.norm_convolutionL1_apply_le _ _

/-- For arbitrary `u, v : Lp A 1 μ`, `α.convolutionL1 μ u v` is represented `μ`-almost everywhere
by `α.bochnerConvolution μ u v` whenever `μ.inv ≪ μ`, with no second-countability assumption on
`G`. -/
theorem coeFn_convolutionL1 (hinv : μ.inv ≪ μ) (u v : Lp A 1 μ) :
    α.convolutionL1 μ u v =ᵐ[μ] α.bochnerConvolution μ u v := by
  have hu : (L1.integrable_coeFn u).toL1 u = u := Integrable.toL1_coeFn u (L1.integrable_coeFn u)
  have hv : (L1.integrable_coeFn v).toL1 v = v := Integrable.toL1_coeFn v (L1.integrable_coeFn v)
  conv_lhs => rw [← hu, ← hv]
  rw [α.convolutionL1_toL1_eq_bochnerConvolution hinv
    (L1.integrable_coeFn u) (L1.integrable_coeFn v)]
  exact Integrable.coeFn_toL1 _

omit [μ.InnerRegularCompactLTTop] in
/-- The twisted involution on `C_c(G, A)` preserves the `ℝ≥0∞` `L¹` norm against any left-invariant
measure finite on compact sets. -/
theorem lintegral_eNorm_twistedInvolution (u : C_c(G, A)) :
    ∫⁻ s, ‖α.twistedInvolution u s‖ₑ ∂μ = ∫⁻ s, ‖u s‖ₑ ∂μ := by
  rw [← ofReal_integral_norm_eq_lintegral_eNorm (α.twistedInvolution u).integrable,
    ← ofReal_integral_norm_eq_lintegral_eNorm u.integrable]
  have h := ConvolutionAlgebra.norm_star (ConvolutionAlgebra.toConv (α := α) (μ := μ) u)
  rw [ConvolutionAlgebra.norm_eq_integral_norm, ConvolutionAlgebra.norm_eq_integral_norm,
    ConvolutionAlgebra.ofConv_star, ConvolutionAlgebra.ofConv_toConv] at h
  rw [h]

omit [μ.InnerRegularCompactLTTop] in
/-- Construct the `L¹` majorant `W` for the twisted involution of a telescopic `C_c(G, A)` series
`u` with partial sums `φ`, bounding `‖α.twistedInvolution (φ n) s‖ₑ ≤ W s` everywhere. -/
private theorem exists_bochnerInvolution_majorant {φ u : ℕ → C_c(G, A)}
    (hsum_u : ∀ n, ∑ i ∈ Finset.range (n + 1), u i = φ n)
    (hu_fin : (∑' k, ∫⁻ s, ‖u k s‖ₑ ∂μ) ≠ ∞) :
    ∃ W : G → ℝ≥0∞, MemLp W 1 μ ∧ ∀ n s, ‖α.twistedInvolution (φ n) s‖ₑ ≤ W s := by
  let w : ℕ → C_c(G, A) := fun k => α.twistedInvolution (u k)
  let W : G → ℝ≥0∞ := fun s => ∑' k, ‖w k s‖ₑ
  have hW_meas : AEMeasurable W μ :=
    AEMeasurable.tsum fun k => (w k).integrable.aestronglyMeasurable.eNorm
  have hW_fin : ∫⁻ s, W s ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun k => (w k).integrable.aestronglyMeasurable.eNorm]
    simpa only [w, α.lintegral_eNorm_twistedInvolution] using hu_fin
  have hW_memLp : MemLp W 1 μ :=
    (eLpNorm_one_eq_lintegral_eNorm hW_meas.aestronglyMeasurable).trans_lt hW_fin.lt_top
  have hsum_w (n : ℕ) : ∑ i ∈ Finset.range (n + 1), w i = α.twistedInvolution (φ n) := by
    rw [← hsum_u n, map_sum]
  exact ⟨W, hW_memLp, fun n s => eNorm_partial_sum_le_tsum hsum_w n s⟩

private theorem bochnerInvolution_core (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    ∃ hh : Integrable (α.bochnerInvolution f) μ,
      α.twistedInvolutionL1 μ (hf.toL1 f) = hh.toL1 (α.bochnerInvolution f) := by
  -- 1. Approximate `f` in `L¹` and a.e. by a telescopic `C_c` series, and build its `L¹` majorant.
  obtain ⟨φ, u, hsum_u, hφ_L1, hφ_ae, hu_fin⟩ := hf.exists_sum_compactlySupported_tendsto
  obtain ⟨W, hW_memLp, hk_le⟩ := α.exists_bochnerInvolution_majorant hsum_u hu_fin
  -- 2. Deduce a.e. convergence along `μ.inv ≪ μ` and dominated `L¹` convergence in `s`.
  have hinv_qmp : QuasiMeasurePreserving Inv.inv μ μ := ⟨measurable_inv.aemeasurable, hinv⟩
  have hlim : ∀ᵐ s ∂μ,
      Tendsto (fun n => α.twistedInvolution (φ n) s) atTop (𝓝 (α.bochnerInvolution f s)) := by
    filter_upwards [hinv_qmp.ae hφ_ae] with s hs
    have hcont : Continuous fun a : A => ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star a) :=
      continuous_const.smul ((StarAlgEquiv.isometry (α s)).continuous.comp continuous_star)
    simpa only [Function.comp_def, twistedInvolution_apply, bochnerInvolution_apply] using
      (hcont.tendsto (f s⁻¹)).comp hs
  have hh_memLp : MemLp (α.bochnerInvolution f) 1 μ :=
    memLp_of_ae_tendsto
      (.of_forall fun n => (α.twistedInvolution (φ n)).integrable.aestronglyMeasurable)
      hW_memLp (.of_forall fun n => .of_forall fun s => hk_le n s) hlim
  have hh : Integrable (α.bochnerInvolution f) μ := memLp_one_iff_integrable.1 hh_memLp
  have hh_tendsto :
      Tendsto (fun n => (α.twistedInvolution (φ n)).integrable.toL1 (α.twistedInvolution (φ n)))
        atTop (𝓝 (hh.toL1 (α.bochnerInvolution f))) := by
    simpa only [Integrable.toL1] using tendsto_toLp_of_ae_tendsto ENNReal.one_ne_top
      (fun n => memLp_one_iff_integrable.2 (α.twistedInvolution (φ n)).integrable)
      hh_memLp hW_memLp (.of_forall fun n => .of_forall fun s => hk_le n s) hlim
  refine ⟨hh, ?_⟩
  -- 3. Identify the `L¹` limit with `twistedInvolutionL1` by continuity.
  have hstar_tendsto :
      Tendsto (fun n => α.twistedInvolutionL1 μ ((φ n).integrable.toL1 (φ n))) atTop
        (𝓝 (α.twistedInvolutionL1 μ (hf.toL1 f))) :=
    ((α.twistedInvolutionL1 μ).continuous.tendsto (hf.toL1 f)).comp hφ_L1
  have hstar_eq (n : ℕ) :
      α.twistedInvolutionL1 μ ((φ n).integrable.toL1 (φ n)) =
        (α.twistedInvolution (φ n)).integrable.toL1 (α.twistedInvolution (φ n)) := by
    simpa only [toL1_eq_integrable_toL1, ConvolutionAlgebra.ofConv_toConv,
      ConvolutionAlgebra.ofConv_star] using
      (ConvolutionAlgebra.toL1_star (α := α) (μ := μ) (ConvolutionAlgebra.toConv (φ n))).symm
  simp_rw [hstar_eq] at hstar_tendsto
  exact tendsto_nhds_unique hstar_tendsto hh_tendsto

/-- When `μ` is left-invariant and `μ.inv ≪ μ`, the twisted involution `bochnerInvolution f` of an
integrable function `f` is integrable. -/
theorem integrable_bochnerInvolution
    (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    Integrable (α.bochnerInvolution f) μ :=
  (α.bochnerInvolution_core hinv hf).choose

/-- Twisted `L¹` involution `twistedInvolutionL1` of the `L¹` class of an integrable function
agrees with the `L¹` class of `bochnerInvolution`, whenever `μ.inv ≪ μ`. -/
theorem twistedInvolutionL1_toL1_eq_bochnerInvolution
    (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    α.twistedInvolutionL1 μ (hf.toL1 f) =
      (α.integrable_bochnerInvolution hinv hf).toL1 (α.bochnerInvolution f) :=
  (α.bochnerInvolution_core hinv hf).choose_spec

/-- The twisted involution preserves the `L¹` norm of any integrable function when `μ.inv ≪ μ`. -/
theorem integral_norm_bochnerInvolution
    (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    ∫ s, ‖α.bochnerInvolution f s‖ ∂μ = ∫ s, ‖f s‖ ∂μ := by
  have hint := α.integrable_bochnerInvolution hinv hf
  rw [← L1.norm_of_fun_eq_integral_norm hint, ← L1.norm_of_fun_eq_integral_norm hf,
    ← α.twistedInvolutionL1_toL1_eq_bochnerInvolution hinv hf, LinearIsometryEquiv.norm_map]

/-- For `u : Lp A 1 μ`, `α.twistedInvolutionL1 μ u` is represented `μ`-almost everywhere by
`α.bochnerInvolution u` whenever `μ.inv ≪ μ` (without assuming `[μ.Regular]`). -/
theorem coeFn_twistedInvolutionL1 (hinv : μ.inv ≪ μ) (u : Lp A 1 μ) :
    α.twistedInvolutionL1 μ u =ᵐ[μ] α.bochnerInvolution u := by
  have hu : (L1.integrable_coeFn u).toL1 u = u := Integrable.toL1_coeFn u (L1.integrable_coeFn u)
  conv_lhs => rw [← hu]
  rw [α.twistedInvolutionL1_toL1_eq_bochnerInvolution hinv (L1.integrable_coeFn u)]
  exact Integrable.coeFn_toL1 _

end InvAbsolutelyContinuous

section RegularHaar

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

/-- For the trivial action and a regular Haar measure, `twistedInvolutionL1` is pointwise `star`
composed with `MeasureTheory.Lp.modularInversion`. -/
@[simp]
theorem twistedInvolutionL1_trivial (f : Lp A 1 μ) :
    (trivial (G := G) (A := A)).twistedInvolutionL1 μ f =
      star (Lp.modularInversion μ 1 ℂ f) := by
  refine Lp.ext ?_
  filter_upwards [(trivial (G := G) (A := A)).coeFn_twistedInvolutionL1
      (Measure.inv_absolutelyContinuous_of_regular μ) f,
    Lp.coeFn_star (Lp.modularInversion μ 1 ℂ f),
    Lp.coeFn_modularInversion (𝕜 := ℂ) f] with s h₁ h₂ h₃
  rw [h₁, bochnerInvolution_apply, trivial_apply, h₂, Pi.star_apply, h₃]
  simp [ENNReal.toReal_one, star_smul]

end RegularHaar

end TauCeti.CStarAction
