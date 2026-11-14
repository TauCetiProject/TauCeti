/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Normed
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Ring.Completion
public import TauCeti.MeasureTheory.Function.Lp.GroupConvolution
import TauCeti.Analysis.Normed.Operator.Completion
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact
import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.MeasureTheory.Group.Convolution.Support

/-!
# Bochner `L¹` realization of the twisted `L¹` Banach ⋆-algebra

For a locally compact group `G`, a possibly nonunital (or zero) C⋆-algebra `A`, and a locally
finite Borel measure `μ` that is inner regular on sets of finite measure with respect to compact
sets — in particular any regular or inner regular Haar measure — compactly supported continuous
functions are dense in the Bochner space `L¹(G, A, μ)`. Consequently, the canonical linear isometry
`TauCeti.CStarAction.ConvolutionAlgebra.toL1LI` extends to a linear isometric equivalence
`TauCeti.CStarAction.ConvolutionAlgebra.toL1Equiv` from the twisted `L¹` completion
`UniformSpace.Completion (ConvolutionAlgebra α μ)` onto `Lp A 1 μ`.

Under this identification, the Banach ⋆-algebra operations of the twisted `L¹` completion are
represented almost everywhere on integrable functions `f, g : G → A` by the pointwise Bochner
formulas

* `(α.bochnerConvolution μ f g) s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ`, and
* `(α.bochnerInvolution f) s = c(s) • α s (star (f s⁻¹))`,

whenever `μ` is left-invariant and `μ.inv ≪ μ` (in particular for both inner regular and regular
Haar measures, without any σ-finiteness, second countability, or Hausdorff separation assumption).
To avoid global Fubini hypotheses on non-σ-compact groups, the proof expands `L¹` approximations
into telescopic series in `C_c(G, A)` and exchanges integration on each compactly supported term.

For the trivial action on `ℂ`, the transported multiplication and involution agree with scalar
group convolution `MeasureTheory.Lp.convolutionL` and conjugated modular inversion
`MeasureTheory.Lp.modularInversion`.

## Main definitions

* `TauCeti.CStarAction.ConvolutionAlgebra.toL1CompletionLI`: the linear isometric extension of
  `toL1LI` to `UniformSpace.Completion (ConvolutionAlgebra α μ) →ₗᵢ[ℂ] Lp A 1 μ`.
* `TauCeti.CStarAction.ConvolutionAlgebra.toL1Equiv`: the linear isometric equivalence
  `UniformSpace.Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ`.
* `TauCeti.CStarAction.bochnerConvolution`: the pointwise Bochner twisted convolution of two
  functions `G → A`.
* `TauCeti.CStarAction.bochnerInvolution`: the pointwise twisted involution of a function `G → A`.

## Main statements

* `TauCeti.CStarAction.ConvolutionAlgebra.denseRange_toL1`: `toL1` has dense range in `Lp A 1 μ`.
* `TauCeti.CStarAction.integrable_bochnerConvolution` and
  `TauCeti.CStarAction.toL1Equiv_mul_symm_toL1`: twisted convolution of integrable functions is
  integrable and represents multiplication in the twisted `L¹` completion.
* `TauCeti.CStarAction.integrable_bochnerInvolution` and
  `TauCeti.CStarAction.toL1Equiv_star_symm_toL1`: twisted involution of an integrable function is
  integrable with the same `L¹` norm and represents the involution of the twisted `L¹` completion.
* `TauCeti.CStarAction.ConvolutionAlgebra.toL1Equiv_trivial_mul` and
  `TauCeti.CStarAction.ConvolutionAlgebra.toL1Equiv_trivial_star`: comparison with
  `MeasureTheory.Lp.convolutionL` and `MeasureTheory.Lp.modularInversion` for the trivial action.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs **134**,
  American Mathematical Society (2007), Chapter 2.
-/

public section

noncomputable section

open Filter Function MeasureTheory Topology UniformSpace
open scoped CompactlySupported ENNReal NNReal

namespace TauCeti

namespace CStarAction.ConvolutionAlgebra

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [MeasurableSpace G]

section CompletionLI

variable [OpensMeasurableSpace G] {α : CStarAction G A} {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]

/-- On `toConv f`, `toL1` produces the `L¹` class of `f : C_c(G, A)`. -/
@[simp]
theorem toL1_toConv (f : C_c(G, A)) :
    toL1 (α := α) (μ := μ) (toConv f) = f.integrable.toL1 f :=
  Lp.ext ((coeFn_toL1 (toConv f)).trans f.integrable.coeFn_toL1.symm)

variable (α μ) in
/-- Extend `toL1LI` to a linear isometry from the completion of the compact-support convolution
algebra into Bochner `L¹(G, A, μ)`. When `μ` lacks full support, the completion quotients out the
almost-everywhere zero compactly supported functions. -/
def toL1CompletionLI : Completion (ConvolutionAlgebra α μ) →ₗᵢ[ℂ] Lp A 1 μ :=
  (toL1LI α μ).fromCompletion

/-- On compactly supported convolution coefficients, `toL1CompletionLI` agrees with `toL1`. -/
@[simp]
theorem toL1CompletionLI_coe (f : ConvolutionAlgebra α μ) :
    toL1CompletionLI α μ f = toL1 f :=
  ((toL1LI α μ).fromCompletion_apply_coe f).trans (toL1LI_apply f)

end CompletionLI

section DenseEquiv

variable [R1Space G] [WeaklyLocallyCompactSpace G] [BorelSpace G]
  {α : CStarAction G A} {μ : Measure G} [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- Compactly supported convolution coefficients have dense image in Bochner `L¹(G, A, μ)`,
including for zero or nonunital coefficient algebras and measures without full support. -/
theorem denseRange_toL1 : DenseRange (toL1 (α := α) (μ := μ)) := by
  refine (Lp.dense_setOf_continuous_hasCompactSupport (E := A) (μ := μ)
    ENNReal.one_ne_top).mono ?_
  rintro u ⟨f, hfc, hfs, huf⟩
  let g : C_c(G, A) := ⟨⟨f, hfc⟩, hfs⟩
  exact ⟨toConv g, Lp.ext ((coeFn_toL1 (toConv g)).trans huf.symm)⟩

/-- `toL1LI` has dense range in Bochner `L¹(G, A, μ)`. -/
theorem denseRange_toL1LI : DenseRange (toL1LI α μ) := by
  have hcoe : ⇑(toL1LI α μ) = toL1 (α := α) (μ := μ) := funext toL1LI_apply
  exact hcoe ▸ denseRange_toL1

variable (α μ) in
/-- **Bochner `L¹` realization of the twisted `L¹` completion**: the linear isometric equivalence
identifying `UniformSpace.Completion (ConvolutionAlgebra α μ)` with `Lp A 1 μ` via `toL1`. -/
def toL1Equiv : Completion (ConvolutionAlgebra α μ) ≃ₗᵢ[ℂ] Lp A 1 μ :=
  (toL1LI α μ).fromCompletionEquiv denseRange_toL1LI

/-- As a linear isometry, `toL1Equiv` is `toL1CompletionLI`. -/
@[simp]
theorem toLinearIsometry_toL1Equiv :
    (toL1Equiv α μ).toLinearIsometry = toL1CompletionLI α μ :=
  (toL1LI α μ).toLinearIsometry_fromCompletionEquiv denseRange_toL1LI

/-- Evaluation of `toL1Equiv` agrees with `toL1CompletionLI`. -/
theorem toL1Equiv_apply (x : Completion (ConvolutionAlgebra α μ)) :
    toL1Equiv α μ x = toL1CompletionLI α μ x := by
  rw [← LinearIsometryEquiv.coe_toLinearIsometry, toLinearIsometry_toL1Equiv]

/-- On elements of `ConvolutionAlgebra α μ`, `toL1Equiv` is `toL1`. -/
@[simp]
theorem toL1Equiv_coe (f : ConvolutionAlgebra α μ) :
    toL1Equiv α μ f = toL1 f :=
  ((toL1LI α μ).fromCompletionEquiv_apply_coe denseRange_toL1LI f).trans (toL1LI_apply f)

/-- The inverse of `toL1Equiv` maps `toL1 f` back to the image of `f` in the completion. -/
@[simp]
theorem toL1Equiv_symm_toL1 (f : ConvolutionAlgebra α μ) :
    (toL1Equiv α μ).symm (toL1 f) = f := by
  rw [← toL1LI_apply]
  exact (toL1LI α μ).fromCompletionEquiv_symm_apply_apply denseRange_toL1LI f

/-- For `f : C_c(G, A)`, the inverse of `toL1Equiv` sends `f`'s `L¹` class to `toConv f`. -/
@[simp]
theorem toL1Equiv_symm_ccToL1 (f : C_c(G, A)) :
    (toL1Equiv α μ).symm (f.integrable.toL1 f) =
      ((toConv f : ConvolutionAlgebra α μ) : Completion (ConvolutionAlgebra α μ)) := by
  rw [← toL1_toConv (α := α) (μ := μ), toL1Equiv_symm_toL1]

end DenseEquiv

end CStarAction.ConvolutionAlgebra

namespace CStarAction

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

/-- On compactly supported continuous functions, `bochnerConvolution` agrees with `convolution`. -/
theorem bochnerConvolution_coe_cc [IsTopologicalGroup G] [OpensMeasurableSpace G]
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
theorem bochnerInvolution_coe_cc (α : CStarAction G A) (f : C_c(G, A)) :
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

/-! ### Dominated `L¹` convergence for `C_c` approximations -/

section DominatedL1

variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsLocallyFiniteMeasure μ]

/-- Dominated `L¹` convergence for a sequence `k : ℕ → C_c(G, A)` converging `μ`-almost everywhere
to `h : G → A` with an `L¹` majorant `W : G → ℝ≥0∞`. -/
private theorem integrable_and_tendsto_toL1_of_ae_tendsto {α : CStarAction G A}
    {k : ℕ → C_c(G, A)} {h : G → A} {W : G → ℝ≥0∞} (hW_fin : ∫⁻ s, W s ∂μ ≠ ∞)
    (hk_le : ∀ n s, ‖k n s‖ₑ ≤ W s)
    (hlim : ∀ᵐ s ∂μ, Tendsto (fun n => k n s) atTop (𝓝 (h s))) :
    ∃ hh : Integrable h μ,
      Tendsto (fun n => ConvolutionAlgebra.toL1 (α := α) (ConvolutionAlgebra.toConv (k n)))
        atTop (𝓝 (hh.toL1 h)) := by
  have hh_meas : AEStronglyMeasurable h μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (k n).integrable.aestronglyMeasurable) hlim
  have hh_le : ∀ᵐ s ∂μ, ‖h s‖ₑ ≤ W s := by
    filter_upwards [hlim] with s hs
    exact le_of_tendsto' hs.eNorm fun n => hk_le n s
  have hh : Integrable h μ :=
    ⟨hh_meas, lt_of_le_of_lt (lintegral_mono_ae hh_le) hW_fin.lt_top⟩
  have hh_memLp : MemLp h 1 μ := memLp_one_iff_integrable.2 hh
  refine ⟨hh, ?_⟩
  rw [Lp.ext (hh.coeFn_toL1.trans hh_memLp.coeFn_toLp.symm)]
  refine Lp.tendsto_Lp_of_tendsto_eLpNorm h hh_memLp ?_
  have hcongr (n : ℕ) :
      eLpNorm (⇑(ConvolutionAlgebra.toL1 (α := α) (μ := μ) (ConvolutionAlgebra.toConv (k n))) - h)
        1 μ = ∫⁻ s, ‖k n s - h s‖ₑ ∂μ := by
    have hcoe := ConvolutionAlgebra.coeFn_toL1 (α := α) (μ := μ) (ConvolutionAlgebra.toConv (k n))
    rw [eLpNorm_congr_ae (hcoe.sub EventuallyEq.rfl),
      eLpNorm_one_eq_lintegral_eNorm ((k n).integrable.sub hh).aestronglyMeasurable]
    rfl
  simp_rw [hcongr]
  have hzero : (0 : ℝ≥0∞) = ∫⁻ _ : G, 0 ∂μ := by simp
  rw [hzero]
  refine tendsto_lintegral_of_dominated_convergence' (fun s => 2 * W s)
    (fun n => ((k n).integrable.sub hh).aestronglyMeasurable.eNorm)
    (fun n => ?_) ?_ ?_
  · filter_upwards [hh_le] with s hs
    calc ‖k n s - h s‖ₑ ≤ ‖k n s‖ₑ + ‖h s‖ₑ := eNorm_sub_le
      _ ≤ W s + W s := add_le_add (hk_le n s) hs
      _ = 2 * W s := (two_mul (W s)).symm
  · rw [lintegral_const_mul' 2 _ (by simp)]
    exact (ENNReal.mul_lt_top (by simp) hW_fin.lt_top).ne
  · filter_upwards [hlim] with s hs
    simpa using (hs.sub (tendsto_const_nhds (x := h s))).eNorm

end DominatedL1

/-! ### Bochner twisted convolution and involution for left-invariant measures with `μ.inv ≪ μ` -/

section InvAbsolutelyContinuous

variable [MeasurableSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  (α : CStarAction G A) {μ : Measure G}
  [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

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
      (∀ n r, ‖φ n r‖ₑ ≤ ∑' i, ‖u i r‖ₑ) ∧
      (∀ n t, ‖ψ n t‖ₑ ≤ ∑' j, ‖v j t‖ₑ) ∧
      (∀ n s, ‖α.convolution μ (φ n) (ψ n) s‖ₑ ≤ W s) := by
  let W : G → ℝ≥0∞ := fun s => ∑' p : ℕ × ℕ, ∫⁻ r, ‖u p.1 r‖ₑ * ‖v p.2 (r⁻¹ * s)‖ₑ ∂μ
  have hW_meas_term (p : ℕ × ℕ) :
      Measurable fun s => ∫⁻ r, ‖u p.1 r‖ₑ * ‖v p.2 (r⁻¹ * s)‖ₑ ∂μ := by
    have hsupp : ∀ s r, ‖u p.1 r‖ * ‖v p.2 (r⁻¹ * s)‖ ≠ 0 → r ∈ tsupport (u p.1) :=
      fun _ _ hsr => subset_tsupport _ (mem_support.2 fun hu => hsr (by simp [hu]))
    have hcont : Continuous (uncurry fun s r => ‖u p.1 r‖ * ‖v p.2 (r⁻¹ * s)‖) := by
      rw [uncurry_def]; fun_prop
    have hNcont := continuous_integral_of_compact_support μ (u p.1).hasCompactSupport hcont hsupp
    have heq : (fun s => ∫⁻ r, ‖u p.1 r‖ₑ * ‖v p.2 (r⁻¹ * s)‖ₑ ∂μ) =
        fun s => ENNReal.ofReal (∫ r, ‖u p.1 r‖ * ‖v p.2 (r⁻¹ * s)‖ ∂μ) := by
      ext s
      have hint_s : Integrable (fun r => ‖u p.1 r‖ * ‖v p.2 (r⁻¹ * s)‖) μ :=
        (hcont.comp (.prodMk_right s)).integrable_of_hasCompactSupport
          ((u p.1).hasCompactSupport.mono' fun r hr => hsupp s r hr)
      rw [ofReal_integral_eq_lintegral_ofReal hint_s
        (.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      congr 1 with r
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
    exact heq ▸ ENNReal.measurable_ofReal.comp hNcont.measurable
  have hW_fin : ∫⁻ s, W s ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun p => (hW_meas_term p).aemeasurable]
    simp_rw [lintegral_lintegral_eNorm_mul_inv_mul μ]
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
  have hφ_le (n : ℕ) (r : G) : ‖φ n r‖ₑ ≤ ∑' i, ‖u i r‖ₑ := by
    rw [← hsum_u n, CompactlySupportedContinuousMap.coe_sum, Finset.sum_apply]
    exact (eNorm_sum_le _ _).trans (sum_le_tsum (Finset.range (n + 1)))
  have hψ_le (n : ℕ) (t : G) : ‖ψ n t‖ₑ ≤ ∑' j, ‖v j t‖ₑ := by
    rw [← hsum_v n, CompactlySupportedContinuousMap.coe_sum, Finset.sum_apply]
    exact (eNorm_sum_le _ _).trans (sum_le_tsum (Finset.range (n + 1)))
  refine ⟨W, Measurable.tsum hW_meas_term, hW_fin, hW_eq, hφ_le, hψ_le, fun n s => ?_⟩
  rw [convolution_apply, hW_eq s]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun r => ?_)
  have hprod : ‖φ n r * α r (ψ n (r⁻¹ * s))‖ₑ ≤ ‖φ n r‖ₑ * ‖ψ n (r⁻¹ * s)‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm (φ n r), ← ofReal_norm (ψ n (r⁻¹ * s)),
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      ((norm_mul_le _ _).trans_eq (by rw [StarAlgEquiv.norm_map]))
  exact hprod.trans (mul_le_mul' (hφ_le n r) (hψ_le n (r⁻¹ * s)))

private theorem bochnerConvolution_core (hinv : μ.inv ≪ μ) {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ) ∧
      ∃ hh : Integrable (α.bochnerConvolution μ f g) μ,
        ConvolutionAlgebra.toL1Equiv α μ
          ((ConvolutionAlgebra.toL1Equiv α μ).symm (hf.toL1 f) *
            (ConvolutionAlgebra.toL1Equiv α μ).symm (hg.toL1 g)) =
          hh.toL1 (α.bochnerConvolution μ f g) := by
  obtain ⟨φ, u, hsum_u, hφ_L1, hφ_ae, hu_fin⟩ := hf.exists_sum_compactlySupported_tendsto
  obtain ⟨ψ, v, hsum_v, hψ_L1, hψ_ae, hv_fin⟩ := hg.exists_sum_compactlySupported_tendsto
  obtain ⟨W, hW_meas, hW_fin, hW_eq, hφ_le, hψ_le, hconv_le⟩ :=
    α.exists_bochnerConvolution_majorant hsum_u hsum_v hu_fin hv_fin
  have hU_meas : Measurable fun r => ∑' i, ‖u i r‖ₑ :=
    Measurable.tsum fun i => (u i).continuous.eNorm.measurable
  have hV_meas : Measurable fun t => ∑' j, ‖v j t‖ₑ :=
    Measurable.tsum fun j => (v j).continuous.eNorm.measurable
  -- For `μ`-a.e. `s`, `W s < ∞`, so dominated convergence in `r` applies.
  have hconv_ae : ∀ᵐ s ∂μ,
      Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ ∧
        Tendsto (fun n => α.convolution μ (φ n) (ψ n) s) atTop
          (𝓝 (α.bochnerConvolution μ f g s)) := by
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
      rw [← ENNReal.ofReal_le_iff_le_toReal hr.ne]
      refine (ENNReal.ofReal_le_ofReal
        ((norm_mul_le (φ n r) (α r (ψ n (r⁻¹ * s)))).trans_eq
          (by rw [StarAlgEquiv.norm_map]))).trans ?_
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
      exact mul_le_mul' (hφ_le n r) (hψ_le n (r⁻¹ * s))
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
  obtain ⟨hh, hh_tendsto⟩ := integrable_and_tendsto_toL1_of_ae_tendsto (α := α) hW_fin hconv_le
    (hconv_ae.mono fun _ h => h.2)
  refine ⟨hconv_ae.mono fun _ h => h.1, hh, ?_⟩
  let e := ConvolutionAlgebra.toL1Equiv α μ
  have hmul_tendsto :
      Tendsto (fun n => e ((e.symm ((φ n).integrable.toL1 (φ n))) *
          (e.symm ((ψ n).integrable.toL1 (ψ n))))) atTop
        (𝓝 (e (e.symm (hf.toL1 f) * e.symm (hg.toL1 g)))) :=
    (e.continuous.tendsto _).comp
      (((e.symm.continuous.tendsto _).comp hφ_L1).mul ((e.symm.continuous.tendsto _).comp hψ_L1))
  have hmul_eq (n : ℕ) :
      e ((e.symm ((φ n).integrable.toL1 (φ n))) * (e.symm ((ψ n).integrable.toL1 (ψ n)))) =
        ConvolutionAlgebra.toL1 (α := α)
          (ConvolutionAlgebra.toConv (α.convolution μ (φ n) (ψ n))) := by
    dsimp only [e]
    rw [ConvolutionAlgebra.toL1Equiv_symm_ccToL1, ConvolutionAlgebra.toL1Equiv_symm_ccToL1,
      ← Completion.coe_mul', ConvolutionAlgebra.toL1Equiv_coe]
    rfl
  simp_rw [hmul_eq] at hmul_tendsto
  exact tendsto_nhds_unique hmul_tendsto hh_tendsto

/-- When `μ` is left-invariant and `μ.inv ≪ μ`, the twisted convolution integrand
`r ↦ f r * α r (g (r⁻¹ * s))` is `μ`-integrable for `μ`-almost every `s`. -/
theorem ae_integrable_bochnerConvolution_integrand_of_inv_absolutelyContinuous
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
  (α.bochnerConvolution_core hinv hf hg).1

/-- When `μ` is left-invariant and `μ.inv ≪ μ`, the Bochner twisted convolution of two integrable
functions is integrable. -/
theorem integrable_bochnerConvolution_of_inv_absolutelyContinuous
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (α.bochnerConvolution μ f g) μ :=
  (α.bochnerConvolution_core hinv hf hg).2.choose

/-- Multiplication in the twisted `L¹` completion corresponds under `toL1Equiv` to the `L¹` class
of `bochnerConvolution` on integrable functions, whenever `μ.inv ≪ μ`. -/
theorem toL1Equiv_mul_symm_toL1_of_inv_absolutelyContinuous
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      ((ConvolutionAlgebra.toL1Equiv α μ).symm (hf.toL1 f) *
        (ConvolutionAlgebra.toL1Equiv α μ).symm (hg.toL1 g)) =
      (α.integrable_bochnerConvolution_of_inv_absolutelyContinuous hinv hf hg).toL1
        (α.bochnerConvolution μ f g) :=
  (α.bochnerConvolution_core hinv hf hg).2.choose_spec

/-- Submultiplicativity of the `L¹` norm for `bochnerConvolution` of integrable functions when
`μ.inv ≪ μ`. -/
theorem integral_norm_bochnerConvolution_le_of_inv_absolutelyContinuous
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ s, ‖α.bochnerConvolution μ f g s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := by
  have hint := α.integrable_bochnerConvolution_of_inv_absolutelyContinuous hinv hf hg
  rw [← L1.norm_of_fun_eq_integral_norm hint, ← L1.norm_of_fun_eq_integral_norm hf,
    ← L1.norm_of_fun_eq_integral_norm hg,
    ← α.toL1Equiv_mul_symm_toL1_of_inv_absolutelyContinuous hinv hf hg,
    LinearIsometryEquiv.norm_map]
  exact (norm_mul_le _ _).trans_eq (by simp)

private theorem bochnerInvolution_core (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    ∃ hh : Integrable (α.bochnerInvolution f) μ,
      ConvolutionAlgebra.toL1Equiv α μ
        (star ((ConvolutionAlgebra.toL1Equiv α μ).symm (hf.toL1 f))) =
        hh.toL1 (α.bochnerInvolution f) := by
  obtain ⟨φ, u, hsum_u, hφ_L1, hφ_ae, hu_fin⟩ := hf.exists_sum_compactlySupported_tendsto
  -- Each `w k = α.twistedInvolution (u k)` has the same `L¹` norm as `u k`.
  let w : ℕ → C_c(G, A) := fun k => α.twistedInvolution (u k)
  let W : G → ℝ≥0∞ := fun s => ∑' k, ‖w k s‖ₑ
  have hw_int (k : ℕ) : ∫⁻ s, ‖w k s‖ₑ ∂μ = ∫⁻ s, ‖u k s‖ₑ ∂μ := by
    rw [← ofReal_integral_norm_eq_lintegral_eNorm (w k).integrable,
      ← ofReal_integral_norm_eq_lintegral_eNorm (u k).integrable]
    have hnorm := ConvolutionAlgebra.norm_star (α := α) (μ := μ)
      (ConvolutionAlgebra.toConv (u k))
    simp only [ConvolutionAlgebra.norm_eq_integral_norm, ConvolutionAlgebra.ofConv_star] at hnorm
    exact congrArg ENNReal.ofReal hnorm
  have hW_fin : ∫⁻ s, W s ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun k => (w k).integrable.aestronglyMeasurable.eNorm]
    simpa only [hw_int] using hu_fin
  have hk_le (n : ℕ) (s : G) : ‖α.twistedInvolution (φ n) s‖ₑ ≤ W s := by
    have hsum_s : α.twistedInvolution (φ n) s = ∑ i ∈ Finset.range (n + 1), w i s := by
      rw [← hsum_u n, map_sum, CompactlySupportedContinuousMap.coe_sum, Finset.sum_apply]
    rw [hsum_s]
    exact (eNorm_sum_le _ _).trans (sum_le_tsum (Finset.range (n + 1)))
  have hinv_qmp : QuasiMeasurePreserving Inv.inv μ μ := ⟨measurable_inv.aemeasurable, hinv⟩
  have hlim : ∀ᵐ s ∂μ,
      Tendsto (fun n => α.twistedInvolution (φ n) s) atTop (𝓝 (α.bochnerInvolution f s)) := by
    filter_upwards [hinv_qmp.ae hφ_ae] with s hs
    have hcont : Continuous fun a : A => ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star a) :=
      continuous_const.smul ((StarAlgEquiv.isometry (α s)).continuous.comp continuous_star)
    simpa only [Function.comp_def, twistedInvolution_apply, bochnerInvolution_apply] using
      (hcont.tendsto (f s⁻¹)).comp hs
  obtain ⟨hh, hh_tendsto⟩ := integrable_and_tendsto_toL1_of_ae_tendsto (α := α) hW_fin hk_le hlim
  refine ⟨hh, ?_⟩
  let e := ConvolutionAlgebra.toL1Equiv α μ
  have hstar_tendsto :
      Tendsto (fun n => e (star (e.symm ((φ n).integrable.toL1 (φ n))))) atTop
        (𝓝 (e (star (e.symm (hf.toL1 f))))) :=
    (e.continuous.tendsto _).comp ((continuous_star.tendsto _).comp
      ((e.symm.continuous.tendsto _).comp hφ_L1))
  have hstar_eq (n : ℕ) :
      e (star (e.symm ((φ n).integrable.toL1 (φ n)))) =
        ConvolutionAlgebra.toL1 (α := α)
          (ConvolutionAlgebra.toConv (α.twistedInvolution (φ n))) := by
    dsimp only [e]
    rw [ConvolutionAlgebra.toL1Equiv_symm_ccToL1, ← Completion.coe_star,
      ConvolutionAlgebra.toL1Equiv_coe]
    rfl
  simp_rw [hstar_eq] at hstar_tendsto
  exact tendsto_nhds_unique hstar_tendsto hh_tendsto

/-- When `μ` is left-invariant and `μ.inv ≪ μ`, the twisted involution `bochnerInvolution f` of an
integrable function `f` is integrable. -/
theorem integrable_bochnerInvolution_of_inv_absolutelyContinuous
    (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    Integrable (α.bochnerInvolution f) μ :=
  (α.bochnerInvolution_core hinv hf).choose

/-- Involution in the twisted `L¹` completion corresponds under `toL1Equiv` to the `L¹` class of
`bochnerInvolution` on integrable functions, whenever `μ.inv ≪ μ`. -/
theorem toL1Equiv_star_symm_toL1_of_inv_absolutelyContinuous
    (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      (star ((ConvolutionAlgebra.toL1Equiv α μ).symm (hf.toL1 f))) =
      (α.integrable_bochnerInvolution_of_inv_absolutelyContinuous hinv hf).toL1
        (α.bochnerInvolution f) :=
  (α.bochnerInvolution_core hinv hf).choose_spec

/-- The twisted involution preserves the `L¹` norm of any integrable function when `μ.inv ≪ μ`. -/
theorem integral_norm_bochnerInvolution_of_inv_absolutelyContinuous
    (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    ∫ s, ‖α.bochnerInvolution f s‖ ∂μ = ∫ s, ‖f s‖ ∂μ := by
  have hint := α.integrable_bochnerInvolution_of_inv_absolutelyContinuous hinv hf
  rw [← L1.norm_of_fun_eq_integral_norm hint, ← L1.norm_of_fun_eq_integral_norm hf,
    ← α.toL1Equiv_star_symm_toL1_of_inv_absolutelyContinuous hinv hf,
    LinearIsometryEquiv.norm_map, norm_star, LinearIsometryEquiv.norm_map]

/-- For elements `u, v : Lp A 1 μ`, the product of their preimages in the twisted `L¹` completion
is represented `μ`-almost everywhere by `α.bochnerConvolution μ u v`. -/
theorem coeFn_toL1Equiv_mul_of_inv_absolutelyContinuous
    (hinv : μ.inv ≪ μ) (u v : Lp A 1 μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      ((ConvolutionAlgebra.toL1Equiv α μ).symm u *
        (ConvolutionAlgebra.toL1Equiv α μ).symm v) =ᵐ[μ]
      α.bochnerConvolution μ u v := by
  have hu : (L1.integrable_coeFn u).toL1 u = u := Integrable.toL1_coeFn u (L1.integrable_coeFn u)
  have hv : (L1.integrable_coeFn v).toL1 v = v := Integrable.toL1_coeFn v (L1.integrable_coeFn v)
  conv_lhs => rw [← hu, ← hv]
  rw [α.toL1Equiv_mul_symm_toL1_of_inv_absolutelyContinuous hinv
    (L1.integrable_coeFn u) (L1.integrable_coeFn v)]
  exact Integrable.coeFn_toL1 _

/-- For `u : Lp A 1 μ`, the star of its preimage in the twisted `L¹` completion is represented
`μ`-almost everywhere by `α.bochnerInvolution u`. -/
theorem coeFn_toL1Equiv_star_of_inv_absolutelyContinuous
    (hinv : μ.inv ≪ μ) (u : Lp A 1 μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      (star ((ConvolutionAlgebra.toL1Equiv α μ).symm u)) =ᵐ[μ]
      α.bochnerInvolution u := by
  have hu : (L1.integrable_coeFn u).toL1 u = u := Integrable.toL1_coeFn u (L1.integrable_coeFn u)
  conv_lhs => rw [← hu]
  rw [α.toL1Equiv_star_symm_toL1_of_inv_absolutelyContinuous hinv (L1.integrable_coeFn u)]
  exact Integrable.coeFn_toL1 _

end InvAbsolutelyContinuous

/-! ### Specializations to inner regular and regular Haar measures -/

section InnerRegularHaar

variable [MeasurableSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  (α : CStarAction G A) {μ : Measure G} [μ.IsHaarMeasure] [μ.InnerRegular]

/-- For an inner regular Haar measure, the twisted convolution integrand
`r ↦ f r * α r (g (r⁻¹ * s))` is `μ`-integrable for `μ`-almost every `s`. -/
theorem ae_integrable_bochnerConvolution_integrand {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
  α.ae_integrable_bochnerConvolution_integrand_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_innerRegular hf hg

/-- For an inner regular Haar measure, the Bochner twisted convolution of integrable functions is
integrable. -/
theorem integrable_bochnerConvolution {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (α.bochnerConvolution μ f g) μ :=
  α.integrable_bochnerConvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_innerRegular hf hg

/-- For an inner regular Haar measure, multiplication in the twisted `L¹` completion corresponds
under `toL1Equiv` to the `L¹` class of `bochnerConvolution`. -/
theorem toL1Equiv_mul_symm_toL1 {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      ((ConvolutionAlgebra.toL1Equiv α μ).symm (hf.toL1 f) *
        (ConvolutionAlgebra.toL1Equiv α μ).symm (hg.toL1 g)) =
      (α.integrable_bochnerConvolution hf hg).toL1 (α.bochnerConvolution μ f g) :=
  α.toL1Equiv_mul_symm_toL1_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_innerRegular hf hg

/-- Submultiplicativity of the `L¹` norm for `bochnerConvolution` against an inner regular Haar
measure. -/
theorem integral_norm_bochnerConvolution_le {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ s, ‖α.bochnerConvolution μ f g s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ :=
  α.integral_norm_bochnerConvolution_le_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_innerRegular hf hg

/-- For an inner regular Haar measure, the twisted involution of an integrable function is
integrable. -/
theorem integrable_bochnerInvolution {f : G → A} (hf : Integrable f μ) :
    Integrable (α.bochnerInvolution f) μ :=
  α.integrable_bochnerInvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_innerRegular hf

/-- For an inner regular Haar measure, involution in the twisted `L¹` completion corresponds under
`toL1Equiv` to the `L¹` class of `bochnerInvolution`. -/
theorem toL1Equiv_star_symm_toL1 {f : G → A} (hf : Integrable f μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      (star ((ConvolutionAlgebra.toL1Equiv α μ).symm (hf.toL1 f))) =
      (α.integrable_bochnerInvolution hf).toL1 (α.bochnerInvolution f) :=
  α.toL1Equiv_star_symm_toL1_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_innerRegular hf

/-- For an inner regular Haar measure, `bochnerInvolution` preserves the `L¹` norm. -/
theorem integral_norm_bochnerInvolution {f : G → A} (hf : Integrable f μ) :
    ∫ s, ‖α.bochnerInvolution f s‖ ∂μ = ∫ s, ‖f s‖ ∂μ :=
  α.integral_norm_bochnerInvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_innerRegular hf

/-- Almost-everywhere formula for multiplication in the twisted `L¹` completion for an inner
regular Haar measure. -/
theorem coeFn_toL1Equiv_mul (u v : Lp A 1 μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      ((ConvolutionAlgebra.toL1Equiv α μ).symm u *
        (ConvolutionAlgebra.toL1Equiv α μ).symm v) =ᵐ[μ]
      α.bochnerConvolution μ u v :=
  α.coeFn_toL1Equiv_mul_of_inv_absolutelyContinuous μ.inv_absolutelyContinuous_of_innerRegular u v

/-- Almost-everywhere formula for involution in the twisted `L¹` completion for an inner regular
Haar measure. -/
theorem coeFn_toL1Equiv_star (u : Lp A 1 μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      (star ((ConvolutionAlgebra.toL1Equiv α μ).symm u)) =ᵐ[μ]
      α.bochnerInvolution u :=
  α.coeFn_toL1Equiv_star_of_inv_absolutelyContinuous μ.inv_absolutelyContinuous_of_innerRegular u

end InnerRegularHaar

section RegularHaar

variable [MeasurableSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  (α : CStarAction G A) {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

/-- For a regular Haar measure, the twisted convolution integrand `r ↦ f r * α r (g (r⁻¹ * s))`
is `μ`-integrable for `μ`-almost every `s`. -/
theorem ae_integrable_bochnerConvolution_integrand_of_regular {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ s ∂μ, Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
  α.ae_integrable_bochnerConvolution_integrand_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_regular hf hg

/-- For a regular Haar measure, the Bochner twisted convolution of integrable functions is
integrable. -/
theorem integrable_bochnerConvolution_of_regular {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (α.bochnerConvolution μ f g) μ :=
  α.integrable_bochnerConvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_regular hf hg

/-- For a regular Haar measure, multiplication in the twisted `L¹` completion corresponds under
`toL1Equiv` to the `L¹` class of `bochnerConvolution`. -/
theorem toL1Equiv_mul_symm_toL1_of_regular {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      ((ConvolutionAlgebra.toL1Equiv α μ).symm (hf.toL1 f) *
        (ConvolutionAlgebra.toL1Equiv α μ).symm (hg.toL1 g)) =
      (α.integrable_bochnerConvolution_of_regular hf hg).toL1 (α.bochnerConvolution μ f g) :=
  α.toL1Equiv_mul_symm_toL1_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_regular hf hg

/-- Submultiplicativity of the `L¹` norm for `bochnerConvolution` against a regular Haar
measure. -/
theorem integral_norm_bochnerConvolution_le_of_regular {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ s, ‖α.bochnerConvolution μ f g s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ :=
  α.integral_norm_bochnerConvolution_le_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_regular hf hg

/-- For a regular Haar measure, the twisted involution of an integrable function is integrable. -/
theorem integrable_bochnerInvolution_of_regular {f : G → A} (hf : Integrable f μ) :
    Integrable (α.bochnerInvolution f) μ :=
  α.integrable_bochnerInvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_regular hf

/-- For a regular Haar measure, involution in the twisted `L¹` completion corresponds under
`toL1Equiv` to the `L¹` class of `bochnerInvolution`. -/
theorem toL1Equiv_star_symm_toL1_of_regular {f : G → A} (hf : Integrable f μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      (star ((ConvolutionAlgebra.toL1Equiv α μ).symm (hf.toL1 f))) =
      (α.integrable_bochnerInvolution_of_regular hf).toL1 (α.bochnerInvolution f) :=
  α.toL1Equiv_star_symm_toL1_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_regular hf

/-- For a regular Haar measure, `bochnerInvolution` preserves the `L¹` norm. -/
theorem integral_norm_bochnerInvolution_of_regular {f : G → A} (hf : Integrable f μ) :
    ∫ s, ‖α.bochnerInvolution f s‖ ∂μ = ∫ s, ‖f s‖ ∂μ :=
  α.integral_norm_bochnerInvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_regular hf

/-- Almost-everywhere formula for multiplication in the twisted `L¹` completion for a regular Haar
measure. -/
theorem coeFn_toL1Equiv_mul_of_regular (u v : Lp A 1 μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      ((ConvolutionAlgebra.toL1Equiv α μ).symm u *
        (ConvolutionAlgebra.toL1Equiv α μ).symm v) =ᵐ[μ]
      α.bochnerConvolution μ u v :=
  α.coeFn_toL1Equiv_mul_of_inv_absolutelyContinuous μ.inv_absolutelyContinuous_of_regular u v

/-- Almost-everywhere formula for involution in the twisted `L¹` completion for a regular Haar
measure. -/
theorem coeFn_toL1Equiv_star_of_regular (u : Lp A 1 μ) :
    ConvolutionAlgebra.toL1Equiv α μ
      (star ((ConvolutionAlgebra.toL1Equiv α μ).symm u)) =ᵐ[μ]
      α.bochnerInvolution u :=
  α.coeFn_toL1Equiv_star_of_inv_absolutelyContinuous μ.inv_absolutelyContinuous_of_regular u

end RegularHaar

/-! ### Trivial-action comparison with `Lp.convolutionL` and `Lp.modularInversion` -/

namespace ConvolutionAlgebra

section TrivialMul

variable [MeasurableSpace G] [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] [BorelSpace G]
  (μ : Measure G) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

/-- For the trivial action on `ℂ`, `toL1Equiv` intertwines multiplication in the twisted `L¹`
completion with scalar group convolution `MeasureTheory.Lp.convolutionL`. -/
theorem toL1Equiv_trivial_mul
    (x y : Completion (ConvolutionAlgebra (CStarAction.trivial (G := G) (A := ℂ)) μ)) :
    toL1Equiv (CStarAction.trivial (G := G) (A := ℂ)) μ (x * y) =
      Lp.convolutionL μ 1 ENNReal.one_ne_top
        (toL1Equiv (CStarAction.trivial (G := G) (A := ℂ)) μ x)
        (toL1Equiv (CStarAction.trivial (G := G) (A := ℂ)) μ y) := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f g =>
    rw [← Completion.coe_mul', toL1Equiv_coe, toL1Equiv_coe, toL1Equiv_coe]
    have hf : toL1 f = f.ofConv.integrable.toL1 f.ofConv :=
      Lp.ext ((coeFn_toL1 f).trans f.ofConv.integrable.coeFn_toL1.symm)
    have hg : toL1 g = g.ofConv.integrable.toL1 g.ofConv :=
      Lp.ext ((coeFn_toL1 g).trans g.ofConv.integrable.coeFn_toL1.symm)
    rw [hf, hg]
    refine Lp.ext ((coeFn_toL1 (f * g)).trans ?_)
    refine EventuallyEq.trans (.of_forall fun s => ?_)
      (Lp.convolutionL_toL1_ae_eq (μ := μ) f.ofConv.continuous f.ofConv.hasCompactSupport
        g.ofConv.continuous g.ofConv.hasCompactSupport).symm
    simp [ofConv_mul]

/-- Transported form of `toL1Equiv_trivial_mul` on classes `u, v : Lp ℂ 1 μ`. -/
theorem toL1Equiv_symm_convolutionL (u v : Lp ℂ 1 μ) :
    (toL1Equiv (CStarAction.trivial (G := G) (A := ℂ)) μ).symm
      (Lp.convolutionL μ 1 ENNReal.one_ne_top u v) =
      (toL1Equiv (CStarAction.trivial (G := G) (A := ℂ)) μ).symm u *
        (toL1Equiv (CStarAction.trivial (G := G) (A := ℂ)) μ).symm v := by
  apply (toL1Equiv (CStarAction.trivial (G := G) (A := ℂ)) μ).injective
  simp [toL1Equiv_trivial_mul]

end TrivialMul

section TrivialStar

variable [MeasurableSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- For the trivial action on any C⋆-algebra `A` (in particular `A = ℂ`), `toL1Equiv` intertwines
the involution of the twisted `L¹` completion with pointwise star followed by
`MeasureTheory.Lp.modularInversion`. -/
theorem toL1Equiv_trivial_star
    (x : Completion (ConvolutionAlgebra (CStarAction.trivial (G := G) (A := A)) μ)) :
    toL1Equiv (CStarAction.trivial (G := G) (A := A)) μ (star x) =
      Lp.modularInversion μ 1 ℂ
        (star (toL1Equiv (CStarAction.trivial (G := G) (A := A)) μ x)) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    rw [← Completion.coe_star, toL1Equiv_coe, toL1Equiv_coe]
    refine Lp.ext ?_
    filter_upwards [coeFn_toL1 (star f),
      Lp.coeFn_modularInversion (𝕜 := ℂ) (star (toL1 f)),
      (μ.quasiMeasurePreserving_inv_of_regular).ae
        ((Lp.coeFn_star (toL1 f)).trans (coeFn_toL1 f).star)] with s h₁ h₂ h₃
    rw [h₁, h₂]
    simp only [ofConv_star, twistedInvolution_apply, trivial_apply, ENNReal.toReal_one, inv_one,
      Real.rpow_one, Complex.coe_smul]
    exact congrArg ((Measure.modularCharacter s : ℝ) • ·) h₃.symm

end TrivialStar

end ConvolutionAlgebra

end CStarAction

end TauCeti
