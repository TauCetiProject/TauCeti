/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Ring.Completion
public import TauCeti.MeasureTheory.Function.Lp.Operator.Multiplication
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Group.Convolution.Support

/-!
# Realizing the cocycle-twisted `L¹` Banach ⋆-algebra in Bochner `L¹`

Let `α : CStarAction G A` be a point-norm continuous action of a topological group `G` on a
possibly nonunital complex C⋆-algebra `A`, and let `ω : CentralCocycle α` be a normalized
continuous central multiplier cocycle. By `TauCeti.CompactlySupportedL1`, when `G` is a weakly
locally compact `R₁` Borel space and `μ` is finite on compact sets and inner regular for compact
sets on sets of finite measure (`IsFiniteMeasureOnCompacts μ` and `μ.InnerRegularCompactLTTop`),
`CompactlySupportedL1.completionEquivL1 ω A μ ℂ` identifies the abstract completion
`UniformSpace.Completion (TwistedConvolutionAlgebra ω μ)` isometrically with Bochner `Lp A 1 μ`.

Here we construct the concrete cocycle-twisted operations on `Lp A 1 μ` and prove that they match
multiplication and star on `Completion (TwistedConvolutionAlgebra ω μ)` across `completionEquivL1`:

* `CentralCocycle.convolutionL1`: cocycle-twisted `L¹` convolution on `Lp A 1 μ`, defined for any
  left-invariant Borel measure finite on compact sets and inner regular on finite-measure sets on a
  weakly locally compact topological group (without `LocallyCompactSpace` or Haar full support) as
  the `Lp A 1 μ`-valued Bochner integral
  `f ⋆_{α, ω} g = ∫ r, M_r ((mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)) ∂μ`, where `M_r` is
  `Lp.strongOperatorMultiplication` by `s ↦ (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd`. We also
  provide representative-independent formulas (`convolutionL1_eq_integral_of_ae_eq`,
  `convolutionL1_toL1`, `convolutionL1_toLp_ae_eq`), associativity, submultiplicativity, and the
  trivial-cocycle reduction `one_convolutionL1`.
* `CentralCocycle.involutionL1`: cocycle-twisted `L¹` involution on `Lp A 1 μ` as a conjugate-linear
  isometric equivalence for locally compact `G`, reversing `convolutionL1`, agreeing with `star` on
  `Completion (TwistedConvolutionAlgebra ω μ)` and `C_c(G, A)`, reducing to
  `CStarAction.twistedInvolutionL1` at `ω = 1`, acting pointwise via
  `Lp.strongOperatorMultiplication` on `α.twistedInvolutionL1`
  (`coeFn_involutionL1_eq_twistedInvolutionL1`), and represented almost everywhere for a regular
  Haar measure by `s ↦ c(s) • (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f s⁻¹)))`
  (`coeFn_involutionL1`, `coeFn_involutionL1_of_ae_eq`, `involutionL1_toL1_ae_eq`).

## References

* Judith A. Packer and Iain Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc.
  Cambridge Philos. Soc. 106 (1989), 293–311, Section 2.
* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 2.
-/

public section

noncomputable section

open Filter Function MeasureTheory UniformSpace
open scoped ENNReal CompactlySupported MultiplierAlgebra

namespace TauCeti.CStarAction

section ConvolutionL1

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} (ω : CentralCocycle α) {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

omit [WeaklyLocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] in
private theorem norm_mulSnd_compLp_le (a : A) (r : G) (g : Lp A 1 μ) :
    ‖Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
        (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
        (fun _ => ω.continuous_snd_apply continuous_const
          (continuous_const.inv.mul continuous_id) continuous_const)
        ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
        ((ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ 1 r g))‖ ≤ ‖a‖ * ‖g‖ := by
  let M : Lp A 1 μ →L[ℂ] Lp A 1 μ :=
    Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
      (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
      (fun _ => ω.continuous_snd_apply continuous_const
        (continuous_const.inv.mul continuous_id) continuous_const)
      ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
  have hM : ‖M‖ ≤ 1 :=
    Lp.norm_strongOperatorMultiplication_le μ ENNReal.one_ne_top
      (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
      (fun _ => ω.continuous_snd_apply continuous_const
        (continuous_const.inv.mul continuous_id) continuous_const)
      ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
      zero_le_one fun _ => DoubleCentralizer.norm_unitary_snd_le_one _
  calc
    ‖M ((ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ 1 r g))‖ ≤
        1 * ‖(ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ 1 r g)‖ :=
      M.le_of_opNorm_le hM _
    _ ≤ ‖ContinuousLinearMap.mul ℂ A a‖ * ‖α.translateLp μ 1 r g‖ := by
      rw [one_mul]
      exact ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ ‖a‖ * ‖g‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le ℂ A a)
        (norm_nonneg g)

/-- The `Lp A 1 μ`-valued integrand of cocycle-twisted `L¹` convolution is Bochner integrable
against any left-invariant Borel measure finite on compact sets and inner regular on
finite-measure sets, without `LocallyCompactSpace` or full support. -/
theorem CentralCocycle.integrable_mul_translateLp {f : G → A} (hf : Integrable f μ)
    (g : Lp A 1 μ) :
    Integrable (fun r =>
      Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
        (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
        (fun _ => ω.continuous_snd_apply continuous_const
          (continuous_const.inv.mul continuous_id) continuous_const)
        ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
        ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g))) μ := by
  let F : G → G → A →L[ℂ] A := fun r s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd
  have hF : ∀ v : A, Continuous fun q : G × G => F q.1 q.2 v := fun _ =>
    ω.continuous_snd_apply continuous_fst (continuous_fst.inv.mul continuous_snd) continuous_const
  let M (r : G) : Lp A 1 μ →L[ℂ] Lp A 1 μ :=
    Lp.strongOperatorMultiplication μ ENNReal.one_ne_top (F r)
      (fun v => (hF v).comp (continuous_const.prodMk continuous_id))
      ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
  have hmeas : AEStronglyMeasurable
      (fun r => M r ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g))) μ :=
    (α.integrable_mul_translateLp hf g).aefinStronglyMeasurable
      |>.aestronglyMeasurable_apply_continuous
      (fun v => Lp.continuous_strongOperatorMultiplication_apply μ ENNReal.one_ne_top F hF
        (fun _ _ => DoubleCentralizer.norm_unitary_snd_le_one _) v)
      (fun r => (M r).continuous)
      (fun r => map_zero (M r))
  exact (hf.norm.mul_const ‖g‖).mono' hmeas
    (.of_forall fun r => norm_mulSnd_compLp_le ω (f r) r g)

omit [WeaklyLocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] in
private theorem norm_integral_mulSnd_compLp_le (f g : Lp A 1 μ) :
    ‖∫ r, Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
        (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
        (fun _ => ω.continuous_snd_apply continuous_const
          (continuous_const.inv.mul continuous_id) continuous_const)
        ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
        ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)) ∂μ‖ ≤
      ‖f‖ * ‖g‖ := by
  rw [L1.norm_eq_integral_norm f, ← integral_mul_const]
  exact norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.mul_const _)
    (.of_forall fun r => norm_mulSnd_compLp_le ω (f r) r g)

namespace CentralCocycle

variable (μ) in
/-- **Cocycle-twisted `L¹` convolution** on `Lp A 1 μ`, defined as the continuous bilinear map
`Lp A 1 μ →L[ℂ] Lp A 1 μ →L[ℂ] Lp A 1 μ` integrating the cocycle-twisted left translates. -/
def convolutionL1 : Lp A 1 μ →L[ℂ] Lp A 1 μ →L[ℂ] Lp A 1 μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun (f g : Lp A 1 μ) =>
        ∫ r, Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
          (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
          (fun _ => ω.continuous_snd_apply continuous_const
            (continuous_const.inv.mul continuous_id) continuous_const)
          ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
          ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)) ∂μ)
      (fun f₁ f₂ g => by
        rw [← integral_add (ω.integrable_mul_translateLp (L1.integrable_coeFn f₁) g)
          (ω.integrable_mul_translateLp (L1.integrable_coeFn f₂) g)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f₁ f₂] with r hr
        rw [hr, Pi.add_apply, map_add, ContinuousLinearMap.add_compLp, map_add])
      (fun c f g => by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with r hr
        rw [hr, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_compLp, map_smul])
      (fun f g₁ g₂ => by
        rw [← integral_add (ω.integrable_mul_translateLp (L1.integrable_coeFn f) g₁)
          (ω.integrable_mul_translateLp (L1.integrable_coeFn f) g₂)]
        refine integral_congr_ae (.of_forall fun r => ?_)
        dsimp only
        rw [map_add, ← ContinuousLinearMap.compLpL₂_apply_apply (p := 1) (μ := μ), map_add,
          ContinuousLinearMap.compLpL₂_apply_apply, ContinuousLinearMap.compLpL₂_apply_apply,
          map_add])
      (fun c f g => by
        rw [← integral_smul]
        refine integral_congr_ae (.of_forall fun r => ?_)
        dsimp only
        rw [map_smul, ← ContinuousLinearMap.compLpL₂_apply_apply (p := 1) (μ := μ), map_smul,
          ContinuousLinearMap.compLpL₂_apply_apply, map_smul]))
    1 fun f g => by simpa using norm_integral_mulSnd_compLp_le ω f g

/-- The defining `Lp A 1 μ`-valued Bochner integral for cocycle-twisted `L¹` convolution. -/
theorem convolutionL1_apply (f g : Lp A 1 μ) :
    ω.convolutionL1 μ f g =
      ∫ r, Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
        (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
        (fun _ => ω.continuous_snd_apply continuous_const
          (continuous_const.inv.mul continuous_id) continuous_const)
        ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
        ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)) ∂μ :=
  (rfl)

/-- Representative-independent Bochner integral formula for cocycle-twisted `L¹` convolution:
if `f =ᵐ[μ] f₀`, `f` may be replaced by `f₀` in the outer integral. -/
theorem convolutionL1_eq_integral_of_ae_eq {f₀ : G → A} {f g : Lp A 1 μ} (hf₀ : f =ᵐ[μ] f₀) :
    ω.convolutionL1 μ f g =
      ∫ r, Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
        (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
        (fun _ => ω.continuous_snd_apply continuous_const
          (continuous_const.inv.mul continuous_id) continuous_const)
        ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
        ((ContinuousLinearMap.mul ℂ A (f₀ r)).compLp (α.translateLp μ 1 r g)) ∂μ := by
  rw [convolutionL1_apply]
  refine integral_congr_ae ?_
  filter_upwards [hf₀] with r hr
  rw [hr]

/-- Cocycle-twisted `L¹` convolution of the `L¹` class of an integrable function `f₀` with `g`. -/
theorem convolutionL1_toL1 {f₀ : G → A} (hf₀ : Integrable f₀ μ) (g : Lp A 1 μ) :
    ω.convolutionL1 μ (hf₀.toL1 f₀) g =
      ∫ r, Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
        (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
        (fun _ => ω.continuous_snd_apply continuous_const
          (continuous_const.inv.mul continuous_id) continuous_const)
        ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
        ((ContinuousLinearMap.mul ℂ A (f₀ r)).compLp (α.translateLp μ 1 r g)) ∂μ :=
  ω.convolutionL1_eq_integral_of_ae_eq hf₀.coeFn_toL1

/-- **Submultiplicativity of cocycle-twisted `L¹` convolution**:
`‖f ⋆_{α, ω} g‖₁ ≤ ‖f‖₁ * ‖g‖₁`. -/
theorem norm_convolutionL1_apply_le (f g : Lp A 1 μ) :
    ‖ω.convolutionL1 μ f g‖ ≤ ‖f‖ * ‖g‖ :=
  norm_integral_mulSnd_compLp_le ω f g

/-- Cocycle-twisted `L¹` convolution has operator norm at most `1` as a bilinear map, including
zero algebras and the zero measure. -/
theorem norm_convolutionL1_le : ‖ω.convolutionL1 μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun f g => by
    simpa using ω.norm_convolutionL1_apply_le f g

/-- On compactly supported continuous coefficient functions, `convolutionL1` is represented almost
everywhere by the pointwise twisted convolution integral
`s ↦ ∫ r, (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ`. -/
theorem convolutionL1_toLp_ae_eq (f g : C_c(G, A)) :
    ω.convolutionL1 μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ f)
        (CompactlySupportedContinuousMap.toLp 1 μ ℂ g) =ᵐ[μ]
      ω.convolution μ f g := by
  set F : G → G → A := fun s r =>
    (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s)))
  have hFc : Continuous (uncurry F) := by
    rw [uncurry_def]
    fun_prop
  have hFsupp (s r : G) (hsr : F s r ≠ 0) : r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
    mem_tsupport_and_inv_mul_mem_tsupport hsr (fun h => by simp [F, h])
      (fun h => by simp [F, h])
  have hFs : HasCompactSupport (uncurry F) :=
    hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport hFsupp
  refine (L1.integrable_coeFn _).ae_eq_of_forall_setIntegral_eq _ _
    (ω.convolution μ f g).integrable fun s _ hμs => ?_
  have hinner (r : G) :
      ∫ x in s, (Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
          (fun t => (ω.value r (r⁻¹ * t) : 𝓜(ℂ, A)).snd)
          (fun _ => ω.continuous_snd_apply continuous_const
            (continuous_const.inv.mul continuous_id) continuous_const)
          ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
          ((ContinuousLinearMap.mul ℂ A (f r)).compLp
            (α.translateLp μ 1 r (CompactlySupportedContinuousMap.toLp 1 μ ℂ g))) : G → A) x ∂μ =
        ∫ x in s, F x r ∂μ := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [Lp.strongOperatorMultiplication_ae (𝕜 := ℂ) (E := A) (E' := A) μ
        ENNReal.one_ne_top _ _ _
        ((ContinuousLinearMap.mul ℂ A (f r)).compLp
          (α.translateLp μ 1 r (CompactlySupportedContinuousMap.toLp 1 μ ℂ g))),
      (ContinuousLinearMap.mul ℂ A (f r)).coeFn_compLp
        (α.translateLp μ 1 r (CompactlySupportedContinuousMap.toLp 1 μ ℂ g)),
      α.coeFn_translateLp r (CompactlySupportedContinuousMap.toLp 1 μ ℂ g),
      (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
        (CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ g)]
      with x h₀ h₁ h₂ h₃
    rw [h₀, h₁, ContinuousLinearMap.mul_apply', h₂, h₃]
  rw [← Set.setIntegralLp_apply (𝕜 := ℂ) s hμs, ω.convolutionL1_apply,
    ← (Set.setIntegralLp (𝕜 := ℂ) s hμs).integral_comp_comm
      (ω.integrable_mul_translateLp (L1.integrable_coeFn _) _)]
  simp_rw [Set.setIntegralLp_apply, convolution_apply]
  refine (integral_congr_ae ?_).trans
    (integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := μ.restrict s)
      (f := fun r x => F x r) (hFc.comp continuous_swap)
      (hFs.comp_homeomorph (Homeomorph.prodComm G G)))
  filter_upwards [CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ f] with r hr
  rw [hr, hinner r]

@[simp]
theorem convolutionL1_toLp (f g : C_c(G, A)) :
    ω.convolutionL1 μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ f)
        (CompactlySupportedContinuousMap.toLp 1 μ ℂ g) =
      CompactlySupportedContinuousMap.toLp 1 μ ℂ (ω.convolution μ f g) :=
  Lp.ext ((ω.convolutionL1_toLp_ae_eq f g).trans
    (CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ
      (ω.convolution μ f g)).symm)

end CentralCocycle

namespace TwistedConvolutionAlgebra

/-- `CompactlySupportedL1.toL1 ℂ` turns the cocycle-twisted convolution product into
`CentralCocycle.convolutionL1`. -/
@[simp]
theorem toL1_mul (f g : TwistedConvolutionAlgebra ω μ) :
    CompactlySupportedL1.toL1 ℂ (f * g) =
      ω.convolutionL1 μ (CompactlySupportedL1.toL1 ℂ f) (CompactlySupportedL1.toL1 ℂ g) := by
  rw [CompactlySupportedL1.toL1_eq_toLp ℂ, CompactlySupportedL1.toL1_eq_toLp ℂ,
    CompactlySupportedL1.toL1_eq_toLp ℂ]
  simpa only [toFun_mul] using (ω.convolutionL1_toLp (μ := μ) f.toFun g.toFun).symm

/-- `completionEquivL1` intertwines multiplication in the abstract cocycle-twisted `L¹` completion
with `CentralCocycle.convolutionL1` on `Lp A 1 μ`. -/
@[simp]
theorem completionEquivL1_mul (x y : Completion (TwistedConvolutionAlgebra ω μ)) :
    CompactlySupportedL1.completionEquivL1 ω A μ ℂ (x * y) =
      ω.convolutionL1 μ (CompactlySupportedL1.completionEquivL1 ω A μ ℂ x)
        (CompactlySupportedL1.completionEquivL1 ω A μ ℂ y) := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f g =>
    rw [← Completion.coe_mul', CompactlySupportedL1.completionEquivL1_coe,
      CompactlySupportedL1.completionEquivL1_coe, CompactlySupportedL1.completionEquivL1_coe,
      toL1_mul]

@[simp]
theorem completionEquivL1_symm_convolutionL1 (f g : Lp A 1 μ) :
    (CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm (ω.convolutionL1 μ f g) =
      (CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm f *
        (CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm g := by
  apply (CompactlySupportedL1.completionEquivL1 ω A μ ℂ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, completionEquivL1_mul,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

end TwistedConvolutionAlgebra

namespace CentralCocycle

/-- Cocycle-twisted `L¹` convolution is associative on `Lp A 1 μ`. -/
theorem convolutionL1_assoc (f g h : Lp A 1 μ) :
    ω.convolutionL1 μ (ω.convolutionL1 μ f g) h =
      ω.convolutionL1 μ f (ω.convolutionL1 μ g h) := by
  apply (CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm.injective
  simp only [TwistedConvolutionAlgebra.completionEquivL1_symm_convolutionL1, mul_assoc]

/-- For the trivial cocycle `1`, `CentralCocycle.convolutionL1` coincides with
`CStarAction.convolutionL1`. -/
@[simp]
theorem one_convolutionL1 (f g : Lp A 1 μ) :
    (1 : CentralCocycle α).convolutionL1 μ f g = α.convolutionL1 μ f g := by
  rw [convolutionL1_apply, α.convolutionL1_apply]
  refine integral_congr_ae (.of_forall fun r => ?_)
  refine Lp.ext ?_
  filter_upwards [Lp.strongOperatorMultiplication_ae (𝕜 := ℂ) (E := A) (E' := A) μ
    ENNReal.one_ne_top _ _ _
    ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g))] with s hs
  rw [hs]
  simp only [one_value, Submonoid.coe_one, DoubleCentralizer.one_snd]
  rfl

end CentralCocycle

end ConvolutionL1

section InvolutionL1

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} (ω : CentralCocycle α) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

namespace CentralCocycle

/-- **Cocycle-twisted `L¹` involution** on `Lp A 1 μ`, transported from the isometric `⋆`-operation
on `Completion (TwistedConvolutionAlgebra ω μ)` across `completionEquivL1`. -/
def involutionL1 : Lp A 1 μ ≃ₗᵢ⋆[ℂ] Lp A 1 μ :=
  ((CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm.trans (starₗᵢ ℂ)).trans
    (CompactlySupportedL1.completionEquivL1 ω A μ ℂ)

end CentralCocycle

variable {μ}

namespace TwistedConvolutionAlgebra

@[simp]
theorem completionEquivL1_star (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    CompactlySupportedL1.completionEquivL1 ω A μ ℂ (star x) =
      ω.involutionL1 μ (CompactlySupportedL1.completionEquivL1 ω A μ ℂ x) := by
  simp only [CentralCocycle.involutionL1, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, starₗᵢ_apply]

@[simp]
theorem completionEquivL1_symm_involutionL1 (f : Lp A 1 μ) :
    (CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm (ω.involutionL1 μ f) =
      star ((CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm f) := by
  simp only [CentralCocycle.involutionL1, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, starₗᵢ_apply]

@[simp]
theorem toL1_star (f : TwistedConvolutionAlgebra ω μ) :
    CompactlySupportedL1.toL1 ℂ (star f) =
      ω.involutionL1 μ (CompactlySupportedL1.toL1 ℂ f) := by
  rw [← CompactlySupportedL1.completionEquivL1_coe, Completion.coe_star,
    completionEquivL1_star, CompactlySupportedL1.completionEquivL1_coe]

end TwistedConvolutionAlgebra

namespace CentralCocycle

@[simp]
theorem involutionL1_toLp (f : C_c(G, A)) :
    ω.involutionL1 μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ f) =
      CompactlySupportedContinuousMap.toLp 1 μ ℂ (ω.involution f) := by
  simpa only [CompactlySupportedL1.toL1_eq_toLp, CompactlySupportedL1.toFun_ofFun,
    TwistedConvolutionAlgebra.toFun_star] using
    (TwistedConvolutionAlgebra.toL1_star (ω := ω) (μ := μ) (CompactlySupportedL1.ofFun f)).symm

@[simp]
theorem involutionL1_involutionL1 (f : Lp A 1 μ) :
    ω.involutionL1 μ (ω.involutionL1 μ f) = f := by
  simp only [involutionL1, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, starₗᵢ_apply, star_star,
    LinearIsometryEquiv.apply_symm_apply]

@[simp]
theorem involutionL1_symm :
    (ω.involutionL1 μ).symm = ω.involutionL1 μ :=
  LinearIsometryEquiv.ext fun f =>
    (LinearIsometryEquiv.symm_apply_eq _).2 (ω.involutionL1_involutionL1 f).symm

/-- The cocycle-twisted `L¹` involution reverses cocycle-twisted `L¹` convolution. -/
theorem involutionL1_convolutionL1 (f g : Lp A 1 μ) :
    ω.involutionL1 μ (ω.convolutionL1 μ f g) =
      ω.convolutionL1 μ (ω.involutionL1 μ g) (ω.involutionL1 μ f) := by
  apply (CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm.injective
  simp only [TwistedConvolutionAlgebra.completionEquivL1_symm_involutionL1,
    TwistedConvolutionAlgebra.completionEquivL1_symm_convolutionL1]
  exact star_mul ((CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm f)
    ((CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm g)

/-- On `Lp A 1 μ`, `ω.involutionL1` is obtained by multiplying `α.twistedInvolutionL1` pointwise
by `s ↦ (ω⁻¹.value s s⁻¹ : 𝓜(ℂ, A)).fst = (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst`, without
requiring Haar full support or regularity. -/
theorem involutionL1_eq_strongOperatorMultiplication_twistedInvolutionL1 (f : Lp A 1 μ) :
    ω.involutionL1 μ f =
      Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
        (fun s => (ω⁻¹.value s s⁻¹ : 𝓜(ℂ, A)).fst)
        (fun _ => ω⁻¹.continuous_fst_apply continuous_id continuous_inv continuous_const)
        ⟨1, fun _ => DoubleCentralizer.norm_unitary_fst_le_one _⟩
        (α.twistedInvolutionL1 μ f) := by
  have hc₁ : Continuous (ω.involutionL1 μ) := (ω.involutionL1 μ).continuous
  have hc₂ : Continuous fun u : Lp A 1 μ =>
      Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
        (fun s => (ω⁻¹.value s s⁻¹ : 𝓜(ℂ, A)).fst)
        (fun _ => ω⁻¹.continuous_fst_apply continuous_id continuous_inv continuous_const)
        ⟨1, fun _ => DoubleCentralizer.norm_unitary_fst_le_one _⟩
        (α.twistedInvolutionL1 μ u) :=
    (Lp.strongOperatorMultiplication μ ENNReal.one_ne_top _ _ _).continuous.comp
      (α.twistedInvolutionL1 μ).continuous
  refine congrFun ((CompactlySupportedL1.denseRange_toL1 ℂ
    (tag := ω) (E := A) (μ := μ)).equalizer hc₁ hc₂ ?_) f
  ext g : 1
  dsimp only [Function.comp_apply]
  rw [CompactlySupportedL1.toL1_eq_toLp ℂ, ω.involutionL1_toLp, α.twistedInvolutionL1_toLp]
  refine Lp.ext ?_
  filter_upwards [CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ
      (ω.involution g.toFun),
    Lp.strongOperatorMultiplication_ae (𝕜 := ℂ) (E := A) (E' := A) μ ENNReal.one_ne_top _ _ _
      (CompactlySupportedContinuousMap.toLp 1 μ ℂ (α.twistedInvolution g.toFun)),
    CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ
      (α.twistedInvolution g.toFun)] with s h₁ h₂ h₃
  rw [h₁, h₂, h₃, ω.involution_apply, α.twistedInvolution_apply, ω.coe_inv_value,
    map_smul]

/-- Without Haar regularity or full support, `ω.involutionL1 μ f` is represented almost everywhere
by `s ↦ (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst ((α.twistedInvolutionL1 μ f) s)`. -/
theorem coeFn_involutionL1_eq_twistedInvolutionL1 (f : Lp A 1 μ) :
    ω.involutionL1 μ f =ᵐ[μ]
      fun s => (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst ((α.twistedInvolutionL1 μ f) s) := by
  rw [ω.involutionL1_eq_strongOperatorMultiplication_twistedInvolutionL1 f]
  filter_upwards [Lp.strongOperatorMultiplication_ae (𝕜 := ℂ) (E := A) (E' := A) μ
    ENNReal.one_ne_top _ _ _ (α.twistedInvolutionL1 μ f)] with s hs
  simpa only [ω.coe_inv_value] using hs

/-- For the trivial cocycle `1`, `CentralCocycle.involutionL1` coincides with
`CStarAction.twistedInvolutionL1`. -/
@[simp]
theorem one_involutionL1 (f : Lp A 1 μ) :
    (1 : CentralCocycle α).involutionL1 μ f = α.twistedInvolutionL1 μ f := by
  refine Lp.ext ?_
  filter_upwards [(1 : CentralCocycle α).coeFn_involutionL1_eq_twistedInvolutionL1 f] with s hs
  simpa using hs

end CentralCocycle

end InvolutionL1

section RegularHaar

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  {α : CStarAction G A} (ω : CentralCocycle α) {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]

namespace CentralCocycle

/-- For a regular Haar measure, the cocycle-twisted `L¹` involution is represented almost
everywhere by
`s ↦ ((Measure.modularCharacter s : ℝ) : ℂ) • (star (ω.value s s⁻¹)).fst (α s (star (f s⁻¹)))`. -/
theorem coeFn_involutionL1 (f : Lp A 1 μ) :
    ω.involutionL1 μ f =ᵐ[μ] fun s =>
      ((Measure.modularCharacter s : ℝ) : ℂ) •
        (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f s⁻¹))) := by
  filter_upwards [ω.coeFn_involutionL1_eq_twistedInvolutionL1 f,
    α.coeFn_twistedInvolutionL1 f] with s h₁ h₂
  rw [h₁, h₂, ← Complex.coe_smul, map_smul]

/-- Representative-independent almost-everywhere formula for `ω.involutionL1 μ f` against a
regular Haar measure. -/
theorem coeFn_involutionL1_of_ae_eq {f₀ : G → A} {f : Lp A 1 μ} (hf₀ : f =ᵐ[μ] f₀) :
    ω.involutionL1 μ f =ᵐ[μ] fun s =>
      ((Measure.modularCharacter s : ℝ) : ℂ) •
        (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f₀ s⁻¹))) := by
  filter_upwards [ω.coeFn_involutionL1 f,
    (Measure.quasiMeasurePreserving_inv_of_regular μ).ae hf₀] with s h₁ h₂
  rw [h₁, h₂]

/-- Almost-everywhere formula for `ω.involutionL1` applied to the `L¹` class of an integrable
function `f₀` against a regular Haar measure. -/
theorem involutionL1_toL1_ae_eq {f₀ : G → A} (hf₀ : Integrable f₀ μ) :
    ω.involutionL1 μ (hf₀.toL1 f₀) =ᵐ[μ] fun s =>
      ((Measure.modularCharacter s : ℝ) : ℂ) •
        (star (ω.value s s⁻¹ : 𝓜(ℂ, A))).fst (α s (star (f₀ s⁻¹))) :=
  ω.coeFn_involutionL1_of_ae_eq hf₀.coeFn_toL1

end CentralCocycle

end RegularHaar

end TauCeti.CStarAction
