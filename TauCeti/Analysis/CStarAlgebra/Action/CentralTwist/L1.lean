/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1
public import TauCeti.MeasureTheory.Function.Lp.Operator.Multiplication
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Constructions.Baire.Metrizable
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Group.Convolution.OpenSubgroup
import TauCeti.MeasureTheory.Group.Convolution.Pointwise
import TauCeti.MeasureTheory.Group.Convolution.Support
import TauCeti.MeasureTheory.Group.OpenSubgroup
import TauCeti.MeasureTheory.Group.Prod
import TauCeti.MeasureTheory.Group.SigmaCompactSupport

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
  `convolutionL1_toL1`, `convolutionL1_toLp_ae_eq`), associativity, submultiplicativity, the
  trivial-cocycle reduction `one_convolutionL1`, and—for regular Haar measures on locally compact
  Hausdorff groups—pointwise a.e. convolution formulas for arbitrary `L¹` classes and integrable
  representatives (`coeFn_convolutionL1`, `coeFn_convolutionL1_of_ae_eq`,
  `convolutionL1_toL1_ae_eq`).
* `CentralCocycle.involutionL1`: cocycle-twisted `L¹` involution on `Lp A 1 μ` as a conjugate-linear
  isometric equivalence for locally compact `G` with a left-invariant Borel measure finite on
  compact sets and inner regular for compact sets on finite-measure sets
  (`IsFiniteMeasureOnCompacts μ`, `μ.InnerRegularCompactLTTop`, `μ.IsMulLeftInvariant`), reversing
  `convolutionL1`, agreeing with `star` on `Completion (TwistedConvolutionAlgebra ω μ)` and
  `C_c(G, A)`, reducing to `CStarAction.twistedInvolutionL1` at `ω = 1`, acting pointwise via
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

omit [WeaklyLocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] in
variable (μ) in
/-- Left-twist multiplier operator on `Lp A 1 μ` at group element `r : G`: pointwise
multiplication by `s ↦ (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd`. -/
private noncomputable def mulSndOp (r : G) : Lp A 1 μ →L[ℂ] Lp A 1 μ :=
  Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
    (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
    (fun _ => ω.continuous_snd_apply continuous_const
      (continuous_const.inv.mul continuous_id) continuous_const)
    ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩

omit [WeaklyLocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] in
variable (μ) in
private theorem norm_mulSndOp_le (r : G) : ‖mulSndOp ω μ r‖ ≤ 1 :=
  Lp.norm_strongOperatorMultiplication_le μ ENNReal.one_ne_top
    (fun s => (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd)
    (fun _ => ω.continuous_snd_apply continuous_const
      (continuous_const.inv.mul continuous_id) continuous_const)
    ⟨1, fun _ => DoubleCentralizer.norm_unitary_snd_le_one _⟩
    zero_le_one fun _ => DoubleCentralizer.norm_unitary_snd_le_one _

omit [WeaklyLocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] in
private theorem norm_mulSnd_compLp_le (a : A) (r : G) (g : Lp A 1 μ) :
    ‖mulSndOp ω μ r ((ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ 1 r g))‖ ≤
      ‖a‖ * ‖g‖ := by
  calc
    ‖mulSndOp ω μ r ((ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ 1 r g))‖ ≤
        1 * ‖(ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ 1 r g)‖ :=
      (mulSndOp ω μ r).le_of_opNorm_le (norm_mulSndOp_le ω μ r) _
    _ ≤ ‖ContinuousLinearMap.mul ℂ A a‖ * ‖α.translateLp μ 1 r g‖ := by
      rw [one_mul]
      exact ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ ‖a‖ * ‖g‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le ℂ A a)
        (norm_nonneg g)

/-- The `Lp A 1 μ`-valued integrand of cocycle-twisted `L¹` convolution is Bochner integrable on
a weakly locally compact topological group against any left-invariant Borel measure finite on
compact sets and inner regular on finite-measure sets, without `LocallyCompactSpace` or Haar full
support. -/
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
  have hmeas : AEStronglyMeasurable
      (fun r => mulSndOp ω μ r ((ContinuousLinearMap.mul ℂ A (f r)).compLp
        (α.translateLp μ 1 r g))) μ :=
    (α.integrable_mul_translateLp hf g).aefinStronglyMeasurable
      |>.aestronglyMeasurable_apply_continuous
      (fun v => Lp.continuous_strongOperatorMultiplication_apply μ ENNReal.one_ne_top F hF
        (fun _ _ => DoubleCentralizer.norm_unitary_snd_le_one _) v)
      (fun r => (mulSndOp ω μ r).continuous)
      (fun r => map_zero (mulSndOp ω μ r))
  exact (hf.norm.mul_const ‖g‖).mono' hmeas
    (.of_forall fun r => norm_mulSnd_compLp_le ω (f r) r g)

omit [WeaklyLocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] in
private theorem norm_integral_mulSnd_compLp_le (f g : Lp A 1 μ) :
    ‖∫ r, mulSndOp ω μ r ((ContinuousLinearMap.mul ℂ A (f r)).compLp
        (α.translateLp μ 1 r g)) ∂μ‖ ≤ ‖f‖ * ‖g‖ := by
  rw [L1.norm_eq_integral_norm f, ← integral_mul_const]
  exact norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.mul_const _)
    (.of_forall fun r => norm_mulSnd_compLp_le ω (f r) r g)

namespace CentralCocycle

variable (μ) in
/-- **Cocycle-twisted `L¹` convolution** on `Lp A 1 μ`, defined as the continuous bilinear map
`Lp A 1 μ →L[ℂ] Lp A 1 μ →L[ℂ] Lp A 1 μ` integrating the cocycle-twisted left translates. -/
def convolutionL1 : Lp A 1 μ →L[ℂ] Lp A 1 μ →L[ℂ] Lp A 1 μ :=
  let hi (u v : Lp A 1 μ) : Integrable (fun r => mulSndOp ω μ r
      ((ContinuousLinearMap.mul ℂ A (u r)).compLp (α.translateLp μ 1 r v))) μ :=
    ω.integrable_mul_translateLp (L1.integrable_coeFn u) v
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun (f g : Lp A 1 μ) =>
        ∫ r, mulSndOp ω μ r ((ContinuousLinearMap.mul ℂ A (f r)).compLp
          (α.translateLp μ 1 r g)) ∂μ)
      (fun f₁ f₂ g => by
        rw [← integral_add (hi f₁ g) (hi f₂ g)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f₁ f₂] with r hr
        rw [hr, Pi.add_apply, map_add, ContinuousLinearMap.add_compLp, map_add])
      (fun c f g => by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with r hr
        rw [hr, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_compLp, map_smul])
      (fun f g₁ g₂ => by
        rw [← integral_add (hi f g₁) (hi f g₂)]
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

omit [WeaklyLocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] in
private theorem setIntegral_mulSndOp_compLp (a : A) (r : G) (g : Lp A 1 μ)
    (s : Set G) :
    ∫ x in s, (mulSndOp ω μ r ((ContinuousLinearMap.mul ℂ A a).compLp
        (α.translateLp μ 1 r g)) : G → A) x ∂μ =
      ∫ x in s, (ω.value r (r⁻¹ * x) : 𝓜(ℂ, A)).snd (a * α r (g (r⁻¹ * x))) ∂μ := by
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [Lp.strongOperatorMultiplication_ae (𝕜 := ℂ) (E := A) (E' := A) μ
      ENNReal.one_ne_top _ _ _
      ((ContinuousLinearMap.mul ℂ A a).compLp (α.translateLp μ 1 r g)),
    (ContinuousLinearMap.mul ℂ A a).coeFn_compLp (α.translateLp μ 1 r g),
    α.coeFn_translateLp r g] with x h₀ h₁ h₂
  rw [mulSndOp, h₀, h₁, ContinuousLinearMap.mul_apply', h₂]

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
      ∫ x in s, (mulSndOp ω μ r ((ContinuousLinearMap.mul ℂ A (f r)).compLp
          (α.translateLp μ 1 r (CompactlySupportedContinuousMap.toLp 1 μ ℂ g))) : G → A) x ∂μ =
        ∫ x in s, F x r ∂μ := by
    refine (setIntegral_mulSndOp_compLp ω (f r) r
      (CompactlySupportedContinuousMap.toLp 1 μ ℂ g) s).trans
        (integral_congr_ae (ae_restrict_of_ae ?_))
    filter_upwards [(measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae
      (CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ g)] with x hx
    rw [hx]
  rw [← Set.setIntegralLp_apply (𝕜 := ℂ) s hμs, ω.convolutionL1_apply,
    ← (Set.setIntegralLp (𝕜 := ℂ) s hμs).integral_comp_comm
      (ω.integrable_mul_translateLp (L1.integrable_coeFn _) _)]
  simp_rw [Set.setIntegralLp_apply, convolution_apply]
  refine (integral_congr_ae ?_).trans
    (integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := μ.restrict s)
      (f := fun r x => F x r) (hFc.comp continuous_swap)
      (hFs.comp_homeomorph (Homeomorph.prodComm G G)))
  filter_upwards [CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ f] with r hr
  rw [hr]
  simpa only [mulSndOp] using hinner r

/-- On compactly supported continuous functions, `CentralCocycle.convolutionL1` agrees with
`CentralCocycle.convolution` after embedding into `Lp A 1 μ`. -/
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

/-- `(completionEquivL1 ω A μ ℂ).symm` sends `CentralCocycle.convolutionL1` on `Lp A 1 μ` to
multiplication in `Completion (TwistedConvolutionAlgebra ω μ)`. -/
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

/-- `completionEquivL1` intertwines `star` on `Completion (TwistedConvolutionAlgebra ω μ)` with
`CentralCocycle.involutionL1` on `Lp A 1 μ`. -/
@[simp]
theorem completionEquivL1_star (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    CompactlySupportedL1.completionEquivL1 ω A μ ℂ (star x) =
      ω.involutionL1 μ (CompactlySupportedL1.completionEquivL1 ω A μ ℂ x) := by
  simp only [CentralCocycle.involutionL1, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, starₗᵢ_apply]

/-- `(completionEquivL1 ω A μ ℂ).symm` sends `CentralCocycle.involutionL1` on `Lp A 1 μ` to `star`
in `Completion (TwistedConvolutionAlgebra ω μ)`. -/
@[simp]
theorem completionEquivL1_symm_involutionL1 (f : Lp A 1 μ) :
    (CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm (ω.involutionL1 μ f) =
      star ((CompactlySupportedL1.completionEquivL1 ω A μ ℂ).symm f) := by
  simp only [CentralCocycle.involutionL1, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, starₗᵢ_apply]

/-- `CompactlySupportedL1.toL1 ℂ` intertwines `star` on `TwistedConvolutionAlgebra ω μ` with
`CentralCocycle.involutionL1` on `Lp A 1 μ`. -/
@[simp]
theorem toL1_star (f : TwistedConvolutionAlgebra ω μ) :
    CompactlySupportedL1.toL1 ℂ (star f) =
      ω.involutionL1 μ (CompactlySupportedL1.toL1 ℂ f) := by
  rw [← CompactlySupportedL1.completionEquivL1_coe, Completion.coe_star,
    completionEquivL1_star, CompactlySupportedL1.completionEquivL1_coe]

end TwistedConvolutionAlgebra

namespace CentralCocycle

omit [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] in
variable (μ) in
/-- Left-multiplication operator on `Lp A 1 μ` for the cocycle involution twist
`s ↦ (ω⁻¹.value s s⁻¹ : 𝓜(ℂ, A)).fst`. -/
private noncomputable def invFstOp : Lp A 1 μ →L[ℂ] Lp A 1 μ :=
  Lp.strongOperatorMultiplication μ ENNReal.one_ne_top
    (fun s => (ω⁻¹.value s s⁻¹ : 𝓜(ℂ, A)).fst)
    (fun _ => ω⁻¹.continuous_fst_apply continuous_id continuous_inv continuous_const)
    ⟨1, fun _ => DoubleCentralizer.norm_unitary_fst_le_one _⟩

/-- On compactly supported continuous functions, `CentralCocycle.involutionL1` agrees with
`CentralCocycle.involution` after embedding into `Lp A 1 μ`. -/
@[simp]
theorem involutionL1_toLp (f : C_c(G, A)) :
    ω.involutionL1 μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ f) =
      CompactlySupportedContinuousMap.toLp 1 μ ℂ (ω.involution f) := by
  simpa only [CompactlySupportedL1.toL1_eq_toLp, CompactlySupportedL1.toFun_ofFun,
    TwistedConvolutionAlgebra.toFun_star] using
    (TwistedConvolutionAlgebra.toL1_star (ω := ω) (μ := μ) (CompactlySupportedL1.ofFun f)).symm

/-- Cocycle-twisted `L¹` involution is involutive on `Lp A 1 μ`. -/
@[simp]
theorem involutionL1_involutionL1 (f : Lp A 1 μ) :
    ω.involutionL1 μ (ω.involutionL1 μ f) = f := by
  simp only [involutionL1, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, starₗᵢ_apply, star_star,
    LinearIsometryEquiv.apply_symm_apply]

/-- `ω.involutionL1 μ` is its own inverse as a conjugate-linear isometric equivalence. -/
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
  have hc₂ : Continuous fun u : Lp A 1 μ => invFstOp ω μ (α.twistedInvolutionL1 μ u) :=
    (invFstOp ω μ).continuous.comp (α.twistedInvolutionL1 μ).continuous
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
  rw [h₁, invFstOp, h₂, h₃, ω.involution_apply, α.twistedInvolution_apply, ω.coe_inv_value,
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

section PointwiseConvolution

variable [T2Space G]

/-- Any continuous map from a σ-compact Hausdorff product into a pseudometrizable space is strongly
measurable with respect to the product σ-algebra. -/
private theorem stronglyMeasurable_prod_of_continuous {X E : Type*}
    [TopologicalSpace X] [SigmaCompactSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    {ψ : X × X → E} (hψ : Continuous ψ) : StronglyMeasurable ψ := by
  borelize E
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
  · have hm : @Measurable (X × X) E Prod.instMeasurableSpace (borel E) ψ := by
      rw [← TauCeti.baire_eq_borel (X := E)]
      exact hψ.measurable_baire_prod_of_sigmaCompact
    exact hm
  · obtain ⟨K, hK, hcover⟩ := isSigmaCompact_univ (X := X × X)
    have hrange : Set.range ψ = ⋃ n, ψ '' K n := by
      rw [← Set.image_univ, ← hcover, Set.image_iUnion]
    rw [hrange]
    exact .iUnion fun n => ((hK n).image hψ).isSeparable

/-- Simultaneously enclose `f`, `g`, and `ω.convolutionL1 μ f g` inside one σ-compact open
subgroup outside which all three vanish `μ`-almost everywhere. -/
private theorem exists_openSubgroup_isSigmaCompact_convolution_triple (f g : Lp A 1 μ) :
    ∃ H : OpenSubgroup G, IsSigmaCompact (H : Set G) ∧
      (f : G → A) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 ∧
      (g : G → A) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 ∧
      (ω.convolutionL1 μ f g : G → A) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
  let F : Fin 3 → G → ℝ := fun i x =>
    match i with
    | 0 => ‖f x‖
    | 1 => ‖g x‖
    | 2 => ‖(ω.convolutionL1 μ f g : G → A) x‖
  have hF (i : Fin 3) : AEFinStronglyMeasurable (F i) μ := by
    fin_cases i
    · exact (L1.integrable_coeFn f).norm.aefinStronglyMeasurable
    · exact (L1.integrable_coeFn g).norm.aefinStronglyMeasurable
    · exact (L1.integrable_coeFn (ω.convolutionL1 μ f g)).norm.aefinStronglyMeasurable
  obtain ⟨H, hH, hFH⟩ := exists_openSubgroup_isSigmaCompact_forall_ae_eq_zero hF
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · filter_upwards [hFH 0] with x hx
    exact norm_eq_zero.1 hx
  · filter_upwards [hFH 1] with x hx
    exact norm_eq_zero.1 hx
  · filter_upwards [hFH 2] with x hx
    exact norm_eq_zero.1 hx

/-- **Pointwise representation of `CentralCocycle.convolutionL1` on regular Haar groups.**
On a locally compact Hausdorff group with a regular Haar measure `μ` (without σ-compactness or
second countability), for `f, g : Lp A 1 μ`, `ω.convolutionL1 μ f g` agrees `μ`-almost everywhere
with the pointwise cocycle-twisted convolution integral
`s ↦ ∫ r, (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ`. -/
theorem coeFn_convolutionL1 (f g : Lp A 1 μ) :
    ω.convolutionL1 μ f g =ᵐ[μ] fun s =>
      ∫ r, (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))) ∂μ := by
  obtain ⟨H, hH, hf_off, hg_off, hconv_off⟩ :=
    exists_openSubgroup_isSigmaCompact_convolution_triple ω f g
  have hH_meas : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  have _ : SigmaCompactSpace H := isSigmaCompact_iff_sigmaCompactSpace.1 hH
  let ν : Measure H := μ.comap ((↑) : H → G)
  have _ : SigmaFinite ν := H.sigmaFinite_comap μ hH
  have hf_sub : Integrable (fun r : H => f (r : G)) ν :=
    (integrable_iff_comap_subtypeVal_of_ae_eq_zero hH_meas hf_off).1 (L1.integrable_coeFn f)
  have hg_sub : Integrable (fun x : H => g (x : G)) ν :=
    (integrable_iff_comap_subtypeVal_of_ae_eq_zero hH_meas hg_off).1 (L1.integrable_coeFn g)
  have hconv_sub : Integrable (fun x : H => (ω.convolutionL1 μ f g : G → A) (x : G)) ν :=
    (integrable_iff_comap_subtypeVal_of_ae_eq_zero hH_meas hconv_off).1 (L1.integrable_coeFn _)
  -- Product integrand `(x, r) ↦ ω(r, r⁻¹ * x).snd (f r * α r (g (r⁻¹ * x)))` on `H × H`.
  let G₂ : H × H → A := fun q =>
    (ω.value (q.2 : G) ((q.2⁻¹ * q.1 : H) : G) : 𝓜(ℂ, A)).snd
      (f (q.2 : G) * α (q.2 : G) (g ((q.2⁻¹ * q.1 : H) : G)))
  have hG₂_int {s₀ : Set H} (hνs₀ : ν s₀ < ∞) :
      Integrable G₂ ((ν.restrict s₀).prod ν) := by
    let u : H × H → A × A := fun q => (f (q.2 : G), g ((q.2⁻¹ * q.1 : H) : G))
    have hu₁ : AEStronglyMeasurable (fun q : H × H => f (q.2 : G)) ((ν.restrict s₀).prod ν) :=
      hf_sub.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have hu₂ : AEStronglyMeasurable (fun q : H × H => g ((q.2⁻¹ * q.1 : H) : G))
        ((ν.restrict s₀).prod ν) :=
      hg_sub.aestronglyMeasurable.comp_inv_mul_swap_prod
    have hu : AEStronglyMeasurable u ((ν.restrict s₀).prod ν) := hu₁.prodMk hu₂
    let Φ : H × H → A × A → A := fun q ab =>
      (ω.value (q.2 : G) ((q.2⁻¹ * q.1 : H) : G) : 𝓜(ℂ, A)).snd
        (ab.1 * α (q.2 : G) ab.2)
    have hΦ_meas (ab : A × A) : AEStronglyMeasurable (fun q : H × H => Φ q ab)
        ((ν.restrict s₀).prod ν) := by
      refine (stronglyMeasurable_prod_of_continuous ?_).aestronglyMeasurable
      have h1 : Continuous fun q : H × H => (q.2 : G) :=
        continuous_subtypeVal.comp continuous_snd
      have h2 : Continuous fun q : H × H => ((q.2⁻¹ * q.1 : H) : G) :=
        continuous_subtypeVal.comp (continuous_snd.inv.mul continuous_fst)
      have h3 : Continuous fun q : H × H => ab.1 * α (q.2 : G) ab.2 :=
        continuous_const.mul ((α.continuous_orbit ab.2).comp h1)
      exact ω.continuous_snd_apply h1 h2 h3
    have hΦ_cont (q : H × H) : ContinuousAt (Φ q) (u q) := by
      refine Continuous.continuousAt ?_
      have hlin : Continuous fun ab : A × A => ab.1 * α (q.2 : G) ab.2 :=
        continuous_fst.mul ((StarAlgEquiv.isometry (α (q.2 : G))).continuous.comp continuous_snd)
      exact (ω.value (q.2 : G) ((q.2⁻¹ * q.1 : H) : G) : 𝓜(ℂ, A)).snd.continuous.comp hlin
    have hG₂_meas : AEStronglyMeasurable G₂ ((ν.restrict s₀).prod ν) :=
      hu.apply_of_forall_of_continuousAt hΦ_meas (.of_forall hΦ_cont)
    have hnorm : Integrable (fun q : H × H => ‖f (q.2 : G)‖ * ‖g ((q.2⁻¹ * q.1 : H) : G)‖)
        ((ν.restrict s₀).prod ν) :=
      Integrable.smul_comp_inv_mul_swap_restrict_prod (𝕜 := ℝ) (E := ℝ)
        hf_sub.norm (memLp_one_iff_integrable.2 hg_sub.norm) hνs₀
    refine hnorm.mono' hG₂_meas (.of_forall fun q => ?_)
    calc
      ‖G₂ q‖ ≤ 1 * ‖f (q.2 : G) * α (q.2 : G) (g ((q.2⁻¹ * q.1 : H) : G))‖ := by
        simpa only [one_mul] using
          (ω.value (q.2 : G) ((q.2⁻¹ * q.1 : H) : G) : 𝓜(ℂ, A)).snd.le_of_opNorm_le
            (DoubleCentralizer.norm_unitary_snd_le_one _) _
      _ ≤ ‖f (q.2 : G)‖ * ‖α (q.2 : G) (g ((q.2⁻¹ * q.1 : H) : G))‖ := by
        rw [one_mul]
        exact norm_mul_le _ _
      _ = ‖f (q.2 : G)‖ * ‖g ((q.2⁻¹ * q.1 : H) : G)‖ := by rw [StarAlgEquiv.norm_map]
  -- Helper: pointwise convolution integrand vanishes a.e. outside `H`, so its integral on `G`
  -- equals its integral on `(H, ν)` at every `x : H`.
  have houter (x : H) :
      ∫ r : G, (ω.value r (r⁻¹ * (x : G)) : 𝓜(ℂ, A)).snd
          (f r * α r (g (r⁻¹ * (x : G)))) ∂μ =
        ∫ r : H, G₂ (x, r) ∂ν := by
    have hx_off : (fun r : G => (ω.value r (r⁻¹ * (x : G)) : 𝓜(ℂ, A)).snd
        (f r * α r (g (r⁻¹ * (x : G))))) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
      filter_upwards [hf_off] with r hr
      simp [hr]
    rw [integral_eq_subtype_comap_of_ae_eq_zero hH_meas hx_off]
    rfl
  -- Helper: set integrals of functions over `s₀ ⊆ H` match set integrals over `s = (↑) '' s₀ ⊆ G`.
  have hset_int {s₀ : Set H} (hs₀ : MeasurableSet s₀) (F : G → A) :
      ∫ x in ((↑) : H → G) '' s₀, F x ∂μ = ∫ x in s₀, F (x : G) ∂ν := by
    let s : Set G := ((↑) : H → G) '' s₀
    have hs_meas : MeasurableSet s := H.measurableEmbedding_coe.measurableSet_image.2 hs₀
    have hs_sub : s ⊆ (H : Set G) := Subtype.coe_image_subset (H : Set G) s₀
    have hind : s.indicator F =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
      filter_upwards [ae_restrict_mem hH_meas.compl] with x hx
      exact Set.indicator_of_notMem (fun hys => hx (hs_sub hys)) F
    rw [← integral_indicator hs_meas, integral_eq_subtype_comap_of_ae_eq_zero hH_meas hind,
      ← integral_indicator hs₀]
    congr 1 with x
    simp [s, Set.indicator_image Subtype.coe_injective]
    rfl
  -- Compare on `H` by set integrals over finite-measure subsets, and show both vanish on `Hᶜ`.
  refine ae_of_ae_restrict_of_ae_restrict_compl (H : Set G) ?_ ?_
  · refine (ae_restrict_iff_subtype hH_meas).2 ?_
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s₀ _ _ => hconv_sub.integrableOn)
      (fun s₀ _ hνs₀ => ((hG₂_int hνs₀).integral_prod_left).congr
        (.of_forall fun x => (houter x).symm))
      fun s₀ hs₀ hνs₀ => ?_
    let s : Set G := ((↑) : H → G) '' s₀
    have hs_meas : MeasurableSet s := H.measurableEmbedding_coe.measurableSet_image.2 hs₀
    have hs_sub : s ⊆ (H : Set G) := Subtype.coe_image_subset (H : Set G) s₀
    have hμs : μ s < ∞ := by
      have hμ_eq : μ s = ν s₀ := by
        rw [← Set.inter_eq_left.2 hs_sub, ← Measure.restrict_apply hs_meas,
          ← map_comap_subtypeVal hH_meas]
        exact (Measure.map_apply H.measurableEmbedding_coe.measurable hs_meas).trans
          (congrArg ν (Subtype.val_injective.preimage_image s₀))
      exact hμ_eq ▸ hνs₀
    let S := Set.setIntegralLp (𝕜 := ℝ) (F := A) (p := 1) s hμs
    have hint := ω.integrable_mul_translateLp (L1.integrable_coeFn f) g
    have hS : ∫ r : G, ∫ x in s, (ω.value r (r⁻¹ * x) : 𝓜(ℂ, A)).snd
          (f r * α r (g (r⁻¹ * x))) ∂μ ∂μ =
        ∫ r : H, ∫ x in s, (ω.value (r : G) ((r : G)⁻¹ * x) : 𝓜(ℂ, A)).snd
          (f (r : G) * α (r : G) (g ((r : G)⁻¹ * x))) ∂μ ∂ν := by
      refine integral_eq_subtype_comap_of_ae_eq_zero hH_meas ?_
      filter_upwards [hf_off] with r hr
      simp [hr]
    calc
      ∫ x in s₀, (ω.convolutionL1 μ f g : G → A) (x : G) ∂ν
          = ∫ x in s, (ω.convolutionL1 μ f g : G → A) x ∂μ := (hset_int hs₀ _).symm
      _ = S (ω.convolutionL1 μ f g) := (Set.setIntegralLp_apply s hμs _).symm
      _ = ∫ r : G, S (mulSndOp ω μ r
            ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g))) ∂μ := by
          rw [ω.convolutionL1_apply, ← S.integral_comp_comm hint]
          rfl
      _ = ∫ r : G, ∫ x in s, (ω.value r (r⁻¹ * x) : 𝓜(ℂ, A)).snd
            (f r * α r (g (r⁻¹ * x))) ∂μ ∂μ := by
          refine integral_congr_ae (.of_forall fun r => ?_)
          dsimp only [S]
          rw [Set.setIntegralLp_apply, setIntegral_mulSndOp_compLp]
      _ = ∫ r : H, ∫ x in s, (ω.value (r : G) ((r : G)⁻¹ * x) : 𝓜(ℂ, A)).snd
            (f (r : G) * α (r : G) (g ((r : G)⁻¹ * x))) ∂μ ∂ν := hS
      _ = ∫ r : H, ∫ x in s₀, G₂ (x, r) ∂ν ∂ν := by
          refine integral_congr_ae (.of_forall fun r => ?_)
          exact hset_int hs₀ _
      _ = ∫ x in s₀, ∫ r : H, G₂ (x, r) ∂ν ∂ν :=
          (integral_integral_swap (hG₂_int hνs₀)).symm
      _ = ∫ x in s₀, ∫ r : G, (ω.value r (r⁻¹ * (x : G)) : 𝓜(ℂ, A)).snd
            (f r * α r (g (r⁻¹ * (x : G)))) ∂μ ∂ν := by
          refine integral_congr_ae (.of_forall fun x => (houter x).symm)
  · filter_upwards [hconv_off, ae_restrict_mem hH_meas.compl] with x hx₁ hxH
    rw [hx₁, Pi.zero_apply]
    symm
    refine integral_eq_zero_of_ae ?_
    filter_upwards [(ae_restrict_iff' hH_meas.compl).1 hf_off,
      (Measure.quasiMeasurePreserving_inv_mul_of_regular μ x).ae
        ((ae_restrict_iff' hH_meas.compl).1 hg_off)] with r hfr hgr
    by_cases hr : r ∈ (H : Set G)
    · have hrx : r⁻¹ * x ∉ (H : Set G) := fun h => hxH (by simpa using H.mul_mem hr h)
      simp [hgr hrx]
    · simp [hfr hr]

/-- Representative-independent almost-everywhere formula for `ω.convolutionL1 μ f g` against a
regular Haar measure on a locally compact Hausdorff group. -/
theorem coeFn_convolutionL1_of_ae_eq {f₀ g₀ : G → A} {f g : Lp A 1 μ}
    (hf₀ : f =ᵐ[μ] f₀) (hg₀ : g =ᵐ[μ] g₀) :
    ω.convolutionL1 μ f g =ᵐ[μ] fun s =>
      ∫ r, (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f₀ r * α r (g₀ (r⁻¹ * s))) ∂μ := by
  filter_upwards [ω.coeFn_convolutionL1 f g] with s hs
  refine hs.trans (integral_congr_ae ?_)
  filter_upwards [hf₀, (Measure.quasiMeasurePreserving_inv_mul_of_regular μ s).ae hg₀]
    with r hrf hrg
  rw [hrf, hrg]

/-- Almost-everywhere formula for `ω.convolutionL1` applied to the `L¹` classes of two integrable
functions `f₀` and `g₀` against a regular Haar measure on a locally compact Hausdorff group. -/
theorem convolutionL1_toL1_ae_eq {f₀ g₀ : G → A} (hf₀ : Integrable f₀ μ)
    (hg₀ : Integrable g₀ μ) :
    ω.convolutionL1 μ (hf₀.toL1 f₀) (hg₀.toL1 g₀) =ᵐ[μ] fun s =>
      ∫ r, (ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f₀ r * α r (g₀ (r⁻¹ * s))) ∂μ :=
  ω.coeFn_convolutionL1_of_ae_eq hf₀.coeFn_toL1 hg₀.coeFn_toL1

end PointwiseConvolution

end CentralCocycle

end RegularHaar

end TauCeti.CStarAction
