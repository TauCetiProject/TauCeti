/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Integration along oriented parametrizations

The absolute Jacobian in change of variables cancels the chart sign when the parametrization
preserves the tangent orientation. The resulting coefficient is evaluation on its tangent map.
Finite chart partitions then compute canonical integration from parametrizations, including
disconnected manifolds of any positive dimension and finite sets of seams. The parametrizations
are defined on the model space `E` of the manifold, and the parameter integrals are taken for the
Haar measure of a basis of `E` on which the tangent orientation is tested.

## Formal sources

The integral and integrability comparisons use Mathlib.MeasureTheory.Function.Jacobian,
specifically `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` and
`MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {k : ℕ}

/-- An orientation-preserving tangent parametrization cancels the chart sign against its
absolute coordinate Jacobian. The coordinate expression is the actual chart derivative. -/
theorem Manifold.OrientationLift.sign_mul_abs_det_mul_inChartAt_eq
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I M ℝ k) (Q : E → M) (z : E) (α : M)
    (hx : Q z ∈ (chartAt H α).source) (e : E ≃L[ℝ] TangentSpace I (Q z))
    (hQ : HasMFDerivAt 𝓘(ℝ, E) I Q z
      (e.toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (ho : Orientation.map (Fin k) e.toLinearEquiv b.orientation = l.orientationAt (Q z)) :
      (Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt α (Q z) : ℝ) *
        |(fderiv ℝ (extChartAt I α ∘ Q) z).det| *
          φ.inChartAt α (extChartAt I α (Q z)) b =
            φ (Q z) (fun i ↦ e (b i)) := by
  let η := (trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ (Q z)
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)
  let L := e.trans η
  have hd : HasFDerivAt (extChartAt I α ∘ Q) L.toContinuousLinearMap z := by
    have h := hQ.hasFDerivAt_extChartAt_comp (e := e.toContinuousLinearMap) hx
    rw [← Bundle.Trivialization.coe_continuousLinearEquivAt_eq' _
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)] at h
    exact h
  have hB : (b.map L.toLinearEquiv).orientation = l.chartOrientation α ⟨Q z, hx⟩ := by
    rw [Module.Basis.orientation_map]
    -- Read the composite tangent equivalence as the composite of its underlying linear maps.
    change Orientation.map (Fin k) (e.toLinearEquiv.trans η.toLinearEquiv) b.orientation = _
    rw [Orientation.map_trans, ho]
    have h := l.mapOrientation_orientationAt hx
    rw [Bundle.Trivialization.mapOrientation_apply] at h
    exact h
  have heval : (φ.inChartAt α (extChartAt I α (Q z))).compContinuousLinearMap
      L.toContinuousLinearMap = (φ (Q z)).compContinuousLinearMap e.toContinuousLinearMap := by
    ext v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      RoughForm.inChartAt_apply,
      (extChartAt I α).left_inv (by simpa only [extChartAt_source] using hx)]
    rw [← TangentBundle.symmL_trivializationAt hx]
    have hηsym : (trivializationAt E (TangentSpace I) α).symmL ℝ (Q z) =
        η.symm.toContinuousLinearMap :=
      (Bundle.Trivialization.symm_continuousLinearEquivAt_eq' _
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).symm
    rw [hηsym]
    congr 1
    funext i
    exact η.symm_apply_apply (e (v i))
  rw [hd.fderiv]
  -- The coordinate derivative L is the same linear map under its continuous and linear wrappers.
  change _ * _ * |L.toLinearEquiv.toLinearMap.det| * _ = _
  rw [l.signBasis_mul_signAt_mul_abs_det_eq b α hx L.toLinearEquiv hB]
  have h := congrArg (fun ω : E [⋀^Fin k]→L[ℝ] ℝ ↦ ω b) heval
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis] at h
  exact h

omit [IsManifold I 1 M] in
/-- On one parameter piece, intrinsic top-form integrability gives coefficient integrability,
and orientation transport turns the chart Jacobian integral into the parameter integral. -/
theorem Manifold.OrientationLift.integrableOn_and_integral_chart_parameter_piece
    [MeasurableSpace E] [BorelSpace E]
    (l : Manifold.OrientationLift I M (Fin k)) (B : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I M ℝ k) (hi : IntegrableTopForm φ) (α : M)
    {Q : E → M} {S : Set E} (hS : MeasurableSet S) (d : E → E →L[ℝ] E)
    (hd : ∀ z ∈ S, HasFDerivWithinAt (extChartAt I α ∘ Q) (d z) S z)
    (hinj : InjOn (extChartAt I α ∘ Q) S) (V : E → ℝ)
    (htransport : ∀ z ∈ S,
      (Orientation.signBasis l.modelOrientation B : ℝ) * |(d z).det| *
        φ.signedInChartAt B α (fun x ↦ l.signAt α x) (extChartAt I α (Q z)) = V z) :
    IntegrableOn V S B.addHaar ∧
      (Orientation.signBasis l.modelOrientation B : ℝ) *
        (∫ y in (extChartAt I α ∘ Q) '' S,
          φ.signedInChartAt B α (fun x ↦ l.signAt α x) y ∂B.addHaar) =
        ∫ z in S, V z ∂B.addHaar := by
  have hC := signed_coefficient_integrable l hi B α
  constructor
  · have hh := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul B.addHaar
      hS hd hinj (fun y ↦ (Orientation.signBasis l.modelOrientation B : ℝ) *
        φ.signedInChartAt B α (fun x ↦ l.signAt α x) y)).mp
      ((hC.const_mul _).integrableOn)
    apply hh.congr_fun _ hS
    intro z hz
    simpa only [Function.comp_apply, smul_eq_mul, mul_left_comm, mul_assoc] using htransport z hz
  · rw [integral_image_eq_integral_abs_det_fderiv_smul B.addHaar hS hd hinj,
      ← integral_const_mul]
    apply setIntegral_congr_fun hS
    intro z hz
    simpa only [Function.comp_apply, smul_eq_mul, mul_assoc] using htransport z hz

omit [IsManifold I 1 M] in
/-- Integrability and the signed chart integral of one chart piece of a manifold, computed on
disjoint parametrizations covering the complement of a finite set of seams, for a measure with
null singletons. -/
private theorem integrableOn_and_sign_mul_integral_chart_piece [MeasurableSpace E]
    [BorelSpace E] {ι : Type*} [Fintype ι] [Nontrivial E]
    (l : Manifold.OrientationLift I M (Fin k)) (B : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I M ℝ k) (hi : IntegrableTopForm φ) (α : M) {s : Set M}
    (hsm : IsChartMeasurable I s) (hsrc : s ⊆ (extChartAt I α).source)
    {Q : ι → E → M} {D : Set E} (hQ : ∀ i, ContinuousOn (Q i) D) (hD : MeasurableSet D)
    {Z : Set M} (hZ : Z.Finite) (himage : (⋃ i, Q i '' D) = Zᶜ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D)))
    (hinj : ∀ i, InjOn (Q i) D) (d : ι → E → E →L[ℝ] E)
    (hd : ∀ i z, z ∈ D → Q i z ∈ (extChartAt I α).source →
      HasFDerivAt (extChartAt I α ∘ Q i) (d i z) z)
    (V : ι → E → ℝ)
    (htransport : ∀ i z, z ∈ D → Q i z ∈ (extChartAt I α).source →
      (Orientation.signBasis l.modelOrientation B : ℝ) * |(d i z).det| *
        φ.signedInChartAt B α (fun x ↦ l.signAt α x) (extChartAt I α (Q i z)) = V i z) :
    (∀ i, IntegrableOn (V i) (D ∩ Q i ⁻¹' s) B.addHaar) ∧
      (Orientation.signBasis l.modelOrientation B : ℝ) *
        (∫ y in (extChartAt I α) '' s,
          φ.signedInChartAt B α (fun x ↦ l.signAt α x) y ∂B.addHaar) =
        ∑ i, ∫ z in D ∩ Q i ⁻¹' s, V i z ∂B.addHaar := by
  have hS (i : ι) : MeasurableSet (D ∩ Q i ⁻¹' s) :=
    hsm.measurableSet_inter_preimage (hQ i) hD α hsrc
  have hderiv (i : ι) : ∀ z ∈ D ∩ Q i ⁻¹' s,
      HasFDerivWithinAt (extChartAt I α ∘ Q i) (d i z) (D ∩ Q i ⁻¹' s) z :=
    fun z hz ↦ (hd i z hz.1 (hsrc hz.2)).hasFDerivWithinAt
  have hΨinj (i : ι) : InjOn (extChartAt I α ∘ Q i) (D ∩ Q i ⁻¹' s) := by
    intro x hx y hy he
    exact hinj i hx.1 hy.1 ((extChartAt I α).injOn (hsrc hx.2) (hsrc hy.2) he)
  have hC := signed_coefficient_integrable l hi B α
  have hpiece (i : ι) : IntegrableOn (V i) (D ∩ Q i ⁻¹' s) B.addHaar ∧
      (Orientation.signBasis l.modelOrientation B : ℝ) *
        (∫ y in (extChartAt I α ∘ Q i) '' (D ∩ Q i ⁻¹' s),
          φ.signedInChartAt B α (fun x ↦ l.signAt α x) y ∂B.addHaar) =
        ∫ z in D ∩ Q i ⁻¹' s, V i z ∂B.addHaar :=
    l.integrableOn_and_integral_chart_parameter_piece B φ hi α (hS i) (d i) (hderiv i)
      (hΨinj i) (V i) fun z hz ↦ htransport i z hz.1 (hsrc hz.2)
  exact ⟨fun i ↦ (hpiece i).1, mul_integral_image_eq_sum_pieces hZ himage hdisj
    ((extChartAt I α).injOn.mono hsrc) B.addHaar hC.integrableOn _ V
    (fun i ↦ measurable_image_of_fderivWithin (hS i) (hderiv i) (hΨinj i))
    fun i ↦ (hpiece i).2⟩

end TauCeti

namespace TauCeti

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N] {k : ℕ}

private theorem integralTopForm_eq_sum_parameter_integrals [Nontrivial E] {ι : Type*} [Fintype ι]
    [CompactSpace N] (l : Manifold.OrientationLift I N (Fin k)) (B : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I N ℝ k) (hi : IntegrableTopForm φ)
    {Q : ι → E → N} {D : Set E} (hQ : ∀ i, ContinuousOn (Q i) D) (hD : MeasurableSet D)
    {Z : Set N} (hZ : Z.Finite) (himage : (⋃ i, Q i '' D) = Zᶜ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D)))
    (hinj : ∀ i, InjOn (Q i) D) (d : N → ι → E → E →L[ℝ] E)
    (hd : ∀ α i z, z ∈ D → Q i z ∈ (extChartAt I α).source →
      HasFDerivAt (extChartAt I α ∘ Q i) (d α i z) z)
    (V : ι → E → ℝ)
    (htransport : ∀ α i z, z ∈ D → Q i z ∈ (extChartAt I α).source →
      (Orientation.signBasis l.modelOrientation B : ℝ) * |(d α i z).det| *
        φ.signedInChartAt B α (fun x ↦ l.signAt α x) (extChartAt I α (Q i z)) = V i z) :
    (∀ i, IntegrableOn (V i) D B.addHaar) ∧
      integralTopForm (Manifold.Orientation.mk l) φ = ∑ i, ∫ z in D, V i z ∂B.addHaar := by
  classical
  obtain ⟨m, α, s, hsm, hsrc, hpieces, hcover, hform⟩ := exists_chart_partition_integralTopForm l B
  have hA (j : Fin m) := integrableOn_and_sign_mul_integral_chart_piece l B φ hi (α j) (hsm j)
    (hsrc j) hQ hD hZ himage hdisj hinj (d (α j)) (hd (α j)) V (htransport (α j))
  -- For a fixed parametrization, the pulled-back chart pieces partition the entire domain.
  have hSpair (i : ι) : Pairwise (fun j k ↦ Disjoint (D ∩ Q i ⁻¹' s j) (D ∩ Q i ⁻¹' s k)) := by
    intro j k hjk
    apply disjoint_left.mpr
    intro z hz hz'
    exact disjoint_left.mp (hpieces hjk) hz.2 hz'.2
  have hSD (i : ι) : (⋃ j, D ∩ Q i ⁻¹' s j) = D := by
    simp only [← inter_iUnion, ← preimage_iUnion, hcover, preimage_univ, inter_univ]
  refine ⟨?_, ?_⟩
  · intro i
    rw [← hSD i, integrableOn_finite_iUnion]
    exact fun j ↦ (hA j).1 i
  · rw [hform φ hi, Finset.mul_sum, Finset.sum_congr rfl fun j _ ↦ (hA j).2, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_iUnion_fintype
      (fun j ↦ (hsm j).measurableSet_inter_preimage (hQ i) hD (α j) (hsrc j)) (hSpair i)
      (fun j ↦ (hA j).1 i), hSD i]

/-- Finitely many disjoint positively oriented parametrizations compute the canonical integral
of a compact positive-dimensional manifold outside a finite set of seams. The parametrizations are
defined on the model space `E`, the tangent orientation is tested on a basis `B` of `E`, and the
parameter integrals are taken for the Haar measure of `B`. Parameter integrability follows from
intrinsic integrability. -/
theorem integralTopForm_eq_oriented_parametrizations [Nontrivial E] {ι : Type*} [Fintype ι]
    [CompactSpace N] (l : Manifold.OrientationLift I N (Fin k)) (B : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I N ℝ k) (hi : IntegrableTopForm φ) {Q : ι → E → N} {D : Set E}
    (hD : MeasurableSet D) {Z : Set N} (hZ : Z.Finite) (himage : (⋃ i, Q i '' D) = Zᶜ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D)))
    (hinj : ∀ i, InjOn (Q i) D) (e : ∀ i z, E ≃L[ℝ] TangentSpace I (Q i z))
    (hd : ∀ i, ∀ z ∈ D, HasMFDerivAt 𝓘(ℝ, E) I (Q i) z
      ((e i z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (ho : ∀ i, ∀ z ∈ D,
      Orientation.map (Fin k) (e i z).toLinearEquiv B.orientation = l.orientationAt (Q i z)) :
    (∀ i, IntegrableOn (fun z ↦ φ (Q i z) (fun j ↦ e i z (B j))) D B.addHaar) ∧
      integralTopForm (Manifold.Orientation.mk l) φ =
        ∑ i, ∫ z in D, φ (Q i z) (fun j ↦ e i z (B j)) ∂B.addHaar := by
  have hQ (i : ι) : ContinuousOn (Q i) D :=
    fun z hz ↦ (hd i z hz).continuousAt.continuousWithinAt
  let d := fun α i z ↦
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (Q i z)).comp
      (e i z).toContinuousLinearMap
  have hd' (α : N) (i : ι) (z : E) (hz : z ∈ D) (hs : Q i z ∈ (extChartAt I α).source) :
      HasFDerivAt (extChartAt I α ∘ Q i) (d α i z) z :=
    (hd i z hz).hasFDerivAt_extChartAt_comp (e := (e i z).toContinuousLinearMap)
      (by simpa only [extChartAt_source] using hs)
  apply integralTopForm_eq_sum_parameter_integrals l B φ hi hQ hD hZ himage hdisj hinj d hd' _
  intro α i z hz hs
  have h := l.sign_mul_abs_det_mul_inChartAt_eq B φ (Q i) z α
    (by simpa only [extChartAt_source] using hs) (e i z) (hd i z hz) (ho i z hz)
  rw [RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hs, ← (hd' α i z hz hs).fderiv]
  calc
    _ = (Orientation.signBasis l.modelOrientation B : ℝ) * (l.signAt α (Q i z) : ℝ) *
        |(fderiv ℝ (extChartAt I α ∘ Q i) z).det| *
        φ.inChartAt α (extChartAt I α (Q i z)) B := by ring
    _ = _ := h

/-- One positively oriented parametrization computes the canonical integral of a compact
positive-dimensional manifold outside a finite set of seams, including parameter-integrability as a
conclusion. -/
theorem integralTopForm_eq_oriented_parametrization [Nontrivial E] [CompactSpace N]
    (l : Manifold.OrientationLift I N (Fin k)) (B : Module.Basis (Fin k) ℝ E)
    (φ : RoughForm I N ℝ k) (hi : IntegrableTopForm φ) {Q : E → N} {D : Set E}
    (hD : MeasurableSet D) {Z : Set N} (hZ : Z.Finite) (himage : Q '' D = Zᶜ) (hinj : InjOn Q D)
    (e : ∀ z, E ≃L[ℝ] TangentSpace I (Q z))
    (hd : ∀ z ∈ D, HasMFDerivAt 𝓘(ℝ, E) I Q z
      ((e z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (ho : ∀ z ∈ D,
      Orientation.map (Fin k) (e z).toLinearEquiv B.orientation = l.orientationAt (Q z)) :
    IntegrableOn (fun z ↦ φ (Q z) (fun i ↦ e z (B i))) D B.addHaar ∧
      integralTopForm (Manifold.Orientation.mk l) φ =
        ∫ z in D, φ (Q z) (fun i ↦ e z (B i)) ∂B.addHaar := by
  have h := integralTopForm_eq_oriented_parametrizations (ι := PUnit.{1}) l B φ hi
    (Q := fun _ ↦ Q) hD hZ (by simpa only [iUnion_const] using himage)
    (fun i j hij ↦ False.elim (hij (Subsingleton.elim i j))) (fun _ ↦ hinj)
    (fun _ ↦ e) (fun _ ↦ hd) (fun _ ↦ ho)
  simpa using h

end TauCeti
