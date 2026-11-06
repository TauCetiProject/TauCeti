/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Integration along oriented parametrizations

The absolute Jacobian in change of variables cancels the chart sign when the parametrization
preserves the tangent orientation. The resulting coefficient is evaluation on its tangent map.
Finite chart partitions then compute canonical integration from parametrizations, including
disconnected manifolds of any positive dimension and finite sets of seams.

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

omit [IsManifold I 1 M] in
/-- The chart sign and the absolute determinant of a linear equivalence carrying a basis `b` to
a basis of the chart orientation combine to the determinant itself. -/
private theorem signBasis_mul_signAt_mul_abs_det_eq
    (l : Manifold.OrientationLift I M (Fin k)) (b : Module.Basis (Fin k) ℝ E)
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) (L : E ≃ₗ[ℝ] E)
    (hB : (b.map L).orientation = l.chartOrientation α ⟨x, hx⟩) :
    (Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt α x : ℝ) *
      |L.toLinearMap.det| = L.toLinearMap.det := by
  have hsign : (Orientation.signBasis (l.chartOrientation α ⟨x, hx⟩) b : ℝ) =
      (Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt α x : ℝ) := by
    rw [Manifold.OrientationLift.chartOrientation_eq_ite,
      Manifold.OrientationLift.signAt_of_mem _ hx]
    rcases Int.units_eq_one_or (l.sign α ⟨x, hx⟩) with hs | hs <;>
      simp [hs, Orientation.signBasis_neg]
  have hpos : 0 < (Orientation.signBasis (l.chartOrientation α ⟨x, hx⟩) b : ℝ) *
      L.toLinearMap.det := by
    have h := Orientation.signBasis_mul_det_mul_pos (l.chartOrientation α ⟨x, hx⟩)
      b (b.map L)
    have hsB : Orientation.signBasis (l.chartOrientation α ⟨x, hx⟩)
        (b.map L) = 1 := by
      rw [← hB]
      exact Orientation.signBasis_orientation _
    rw [hsB, Units.val_one, Int.cast_one, mul_one] at h
    -- Normalize basis-map evaluation to a determinant composed with the original basis.
    change 0 < (Orientation.signBasis (l.chartOrientation α ⟨x, hx⟩) b : ℝ) *
      b.det (L.toLinearMap ∘ b) at h
    simpa only [Module.Basis.det_comp, Module.Basis.det_self, mul_one] using h
  rw [← hsign]
  rcases Int.units_eq_one_or (Orientation.signBasis (l.chartOrientation α ⟨x, hx⟩) b)
    with hs | hs
  · simp only [hs, Units.val_one, Int.cast_one, one_mul] at hpos ⊢
    exact abs_of_pos hpos
  · simp only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      neg_one_mul] at hpos ⊢
    rw [abs_of_neg (neg_pos.mp hpos), neg_neg]

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
  rw [signBasis_mul_signAt_mul_abs_det_eq l b α hx L.toLinearEquiv hB]
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
  have hC : Integrable (φ.signedInChartAt B α (fun x ↦ l.signAt α x)) B.addHaar := by
    apply (RoughForm.integrable_signedInChartAt_iff_unsigned φ B α
      (fun x ↦ l.signAt α x) ?_ B.addHaar).mpr
      (((integrableTopForm_iff φ).mp hi).2.2 B α)
    apply continuousOn_iff_continuous_domRestrict.mp
    simpa only [extChartAt_source] using l.continuousOn_signAt α
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

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
private theorem chart_parameter_piece_image {Q : E → M} {D : Set E} (α : M) (s : Set M) :
    (extChartAt I α ∘ Q) '' (D ∩ Q ⁻¹' s) = (extChartAt I α) '' (Q '' D ∩ s) := by
  rw [image_comp, image_inter_preimage]

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- If disjoint parametrizations cover the complement of a finite set of seams, the integral over
the coordinate image of a chart piece is the sum of the integrals over the images of the pieces
cut out by each parametrization. -/
private theorem mul_integral_chart_image_eq_sum_pieces [MeasurableSpace E] {ι : Type*}
    [Fintype ι] {Q : ι → E → M} {D : Set E} {Z : Set M} (hZ : Z.Finite)
    (himage : (⋃ i, Q i '' D) = Zᶜ) (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D)))
    (α : M) {s : Set M} (hsrc : s ⊆ (extChartAt I α).source) (μ : Measure E)
    [NullSingletonClass μ] {C : E → ℝ} (hC : Integrable C μ) (c : ℝ) (V : ι → E → ℝ)
    (hT : ∀ i, MeasurableSet ((extChartAt I α ∘ Q i) '' (D ∩ Q i ⁻¹' s)))
    (hpiece : ∀ i, c * ∫ y in (extChartAt I α ∘ Q i) '' (D ∩ Q i ⁻¹' s), C y ∂μ =
      ∫ z in D ∩ Q i ⁻¹' s, V i z ∂μ) :
    c * ∫ y in (extChartAt I α) '' s, C y ∂μ = ∑ i, ∫ z in D ∩ Q i ⁻¹' s, V i z ∂μ := by
  have hpair : Pairwise (fun i k ↦ Disjoint ((extChartAt I α ∘ Q i) '' (D ∩ Q i ⁻¹' s))
      ((extChartAt I α ∘ Q k) '' (D ∩ Q k ⁻¹' s))) := by
    intro i k hik
    apply disjoint_left.mpr
    rintro y ⟨z, hz, hy⟩ ⟨w, hw, hy'⟩
    have he : Q i z = Q k w :=
      (extChartAt I α).injOn (hsrc hz.2) (hsrc hw.2) (hy.trans hy'.symm)
    exact disjoint_left.mp (hdisj hik) ⟨z, hz.1, he⟩ ⟨w, hw.1, rfl⟩
  have hcover : (⋃ i, (extChartAt I α ∘ Q i) '' (D ∩ Q i ⁻¹' s)) =
      (extChartAt I α) '' (s \ Z) := by
    simp_rw [chart_parameter_piece_image]
    rw [← image_iUnion, ← iUnion_inter, himage]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  rw [setIntegral_congr_set (hZ.image_sdiff_ae_eq (extChartAt I α) s μ), ← hcover,
    integral_iUnion_fintype hT hpair (fun i ↦ hC.integrableOn), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hpiece i

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
  have hC : Integrable (φ.signedInChartAt B α (fun x ↦ l.signAt α x)) B.addHaar := by
    apply (RoughForm.integrable_signedInChartAt_iff_unsigned φ B α
      (fun x ↦ l.signAt α x) ?_ B.addHaar).mpr
      (((integrableTopForm_iff φ).mp hi).2.2 B α)
    apply continuousOn_iff_continuous_domRestrict.mp
    simpa only [extChartAt_source] using l.continuousOn_signAt α
  have hpiece (i : ι) : IntegrableOn (V i) (D ∩ Q i ⁻¹' s) B.addHaar ∧
      (Orientation.signBasis l.modelOrientation B : ℝ) *
        (∫ y in (extChartAt I α ∘ Q i) '' (D ∩ Q i ⁻¹' s),
          φ.signedInChartAt B α (fun x ↦ l.signAt α x) y ∂B.addHaar) =
        ∫ z in D ∩ Q i ⁻¹' s, V i z ∂B.addHaar :=
    l.integrableOn_and_integral_chart_parameter_piece B φ hi α (hS i) (d i) (hderiv i)
      (hΨinj i) (V i) fun z hz ↦ htransport i z hz.1 (hsrc hz.2)
  exact ⟨fun i ↦ (hpiece i).1, mul_integral_chart_image_eq_sum_pieces hZ himage hdisj α hsrc
    B.addHaar hC _ V (fun i ↦ measurable_image_of_fderivWithin (hS i) (hderiv i) (hΨinj i))
    fun i ↦ (hpiece i).2⟩

end TauCeti

namespace TauCeti

variable {n : ℕ} [NeZero n]

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold
  𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 1 N]

private theorem integralTopForm_eq_sum_parameter_integrals {ι : Type*} [Fintype ι]
    [CompactSpace N] (l : Manifold.OrientationLift 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) N (Fin n))
    (φ : RoughForm 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) N ℝ n) (hi : IntegrableTopForm φ)
    {Q : ι → (EuclideanSpace ℝ (Fin n)) → N} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hQ : ∀ i, ContinuousOn (Q i) D)
    (hD : MeasurableSet D)
    {Z : Set N} (hZ : Z.Finite) (himage : (⋃ i, Q i '' D) = Zᶜ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D)))
    (hinj : ∀ i, InjOn (Q i) D) (d : N → ι → (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin
      n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)))
    (hd : ∀ α i z, z ∈ D → Q i z ∈ (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α).source →
      HasFDerivAt (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α ∘ Q i) (d α i z) z)
    (V : ι → (EuclideanSpace ℝ (Fin n)) → ℝ)
    (htransport : ∀ α i z, z ∈ D → Q i z ∈ (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α).source →
      (Orientation.signBasis l.modelOrientation
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis : ℝ) *
        |(d α i z).det| * φ.signedInChartAt (EuclideanSpace.basisFun (Fin n) ℝ).toBasis α
          (fun x ↦ l.signAt α x) (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α (Q i z)) = V i z) :
    (∀ i, IntegrableOn (V i) D) ∧
      integralTopForm (Manifold.Orientation.mk l) φ = ∑ i, ∫ z in D, V i z := by
  classical
  let B := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  obtain ⟨m, α, s, hsm, hsrc, hpieces, hcover, hform⟩ :=
    exists_chart_partition_integralTopForm l B
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
  have hvolume : B.addHaar = (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).addHaar_eq_volume
  refine ⟨?_, ?_⟩
  · intro i
    rw [← hSD i, integrableOn_finite_iUnion]
    intro j
    simpa only [hvolume] using (hA j).1 i
  · rw [hform φ hi, Finset.mul_sum, Finset.sum_congr rfl fun j _ ↦ (hA j).2, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_iUnion_fintype
      (fun j ↦ (hsm j).measurableSet_inter_preimage (hQ i) hD (α j) (hsrc j)) (hSpair i)
      (fun j ↦ (hA j).1 i), hSD i, hvolume]

/-- Finitely many disjoint positively oriented parametrizations compute the canonical integral
of a compact positive-dimensional manifold outside a finite set of seams. Parameter integrability
follows from intrinsic integrability. -/
theorem integralTopForm_eq_oriented_parametrizations {ι : Type*} [Fintype ι] [CompactSpace N]
    (l : Manifold.OrientationLift 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) N (Fin n))
    (φ : RoughForm 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) N ℝ n) (hi : IntegrableTopForm φ)
    {Q : ι → (EuclideanSpace ℝ (Fin n)) → N} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : MeasurableSet D)
    {Z : Set N} (hZ : Z.Finite) (himage : (⋃ i, Q i '' D) = Zᶜ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D)))
    (hinj : ∀ i, InjOn (Q i) D)
    (e : ∀ i z, (EuclideanSpace ℝ (Fin n)) ≃L[ℝ] TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (Q
      i z))
    (hd : ∀ i, ∀ z ∈ D, HasMFDerivAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin
      n))) (Q i) z
      ((e i z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (ho : ∀ i, ∀ z ∈ D, Orientation.map (Fin n) (e i z).toLinearEquiv
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation = l.orientationAt (Q i z)) :
    (∀ i, IntegrableOn (fun z ↦ φ (Q i z) (fun j ↦ e i z
      ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j))) D) ∧
      integralTopForm (Manifold.Orientation.mk l) φ =
        ∑ i, ∫ z in D, φ (Q i z)
          (fun j ↦ e i z ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j)) := by
  have hQ (i : ι) : ContinuousOn (Q i) D :=
    fun z hz ↦ (hd i z hz).continuousAt.continuousWithinAt
  let d := fun α i z ↦
    ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
      α).continuousLinearMapAt ℝ (Q i z)).comp
      (e i z).toContinuousLinearMap
  have hd' (α : N) (i : ι) (z : (EuclideanSpace ℝ (Fin n))) (hz : z ∈ D)
      (hs : Q i z ∈ (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α).source) :
      HasFDerivAt (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α ∘ Q i) (d α i z) z :=
    (hd i z hz).hasFDerivAt_extChartAt_comp (e := (e i z).toContinuousLinearMap)
      (by simpa only [extChartAt_source] using hs)
  apply integralTopForm_eq_sum_parameter_integrals l φ hi hQ hD hZ himage hdisj hinj d hd' _
  intro α i z hz hs
  have h := l.sign_mul_abs_det_mul_inChartAt_eq (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    φ (Q i) z α (by simpa only [extChartAt_source] using hs) (e i z) (hd i z hz) (ho i z hz)
  rw [RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hs]
  rw [← (hd' α i z hz hs).fderiv]
  calc
    _ = (Orientation.signBasis l.modelOrientation (EuclideanSpace.basisFun (Fin n) ℝ).toBasis : ℝ) *
        (l.signAt α (Q i z) : ℝ) * |(fderiv ℝ (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α ∘ Q
          i) z).det| *
        φ.inChartAt α (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α (Q i z))
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis := by ring
    _ = _ := h

/-- One positively oriented parametrization computes the canonical integral of a compact
positive-dimensional manifold outside its seam, including parameter-integrability as a conclusion.
-/
theorem integralTopForm_eq_oriented_parametrization [CompactSpace N]
    (l : Manifold.OrientationLift 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) N (Fin n))
    (φ : RoughForm 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) N ℝ n) (hi : IntegrableTopForm φ)
    {Q : (EuclideanSpace ℝ (Fin n)) → N} {D : Set (EuclideanSpace ℝ (Fin n))}
      (hD : MeasurableSet D)
    {p : N} (himage : Q '' D = {p}ᶜ) (hinj : InjOn Q D)
    (e : ∀ z, (EuclideanSpace ℝ (Fin n)) ≃L[ℝ] TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (Q z))
    (hd : ∀ z ∈ D, HasMFDerivAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
      Q z
      ((e z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (ho : ∀ z ∈ D, Orientation.map (Fin n) (e z).toLinearEquiv
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation = l.orientationAt (Q z)) :
    IntegrableOn (fun z ↦ φ (Q z) (fun i ↦ e z ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i))) D ∧
      integralTopForm (Manifold.Orientation.mk l) φ =
        ∫ z in D, φ (Q z) (fun i ↦ e z ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i)) := by
  have h := integralTopForm_eq_oriented_parametrizations (ι := PUnit.{1}) l φ hi
    (Q := fun _ ↦ Q) hD (finite_singleton p)
    (by simpa only [iUnion_const] using himage)
    (fun i j hij ↦ False.elim (hij (Subsingleton.elim i j))) (fun _ ↦ hinj)
    (fun _ ↦ e) (fun _ ↦ hd) (fun _ ↦ ho)
  simpa using h

end TauCeti
