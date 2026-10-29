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
  have hsign : (Orientation.signBasis (l.chartOrientation α ⟨Q z, hx⟩) b : ℝ) =
      (Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt α (Q z) : ℝ) := by
    rw [Manifold.OrientationLift.chartOrientation_eq_ite,
      Manifold.OrientationLift.signAt_of_mem _ hx]
    rcases Int.units_eq_one_or (l.sign α ⟨Q z, hx⟩) with hs | hs <;>
      simp [hs, Orientation.signBasis_neg]
  have hpos : 0 < (Orientation.signBasis (l.chartOrientation α ⟨Q z, hx⟩) b : ℝ) *
      L.toLinearEquiv.toLinearMap.det := by
    have h := Orientation.signBasis_mul_det_mul_pos (l.chartOrientation α ⟨Q z, hx⟩)
      b (b.map L.toLinearEquiv)
    have hsB : Orientation.signBasis (l.chartOrientation α ⟨Q z, hx⟩)
        (b.map L.toLinearEquiv) = 1 := by
      rw [← hB]
      exact Orientation.signBasis_orientation _
    rw [hsB, Units.val_one, Int.cast_one, mul_one] at h
    -- Normalize basis-map evaluation to a determinant composed with the original basis.
    change 0 < (Orientation.signBasis (l.chartOrientation α ⟨Q z, hx⟩) b : ℝ) *
      b.det (L.toLinearEquiv.toLinearMap ∘ b) at h
    simpa only [Module.Basis.det_comp, Module.Basis.det_self, mul_one] using h
  have hdet : (Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt α (Q z) : ℝ) *
      |L.toLinearEquiv.toLinearMap.det| = L.toLinearEquiv.toLinearMap.det := by
    rw [← hsign]
    rcases Int.units_eq_one_or (Orientation.signBasis (l.chartOrientation α ⟨Q z, hx⟩) b)
      with hs | hs
    · simp only [hs, Units.val_one, Int.cast_one, one_mul] at hpos ⊢
      exact abs_of_pos hpos
    · simp only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
        neg_one_mul] at hpos ⊢
      rw [abs_of_neg (neg_pos.mp hpos), neg_neg]
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
  rw [hdet]
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

end TauCeti

namespace TauCeti

variable {n : ℕ} [NeZero n]

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold
  𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 1 N]

omit [IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 1 N] [NeZero n] in
private theorem chart_parameter_piece_image {Q : (EuclideanSpace ℝ (Fin n)) → N} {D : Set
  (EuclideanSpace ℝ (Fin n))}
    (α : N) (s : Set N) :
    (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α ∘ Q) '' (D ∩ Q ⁻¹' s) =
      (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) α) '' (Q '' D ∩ s) := by
  rw [image_comp, image_inter_preimage]

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
  -- First pull the disjoint measurable chart partition back to each parameter domain.
  let S := fun j : Fin m ↦ fun i : ι ↦ D ∩ Q i ⁻¹' s j
  let T := fun j : Fin m ↦ fun i : ι ↦ (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (α j) ∘ Q i)
    '' S j i
  let C := fun j : Fin m ↦ φ.signedInChartAt B (α j) (fun x ↦ l.signAt (α j) x)
  have hS (j : Fin m) (i : ι) : MeasurableSet (S j i) :=
    (hsm j).measurableSet_inter_preimage (hQ i) hD (α j) (hsrc j)
  have hderiv (j : Fin m) (i : ι) : ∀ z ∈ S j i,
      HasFDerivWithinAt (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (α j) ∘ Q i) (d (α j) i z) (S
        j i) z :=
    fun z hz ↦ (hd (α j) i z hz.1 (hsrc j hz.2)).hasFDerivWithinAt
  have hΨinj (j : Fin m) (i : ι) :
      InjOn (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (α j) ∘ Q i) (S j i) := by
    intro x hx y hy he
    exact hinj i hx.1 hy.1 ((extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (α j)).injOn
      (hsrc j hx.2) (hsrc j hy.2) he)
  have hT (j : Fin m) (i : ι) : MeasurableSet (T j i) := by
    dsimp only [T]
    rw [← range_domRestrict]
    exact (measurableEmbedding_of_fderivWithin (hS j i) (hderiv j i)
      (hΨinj j i)).measurableSet_range
  have hC (j : Fin m) : Integrable (C j) B.addHaar := by
    apply (RoughForm.integrable_signedInChartAt_iff_unsigned φ B (α j)
      (fun x ↦ l.signAt (α j) x) ?_ B.addHaar).mpr
      (((integrableTopForm_iff φ).mp hi).2.2 B (α j))
    apply continuousOn_iff_continuous_domRestrict.mp
    simpa only [extChartAt_source] using l.continuousOn_signAt (α j)
  -- Compare each intersection of a chart piece with one parametrization once, for both
  -- integrability and its signed integral. The two finite partitions are assembled below.
  have hpiece (j : Fin m) (i : ι) : IntegrableOn (V i) (S j i) B.addHaar ∧
      (Orientation.signBasis l.modelOrientation B : ℝ) * (∫ y in T j i, C j y ∂B.addHaar) =
        ∫ z in S j i, V i z ∂B.addHaar := by
    apply l.integrableOn_and_integral_chart_parameter_piece B φ hi (α j) (hS j i)
      (d (α j) i) (hderiv j i) (hΨinj j i) (V i)
    intro z hz
    exact htransport (α j) i z hz.1 (hsrc j hz.2)
  -- For a fixed chart, disjoint parametrization images cover its piece up to finite seams.
  have hTpair (j : Fin m) : Pairwise (fun i k ↦ Disjoint (T j i) (T j k)) := by
    intro i k hik
    apply disjoint_left.mpr
    rintro y ⟨z, hz, hy⟩ ⟨w, hw, hy'⟩
    have he : Q i z = Q k w := (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (α j)).injOn
      (hsrc j hz.2) (hsrc j hw.2) (hy.trans hy'.symm)
    exact disjoint_left.mp (hdisj hik) ⟨z, hz.1, he⟩ ⟨w, hw.1, rfl⟩
  have hTcover (j : Fin m) : (⋃ i, T j i) =
      (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (α j)) '' (s j \ Z) := by
    dsimp only [T, S]
    simp_rw [chart_parameter_piece_image]
    rw [← image_iUnion, ← iUnion_inter, himage]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  -- For a fixed parametrization, the pulled-back chart pieces partition the entire domain.
  have hSpair (i : ι) : Pairwise (fun j k ↦ Disjoint (S j i) (S k i)) := by
    intro j k hjk
    apply disjoint_left.mpr
    intro z hz hz'
    exact disjoint_left.mp (hpieces hjk) hz.2 hz'.2
  have hSD (i : ι) : (⋃ j, S j i) = D := by
    simp only [S, ← inter_iUnion, ← preimage_iUnion, hcover, preimage_univ, inter_univ]
  have hvolume : B.addHaar = (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).addHaar_eq_volume
  refine ⟨?_, ?_⟩
  · intro i
    rw [← hSD i, integrableOn_finite_iUnion]
    intro j
    simpa only [hvolume] using (hpiece j i).1
  · rw [hform φ hi, Finset.mul_sum]
    have hj (j : Fin m) :
        (Orientation.signBasis l.modelOrientation B : ℝ) *
          (∫ y in (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (α j)) '' s j, C j y ∂B.addHaar) =
          ∑ i, ∫ z in S j i, V i z ∂B.addHaar := by
      rw [setIntegral_congr_set (hZ.image_sdiff_ae_eq (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))
        (α j)) (s j) B.addHaar),
        ← hTcover j, integral_iUnion_fintype (hT j) (hTpair j)
          (fun i ↦ (hC j).integrableOn), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ (hpiece j i).2
    -- Expand the canonical chart sum, then swap the chart and parameter indices.
    change (∑ j, (Orientation.signBasis l.modelOrientation B : ℝ) *
      (∫ y in (extChartAt 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (α j)) '' s j, C j y ∂B.addHaar)) = _
    simp_rw [hj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← integral_iUnion_fintype (fun j ↦ hS j i) (hSpair i) (fun j ↦ (hpiece j i).1), hSD i,
      hvolume]

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
