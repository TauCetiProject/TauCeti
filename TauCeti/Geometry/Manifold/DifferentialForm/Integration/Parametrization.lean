/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Integration along oriented parametrizations

The absolute Jacobian in change of variables cancels the chart sign when the parametrization
preserves the tangent orientation. The resulting coefficient is evaluation on its tangent map.
Finite chart partitions then compute canonical integration from parametrizations, including
disconnected one-dimensional manifolds and finite sets of seams.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {k : ℕ}

omit [FiniteDimensional ℝ E] in
/-- In a preferred chart, a manifold derivative from a normed source gives the ordinary
coordinate derivative by composing with the tangent chart. -/
theorem _root_.HasMFDerivAt.hasFDerivAt_extChartAt_comp {Q : E → M} {z : E} {α : M}
    {e : E →L[ℝ] TangentSpace I (Q z)}
    (hQ : HasMFDerivAt 𝓘(ℝ, E) I Q z
      (e.comp
        (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hx : Q z ∈ (chartAt H α).source) :
    HasFDerivAt (extChartAt I α ∘ Q)
      (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (Q z)).comp
        e) z := by
  let η := (trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ (Q z)
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)
  let L := η.toContinuousLinearMap.comp e
  have hη : η.toContinuousLinearMap = tangentCoordChange I (Q z) α (Q z) := by
    rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq',
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]
  have hη' : η.toContinuousLinearMap = mfderiv I I (chartAt H α) (Q z) := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hx]
    exact hη
  have hd : HasFDerivAt (extChartAt I α ∘ Q) L z := by
    have h := (hasMFDerivAt_extChartAt (I := I) hx).comp z hQ
    convert! h.hasFDerivAt using 2
    ext v
    rw [← hη']
    rfl
  have he : L =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (Q z)).comp
        e := by
    rw [← Bundle.Trivialization.coe_continuousLinearEquivAt_eq' _
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)]
  exact he ▸ hd

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
  change _ * _ * |L.toLinearEquiv.toLinearMap.det| * _ = _
  rw [hdet]
  have h := congrArg (fun ω : E [⋀^Fin k]→L[ℝ] ℝ ↦ ω b) heval
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis] at h
  exact h

end TauCeti

namespace TauCeti

local notation "E" => EuclideanSpace ℝ (Fin 1)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) 1 N]

omit [IsManifold 𝓘(ℝ, E) 1 N] in
private theorem measurableSet_chart_parameter_piece {Q : E → N} (hQ : Continuous Q)
    (D : Set E) (hD : MeasurableSet D) (α : N) {s : Set N}
    (hs : IsChartMeasurable 𝓘(ℝ, E) s) (hsource : s ⊆ (extChartAt 𝓘(ℝ, E) α).source) :
    MeasurableSet (D ∩ Q ⁻¹' s) := by
  classical
  let U := Q ⁻¹' (extChartAt 𝓘(ℝ, E) α).source
  let Ψ := extChartAt 𝓘(ℝ, E) α ∘ Q
  have hsrc : IsOpen (extChartAt 𝓘(ℝ, E) α).source := by
    simpa only [extChartAt_source] using (chartAt E α).open_source
  have hU : IsOpen U := hsrc.preimage hQ
  have hΨ : ContinuousOn Ψ U :=
    (continuousOn_extChartAt α).comp hQ.continuousOn (fun _ hx ↦ hx)
  have hm : Measurable (U.piecewise Ψ (fun _ ↦ 0)) :=
    hΨ.measurable_piecewise continuousOn_const hU.measurableSet
  have he : D ∩ Q ⁻¹' s = D ∩ U ∩ (U.piecewise Ψ (fun _ ↦ 0)) ⁻¹'
      ((extChartAt 𝓘(ℝ, E) α) '' s) := by
    ext x
    constructor
    · rintro ⟨hx, hxs⟩
      have hu : x ∈ U := hsource hxs
      refine ⟨⟨hx, hu⟩, ?_⟩
      rw [mem_preimage, piecewise_eq_of_mem U _ _ hu]
      exact mem_image_of_mem _ hxs
    · rintro ⟨⟨hx, hu⟩, hz⟩
      rw [mem_preimage, piecewise_eq_of_mem U _ _ hu] at hz
      obtain ⟨y, hy, heq⟩ := hz
      refine ⟨hx, ?_⟩
      have hxy : y = Q x := (extChartAt 𝓘(ℝ, E) α).injOn (hsource hy) hu heq
      change Q x ∈ s
      rwa [← hxy]
  rw [he]
  exact (hD.inter hU.measurableSet).inter
    ((hs.image_extChartAt α hsource).preimage hm)

omit [IsManifold 𝓘(ℝ, E) 1 N] in
private theorem chart_parameter_piece_image {Q : E → N} {D : Set E}
    (α : N) (s : Set N) :
    (extChartAt 𝓘(ℝ, E) α ∘ Q) '' (D ∩ Q ⁻¹' s) =
      (extChartAt 𝓘(ℝ, E) α) '' (Q '' D ∩ s) := by
  rw [image_comp, image_inter_preimage]

omit [IsManifold 𝓘(ℝ, E) 1 N] in
private theorem chart_image_remove_finite_ae (α : N) {Z : Set N} (hZ : Z.Finite) (s : Set N)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    (extChartAt 𝓘(ℝ, E) α) '' s =ᵐ[μ] (extChartAt 𝓘(ℝ, E) α) '' (s \ Z) := by
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null ?_ ((hZ.image (extChartAt 𝓘(ℝ, E) α)).measure_zero μ)
    rintro y ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, by by_contra hne; exact hn ⟨x, ⟨hx, hne⟩, rfl⟩, rfl⟩
  · have hs : (extChartAt 𝓘(ℝ, E) α) '' (s \ Z) ⊆ (extChartAt 𝓘(ℝ, E) α) '' s :=
      image_mono sdiff_subset
    rw [sdiff_eq_empty.mpr hs, measure_empty]

private theorem integralTopForm_eq_sum_parameter_integrals {ι : Type*} [Fintype ι]
    [CompactSpace N] (l : Manifold.OrientationLift 𝓘(ℝ, E) N (Fin 1))
    (φ : RoughForm 𝓘(ℝ, E) N ℝ 1) (hi : IntegrableTopForm φ)
    {Q : ι → E → N} (hQ : ∀ i, Continuous (Q i)) {D : Set E} (hD : MeasurableSet D)
    {Z : Set N} (hZ : Z.Finite) (himage : (⋃ i, Q i '' D) = Zᶜ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D)))
    (hinj : ∀ i, InjOn (Q i) D) (d : N → ι → E → E →L[ℝ] E)
    (hd : ∀ α i z, z ∈ D → Q i z ∈ (extChartAt 𝓘(ℝ, E) α).source →
      HasFDerivAt (extChartAt 𝓘(ℝ, E) α ∘ Q i) (d α i z) z)
    (V : ι → E → ℝ)
    (htransport : ∀ α i z, z ∈ D → Q i z ∈ (extChartAt 𝓘(ℝ, E) α).source →
      (Orientation.signBasis l.modelOrientation
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
        |(d α i z).det| * φ.signedInChartAt (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis α
          (fun x ↦ l.signAt α x) (extChartAt 𝓘(ℝ, E) α (Q i z)) = V i z) :
    (∀ i, IntegrableOn (V i) D) ∧
      integralTopForm (Manifold.Orientation.mk l) φ = ∑ i, ∫ z in D, V i z := by
  classical
  let B := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  obtain ⟨m, α, s, hsm, hsrc, hpieces, hcover, hform⟩ :=
    exists_chart_partition_integralTopForm l B
  let S := fun j : Fin m ↦ fun i : ι ↦ D ∩ Q i ⁻¹' s j
  let T := fun j : Fin m ↦ fun i : ι ↦ (extChartAt 𝓘(ℝ, E) (α j) ∘ Q i) '' S j i
  let C := fun j : Fin m ↦ φ.signedInChartAt B (α j) (fun x ↦ l.signAt (α j) x)
  have hS (j : Fin m) (i : ι) : MeasurableSet (S j i) :=
    measurableSet_chart_parameter_piece (hQ i) D hD (α j) (hsm j) (hsrc j)
  have hderiv (j : Fin m) (i : ι) : ∀ z ∈ S j i,
      HasFDerivWithinAt (extChartAt 𝓘(ℝ, E) (α j) ∘ Q i) (d (α j) i z) (S j i) z :=
    fun z hz ↦ (hd (α j) i z hz.1 (hsrc j hz.2)).hasFDerivWithinAt
  have hΨinj (j : Fin m) (i : ι) :
      InjOn (extChartAt 𝓘(ℝ, E) (α j) ∘ Q i) (S j i) := by
    intro x hx y hy he
    exact hinj i hx.1 hy.1 ((extChartAt 𝓘(ℝ, E) (α j)).injOn
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
  have hVS (j : Fin m) (i : ι) : IntegrableOn (V i) (S j i) B.addHaar := by
    have hh := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul B.addHaar
      (hS j i) (hderiv j i) (hΨinj j i)
        (fun y ↦ (Orientation.signBasis l.modelOrientation B : ℝ) * C j y)).mp
      (((hC j).const_mul _).integrableOn)
    apply hh.congr_fun _ (hS j i)
    intro z hz
    simpa only [Function.comp_apply, smul_eq_mul, mul_left_comm, mul_assoc, B, C] using
      htransport (α j) i z hz.1 (hsrc j hz.2)
  have hpiece (j : Fin m) (i : ι) :
      (Orientation.signBasis l.modelOrientation B : ℝ) * (∫ y in T j i, C j y ∂B.addHaar) =
        ∫ z in S j i, V i z ∂B.addHaar := by
    dsimp only [T]
    rw [integral_image_eq_integral_abs_det_fderiv_smul B.addHaar
      (hS j i) (hderiv j i) (hΨinj j i), ← integral_const_mul]
    apply setIntegral_congr_fun (hS j i)
    intro z hz
    simpa only [Function.comp_apply, smul_eq_mul, mul_assoc, B, C] using
      htransport (α j) i z hz.1 (hsrc j hz.2)
  have hTpair (j : Fin m) : Pairwise (fun i k ↦ Disjoint (T j i) (T j k)) := by
    intro i k hik
    apply disjoint_left.mpr
    rintro y ⟨z, hz, hy⟩ ⟨w, hw, hy'⟩
    have he : Q i z = Q k w := (extChartAt 𝓘(ℝ, E) (α j)).injOn
      (hsrc j hz.2) (hsrc j hw.2) (hy.trans hy'.symm)
    exact disjoint_left.mp (hdisj hik) ⟨z, hz.1, he⟩ ⟨w, hw.1, rfl⟩
  have hTcover (j : Fin m) : (⋃ i, T j i) =
      (extChartAt 𝓘(ℝ, E) (α j)) '' (s j \ Z) := by
    dsimp only [T, S]
    simp_rw [chart_parameter_piece_image]
    rw [← image_iUnion, ← iUnion_inter, himage]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  have hSpair (i : ι) : Pairwise (fun j k ↦ Disjoint (S j i) (S k i)) := by
    intro j k hjk
    apply disjoint_left.mpr
    intro z hz hz'
    exact disjoint_left.mp (hpieces hjk) hz.2 hz'.2
  have hSD (i : ι) : (⋃ j, S j i) = D := by
    simp only [S, ← inter_iUnion, ← preimage_iUnion, hcover, preimage_univ, inter_univ]
  have hvolume : B.addHaar = (volume : Measure E) :=
    (EuclideanSpace.basisFun (Fin 1) ℝ).addHaar_eq_volume
  refine ⟨?_, ?_⟩
  · intro i
    rw [← hSD i, integrableOn_finite_iUnion]
    intro j
    simpa only [hvolume] using hVS j i
  · rw [hform φ hi, Finset.mul_sum]
    have hj (j : Fin m) :
        (Orientation.signBasis l.modelOrientation B : ℝ) *
          (∫ y in (extChartAt 𝓘(ℝ, E) (α j)) '' s j, C j y ∂B.addHaar) =
          ∑ i, ∫ z in S j i, V i z ∂B.addHaar := by
      rw [setIntegral_congr_set (chart_image_remove_finite_ae (α j) hZ (s j) B.addHaar),
        ← hTcover j, integral_iUnion_fintype (hT j) (hTpair j)
          (fun i ↦ (hC j).integrableOn), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ hpiece j i
    change (∑ j, (Orientation.signBasis l.modelOrientation B : ℝ) *
      (∫ y in (extChartAt 𝓘(ℝ, E) (α j)) '' s j, C j y ∂B.addHaar)) = _
    simp_rw [hj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← integral_iUnion_fintype (fun j ↦ hS j i) (hSpair i) (fun j ↦ hVS j i), hSD i, hvolume]

/-- Finitely many disjoint positively oriented parametrizations compute the canonical integral
of a compact one-dimensional manifold outside a finite set of seams. Parameter integrability
follows from intrinsic integrability. -/
theorem integralTopForm_eq_oriented_parametrizations {ι : Type*} [Fintype ι] [CompactSpace N]
    (l : Manifold.OrientationLift 𝓘(ℝ, E) N (Fin 1))
    (φ : RoughForm 𝓘(ℝ, E) N ℝ 1) (hi : IntegrableTopForm φ)
    {Q : ι → E → N} (hQ : ∀ i, Continuous (Q i)) {D : Set E} (hD : MeasurableSet D)
    {Z : Set N} (hZ : Z.Finite) (himage : (⋃ i, Q i '' D) = Zᶜ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D)))
    (hinj : ∀ i, InjOn (Q i) D)
    (e : ∀ i z, E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (Q i z))
    (hd : ∀ i, ∀ z ∈ D, HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (Q i) z
      ((e i z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (ho : ∀ i, ∀ z ∈ D, Orientation.map (Fin 1) (e i z).toLinearEquiv
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation = l.orientationAt (Q i z)) :
    (∀ i, IntegrableOn (fun z ↦ φ (Q i z) (fun j ↦ e i z
      ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis j))) D) ∧
      integralTopForm (Manifold.Orientation.mk l) φ =
        ∑ i, ∫ z in D, φ (Q i z)
          (fun j ↦ e i z ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis j)) := by
  let d := fun α i z ↦
    ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) α).continuousLinearMapAt ℝ (Q i z)).comp
      (e i z).toContinuousLinearMap
  have hd' (α : N) (i : ι) (z : E) (hz : z ∈ D)
      (hs : Q i z ∈ (extChartAt 𝓘(ℝ, E) α).source) :
      HasFDerivAt (extChartAt 𝓘(ℝ, E) α ∘ Q i) (d α i z) z :=
    (hd i z hz).hasFDerivAt_extChartAt_comp (e := (e i z).toContinuousLinearMap)
      (by simpa only [extChartAt_source] using hs)
  apply integralTopForm_eq_sum_parameter_integrals l φ hi hQ hD hZ himage hdisj hinj d hd' _
  intro α i z hz hs
  have h := l.sign_mul_abs_det_mul_inChartAt_eq (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
    φ (Q i) z α (by simpa only [extChartAt_source] using hs) (e i z) (hd i z hz) (ho i z hz)
  rw [RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hs]
  rw [← (hd' α i z hz hs).fderiv]
  calc
    _ = (Orientation.signBasis l.modelOrientation (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
        (l.signAt α (Q i z) : ℝ) * |(fderiv ℝ (extChartAt 𝓘(ℝ, E) α ∘ Q i) z).det| *
        φ.inChartAt α (extChartAt 𝓘(ℝ, E) α (Q i z))
          (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis := by ring
    _ = _ := h

/-- One positively oriented parametrization computes the canonical integral of a compact
one-dimensional manifold outside its seam, including parameter-integrability as a conclusion. -/
theorem integralTopForm_eq_oriented_parametrization [CompactSpace N]
    (l : Manifold.OrientationLift 𝓘(ℝ, E) N (Fin 1))
    (φ : RoughForm 𝓘(ℝ, E) N ℝ 1) (hi : IntegrableTopForm φ)
    {Q : E → N} (hQ : Continuous Q) {D : Set E} (hD : MeasurableSet D)
    {p : N} (himage : Q '' D = {p}ᶜ) (hinj : InjOn Q D)
    (e : ∀ z, E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (Q z))
    (hd : ∀ z ∈ D, HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) Q z
      ((e z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (ho : ∀ z ∈ D, Orientation.map (Fin 1) (e z).toLinearEquiv
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation = l.orientationAt (Q z)) :
    IntegrableOn (fun z ↦ φ (Q z) (fun i ↦ e z ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis i))) D ∧
      integralTopForm (Manifold.Orientation.mk l) φ =
        ∫ z in D, φ (Q z) (fun i ↦ e z ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis i)) := by
  have h := integralTopForm_eq_oriented_parametrizations (ι := PUnit.{1}) l φ hi
    (Q := fun _ ↦ Q) (fun _ ↦ hQ) hD (finite_singleton p)
    (by simpa only [iUnion_const] using himage)
    (fun i j hij ↦ False.elim (hij (Subsingleton.elim i j))) (fun _ ↦ hinj)
    (fun _ ↦ e) (fun _ ↦ hd) (fun _ ↦ ho)
  simpa using h

end TauCeti
