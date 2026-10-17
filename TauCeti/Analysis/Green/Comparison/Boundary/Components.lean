/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.PathCoefficient
public import TauCeti.Analysis.Green.Comparison.Regularity
public import TauCeti.Analysis.Green.Comparison.PullbackExteriorDerivative
public import TauCeti.Analysis.Green.Comparison.Area.Image
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Parametrization
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes

/-!
# Green on finitely many actual boundary components

An oriented finite family of arcs covers a compact one-dimensional manifold outside
its finite seam set. Its canonical integral is the sum of the existing path circulations,
allowing subdivisions, disconnected smooth boundaries, and clockwise hole components.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Topology ContDiff

namespace TauCeti.Green

local notation "E" => EuclideanSpace ℝ (Fin 1)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) 1 N]

/-- A finite family of actual positively oriented arcs computes the canonical
circulation integral. All component curve integrabilities are conclusions. -/
theorem integralTopForm_mpullback_eq_sum_curveIntegral {ι : Type*} [Fintype ι]
    [CompactSpace N]
    (o : Manifold.Orientation 𝓘(ℝ, E) N (Fin 1))
    (p r : ι → N) (q : ∀ i, Path (p i) (r i))
    (f : N → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 1 f)
    (P Q : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U) (hrange : range f ⊆ U)
    (hP : ContinuousOn P U) (hQ : ContinuousOn Q U)
    (Z : Set N) (hZ : Z.Finite)
    (hqimage : (⋃ i, (q i).extend '' Ioo (0 : ℝ) 1) = Zᶜ)
    (hqdisj : Pairwise (fun i j ↦ Disjoint
      ((q i).extend '' Ioo (0 : ℝ) 1) ((q j).extend '' Ioo (0 : ℝ) 1)))
    (hqinj : ∀ i, InjOn (q i).extend (Ioo (0 : ℝ) 1))
    (e : ∀ (i : ι) (z : E), E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) ((q i).extend (z 0)))
    (hqd : ∀ i (z : E), z 0 ∈ Ioo (0 : ℝ) 1 →
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (q i).extend (z 0)) z
        ((e i z).toContinuousLinearMap.comp
          (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hqo : ∀ i (z : E), z 0 ∈ Ioo (0 : ℝ) 1 →
      Orientation.map (Fin 1) (e i z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
          o.orientationAt ((q i).extend (z 0))) :
    IntegrableTopForm (mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) ∧
      (∀ i, CurveIntegrable (oneForm P Q) ((q i).map hf.continuous)) ∧
      integralTopForm o
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) =
          ∑ i, curveIntegral (oneForm P Q) ((q i).map hf.continuous) := by
  classical
  obtain ⟨l, rfl⟩ := o.exists_lift
  simp only [Manifold.Orientation.orientationAt_mk] at hqo
  let φ := mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)
  let R := fun i (z : E) ↦ (q i).extend (z 0)
  let D : Set E := (EuclideanSpace.proj 0) ⁻¹' Ioo (0 : ℝ) 1
  let γ := fun i ↦ (q i).map hf.continuous
  have hc : IsCompact (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ) φ) :=
    isCompact_univ.of_isClosed_subset
    (_root_.isClosed_tsupport (α := (EuclideanSpace ℝ (Fin 1)) [⋀^Fin _]→L[ℝ] ℝ) φ) (subset_univ _)
  have hφ := ContMDiff.isSmoothForm_mpullback_manifoldOneForm (n := 0) hf hU hrange
    (contDiffOn_zero.mpr hP) (contDiffOn_zero.mpr hQ)
  have hi := hφ.integrableTopForm hc (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  have heval (i : ι) (z : E) (hz : z ∈ D) :
      φ (R i z) (fun j ↦ e i z ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis j)) =
        circulationFun P Q (γ i).extend (z 0) := by
    exact Path.mpullback_manifoldOneForm_coefficient (q i) f hf.continuous P Q z
      (e i z).toContinuousLinearMap (hqd i z hz)
      ((hf (R i z)).mdifferentiableAt one_ne_zero)
  have hD : MeasurableSet D := measurableSet_Ioo.preimage
    (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable
  have hri (i : ι) : R i '' D = (q i).extend '' Ioo (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z 0, hz, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t), ht, rfl⟩
  have himage : (⋃ i, R i '' D) = Zᶜ := by simpa only [hri] using hqimage
  have hdisj : Pairwise (fun i j ↦ Disjoint (R i '' D) (R j '' D)) := by
    simpa only [hri] using hqdisj
  have hinj (i : ι) : InjOn (R i) D := by
    intro x hx y hy he
    have hp := hqinj i hx hy he
    ext j
    rw [Subsingleton.elim j 0]
    exact hp
  have hr := integralTopForm_eq_oriented_parametrizations l φ hi hD
    hZ himage hdisj hinj e hqd hqo
  have hic (i : ι) : IntervalIntegrable (circulationFun P Q (γ i).extend) volume 0 1 := by
    have hparam := (hr.1 i).congr_fun (heval i) hD
    have hci : IntegrableOn (circulationFun P Q (γ i).extend) (Ioo (0 : ℝ) 1) :=
      ((TauCeti.volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).integrableOn_comp_preimage
        (TauCeti.measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0)).mp hparam
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (integrableOn_congr_set_ae Ioo_ae_eq_Ioc).mp hci
  refine ⟨hi, fun i ↦ ?_, ?_⟩
  · rw [curveIntegrable_iff_intervalIntegrable_deriv]
    simpa only [← circulationFun_eq_oneForm] using hic i
  · rw [hr.2]
    apply Finset.sum_congr rfl
    intro i _
    rw [curveIntegral_oneForm_eq, setIntegral_congr_fun hD (heval i)]
    have hp :=
      (TauCeti.volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).setIntegral_preimage_emb
      (TauCeti.measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0)
      (circulationFun P Q (γ i).extend) (Ioo (0 : ℝ) 1)
    -- Read the Euclidean parameter integral as pullback along its measure-preserving projection.
    change (∫ z in (EuclideanSpace.proj 0) ⁻¹' Ioo (0 : ℝ) 1,
      circulationFun P Q (γ i).extend (EuclideanSpace.proj 0 z)) = _
    rw [hp, ← integral_Icc_eq_integral_Ioo,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

section SmoothBoundary

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (1 + 1)) M]
  [IsManifold (𝓡∂ (1 + 1)) ∞ M] [T2Space M] [CompactSpace M]

local instance boundaryComponentsIsManifold : IsManifold 𝓘(ℝ, E) ∞ ((𝓡∂ (1 + 1)).boundary M) :=
  isManifold_boundary M (by simp)

local instance boundaryComponentsCompactSpace : CompactSpace ((𝓡∂ (1 + 1)).boundary M) :=
  isCompact_iff_compactSpace.mp
    ((𝓡∂ (1 + 1)).isClosed_boundary (M := M)
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)).isCompact

/-- Global Stokes on an actual smooth boundary is the finite sum of oriented boundary-arc
curve integrals, allowing subdivisions whose endpoints differ. The area form is the actual
pullback of planar area, weighted by curl. -/
theorem integralTopForm_curl_area_eq_boundary_sum_curveIntegral {ι : Type*} [Fintype ι]
    (o : Manifold.Orientation (𝓡∂ (1 + 1)) M (Fin (1 + 1)))
    (f : M → ℂ) (hf : ContMDiff (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) 2 f)
    (P Q : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U) (hrange : range f ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (p r : ι → (𝓡∂ (1 + 1)).boundary M) (q : ∀ i, Path (p i) (r i))
    (Z : Set ((𝓡∂ (1 + 1)).boundary M)) (hZ : Z.Finite)
    (hqimage : (⋃ i, (q i).extend '' Ioo (0 : ℝ) 1) = Zᶜ)
    (hqdisj : Pairwise (fun i j ↦ Disjoint
      ((q i).extend '' Ioo (0 : ℝ) 1) ((q j).extend '' Ioo (0 : ℝ) 1)))
    (hqinj : ∀ i, InjOn (q i).extend (Ioo (0 : ℝ) 1))
    (e : ∀ (i : ι) (z : E), E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) ((q i).extend (z 0)))
    (hqd : ∀ i (z : E), z 0 ∈ Ioo (0 : ℝ) 1 →
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (q i).extend (z 0)) z
        ((e i z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hqo : ∀ i (z : E), z 0 ∈ Ioo (0 : ℝ) 1 →
      Orientation.map (Fin 1) (e i z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
          (boundaryOrientation o).orientationAt ((q i).extend (z 0))) :
    let g := fun x : (𝓡∂ (1 + 1)).boundary M ↦ f x
    let hg : Continuous g := hf.continuous.comp continuous_subtype_val
    IntegrableTopForm (fun x ↦ curl P Q (f x) •
      mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f manifoldAreaForm x) ∧
      (∀ i, CurveIntegrable (oneForm P Q) ((q i).map hg)) ∧
      integralTopForm o (fun x ↦ curl P Q (f x) •
        mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f manifoldAreaForm x) =
          ∑ i, curveIntegral (oneForm P Q) ((q i).map hg) := by
  obtain ⟨l, rfl⟩ := o.exists_lift
  let φ := mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)
  let g := fun x : (𝓡∂ (1 + 1)).boundary M ↦ f x
  have hinc := (isSmoothEmbedding_subtypeVal_boundary (n := 1) M
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)).contMDiff
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 1 g :=
    (hf.of_le (by norm_num)).comp (hinc.of_le (by simp))
  have he : boundaryRestriction φ = mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) g
      (manifoldOneForm P Q) := by
    exact boundaryRestriction_mpullback (hf.mdifferentiable (by norm_num)) (manifoldOneForm P Q)
  have hφ := ContMDiff.isSmoothForm_mpullback_manifoldOneForm (n := 1) hf hU hrange hP hQ
  have hc : IsCompact (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 2)) [⋀^Fin _]→L[ℝ] ℝ) φ) :=
    isCompact_univ.of_isClosed_subset
    (_root_.isClosed_tsupport (α := (EuclideanSpace ℝ (Fin 2)) [⋀^Fin _]→L[ℝ] ℝ) φ) (subset_univ _)
  have hi := hφ.continuous_mextDeriv.integrableTopForm
    (RoughForm.isCompact_tsupport_mextDeriv hc)
    (EuclideanSpace.basisFun (Fin (1 + 1)) ℝ).toBasis
  have hd := ContMDiff.mextDeriv_mpullback_manifoldOneForm hf
    (fun x ↦ ((hP (f x) (hrange (mem_range_self x))).contDiffAt
      (hU.mem_nhds (hrange (mem_range_self x)))).differentiableAt one_ne_zero)
    (fun x ↦ ((hQ (f x) (hrange (mem_range_self x))).contDiffAt
      (hU.mem_nhds (hrange (mem_range_self x)))).differentiableAt one_ne_zero)
  have hr := integralTopForm_mpullback_eq_sum_curveIntegral
    (boundaryOrientation (Manifold.Orientation.mk l)) p r q g hg P Q U hU
    (by rintro z ⟨x, rfl⟩; exact hrange (mem_range_self x.val))
    hP.continuousOn hQ.continuousOn Z hZ hqimage hqdisj hqinj e hqd hqo
  refine ⟨hd ▸ hi, hr.2.1, ?_⟩
  rw [← hd, integralTopForm_mextDeriv (Manifold.Orientation.mk l) hφ hc, he]
  exact hr.2.2

/-- The genuine smooth-boundary comparison with coordinate area: for an injective positively
oriented planar immersion, Stokes is Green over its actual image and the actual boundary
arcs. Both planar area and all boundary curve integrabilities are conclusions. -/
theorem integral_image_curl_eq_boundary_sum_curveIntegral {ι : Type*} [Fintype ι]
    (o : Manifold.Orientation (𝓡∂ (1 + 1)) M (Fin (1 + 1)))
    (f : M → ℂ) (hf : ContMDiff (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) 2 f)
    (hinj : Function.Injective f)
    (F : M → EuclideanSpace ℝ (Fin (1 + 1)) ≃L[ℝ] ℂ)
    (hF : ∀ x, (F x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
        (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f x))
    (hFo : ∀ x, Orientation.map (Fin (1 + 1)) (F x).toLinearEquiv
      -- Fix the common Euclidean tangent model so orientation transport ignores base-point
      -- wrappers.
      (show Orientation ℝ (EuclideanSpace ℝ (Fin (1 + 1))) (Fin (1 + 1)) from
        o.orientationAt x) = Complex.orientation)
    (P Q : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U) (hrange : range f ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (p r : ι → (𝓡∂ (1 + 1)).boundary M) (q : ∀ i, Path (p i) (r i))
    (Z : Set ((𝓡∂ (1 + 1)).boundary M)) (hZ : Z.Finite)
    (hqimage : (⋃ i, (q i).extend '' Ioo (0 : ℝ) 1) = Zᶜ)
    (hqdisj : Pairwise (fun i j ↦ Disjoint
      ((q i).extend '' Ioo (0 : ℝ) 1) ((q j).extend '' Ioo (0 : ℝ) 1)))
    (hqinj : ∀ i, InjOn (q i).extend (Ioo (0 : ℝ) 1))
    (e : ∀ (i : ι) (z : E), E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) ((q i).extend (z 0)))
    (hqd : ∀ i (z : E), z 0 ∈ Ioo (0 : ℝ) 1 →
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (q i).extend (z 0)) z
        ((e i z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hqo : ∀ i (z : E), z 0 ∈ Ioo (0 : ℝ) 1 →
      Orientation.map (Fin 1) (e i z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
          (boundaryOrientation o).orientationAt ((q i).extend (z 0))) :
    let g := fun x : (𝓡∂ (1 + 1)).boundary M ↦ f x
    let hg : Continuous g := hf.continuous.comp continuous_subtype_val
    IntegrableOn (curl P Q) (range f) ∧
      (∀ i, CurveIntegrable (oneForm P Q) ((q i).map hg)) ∧
      (∫ z in range f, curl P Q z) =
          ∑ i, curveIntegral (oneForm P Q) ((q i).map hg) := by
  have hr := integralTopForm_curl_area_eq_boundary_sum_curveIntegral
    o f hf P Q U hU hrange hP hQ p r q
    Z hZ hqimage hqdisj hqinj e hqd hqo
  have he : mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f
      (fun z ↦ curl P Q z • manifoldAreaForm z) =
      (fun x ↦ curl P Q (f x) • mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f manifoldAreaForm x) := by
    ext x v
    simp only [mpullback_apply, ContinuousAlternatingMap.smul_apply]
  have hi : IntegrableTopForm (mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f
      (fun z ↦ curl P Q z • manifoldAreaForm z)) := he.symm ▸ hr.1
  obtain ⟨l, rfl⟩ := o.exists_lift
  have ha := integralTopForm_mpullback_area_eq_integral_image l
    (hf.mdifferentiable (by norm_num)) hinj F hF hFo (curl P Q) hi
  refine ⟨ha.1, hr.2.1, ?_⟩
  rw [he] at ha
  exact ha.2.symm.trans hr.2.2

end SmoothBoundary

end TauCeti.Green
