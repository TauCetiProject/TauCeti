/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.PDE.Ellipticity.Compact
import TauCeti.Analysis.PDE.Regularity.Semilinear
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.ContMDiff.LocalRepresentative
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Chart
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# Smoothness of semilinear weak solutions on closed Riemannian manifolds

Let `M` be a closed smooth Riemannian manifold of dimension at most three, and let `w ∈ H¹(M)`
solve the semilinear elliptic equation

`Δ⁺w = A Φ(w) + C`

weakly against smooth test functions, where `A, C : M → ℝ` and `Φ : ℝ → ℝ` are smooth and the
forcing `A Φ(w) + C` is square integrable on `M`. This file proves that `w` agrees almost
everywhere with a smooth classical solution `u : M → ℝ` satisfying `-Δu = A Φ(u) + C` pointwise
everywhere on `M` (`TauCeti.Manifold.SobolevH1.exists_contMDiff_of_forall_dirichletForm_eq`).

## The argument

Around each point `p ∈ M`, the model space `E` is identified with `EuclideanSpace ℝ (Fin d)` via
`Module.finBasis ℝ E`, so that the pullback of the model-space Haar measure is Lebesgue measure
with factor `1`. Reading `H¹(M)` in the chart at `p`
(`TauCeti.Manifold.SobolevH1.exists_continuousLinearMap_w1p_extChartAt`) yields a bounded operator
`T : H¹(M) → W^{1,2}(Ω)` on an open neighbourhood `Ω` of the chart image of `p`. On a coordinate
ball `B` with compact closure inside `Ω`, the coordinate Dirichlet energy has coefficient matrix
`a(y) = ρ(Ψ(y)) g⁻¹(Ψ(y))`, where `ρ = √det(g)` is the chart volume density and `g⁻¹` is the
inverse chart Gram matrix. Since `a` is smooth and pointwise positive-definite on `closedBall`, it
is uniformly elliptic on `B` (`TauCeti.PDE.exists_uniformlyEllipticOn_of_posDef`). Transplanting
Euclidean test functions `φ ∈ 𝓓(B, ℝ)` to smooth functions on `M` shows that `T w` solves the
divergence-form semilinear equation `-div(a ∇(T w)) = (ρ A) Φ(T w) + ρ C` in `B`, with forcing
square integrable on `B`. The Euclidean semilinear regularity theorem
(`UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_forall_energyFormH1_ofTestFunctionₗ_eq`)
produces a smooth representative of `T w` on `B`, which pulls back to a smooth representative of
`w` on an open neighbourhood of `p`. Gluing the local smooth representatives
(`TauCeti.Manifold.exists_contMDiff_ae_eq_of_locally`) gives a global smooth function `u` with
`toLp w =ᵐ u`, and Green's identity turns the weak equation into the pointwise PDE
`-Δu = A Φ(u) + C`.

## Main results

* `TauCeti.Manifold.SobolevH1.neg_laplaceBeltrami_eq_of_forall_dirichletForm_ofSmooth_eq`: a
  smooth function satisfying `D(u, ψ) = ∫ f ψ dV` for continuous `f` solves `-Δu = f` pointwise.
* `TauCeti.Manifold.SobolevH1.exists_contMDiff_of_forall_dirichletForm_eq`: in dimension `< 4`,
  every `H¹(M)` weak solution of `Δ⁺w = A Φ(w) + C` with `L²` forcing has a smooth representative
  solving `-Δu = A Φ(u) + C` everywhere.
-/

public section

open Bundle MeasureTheory Metric Module Riemannian.Tensor Set TauCeti TauCeti.Manifold
  TauCeti.PDE TopologicalSpace
open scoped ContDiff Distributions Manifold Gradient ENNReal InnerProductSpace Matrix

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Coordinate Euclidean space of the same dimension as the model space `E`. -/
private abbrev CoordSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The continuous linear equivalence identifying the model space `E` with
`EuclideanSpace ℝ (Fin (finrank ℝ E))` by sending `Module.finBasis ℝ E` to the standard
orthonormal basis. -/
private def finBasisEquivEuclidean : E ≃L[ℝ] CoordSpace E :=
  ((Module.finBasis ℝ E).equiv
    (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis (Equiv.refl _))
    |>.toContinuousLinearEquiv

private theorem finBasisEquivEuclidean_symm_basisFun (k : Fin (Module.finrank ℝ E)) :
    (finBasisEquivEuclidean (E := E)).symm
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ k) =
      Module.finBasis ℝ E k := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  simp [finBasisEquivEuclidean]

section CoordinateGeometry

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Coordinate expression of the inverse chart composed with `finBasisEquivEuclidean.symm`. -/
private abbrev coordMap (p : M) (y : CoordSpace E) : M :=
  (extChartAt I p).symm ((finBasisEquivEuclidean (E := E)).symm y)

/-- The open manifold preimage of a coordinate open set `B` in `CoordSpace E`. -/
private def coordPreimage (p : M) (B : Opens (CoordSpace E)) : Set M :=
  (extChartAt I p).source ∩
    extChartAt I p ⁻¹' ((finBasisEquivEuclidean (E := E)).symm '' (B : Set _))

private theorem isOpen_coordPreimage (p : M) (B : Opens (CoordSpace E)) :
    IsOpen (coordPreimage (I := I) p B) :=
  isOpen_extChartAt_preimage' p
    ((finBasisEquivEuclidean (E := E)).symm.toHomeomorph.isOpenMap _ B.isOpen)

private theorem coordPreimage_subset_chartAt_source (p : M) (B : Opens (CoordSpace E)) :
    coordPreimage (I := I) p B ⊆ (chartAt H p).source := by
  rw [← extChartAt_source (I := I)]
  exact inter_subset_left

private theorem image_extChartAt_coordPreimage (p : M) {B : Opens (CoordSpace E)}
    (hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set _) (extChartAt I p).target) :
    extChartAt I p '' coordPreimage (I := I) p B =
      (finBasisEquivEuclidean (E := E)).symm '' (B : Set _) := by
  have hsub' : (finBasisEquivEuclidean (E := E)).symm '' (B : Set _) ⊆ (extChartAt I p).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact hBt hy
  rw [coordPreimage, PartialEquiv.image_source_inter_eq',
    PartialEquiv.target_inter_inv_preimage_preimage, inter_eq_right.2 hsub']

private theorem coordMap_mem_trivializationAt_baseSet [IsManifold I 1 M] (p : M) {y : CoordSpace E}
    (hy : (finBasisEquivEuclidean (E := E)).symm y ∈ (extChartAt I p).target) :
    coordMap (I := I) p y ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
  exact (extChartAt I p).map_target hy

end CoordinateGeometry

section CoordinateHelpers

/-- Because `finBasisEquivEuclidean` sends `Module.finBasis ℝ E` to the standard orthonormal basis
of `EuclideanSpace`, its inverse preserves Lebesgue measure to the basis Haar measure on `E`. -/
private theorem measurePreserving_finBasisEquivEuclidean_symm [MeasurableSpace E] [BorelSpace E] :
    MeasurePreserving (finBasisEquivEuclidean (E := E)).symm volume
      (Module.finBasis ℝ E).addHaar := by
  refine ⟨(finBasisEquivEuclidean (E := E)).symm.continuous.measurable, ?_⟩
  rw [← (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume,
    Module.Basis.map_addHaar]
  congr 1
  ext k
  simpa using finBasisEquivEuclidean_symm_basisFun (E := E) k

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The coordinate divergence-form coefficient matrix `a(y) = ρ(Ψ y) g⁻¹(Ψ y)` in the chart at
`p`. -/
private def chartCoeff (p : M) (y : CoordSpace E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  chartVolumeDensity (I := I) p (coordMap (I := I) p y) •
    chartInvGramMatrix (I := I) p (coordMap (I := I) p y)

section Boundaryless

variable [I.Boundaryless]

/-- Coordinate expression of a single directional component of the Euclidean gradient of a function
read through `finBasisEquivEuclidean`. -/
private theorem gradient_comp_coord_apply (p : M) {y : CoordSpace E}
    (hy : (finBasisEquivEuclidean (E := E)).symm y ∈ (extChartAt I p).target)
    {f : M → ℝ} (hf : MDifferentiableAt I 𝓘(ℝ) f (coordMap (I := I) p y))
    (k : Fin (Module.finrank ℝ E)) :
    (∇ (fun z ↦ f (coordMap (I := I) p z)) y) k =
      ⟪chartLocalFrame (I := I) p k (coordMap (I := I) p y),
        mgradient I f (coordMap (I := I) p y)⟫_ℝ := by
  set x := coordMap (I := I) p y
  have hxs : x ∈ (chartAt H p).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target hy
  have hfx : extChartAt I p x = (finBasisEquivEuclidean (E := E)).symm y :=
    (extChartAt I p).right_inv hy
  have hcoord : (∇ (fun z ↦ f (coordMap (I := I) p z)) y) k =
      ⟪∇ (fun z ↦ f (coordMap (I := I) p z)) y,
        EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ k⟫_ℝ := by
    rw [EuclideanSpace.inner_basisFun_real]
  rw [hcoord, inner_gradient_left]
  have hcomp : (fun z ↦ f (coordMap (I := I) p z)) =
      (f ∘ (extChartAt I p).symm) ∘ (finBasisEquivEuclidean (E := E)).symm := rfl
  rw [hcomp, (finBasisEquivEuclidean (E := E)).symm.comp_right_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    finBasisEquivEuclidean_symm_basisFun, ← hfx, ← mvfderiv_chartLocalFrame p hxs hf k,
    ← inner_mgradient_right]

/-- Pointwise coordinate expression of the Riemannian Dirichlet integrand:
`ρ(Ψ y) ⟪∇u(Ψ y), ∇v(Ψ y)⟫ = ⟨∇(v ∘ Ψ)(y), (ρ(Ψ y) g⁻¹(Ψ y)) ∇(u ∘ Ψ)(y)⟩`. -/
private theorem chartVolumeDensity_mul_inner_mgradient_eq_matrixBilinearForm (p : M)
    {y : CoordSpace E}
    (hy : (finBasisEquivEuclidean (E := E)).symm y ∈ (extChartAt I p).target)
    {u v : M → ℝ}
    (hu : MDifferentiableAt I 𝓘(ℝ) u (coordMap (I := I) p y))
    (hv : MDifferentiableAt I 𝓘(ℝ) v (coordMap (I := I) p y)) :
    chartVolumeDensity (I := I) p (coordMap (I := I) p y) *
        ⟪mgradient I u (coordMap (I := I) p y), mgradient I v (coordMap (I := I) p y)⟫_ℝ =
      matrixBilinearForm (chartCoeff (I := I) p y)
        (∇ (fun z ↦ v (coordMap (I := I) p z)) y)
        (∇ (fun z ↦ u (coordMap (I := I) p z)) y) := by
  set x := coordMap (I := I) p y
  have hxs : x ∈ (chartAt H p).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target hy
  have hinner : ⟪mgradient I u x, mgradient I v x⟫_ℝ =
      ∑ i, ⟪chartLocalFrame (I := I) p i x, mgradient I v x⟫_ℝ *
        ∑ j, chartInvGramMatrix (I := I) p x i j *
          ⟪chartLocalFrame (I := I) p j x, mgradient I u x⟫_ℝ := by
    rw [real_inner_comm]
    conv_lhs => rw [← (sum_inner_chartDualFrame_smul (I := I) p hxs (mgradient I v x)).2]
    simp only [sum_inner, real_inner_smul_left, chartDualFrame_apply]
  rw [hinner, chartCoeff, matrixBilinearForm_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [gradient_comp_coord_apply p hy hv i]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [gradient_comp_coord_apply p hy hu j]
  ring

end Boundaryless

section ChartIntegrals

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem setIntegral_coordPreimage (p : M) {B : Opens (CoordSpace E)}
    (hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set _) (extChartAt I p).target)
    (h : M → ℝ) :
    ∫ x in coordPreimage (I := I) p B, h x ∂riemannianVolume I M =
      ∫ y in (B : Set _),
        chartVolumeDensity (I := I) p (coordMap (I := I) p y) * h (coordMap (I := I) p y) := by
  let _ : MeasurableSpace E := extChartAtMeasurableSpaceE
  have _ : BorelSpace E := extChartAtBorelSpaceE
  have hL_emb :=
    (finBasisEquivEuclidean (E := E)).symm.toHomeomorph.isOpenEmbedding.measurableEmbedding
  rw [setIntegral_riemannianVolume_of_subset (coordPreimage_subset_chartAt_source p B)
      (isOpen_coordPreimage p B).measurableSet,
    image_extChartAt_coordPreimage p hBt,
    (measurePreserving_finBasisEquivEuclidean_symm (E := E)).setIntegral_image_emb hL_emb]
  simp [coordMap]

private theorem setLIntegral_coordPreimage (p : M) {B : Opens (CoordSpace E)}
    (hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set _) (extChartAt I p).target)
    (h : M → ℝ≥0∞) :
    ∫⁻ x in coordPreimage (I := I) p B, h x ∂riemannianVolume I M =
      ∫⁻ y in (B : Set _),
        ENNReal.ofReal (chartVolumeDensity (I := I) p (coordMap (I := I) p y)) *
          h (coordMap (I := I) p y) := by
  let _ : MeasurableSpace E := extChartAtMeasurableSpaceE
  have _ : BorelSpace E := extChartAtBorelSpaceE
  have hL_emb :=
    (finBasisEquivEuclidean (E := E)).symm.toHomeomorph.isOpenEmbedding.measurableEmbedding
  rw [setLIntegral_riemannianVolume_of_subset (coordPreimage_subset_chartAt_source p B)
      (isOpen_coordPreimage p B).measurableSet,
    image_extChartAt_coordPreimage p hBt,
    ← (measurePreserving_finBasisEquivEuclidean_symm (E := E)).setLIntegral_comp_emb hL_emb]

end ChartIntegrals

end CoordinateHelpers

section SmoothChartCoeff

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Smoothness of the chart volume density and coordinate coefficient matrix on any subset mapping
into the chart target. -/
private theorem contDiffOn_chartVolumeDensity_and_chartCoeff (p : M) {S : Set (CoordSpace E)}
    (hSt : MapsTo (finBasisEquivEuclidean (E := E)).symm S (extChartAt I p).target) :
    ContDiffOn ℝ ∞ (fun y ↦ chartVolumeDensity (I := I) p (coordMap (I := I) p y)) S ∧
      ∀ i j, ContDiffOn ℝ ∞ (fun y ↦ chartCoeff (I := I) p y i j) S := by
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hΨ : ContMDiffOn 𝓘(ℝ, CoordSpace E) I ∞ (coordMap (I := I) p) S :=
    (contMDiffOn_extChartAt_symm p).comp
      (finBasisEquivEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn hSt
  have hbase : MapsTo (coordMap (I := I) p) S (trivializationAt E (TangentSpace I) p).baseSet :=
    fun _ hy ↦ coordMap_mem_trivializationAt_baseSet p (hSt hy)
  have hρ : ContDiffOn ℝ ∞ (fun y ↦ chartVolumeDensity (I := I) p (coordMap (I := I) p y)) S :=
    ((contMDiffOn_chartVolumeDensity (I := I) (n := ∞) p).comp hΨ hbase).contDiffOn
  refine ⟨hρ, fun i j ↦ ?_⟩
  have hinv : ContDiffOn ℝ ∞
      (fun y ↦ chartInvGramMatrix (I := I) p (coordMap (I := I) p y) i j) S :=
    ((contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) p i j).comp hΨ hbase).contDiffOn
  simpa [chartCoeff] using hρ.mul hinv

/-- Uniform ellipticity of the coordinate coefficient matrix `chartCoeff` on any compact subset
mapping into the chart target. -/
private theorem exists_uniformlyEllipticOn_chartCoeff (p : M) {K : Set (CoordSpace E)}
    (hK : IsCompact K)
    (hKt : MapsTo (finBasisEquivEuclidean (E := E)).symm K (extChartAt I p).target) :
    ∃ lam Lam, UniformlyEllipticOn K (chartCoeff (I := I) p) lam Lam := by
  have hsm := (contDiffOn_chartVolumeDensity_and_chartCoeff (I := I) p hKt).2
  have hcont : ContinuousOn (chartCoeff (I := I) p) K :=
    continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦ (hsm i j).continuousOn
  refine exists_uniformlyEllipticOn_of_posDef hK hcont fun y hy ↦ ?_
  have hbase := coordMap_mem_trivializationAt_baseSet (I := I) p (hKt hy)
  rw [chartCoeff, chartInvGramMatrix_def]
  exact ((posDef_chartGramMatrix (I := I) p hbase).inv).smul
    (chartVolumeDensity_pos (I := I) p hbase)

end SmoothChartCoeff

section Regularity

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **From the weak equation to the pointwise PDE.** If a smooth function `u` on a closed manifold
with a `C¹` Riemannian metric satisfies `D(u, ψ) = ∫ f ψ dV` for every smooth test function `ψ`,
where `f` is continuous, then `-Δu = f` holds at every point of `M`. -/
theorem neg_laplaceBeltrami_eq_of_forall_dirichletForm_ofSmooth_eq
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (u : C^∞⟮I, M; ℝ⟯) {f : M → ℝ} (hf : Continuous f)
    (h : ∀ ψ : C^∞⟮I, M; ℝ⟯,
      dirichletForm (ofSmooth u) (ofSmooth ψ) =
        ∫ x, f x * ψ x ∂riemannianVolume I M) (x : M) :
    -laplaceBeltrami I u x = f x := by
  have hΔ : Continuous fun y ↦ -laplaceBeltrami I u y :=
    (continuous_laplaceBeltrami (u.contMDiff.of_le (by simp))).neg
  have hae : (fun y ↦ -laplaceBeltrami I u y) =ᵐ[riemannianVolume I M] f := by
    refine ae_eq_of_integral_contMDiff_smul_eq I hΔ.locallyIntegrable hf.locallyIntegrable
      fun ψ hψ _ ↦ ?_
    let ψ' : C^∞⟮I, M; ℝ⟯ := ⟨ψ, hψ⟩
    have hpair : dirichletForm (ofSmooth u) (ofSmooth ψ') =
        ∫ y, ψ y * -laplaceBeltrami I u y ∂riemannianVolume I M := by
      rw [dirichletForm_comm, dirichletForm_ofSmooth_right]
      refine integral_congr_ae ?_
      filter_upwards [toLp_ofSmooth_ae_eq ψ'] with y hy
      rw [hy]
      rfl
    have hrhs : dirichletForm (ofSmooth u) (ofSmooth ψ') =
        ∫ y, ψ y * f y ∂riemannianVolume I M :=
      (h ψ').trans <| integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ mul_comm (f y) (ψ y)
    simpa only [smul_eq_mul] using hpair.symm.trans hrhs
  exact congrFun (Measure.eq_of_ae_eq hae hΔ hf) x

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [I.Boundaryless] [T2Space M] in
/-- Transfer of `L²(M)` integrability to a coordinate open set `B` contained in a compact subset
of the chart target. -/
private theorem memLp_chartVolumeDensity_mul_comp (p : M)
    {B : Opens (CoordSpace E)} {K : Set (CoordSpace E)} (hK : IsCompact K)
    (hBK : (B : Set (CoordSpace E)) ⊆ K)
    (hKt : MapsTo (finBasisEquivEuclidean (E := E)).symm K (extChartAt I p).target)
    {f : M → ℝ} (hf : MemLp f 2 (riemannianVolume I M)) :
    MemLp (fun y ↦ chartVolumeDensity (I := I) p (coordMap (I := I) p y) *
      f (coordMap (I := I) p y)) 2 (volume.restrict (B : Set (CoordSpace E))) := by
  classical
  have hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set (CoordSpace E))
      (extChartAt I p).target := hKt.mono_left hBK
  have hρ_cont : ContinuousOn (fun y ↦ chartVolumeDensity (I := I) p (coordMap (I := I) p y)) K :=
    (contDiffOn_chartVolumeDensity_and_chartCoeff (I := I) p hKt).1.continuousOn
  have hΨ_cont : ContinuousOn (coordMap (I := I) p) (B : Set (CoordSpace E)) :=
    (continuousOn_extChartAt_symm p).comp
      (finBasisEquivEuclidean (E := E)).symm.continuous.continuousOn hBt
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · have hBe : (B : Set (CoordSpace E)) = ∅ := Set.subset_empty_iff.1 (hBK.trans hKe.subset)
    simp [hBe]
  obtain ⟨y₁, _, hy₁_max⟩ := hK.exists_isMaxOn hKne hρ_cont
  set M_ρ := chartVolumeDensity (I := I) p (coordMap (I := I) p y₁)
  -- Quasi-measure-preservation of the piecewise inverse chart on `B`.
  have hqmp : QuasiMeasurePreserving
      (Set.piecewise (B : Set (CoordSpace E)) (coordMap (I := I) p) (fun _ ↦ p))
      (volume.restrict (B : Set (CoordSpace E))) (riemannianVolume I M) := by
    have hmeas_pw : Measurable
        (Set.piecewise (B : Set (CoordSpace E)) (coordMap (I := I) p) (fun _ ↦ p)) :=
      ContinuousOn.measurable_piecewise hΨ_cont continuousOn_const B.isOpen.measurableSet
    refine ⟨hmeas_pw.aemeasurable, Measure.AbsolutelyContinuous.mk fun s hs hμs ↦ ?_⟩
    rw [Measure.map_apply hmeas_pw hs, Measure.restrict_apply (hmeas_pw hs)]
    have hnull_int :
        ∫⁻ y in (B : Set (CoordSpace E)),
            ENNReal.ofReal (chartVolumeDensity (I := I) p (coordMap (I := I) p y)) *
              s.indicator (1 : M → ℝ≥0∞) (coordMap (I := I) p y) = 0 := by
      rw [← setLIntegral_coordPreimage p hBt (s.indicator 1)]
      exact nonpos_iff_eq_zero.1 <|
        (lintegral_mono_set (subset_univ _)).trans (by simp [lintegral_indicator_one hs, hμs])
    have hmeas_ind : AEMeasurable
        (fun y ↦ ENNReal.ofReal (chartVolumeDensity (I := I) p (coordMap (I := I) p y)) *
          s.indicator (1 : M → ℝ≥0∞) (coordMap (I := I) p y))
        (volume.restrict (B : Set (CoordSpace E))) := by
      refine AEMeasurable.mul ?_ ?_
      · exact (ENNReal.continuous_ofReal.comp_continuousOn
          (hρ_cont.mono hBK)).aemeasurable B.isOpen.measurableSet
      · refine (((measurable_const (a := (1 : ℝ≥0∞))).indicator hs).comp
            hmeas_pw).aemeasurable.congr ?_
        filter_upwards [ae_restrict_mem B.isOpen.measurableSet] with y hy
        simp only [Function.comp_apply, Set.piecewise_eq_of_mem _ _ _ hy]
        rfl
    have hae0 := (lintegral_eq_zero_iff' hmeas_ind).1 hnull_int
    have hset0 : volume.restrict (B : Set (CoordSpace E))
        (Set.piecewise (B : Set (CoordSpace E)) (coordMap (I := I) p) (fun _ ↦ p) ⁻¹' s ∩
          (B : Set (CoordSpace E))) = 0 := by
      rw [← lintegral_indicator_one ((hmeas_pw hs).inter B.isOpen.measurableSet)]
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [hae0, ae_restrict_mem B.isOpen.measurableSet] with y hy0 hyB
      have hρ_pos : 0 < chartVolumeDensity (I := I) p (coordMap (I := I) p y) :=
        chartVolumeDensity_pos p (coordMap_mem_trivializationAt_baseSet p (hBt hyB))
      have h1 : s.indicator (1 : M → ℝ≥0∞) (coordMap (I := I) p y) = 0 := by
        rcases mul_eq_zero.1 hy0 with hρ0 | hind0
        · exact absurd hρ0 (ENNReal.ofReal_pos.2 hρ_pos).ne'
        · exact hind0
      have hnot : coordMap (I := I) p y ∉ s := fun h ↦ by simp [h] at h1
      have hnot' : y ∉ Set.piecewise (B : Set (CoordSpace E)) (coordMap (I := I) p) (fun _ ↦ p) ⁻¹'
          s ∩ (B : Set (CoordSpace E)) :=
        fun h ↦ hnot (by simpa [Set.piecewise_eq_of_mem _ _ _ hyB] using h.1)
      simp [hnot']
    rw [Measure.restrict_apply ((hmeas_pw hs).inter B.isOpen.measurableSet), inter_assoc,
      inter_self] at hset0
    exact hset0
  have hf_meas : AEStronglyMeasurable
      (fun y ↦ chartVolumeDensity (I := I) p (coordMap (I := I) p y) * f (coordMap (I := I) p y))
      (volume.restrict (B : Set (CoordSpace E))) := by
    have hfΨ : AEStronglyMeasurable (fun y ↦ f (coordMap (I := I) p y))
        (volume.restrict (B : Set (CoordSpace E))) := by
      refine (hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp).congr ?_
      filter_upwards [ae_restrict_mem B.isOpen.measurableSet] with y hy
      simp [Function.comp_apply, Set.piecewise_eq_of_mem _ _ _ hy]
    exact ((hρ_cont.mono hBK).aestronglyMeasurable B.isOpen.measurableSet).mul hfΨ
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by simp) (by simp) hf_meas]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hbound :
      ∫⁻ y in (B : Set (CoordSpace E)),
          ‖chartVolumeDensity (I := I) p (coordMap (I := I) p y) *
            f (coordMap (I := I) p y)‖ₑ ^ (2 : ℕ) ≤
        ENNReal.ofReal M_ρ * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂riemannianVolume I M := by
    calc ∫⁻ y in (B : Set (CoordSpace E)),
            ‖chartVolumeDensity (I := I) p (coordMap (I := I) p y) *
              f (coordMap (I := I) p y)‖ₑ ^ (2 : ℕ)
        ≤ ∫⁻ y in (B : Set (CoordSpace E)), ENNReal.ofReal M_ρ *
            (ENNReal.ofReal (chartVolumeDensity (I := I) p (coordMap (I := I) p y)) *
              ‖f (coordMap (I := I) p y)‖ₑ ^ (2 : ℕ)) := by
          refine setLIntegral_mono_ae' B.isOpen.measurableSet
            (Filter.Eventually.of_forall fun y hyB ↦ ?_)
          have hρ_nonneg := chartVolumeDensity_nonneg (I := I) p (coordMap (I := I) p y)
          have hρ_le : chartVolumeDensity (I := I) p (coordMap (I := I) p y) ≤ M_ρ :=
            hy₁_max (hBK hyB)
          rw [eNorm_mul, mul_pow, Real.eNorm_eq_ofReal hρ_nonneg, sq, mul_assoc]
          gcongr
      _ = ENNReal.ofReal M_ρ *
            ∫⁻ y in (B : Set (CoordSpace E)),
              ENNReal.ofReal (chartVolumeDensity (I := I) p (coordMap (I := I) p y)) *
                ‖f (coordMap (I := I) p y)‖ₑ ^ (2 : ℕ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal M_ρ *
            ∫⁻ x in coordPreimage (I := I) p B, ‖f x‖ₑ ^ (2 : ℕ) ∂riemannianVolume I M := by
          rw [setLIntegral_coordPreimage p hBt]
      _ ≤ ENNReal.ofReal M_ρ * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂riemannianVolume I M := by
          gcongr
          exact Measure.restrict_le_self
  have hf_lt : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂riemannianVolume I M < ⊤ := by
    have hlt := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (by simp) (by simp) hf.eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hlt
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf_lt)

omit [I.Boundaryless] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Transplanting a Euclidean test function `φ ∈ 𝓓(B, ℝ)` to a smooth function `ψ` on `M`
supported in `coordPreimage p B` and agreeing with `φ` in coordinates. -/
private theorem exists_contMDiff_of_testFunction (p : M) {B : Opens (CoordSpace E)}
    (hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set _) (extChartAt I p).target)
    (φ : 𝓓(B, ℝ)) :
    ∃ ψ : C^∞⟮I, M; ℝ⟯,
      tsupport (ψ : M → ℝ) ⊆ coordPreimage (I := I) p B ∧
        ∀ y ∈ (B : Set (CoordSpace E)), ψ (coordMap (I := I) p y) = φ y := by
  have htsupp_L : tsupport (φ ∘ finBasisEquivEuclidean (E := E)) ⊆
      (finBasisEquivEuclidean (E := E)).symm '' (B : Set (CoordSpace E)) := by
    have hsub : tsupport (φ ∘ finBasisEquivEuclidean (E := E)) ⊆
        (finBasisEquivEuclidean (E := E)) ⁻¹' tsupport φ :=
      closure_minimal (fun _ hz ↦ subset_tsupport _ hz)
        ((isClosed_tsupport _).preimage (finBasisEquivEuclidean (E := E)).continuous)
    intro z hz
    exact ⟨finBasisEquivEuclidean z, φ.tsupport_subset (hsub hz),
      (finBasisEquivEuclidean (E := E)).symm_apply_apply z⟩
  have htsupp_t : tsupport (φ ∘ finBasisEquivEuclidean (E := E)) ⊆ (extChartAt I p).target :=
    htsupp_L.trans (by rintro _ ⟨y, hy, rfl⟩; exact hBt hy)
  obtain ⟨ψ₀, hψ₀, _, hψ_supp, hψ_eq⟩ := exists_contMDiff_comp_extChartAt_symm_eq
    (φ.contDiff.comp (finBasisEquivEuclidean (E := E)).contDiff)
    (φ.hasCompactSupport.comp_homeomorph (finBasisEquivEuclidean (E := E)).toHomeomorph) htsupp_t
  let ψ : C^∞⟮I, M; ℝ⟯ := ⟨ψ₀, hψ₀⟩
  refine ⟨ψ, ?_, fun y hy ↦ ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hψ_supp hx
    refine ⟨(extChartAt I p).map_target (htsupp_t hz), ?_⟩
    rw [mem_preimage, (extChartAt I p).right_inv (htsupp_t hz)]
    exact htsupp_L hz
  · have h : ψ (coordMap (I := I) p y) =
        ψ₀ ((extChartAt I p).symm ((finBasisEquivEuclidean (E := E)).symm y)) := rfl
    rw [h, hψ_eq _ (hBt hy)]
    simp

omit [I.Boundaryless] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Pairing a function `f` on `M` against a transplanted test function `ψ` yields the weighted
coordinate integral over `B`. -/
private theorem integral_mul_of_tsupport_subset_coordPreimage (p : M) {B : Opens (CoordSpace E)}
    (hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set _) (extChartAt I p).target)
    {φ : 𝓓(B, ℝ)} {ψ : C^∞⟮I, M; ℝ⟯}
    (hψ_supp : tsupport (ψ : M → ℝ) ⊆ coordPreimage (I := I) p B)
    (hψ_comp : ∀ y ∈ (B : Set (CoordSpace E)), ψ (coordMap (I := I) p y) = φ y)
    (f : M → ℝ) :
    ∫ x, f x * ψ x ∂riemannianVolume I M =
      ∫ y in (B : Set _),
        (chartVolumeDensity (I := I) p (coordMap (I := I) p y) *
          f (coordMap (I := I) p y)) * φ y := by
  have hzero_rhs : ∀ x ∉ coordPreimage (I := I) p B, f x * ψ x = 0 := fun x hx ↦ by
    have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hψ_supp h)
    simp [hψx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero_rhs,
    setIntegral_coordPreimage p hBt]
  refine setIntegral_congr_fun B.isOpen.measurableSet fun y hyB ↦ ?_
  rw [hψ_comp y hyB, mul_assoc]

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- On smooth functions `u`, the manifold Dirichlet form against a transplanted test function `ψ`
agrees with the coordinate divergence-form energy `energyFormH1`. -/
private theorem dirichletForm_ofSmooth_eq_energyFormH1_ofTestFunctionₗ (p : M)
    {B : Opens (CoordSpace E)}
    (hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set _) (extChartAt I p).target)
    {φ : 𝓓(B, ℝ)} {ψ : C^∞⟮I, M; ℝ⟯}
    (hψ_supp : tsupport (ψ : M → ℝ) ⊆ coordPreimage (I := I) p B)
    (hψ_comp : ∀ y ∈ (B : Set (CoordSpace E)), ψ (coordMap (I := I) p y) = φ y)
    {u : C^∞⟮I, M; ℝ⟯} {U : W1p volume B 2}
    (hU_grad : (W1p.gradient U : CoordSpace E → CoordSpace E) =ᵐ[volume.restrict (B : Set _)]
      ∇ (fun y ↦ u (coordMap (I := I) p y))) :
    dirichletForm (ofSmooth u) (ofSmooth ψ) =
      energyFormH1 (chartCoeff (I := I) p) 0 0 U (W1p.ofTestFunctionₗ volume B 2 φ) := by
  have hzero_compl : ∀ x ∉ coordPreimage (I := I) p B,
      ⟪mgradient I u x, mgradient I ψ x⟫_ℝ = 0 := fun x hx ↦ by
    have hnot : x ∉ tsupport (ψ : M → ℝ) := fun h ↦ hx (hψ_supp h)
    have hg0 : mgradient I ψ x = 0 := mgradient_eq_zero_iff.2 <|
      (notMem_tsupport_iff_eventuallyEq.1 hnot).mvfderiv_eq.trans mvfderiv_zero
    simp [hg0]
  have hlhs : dirichletForm (ofSmooth u) (ofSmooth ψ) =
      ∫ y in (B : Set _),
        matrixBilinearForm (chartCoeff (I := I) p y)
          (∇ (φ : CoordSpace E → ℝ) y)
          (∇ (fun z ↦ u (coordMap (I := I) p z)) y) := by
    rw [dirichletForm_ofSmooth,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero_compl,
      setIntegral_coordPreimage p hBt]
    refine setIntegral_congr_fun B.isOpen.measurableSet fun y hyB ↦ ?_
    have hgrad_eq : ∇ (fun z ↦ ψ (coordMap (I := I) p z)) y = ∇ (φ : CoordSpace E → ℝ) y := by
      have hev : (fun z ↦ ψ (coordMap (I := I) p z)) =ᶠ[nhds y] (φ : CoordSpace E → ℝ) :=
        Filter.eventuallyEq_of_mem (B.isOpen.mem_nhds hyB) fun z hz ↦ hψ_comp z hz
      simp only [gradient, hev.fderiv_eq]
    rw [chartVolumeDensity_mul_inner_mgradient_eq_matrixBilinearForm p (hBt hyB)
      (u.contMDiff.mdifferentiable (by simp) _) (ψ.contMDiff.mdifferentiable (by simp) _),
      hgrad_eq]
  have hgrad_φ :
      (W1p.gradient (W1p.ofTestFunctionₗ volume B 2 φ) : CoordSpace E → CoordSpace E)
        =ᵐ[volume.restrict (B : Set _)] ∇ (φ : CoordSpace E → ℝ) := by
    rw [W1p.gradient_ofTestFunctionₗ]
    exact gradientTestFunctionLp_apply_ae (mu := volume) (Omega := B) 2 φ
  rw [hlhs, energyFormH1_zero_zero_eq_setIntegral]
  refine integral_congr_ae ?_
  filter_upwards [hU_grad, hgrad_φ] with y hgu hgφ
  rw [hgu, hgφ]

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Extending the Dirichlet-form identification from smooth functions to all `w ∈ H¹(M)` by
density. -/
private theorem dirichletForm_eq_energyFormH1_ofTestFunctionₗ (p : M)
    {B : Opens (CoordSpace E)}
    (hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set _) (extChartAt I p).target)
    {TB : SobolevH1 I M →L[ℝ] W1p volume B 2}
    (hTB_grad : ∀ u : C^∞⟮I, M; ℝ⟯,
      (W1p.gradient (TB (ofSmooth u)) : CoordSpace E → CoordSpace E)
        =ᵐ[volume.restrict (B : Set _)] ∇ (fun y ↦ u (coordMap (I := I) p y)))
    (hcoeff : MemLp
      (fun y ↦ energyIntegrand (chartCoeff (I := I) p y)
        ((0 : CoordSpace E → CoordSpace E) y) ((0 : CoordSpace E → ℝ) y)) ⊤
      (volume.restrict (B : Set _)))
    {φ : 𝓓(B, ℝ)} {ψ : C^∞⟮I, M; ℝ⟯}
    (hψ_supp : tsupport (ψ : M → ℝ) ⊆ coordPreimage (I := I) p B)
    (hψ_comp : ∀ y ∈ (B : Set (CoordSpace E)), ψ (coordMap (I := I) p y) = φ y)
    (w : SobolevH1 I M) :
    dirichletForm w (ofSmooth ψ) =
      energyFormH1 (chartCoeff (I := I) p) 0 0 (TB w) (W1p.ofTestFunctionₗ volume B 2 φ) := by
  refine SobolevH1.induction_on w ?_ fun u ↦
    dirichletForm_ofSmooth_eq_energyFormH1_ofTestFunctionₗ p hBt hψ_supp hψ_comp (hTB_grad u)
  have hcont_lhs : Continuous fun w' : SobolevH1 I M ↦ dirichletForm w' (ofSmooth ψ) :=
    (dirichletForm (I := I) (M := M)).flip (ofSmooth ψ) |>.continuous
  have hcont_rhs : Continuous fun w' : SobolevH1 I M ↦
      energyFormH1 (chartCoeff (I := I) p) 0 0 (TB w')
        (W1p.ofTestFunctionₗ volume B 2 φ) := by
    have heq : (fun w' : SobolevH1 I M ↦
        energyFormH1 (chartCoeff (I := I) p) 0 0 (TB w')
          (W1p.ofTestFunctionₗ volume B 2 φ)) =
        fun w' ↦ energyFormH1L hcoeff (TB w') (W1p.ofTestFunctionₗ volume B 2 φ) := by
      funext w'; exact (energyFormH1L_apply hcoeff _ _).symm
    rw [heq]
    exact ((energyFormH1L hcoeff).flip (W1p.ofTestFunctionₗ volume B 2 φ)).continuous.comp
      TB.continuous
  exact isClosed_eq hcont_lhs hcont_rhs

omit [I.Boundaryless] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Pulling back a smooth coordinate representative `v` on `B` to a smooth representative `g` of
`toLp w` on the chart neighbourhood `coordPreimage p B`. -/
private theorem exists_contMDiffOn_coordPreimage_ae_eq (p : M) {B : Opens (CoordSpace E)}
    (hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set _) (extChartAt I p).target)
    {w : SobolevH1 I M} {v : CoordSpace E → ℝ} (hv_sm : ContDiffOn ℝ ∞ v (B : Set _))
    (hv_ae : (fun y ↦ toLp w (coordMap (I := I) p y)) =ᵐ[volume.restrict (B : Set _)] v) :
    ∃ g : M → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ g (coordPreimage (I := I) p B) ∧
      (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict (coordPreimage (I := I) p B)] g := by
  let U := coordPreimage (I := I) p B
  let g : M → ℝ := fun x ↦ v (finBasisEquivEuclidean (extChartAt I p x))
  have hmaps_U : MapsTo (fun x ↦ finBasisEquivEuclidean (extChartAt I p x)) U
      (B : Set (CoordSpace E)) := by
    intro x hx
    obtain ⟨y, hyB, hyx⟩ := hx.2
    dsimp only
    have hxy : extChartAt I p x = (finBasisEquivEuclidean (E := E)).symm y := hyx.symm
    rw [hxy, (finBasisEquivEuclidean (E := E)).apply_symm_apply]
    exact hyB
  have hg_sm : ContMDiffOn I 𝓘(ℝ) ∞ g U :=
    hv_sm.contMDiffOn.comp
      ((finBasisEquivEuclidean (E := E)).contDiff.contMDiff.comp_contMDiffOn
        ((contMDiffOn_extChartAt (I := I) (x := p)).mono (coordPreimage_subset_chartAt_source p B)))
      hmaps_U
  refine ⟨g, hg_sm, ?_⟩
  have hvg : (fun y ↦ toLp w (coordMap (I := I) p y)) =ᵐ[volume.restrict (B : Set _)]
      fun y ↦ g (coordMap (I := I) p y) := by
    filter_upwards [hv_ae, ae_restrict_mem B.isOpen.measurableSet] with y hy hyB
    have hgv : g (coordMap (I := I) p y) = v y := by
      simp only [g, coordMap, (extChartAt I p).right_inv (hBt hyB),
        (finBasisEquivEuclidean (E := E)).apply_symm_apply]
    rw [hgv, hy]
  have hed_meas : AEMeasurable (fun x ↦ edist (toLp w x) (g x))
      ((riemannianVolume I M).restrict U) :=
    ((Lp.aestronglyMeasurable (toLp w)).restrict.aemeasurable).edist
      (hg_sm.continuousOn.aemeasurable (isOpen_coordPreimage p B).measurableSet)
  have hed_zero : ∫⁻ x in U, edist (toLp w x) (g x) ∂riemannianVolume I M = 0 := by
    rw [setLIntegral_coordPreimage p hBt]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hvg] with y hy
    simp [hy]
  exact ((lintegral_eq_zero_iff' hed_meas).1 hed_zero).mono fun x hx ↦ edist_eq_zero.1 hx

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Reading the manifold weak semilinear equation in a coordinate open set `B` yields the
divergence-form weak equation against Euclidean test functions `φ ∈ 𝓓(B, ℝ)`. -/
private theorem energyFormH1_ofTestFunctionₗ_eq_coord {A C : M → ℝ} {Φ : ℝ → ℝ}
    {w : SobolevH1 I M}
    (hw : ∀ ψ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth ψ) =
        ∫ x, (A x * Φ (toLp w x) + C x) * ψ x ∂riemannianVolume I M)
    (p : M) {B : Opens (CoordSpace E)}
    (hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set (CoordSpace E))
      (extChartAt I p).target)
    {TB : SobolevH1 I M →L[ℝ] W1p volume B 2}
    (hTB_val : (W1p.value (TB w) : CoordSpace E → ℝ) =ᵐ[volume.restrict (B : Set _)]
      fun y ↦ toLp w (coordMap (I := I) p y))
    (hTB_grad : ∀ u : C^∞⟮I, M; ℝ⟯,
      (W1p.gradient (TB (ofSmooth u)) : CoordSpace E → CoordSpace E)
        =ᵐ[volume.restrict (B : Set _)] ∇ (fun y ↦ u (coordMap (I := I) p y)))
    (hcoeff : MemLp
      (fun y ↦ energyIntegrand (chartCoeff (I := I) p y)
        ((0 : CoordSpace E → CoordSpace E) y) ((0 : CoordSpace E → ℝ) y)) ⊤
      (volume.restrict (B : Set (CoordSpace E))))
    (φ : 𝓓(B, ℝ)) :
    energyFormH1 (chartCoeff (I := I) p) 0 0 (TB w) (W1p.ofTestFunctionₗ volume B 2 φ) =
      ∫ y in (B : Set (CoordSpace E)),
        ((chartVolumeDensity (I := I) p (coordMap (I := I) p y) * A (coordMap (I := I) p y)) *
            Φ (W1p.value (TB w) y) +
          chartVolumeDensity (I := I) p (coordMap (I := I) p y) * C (coordMap (I := I) p y)) *
          φ y := by
  obtain ⟨ψ, hψ_supp, hψ_comp⟩ := exists_contMDiff_of_testFunction p hBt φ
  rw [← dirichletForm_eq_energyFormH1_ofTestFunctionₗ p hBt hTB_grad hcoeff hψ_supp hψ_comp w,
    hw ψ, integral_mul_of_tsupport_subset_coordPreimage p hBt hψ_supp hψ_comp]
  refine integral_congr_ae ?_
  filter_upwards [hTB_val] with y hy
  rw [hy]
  ring

/-- Euclidean semilinear elliptic regularity on a coordinate open set `B` with compact closure
inside the chart target. -/
private theorem exists_contDiffOn_coord_ae_eq (hE : Module.finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {w : SobolevH1 I M}
    (hf : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ ψ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth ψ) =
        ∫ x, (A x * Φ (toLp w x) + C x) * ψ x ∂riemannianVolume I M)
    (p : M) {B : Opens (CoordSpace E)} {K : Set (CoordSpace E)} (hK : IsCompact K)
    (hBK : (B : Set (CoordSpace E)) ⊆ K)
    (hKt : MapsTo (finBasisEquivEuclidean (E := E)).symm K (extChartAt I p).target)
    (TB : SobolevH1 I M →L[ℝ] W1p volume B 2)
    (hTB_val : (W1p.value (TB w) : CoordSpace E → ℝ) =ᵐ[volume.restrict (B : Set _)]
      fun y ↦ toLp w (coordMap (I := I) p y))
    (hTB_grad : ∀ u : C^∞⟮I, M; ℝ⟯,
      (W1p.gradient (TB (ofSmooth u)) : CoordSpace E → CoordSpace E)
        =ᵐ[volume.restrict (B : Set _)] ∇ (fun y ↦ u (coordMap (I := I) p y))) :
    ∃ v : CoordSpace E → ℝ, ContDiffOn ℝ ∞ v (B : Set (CoordSpace E)) ∧
      (W1p.value (TB w) : CoordSpace E → ℝ) =ᵐ[volume.restrict (B : Set _)] v := by
  have hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set (CoordSpace E))
      (extChartAt I p).target := hKt.mono_left hBK
  obtain ⟨hρ_sm, ha_sm⟩ := contDiffOn_chartVolumeDensity_and_chartCoeff (I := I) p hBt
  obtain ⟨lam, Lam, ha_K⟩ := exists_uniformlyEllipticOn_chartCoeff (I := I) p hK hKt
  have ha_ell : UniformlyEllipticOn (B : Set (CoordSpace E)) (chartCoeff (I := I) p) lam Lam :=
    ha_K.mono_set hBK
  have hcoeff :=
    memLp_energyIntegrand_of_bounds (mu := volume) (Omega := B) (a := chartCoeff (I := I) p)
      (b := 0) (c := 0) (beta := 0) (gamma := 0)
      ha_ell.upper_nonneg
      ((continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦
        (ha_sm i j).continuousOn).aestronglyMeasurable B.isOpen.measurableSet)
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun _ hy η ξ ↦ ha_ell.upper_bound hy η ξ) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
  have hΨ_sm : ContMDiffOn 𝓘(ℝ, CoordSpace E) I ∞ (coordMap (I := I) p)
      (B : Set (CoordSpace E)) :=
    (contMDiffOn_extChartAt_symm p).comp
      (finBasisEquivEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn hBt
  let A_B : CoordSpace E → ℝ :=
    fun y ↦ chartVolumeDensity (I := I) p (coordMap (I := I) p y) * A (coordMap (I := I) p y)
  let C_B : CoordSpace E → ℝ :=
    fun y ↦ chartVolumeDensity (I := I) p (coordMap (I := I) p y) * C (coordMap (I := I) p y)
  have hA_B : ContDiffOn ℝ ∞ A_B (B : Set (CoordSpace E)) :=
    hρ_sm.mul (hA.comp_contMDiffOn hΨ_sm).contDiffOn
  have hC_B : ContDiffOn ℝ ∞ C_B (B : Set (CoordSpace E)) :=
    hρ_sm.mul (hC.comp_contMDiffOn hΨ_sm).contDiffOn
  have hf_B : MemLp (fun y ↦ A_B y * Φ (W1p.value (TB w) y) + C_B y) 2
      (volume.restrict (B : Set (CoordSpace E))) := by
    refine (memLp_chartVolumeDensity_mul_comp p hK hBK hKt hf).ae_eq ?_
    filter_upwards [hTB_val] with y hy
    rw [hy]
    simp only [A_B, C_B]
    ring
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) < 4 := by simpa using hE
  exact ha_ell.exists_contDiffOn_ae_eq_of_forall_energyFormH1_ofTestFunctionₗ_eq hcard
    ha_sm hA_B hC_B hΦ
    (fun K' _ hK'B ↦ hf_B.mono_measure (Measure.restrict_mono hK'B le_rfl))
    (energyFormH1_ofTestFunctionₗ_eq_coord hw p hBt hTB_val hTB_grad hcoeff)

/-- **Local smoothness of a semilinear weak solution in a chart.** Around every point `p ∈ M` of a
closed smooth Riemannian manifold of dimension `< 4`, a weak `H¹(M)` solution of
`Δ⁺w = A Φ(w) + C` with smooth `A, C, Φ` and `L²` forcing agrees almost everywhere on an open
neighbourhood of `p` with a smooth function. -/
private theorem exists_nhds_contMDiffOn_ae_eq (hE : Module.finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {w : SobolevH1 I M}
    (hf : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ ψ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth ψ) =
        ∫ x, (A x * Φ (toLp w x) + C x) * ψ x ∂riemannianVolume I M)
    (p : M) :
    ∃ U ∈ nhds p, ∃ g : M → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ g U ∧
      (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict U] g := by
  obtain ⟨Ω, hpΩ, hΩt, T, hTu, hTw⟩ :=
    exists_continuousLinearMap_w1p_extChartAt (I := I) (M := M) p (finBasisEquivEuclidean (E := E))
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen _ hpΩ
  let c : CoordSpace E := finBasisEquivEuclidean (extChartAt I p p)
  let K : Set (CoordSpace E) := closedBall c (r / 2)
  let B : Opens (CoordSpace E) := ⟨ball c (r / 2), isOpen_ball⟩
  have hKΩ : K ⊆ (Ω : Set (CoordSpace E)) := (closedBall_subset_ball (by linarith)).trans hrΩ
  have hBK : (B : Set (CoordSpace E)) ⊆ K := ball_subset_closedBall
  have hBΩ : B ≤ Ω := hBK.trans hKΩ
  have hKt : MapsTo (finBasisEquivEuclidean (E := E)).symm K (extChartAt I p).target :=
    hΩt.mono_left hKΩ
  have hBt : MapsTo (finBasisEquivEuclidean (E := E)).symm (B : Set (CoordSpace E))
      (extChartAt I p).target := hKt.mono_left hBK
  let TB : SobolevH1 I M →L[ℝ] W1p volume B 2 := (W1p.restrictL hBΩ).comp T
  have hTB_val : (W1p.value (TB w) : CoordSpace E → ℝ) =ᵐ[volume.restrict (B : Set _)]
      fun y ↦ toLp w (coordMap (I := I) p y) :=
    (W1p.value_restrictL_ae hBΩ (T w)).trans
      (ae_restrict_of_ae_restrict_of_subset hBΩ (hTw w))
  have hTB_grad (u : C^∞⟮I, M; ℝ⟯) :
      (W1p.gradient (TB (ofSmooth u)) : CoordSpace E → CoordSpace E) =ᵐ[volume.restrict (B : Set _)]
        ∇ (fun y ↦ u (coordMap (I := I) p y)) :=
    (W1p.gradient_restrictL_ae hBΩ (T (ofSmooth u))).trans
      (ae_restrict_of_ae_restrict_of_subset hBΩ (hTu u).2)
  obtain ⟨v, hv_sm, hv_ae⟩ := exists_contDiffOn_coord_ae_eq hE hA hC hΦ hf hw p
    (isCompact_closedBall _ _) hBK hKt TB hTB_val hTB_grad
  obtain ⟨g, hg_sm, hg_ae⟩ :=
    exists_contMDiffOn_coordPreimage_ae_eq p hBt hv_sm (hTB_val.symm.trans hv_ae)
  have hpU : p ∈ coordPreimage (I := I) p B :=
    ⟨mem_extChartAt_source p, c, mem_ball_self (half_pos hr),
      (finBasisEquivEuclidean (E := E)).symm_apply_apply _⟩
  exact ⟨coordPreimage (I := I) p B, (isOpen_coordPreimage p B).mem_nhds hpU, g, hg_sm, hg_ae⟩

/-- **Smoothness of semilinear weak solutions on closed Riemannian manifolds.** Let `M` be a closed
smooth Riemannian manifold of dimension `< 4`, let `A, C : M → ℝ` and `Φ : ℝ → ℝ` be smooth, and
let `w ∈ H¹(M)` satisfy
`D(w, ψ) = ∫ (A Φ(w) + C) ψ dV`
for every smooth function `ψ`, with `A Φ(w) + C ∈ L²(M)`. Then `w` agrees almost everywhere with
a smooth classical solution `u : M → ℝ` of `-Δu = A Φ(u) + C`. -/
theorem exists_contMDiff_of_forall_dirichletForm_eq (hE : Module.finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {w : SobolevH1 I M}
    (hf : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ ψ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth ψ) =
        ∫ x, (A x * Φ (toLp w x) + C x) * ψ x ∂riemannianVolume I M) :
    ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧
      (toLp w : M → ℝ) =ᵐ[riemannianVolume I M] u ∧
      ∀ x, -laplaceBeltrami I u x = A x * Φ (u x) + C x := by
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  -- Glue local smooth representatives on the compact manifold `M`.
  obtain ⟨u, hu, hwu⟩ := exists_contMDiff_ae_eq_of_locally (I := I) (I' := 𝓘(ℝ)) (n := ∞)
    (μ := riemannianVolume I M)
    (exists_nhds_contMDiffOn_ae_eq hE hA hC hΦ hf hw)
  let u' : C^∞⟮I, M; ℝ⟯ := ⟨u, hu⟩
  have hweq : w = ofSmooth u' :=
    toLp_injective (Lp.ext (hwu.trans (toLp_ofSmooth_ae_eq u').symm))
  have hf_cont : Continuous fun x ↦ A x * Φ (u x) + C x :=
    (hA.continuous.mul (hΦ.continuous.comp hu.continuous)).add hC.continuous
  refine ⟨u, hu, hwu, neg_laplaceBeltrami_eq_of_forall_dirichletForm_ofSmooth_eq u' hf_cont ?_⟩
  intro ψ
  rw [← hweq, hw ψ]
  refine integral_congr_ae ?_
  filter_upwards [hwu] with x hx
  rw [hx]

end Regularity

end TauCeti.Manifold.SobolevH1

end
