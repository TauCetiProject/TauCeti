/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.PDE.EnergyForm.Sobolev
import TauCeti.Analysis.PDE.Regularity.Semilinear
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Chart
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz

/-!
# Elliptic regularity for semilinear equations on `H¹(M)`

Let `M` be a closed smooth Riemannian manifold of dimension at most three, and let `A, C : M → ℝ`
and `Φ : ℝ → ℝ` be smooth. This file proves that a weak solution `w ∈ H¹(M)` of the semilinear
equation

`Δ⁺w = A(x) Φ(w) + C(x)`

whose nonlinear forcing `A Φ(w) + C` lies in `L²(M)` is represented by a smooth function
`u : C^∞⟮I, M; ℝ⟯`: `w = ofSmooth u` in `H¹(M)`, and `u` solves `-Δu = A Φ(u) + C` everywhere
on `M` (`TauCeti.Manifold.SobolevH1.exists_contMDiff_of_forall_dirichletForm_ofSmooth_eq`).
Here `Δ⁺ = -div grad` is the nonnegative Laplace–Beltrami operator.

## The argument

Near each point `p ∈ M`, identify the model space `E` with `ℝⁿ` via the basis equivalence carrying
`Module.finBasis ℝ E` to the standard basis of `EuclideanSpace ℝ (Fin n)`. This pushes Lebesgue
measure on `ℝⁿ` forward to the Haar measure `(Module.finBasis ℝ E).addHaar` with constant `1`.
Restricting the chart operator
`TauCeti.Manifold.SobolevH1.exists_continuousLinearMap_w1p_extChartAt` to a precompact coordinate
ball `Ω` around the image of `p`, the Dirichlet form of `M` against transplanted smooth test
functions `η ∈ 𝓓(Ω, ℝ)` becomes the divergence-form energy form `energyFormH1 a 0 0` with smooth
symmetric uniformly elliptic coefficient matrix `a = ρ G⁻¹`, where `ρ` is the chart volume density
and `G⁻¹` is the inverse chart Gram matrix. Continuity in `w` extends this identity from smooth
functions to all of `H¹(M)`.

The Euclidean semilinear bootstrap
`TauCeti.PDE.UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_forall_energyFormH1_ofTestFunctionₗ_eq`
produces a smooth representative on `Ω`, which pulls back to a smooth representative of `w` on an
open neighbourhood `U_p` of `p`. Because the Riemannian volume is positive on nonempty open sets,
any two local smooth representatives agree on overlaps, so they glue to a global smooth function
`u`. Compactness yields `toLp w =ᵐ u`, injectivity of `toLp` identifies `w = ofSmooth u`, and
Green's identity with continuity yields the classical equation `-Δu = A Φ(u) + C` pointwise.

## Main results

* `TauCeti.Manifold.SobolevH1.exists_contMDiff_of_forall_dirichletForm_ofSmooth_eq`: in dimension
  at most three, a weak solution in `H¹(M)` of `Δ⁺w = A Φ(w) + C` tested against smooth functions,
  with `L²` forcing, is smooth and solves the classical equation everywhere.
* `TauCeti.Manifold.SobolevH1.exists_contMDiff_of_forall_dirichletForm_eq`: the corresponding
  statement when the weak equation is tested against all elements of `H¹(M)`.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Chapter 3.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.1.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.22 and 8.24.
-/

public section

open Bundle MeasureTheory Metric Module Riemannian.Tensor Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace TauCeti.Manifold.SobolevH1

/-! ### Canonical Euclidean coordinates for the model space -/

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The continuous linear equivalence identifying the model space `E` with
`EuclideanSpace ℝ (Fin (finrank ℝ E))` by carrying `Module.finBasis ℝ E` to the standard basis. -/
private def finBasisEquivEuclidean :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  ((Module.finBasis ℝ E).equiv
    (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
    (Equiv.refl _)).toContinuousLinearEquiv

private theorem finBasisEquivEuclidean_symm_basisFun (i : Fin (Module.finrank ℝ E)) :
    finBasisEquivEuclidean (E := E).symm
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ i) = Module.finBasis ℝ E i := by
  have h : finBasisEquivEuclidean (E := E) (Module.finBasis ℝ E i) =
      EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ i :=
    (Module.finBasis ℝ E).equiv_apply i
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis (Equiv.refl _)
  rw [← h, ContinuousLinearEquiv.symm_apply_apply]

/-- The inverse of `finBasisEquivEuclidean` carries Euclidean Lebesgue measure to the Haar measure
normalized by `Module.finBasis ℝ E`. -/
private theorem measurePreserving_finBasisEquivEuclidean_symm :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    MeasurePreserving (finBasisEquivEuclidean (E := E)).symm volume
      (Module.finBasis ℝ E).addHaar := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  refine ⟨(finBasisEquivEuclidean (E := E)).symm.continuous.measurable, ?_⟩
  rw [← (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume,
    Module.Basis.map_addHaar]
  congr 1
  ext i
  exact finBasisEquivEuclidean_symm_basisFun i

end Coordinates

/-! ### Transplanting test functions from Euclidean coordinates -/

section Transplant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Transplant a Euclidean test function `η : 𝓓(Ω, ℝ)` through `finBasisEquivEuclidean ∘ extChartAt`
to a smooth function on `M` supported in the chart preimage of `Ω`. -/
private theorem exists_transplant_testFunction (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo finBasisEquivEuclidean.symm Ω (extChartAt I p).target) (η : 𝓓(Ω, ℝ)) :
    ∃ φ : C^∞⟮I, M; ℝ⟯,
      tsupport (φ : M → ℝ) ⊆
          (extChartAt I p).source ∩
            extChartAt I p ⁻¹' (finBasisEquivEuclidean.symm '' (Ω : Set _)) ∧
        ∀ y ∈ Ω, φ ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)) = η y := by
  set L := finBasisEquivEuclidean (E := E)
  set wE : E → ℝ := η ∘ L
  have hwE_smooth : ContDiff ℝ ∞ wE := η.contDiff.comp L.contDiff
  have hwE_supp : HasCompactSupport wE := η.hasCompactSupport.comp_homeomorph L.toHomeomorph
  have htsupp_wE : tsupport wE ⊆ L.symm '' (Ω : Set _) := by
    intro z hz
    have hLz : L z ∈ tsupport (η : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ) :=
      (tsupport_comp_subset_preimage (η : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ)
        L.continuous) hz
    exact ⟨L z, η.tsupport_subset hLz, L.symm_apply_apply z⟩
  obtain ⟨u, hu, -, htsupp_u, hu_symm⟩ := exists_contMDiff_comp_extChartAt_symm_eq (I := I)
    (c := p) hwE_smooth hwE_supp (htsupp_wE.trans (image_subset_iff.2 hΩt))
  refine ⟨⟨u, hu⟩, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨z, hz, rfl⟩ := htsupp_u hx
    have hzt : z ∈ (extChartAt I p).target := (image_subset_iff.2 hΩt) (htsupp_wE hz)
    refine ⟨(extChartAt I p).map_target hzt, ?_⟩
    rw [mem_preimage, (extChartAt I p).right_inv hzt]
    exact htsupp_wE hz
  · exact (hu_symm (L.symm y) (hΩt hy)).trans (by simp [wE])

end Transplant

/-! ### Local coordinate representation of the Dirichlet form -/

section LocalCoord

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- In the Euclidean coordinates given by `finBasisEquivEuclidean` on the chart at `p`, the
inner product of two Riemannian gradients is the inverse Gram bilinear form evaluated on their
coordinate gradients. -/
private theorem inner_mgradient_eq_matrixBilinearForm [I.Boundaryless] (p : M)
    {y : EuclideanSpace ℝ (Fin (finrank ℝ E))}
    (hy : finBasisEquivEuclidean.symm y ∈ (extChartAt I p).target)
    {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 1 u) (hv : ContMDiff I 𝓘(ℝ) 1 v) :
    ⟪mgradient I u ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)),
        mgradient I v ((extChartAt I p).symm (finBasisEquivEuclidean.symm y))⟫_ℝ =
      PDE.matrixBilinearForm
        (chartInvGramMatrix (I := I) p ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)))
        (∇ (fun z ↦ v ((extChartAt I p).symm (finBasisEquivEuclidean.symm z))) y)
        (∇ (fun z ↦ u ((extChartAt I p).symm (finBasisEquivEuclidean.symm z))) y) := by
  set L := finBasisEquivEuclidean (E := E)
  set x := (extChartAt I p).symm (L.symm y)
  have hxs : x ∈ (chartAt H p).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target hy
  have hright : extChartAt I p x = L.symm y := (extChartAt I p).right_inv hy
  -- Each chart-frame derivative equals the corresponding Euclidean gradient component.
  have hcomp (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) 1 f) (k : Fin (finrank ℝ E)) :
      mvfderiv I f x (chartLocalFrame (I := I) p k x) =
        (∇ (fun z ↦ f ((extChartAt I p).symm (L.symm z))) y) k := by
    rw [mvfderiv_chartLocalFrame p hxs (hf.mdifferentiable one_ne_zero x) k, hright,
      ← finBasisEquivEuclidean_symm_basisFun k, ← EuclideanSpace.inner_basisFun_real,
      inner_gradient_left]
    have hfun : (fun z ↦ f ((extChartAt I p).symm (L.symm z))) =
        (f ∘ (extChartAt I p).symm) ∘ L.symm := rfl
    rw [hfun, L.symm.comp_right_fderiv, ContinuousLinearMap.comp_apply]
    rfl
  rw [inner_mgradient_right, mgradient_def, rieszDual_eq_sum_chartLocalFrame p hxs, map_sum,
    PDE.matrixBilinearForm_apply]
  simp only [map_smul, smul_eq_mul, dotProduct, mul_comm _ (mvfderiv I v x _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hcomp v hv i]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hcomp u hu j]

variable [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Continuity of the chart volume density in canonical Euclidean coordinates. -/
private theorem continuousOn_chartVolumeDensity_coord (p : M)
    {K : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hKt : MapsTo finBasisEquivEuclidean.symm K (extChartAt I p).target) :
    ContinuousOn
      (fun y ↦ chartVolumeDensity (I := I) p
        ((extChartAt I p).symm (finBasisEquivEuclidean.symm y))) K := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  exact (contMDiffOn_chartVolumeDensity (I := I) (n := 0) p).continuousOn.comp
    ((continuousOn_extChartAt_symm p).comp
      (finBasisEquivEuclidean (E := E)).symm.continuous.continuousOn hKt)
    fun y hy ↦ by
      simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
        (extChartAt I p).map_target (hKt hy)

/-- Continuity of the coordinate coefficient matrix `ρ G⁻¹` on a subset of the chart target. -/
private theorem continuousOn_coordCoeff (p : M)
    {K : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hKt : MapsTo finBasisEquivEuclidean.symm K (extChartAt I p).target) :
    ContinuousOn
      (fun y ↦ chartVolumeDensity (I := I) p
          ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)) •
        chartInvGramMatrix (I := I) p
          ((extChartAt I p).symm (finBasisEquivEuclidean.symm y))) K := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have hψ : ContinuousOn (fun y ↦ (extChartAt I p).symm (finBasisEquivEuclidean.symm y)) K :=
    (continuousOn_extChartAt_symm p).comp
      (finBasisEquivEuclidean (E := E)).symm.continuous.continuousOn hKt
  have hmaps : MapsTo (fun y ↦ (extChartAt I p).symm (finBasisEquivEuclidean.symm y)) K
      (trivializationAt E (TangentSpace I) p).baseSet := fun y hy ↦ by
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I p).map_target (hKt hy)
  have hG : ContinuousOn (fun y ↦ chartInvGramMatrix (I := I) p
      ((extChartAt I p).symm (finBasisEquivEuclidean.symm y))) K :=
    continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦
      (contMDiffOn_chartInvGramMatrix_entry (I := I) (n := 0) p i j).continuousOn.comp hψ hmaps
  exact (continuousOn_chartVolumeDensity_coord p hKt).smul hG

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Smoothness of the chart density and coefficient matrix `ρ G⁻¹`, together with uniform
ellipticity on a precompact coordinate ball. -/
private theorem exists_uniformlyEllipticOn_coordCoeff (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩc : IsCompact (closure (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))))
    (hΩct : MapsTo finBasisEquivEuclidean.symm
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) (extChartAt I p).target) :
    let ψ : EuclideanSpace ℝ (Fin (finrank ℝ E)) → M :=
      fun y ↦ (extChartAt I p).symm (finBasisEquivEuclidean.symm y)
    let a : EuclideanSpace ℝ (Fin (finrank ℝ E)) →
        Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ :=
      fun y ↦ chartVolumeDensity (I := I) p (ψ y) • chartInvGramMatrix (I := I) p (ψ y)
    ContDiffOn ℝ ∞ (fun y ↦ chartVolumeDensity (I := I) p (ψ y)) Ω ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun y ↦ a y i j) Ω) ∧
      ∃ lam Lam, PDE.UniformlyEllipticOn (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))
        a lam Lam := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set ψ : EuclideanSpace ℝ (Fin (finrank ℝ E)) → M :=
    fun y ↦ (extChartAt I p).symm (finBasisEquivEuclidean.symm y)
  have hψ_smooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) I ∞ ψ
      (finBasisEquivEuclidean.symm ⁻¹' (extChartAt I p).target) :=
    (contMDiffOn_extChartAt_symm p).comp
      (finBasisEquivEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn (mapsTo_preimage _ _)
  have hψ_maps : MapsTo ψ (finBasisEquivEuclidean.symm ⁻¹' (extChartAt I p).target)
      (trivializationAt E (TangentSpace I) p).baseSet := fun y hy ↦ by
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I p).map_target hy
  have hρ_smooth : ContDiffOn ℝ ∞ (fun y ↦ chartVolumeDensity (I := I) p (ψ y))
      (finBasisEquivEuclidean.symm ⁻¹' (extChartAt I p).target) :=
    ((contMDiffOn_chartVolumeDensity (I := I) (n := ∞) p).comp hψ_smooth hψ_maps).contDiffOn
  have hG_smooth (i j : Fin (finrank ℝ E)) :
      ContDiffOn ℝ ∞ (fun y ↦ chartInvGramMatrix (I := I) p (ψ y) i j)
        (finBasisEquivEuclidean.symm ⁻¹' (extChartAt I p).target) :=
    ((contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) p i j).comp
      hψ_smooth hψ_maps).contDiffOn
  have hΩt : MapsTo finBasisEquivEuclidean.symm Ω (extChartAt I p).target :=
    hΩct.mono_left subset_closure
  refine ⟨hρ_smooth.mono hΩt, fun i j ↦ (hρ_smooth.mul (hG_smooth i j)).mono hΩt, ?_⟩
  obtain ⟨lam, Lam, ha_ell⟩ :=
    PDE.exists_uniformlyEllipticOn_of_continuousOn_posDef hΩc (continuousOn_coordCoeff p hΩct)
      fun y hy ξ hξ ↦ by
        have hbase : ψ y ∈ (trivializationAt E (TangentSpace I) p).baseSet := hψ_maps (hΩct hy)
        have hρpos := chartVolumeDensity_pos (I := I) p hbase
        have hξ' : (ξ : Fin (finrank ℝ E) → ℝ) ≠ 0 := fun h ↦ hξ (WithLp.ofLp_injective 2 h)
        have hGpos := (posDef_chartGramMatrix (I := I) p hbase).inv.dotProduct_mulVec_pos hξ'
        rw [Matrix.toQuadraticForm'_smul, _root_.smul_apply, smul_eq_mul,
          Matrix.toQuadraticForm'_apply, chartInvGramMatrix_def]
        exact mul_pos hρpos (by simpa only [star_trivial] using hGpos)
  exact ⟨lam, Lam, ha_ell.mono_set subset_closure⟩

end LocalCoord

section VolumeCoord

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Integrating a function supported in the chart preimage of `Ω` against the Riemannian volume
turns into an integral over `Ω` weighted by the chart density. -/
private theorem integral_riemannianVolume_eq_setIntegral_coord (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo finBasisEquivEuclidean.symm Ω (extChartAt I p).target)
    {f : M → ℝ}
    (hf : Function.support f ⊆
      (extChartAt I p).source ∩
        extChartAt I p ⁻¹'
          (finBasisEquivEuclidean.symm '' (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))))) :
    ∫ x, f x ∂riemannianVolume I M =
      ∫ y in Ω, chartVolumeDensity (I := I) p
          ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)) *
        f ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)) := by
  let _ : MeasurableSpace E := extChartAtMeasurableSpaceE (E := E)
  have : BorelSpace E := extChartAtBorelSpaceE (E := E)
  set Ωs : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))) :=
    (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))
  set U : Set M :=
    (extChartAt I p).source ∩ extChartAt I p ⁻¹' (finBasisEquivEuclidean.symm '' Ωs)
  have hLΩ_open : IsOpen (finBasisEquivEuclidean.symm '' Ωs) :=
    (finBasisEquivEuclidean (E := E)).symm.toHomeomorph.isOpenMap _ Ω.isOpen
  have hU_open : IsOpen U := isOpen_extChartAt_preimage' p hLΩ_open
  have hU_sub : U ⊆ (chartAt H p).source := by
    rw [← extChartAt_source (I := I)]
    exact inter_subset_left
  have himage : extChartAt I p '' U = finBasisEquivEuclidean.symm '' Ωs := by
    rw [PartialEquiv.image_source_inter_eq', PartialEquiv.target_inter_inv_preimage_preimage,
      inter_eq_right.2 (image_subset_iff.2 hΩt)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
        Function.notMem_support.1 fun h ↦ hx (hf h),
    setIntegral_riemannianVolume_of_subset hU_sub hU_open.measurableSet, himage]
  have hpre : finBasisEquivEuclidean.symm ⁻¹' (finBasisEquivEuclidean.symm '' Ωs) = Ωs :=
    preimage_image_eq Ωs (finBasisEquivEuclidean (E := E)).symm.injective
  have hmp := measurePreserving_finBasisEquivEuclidean_symm (E := E)
  have hemb : MeasurableEmbedding (finBasisEquivEuclidean (E := E)).symm :=
    (finBasisEquivEuclidean (E := E)).symm.toHomeomorph.measurableEmbedding
  simpa only [hpre, smul_eq_mul] using (hmp.setIntegral_preimage_emb hemb
    (fun z ↦ chartVolumeDensity (I := I) p ((extChartAt I p).symm z) •
      f ((extChartAt I p).symm z)) (finBasisEquivEuclidean.symm '' Ωs)).symm

/-- Lebesgue integral over a coordinate open set against `riemannianVolume` in canonical
Euclidean coordinates. -/
private theorem setLIntegral_riemannianVolume_eq_coord (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo finBasisEquivEuclidean.symm Ω (extChartAt I p).target) (f : M → ℝ≥0∞) :
    ∫⁻ x in (extChartAt I p).source ∩
        extChartAt I p ⁻¹'
          (finBasisEquivEuclidean.symm '' (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))),
      f x ∂riemannianVolume I M =
      ∫⁻ y in Ω,
        ENNReal.ofReal (chartVolumeDensity (I := I) p
          ((extChartAt I p).symm (finBasisEquivEuclidean.symm y))) *
        f ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)) ∂volume := by
  let _ : MeasurableSpace E := extChartAtMeasurableSpaceE (E := E)
  have : BorelSpace E := extChartAtBorelSpaceE (E := E)
  set Ωs : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))) :=
    (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))
  have hLΩ_open : IsOpen (finBasisEquivEuclidean.symm '' Ωs) :=
    (finBasisEquivEuclidean (E := E)).symm.toHomeomorph.isOpenMap _ Ω.isOpen
  have hmp := measurePreserving_finBasisEquivEuclidean_symm (E := E)
  have hemb : MeasurableEmbedding (finBasisEquivEuclidean (E := E)).symm :=
    (finBasisEquivEuclidean (E := E)).symm.toHomeomorph.measurableEmbedding
  have hpre : finBasisEquivEuclidean.symm ⁻¹' (finBasisEquivEuclidean.symm '' Ωs) = Ωs :=
    preimage_image_eq Ωs (finBasisEquivEuclidean (E := E)).symm.injective
  rw [setLIntegral_riemannianVolume_inter_preimage p hLΩ_open (image_subset_iff.2 hΩt),
    ← hmp.setLIntegral_comp_preimage_emb hemb _ (finBasisEquivEuclidean.symm '' Ωs), hpre]

/-- Pulling an `L²(M)` function back to a precompact chart ball and weighting by the chart
volume density produces a function in `L²(Ω)`. -/
private theorem memLp_chartVolumeDensity_mul_comp (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩc : IsCompact (closure (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))))
    (hΩct : MapsTo finBasisEquivEuclidean.symm
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) (extChartAt I p).target)
    {F : M → ℝ} (hF : MemLp F 2 (riemannianVolume I M))
    {G : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ}
    (hGm : AEStronglyMeasurable G (volume.restrict (Ω : Set _)))
    (hGae : G =ᵐ[volume.restrict (Ω : Set _)] fun y ↦
      chartVolumeDensity (I := I) p ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)) *
        F ((extChartAt I p).symm (finBasisEquivEuclidean.symm y))) :
    MemLp G 2 (volume.restrict (Ω : Set _)) := by
  let Ωs : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))) := Ω
  let ψ : EuclideanSpace ℝ (Fin (finrank ℝ E)) → M :=
    fun y ↦ (extChartAt I p).symm (finBasisEquivEuclidean.symm y)
  have hΩt : MapsTo finBasisEquivEuclidean.symm Ωs (extChartAt I p).target :=
    hΩct.mono_left subset_closure
  obtain ⟨M₀, hM₀⟩ :=
    hΩc.exists_bound_of_continuousOn (continuousOn_chartVolumeDensity_coord p hΩct)
  -- Bound `∫_Ω (ρ F)² ≤ max M₀ 0 * ∫_Ω ρ F² ≤ max M₀ 0 * ∫_M F² < ∞`.
  rw [MemLp, eLpNorm_congr_ae hGae,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) ENNReal.ofNat_ne_top (hGm.congr hGae)]
  simp only [ENNReal.toReal_ofNat]
  have hpt : ∫⁻ y in Ωs, ‖chartVolumeDensity (I := I) p (ψ y) * F (ψ y)‖ₑ ^ (2 : ℝ) ∂volume ≤
      ∫⁻ y in Ωs, ENNReal.ofReal (max M₀ 0) *
        (ENNReal.ofReal (chartVolumeDensity (I := I) p (ψ y)) * ‖F (ψ y)‖ₑ ^ (2 : ℝ)) ∂volume := by
    refine setLIntegral_mono' Ω.isOpen.measurableSet fun y hy ↦ ?_
    have hρnn := chartVolumeDensity_nonneg (I := I) p (ψ y)
    have hρle : chartVolumeDensity (I := I) p (ψ y) ≤ max M₀ 0 := by
      have h := hM₀ y (subset_closure hy)
      rw [Real.norm_of_nonneg hρnn] at h
      exact h.trans (le_max_left _ _)
    rw [eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), Real.eNorm_eq_ofReal hρnn,
      ENNReal.rpow_two, sq, mul_assoc]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hρle) bot_le
  have hbound : ∫⁻ y in Ωs, ‖chartVolumeDensity (I := I) p (ψ y) * F (ψ y)‖ₑ ^ (2 : ℝ) ∂volume ≤
      ENNReal.ofReal (max M₀ 0) * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M := by
    refine hpt.trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← setLIntegral_riemannianVolume_eq_coord p hΩt (fun x ↦ ‖F x‖ₑ ^ (2 : ℝ))]
    exact mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) bot_le
  have hFfin : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M < ⊤ := by
    have h := hF.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) ENNReal.ofNat_ne_top
      hF.aestronglyMeasurable] at h
    simp only [ENNReal.toReal_ofNat] at h
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 h
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin)).ne

end VolumeCoord

section LocalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [T2Space M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [T2Space M] in
/-- On a precompact chart ball, the Dirichlet form of `w ∈ H¹(M)` against a transplanted test
function `φ` equals the Euclidean divergence-form energy form with coefficient matrix `ρ G⁻¹`. -/
private theorem energyFormH1_eq_dirichletForm_of_transplant (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩc : IsCompact (closure (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))))
    (hΩct : MapsTo finBasisEquivEuclidean.symm
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) (extChartAt I p).target)
    {T : SobolevH1 I M → W1p volume Ω 2} (hTc : Continuous T)
    (hTg : ∀ u : C^∞⟮I, M; ℝ⟯,
      W1p.gradient (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set _)]
        ∇ fun y ↦ u ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)))
    {η : 𝓓(Ω, ℝ)} {φ : C^∞⟮I, M; ℝ⟯}
    (hφsupp : tsupport (φ : M → ℝ) ⊆
      (extChartAt I p).source ∩
        extChartAt I p ⁻¹'
          (finBasisEquivEuclidean.symm '' (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))))
    (hφeq : ∀ y ∈ Ω, φ ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)) = η y)
    (w : SobolevH1 I M) :
    PDE.energyFormH1
        (fun y ↦ chartVolumeDensity (I := I) p
            ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)) •
          chartInvGramMatrix (I := I) p ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)))
        0 0 (T w) (W1p.ofTestFunctionₗ volume Ω 2 η) =
      dirichletForm w (ofSmooth φ) := by
  set a : EuclideanSpace ℝ (Fin (finrank ℝ E)) →
      Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ :=
    fun y ↦ chartVolumeDensity (I := I) p
        ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)) •
      chartInvGramMatrix (I := I) p ((extChartAt I p).symm (finBasisEquivEuclidean.symm y))
  have hΩt : MapsTo finBasisEquivEuclidean.symm Ω (extChartAt I p).target :=
    hΩct.mono_left subset_closure
  have hcoeff := PDE.memLp_energyIntegrand_of_continuousOn (mu := volume) (b := 0) (c := 0) hΩc
    (continuousOn_coordCoeff p hΩct) continuousOn_const continuousOn_const
  -- Extend the identity from smooth functions to all of `H¹(M)` by continuity.
  have hlhs_cont : Continuous fun w : SobolevH1 I M ↦
      PDE.energyFormH1 a 0 0 (T w) (W1p.ofTestFunctionₗ volume Ω 2 η) := by
    have heq : (fun w : SobolevH1 I M ↦
          PDE.energyFormH1 a 0 0 (T w) (W1p.ofTestFunctionₗ volume Ω 2 η)) =
        fun w ↦ PDE.energyFormH1L hcoeff (T w) (W1p.ofTestFunctionₗ volume Ω 2 η) :=
      funext fun w ↦ (PDE.energyFormH1L_apply hcoeff _ _).symm
    rw [heq]
    exact ((ContinuousLinearMap.apply ℝ ℝ (W1p.ofTestFunctionₗ volume Ω 2 η)).continuous.comp
      (PDE.energyFormH1L hcoeff).continuous).comp hTc
  have hrhs_cont : Continuous fun w : SobolevH1 I M ↦ dirichletForm w (ofSmooth φ) :=
    (ContinuousLinearMap.apply ℝ ℝ (ofSmooth φ)).continuous.comp dirichletForm.continuous
  refine induction_on w (isClosed_eq hlhs_cont hrhs_cont) fun u ↦ ?_
  rw [PDE.energyFormH1_zero_zero_eq_setIntegral, dirichletForm_ofSmooth]
  have hsupp_inner : Function.support (fun x ↦ ⟪mgradient I u x, mgradient I φ x⟫_ℝ) ⊆
      (extChartAt I p).source ∩
        extChartAt I p ⁻¹'
          (finBasisEquivEuclidean.symm '' (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) :=
    fun x hx ↦ hφsupp <| by_contra fun hnot ↦ hx <| by
      have h0 : mgradient I φ x = 0 := mgradient_eq_zero_iff.2 <|
        (notMem_tsupport_iff_eventuallyEq.1 hnot).mvfderiv_eq.trans mvfderiv_zero
      simp [h0]
  rw [integral_riemannianVolume_eq_setIntegral_coord p hΩt hsupp_inner]
  refine integral_congr_ae ?_
  filter_upwards [hTg u, gradientTestFunctionLp_apply_ae (mu := volume) 2 η,
    ae_restrict_mem Ω.isOpen.measurableSet] with y hu_g hη_g hy
  have hgrad_φ : ∇ (fun z ↦ φ ((extChartAt I p).symm (finBasisEquivEuclidean.symm z))) y =
      ∇ (η : _ → ℝ) y := by
    have hev : (fun z ↦ φ ((extChartAt I p).symm (finBasisEquivEuclidean.symm z))) =ᶠ[𝓝 y]
        (η : _ → ℝ) :=
      Filter.eventually_of_mem (Ω.isOpen.mem_nhds hy) fun z hz ↦ hφeq z hz
    simp only [gradient, hev.fderiv_eq]
  rw [W1p.gradient_ofTestFunctionₗ, hη_g, hu_g, ← hgrad_φ,
    inner_mgradient_eq_matrixBilinearForm p (hΩt hy) (u.contMDiff.of_le (by simp))
      (φ.contMDiff.of_le (by simp)),
    PDE.matrixBilinearForm_smul_apply]

omit [T2Space M] in
/-- Shrink the chart operator `exists_continuousLinearMap_w1p_extChartAt` to a precompact coordinate
ball `Ω` around `L (extChartAt I p p)`. -/
private theorem exists_precompact_chart_w1p {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
    [(volume : Measure F).IsAddHaarMeasure] (p : M) (L : E ≃L[ℝ] F) :
    ∃ Ω : Opens F,
      L (extChartAt I p p) ∈ Ω ∧ IsCompact (closure (Ω : Set F)) ∧
        MapsTo L.symm (closure (Ω : Set F)) (extChartAt I p).target ∧
        ∃ T : SobolevH1 I M → W1p volume Ω 2, Continuous T ∧
          (∀ u : C^∞⟮I, M; ℝ⟯,
            W1p.gradient (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set F)]
              ∇ fun y ↦ u ((extChartAt I p).symm (L.symm y))) ∧
          ∀ w : SobolevH1 I M, W1p.value (T w) =ᵐ[volume.restrict (Ω : Set F)]
            fun y ↦ toLp w ((extChartAt I p).symm (L.symm y)) := by
  obtain ⟨Ω₀, hpΩ₀, hΩ₀t, T₀, hT₀s, hT₀v⟩ :=
    exists_continuousLinearMap_w1p_extChartAt (I := I) (M := M) p L
  obtain ⟨r, hr, hrΩ₀⟩ := nhds_basis_closedBall.mem_iff.1 (Ω₀.isOpen.mem_nhds hpΩ₀)
  set Ω : Opens F := ⟨ball (L (extChartAt I p p)) r, isOpen_ball⟩
  have hΩcl : closure (Ω : Set F) ⊆ closedBall (L (extChartAt I p p)) r :=
    closure_ball_subset_closedBall
  have hΩ_le : Ω ≤ Ω₀ := ball_subset_closedBall.trans hrΩ₀
  refine ⟨Ω, mem_ball_self hr, (isCompact_closedBall _ r).of_isClosed_subset isClosed_closure hΩcl,
    hΩ₀t.mono_left (hΩcl.trans hrΩ₀), fun w ↦ W1p.restrictL hΩ_le (T₀ w),
    (W1p.restrictL hΩ_le).continuous.comp T₀.continuous, fun u ↦ ?_, fun w ↦ ?_⟩
  · exact (W1p.gradient_restrictL_ae hΩ_le (T₀ (ofSmooth u))).trans
      (ae_restrict_of_ae_restrict_of_subset hΩ_le (hT₀s u).2)
  · exact (W1p.value_restrictL_ae hΩ_le (T₀ w)).trans
      (ae_restrict_of_ae_restrict_of_subset hΩ_le (hT₀v w))

omit [I.Boundaryless] [T2Space M] in
/-- Transfer almost-everywhere agreement on a coordinate open set `Ω` to almost-everywhere
agreement against `riemannianVolume` on the chart preimage of `Ω`. -/
private theorem ae_eq_comp_extChartAt_of_ae_eq_coord (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo finBasisEquivEuclidean.symm Ω (extChartAt I p).target)
    {w : SobolevH1 I M} {w_loc : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ}
    (hw_cont : ContinuousOn w_loc Ω)
    (hae_coord : (fun y ↦ toLp w ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)))
      =ᵐ[volume.restrict (Ω : Set _)] w_loc)
    (hmeas_coord : AEStronglyMeasurable
      (fun y ↦ toLp w ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)))
      (volume.restrict (Ω : Set _))) :
    (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict
        ((extChartAt I p).source ∩
          extChartAt I p ⁻¹'
            (finBasisEquivEuclidean.symm '' (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))))]
      fun x ↦ w_loc (finBasisEquivEuclidean (extChartAt I p x)) := by
  set Ωs : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))) :=
    (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))
  set U : Set M :=
    (extChartAt I p).source ∩ extChartAt I p ⁻¹' (finBasisEquivEuclidean.symm '' Ωs)
  set u : M → ℝ := fun x ↦ w_loc (finBasisEquivEuclidean (extChartAt I p x))
  have hU_open : IsOpen U := isOpen_extChartAt_preimage' p
    ((finBasisEquivEuclidean (E := E)).symm.toHomeomorph.isOpenMap _ Ω.isOpen)
  have hu_cont : ContinuousOn u U :=
    hw_cont.comp ((finBasisEquivEuclidean (E := E)).continuous.comp_continuousOn
      ((continuousOn_extChartAt p).mono inter_subset_left)) fun x hx ↦ by
        obtain ⟨y, hy, hyx⟩ := hx.2
        rwa [← hyx, (finBasisEquivEuclidean (E := E)).apply_symm_apply]
  have hzero : ∫⁻ x in U, ‖toLp w x - u x‖ₑ ∂riemannianVolume I M = 0 := by
    rw [setLIntegral_riemannianVolume_eq_coord p hΩt (fun x ↦ ‖toLp w x - u x‖ₑ)]
    refine (lintegral_eq_zero_iff' ?_).2 ?_
    · refine ((continuousOn_chartVolumeDensity_coord p hΩt).aemeasurable
        Ω.isOpen.measurableSet).ennreal_ofReal.mul ((hmeas_coord.sub ?_).eNorm)
      refine (hw_cont.aestronglyMeasurable Ω.isOpen.measurableSet).congr ?_
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
      simp only [u, (extChartAt I p).right_inv (hΩt hy),
        (finBasisEquivEuclidean (E := E)).apply_symm_apply]
    · filter_upwards [hae_coord, ae_restrict_mem Ω.isOpen.measurableSet] with y hyw hy
      simp only [Pi.zero_apply, u, (extChartAt I p).right_inv (hΩt hy),
        (finBasisEquivEuclidean (E := E)).apply_symm_apply, hyw, sub_self, eNorm_zero, mul_zero]
  have hmeas_diff : AEMeasurable (fun x ↦ ‖toLp w x - u x‖ₑ)
      ((riemannianVolume I M).restrict U) :=
    (((Lp.aestronglyMeasurable (toLp w)).restrict).sub
      (hu_cont.aestronglyMeasurable hU_open.measurableSet)).eNorm
  filter_upwards [(lintegral_eq_zero_iff' hmeas_diff).1 hzero] with x hx
  exact sub_eq_zero.1 (eNorm_eq_zero.1 hx)

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Smooth coordinate representative on a precompact chart ball `Ω` via Euclidean semilinear
elliptic regularity. -/
private theorem exists_coord_contDiffOn_ae_eq (hdim : Module.finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M}
    (hf : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) =
      ∫ x, (A x * Φ (toLp w x) + C x) * φ x ∂riemannianVolume I M)
    (p : M) {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩc : IsCompact (closure (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))))
    (hΩct : MapsTo finBasisEquivEuclidean.symm
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) (extChartAt I p).target)
    {T : SobolevH1 I M → W1p volume Ω 2} (hTc : Continuous T)
    (hTg : ∀ u : C^∞⟮I, M; ℝ⟯,
      W1p.gradient (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set _)]
        ∇ fun y ↦ u ((extChartAt I p).symm (finBasisEquivEuclidean.symm y)))
    (hTv : W1p.value (T w) =ᵐ[volume.restrict (Ω : Set _)]
      fun y ↦ toLp w ((extChartAt I p).symm (finBasisEquivEuclidean.symm y))) :
    ∃ w_loc : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, ContDiffOn ℝ ∞ w_loc Ω ∧
      (W1p.value (T w) : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ) =ᵐ[volume.restrict (Ω : Set _)]
        w_loc := by
  have hΩt : MapsTo finBasisEquivEuclidean.symm Ω (extChartAt I p).target :=
    hΩct.mono_left subset_closure
  let ψ : EuclideanSpace ℝ (Fin (finrank ℝ E)) → M :=
    fun y ↦ (extChartAt I p).symm (finBasisEquivEuclidean.symm y)
  let a := fun y ↦ chartVolumeDensity (I := I) p (ψ y) • chartInvGramMatrix (I := I) p (ψ y)
  let Ac := fun y ↦ chartVolumeDensity (I := I) p (ψ y) * A (ψ y)
  let Cc := fun y ↦ chartVolumeDensity (I := I) p (ψ y) * C (ψ y)
  obtain ⟨hρ_smooth, ha_smooth, lam, Lam, ha_ell⟩ :=
    exists_uniformlyEllipticOn_coordCoeff p hΩc hΩct
  have hψ_smooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) I ∞ ψ Ω :=
    (contMDiffOn_extChartAt_symm p).comp
      (finBasisEquivEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn hΩt
  have hAc_smooth : ContDiffOn ℝ ∞ Ac Ω := hρ_smooth.mul (hA.comp_contMDiffOn hψ_smooth).contDiffOn
  have hCc_smooth : ContDiffOn ℝ ∞ Cc Ω := hρ_smooth.mul (hC.comp_contMDiffOn hψ_smooth).contDiffOn
  have hf_loc : MemLp (fun y ↦ Ac y * Φ (W1p.value (T w) y) + Cc y) 2
      (volume.restrict (Ω : Set _)) := by
    have hmeas : AEStronglyMeasurable (fun y ↦ Ac y * Φ (W1p.value (T w) y) + Cc y)
        (volume.restrict (Ω : Set _)) :=
      ((hAc_smooth.continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet).mul
        (hΦ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))).add
        (hCc_smooth.continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet)
    refine memLp_chartVolumeDensity_mul_comp p hΩc hΩct hf hmeas ?_
    filter_upwards [hTv] with y hy
    simp only [Ac, Cc, ψ, hy]; ring
  have hweak (η : 𝓓(Ω, ℝ)) : PDE.energyFormH1 a 0 0 (T w) (W1p.ofTestFunctionₗ volume Ω 2 η) =
      ∫ y in Ω, (Ac y * Φ (W1p.value (T w) y) + Cc y) * η y := by
    obtain ⟨φ, hφsupp, hφeq⟩ := exists_transplant_testFunction p hΩt η
    refine (energyFormH1_eq_dirichletForm_of_transplant p hΩc hΩct hTc hTg hφsupp hφeq w).trans ?_
    refine (hw φ).trans ?_
    refine (integral_riemannianVolume_eq_setIntegral_coord p hΩt fun x hx ↦
      hφsupp (subset_tsupport _ fun h0 ↦ hx (by simp [h0]))).trans ?_
    refine integral_congr_ae ?_
    filter_upwards [hTv, ae_restrict_mem Ω.isOpen.measurableSet] with y hyw hy
    dsimp only [Ac, Cc, ψ]
    rw [hyw, hφeq y hy]
    ring
  exact ha_ell.exists_contDiffOn_ae_eq_of_forall_energyFormH1_ofTestFunctionₗ_eq
    (by simpa using hdim) ha_smooth hAc_smooth hCc_smooth hΦ
    (fun K _ hKΩ ↦ hf_loc.mono_measure (Measure.restrict_mono hKΩ le_rfl)) hweak

/-- **Local smooth representative** of a semilinear weak solution on `H¹(M)` near a point `p`. -/
private theorem exists_local_contMDiffOn_ae_eq (hdim : Module.finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M}
    (hf : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) =
      ∫ x, (A x * Φ (toLp w x) + C x) * φ x ∂riemannianVolume I M) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ u : M → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ u U ∧
      (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict U] u := by
  obtain ⟨Ω, hpΩ, hΩc, hΩct, T, hTc, hTg, hTv⟩ :=
    exists_precompact_chart_w1p (I := I) (M := M) p finBasisEquivEuclidean
  have hΩt : MapsTo finBasisEquivEuclidean.symm Ω (extChartAt I p).target :=
    hΩct.mono_left subset_closure
  obtain ⟨w_loc, hw_loc_smooth, hw_loc_ae⟩ :=
    exists_coord_contDiffOn_ae_eq hdim hA hC hΦ hf hw p hΩc hΩct hTc hTg (hTv w)
  let Ωs : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))) :=
    (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))
  let U : Set M :=
    (extChartAt I p).source ∩ extChartAt I p ⁻¹' (finBasisEquivEuclidean.symm '' Ωs)
  refine ⟨U, isOpen_extChartAt_preimage' p
      ((finBasisEquivEuclidean (E := E)).symm.toHomeomorph.isOpenMap _ Ω.isOpen),
    ⟨mem_extChartAt_source p, ⟨_, hpΩ, (finBasisEquivEuclidean (E := E)).symm_apply_apply _⟩⟩,
    fun x ↦ w_loc (finBasisEquivEuclidean (extChartAt I p x)), ?_, ?_⟩
  · exact hw_loc_smooth.contMDiffOn.comp
      ((finBasisEquivEuclidean (E := E)).contDiff.contMDiff.comp_contMDiffOn
        ((contMDiffOn_extChartAt (I := I)).mono
          (inter_subset_left.trans (extChartAt_source (I := I) p).subset)))
      fun x hx ↦ by
        obtain ⟨y, hy, hyx⟩ := hx.2
        change finBasisEquivEuclidean (extChartAt I p x) ∈ Ωs
        rwa [← hyx, (finBasisEquivEuclidean (E := E)).apply_symm_apply]
  · exact ae_eq_comp_extChartAt_of_ae_eq_coord p hΩt hw_loc_smooth.continuousOn
      ((hTv w).symm.trans hw_loc_ae) ((Lp.aestronglyMeasurable (W1p.value (T w))).congr (hTv w))

end LocalRegularity

/-! ### Global smoothness and classical equation -/

section GlobalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [T2Space M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A smooth representative of a weak solution solves the classical equation `-Δu = A Φ(u) + C`
everywhere on `M`. -/
private theorem neg_laplaceBeltrami_eq_of_ofSmooth_eq
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M} {u : C^∞⟮I, M; ℝ⟯}
    (hw_eq : w = ofSmooth u)
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) =
      ∫ x, (A x * Φ (toLp w x) + C x) * φ x ∂riemannianVolume I M) (x : M) :
    -laplaceBeltrami I u x = A x * Φ (u x) + C x := by
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hu_cont : Continuous (u : M → ℝ) := u.contMDiff.continuous
  have hΔ_cont : Continuous fun y ↦ -laplaceBeltrami I u y :=
    (continuous_laplaceBeltrami (u.contMDiff.of_le (by simp))).neg
  have hrhs_cont : Continuous fun y ↦ A y * Φ (u y) + C y :=
    (hA.continuous.mul (hΦ.continuous.comp hu_cont)).add hC.continuous
  set g : M → ℝ := fun y ↦ -laplaceBeltrami I u y - (A y * Φ (u y) + C y)
  have hg_cont : Continuous g := hΔ_cont.sub hrhs_cont
  have hae : (toLp w : M → ℝ) =ᵐ[riemannianVolume I M] u := by
    rw [hw_eq]
    exact toLp_ofSmooth_ae_eq u
  have hg_ae : g =ᵐ[riemannianVolume I M] 0 := by
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hg_cont.locallyIntegrable
      fun φ hφ _ ↦ ?_
    set φm : C^∞⟮I, M; ℝ⟯ := ⟨φ, hφ⟩
    have h1 : ∫ y, φ y * -laplaceBeltrami I u y ∂riemannianVolume I M =
        dirichletForm w (ofSmooth φm) := by
      rw [hw_eq, dirichletForm_comm, dirichletForm_ofSmooth_right]
      exact integral_congr_ae ((toLp_ofSmooth_ae_eq φm).mono fun y hy ↦ by
        dsimp only; rw [hy]; rfl)
    have h2 : ∫ y, φ y * (A y * Φ (u y) + C y) ∂riemannianVolume I M =
        dirichletForm w (ofSmooth φm) := by
      rw [hw φm]
      exact integral_congr_ae (hae.mono fun y hy ↦ by dsimp only; rw [hy, mul_comm]; rfl)
    have hI1 : Integrable (fun y ↦ φ y * -laplaceBeltrami I u y) (riemannianVolume I M) :=
      (hφ.continuous.mul hΔ_cont).integrable_of_hasCompactSupport (.of_compactSpace _)
    have hI2 : Integrable (fun y ↦ φ y * (A y * Φ (u y) + C y)) (riemannianVolume I M) :=
      (hφ.continuous.mul hrhs_cont).integrable_of_hasCompactSupport (.of_compactSpace _)
    calc ∫ y, φ y • g y ∂riemannianVolume I M
        = ∫ y, (φ y * -laplaceBeltrami I u y - φ y * (A y * Φ (u y) + C y))
            ∂riemannianVolume I M := by simp only [g, smul_eq_mul, mul_sub]
      _ = ∫ y, φ y * -laplaceBeltrami I u y ∂riemannianVolume I M -
            ∫ y, φ y * (A y * Φ (u y) + C y) ∂riemannianVolume I M := integral_sub hI1 hI2
      _ = 0 := by rw [h1, h2, sub_self]
  exact sub_eq_zero.1 (congrFun ((hg_cont.ae_eq_iff_eq _ continuous_zero).1 hg_ae) x)

/-- **Smoothness of weak solutions of semilinear equations on a closed manifold.** On a closed
smooth Riemannian manifold of dimension at most three, let `A`, `C` and `Φ` be smooth. If
`w ∈ H¹(M)` solves `Δ⁺w = A(x) Φ(w) + C(x)` against smooth test functions and its nonlinear
forcing `A Φ(w) + C` lies in `L²(M)`, then `w` is represented by a smooth function `u` that solves
`-Δu = A(x) Φ(u) + C(x)` everywhere on `M`. -/
theorem exists_contMDiff_of_forall_dirichletForm_ofSmooth_eq (hdim : Module.finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M}
    (hf : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) =
      ∫ x, (A x * Φ (toLp w x) + C x) * φ x ∂riemannianVolume I M) :
    ∃ u : C^∞⟮I, M; ℝ⟯, w = ofSmooth u ∧
      ∀ x, -laplaceBeltrami I u x = A x * Φ (u x) + C x := by
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  -- Obtain a local smooth representative around every point and glue them on overlaps.
  choose U hU_open hpU uloc huloc_smooth huloc_ae using
    exists_local_contMDiffOn_ae_eq hdim hA hC hΦ hf hw
  set ufun : M → ℝ := fun x ↦ uloc x x
  have hglue (p : M) : EqOn ufun (uloc p) (U p) := fun q hq ↦ by
    have hW_open : IsOpen (U q ∩ U p) := (hU_open q).inter (hU_open p)
    have hq_ae : (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict (U q ∩ U p)] uloc q :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (huloc_ae q)
    have hp_ae : (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict (U q ∩ U p)] uloc p :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (huloc_ae p)
    exact Measure.eqOn_open_of_ae_eq (hq_ae.symm.trans hp_ae) hW_open
      ((huloc_smooth q).continuousOn.mono inter_subset_left)
      ((huloc_smooth p).continuousOn.mono inter_subset_right) ⟨hpU q, hq⟩
  have hu_smooth : ContMDiff I 𝓘(ℝ) ∞ ufun := fun p ↦
    ((huloc_smooth p).contMDiffAt ((hU_open p).mem_nhds (hpU p))).congr_of_eventuallyEq
      (Filter.eventually_of_mem ((hU_open p).mem_nhds (hpU p)) fun q hq ↦ hglue p hq)
  set u : C^∞⟮I, M; ℝ⟯ := ⟨ufun, hu_smooth⟩
  -- A finite subcover promotes the local a.e. equalities to `toLp w =ᵐ u`, giving `w = ofSmooth u`.
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU_open fun x _ ↦
    mem_iUnion.2 ⟨x, hpU x⟩
  have hae_global : (toLp w : M → ℝ) =ᵐ[riemannianVolume I M] u := by
    rw [Filter.EventuallyEq, ae_iff]
    have hsub : {x | ¬toLp w x = u x} ⊆ ⋃ p ∈ s, ({x | ¬toLp w x = u x} ∩ U p) := fun x hx ↦ by
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hs (mem_univ x))
      exact mem_iUnion₂.2 ⟨p, hp, hx, hxp⟩
    refine le_antisymm ((measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)) bot_le
    refine le_of_eq (Finset.sum_eq_zero fun p _ ↦ ?_)
    rw [← Measure.restrict_apply' (hU_open p).measurableSet]
    exact ae_iff.1 <| (huloc_ae p).trans <|
      Filter.eventually_of_mem (ae_restrict_mem (hU_open p).measurableSet)
        fun x hx ↦ (hglue p hx).symm
  have hw_eq : w = ofSmooth u :=
    toLp_injective (Lp.ext (hae_global.trans (toLp_ofSmooth_ae_eq u).symm))
  exact ⟨u, hw_eq, neg_laplaceBeltrami_eq_of_ofSmooth_eq hA hC hΦ hw_eq hw⟩

/-- **Smoothness of `H¹` weak solutions of semilinear equations.** Convenience form of
`TauCeti.Manifold.SobolevH1.exists_contMDiff_of_forall_dirichletForm_ofSmooth_eq` when the weak
equation holds against every `v ∈ H¹(M)`. -/
theorem exists_contMDiff_of_forall_dirichletForm_eq (hdim : Module.finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M}
    (hf : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ v : SobolevH1 I M, dirichletForm w v =
      ∫ x, (A x * Φ (toLp w x) + C x) * toLp v x ∂riemannianVolume I M) :
    ∃ u : C^∞⟮I, M; ℝ⟯, w = ofSmooth u ∧
      ∀ x, -laplaceBeltrami I u x = A x * Φ (u x) + C x :=
  exists_contMDiff_of_forall_dirichletForm_ofSmooth_eq hdim hA hC hΦ hf fun φ ↦
    (hw (ofSmooth φ)).trans <| integral_congr_ae <|
      (toLp_ofSmooth_ae_eq φ).mono fun x hx ↦ congrArg ((A x * Φ (toLp w x) + C x) * ·) hx

end GlobalRegularity

end TauCeti.Manifold.SobolevH1
