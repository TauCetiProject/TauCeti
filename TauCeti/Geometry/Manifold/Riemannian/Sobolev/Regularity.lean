/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.PDE.Ellipticity.PosDef
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.PDE.Regularity.Semilinear
import TauCeti.Analysis.PDE.Regularity.Smooth
import TauCeti.Geometry.Manifold.ContMDiff.LocalRepresentative
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.ChartCutoff
import TauCeti.Geometry.Manifold.Riemannian.Poisson
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Chart
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Integral.ContinuousMap
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Interior elliptic regularity on the Sobolev space `H¹(M)`

Let `M` be a closed manifold equipped with a Riemannian metric, its Riemannian volume `dV`, and the
Sobolev space `H¹(M)` (`TauCeti.Manifold.SobolevH1`). Reading an element `w ∈ H¹(M)` in an extended
chart around `p ∈ M` produces a Euclidean Sobolev function `T w ∈ W^{1,2}(Ω)`
(`TauCeti.Manifold.SobolevH1.exists_continuousLinearMap_w1p_extChartAt`), and in coordinates the
Dirichlet form `D(w, ·)` becomes the divergence-form energy form with principal coefficient
`a(y) = √(det g(ψ(y))) g⁻¹(ψ(y))`, where `g` is the chart Gram matrix and `ψ` is the inverse chart.
On a closed coordinate ball inside the chart target, `a` is continuous and pointwise positive
definite, hence uniformly elliptic (`TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact`). This
transfers Euclidean interior regularity to `H¹(M)`:

* **De Giorgi continuity**
  (`TauCeti.Manifold.SobolevH1.exists_continuous_ae_eq_of_dirichletForm_eq`):
  for a continuous Riemannian metric and a forcing `f ∈ Lʳ(M)` with `r ≥ 2` and `r > dim M / 2`,
  every weak solution `w ∈ H¹(M)` of `Δ⁺w = f` agrees almost everywhere with a continuous function
  on `M`.
* **Semilinear `C^∞` bootstrap**
  (`TauCeti.Manifold.SobolevH1.contMDiff_of_dirichletForm_eq_semilinear`): in dimension at most
  three, if the metric, `A`, `C` on `M`, and `Φ : ℝ → ℝ` are smooth, then any continuous function
  `u` representing a weak solution `w ∈ H¹(M)` of `Δ⁺w = A Φ(u) + C` is smooth on `M` and solves
  `Δ⁺u = A Φ(u) + C` classically everywhere.
* **Linear `C^∞` regularity in every dimension**
  (`SobolevH1.exists_eq_ofSmooth_and_neg_laplaceBeltrami_add_mul_eq_of_dirichletForm_add_eq`):
  if the metric, a potential `V` and a forcing `f` are smooth, every weak solution `w ∈ H¹(M)` of
  `Δ⁺w + V w = f` is a smooth function solving the equation classically. In coordinates the
  potential becomes the mass term of a divergence-form operator with smooth coefficients, to which
  Euclidean interior smoothness
  (`TauCeti.PDE.UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_contDiffOn`) applies. In particular
  weak eigenfunctions of `Δ⁺` are smooth
  (`SobolevH1.exists_eq_ofSmooth_and_neg_laplaceBeltrami_eq_mul_of_dirichletForm_eq_mul`). With
  the weak Poisson theory of `TauCeti.Geometry.Manifold.Riemannian.Poisson` this solves `Δ⁺u = f`
  with `u` smooth for every smooth `f` of integral zero
  (`TauCeti.Manifold.SobolevH1.exists_neg_laplaceBeltrami_eq`). For a smooth `1`-form `a` on a
  closed four-manifold, this is the scalar equation `Δ⁺ξ = d*a / 2` of the global Coulomb gauge
  `d*(a - 2 dξ) = 0`.

Local continuous or smooth representatives constructed in charts are glued to a global one by
`TauCeti.exists_contMDiff_ae_eq_of_locally`, since the Riemannian volume charges every nonempty
open set (`TauCeti.isOpenPosMeasure_riemannianVolume`). A smooth representative solves the equation
classically: by Green's identity, `Δ⁺u - f` is continuous and orthogonal to every smooth function,
hence zero (`ae_eq_zero_of_integral_contMDiff_smul_eq_zero`).

## Main results

* `TauCeti.Manifold.SobolevH1.exists_continuous_ae_eq_of_dirichletForm_eq`: De Giorgi continuity of
  weak solutions of `Δ⁺w = f` for `f ∈ Lʳ(M)`, `r ≥ 2`, `r > dim M / 2`.
* `TauCeti.Manifold.SobolevH1.eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq`: a weak
  solution agreeing almost everywhere with a smooth function `u` is `ofSmooth u`, and `u` solves
  `Δ⁺u = f` everywhere.
* `TauCeti.Manifold.SobolevH1.contMDiff_of_dirichletForm_eq_semilinear`: smoothness and classical
  equation `Δ⁺u = A Φ(u) + C` for continuous weak solutions in dimension at most three.
* `SobolevH1.exists_eq_ofSmooth_and_neg_laplaceBeltrami_add_mul_eq_of_dirichletForm_add_eq`:
  a weak solution of `Δ⁺w + V w = f` with smooth `V` and `f` is a smooth classical solution, in
  every dimension.
* `SobolevH1.exists_eq_ofSmooth_and_neg_laplaceBeltrami_eq_mul_of_dirichletForm_eq_mul`:
  a weak solution of `Δ⁺w = μ w` is a smooth classical eigenfunction.
* `TauCeti.Manifold.SobolevH1.exists_neg_laplaceBeltrami_eq`: a smooth `f` of integral zero is
  `Δ⁺u` for a smooth `u` of integral zero.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), §3.7.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., American Mathematical Society (2010),
  §6.3.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), Chapter 8.

## Attribution

Adapted from the chart bridge, De Giorgi continuity and semilinear bootstrap of
[TauCetiProject/TauCeti#40536](https://github.com/TauCetiProject/TauCeti/pull/40536).
-/

public section

open Bundle Filter MeasureTheory Metric Module Riemannian.Tensor Set TauCeti.MeasureTheory
  TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Manifold Matrix NNReal
  Topology

noncomputable section

namespace TauCeti.Manifold

namespace SobolevH1

section CoordEquiv

/-- The linear equivalence from `E` to `EuclideanSpace ℝ (Fin (finrank ℝ E))` sending the canonical
basis `Module.finBasis ℝ E` to the standard orthonormal basis `EuclideanSpace.basisFun`. -/
private def coordEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
  ((Module.finBasis ℝ E).equiv
    (EuclideanSpace.basisFun (Fin (finrank ℝ E)) ℝ).toBasis (Equiv.refl _)).toContinuousLinearEquiv

private theorem coordEquiv_symm_single (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (k : Fin (finrank ℝ E)) :
    (coordEquiv E).symm (EuclideanSpace.single k 1) = Module.finBasis ℝ E k := by
  apply (coordEquiv E).injective
  rw [(coordEquiv E).apply_symm_apply]
  simp [coordEquiv, EuclideanSpace.basisFun_apply]

section MeasureCoord

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

private theorem measurePreserving_coordEquiv_symm (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    MeasurePreserving (coordEquiv E).symm volume (Module.finBasis ℝ E).addHaar := by
  rw [← (EuclideanSpace.basisFun (Fin (finrank ℝ E)) ℝ).addHaar_eq_volume]
  -- `(coordEquiv E).symm` is the linear equivalence matching the two bases.
  exact Module.Basis.measurePreserving_equiv _ (Module.finBasis ℝ E) (Equiv.refl _)

end MeasureCoord

attribute [irreducible] coordEquiv

end CoordEquiv

section CoordinatePDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inverse chart map `(extChartAt I p).symm ∘ (coordEquiv E).symm`. -/
private def chartInvMap (p : M) (y : EuclideanSpace ℝ (Fin (finrank ℝ E))) : M :=
  (extChartAt I p).symm ((coordEquiv E).symm y)

/-- The open neighbourhood on `M` corresponding to an open coordinate set `Ω`. -/
private def chartNbhd (p : M) (Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))) : Set M :=
  (extChartAt I p).source ∩ extChartAt I p ⁻¹' ((coordEquiv E).symm '' (Ω : Set _))

private theorem isOpen_chartNbhd (p : M) (Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))) :
    IsOpen (chartNbhd (I := I) p Ω) :=
  isOpen_extChartAt_preimage' p ((coordEquiv E).symm.toHomeomorph.isOpenMap _ Ω.isOpen)

private theorem mem_chartNbhd_self (p : M) {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hpΩ : coordEquiv E (extChartAt I p p) ∈ Ω) :
    p ∈ chartNbhd (I := I) p Ω :=
  ⟨mem_extChartAt_source p, coordEquiv E (extChartAt I p p), hpΩ, by simp⟩

/-- The inverse chart `chartInvMap p` maps coordinates in the chart target into the base set of
the tangent trivialization at `p`. -/
private theorem mapsTo_chartInvMap_baseSet [IsManifold I ∞ M] (p : M)
    {s : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hs : MapsTo (coordEquiv E).symm s (extChartAt I p).target) :
    MapsTo (chartInvMap (I := I) p) s (trivializationAt E (TangentSpace I) p).baseSet :=
  fun y hy ↦ by
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target (hs hy)

private theorem contMDiffOn_chartInvMap [IsManifold I ∞ M] (p : M)
    {s : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hs : MapsTo (coordEquiv E).symm s (extChartAt I p).target) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) I ∞ (chartInvMap (I := I) p) s :=
  (contMDiffOn_extChartAt_symm p).comp (coordEquiv E).symm.contDiff.contMDiff.contMDiffOn hs

/-- A smooth function of the coordinates on `Ω`, read on `M` through the chart at `p`, is smooth
on `chartNbhd p Ω`. -/
private theorem contMDiffOn_comp_coordEquiv_extChartAt [IsManifold I ∞ M] (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    {G : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ} (hG : ContDiffOn ℝ ∞ G Ω) :
    ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ G (coordEquiv E (extChartAt I p x)))
      (chartNbhd (I := I) p Ω) := by
  refine hG.contMDiffOn.comp ((coordEquiv E).contDiff.contMDiff.comp_contMDiffOn
    ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := p)).mono
      (extChartAt_source I p ▸ inter_subset_left))) ?_
  rintro x ⟨-, y, hyΩ, hyx⟩
  rw [mem_preimage, ← hyx, (coordEquiv E).apply_symm_apply]
  exact hyΩ

/-- In the basis-adapted coordinates `coordEquiv E ∘ extChartAt I p`, the Euclidean gradient of
`u ∘ chartInvMap p` has components equal to the derivatives of `u` along `chartLocalFrame`. -/
private theorem gradient_comp_coordEquiv_apply [I.Boundaryless] [IsManifold I ∞ M] (p : M)
    {u : M → ℝ} {y : EuclideanSpace ℝ (Fin (finrank ℝ E))}
    (hy : (coordEquiv E).symm y ∈ (extChartAt I p).target)
    (hu : MDifferentiableAt I 𝓘(ℝ) u (chartInvMap (I := I) p y))
    (k : Fin (finrank ℝ E)) :
    ∇ (fun z ↦ u (chartInvMap (I := I) p z)) y k =
      mvfderiv I u (chartInvMap (I := I) p y)
        (chartLocalFrame (I := I) p k (chartInvMap (I := I) p y)) := by
  have hx_src : chartInvMap (I := I) p y ∈ (chartAt H p).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target hy
  have hz_eq : extChartAt I p (chartInvMap (I := I) p y) = (coordEquiv E).symm y :=
    (extChartAt I p).right_inv hy
  have hcoord : ∇ (fun w ↦ u (chartInvMap (I := I) p w)) y k =
      ⟪∇ ((u ∘ (extChartAt I p).symm) ∘ (coordEquiv E).symm) y,
        EuclideanSpace.single k (1 : ℝ)⟫_ℝ := by
    rw [EuclideanSpace.inner_single_right, one_mul, conj_trivial]
    -- `chartInvMap p` is `(extChartAt I p).symm ∘ (coordEquiv E).symm` by definition.
    rfl
  rw [hcoord, gradient, InnerProductSpace.toDual_symm_apply,
    ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, coordEquiv_symm_single, ← hz_eq,
    ← mvfderiv_chartLocalFrame (I := I) p hx_src hu k]

/-- Pointwise identity between the Riemannian gradient inner product and the inverse chart Gram
bilinear form in coordinates. -/
private theorem inner_mgradient_eq_matrixBilinearForm [I.Boundaryless] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (p : M) {u v : M → ℝ}
    {y : EuclideanSpace ℝ (Fin (finrank ℝ E))}
    (hy : (coordEquiv E).symm y ∈ (extChartAt I p).target)
    (hu : MDifferentiableAt I 𝓘(ℝ) u (chartInvMap (I := I) p y))
    (hv : MDifferentiableAt I 𝓘(ℝ) v (chartInvMap (I := I) p y)) :
    ⟪mgradient I u (chartInvMap (I := I) p y),
        mgradient I v (chartInvMap (I := I) p y)⟫_ℝ =
      PDE.matrixBilinearForm
        (chartInvGramMatrix (I := I) p (chartInvMap (I := I) p y))
        (∇ (fun z ↦ v (chartInvMap (I := I) p z)) y)
        (∇ (fun z ↦ u (chartInvMap (I := I) p z)) y) := by
  have hx_src : chartInvMap (I := I) p y ∈ (chartAt H p).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target hy
  rw [real_inner_comm, inner_mgradient, mgradient_def,
    rieszDual_eq_sum_chartLocalFrame (I := I) p hx_src, map_sum]
  simp only [ContinuousLinearMap.map_smul, smul_eq_mul, PDE.matrixBilinearForm_apply,
    dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm, gradient_comp_coordEquiv_apply p hy hv i]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [gradient_comp_coordEquiv_apply p hy hu j]

section CoordIntegral

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

variable [CompactSpace M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The divergence-form principal matrix field `a(y) = ρ(ψ y) G⁻¹(ψ y)` in coordinates at `p`. -/
private def chartMatrix (p : M) (y : EuclideanSpace ℝ (Fin (finrank ℝ E))) :
    Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ :=
  chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) •
    chartInvGramMatrix (I := I) p (chartInvMap (I := I) p y)

/-- A real function on `M` vanishing outside `chartNbhd p Ω` integrates over `M` to the
density-weighted Euclidean integral over `Ω`. -/
private theorem integral_riemannianVolume_eq_setIntegral_coord (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target)
    {h : M → ℝ} (hsupp : ∀ x, x ∉ chartNbhd (I := I) p Ω → h x = 0) :
    ∫ x, h x ∂riemannianVolume I M =
      ∫ y in (Ω : Set _),
        chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
          h (chartInvMap (I := I) p y) := by
  let ΩE : Set E := (coordEquiv E).symm '' (Ω : Set _)
  have hΩEt : ΩE ⊆ (extChartAt I p).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact hΩt hy
  have hUsub : chartNbhd (I := I) p Ω ⊆ (chartAt H p).source := by
    rw [← extChartAt_source (I := I)]
    exact inter_subset_left
  have hUmeas : MeasurableSet (chartNbhd (I := I) p Ω) := (isOpen_chartNbhd p Ω).measurableSet
  have himg : extChartAt I p '' chartNbhd (I := I) p Ω = ΩE := by
    dsimp only [chartNbhd]
    rw [PartialEquiv.image_source_inter_eq',
      PartialEquiv.target_inter_inv_preimage_preimage, inter_eq_right.2 hΩEt]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    setIntegral_riemannianVolume_of_subset hUsub hUmeas, himg]
  simp only [smul_eq_mul]
  have hpre : (coordEquiv E).symm ⁻¹' ΩE = (Ω : Set _) :=
    (coordEquiv E).symm.injective.preimage_image _
  have hemb := (coordEquiv E).symm.toHomeomorph.measurableEmbedding
  have hmp := (measurePreserving_coordEquiv_symm E).restrict_preimage_emb hemb ΩE
  rw [← hpre]
  exact (hmp.integral_comp hemb fun z ↦
    chartVolumeDensity (I := I) p ((extChartAt I p).symm z) *
      h ((extChartAt I p).symm z)).symm

/-- A `riemannianVolume`-null subset of `chartNbhd p Ω` corresponds to a Lebesgue null subset of
`Ω`. -/
private theorem ae_eq_restrict_chart_iff (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target)
    {u g : M → ℝ} :
    u =ᵐ[(riemannianVolume I M).restrict (chartNbhd (I := I) p Ω)] g ↔
      (fun y ↦ u (chartInvMap (I := I) p y)) =ᵐ[volume.restrict (Ω : Set _)]
        fun y ↦ g (chartInvMap (I := I) p y) := by
  rw [EventuallyEq, EventuallyEq, ae_restrict_iff' (isOpen_chartNbhd p Ω).measurableSet,
    ae_restrict_iff' Ω.isOpen.measurableSet, MeasureTheory.ae_iff, MeasureTheory.ae_iff]
  simp only [Classical.not_imp]
  let S : Set M := {x | x ∈ chartNbhd (I := I) p Ω ∧ u x ≠ g x}
  let T : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))) :=
    {y | y ∈ (Ω : Set _) ∧ u (chartInvMap (I := I) p y) ≠ g (chartInvMap (I := I) p y)}
  have hSsub : S ⊆ (extChartAt I p).source := fun _ hx ↦ hx.1.1
  rw [riemannianVolume_eq_zero_iff_image_of_subset hSsub (Module.finBasis ℝ E).addHaar]
  have himg : (coordEquiv E).symm '' T = extChartAt I p '' S := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyΩ, hne⟩, rfl⟩
      have hzt : (coordEquiv E).symm y ∈ (extChartAt I p).target := hΩt hyΩ
      refine ⟨chartInvMap (I := I) p y, ⟨⟨(extChartAt I p).map_target hzt, ?_⟩, hne⟩,
        (extChartAt I p).right_inv hzt⟩
      rw [mem_preimage]
      dsimp only [chartInvMap]
      rw [(extChartAt I p).right_inv hzt]
      exact ⟨y, hyΩ, rfl⟩
    · rintro ⟨x, ⟨⟨hxs, y, hyΩ, hyx⟩, hne⟩, rfl⟩
      have hxy : chartInvMap (I := I) p y = x := by
        dsimp only [chartInvMap]
        rw [hyx, (extChartAt I p).left_inv hxs]
      exact ⟨y, ⟨hyΩ, by rwa [hxy]⟩, hyx⟩
  have hvol : volume T = (Module.finBasis ℝ E).addHaar ((coordEquiv E).symm '' T) := by
    have hemb := (coordEquiv E).symm.toHomeomorph.measurableEmbedding
    have hpre : (coordEquiv E).symm ⁻¹' ((coordEquiv E).symm '' T) = T :=
      (coordEquiv E).symm.injective.preimage_image T
    rw [← (measurePreserving_coordEquiv_symm E).measure_preimage_emb hemb, hpre]
  rw [← himg, hvol]

/-- Precomposition with `chartInvMap p` maps `Lʳ(M)` into `Lʳ(Ω)` whenever the chart density is
bounded below on `Ω`. -/
private theorem memLp_comp_coordEquiv_of_memLp (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target)
    {m : ℝ} (hm : 0 < m)
    (hρ : ∀ y ∈ Ω, m ≤ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y))
    {r : ℝ≥0∞} {f : M → ℝ} (hf : MemLp f r (riemannianVolume I M)) :
    MemLp (fun y ↦ f (chartInvMap (I := I) p y)) r (volume.restrict (Ω : Set _)) := by
  classical
  let ΩE : Set E := (coordEquiv E).symm '' (Ω : Set _)
  have hΩEo : IsOpen ΩE := (coordEquiv E).symm.toHomeomorph.isOpenMap _ Ω.isOpen
  have hΩEt : ΩE ⊆ (extChartAt I p).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact hΩt hy
  let ψ₀ : E → M := ΩE.piecewise (extChartAt I p).symm fun _ ↦ p
  have hψ₀m : Measurable ψ₀ :=
    ContinuousOn.measurable_piecewise ((continuousOn_extChartAt_symm p).mono hΩEt)
      continuousOn_const hΩEo.measurableSet
  let ψ : EuclideanSpace ℝ (Fin (finrank ℝ E)) → M := ψ₀ ∘ (coordEquiv E).symm
  have hψm : Measurable ψ := hψ₀m.comp (coordEquiv E).symm.continuous.measurable
  have hmap : (volume.restrict (Ω : Set _)).map ψ ≤
      ENNReal.ofReal m⁻¹ • riemannianVolume I M := by
    refine Measure.le_iff.2 fun s hs ↦ ?_
    rw [Measure.map_apply hψm hs, smul_apply, smul_eq_mul, ← lintegral_indicator_one hs,
      ← lintegral_indicator_one (hψm hs)]
    have hemb := (coordEquiv E).symm.toHomeomorph.measurableEmbedding
    have hpre : (coordEquiv E).symm ⁻¹' ΩE = (Ω : Set _) :=
      (coordEquiv E).symm.injective.preimage_image _
    have hmp := (measurePreserving_coordEquiv_symm E).restrict_preimage_emb hemb ΩE
    calc ∫⁻ y, (ψ ⁻¹' s).indicator 1 y ∂volume.restrict (Ω : Set _)
        = ∫⁻ y, (ψ₀ ⁻¹' s).indicator 1 ((coordEquiv E).symm y)
            ∂volume.restrict ((coordEquiv E).symm ⁻¹' ΩE) := by
          rw [hpre]
          refine lintegral_congr fun y ↦ ?_
          simp only [ψ, indicator_apply, mem_preimage, Function.comp_apply, Pi.one_apply]
      _ = ∫⁻ z in ΩE, (ψ₀ ⁻¹' s).indicator 1 z ∂(Module.finBasis ℝ E).addHaar :=
          hmp.lintegral_comp_emb hemb _
      _ = ∫⁻ z in ΩE, s.indicator 1 ((extChartAt I p).symm z)
            ∂(Module.finBasis ℝ E).addHaar := by
          refine setLIntegral_congr_fun hΩEo.measurableSet fun z hz ↦ ?_
          have hzψ : ψ₀ z = (extChartAt I p).symm z := piecewise_eq_of_mem _ _ _ hz
          simp only [indicator_apply, mem_preimage, hzψ, Pi.one_apply]
      _ ≤ ENNReal.ofReal m⁻¹ * ∫⁻ x, s.indicator 1 x ∂riemannianVolume I M := by
          refine setLIntegral_comp_extChartAt_symm_le_mul_lintegral p hΩEo hΩEt hm ?_ _
          rintro _ ⟨y, hy, rfl⟩
          exact hρ y hy
  have hmemψ : MemLp (f ∘ ψ) r (volume.restrict (Ω : Set _)) :=
    memLp_iff.2 ((eLpNorm_comp_le_of_map_le_smul hψm.aemeasurable hmap r).trans_lt
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        ENNReal.ofReal_ne_top) (memLp_iff.1 hf)))
  refine hmemψ.ae_eq ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
  have hmemE : (coordEquiv E).symm y ∈ ΩE := ⟨y, hy, rfl⟩
  simp only [Function.comp_apply, ψ, ψ₀, chartInvMap, piecewise_eq_of_mem _ _ _ hmemE]

end CoordIntegral

section Coefficients

variable [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The chart volume density read in coordinates is continuous on any set mapped into the chart
target. -/
private theorem continuousOn_chartVolumeDensity_chartInvMap (p : M)
    {K : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hKt : MapsTo (coordEquiv E).symm K (extChartAt I p).target) :
    ContinuousOn (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y)) K :=
  (continuousOn_chartVolumeDensity_extChartAt_symm p).comp
    (coordEquiv E).symm.continuous.continuousOn hKt

/-- The coefficient field `chartMatrix p` is continuous on any set mapped into the chart target. -/
private theorem continuousOn_chartMatrix (p : M)
    {K : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hKt : MapsTo (coordEquiv E).symm K (extChartAt I p).target) :
    ContinuousOn (chartMatrix (I := I) p) K := by
  have : IsManifold I ((0 : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  refine (continuousOn_chartVolumeDensity_chartInvMap p hKt).smul
    (continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦ ?_)
  exact (contMDiffOn_chartInvGramMatrix_entry (I := I) (n := 0) p i j).continuousOn.comp
    ((continuousOn_extChartAt_symm p).comp (coordEquiv E).symm.continuous.continuousOn hKt)
    (mapsTo_chartInvMap_baseSet p hKt)

omit [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- The coefficient field `chartMatrix p` is positive definite at every point of the chart
target. -/
private theorem posDef_chartMatrix (p : M) {y : EuclideanSpace ℝ (Fin (finrank ℝ E))}
    (hy : (coordEquiv E).symm y ∈ (extChartAt I p).target) :
    (chartMatrix (I := I) p y).PosDef := by
  have hyb := mapsTo_chartInvMap_baseSet (I := I) p (s := {y}) (by simpa using hy) rfl
  rw [chartMatrix, chartInvGramMatrix_def]
  exact (posDef_chartGramMatrix p hyb).inv.smul (chartVolumeDensity_pos p hyb)

/-- On an open coordinate set inside a compact set mapped into the chart target, a continuous
function on `M`, read in coordinates and weighted by the chart volume density, is square
integrable. -/
private theorem memLp_two_chartVolumeDensity_mul (p : M)
    {K : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))} (hK : IsCompact K)
    (hKt : MapsTo (coordEquiv E).symm K (extChartAt I p).target)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))} (hΩK : (Ω : Set _) ⊆ K)
    {f : M → ℝ} (hf : Continuous f) :
    MemLp (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
      f (chartInvMap (I := I) p y)) 2 (volume.restrict (Ω : Set _)) := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) :=
    isFiniteMeasure_restrict.2 ((measure_mono hΩK).trans_lt hK.measure_lt_top).ne
  refine (ContinuousOn.memLp_top_restrict_of_subset_isCompact ?_ hK Ω.isOpen.measurableSet
    hΩK).mono_exponent le_top
  exact (continuousOn_chartVolumeDensity_chartInvMap p hKt).mul (hf.continuousOn.comp
    ((continuousOn_extChartAt_symm p).comp (coordEquiv E).symm.continuous.continuousOn hKt)
    (mapsTo_univ _ _))

end Coefficients

section ChartBridge

variable [I.Boundaryless] [CompactSpace M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [T2Space M] in
/-- Identity between `dirichletForm w (ofSmooth Φ)` and the Euclidean `energyFormH1` when `Φ` is a
smooth function supported in `chartNbhd p Ω` that agrees with `φ ∈ 𝓓(Ω, ℝ)` in coordinates. -/
private theorem dirichletForm_eq_energyFormH1_of_eq (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target)
    (hcoeff : MemLp (fun y ↦ PDE.energyIntegrand (chartMatrix (I := I) p y) 0 0) ⊤
      (volume.restrict (Ω : Set _)))
    (T : SobolevH1 I M →L[ℝ] W1p volume Ω 2)
    (hTg : ∀ u : C^∞⟮I, M; ℝ⟯, W1p.gradient (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set _)]
      ∇ (fun y ↦ u (chartInvMap (I := I) p y)))
    (φ : 𝓓(Ω, ℝ)) (Φ : C^∞⟮I, M; ℝ⟯)
    (hΦ_ψ : ∀ y ∈ Ω, Φ (chartInvMap (I := I) p y) = φ y)
    (hΦ_U : tsupport (Φ : M → ℝ) ⊆ chartNbhd (I := I) p Ω) (w : SobolevH1 I M) :
    dirichletForm w (ofSmooth Φ) =
      PDE.energyFormH1 (chartMatrix (I := I) p) 0 0 (T w)
        (W1p.ofTestFunctionₗ volume Ω 2 φ) := by
  have hcont_lhs : Continuous fun w : SobolevH1 I M ↦ dirichletForm w (ofSmooth Φ) :=
    (dirichletForm.flip (ofSmooth Φ)).continuous
  have hcont_rhs : Continuous fun w : SobolevH1 I M ↦
      PDE.energyFormH1 (chartMatrix (I := I) p) 0 0 (T w)
        (W1p.ofTestFunctionₗ volume Ω 2 φ) := by
    have hL : (fun w : SobolevH1 I M ↦ PDE.energyFormH1 (chartMatrix (I := I) p) 0 0 (T w)
          (W1p.ofTestFunctionₗ volume Ω 2 φ)) =
        (((PDE.energyFormH1L hcoeff).flip (W1p.ofTestFunctionₗ volume Ω 2 φ)).comp T) :=
      funext fun w ↦ (PDE.energyFormH1L_apply hcoeff (T w) _).symm
    rw [hL]
    exact ContinuousLinearMap.continuous _
  refine induction_on w (isClosed_eq hcont_lhs hcont_rhs) fun u ↦ ?_
  rw [dirichletForm_ofSmooth, PDE.energyFormH1_zero_zero_eq_setIntegral]
  have hgrad_supp : ∀ x, x ∉ chartNbhd (I := I) p Ω →
      ⟪mgradient I u x, mgradient I Φ x⟫_ℝ = 0 := fun x hxU ↦ by
    have hxΦ : x ∉ tsupport (Φ : M → ℝ) := fun h ↦ hxU (hΦ_U h)
    have hev : (Φ : M → ℝ) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.1 hxΦ
    have hm0 : mgradient I (Φ : M → ℝ) x = 0 := by
      rw [mgradient_eq_zero_iff, hev.mvfderiv_eq, mvfderiv_eq_zero_iff]
      exact mfderiv_const
    rw [hm0, inner_zero_right]
  rw [integral_riemannianVolume_eq_setIntegral_coord p hΩt hgrad_supp]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet, hTg u,
    gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with y hy hgu hgφ
  have hΦ_ev : (fun z ↦ Φ (chartInvMap (I := I) p z)) =ᶠ[𝓝 y] (φ : _ → ℝ) :=
    Filter.eventually_of_mem (Ω.isOpen.mem_nhds hy) fun z hz ↦ hΦ_ψ z hz
  have hgradΦ : ∇ (fun z ↦ Φ (chartInvMap (I := I) p z)) y = ∇ (φ : _ → ℝ) y := by
    rw [gradient, gradient, hΦ_ev.fderiv_eq]
  have hdu : MDifferentiableAt I 𝓘(ℝ) u (chartInvMap (I := I) p y) :=
    (u.contMDiff.mdifferentiable (by simp)) _
  have hdΦ : MDifferentiableAt I 𝓘(ℝ) Φ (chartInvMap (I := I) p y) :=
    (Φ.contMDiff.mdifferentiable (by simp)) _
  rw [W1p.gradient_ofTestFunctionₗ, hgφ, hgu,
    inner_mgradient_eq_matrixBilinearForm p (hΩt hy) hdu hdΦ, hgradΦ]
  simp [chartMatrix, PDE.matrixBilinearForm_apply, smul_eq_mul]

/-- Transplant a Euclidean test function `φ ∈ 𝓓(Ω, ℝ)` along `coordEquiv E ∘ extChartAt I p` to
`Φ ∈ C^∞(M)`, transforming both `dirichletForm` and `L²(M)` pairings into coordinates. -/
private theorem exists_contMDiff_of_testFunction (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target)
    (hcoeff : MemLp (fun y ↦ PDE.energyIntegrand (chartMatrix (I := I) p y) 0 0) ⊤
      (volume.restrict (Ω : Set _)))
    (T : SobolevH1 I M →L[ℝ] W1p volume Ω 2)
    (hTg : ∀ u : C^∞⟮I, M; ℝ⟯, W1p.gradient (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set _)]
      ∇ (fun y ↦ u (chartInvMap (I := I) p y)))
    (φ : 𝓓(Ω, ℝ)) :
    ∃ Φ : C^∞⟮I, M; ℝ⟯,
      (∀ w : SobolevH1 I M, dirichletForm w (ofSmooth Φ) =
        PDE.energyFormH1 (chartMatrix (I := I) p) 0 0 (T w)
          (W1p.ofTestFunctionₗ volume Ω 2 φ)) ∧
      ∀ f : M → ℝ, ∫ x, f x * Φ x ∂riemannianVolume I M =
        ∫ y in (Ω : Set _),
          (chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
            f (chartInvMap (I := I) p y)) * φ y := by
  let wE : E → ℝ := fun z ↦ φ (coordEquiv E z)
  have hwE_smooth : ContDiff ℝ ∞ wE := φ.contDiff.comp (coordEquiv E).contDiff
  have hsupp_sub : tsupport wE ⊆ (coordEquiv E).symm '' tsupport (φ : _ → ℝ) := by
    refine closure_minimal (fun z hz ↦ ?_)
      (φ.hasCompactSupport.isCompact.image (coordEquiv E).symm.continuous).isClosed
    exact ⟨coordEquiv E z, subset_tsupport _ hz, (coordEquiv E).symm_apply_apply z⟩
  have hwE_comp : HasCompactSupport wE :=
    (φ.hasCompactSupport.isCompact.image (coordEquiv E).symm.continuous).of_isClosed_subset
      (isClosed_tsupport wE) hsupp_sub
  have hφΩ : tsupport (φ : _ → ℝ) ⊆ (Ω : Set _) := φ.tsupport_subset
  have hwE_tgt : tsupport wE ⊆ (extChartAt I p).target := by
    refine hsupp_sub.trans ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hΩt (hφΩ hy)
  obtain ⟨Φ₀, hΦ₀, -, hΦ₀supp, hΦ₀eq⟩ :=
    exists_contMDiff_comp_extChartAt_symm_eq (I := I) (n := ∞) (c := p) hwE_smooth hwE_comp hwE_tgt
  let Φ : C^∞⟮I, M; ℝ⟯ := ⟨Φ₀, hΦ₀⟩
  have hΦ_coe (x : M) : Φ x = Φ₀ x := congrFun (ContMDiffMap.coeFn_mk Φ₀ hΦ₀) x
  have hΦ_ψ (y : EuclideanSpace ℝ (Fin (finrank ℝ E))) (hy : y ∈ Ω) :
      Φ (chartInvMap (I := I) p y) = φ y := by
    rw [hΦ_coe, chartInvMap, hΦ₀eq _ (hΩt hy)]
    simp [wE]
  have hΦ_U : tsupport (Φ : M → ℝ) ⊆ chartNbhd (I := I) p Ω := by
    refine hΦ₀supp.trans ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hsupp_sub hz
    have hyt : (coordEquiv E).symm y ∈ (extChartAt I p).target := hΩt (hφΩ hy)
    refine ⟨(extChartAt I p).map_target hyt, ?_⟩
    rw [mem_preimage, (extChartAt I p).right_inv hyt]
    exact ⟨y, hφΩ hy, rfl⟩
  refine ⟨Φ, dirichletForm_eq_energyFormH1_of_eq p hΩt hcoeff T hTg φ Φ hΦ_ψ hΦ_U, fun f ↦ ?_⟩
  have hf_supp : ∀ x, x ∉ chartNbhd (I := I) p Ω → f x * Φ x = 0 := fun x hxU ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hxU (hΦ_U h), mul_zero]
  rw [integral_riemannianVolume_eq_setIntegral_coord p hΩt hf_supp]
  refine setIntegral_congr_fun Ω.isOpen.measurableSet fun y hy ↦ ?_
  rw [hΦ_ψ y hy, mul_assoc]

/-- Bundled local chart data at `p ∈ M` identifying `dirichletForm` on `H¹(M)` with the Euclidean
divergence-form energy form `energyFormH1 (chartMatrix p) 0 0` on an open coordinate domain `Ω`. -/
private structure ChartPDEData (p : M) where
  Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))
  hpΩ : coordEquiv E (extChartAt I p p) ∈ Ω
  hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target
  hρ_cont : ContinuousOn
    (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y)) Ω
  m : ℝ
  hm : 0 < m
  hρ_min : ∀ y ∈ Ω, m ≤ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y)
  M_ρ : ℝ
  hρ_max : ∀ y ∈ Ω, ‖chartVolumeDensity (I := I) p (chartInvMap (I := I) p y)‖ ≤ M_ρ
  lam : ℝ
  Lam : ℝ
  hell : PDE.UniformlyEllipticOn (Ω : Set _) (chartMatrix (I := I) p) lam Lam
  ha_meas : AEStronglyMeasurable (chartMatrix (I := I) p) (volume.restrict (Ω : Set _))
  hcoeff : MemLp (fun y ↦ PDE.energyIntegrand (chartMatrix (I := I) p y) 0 0) ⊤
    (volume.restrict (Ω : Set _))
  hF_memLp2 : ∀ {f : M → ℝ}, Continuous f →
    MemLp (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
      f (chartInvMap (I := I) p y)) 2 (volume.restrict (Ω : Set _))
  T : SobolevH1 I M →L[ℝ] W1p volume Ω 2
  hTv : ∀ w : SobolevH1 I M,
    W1p.value (T w) =ᵐ[volume.restrict (Ω : Set _)]
      fun y ↦ toLp w (chartInvMap (I := I) p y)
  htest : ∀ φ : 𝓓(Ω, ℝ), ∃ Φ : C^∞⟮I, M; ℝ⟯,
    (∀ w : SobolevH1 I M, dirichletForm w (ofSmooth Φ) =
      PDE.energyFormH1 (chartMatrix (I := I) p) 0 0 (T w)
        (W1p.ofTestFunctionₗ volume Ω 2 φ)) ∧
    ∀ f : M → ℝ, ∫ x, f x * Φ x ∂riemannianVolume I M =
      ∫ y in (Ω : Set _),
        (chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
          f (chartInvMap (I := I) p y)) * φ y

/-- Construction of `ChartPDEData` around any point `p ∈ M`. -/
private theorem nonempty_chartPDEData (p : M) : Nonempty (ChartPDEData (I := I) p) := by
  obtain ⟨Ω₀, hpΩ₀, hΩ₀t, T₀, hT₀s, hT₀v⟩ :=
    exists_continuousLinearMap_w1p_extChartAt (I := I) (M := M) p (coordEquiv E)
  let z₀ := coordEquiv E (extChartAt I p p)
  obtain ⟨δ, hδ, hKΩ₀⟩ := nhds_basis_closedBall.mem_iff.1 (Ω₀.isOpen.mem_nhds hpΩ₀)
  let K : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))) := closedBall z₀ δ
  let Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))) := ⟨ball z₀ δ, isOpen_ball⟩
  have hKcomp : IsCompact K := isCompact_closedBall z₀ δ
  have hKne : K.Nonempty := ⟨z₀, mem_closedBall_self hδ.le⟩
  have hΩK : (Ω : Set _) ⊆ K := ball_subset_closedBall
  have hΩΩ₀ : Ω ≤ Ω₀ := hΩK.trans hKΩ₀
  have hKt : MapsTo (coordEquiv E).symm K (extChartAt I p).target := hΩ₀t.mono_left hKΩ₀
  have hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target := hKt.mono_left hΩK
  -- On the compact ball `K` the density is bounded above and below, and `a = chartMatrix p` is
  -- continuous and positive definite, hence uniformly elliptic.
  have hρ_contK := continuousOn_chartVolumeDensity_chartInvMap p hKt
  obtain ⟨y_min, hy_min, hρ_min⟩ := hKcomp.exists_isMinOn hKne hρ_contK
  have hm_pos : 0 < chartVolumeDensity (I := I) p (chartInvMap (I := I) p y_min) :=
    chartVolumeDensity_pos p (mapsTo_chartInvMap_baseSet p hKt hy_min)
  obtain ⟨y_max, -, hρ_max⟩ := hKcomp.exists_isMaxOn hKne hρ_contK.norm
  have ha_cont := continuousOn_chartMatrix p hKt
  have ha_pos : ∀ y ∈ K, (chartMatrix (I := I) p y).PosDef := fun y hy ↦
    posDef_chartMatrix p (hKt hy)
  obtain ⟨lam, Lam, hell⟩ :=
    PDE.exists_uniformlyEllipticOn_of_isCompact_of_posDef hKcomp ha_cont ha_pos
  replace hell := hell.mono_set hΩK
  let : PseudoMetrizableSpace (Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin (finrank ℝ E) → Fin (finrank ℝ E) → ℝ))
  have ha_meas : AEStronglyMeasurable (chartMatrix (I := I) p) (volume.restrict (Ω : Set _)) :=
    (ha_cont.mono hΩK).aestronglyMeasurable Ω.isOpen.measurableSet
  -- The coefficients of the energy form are bounded.
  have hcoeff : MemLp (fun y ↦ PDE.energyIntegrand (chartMatrix (I := I) p y) 0 0) ⊤
      (volume.restrict (Ω : Set _)) :=
    PDE.memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
      hell.upper_nonneg ha_meas aestronglyMeasurable_const aestronglyMeasurable_const
      (fun _ hy η ξ ↦ hell.upper_bound hy η ξ) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
  refine ⟨⟨Ω, mem_ball_self hδ, hΩt, hρ_contK.mono hΩK, _, hm_pos, fun y hy ↦ hρ_min (hΩK hy),
    _, fun y hy ↦ hρ_max (hΩK hy), lam, Lam, hell, ha_meas, hcoeff,
    fun hf ↦ memLp_two_chartVolumeDensity_mul p hKcomp hKt hΩK hf,
    (W1p.restrictL hΩΩ₀).comp T₀,
    fun w ↦ (W1p.value_restrictL_ae hΩΩ₀ (T₀ w)).trans
      (ae_restrict_of_ae_restrict_of_subset hΩΩ₀ (hT₀v w)),
    exists_contMDiff_of_testFunction p hΩt hcoeff ((W1p.restrictL hΩΩ₀).comp T₀) fun u ↦
      (W1p.gradient_restrictL_ae hΩΩ₀ (T₀ (ofSmooth u))).trans
        (ae_restrict_of_ae_restrict_of_subset hΩΩ₀ (hT₀s u).2)⟩⟩

end ChartBridge

end CoordinatePDE

section DeGiorgi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [I.Boundaryless] [T2Space M] in
/-- **De Giorgi continuity in a chart.** For `r ≥ 2` with `r > dim M / 2` and `f ∈ Lʳ(M)`, a weak
solution `w ∈ H¹(M)` of `Δ⁺w = f` agrees almost everywhere on the chart neighbourhood of `d` with a
function continuous there. -/
private theorem ChartPDEData.exists_continuousOn_ae_eq [Nonempty (Fin (finrank ℝ E))] {p : M}
    (d : ChartPDEData (I := I) p) {r : ℝ≥0} (hr : 2 ≤ r) (hrn : (finrank ℝ E : ℝ) < 2 * r)
    {f : M → ℝ} (hf : MemLp f r (riemannianVolume I M)) {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth φ) = ∫ x, f x * φ x ∂riemannianVolume I M) :
    ∃ g : M → ℝ, ContinuousOn g (chartNbhd (I := I) p d.Ω) ∧
      toLp w =ᵐ[(riemannianVolume I M).restrict (chartNbhd (I := I) p d.Ω)] g := by
  -- In coordinates `w` solves a divergence-form equation with forcing `ρ · (f ∘ ψ) ∈ Lʳ`.
  have hf_coord : MemLp (fun y ↦ f (chartInvMap (I := I) p y)) r
      (volume.restrict (d.Ω : Set _)) :=
    memLp_comp_coordEquiv_of_memLp p d.hΩt d.hm d.hρ_min hf
  have hF_memLp : MemLp (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
      f (chartInvMap (I := I) p y)) r (volume.restrict (d.Ω : Set _)) :=
    hf_coord.of_le_mul
      ((d.hρ_cont.aestronglyMeasurable d.Ω.isOpen.measurableSet).mul
        hf_coord.aestronglyMeasurable)
      ((ae_restrict_mem d.Ω.isOpen.measurableSet).mono fun y hy ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (d.hρ_max y hy) (norm_nonneg _))
  have hcont_rep : ContinuousOn (preciseRepresentative volume (W1p.value (d.T w))) d.Ω :=
    PDE.continuousOn_preciseRepresentative_of_forall_memLp hr (by simpa using hrn) d.hell
      d.ha_meas (fun L _ hLΩ ↦ hF_memLp.mono_measure (Measure.restrict_mono hLΩ le_rfl))
      fun φ ↦ by
        obtain ⟨Φ, hD, hI⟩ := d.htest φ
        exact (hD w).symm.trans ((hw Φ).trans (hI f))
  -- The precise representative, read back on `M`, is the continuous representative.
  let g : M → ℝ := fun x ↦ preciseRepresentative volume (W1p.value (d.T w))
    (coordEquiv E (extChartAt I p x))
  refine ⟨g, ?_, (ae_eq_restrict_chart_iff p d.hΩt).2 ?_⟩
  · refine hcont_rep.comp ((coordEquiv E).continuous.continuousOn.comp
      ((continuousOn_extChartAt p).mono inter_subset_left) (mapsTo_univ _ _)) ?_
    rintro x ⟨-, y, hyΩ, hyx⟩
    dsimp only [Function.comp_apply]
    rw [← hyx, (coordEquiv E).apply_symm_apply]
    exact hyΩ
  · filter_upwards [ae_restrict_mem d.Ω.isOpen.measurableSet,
      (d.hTv w).symm, W1p.ae_eq_preciseRepresentative (d.T w)] with y hy h1 h2
    have hψg : g (chartInvMap (I := I) p y) =
        preciseRepresentative volume (W1p.value (d.T w)) y := by
      dsimp only [g, chartInvMap]
      rw [(extChartAt I p).right_inv (d.hΩt hy), (coordEquiv E).apply_symm_apply]
    rw [h1, h2, hψg]

/-- **De Giorgi continuity on `H¹(M)`.** Let `M` be a closed smooth manifold with a continuous
Riemannian metric, let `r ≥ 2` with `r > dim M / 2`, and let `f ∈ Lʳ(M)`. Every `w ∈ H¹(M)`
solving `D(w, φ) = ∫ f φ dV` against all smooth functions `φ` agrees `riemannianVolume`-almost
everywhere with a continuous function on `M`. -/
theorem exists_continuous_ae_eq_of_dirichletForm_eq {r : ℝ≥0} (hr : 2 ≤ r)
    (hrn : (finrank ℝ E : ℝ) < 2 * r) {f : M → ℝ} (hf : MemLp f r (riemannianVolume I M))
    {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth φ) = ∫ x, f x * φ x ∂riemannianVolume I M) :
    ∃ u : M → ℝ, Continuous u ∧ toLp w =ᵐ[riemannianVolume I M] u := by
  -- In dimension zero, every chart source is a singleton, so `M` is discrete.
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with hdim | hdim
  · have : Subsingleton E := finrank_zero_iff.1 hdim
    have : Subsingleton H := I.injective.subsingleton
    have : DiscreteTopology M := ChartedSpace.discreteTopology H M
    exact ⟨toLp w, continuous_of_discreteTopology, Filter.EventuallyEq.rfl⟩
  have : Nonempty (Fin (finrank ℝ E)) := Fin.pos_iff_nonempty.1 hdim
  -- Glue the continuous representatives found in charts.
  obtain ⟨u, hu, hwu⟩ := exists_contMDiff_ae_eq_of_locally (I := I) (I' := 𝓘(ℝ)) (n := 0)
    (μ := riemannianVolume I M) (u := (toLp w : M → ℝ)) fun p ↦ by
      obtain ⟨d⟩ := nonempty_chartPDEData (I := I) p
      obtain ⟨g, hg, hwg⟩ := d.exists_continuousOn_ae_eq hr hrn hf hw
      exact ⟨_, (isOpen_chartNbhd p d.Ω).mem_nhds (mem_chartNbhd_self p d.hpΩ), g,
        contMDiffOn_zero_iff.2 hg, hwg⟩
  exact ⟨u, contMDiff_zero_iff.1 hu, hwu⟩

end DeGiorgi

section SmoothRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section C1

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

local instance instIsContinuousRiemannianBundleOfContMDiffOne :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- If `w ∈ H¹(M)` agrees almost everywhere with a smooth function `u` and solves `D(w, φ) = ∫ f φ`
for a continuous function `f`, then `w = ofSmooth u` and `-laplaceBeltrami I u x = f x` holds
pointwise everywhere on `M`. -/
theorem eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq
    {w : SobolevH1 I M} {u : C^∞⟮I, M; ℝ⟯} {f : M → ℝ} (hf : Continuous f)
    (hwu : toLp w =ᵐ[riemannianVolume I M] u)
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth φ) = ∫ x, f x * φ x ∂riemannianVolume I M) :
    w = ofSmooth u ∧ ∀ x, -laplaceBeltrami I u x = f x := by
  have hw_eq : w = ofSmooth u :=
    toLp_injective (Lp.ext (hwu.trans (toLp_ofSmooth_ae_eq u).symm))
  refine ⟨hw_eq, fun x ↦ sub_eq_zero.1 ?_⟩
  have hΔ_cont : Continuous (-laplaceBeltrami I u) :=
    (continuous_laplaceBeltrami (u.contMDiff.of_le (by simp))).neg
  have hdiff_cont : Continuous fun y ↦ -laplaceBeltrami I u y - f y := hΔ_cont.sub hf
  -- Green's identity turns the weak equation into orthogonality of `-Δu - f` to every smooth `φ`.
  have horth (φ : C^∞⟮I, M; ℝ⟯) :
      ∫ y, φ y • (-laplaceBeltrami I u y - f y) ∂riemannianVolume I M = 0 := by
    have h1 := hw φ
    rw [hw_eq, dirichletForm_comm, dirichletForm_ofSmooth_right] at h1
    have h2 : ∫ y, toLp (ofSmooth φ) y * -laplaceBeltrami I u y ∂riemannianVolume I M =
        ∫ y, φ y * -laplaceBeltrami I u y ∂riemannianVolume I M :=
      integral_congr_ae ((toLp_ofSmooth_ae_eq φ).mono fun y hy ↦ congrArg (· * _) hy)
    have hint1 : Integrable (fun y ↦ φ y * -laplaceBeltrami I u y) (riemannianVolume I M) :=
      ((map_continuous φ).mul hΔ_cont).integrable_of_compactSpace
    have hint2 : Integrable (fun y ↦ φ y * f y) (riemannianVolume I M) :=
      ((map_continuous φ).mul hf).integrable_of_compactSpace
    simp_rw [smul_eq_mul, mul_sub]
    rw [integral_sub hint1 hint2, ← h2, h1, sub_eq_zero]
    simp_rw [mul_comm]
  -- A continuous function orthogonal to every smooth function vanishes almost everywhere, hence
  -- everywhere since the Riemannian volume charges every nonempty open set.
  have hzero : (fun y ↦ -laplaceBeltrami I u y - f y) =ᵐ[riemannianVolume I M] 0 :=
    ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hdiff_cont.locallyIntegrable
      fun φ hφ _ ↦ horth ⟨φ, hφ⟩
  exact congrFun (Measure.eq_of_ae_eq hzero hdiff_cont continuous_zero) x

end C1

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

local instance instIsContinuousRiemannianBundleOfContMDiffInfty :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

omit [I.Boundaryless] [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- Smoothness of the chart volume density in coordinates when the Riemannian metric is smooth. -/
private theorem contDiffOn_chartVolumeDensity_chartInvMap (p : M)
    {s : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hs : MapsTo (coordEquiv E).symm s (extChartAt I p).target) :
    ContDiffOn ℝ ∞ (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y)) s := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  exact ((contMDiffOn_chartVolumeDensity (I := I) (n := ∞) p).comp
    (contMDiffOn_chartInvMap p hs) (mapsTo_chartInvMap_baseSet p hs)).contDiffOn

omit [I.Boundaryless] [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- Smoothness of the coordinate coefficient matrix `chartMatrix p` when the Riemannian metric is
smooth. -/
private theorem contDiffOn_chartMatrix (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target)
    (i j : Fin (finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun y ↦ chartMatrix (I := I) p y i j) Ω := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hG : ContDiffOn ℝ ∞
      (fun y ↦ chartInvGramMatrix (I := I) p (chartInvMap (I := I) p y) i j) Ω :=
    ((contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) p i j).comp
      (contMDiffOn_chartInvMap p hΩt) (mapsTo_chartInvMap_baseSet p hΩt)).contDiffOn
  simpa only [chartMatrix, Matrix.smul_apply, smul_eq_mul] using
    (contDiffOn_chartVolumeDensity_chartInvMap p hΩt).mul hG

omit [I.Boundaryless] [T2Space M] in
/-- **Semilinear smooth bootstrap in a chart.** In dimension at most three, a continuous
representative `u` of a weak solution `w ∈ H¹(M)` of `Δ⁺w = A Φ(u) + C`, read in the coordinates of
the chart data `d`, is smooth on the coordinate domain. -/
private theorem ChartPDEData.contDiffOn_comp_chartInvMap_of_dirichletForm_eq {p : M}
    (d : ChartPDEData (I := I) p) (hE : finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M} {u : M → ℝ}
    (hu_cont : Continuous u) (hwu : toLp w =ᵐ[riemannianVolume I M] u)
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) =
      ∫ x, (A x * Φ (u x) + C x) * φ x ∂riemannianVolume I M) :
    ContDiffOn ℝ ∞ (fun y ↦ u (chartInvMap (I := I) p y)) d.Ω := by
  -- In coordinates the equation reads `-div(a ∇(u ∘ ψ)) = A₀ Φ(u ∘ ψ) + C₀` with `A₀ = ρ (A ∘ ψ)`
  -- and `C₀ = ρ (C ∘ ψ)`, where `ψ` is the inverse chart and `ρ` the chart volume density.
  let A₀ : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ :=
    fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) * A (chartInvMap (I := I) p y)
  let C₀ : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ :=
    fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) * C (chartInvMap (I := I) p y)
  have hψ := contMDiffOn_chartInvMap p d.hΩt
  have hA₀ : ContDiffOn ℝ ∞ A₀ d.Ω :=
    (contDiffOn_chartVolumeDensity_chartInvMap p d.hΩt).mul (hA.comp_contMDiffOn hψ).contDiffOn
  have hC₀ : ContDiffOn ℝ ∞ C₀ d.Ω :=
    (contDiffOn_chartVolumeDensity_chartInvMap p d.hΩt).mul (hC.comp_contMDiffOn hψ).contDiffOn
  let F : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ :=
    fun y ↦ A₀ y * Φ (u (chartInvMap (I := I) p y)) + C₀ y
  have hF_eq (y : EuclideanSpace ℝ (Fin (finrank ℝ E))) :
      chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
        (A (chartInvMap (I := I) p y) * Φ (u (chartInvMap (I := I) p y)) +
          C (chartInvMap (I := I) p y)) = F y := by
    dsimp only [F, A₀, C₀]
    ring
  have hRHS_cont : Continuous fun x ↦ A x * Φ (u x) + C x :=
    (hA.continuous.mul (hΦ.continuous.comp hu_cont)).add hC.continuous
  have hF_L2 : MemLp F 2 (volume.restrict (d.Ω : Set _)) :=
    (d.hF_memLp2 hRHS_cont).ae_eq (Filter.Eventually.of_forall hF_eq)
  have hu_test : ∀ φ : 𝓓(d.Ω, ℝ),
      PDE.energyFormH1 (chartMatrix (I := I) p) 0 0 (d.T w)
          (W1p.ofTestFunctionₗ volume d.Ω 2 φ) =
        ∫ y in (d.Ω : Set _), F y * φ y := fun φ ↦ by
    obtain ⟨Φt, hD, hI⟩ := d.htest φ
    refine (hD w).symm.trans ((hw Φt).trans ((hI fun x ↦ A x * Φ (u x) + C x).trans ?_))
    simp_rw [hF_eq]
  -- The equation extends from test functions to `H¹₀(Ω)`, as the Euclidean bootstrap requires.
  have hu_H10 := PDE.forall_energyFormH1_restrictL_eq_setIntegral
    (le_rfl : d.Ω ≤ d.Ω) d.hcoeff hu_test hF_L2
  have h_id : W1p.restrictL (le_rfl : d.Ω ≤ d.Ω) (d.T w) = d.T w :=
    W1p.ext_value (Lp.ext (W1p.value_restrictL_ae le_rfl (d.T w)))
  rw [h_id] at hu_H10
  have hTv_u : W1p.value (d.T w) =ᵐ[volume.restrict (d.Ω : Set _)]
      fun y ↦ u (chartInvMap (I := I) p y) :=
    (d.hTv w).trans ((ae_eq_restrict_chart_iff p d.hΩt).1 (ae_restrict_of_ae hwu))
  exact d.hell.contDiffOn_of_energyFormH1_eq (by simpa using hE) (contDiffOn_chartMatrix p d.hΩt)
    hA₀ hC₀ hΦ (hu_cont.continuousOn.comp hψ.continuousOn (mapsTo_univ _ _)) hTv_u hu_H10

/-- **Semilinear smooth bootstrap on `H¹(M)`.** Let `M` be a closed smooth Riemannian manifold of
dimension at most three, let `A` and `C` be smooth on `M`, and let `Φ : ℝ → ℝ` be smooth. If
`w ∈ H¹(M)` agrees almost everywhere with a continuous function `u : M → ℝ` and solves
`D(w, φ) = ∫ (A Φ(u) + C) φ dV` against every smooth function `φ`, then `u` is smooth on `M`
and `-laplaceBeltrami I u x = A x * Φ (u x) + C x` holds everywhere on `M`. -/
theorem contMDiff_of_dirichletForm_eq_semilinear (hE : finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M} {u : M → ℝ}
    (hu_cont : Continuous u) (hwu : toLp w =ᵐ[riemannianVolume I M] u)
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) =
      ∫ x, (A x * Φ (u x) + C x) * φ x ∂riemannianVolume I M) :
    ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ x, -laplaceBeltrami I u x = A x * Φ (u x) + C x := by
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  -- Near `p`, `u` agrees with its smooth reading in the coordinates of a chart at `p`.
  have hu_smooth : ContMDiff I 𝓘(ℝ) ∞ u := fun p ↦ by
    obtain ⟨d⟩ := nonempty_chartPDEData (I := I) p
    have hcoord := d.contDiffOn_comp_chartInvMap_of_dirichletForm_eq hE hA hC hΦ hu_cont hwu hw
    refine ((contMDiffOn_comp_coordEquiv_extChartAt p hcoord).congr fun x hx ↦ ?_).contMDiffAt
      ((isOpen_chartNbhd p d.Ω).mem_nhds (mem_chartNbhd_self p d.hpΩ))
    dsimp only [chartInvMap]
    rw [(coordEquiv E).symm_apply_apply, (extChartAt I p).left_inv hx.1]
  exact ⟨hu_smooth, (eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq
    (u := ⟨u, hu_smooth⟩)
    ((hA.continuous.mul (hΦ.continuous.comp hu_cont)).add hC.continuous) hwu hw).2⟩

/-- The reading `ρ (g ∘ ψ)` in the coordinates at `p` of a function `g` on `M`, weighted by the
chart volume density `ρ`, where `ψ` is the inverse chart. Integrals against the Riemannian volume
become Lebesgue integrals of such readings. -/
private def chartWeighted (p : M) (g : M → ℝ) (y : EuclideanSpace ℝ (Fin (finrank ℝ E))) : ℝ :=
  chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) * g (chartInvMap (I := I) p y)

omit [I.Boundaryless] [T2Space M] in
/-- The coordinate reading `ρ (V ∘ ψ)` of a continuous function `V` is bounded on the coordinate
domain of the chart data `d`, since the chart density is bounded there and `V` is bounded on the
compact manifold. -/
private theorem ChartPDEData.exists_norm_chartWeighted_le {p : M} (d : ChartPDEData (I := I) p)
    {V : M → ℝ} (hV : Continuous V) :
    ∃ C, ∀ y ∈ (d.Ω : Set _), ‖chartWeighted (I := I) p V y‖ ≤ C := by
  obtain ⟨CV, hCV⟩ := (isCompact_range hV).isBounded.exists_norm_le
  refine ⟨d.M_ρ * CV, fun y hy ↦ ?_⟩
  rw [chartWeighted, norm_mul]
  exact mul_le_mul (d.hρ_max y hy) (hCV _ (mem_range_self _)) (norm_nonneg _)
    ((norm_nonneg _).trans (d.hρ_max y hy))

omit [I.Boundaryless] [T2Space M] in
/-- The coordinate reading `ρ (V ∘ ψ)` of a continuous function `V` is essentially bounded on the
coordinate domain of the chart data `d`. -/
private theorem ChartPDEData.memLp_top_chartWeighted {p : M} (d : ChartPDEData (I := I) p)
    {V : M → ℝ} (hV : Continuous V) :
    MemLp (chartWeighted (I := I) p V) ⊤ (volume.restrict (d.Ω : Set _)) := by
  obtain ⟨C, hC⟩ := d.exists_norm_chartWeighted_le hV
  have hc_cont : ContinuousOn (chartWeighted (I := I) p V) d.Ω :=
    d.hρ_cont.mul (hV.comp_continuousOn (contMDiffOn_chartInvMap p d.hΩt).continuousOn)
  exact memLp_top_of_bound (hc_cont.aestronglyMeasurable d.Ω.isOpen.measurableSet) C
    ((ae_restrict_mem d.Ω.isOpen.measurableSet).mono hC)

omit [I.Boundaryless] [T2Space M] in
/-- **The weak equation `Δ⁺w + V w = f` in a chart, against test functions.** Read in the
coordinates of the chart data `d`, a weak solution `w ∈ H¹(M)` of `Δ⁺w + V w = f` with
continuous `V` weakly solves `-div(a ∇(w ∘ ψ)) + ρ (V ∘ ψ) (w ∘ ψ) = ρ (f ∘ ψ)` against test
functions. -/
private theorem ChartPDEData.energyFormH1_ofTestFunctionₗ_eq_of_dirichletForm_add_eq {p : M}
    (d : ChartPDEData (I := I) p) {V f : M → ℝ} (hV : Continuous V) {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) +
        ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M =
      ∫ x, f x * φ x ∂riemannianVolume I M) (φ : 𝓓(d.Ω, ℝ)) :
    PDE.energyFormH1 (chartMatrix (I := I) p) 0 (chartWeighted (I := I) p V) (d.T w)
        (W1p.ofTestFunctionₗ volume d.Ω 2 φ) =
      ∫ y in (d.Ω : Set _), chartWeighted (I := I) p f y * φ y := by
  obtain ⟨Φ, hD, hI⟩ := d.htest φ
  have hmass := PDE.energyFormH1_mass_add (b := 0) (c := 0) d.hcoeff
    (d.memLp_top_chartWeighted hV) (d.T w) (W1p.ofTestFunctionₗ volume d.Ω 2 φ)
  simp only [Pi.zero_apply, zero_add] at hmass
  -- In coordinates the potential term `∫ V w Φ dV` is the mass term `∫ ρ (V ∘ ψ) (w ∘ ψ) φ`.
  have hVw := hI fun x ↦ V x * toLp w x
  refine Eq.trans ?_ ((hw Φ).trans (hI f))
  rw [hmass, ← hD w, hVw]
  refine congrArg _ (integral_congr_ae ?_)
  filter_upwards [d.hTv w, W1p.value_ofTestFunctionₗ_ae (p := 2) φ] with y hy hφ
  rw [hy, hφ, chartWeighted]
  ring

omit [I.Boundaryless] [T2Space M] in
/-- **The weak equation `Δ⁺w + V w = f` in a chart.** Read in the coordinates of the chart data
`d`, a weak solution `w ∈ H¹(M)` of `Δ⁺w + V w = f` with continuous `V` and `f` weakly solves
`-div(a ∇(w ∘ ψ)) + ρ (V ∘ ψ) (w ∘ ψ) = ρ (f ∘ ψ)` against all of `H¹₀`. -/
private theorem ChartPDEData.energyFormH1_eq_setIntegral_of_dirichletForm_add_eq {p : M}
    (d : ChartPDEData (I := I) p) {V f : M → ℝ} (hV : Continuous V) (hf : Continuous f)
    {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) +
        ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M =
      ∫ x, f x * φ x ∂riemannianVolume I M) (v : W1p0 volume d.Ω 2) :
    PDE.energyFormH1 (chartMatrix (I := I) p) 0 (chartWeighted (I := I) p V) (d.T w)
        (v : W1p volume d.Ω 2) =
      ∫ y in (d.Ω : Set _), chartWeighted (I := I) p f y * W1p.value (v : W1p volume d.Ω 2) y := by
  -- With the mass `ρ (V ∘ ψ)` added, the coefficients of the energy form are still bounded.
  obtain ⟨C, hC⟩ := d.exists_norm_chartWeighted_le hV
  have hcoeff : MemLp (fun y ↦ PDE.energyIntegrand (chartMatrix (I := I) p y) 0
      (chartWeighted (I := I) p V y)) ⊤ (volume.restrict (d.Ω : Set _)) :=
    PDE.memLp_energyIntegrand_of_bounds (b := 0) (beta := 0) d.hell.upper_nonneg d.ha_meas
      aestronglyMeasurable_const (d.memLp_top_chartWeighted hV).aestronglyMeasurable
      (fun _ hy η ξ ↦ d.hell.upper_bound hy η ξ) (fun _ _ ↦ by simp) hC
  have hF : MemLp (chartWeighted (I := I) p f) 2 (volume.restrict (d.Ω : Set _)) :=
    d.hF_memLp2 hf
  have hcongr (g : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ) :
      ∫ y in (d.Ω : Set _), hF.toLp _ y * g y =
        ∫ y in (d.Ω : Set _), chartWeighted (I := I) p f y * g y :=
    integral_congr_ae (hF.coeFn_toLp.mono fun y hy ↦ congrArg (· * g y) hy)
  rw [← hcongr]
  exact (PDE.forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff _ (d.T w)).2
    (fun φ ↦ (d.energyFormH1_ofTestFunctionₗ_eq_of_dirichletForm_add_eq hV hw φ).trans
      (hcongr φ).symm) v

omit [I.Boundaryless] [T2Space M] in
/-- **Smoothness in a chart for `Δ⁺ + V`.** If `w ∈ H¹(M)` weakly solves `Δ⁺w + V w = f` with
smooth `V` and `f`, then its reading in the coordinates of the chart data `d` agrees almost
everywhere with a function smooth on the coordinate domain. -/
private theorem ChartPDEData.exists_contDiffOn_ae_eq_of_dirichletForm_add_eq {p : M}
    (d : ChartPDEData (I := I) p) {V f : M → ℝ} (hV : ContMDiff I 𝓘(ℝ) ∞ V)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) +
        ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M =
      ∫ x, f x * φ x ∂riemannianVolume I M) :
    ∃ g : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ, ContDiffOn ℝ ∞ g d.Ω ∧
      (fun y ↦ toLp w (chartInvMap (I := I) p y)) =ᵐ[volume.restrict (d.Ω : Set _)] g := by
  have hψ := contMDiffOn_chartInvMap p d.hΩt
  have hρ := contDiffOn_chartVolumeDensity_chartInvMap p d.hΩt
  have hc : ContDiffOn ℝ ∞ (chartWeighted (I := I) p V) d.Ω :=
    hρ.mul (hV.comp_contMDiffOn hψ).contDiffOn
  -- The forcing `ρ (f ∘ ψ)` lies in every `W^{k,2}` near each point of the coordinate domain.
  have hF : ContDiffOn ℝ ∞ (chartWeighted (I := I) p f) d.Ω :=
    hρ.mul (hf.comp_contMDiffOn hψ).contDiffOn
  have hFk : ∀ x ∈ d.Ω, ∃ U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))), x ∈ U ∧
      ∀ k, ∃ Fk : Wkp volume U 2 k,
        (Wkp.value k Fk : _ → ℝ) =ᵐ[volume.restrict (U : Set _)] chartWeighted (I := I) p f :=
    fun x hx ↦ by
      obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (d.Ω.isOpen.mem_nhds hx)
      exact ⟨⟨ball x r, isOpen_ball⟩, mem_ball_self hr, fun k ↦
        Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact k d.Ω.isOpen
          (hF.of_le (by exact_mod_cast le_top)) (isCompact_closedBall x r) ball_subset_closedBall
          hrΩ⟩
  obtain ⟨g, hg, hug⟩ := d.hell.exists_contDiffOn_ae_eq_of_contDiffOn
    (contDiffOn_chartMatrix p d.hΩt) contDiffOn_const hc hFk
    (d.energyFormH1_eq_setIntegral_of_dirichletForm_add_eq hV.continuous hf.continuous hw)
  exact ⟨g, hg, (d.hTv w).symm.trans hug⟩

/-- **Weak solutions of `Δ⁺w + V w = f` are smooth.** Let `M` be a closed smooth Riemannian
manifold, of any dimension, and let the potential `V` and the forcing `f` be smooth on `M`. If
`w ∈ H¹(M)` solves `D(w, φ) + ∫ V w φ dV = ∫ f φ dV` against every smooth function `φ`, then `w`
is a smooth function `u`, and `-laplaceBeltrami I u x + V x * u x = f x` holds everywhere on `M`. -/
theorem exists_eq_ofSmooth_and_neg_laplaceBeltrami_add_mul_eq_of_dirichletForm_add_eq
    {V f : M → ℝ} (hV : ContMDiff I 𝓘(ℝ) ∞ V) (hf : ContMDiff I 𝓘(ℝ) ∞ f) {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) +
        ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M =
      ∫ x, f x * φ x ∂riemannianVolume I M) :
    ∃ u : C^∞⟮I, M; ℝ⟯, w = ofSmooth u ∧ ∀ x, -laplaceBeltrami I u x + V x * u x = f x := by
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  -- Glue the smooth representatives found in charts.
  obtain ⟨u, hu, hwu⟩ := exists_contMDiff_ae_eq_of_locally (I := I) (I' := 𝓘(ℝ)) (n := ∞)
    (μ := riemannianVolume I M) (u := (toLp w : M → ℝ)) fun p ↦ by
      obtain ⟨d⟩ := nonempty_chartPDEData (I := I) p
      obtain ⟨g, hg, hwg⟩ := d.exists_contDiffOn_ae_eq_of_dirichletForm_add_eq hV hf hw
      refine ⟨_, (isOpen_chartNbhd p d.Ω).mem_nhds (mem_chartNbhd_self p d.hpΩ),
        fun x ↦ g (coordEquiv E (extChartAt I p x)), contMDiffOn_comp_coordEquiv_extChartAt p hg,
        (ae_eq_restrict_chart_iff p d.hΩt).2 ?_⟩
      filter_upwards [ae_restrict_mem d.Ω.isOpen.measurableSet, hwg] with y hy hgy
      dsimp only [chartInvMap] at hgy ⊢
      rw [(extChartAt I p).right_inv (d.hΩt hy), (coordEquiv E).apply_symm_apply]
      exact hgy
  let u' : C^∞⟮I, M; ℝ⟯ := ⟨u, hu⟩
  -- With `w = u`, the potential term moves to the forcing `f - V u`, which is continuous.
  have hw' : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) =
      ∫ x, (f x - V x * u' x) * φ x ∂riemannianVolume I M := fun φ ↦ by
    have hVu : ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M =
        ∫ x, V x * u' x * φ x ∂riemannianVolume I M :=
      integral_congr_ae (hwu.mono fun x hx ↦ by simp only [u', ContMDiffMap.coeFn_mk, hx])
    have hfφ : Integrable (fun x ↦ f x * φ x) (riemannianVolume I M) :=
      (hf.continuous.mul (map_continuous φ)).integrable_of_compactSpace
    have hVuφ : Integrable (fun x ↦ V x * u' x * φ x) (riemannianVolume I M) :=
      ((hV.continuous.mul (map_continuous u')).mul (map_continuous φ)).integrable_of_compactSpace
    rw [eq_sub_of_add_eq (hw φ), hVu, ← integral_sub hfφ hVuφ]
    simp_rw [sub_mul]
  obtain ⟨hwu', hΔ⟩ := eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq (u := u')
    (hf.continuous.sub (hV.continuous.mul (map_continuous u'))) hwu hw'
  refine ⟨u', hwu', fun x ↦ ?_⟩
  have h := hΔ x
  simp only [Pi.sub_apply, Pi.mul_apply] at h
  linarith

/-- **Eigenfunctions of `Δ⁺` are smooth.** Let `M` be a closed smooth Riemannian manifold, of any
dimension. If `w ∈ H¹(M)` solves `D(w, φ) = μ ∫ w φ dV` against every smooth function `φ`, for
instance if `D(w, v) = μ ⟪w, v⟫_{L²}` for every `v ∈ H¹(M)`, then `w` is a smooth function `u`
with `-laplaceBeltrami I u = μ u` everywhere on `M`. -/
theorem exists_eq_ofSmooth_and_neg_laplaceBeltrami_eq_mul_of_dirichletForm_eq_mul
    {μ : ℝ} {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth φ) = μ * ∫ x, toLp w x * φ x ∂riemannianVolume I M) :
    ∃ u : C^∞⟮I, M; ℝ⟯, w = ofSmooth u ∧ ∀ x, -laplaceBeltrami I u x = μ * u x := by
  obtain ⟨u, hwu, hΔ⟩ :=
    exists_eq_ofSmooth_and_neg_laplaceBeltrami_add_mul_eq_of_dirichletForm_add_eq
      (V := fun _ ↦ -μ) (f := 0) contMDiff_const contMDiff_const fun φ ↦ by
        rw [hw φ]
        simp only [Pi.zero_apply, zero_mul, integral_zero, neg_mul, mul_assoc, integral_neg,
          integral_const_mul, add_neg_cancel]
  refine ⟨u, hwu, fun x ↦ ?_⟩
  have h := hΔ x
  simp only [Pi.zero_apply] at h
  linarith

/-- **The smooth Poisson equation on a closed manifold.** On a closed connected manifold of any
dimension with a smooth Riemannian metric, every smooth function `f` of integral zero is `Δ⁺u` for
a smooth function `u` of integral zero. -/
theorem exists_neg_laplaceBeltrami_eq [PreconnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃ u : C^∞⟮I, M; ℝ⟯, ∫ x, u x ∂riemannianVolume I M = 0 ∧
      ∀ x, -laplaceBeltrami I u x = f x := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hf2 : MemLp f 2 (riemannianVolume I M) :=
    hf.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨w, hw₀, hw⟩ := (existsUnique_dirichletForm_eq (hf2.toLp f)
    ((integral_congr_ae hf2.coeFn_toLp).trans hf₀)).exists
  obtain ⟨u, rfl, hu⟩ :=
    exists_eq_ofSmooth_and_neg_laplaceBeltrami_add_mul_eq_of_dirichletForm_add_eq (V := 0)
      contMDiff_const hf (w := w) fun φ ↦ by
        rw [hw, integral_congr_ae ((hf2.coeFn_toLp.mul (toLp_ofSmooth_ae_eq φ)).mono
          fun x hx ↦ by simpa only [Pi.mul_apply] using hx)]
        simp
  exact ⟨u, (integral_congr_ae (toLp_ofSmooth_ae_eq u)).symm.trans hw₀,
    fun x ↦ by simpa using hu x⟩

end SmoothRegularity

end SobolevH1

end TauCeti.Manifold
