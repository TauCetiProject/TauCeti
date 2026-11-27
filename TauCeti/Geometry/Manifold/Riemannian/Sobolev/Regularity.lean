/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.PDE.Ellipticity.PosDef
import TauCeti.Analysis.PDE.EnergyForm.WeakDivergence
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.PDE.Regularity.Semilinear
import TauCeti.Analysis.PDE.Regularity.Smooth
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Linear
import TauCeti.Analysis.Sobolev.Wkp.ClosedGraph
import TauCeti.Geometry.Manifold.ContMDiff.LocalRepresentative
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.ChartCutoff
import TauCeti.Geometry.Manifold.Riemannian.Poisson
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Chart
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame
import TauCeti.MeasureTheory.Function.Lp.Norm
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
* **Interior `H²` regularity**
  (`TauCeti.Manifold.SobolevH1.exists_wkp_ae_eq_of_dirichletForm_add_eq`): for a smooth metric,
  a continuous potential `V` and a forcing `f ∈ L²(M)`, every weak solution `w ∈ H¹(M)` of
  `Δ⁺w + V w = f` has square-integrable second weak derivatives near every point: near each chart
  point its reading in coordinates lies in `W^{2,2}`. In coordinates the coefficient `a` is
  smooth, so Euclidean interior `H²` regularity
  (`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiffOn`) applies to the
  forcing `√(det g) (f ∘ ψ)`, which is square integrable because the density is bounded above and
  below on a coordinate ball. In particular the domain of the Laplacian on `L²(M)` lies in `H²` in
  this sense (`TauCeti.Manifold.SobolevH1.exists_wkp_ae_eq_of_mem_domain_negLaplacian`). The
  corresponding estimate `‖w‖_{W^{2,2}} ≤ C (‖f‖_{L²(M)} + ‖w‖_{H¹(M)})` near each point, with `C`
  independent of `w` and `f`
  (`TauCeti.Manifold.SobolevH1.exists_norm_wkp_le_of_dirichletForm_add_eq`), follows by the closed
  graph theorem: the solution-forcing pairs form a closed subspace of
  `H¹(M) × L²(M)`, and regularity factors the chart reading through `W^{2,2}`.
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
* `SobolevH1.exists_eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq_semilinear`:
  a semilinear weak solution in dimension at most three with `L²` forcing is a smooth classical
  solution.
* `TauCeti.Manifold.SobolevH1.exists_wkp_ae_eq_of_dirichletForm_add_eq`: a weak solution of
  `Δ⁺w + V w = f` with continuous `V` and `f ∈ L²(M)` lies in `W^{2,2}` in charts near every point.
* `TauCeti.Manifold.SobolevH1.exists_norm_wkp_le_of_dirichletForm_add_eq`: the interior `H²`
  estimate `‖w‖_{W^{2,2}} ≤ C (‖f‖_{L²(M)} + ‖w‖_{H¹(M)})` in charts near every point.
* `TauCeti.Manifold.SobolevH1.exists_mem_nhds_abs_dirichletForm_le_of_wkp_ae_eq`: near a point
  where `w ∈ H¹(M)` is `W^{2,2}` in a chart, `|D(w, Φ)| ≤ C ‖Φ‖_{L²(M)}` for `Φ` supported nearby.
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

/-- A smooth function supported in `chartNbhd p U` is read in coordinates as a test function. -/
private theorem exists_testFunction_eq_chartInvMap [CompactSpace M] [IsManifold I ∞ M]
    (p : M) {U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hUt : MapsTo (coordEquiv E).symm U (extChartAt I p).target) (Φ : C^∞⟮I, M; ℝ⟯)
    (hΦ : tsupport (Φ : M → ℝ) ⊆ chartNbhd (I := I) p U) :
    ∃ φ : 𝓓(U, ℝ), ∀ y ∈ U, φ y = Φ (chartInvMap (I := I) p y) := by
  set G : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ :=
    (U : Set _).indicator fun y ↦ Φ (chartInvMap (I := I) p y) with hG
  have hK₀ : IsCompact (coordEquiv E '' (extChartAt I p '' tsupport (Φ : M → ℝ))) :=
    ((isClosed_tsupport _).isCompact.image_of_continuousOn ((continuousOn_extChartAt p).mono
      fun x hx ↦ (hΦ hx).1)).image (coordEquiv E).continuous
  have hK₀U : coordEquiv E '' (extChartAt I p '' tsupport (Φ : M → ℝ)) ⊆ U := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨-, y, hy, hyx⟩ := hΦ hx
    rwa [← hyx, (coordEquiv E).apply_symm_apply]
  have hGs : tsupport G ⊆ coordEquiv E '' (extChartAt I p '' tsupport (Φ : M → ℝ)) := by
    refine closure_minimal (fun y hy ↦ ?_) hK₀.isClosed
    have hyU : y ∈ U := by_contra fun h ↦ hy (indicator_of_notMem h _)
    refine ⟨_, ⟨chartInvMap (I := I) p y, subset_tsupport _ fun h ↦ hy ?_, rfl⟩, ?_⟩
    · rw [hG, indicator_of_mem hyU]
      exact h
    · rw [chartInvMap, (extChartAt I p).right_inv (hUt hyU), (coordEquiv E).apply_symm_apply]
  have hGc : ContDiff ℝ ∞ G := by
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_of_tsupport fun y hy ↦ ?_
    have hyU := hK₀U (hGs hy)
    exact (Φ.contMDiff.contMDiffAt.comp y ((contMDiffOn_chartInvMap p hUt).contMDiffAt
      (U.isOpen.mem_nhds hyU))).congr_of_eventuallyEq
        (eventually_of_mem (U.isOpen.mem_nhds hyU) fun z hz ↦ indicator_of_mem hz _)
  exact ⟨⟨G, hGc, hK₀.of_isClosed_subset (isClosed_tsupport G) hGs, hGs.trans hK₀U⟩,
    fun y hy ↦ by simp [hG, hy]⟩

/-- In the basis-adapted coordinates `coordEquiv E ∘ extChartAt I p`, the Euclidean gradient of
`u ∘ chartInvMap p` has components equal to the derivatives of `u` along `chartLocalFrame`. -/
private theorem gradient_comp_coordEquiv_apply [I.Boundaryless] [IsManifold I ∞ M] (p : M)
    {u : M → ℝ} {y : EuclideanSpace ℝ (Fin (finrank ℝ E))}
    (hy : (coordEquiv E).symm y ∈ (extChartAt I p).target)
    (_hu : MDifferentiableAt I 𝓘(ℝ) u (chartInvMap (I := I) p y))
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
    ContinuousLinearEquiv.coe_coe, coordEquiv_symm_single, ← hz_eq, chartLocalFrame_def,
    (Module.finBasis ℝ E).mvfderiv_localFrame_trivializationAt_eq_fderivWithin p
      hx_src u k, I.range_eq_univ, fderivWithin_univ]

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

/-- If the chart density is at least `m > 0` on `Ω`, precomposition with `chartInvMap p` multiplies
`Lʳ` norms by at most `m^(-1/r)`: `‖f ∘ chartInvMap p‖_{Lʳ(Ω)} ≤ m^(-1/r) ‖f‖_{Lʳ(M)}`. -/
private theorem eLpNorm_comp_chartInvMap_le (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target)
    {m : ℝ} (hm : 0 < m)
    (hρ : ∀ y ∈ Ω, m ≤ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y))
    (r : ℝ≥0∞) (f : M → ℝ) :
    eLpNorm (fun y ↦ f (chartInvMap (I := I) p y)) r (volume.restrict (Ω : Set _)) ≤
      ENNReal.ofReal m⁻¹ ^ (1 / r).toReal * eLpNorm f r (riemannianVolume I M) := by
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
  have hψf : f ∘ ψ =ᵐ[volume.restrict (Ω : Set _)] fun y ↦ f (chartInvMap (I := I) p y) := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
    have hmemE : (coordEquiv E).symm y ∈ ΩE := ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, ψ, ψ₀, chartInvMap, piecewise_eq_of_mem _ _ _ hmemE]
  rw [← eLpNorm_congr_ae hψf]
  exact eLpNorm_comp_le_of_map_le_smul hψm.aemeasurable hmap r

/-- Precomposition with `chartInvMap p` maps `Lʳ(M)` into `Lʳ(Ω)` whenever the chart density is
bounded below on `Ω`. -/
private theorem memLp_comp_coordEquiv_of_memLp (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target)
    {m : ℝ} (hm : 0 < m)
    (hρ : ∀ y ∈ Ω, m ≤ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y))
    {r : ℝ≥0∞} {f : M → ℝ} (hf : MemLp f r (riemannianVolume I M)) :
    MemLp (fun y ↦ f (chartInvMap (I := I) p y)) r (volume.restrict (Ω : Set _)) :=
  memLp_iff.2 ((eLpNorm_comp_chartInvMap_le p hΩt hm hρ r f).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
      ENNReal.ofReal_ne_top) (memLp_iff.1 hf)))

/-- `eLpNorm_comp_chartInvMap_le` for `L²` classes `v`, `F` of `f ∘ chartInvMap p` and `f`. -/
private theorem norm_le_sqrt_inv_mul_of_ae_eq_comp_chartInvMap (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target) {m : ℝ} (hm : 0 < m)
    (hρ : ∀ y ∈ Ω, m ≤ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y)) {f : M → ℝ}
    {v : Lp ℝ 2 (volume.restrict (Ω : Set _))} {F : Lp ℝ 2 (riemannianVolume I M)}
    (hv : v =ᵐ[volume.restrict (Ω : Set _)] fun y ↦ f (chartInvMap (I := I) p y))
    (hF : F =ᵐ[riemannianVolume I M] f) : ‖v‖ ≤ √m⁻¹ * ‖F‖ := by
  have h := eLpNorm_comp_chartInvMap_le p hΩt hm hρ 2 f
  rw [← eLpNorm_congr_ae hv, ← eLpNorm_congr_ae hF] at h
  simpa [Lp.norm_def, ← ENNReal.toReal_rpow, hm.le, Real.sqrt_eq_rpow] using
    ENNReal.toReal_mono (by finiteness) h

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
  have hφΩ : tsupport (φ : _ → ℝ) ⊆ (Ω : Set _) := φ.tsupport_subset
  obtain ⟨Φ₀, hΦ₀, -, hΦ₀supp, hΦ₀eq⟩ :=
    exists_contMDiff_comp_extChartAt_symm_comp_symm_eq (I := I) (n := ∞) (c := p) (coordEquiv E)
      φ.contDiff φ.hasCompactSupport fun y hy ↦ hΩt (hφΩ hy)
  let Φ : C^∞⟮I, M; ℝ⟯ := ⟨Φ₀, hΦ₀⟩
  have hΦ_coe (x : M) : Φ x = Φ₀ x := congrFun (ContMDiffMap.coeFn_mk Φ₀ hΦ₀) x
  have hΦ_ψ (y : EuclideanSpace ℝ (Fin (finrank ℝ E))) (hy : y ∈ Ω) :
      Φ (chartInvMap (I := I) p y) = φ y := by
    rw [hΦ_coe, chartInvMap, hΦ₀eq _ (hΩt hy)]
  have hΦ_U : tsupport (Φ : M → ℝ) ⊆ chartNbhd (I := I) p Ω := by
    refine hΦ₀supp.trans ?_
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
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
  T : SobolevH1 I M →L[ℝ] W1p volume Ω 2
  hTv : ∀ w : SobolevH1 I M,
    W1p.value (T w) =ᵐ[volume.restrict (Ω : Set _)]
      fun y ↦ toLp w (chartInvMap (I := I) p y)
  hTg : ∀ u : C^∞⟮I, M; ℝ⟯, W1p.gradient (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set _)]
    ∇ (fun y ↦ u (chartInvMap (I := I) p y))
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
  have hTg : ∀ u : C^∞⟮I, M; ℝ⟯, W1p.gradient ((W1p.restrictL hΩΩ₀).comp T₀ (ofSmooth u))
      =ᵐ[volume.restrict (Ω : Set _)] ∇ (fun y ↦ u (chartInvMap (I := I) p y)) := fun u ↦
    (W1p.gradient_restrictL_ae hΩΩ₀ (T₀ (ofSmooth u))).trans
      (ae_restrict_of_ae_restrict_of_subset hΩΩ₀ (hT₀s u).2)
  -- The coefficients of the energy form are bounded.
  have hcoeff : MemLp (fun y ↦ PDE.energyIntegrand (chartMatrix (I := I) p y) 0 0) ⊤
      (volume.restrict (Ω : Set _)) :=
    PDE.memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
      hell.upper_nonneg ha_meas aestronglyMeasurable_const aestronglyMeasurable_const
      (fun _ hy η ξ ↦ hell.upper_bound hy η ξ) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
  refine ⟨⟨Ω, mem_ball_self hδ, hΩt, hρ_contK.mono hΩK, _, hm_pos, fun y hy ↦ hρ_min (hΩK hy),
    _, fun y hy ↦ hρ_max (hΩK hy), lam, Lam, hell, ha_meas, hcoeff,
    (W1p.restrictL hΩΩ₀).comp T₀,
    fun w ↦ (W1p.value_restrictL_ae hΩΩ₀ (T₀ w)).trans
      (ae_restrict_of_ae_restrict_of_subset hΩΩ₀ (hT₀v w)), hTg,
    exists_contMDiff_of_testFunction p hΩt hcoeff ((W1p.restrictL hΩΩ₀).comp T₀) hTg⟩⟩

end ChartBridge

end CoordinatePDE

section DeGiorgi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The reading `ρ (g ∘ ψ)` in the coordinates at `p` of a function `g` on `M`, weighted by the
chart volume density `ρ`, where `ψ` is the inverse chart. Integrals against the Riemannian volume
become Lebesgue integrals of such readings. -/
private def chartWeighted (p : M) (g : M → ℝ) (y : EuclideanSpace ℝ (Fin (finrank ℝ E))) : ℝ :=
  chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) * g (chartInvMap (I := I) p y)

omit [I.Boundaryless] [T2Space M] in
/-- The coordinate reading `ρ (f ∘ ψ)` of a function `f ∈ Lʳ(M)` lies in `Lʳ` of the coordinate
domain of the chart data `d`, since the chart density is bounded above and below there. -/
private theorem ChartPDEData.memLp_chartWeighted {p : M} (d : ChartPDEData (I := I) p)
    {r : ℝ≥0∞} {f : M → ℝ} (hf : MemLp f r (riemannianVolume I M)) :
    MemLp (chartWeighted (I := I) p f) r (volume.restrict (d.Ω : Set _)) := by
  have hf_coord := memLp_comp_coordEquiv_of_memLp p d.hΩt d.hm d.hρ_min hf
  exact hf_coord.of_le_mul
    ((d.hρ_cont.aestronglyMeasurable d.Ω.isOpen.measurableSet).mul
      hf_coord.aestronglyMeasurable)
    ((ae_restrict_mem d.Ω.isOpen.measurableSet).mono fun y hy ↦ by
      rw [chartWeighted, norm_mul]
      exact mul_le_mul_of_nonneg_right (d.hρ_max y hy) (norm_nonneg _))

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
  have hF_memLp := d.memLp_chartWeighted hf
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
  have hw_eq : w = ofSmooth u := toLp_ae_eq_iff_eq_ofSmooth.1 hwu
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
    (d.memLp_chartWeighted (hRHS_cont.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).ae_eq (Filter.Eventually.of_forall hF_eq)
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

/-- Shared semilinear smooth bootstrap returning the `ContMDiff` proof together with
`w = ofSmooth ⟨u, hu⟩` and the pointwise equation. -/
private theorem contMDiff_and_eq_ofSmooth_of_dirichletForm_eq_semilinear (hE : finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M} {u : M → ℝ}
    (hu_cont : Continuous u) (hwu : toLp w =ᵐ[riemannianVolume I M] u)
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) =
      ∫ x, (A x * Φ (u x) + C x) * φ x ∂riemannianVolume I M) :
    ∃ hu : ContMDiff I 𝓘(ℝ) ∞ u,
      w = ofSmooth ⟨u, hu⟩ ∧ ∀ x, -laplaceBeltrami I u x = A x * Φ (u x) + C x := by
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
  have hcl := eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq (u := ⟨u, hu_smooth⟩)
    ((hA.continuous.mul (hΦ.continuous.comp hu_cont)).add hC.continuous) hwu hw
  exact ⟨hu_smooth, hcl.1, hcl.2⟩

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
    ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ x, -laplaceBeltrami I u x = A x * Φ (u x) + C x :=
  let ⟨hu, _, hΔ⟩ :=
    contMDiff_and_eq_ofSmooth_of_dirichletForm_eq_semilinear hE hA hC hΦ hu_cont hwu hw
  ⟨hu, hΔ⟩

/-- **Semilinear weak solutions in dimension `< 4` are smooth.** Let `M` be a closed smooth
Riemannian manifold of dimension `< 4`, let `A, C : M → ℝ` and `Φ : ℝ → ℝ` be smooth, and let
`w ∈ H¹(M)` satisfy `D(w, ψ) = ∫ (A Φ(w) + C) ψ dV` for every smooth function `ψ`, with
`A Φ(w) + C ∈ L²(M)`. Then `w` is a smooth function `u` solving `-laplaceBeltrami I u x =
A x * Φ (u x) + C x` everywhere on `M`. -/
theorem exists_eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq_semilinear
    (hE : finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M}
    (hf : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ ψ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth ψ) =
        ∫ x, (A x * Φ (toLp w x) + C x) * ψ x ∂riemannianVolume I M) :
    ∃ u : C^∞⟮I, M; ℝ⟯,
      w = ofSmooth u ∧ ∀ x, -laplaceBeltrami I u x = A x * Φ (u x) + C x := by
  have hE2 : (finrank ℝ E : ℝ) < 2 * ((2 : ℝ≥0) : ℝ) := by
    exact_mod_cast (by omega : finrank ℝ E < 2 * 2)
  obtain ⟨u, hu_cont, hwu⟩ :=
    exists_continuous_ae_eq_of_dirichletForm_eq (r := 2) le_rfl hE2 hf hw
  have hw' : ∀ ψ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth ψ) =
        ∫ x, (A x * Φ (u x) + C x) * ψ x ∂riemannianVolume I M := fun ψ ↦ by
    rw [hw ψ]
    refine integral_congr_ae ?_
    filter_upwards [hwu] with x hx
    rw [hx]
  obtain ⟨hu_sm, hwu', hΔ⟩ :=
    contMDiff_and_eq_ofSmooth_of_dirichletForm_eq_semilinear hE hA hC hΦ hu_cont hwu hw'
  exact ⟨⟨u, hu_sm⟩, hwu', hΔ⟩

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
`d`, a weak solution `w ∈ H¹(M)` of `Δ⁺w + V w = f` with continuous `V` and `f ∈ L²(M)` weakly
solves `-div(a ∇(w ∘ ψ)) + ρ (V ∘ ψ) (w ∘ ψ) = ρ (f ∘ ψ)` against all of `H¹₀`. -/
private theorem ChartPDEData.energyFormH1_eq_setIntegral_of_dirichletForm_add_eq {p : M}
    (d : ChartPDEData (I := I) p) {V f : M → ℝ} (hV : Continuous V)
    (hf : MemLp f 2 (riemannianVolume I M)) {w : SobolevH1 I M}
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
    d.memLp_chartWeighted hf
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
    (d.energyFormH1_eq_setIntegral_of_dirichletForm_add_eq hV.continuous
      (hf.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hw)
  exact ⟨g, hg, (d.hTv w).symm.trans hug⟩

omit [I.Boundaryless] [T2Space M] in
/-- On an open set `U` inside the coordinate domain of the chart data `d`, the value of the
restricted chart reading `T w` is the reading `w ∘ ψ` of `w` in coordinates. -/
private theorem ChartPDEData.value_restrictL_T_ae {p : M} (d : ChartPDEData (I := I) p)
    {U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))} (hUΩ : U ≤ d.Ω) (w : SobolevH1 I M) :
    W1p.value (W1p.restrictL hUΩ (d.T w)) =ᵐ[volume.restrict (U : Set _)]
      fun y ↦ toLp w (chartInvMap (I := I) p y) :=
  (W1p.value_restrictL_ae hUΩ (d.T w)).trans (ae_restrict_of_ae_restrict_of_subset hUΩ (d.hTv w))

omit [I.Boundaryless] [T2Space M] in
/-- **`H²` in a chart for `Δ⁺ + V`.** If `w ∈ H¹(M)` weakly solves `Δ⁺w + V w = f` with continuous
`V` and `f ∈ L²(M)`, then on every open set `U` whose closure is compact and contained in the
coordinate domain of the chart data `d`, the reading of `w` in coordinates is the value of an
element of `W^{2,2}(U)`. -/
private theorem ChartPDEData.exists_wkp_ae_eq_of_dirichletForm_add_eq {p : M}
    (d : ChartPDEData (I := I) p) {V f : M → ℝ} (hV : Continuous V)
    (hf : MemLp f 2 (riemannianVolume I M)) {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) +
        ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M =
      ∫ x, f x * φ x ∂riemannianVolume I M)
    {U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hU : IsCompact (closure (U : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))))
    (hUΩ : closure (U : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ⊆ d.Ω) :
    ∃ u : Wkp volume U 2 2, (Wkp.value 2 u : _ → ℝ) =ᵐ[volume.restrict (U : Set _)]
      fun y ↦ toLp w (chartInvMap (I := I) p y) := by
  have hF := d.memLp_chartWeighted hf
  -- The mass `ρ (V ∘ ψ)` is continuous and the coefficient matrix smooth on the coordinate
  -- domain, so interior `H²` regularity applies with the forcing `ρ (f ∘ ψ) ∈ L²`.
  have hc : ContDiffOn ℝ 0 (chartWeighted (I := I) p V) d.Ω :=
    contDiffOn_zero.2 (d.hρ_cont.mul
      (hV.comp_continuousOn (contMDiffOn_chartInvMap p d.hΩt).continuousOn))
  obtain ⟨u, hu⟩ := d.hell.exists_value_eq_value_restrictL_of_contDiffOn 0
    (fun i j ↦ (contDiffOn_chartMatrix p d.hΩt i j).of_le (by exact_mod_cast le_top))
    (b := 0) contDiffOn_const hc (F := hF.toLp _) (u := d.T w) (fun v ↦ by
      rw [d.energyFormH1_eq_setIntegral_of_dirichletForm_add_eq hV hf hw v, Wkp.value_zero]
      exact integral_congr_ae (hF.coeFn_toLp.mono fun y hy ↦ by simp only [hy]))
    hU hUΩ
  have hUΩ' : U ≤ d.Ω := SetLike.coe_subset_coe.mp (subset_closure.trans hUΩ)
  -- With `k = 0`, `u` lies in `Wkp volume U 2 (0 + 2)`, which is `Wkp volume U 2 2` because the
  -- literal `0 + 2` reduces to `2` definitionally.
  have hu' : Wkp.value 2 u = W1p.value (W1p.restrictL hUΩ' (d.T w)) := hu
  exact ⟨u, hu' ▸ d.value_restrictL_T_ae hUΩ' w⟩

omit [I.Boundaryless] [T2Space M] in
/-- A ball around the chart point whose closure is compact and contained in the coordinate domain
of the chart data `d`; in particular the ball lies in that domain and is mapped into the chart
target. -/
private theorem ChartPDEData.exists_ball {p : M} (d : ChartPDEData (I := I) p) :
    ∃ U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))), coordEquiv E (extChartAt I p p) ∈ U ∧
      IsCompact (closure (U : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) ∧
      closure (U : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ⊆ d.Ω ∧ U ≤ d.Ω ∧
      MapsTo (coordEquiv E).symm U (extChartAt I p).target := by
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (d.Ω.isOpen.mem_nhds d.hpΩ)
  have hUK : closure (ball (coordEquiv E (extChartAt I p p)) r) ⊆
      closedBall (coordEquiv E (extChartAt I p p)) r :=
    closure_ball_subset_closedBall
  have hUΩ : closure (ball (coordEquiv E (extChartAt I p p)) r) ⊆ d.Ω := hUK.trans hrΩ
  exact ⟨⟨ball _ r, isOpen_ball⟩, mem_ball_self hr,
    (isCompact_closedBall _ r).of_isClosed_subset isClosed_closure hUK, hUΩ,
    SetLike.coe_subset_coe.mp (subset_closure.trans hUΩ),
    d.hΩt.mono_left (subset_closure.trans hUΩ)⟩

omit [T2Space M] in
/-- **The Dirichlet form of a function which is `H²` in a chart.** If the reading of `w ∈ H¹(M)` in
the coordinates of the chart data `d` is the value of an element of `W^{2,2}(U)`, for an open `U`
whose closure is compact and contained in the coordinate domain, then `|D(w, Φ)| ≤ C ‖Φ‖_{L²(M)}`
for every smooth `Φ` supported in the neighbourhood `chartNbhd p U` of `p`: in coordinates `D(w, Φ)`
is the pairing of the reading of `Φ` with `-div(a ∇(w ∘ ψ)) ∈ L²(U)`. -/
private theorem ChartPDEData.exists_abs_dirichletForm_le_of_wkp {p : M}
    (d : ChartPDEData (I := I) p) {U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hU : IsCompact (closure (U : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))))
    (hUΩ : closure (U : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ⊆ d.Ω) {w : SobolevH1 I M}
    {u : Wkp volume U 2 2} (hu : (Wkp.value 2 u : _ → ℝ) =ᵐ[volume.restrict (U : Set _)]
      fun y ↦ toLp w (chartInvMap (I := I) p y)) :
    ∃ C, 0 ≤ C ∧ ∀ Φ : C^∞⟮I, M; ℝ⟯, tsupport (Φ : M → ℝ) ⊆ chartNbhd (I := I) p U →
      |dirichletForm w (ofSmooth Φ)| ≤ C * ‖toLp (ofSmooth Φ)‖ := by
  have hUΩ' : U ≤ d.Ω := SetLike.coe_subset_coe.mp (subset_closure.trans hUΩ)
  have hUt : MapsTo (coordEquiv E).symm U (extChartAt I p).target := d.hΩt.mono_left hUΩ'
  -- The entries of `a = chartMatrix p` and their derivatives are bounded on compact `closure U`.
  have hcd := contDiffOn_chartMatrix p d.hΩt
  choose K hK using fun i j ↦ hU.exists_bound_of_continuousOn (((hcd i j).continuousOn.prodMk
    ((hcd i j).continuousOn_fderiv_of_isOpen d.Ω.isOpen (by simp))).mono hUΩ)
  have hKle (i j) : K i j ≤ ∑ i, ∑ j, |K i j| := (le_abs_self _).trans <| (Finset.single_le_sum
    (fun j _ ↦ abs_nonneg (K i j)) (Finset.mem_univ j)).trans <| Finset.single_le_sum
      (f := fun i ↦ ∑ j, |K i j|) (fun _ _ ↦ by positivity) (Finset.mem_univ _)
  -- So the energy pairing with `w ∘ ψ ∈ H²(U)` is an `L²` pairing.
  obtain ⟨g, hg⟩ := PDE.exists_energyFormH1_eq_setIntegral_of_wkp_two
    (fun i j ↦ ((hcd i j).mono hUΩ').of_le (by exact_mod_cast le_top)) (fun i j y hy ↦
      have h := (hK i j y (subset_closure hy)).trans (hKle i j)
      ⟨(Real.norm_eq_abs _).symm.trans_le (h.trans' (norm_fst_le (_, _))),
        (norm_gradient_eq_norm_fderiv _ _).trans_le
        (h.trans' (norm_snd_le (chartMatrix (I := I) p y i j, _)))⟩)
    u
  rw [Wkp.value_succ, Wkp.value_one] at hu
  have hTu : W1p.restrictL hUΩ' (d.T w) = Wkp.lowerOrder 1 u :=
    W1p.ext_value (Lp.ext ((d.value_restrictL_T_ae hUΩ' w).trans hu.symm))
  refine ⟨‖g‖ * √d.m⁻¹, by positivity, fun Φ hΦ ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := exists_testFunction_eq_chartInvMap p hUt Φ hΦ
  have hD := dirichletForm_eq_energyFormH1_of_eq p hUt
    (d.hcoeff.mono_measure (Measure.restrict_mono hUΩ' le_rfl))
    ((W1p.restrictL hUΩ').comp d.T) (fun u ↦ (W1p.gradient_restrictL_ae hUΩ' _).trans
      (ae_restrict_of_ae_restrict_of_subset hUΩ' (d.hTg u))) φ Φ
    (fun y hy ↦ (hφ y hy).symm) hΦ w
  rw [ContinuousLinearMap.comp_apply, hTu,
    hg ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩] at hD
  set v := W1p.value (W1p.ofTestFunctionₗ volume U 2 φ)
  have hinner : ∫ y in (U : Set _), g y * v y = ⟪g, v⟫_ℝ := by simp [L2.inner_def, mul_comm]
  rw [hD, hinner, mul_assoc]
  refine (abs_real_inner_le_norm g v).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg g))
  -- `‖φ‖_{L²(U)} ≤ m^(-1/2) ‖Φ‖_{L²(M)}`, as the chart density is at least `m`.
  refine norm_le_sqrt_inv_mul_of_ae_eq_comp_chartInvMap p hUt d.hm
    (fun y hy ↦ d.hρ_min y (hUΩ' hy)) ?_ (toLp_ofSmooth_ae_eq Φ)
  filter_upwards [W1p.value_ofTestFunctionₗ_ae (p := 2) φ,
    ae_restrict_mem U.isOpen.measurableSet] with y hy hyU
  rw [hy, hφ y hyU]

/-- **Interior `H²` regularity on a closed manifold.** Let `M` be a closed smooth Riemannian
manifold, `V` a continuous potential and `f ∈ L²(M)`. If `w ∈ H¹(M)` solves
`D(w, φ) + ∫ V w φ dV = ∫ f φ dV` against every smooth function `φ`, that is `Δ⁺w + V w = f`
weakly, then `w` has square-integrable second weak derivatives near every point of `M`: for every
`p ∈ M` there are a linear identification `L` of the model space with `ℝⁿ`, an open neighbourhood
`Ω` of `L (φ p)` in `ℝⁿ`, where `φ = extChartAt I p`, on which `φ⁻¹ ∘ L⁻¹` is defined, and an
element of `W^{2,2}(Ω)` whose value is `w ∘ φ⁻¹ ∘ L⁻¹` almost everywhere on `Ω`. -/
theorem exists_wkp_ae_eq_of_dirichletForm_add_eq {V f : M → ℝ} (hV : Continuous V)
    (hf : MemLp f 2 (riemannianVolume I M)) {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) +
        ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M =
      ∫ x, f x * φ x ∂riemannianVolume I M) (p : M) :
    ∃ (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))
      (Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))),
      L (extChartAt I p p) ∈ Ω ∧ MapsTo L.symm Ω (extChartAt I p).target ∧
      ∃ u : Wkp volume Ω 2 2, (Wkp.value 2 u : _ → ℝ) =ᵐ[volume.restrict (Ω : Set _)]
        fun y ↦ toLp w ((extChartAt I p).symm (L.symm y)) := by
  obtain ⟨d⟩ := nonempty_chartPDEData (I := I) p
  obtain ⟨U, hpU, hUc, hUΩ, -, hUt⟩ := d.exists_ball
  obtain ⟨u, hu⟩ := d.exists_wkp_ae_eq_of_dirichletForm_add_eq hV hf hw hUc hUΩ
  exact ⟨coordEquiv E, U, hpU, hUt, u, hu⟩

omit [I.Boundaryless] [T2Space M] in
/-- The pairs `(w, f) ∈ H¹(M) × L²(M)` such that `w` weakly solves `Δ⁺w + V w = f` form a closed
subspace: testing the equation against a smooth `φ` is the vanishing of a continuous linear
functional of `(w, f)`. -/
private theorem exists_isClosed_and_mem_iff_dirichletForm_add_eq {V : M → ℝ}
    (hV : Continuous V) :
    ∃ S : Submodule ℝ (SobolevH1 I M × Lp ℝ 2 (riemannianVolume I M)),
      IsClosed (S : Set (SobolevH1 I M × Lp ℝ 2 (riemannianVolume I M))) ∧
      ∀ q : SobolevH1 I M × Lp ℝ 2 (riemannianVolume I M), q ∈ S ↔
        ∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm q.1 (ofSmooth φ) +
            ∫ x, V x * toLp q.1 x * φ x ∂riemannianVolume I M =
          ∫ x, q.2 x * φ x ∂riemannianVolume I M := by
  have hVφ (φ : C^∞⟮I, M; ℝ⟯) : MemLp (fun x ↦ V x * φ x) 2 (riemannianVolume I M) :=
    (hV.mul (map_continuous φ)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let ℓ (φ : C^∞⟮I, M; ℝ⟯) : (SobolevH1 I M × Lp ℝ 2 (riemannianVolume I M)) →L[ℝ] ℝ :=
    (dirichletForm.flip (ofSmooth φ)).comp (ContinuousLinearMap.fst ℝ _ _) +
      ((innerSL ℝ ((hVφ φ).toLp _)).comp toLp).comp (ContinuousLinearMap.fst ℝ _ _) -
      (innerSL ℝ (toLp (ofSmooth φ))).comp (ContinuousLinearMap.snd ℝ _ _)
  have hℓ (φ : C^∞⟮I, M; ℝ⟯) (q : SobolevH1 I M × Lp ℝ 2 (riemannianVolume I M)) :
      ℓ φ q = dirichletForm q.1 (ofSmooth φ) +
        ∫ x, V x * toLp q.1 x * φ x ∂riemannianVolume I M -
          ∫ x, q.2 x * φ x ∂riemannianVolume I M := by
    simp only [ℓ, sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', innerSL_apply_apply,
      L2.inner_def]
    congr 1
    · congr 1
      refine integral_congr_ae ((hVφ φ).coeFn_toLp.mono fun x hx ↦ ?_)
      simp only [hx, RCLike.inner_apply, conj_trivial]
      ring
    · refine integral_congr_ae ((toLp_ofSmooth_ae_eq φ).mono fun x hx ↦ ?_)
      simp only [hx, RCLike.inner_apply, conj_trivial]
  refine ⟨(ContinuousLinearMap.pi ℓ).ker, ContinuousLinearMap.isClosed_ker _, fun q ↦ ?_⟩
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, funext_iff,
    ContinuousLinearMap.pi_apply, Pi.zero_apply, hℓ, sub_eq_zero]

/-- **The interior `H²` estimate on a closed manifold.** Let `M` be a closed smooth Riemannian
manifold and `V` a continuous potential. Near every point `p ∈ M` the `W^{2,2}` norm of the chart
reading of a weak solution `w ∈ H¹(M)` of `Δ⁺w + V w = f`, `f ∈ L²(M)`, is controlled by the data:
there are a linear identification `L` of the model space with `ℝⁿ`, an open neighbourhood `Ω` of
`L (φ p)` in `ℝⁿ`, where `φ = extChartAt I p`, on which `φ⁻¹ ∘ L⁻¹` is defined, and a constant `C`
such that for every such `w` and `f` the element of `W^{2,2}(Ω)` with value `w ∘ φ⁻¹ ∘ L⁻¹` has
norm at most `C (‖f‖_{L²(M)} + ‖w‖_{H¹(M)})`. -/
theorem exists_norm_wkp_le_of_dirichletForm_add_eq {V : M → ℝ} (hV : Continuous V) (p : M) :
    ∃ (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))
      (Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))),
      L (extChartAt I p p) ∈ Ω ∧ MapsTo L.symm Ω (extChartAt I p).target ∧
      ∃ C, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (riemannianVolume I M)) (w : SobolevH1 I M),
        (∀ φ : C^∞⟮I, M; ℝ⟯, dirichletForm w (ofSmooth φ) +
            ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M =
          ∫ x, f x * φ x ∂riemannianVolume I M) →
        ∃ u : Wkp volume Ω 2 2, (Wkp.value 2 u : _ → ℝ) =ᵐ[volume.restrict (Ω : Set _)]
          (fun y ↦ toLp w ((extChartAt I p).symm (L.symm y))) ∧ ‖u‖ ≤ C * (‖f‖ + ‖w‖) := by
  obtain ⟨d⟩ := nonempty_chartPDEData (I := I) p
  obtain ⟨U, hpU, hUc, hUΩ, hUΩ', hUt⟩ := d.exists_ball
  obtain ⟨S, hS, hmem⟩ := exists_isClosed_and_mem_iff_dirichletForm_add_eq (I := I) hV
  have : CompleteSpace S := hS.completeSpace_coe
  -- The chart reading on `U` factors through `W^{2,2}(U)` by interior regularity, so by the closed
  -- graph theorem the factorization is bounded.
  let F : S →L[ℝ] Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))) :=
    W1p.valueL.comp ((W1p.restrictL hUΩ').comp
      (d.T.comp ((ContinuousLinearMap.fst ℝ _ _).comp S.subtypeL)))
  have hF (q : S) : (F q : _ → ℝ) =ᵐ[volume.restrict (U : Set _)]
      fun y ↦ toLp q.val.1 (chartInvMap (I := I) p y) := by
    simpa [F] using d.value_restrictL_T_ae hUΩ' q.val.1
  obtain ⟨C, hC⟩ := Wkp.exists_norm_le_of_forall_exists_value_ae_eq (k := 2) F fun q ↦
    (d.exists_wkp_ae_eq_of_dirichletForm_add_eq hV (Lp.memLp q.val.2) ((hmem _).1 q.property) hUc
      hUΩ).elim fun u hu ↦ ⟨u, hu.trans (hF q).symm⟩
  refine ⟨coordEquiv E, U, hpU, hUt, max C 0, le_max_right _ _, fun f w hw ↦ ?_⟩
  obtain ⟨u, hu, hCu⟩ := hC ⟨(w, f), (hmem _).2 hw⟩
  refine ⟨u, hu.trans (hF _), hCu.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)))⟩
  rw [← Submodule.norm_coe, Prod.norm_def]
  exact max_le (le_add_of_nonneg_left (norm_nonneg f)) (le_add_of_nonneg_right (norm_nonneg w))

/-- **A function which is `H²` near a point has an `L²`-bounded Dirichlet form there.** Let `M` be
a closed smooth Riemannian manifold, `w ∈ H¹(M)` and `p ∈ M`. Suppose that, for a linear
identification `L` of the model space with `ℝⁿ` and an open neighbourhood `Ω` of `L (φ p)`, where
`φ = extChartAt I p`, the reading `w ∘ φ⁻¹ ∘ L⁻¹` is the value of an element of `W^{2,2}(Ω)`.
Then there are a neighbourhood `N` of `p` and a constant `C` with `|D(w, Φ)| ≤ C ‖Φ‖_{L²(M)}` for
every smooth `Φ` supported in `N`: in coordinates `D(w, Φ)` is the pairing of the reading of `Φ`
with `-div(a ∇(w ∘ φ⁻¹)) ∈ L²`. -/
theorem exists_mem_nhds_abs_dirichletForm_le_of_wkp_ae_eq {w : SobolevH1 I M} {p : M}
    {L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))}
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))} (hpΩ : L (extChartAt I p p) ∈ Ω)
    {u : Wkp volume Ω 2 2} (hu : (Wkp.value 2 u : _ → ℝ) =ᵐ[volume.restrict (Ω : Set _)]
      fun y ↦ toLp w ((extChartAt I p).symm (L.symm y))) :
    ∃ N ∈ 𝓝 p, ∃ C, 0 ≤ C ∧ ∀ Φ : C^∞⟮I, M; ℝ⟯, tsupport (Φ : M → ℝ) ⊆ N →
      |dirichletForm w (ofSmooth Φ)| ≤ C * ‖toLp (ofSmooth Φ)‖ := by
  -- Move the reading to the coordinates `coordEquiv E ∘ φ` of the chart data.
  let e := (coordEquiv E).symm.trans L
  let Ω' : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))) := ⟨e ⁻¹' Ω, Ω.isOpen.preimage e.continuous⟩
  obtain ⟨u', hu', -, -⟩ :=
    Wkp.exists_value_ae_eq_comp_continuousLinearEquiv (U := Ω') ENNReal.ofNat_ne_top e rfl u
  have hu'' : (Wkp.value 2 u' : _ → ℝ) =ᵐ[volume.restrict (Ω' : Set _)]
      fun y ↦ toLp w (chartInvMap (I := I) p y) := by
    filter_upwards [hu', (e.quasiMeasurePreserving_restrict volume
      (fun _ hy ↦ hy : MapsTo e Ω' Ω)).ae hu] with y h₁ h₂
    rw [h₁, h₂]
    simp only [e, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply,
      chartInvMap]
  obtain ⟨d⟩ := nonempty_chartPDEData (I := I) p
  have hp' : coordEquiv E (extChartAt I p p) ∈ d.Ω ⊓ Ω' := ⟨d.hpΩ, by simpa [Ω', e] using hpΩ⟩
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 ((d.Ω ⊓ Ω').isOpen.mem_nhds hp')
  let B : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))) :=
    ⟨ball (coordEquiv E (extChartAt I p p)) r, isOpen_ball⟩
  have hBK : closure (B : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) ⊆
      closedBall (coordEquiv E (extChartAt I p p)) r := closure_ball_subset_closedBall
  have hBΩ' : B ≤ Ω' := fun y hy ↦ (hrΩ (hBK (subset_closure hy))).2
  obtain ⟨C, hC, hCΦ⟩ := d.exists_abs_dirichletForm_le_of_wkp
    ((isCompact_closedBall _ r).of_isClosed_subset isClosed_closure hBK)
    (fun y hy ↦ (hrΩ (hBK hy)).1) ((Wkp.value_restrictL_ae hBΩ' 2 u').trans
      (ae_restrict_of_ae_restrict_of_subset hBΩ' hu''))
  exact ⟨_, (isOpen_chartNbhd p B).mem_nhds (mem_chartNbhd_self p (mem_ball_self hr)), C, hC, hCΦ⟩

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
