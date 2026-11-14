/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.PDE.Ellipticity.PosDef
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.PDE.Regularity.Semilinear
import TauCeti.Analysis.PDE.Regularity.Smooth
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.ChartCutoff
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Chart
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

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
* **Linear `C^∞` regularity** (`TauCeti.Manifold.SobolevH1.exists_contMDiff_of_dirichletForm_eq`):
  when the metric and `f` are smooth, `w` is `ofSmooth u` for a smooth function `u` solving the
  classical equation `Δ⁺u = f` pointwise everywhere on `M`.
* **Semilinear `C^∞` bootstrap**
  (`TauCeti.Manifold.SobolevH1.contMDiff_of_dirichletForm_eq_semilinear`): in dimension at most
  three, if the metric, `A`, `C` on `M`, and `Φ : ℝ → ℝ` are smooth, then any continuous function
  `u` representing a weak solution `w ∈ H¹(M)` of `Δ⁺w = A Φ(u) + C` is smooth on `M` and solves
  `Δ⁺u = A Φ(u) + C` classically everywhere.

Local continuous or smooth representatives constructed in charts are patched together globally via
`TauCeti.Manifold.exists_contMDiff_ae_eq_of_locally`, using the full support of the Riemannian
volume (`TauCeti.isOpenPosMeasure_riemannianVolume`) to make continuous local representatives agree
on chart overlaps.

## Main results

* `TauCeti.Manifold.exists_contMDiff_ae_eq_of_locally`: a function on a Riemannian manifold that
  locally agrees almost everywhere with `C^n` functions agrees almost everywhere with a global
  `C^n` function.
* `TauCeti.Manifold.eq_zero_of_forall_integral_mul_eq_zero`: a continuous function on a closed
  smooth Riemannian manifold orthogonal in `L²(M)` to all smooth functions is identically zero.
* `TauCeti.Manifold.SobolevH1.exists_continuous_ae_eq_of_dirichletForm_eq`: De Giorgi continuity of
  weak solutions of `Δ⁺w = f` for `f ∈ Lʳ(M)`, `r ≥ 2`, `r > dim M / 2`.
* `TauCeti.Manifold.SobolevH1.eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq`: a weak
  solution agreeing a.e. with a smooth function `u` equals `ofSmooth u` and solves `Δ⁺u = f`
  pointwise everywhere.
* `TauCeti.Manifold.SobolevH1.exists_contMDiff_of_dirichletForm_eq`: smoothness and classical
  equation `Δ⁺u = f` for smooth `f` and smooth metric.
* `TauCeti.Manifold.SobolevH1.contMDiff_of_dirichletForm_eq_semilinear`: smoothness and classical
  equation `Δ⁺u = A Φ(u) + C` for continuous weak solutions in dimension at most three.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), §3.7.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., American Mathematical Society (2010),
  §6.3.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), Chapter 8.
-/

public section

open Bundle Filter MeasureTheory Metric Module Riemannian.Tensor Set TauCeti.MeasureTheory
  TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Manifold Matrix NNReal
  Topology

noncomputable section

namespace TauCeti.Manifold

section Gluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Gluing local `C^n` representatives on a Riemannian manifold.** If around every point of `M`
the function `u` agrees `riemannianVolume`-almost everywhere on an open neighbourhood with a `C^n`
function into a Hausdorff space, then `u` agrees `riemannianVolume`-almost everywhere on `M` with a
single globally `C^n` function. Taking `n = 0` gives a global continuous representative, and
taking `n = ∞` gives a global smooth representative. -/
theorem exists_contMDiff_ae_eq_of_locally {n : WithTop ℕ∞}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] {u : M → N}
    (h : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ g : M → N, ContMDiffOn I I' n g U ∧ u =ᵐ[(riemannianVolume I M).restrict U] g) :
    ∃ g : M → N, ContMDiff I I' n g ∧ u =ᵐ[riemannianVolume I M] g := by
  choose U hUo hxU g hgn hug using h
  -- Any two local representatives are continuous and agree a.e. on the open overlap, hence agree
  -- everywhere on the overlap because Riemannian volume charges every nonempty open set.
  have hover (x y : M) : EqOn (g x) (g y) (U x ∩ U y) := by
    have hx_ae : u =ᵐ[(riemannianVolume I M).restrict (U x ∩ U y)] g x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hug x)
    have hy_ae : u =ᵐ[(riemannianVolume I M).restrict (U x ∩ U y)] g y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hug y)
    exact Measure.eqOn_open_of_ae_eq (hx_ae.symm.trans hy_ae) ((hUo x).inter (hUo y))
      ((hgn x).continuousOn.mono inter_subset_left) ((hgn y).continuousOn.mono inter_subset_right)
  let G : M → N := fun y ↦ g y y
  have hGeq (x : M) : EqOn G (g x) (U x) := fun y hy ↦ hover y x ⟨hxU y, hy⟩
  refine ⟨G, fun x ↦ ((hgn x).congr (hGeq x)).contMDiffAt ((hUo x).mem_nhds (hxU x)), ?_⟩
  -- Cover `M` by countably many of the open sets `U x` to upgrade local a.e. agreement to global.
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover U fun x ↦ (hUo x).mem_nhds (hxU x)
  rw [EventuallyEq, ae_iff]
  have hsub : {y : M | u y ≠ G y} ⊆ ⋃ x ∈ t, {y : M | y ∈ U x ∧ u y ≠ g x y} := by
    intro y hy
    obtain ⟨x, hxt, hyU⟩ := mem_iUnion₂.1 (hcover ▸ mem_univ y)
    exact mem_iUnion₂.2 ⟨x, hxt, hyU, by rwa [← hGeq x hyU]⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff ht).2 fun x _ ↦ ?_)
  have hx0 : ((riemannianVolume I M).restrict (U x)) {y : M | u y ≠ g x y} = 0 := ae_iff.1 (hug x)
  rwa [Measure.restrict_apply' (hUo x).measurableSet, inter_comm] at hx0

end Gluing

section ClassicalRecovery

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- A continuous function on a closed smooth Riemannian manifold whose integral against every smooth
function vanishes is identically zero. -/
theorem eq_zero_of_forall_integral_mul_eq_zero [IsManifold I ∞ M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : M → ℝ} (hg : Continuous g)
    (h : ∀ φ : C^∞⟮I, M; ℝ⟯, ∫ x, g x * φ x ∂riemannianVolume I M = 0) :
    g = 0 := by
  have hpos {q : M → ℝ} (hq : Continuous q)
      (hint : ∀ φ : C^∞⟮I, M; ℝ⟯, ∫ x, q x * φ x ∂riemannianVolume I M = 0)
      (p : M) : ¬ 0 < q p := by
    intro hqp
    let U : Set M := {x | 0 < q x}
    have hUo : IsOpen U := isOpen_lt continuous_const hq
    have hsymm : Tendsto (extChartAt I p).symm (𝓝 (extChartAt I p p)) (𝓝 p) := by
      have hc := continuousAt_extChartAt_symm (I := I) p
      rwa [ContinuousAt, extChartAt_to_inv] at hc
    obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.1
      (inter_mem (extChartAt_target_mem_nhds (I := I) p) (hsymm.eventually (hUo.mem_nhds hqp)))
    let b : ContDiffBump (extChartAt I p p) := ⟨R / 4, R / 2, by positivity, by linarith⟩
    have hbK : closedBall (extChartAt I p p) b.rOut ⊆ ball (extChartAt I p p) R :=
      closedBall_subset_ball (by dsimp only [b]; linarith)
    obtain ⟨φ, hφ, -, hφU, hφ0, -, hφeq⟩ :=
      exists_contMDiff_transplant (I := I) (n := ∞) (U := U) p
        (fun y hy ↦ (hball hy).1) (fun y hy ↦ (hball hy).2)
        (isCompact_closedBall _ _) hbK b.contDiff (fun _ ↦ b.nonneg) b.tsupport_eq.subset
    have hnonneg : ∀ x, 0 ≤ q x * φ x := fun x ↦ by
      by_cases hx : x ∈ tsupport φ
      · exact mul_nonneg (le_of_lt (hφU hx)) (hφ0 x)
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    have hcont : Continuous fun x ↦ q x * φ x := hq.mul hφ.continuous
    have hzero := hint ⟨φ, hφ⟩
    have hae := (integral_eq_zero_iff_of_nonneg hnonneg
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hzero
    have hp0 : q p * φ p = 0 := congrFun (Measure.eq_of_ae_eq hae hcont continuous_zero) p
    have hφp : φ p = 1 := by
      have hp' : (extChartAt I p).symm (extChartAt I p p) = p :=
        (extChartAt I p).left_inv (mem_extChartAt_source p)
      rw [← hp', hφeq _ (mem_ball_self hR)]
      exact b.one_of_mem_closedBall (mem_closedBall_self (by dsimp only [b]; positivity))
    rw [hφp, mul_one] at hp0
    linarith
  funext p
  refine le_antisymm (not_lt.1 (hpos hg h p))
    (neg_nonpos.1 (not_lt.1 (hpos hg.neg (fun φ ↦ ?_) p)))
  simp_rw [Pi.neg_apply, neg_mul, integral_neg, h φ, neg_zero]

end ClassicalRecovery

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
  refine ⟨(coordEquiv E).symm.continuous.measurable, ?_⟩
  have hmap : ((EuclideanSpace.basisFun (Fin (finrank ℝ E)) ℝ).toBasis).map
      (coordEquiv E).symm.toLinearEquiv = Module.finBasis ℝ E := by
    ext k
    simpa [EuclideanSpace.basisFun_apply] using coordEquiv_symm_single E k
  rw [← (EuclideanSpace.basisFun (Fin (finrank ℝ E)) ℝ).addHaar_eq_volume,
    Module.Basis.map_addHaar, hmap]

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
    ae_restrict_iff' Ω.isOpen.measurableSet, ae_iff, ae_iff]
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
          rfl
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
  simp [chartMatrix, PDE.matrixBilinearForm_apply, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

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
  have hΦ_coe (x : M) : Φ x = Φ₀ x := rfl
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
  have hψ_cont : ContinuousOn (chartInvMap (I := I) p) K :=
    (continuousOn_extChartAt_symm p).comp (coordEquiv E).symm.continuous.continuousOn hKt
  have hψ_base : MapsTo (chartInvMap (I := I) p) K
      (trivializationAt E (TangentSpace I) p).baseSet := fun y hy ↦ by
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target (hKt hy)
  have : IsManifold I ((0 : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have hρ_contK : ContinuousOn
      (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y)) K :=
    (contMDiffOn_chartVolumeDensity (I := I) (n := 0) p).continuousOn.comp hψ_cont hψ_base
  obtain ⟨y_min, hy_min, hρ_min⟩ := hKcomp.exists_isMinOn hKne hρ_contK
  have hm_pos : 0 < chartVolumeDensity (I := I) p (chartInvMap (I := I) p y_min) :=
    chartVolumeDensity_pos p (hψ_base hy_min)
  obtain ⟨y_max, -, hρ_max⟩ := hKcomp.exists_isMaxOn hKne hρ_contK.norm
  have ha_cont : ContinuousOn (chartMatrix (I := I) p) K := by
    have hG_cont : ContinuousOn
        (fun y ↦ chartInvGramMatrix (I := I) p (chartInvMap (I := I) p y)) K :=
      continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦
        (contMDiffOn_chartInvGramMatrix_entry (I := I) (n := 0) p i j).continuousOn.comp
          hψ_cont hψ_base
    exact hρ_contK.smul hG_cont
  have ha_pos : ∀ y ∈ K, (chartMatrix (I := I) p y).PosDef := fun y hy ↦ by
    rw [chartMatrix, chartInvGramMatrix_def]
    exact (posDef_chartGramMatrix p (hψ_base hy)).inv.smul (chartVolumeDensity_pos p (hψ_base hy))
  obtain ⟨lam, Lam, hell⟩ :=
    PDE.exists_uniformlyEllipticOn_of_subset_isCompact_of_posDef hKcomp hΩK ha_cont ha_pos
  let : PseudoMetrizableSpace (Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin (finrank ℝ E) → Fin (finrank ℝ E) → ℝ))
  have ha_meas : AEStronglyMeasurable (chartMatrix (I := I) p) (volume.restrict (Ω : Set _)) :=
    (ha_cont.mono hΩK).aestronglyMeasurable Ω.isOpen.measurableSet
  have hcoeff : MemLp (fun y ↦ PDE.energyIntegrand (chartMatrix (I := I) p y) 0 0) ⊤
      (volume.restrict (Ω : Set _)) :=
    PDE.memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
      hell.upper_nonneg ha_meas aestronglyMeasurable_const aestronglyMeasurable_const
      (fun _ hy η ξ ↦ hell.upper_bound hy η ξ) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
  have hΩ_fin : IsFiniteMeasure (volume.restrict (ball z₀ δ)) :=
    isFiniteMeasure_restrict.2 (measure_ball_lt_top (μ := volume) (x := z₀) (r := δ)).ne
  have hF_memLp2 : ∀ {f : M → ℝ}, Continuous f →
      MemLp (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
        f (chartInvMap (I := I) p y)) 2 (volume.restrict (Ω : Set _)) := fun {f} hf ↦ by
    have hFc : ContinuousOn
        (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
          f (chartInvMap (I := I) p y)) K :=
      hρ_contK.mul (hf.continuousOn.comp hψ_cont (mapsTo_univ _ _))
    exact (hFc.memLp_top_restrict_of_subset_isCompact hKcomp
      Ω.isOpen.measurableSet hΩK).mono_exponent le_top
  refine ⟨⟨Ω, mem_ball_self hδ, hΩt, hρ_contK.mono hΩK, _, hm_pos, fun y hy ↦ hρ_min (hΩK hy),
    _, fun y hy ↦ hρ_max (hΩK hy), lam, Lam, hell, ha_meas, hcoeff, hF_memLp2,
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
    have : DiscreteTopology M := discreteTopology_iff_isOpen_singleton.2 fun p ↦ by
      have hsrc : (extChartAt I p).source = {p} := by
        ext x
        refine ⟨fun hx ↦ (extChartAt I p).injOn hx (mem_extChartAt_source p)
          (Subsingleton.elim _ _), ?_⟩
        rintro rfl
        exact mem_extChartAt_source _
      exact hsrc ▸ isOpen_extChartAt_source p
    exact ⟨toLp w, continuous_of_discreteTopology, Filter.EventuallyEq.rfl⟩
  have : Nonempty (Fin (finrank ℝ E)) := Fin.pos_iff_nonempty.1 hdim
  have hloc : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ g : M → ℝ, ContMDiffOn I 𝓘(ℝ) 0 g U ∧
        toLp w =ᵐ[(riemannianVolume I M).restrict U] g := by
    intro p
    obtain ⟨d⟩ := nonempty_chartPDEData (I := I) p
    let F : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ :=
      fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
        f (chartInvMap (I := I) p y)
    have hf_coord : MemLp (fun y ↦ f (chartInvMap (I := I) p y)) r
        (volume.restrict (d.Ω : Set _)) :=
      memLp_comp_coordEquiv_of_memLp p d.hΩt d.hm d.hρ_min hf
    have hF_memLp : MemLp F r (volume.restrict (d.Ω : Set _)) :=
      hf_coord.of_le_mul
        ((d.hρ_cont.aestronglyMeasurable d.Ω.isOpen.measurableSet).mul
          hf_coord.aestronglyMeasurable)
        ((ae_restrict_mem d.Ω.isOpen.measurableSet).mono fun y hy ↦ by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (d.hρ_max y hy) (norm_nonneg _))
    have hhrn : (Fintype.card (Fin (finrank ℝ E)) : ℝ) < 2 * r := by simpa using hrn
    have hcont_rep : ContinuousOn (preciseRepresentative volume (W1p.value (d.T w))) d.Ω :=
      PDE.continuousOn_preciseRepresentative_of_forall_memLp hr hhrn d.hell d.ha_meas
        (fun L _ hLΩ ↦ hF_memLp.mono_measure (Measure.restrict_mono hLΩ le_rfl))
        fun φ ↦ by
          obtain ⟨Φ, hD, hI⟩ := d.htest φ
          exact (hD w).symm.trans ((hw Φ).trans (hI f))
    let g : M → ℝ := fun x ↦ preciseRepresentative volume (W1p.value (d.T w))
      (coordEquiv E (extChartAt I p x))
    have hg_cont : ContinuousOn g (chartNbhd (I := I) p d.Ω) := by
      refine hcont_rep.comp ((coordEquiv E).continuous.continuousOn.comp
        ((continuousOn_extChartAt p).mono inter_subset_left) (mapsTo_univ _ _)) ?_
      rintro x ⟨-, y, hyΩ, hyx⟩
      dsimp only [Function.comp_apply]
      rw [← hyx, (coordEquiv E).apply_symm_apply]
      exact hyΩ
    have hae_coord : (fun y ↦ (toLp w : M → ℝ) (chartInvMap (I := I) p y)) =ᵐ[
        volume.restrict (d.Ω : Set _)]
        fun y ↦ g (chartInvMap (I := I) p y) := by
      filter_upwards [ae_restrict_mem d.Ω.isOpen.measurableSet,
        (d.hTv w).symm, W1p.ae_eq_preciseRepresentative (d.T w)] with y hy h1 h2
      have hψg : g (chartInvMap (I := I) p y) =
          preciseRepresentative volume (W1p.value (d.T w)) y := by
        dsimp only [g, chartInvMap]
        rw [(extChartAt I p).right_inv (d.hΩt hy), (coordEquiv E).apply_symm_apply]
      rw [h1, h2, hψg]
    exact ⟨chartNbhd (I := I) p d.Ω, isOpen_chartNbhd p d.Ω, mem_chartNbhd_self p d.hpΩ, g,
      contMDiffOn_zero_iff.2 hg_cont, (ae_eq_restrict_chart_iff p d.hΩt).2 hae_coord⟩
  obtain ⟨u, hu, hwu⟩ := exists_contMDiff_ae_eq_of_locally hloc
  exact ⟨u, contMDiff_zero_iff.1 hu, hwu⟩

end DeGiorgi

section SmoothRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- If `w ∈ H¹(M)` agrees almost everywhere with a smooth function `u` and solves `D(w, φ) = ∫ f φ`
for a continuous function `f`, then `w = ofSmooth u` and `-laplaceBeltrami I u x = f x` holds
pointwise everywhere on `M`. -/
theorem eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
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
  have horth : ∀ φ : C^∞⟮I, M; ℝ⟯,
      ∫ y, (-laplaceBeltrami I u y - f y) * φ y ∂riemannianVolume I M = 0 := fun φ ↦ by
    have h1 := hw φ
    rw [hw_eq, dirichletForm_comm, dirichletForm_ofSmooth_right] at h1
    have h2 : ∫ y, toLp (ofSmooth φ) y * -laplaceBeltrami I u y ∂riemannianVolume I M =
        ∫ y, -laplaceBeltrami I u y * φ y ∂riemannianVolume I M := by
      refine integral_congr_ae ?_
      filter_upwards [toLp_ofSmooth_ae_eq φ] with y hy
      rw [hy, mul_comm]
    rw [h2] at h1
    simp_rw [sub_mul]
    have hint1 : Integrable (fun y ↦ -laplaceBeltrami I u y * φ y) (riemannianVolume I M) :=
      (hΔ_cont.mul (map_continuous φ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hint2 : Integrable (fun y ↦ f y * φ y) (riemannianVolume I M) :=
      (hf.mul (map_continuous φ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_sub hint1 hint2, h1, sub_self]
  exact congrFun (eq_zero_of_forall_integral_mul_eq_zero hdiff_cont horth) x

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [I.Boundaryless] [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- Smoothness of the coordinate coefficient matrix `chartMatrix p` when the Riemannian metric is
smooth. -/
private theorem contDiffOn_chartMatrix (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E)))}
    (hΩt : MapsTo (coordEquiv E).symm Ω (extChartAt I p).target)
    (i j : Fin (finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun y ↦ chartMatrix (I := I) p y i j) Ω := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hψ_smooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) I ∞
      (chartInvMap (I := I) p) Ω :=
    (contMDiffOn_extChartAt_symm p).comp (coordEquiv E).symm.contDiff.contMDiff.contMDiffOn hΩt
  have hψ_base : MapsTo (chartInvMap (I := I) p) Ω
      (trivializationAt E (TangentSpace I) p).baseSet := fun y hy ↦ by
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target (hΩt hy)
  have hρ : ContDiffOn ℝ ∞
      (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y)) Ω :=
    ((contMDiffOn_chartVolumeDensity (I := I) (n := ∞) p).comp hψ_smooth hψ_base).contDiffOn
  have hG : ContDiffOn ℝ ∞
      (fun y ↦ chartInvGramMatrix (I := I) p (chartInvMap (I := I) p y) i j) Ω :=
    ((contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) p i j).comp
      hψ_smooth hψ_base).contDiffOn
  simpa only [chartMatrix, Matrix.smul_apply, smul_eq_mul] using hρ.mul hG

/-- **Linear smooth elliptic regularity on `H¹(M)`.** Let `M` be a closed smooth Riemannian
manifold and `f : M → ℝ` a smooth function. Every weak solution `w ∈ H¹(M)` of `D(w, φ) = ∫ f φ dV`
is `ofSmooth u` for a smooth function `u` solving `-laplaceBeltrami I u x = f x` everywhere on
`M`. -/
theorem exists_contMDiff_of_dirichletForm_eq {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {w : SobolevH1 I M}
    (hw : ∀ φ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth φ) = ∫ x, f x * φ x ∂riemannianVolume I M) :
    ∃ u : C^∞⟮I, M; ℝ⟯, w = ofSmooth u ∧ ∀ x, -laplaceBeltrami I u x = f x := by
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hloc : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ g : M → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ g U ∧
        toLp w =ᵐ[(riemannianVolume I M).restrict U] g := by
    intro p
    obtain ⟨d⟩ := nonempty_chartPDEData (I := I) p
    have hψ_smooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) I ∞
        (chartInvMap (I := I) p) d.Ω :=
      (contMDiffOn_extChartAt_symm p).comp (coordEquiv E).symm.contDiff.contMDiff.contMDiffOn d.hΩt
    have hψ_base : MapsTo (chartInvMap (I := I) p) d.Ω
        (trivializationAt E (TangentSpace I) p).baseSet := fun y hy ↦ by
      rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
      exact (extChartAt I p).map_target (d.hΩt hy)
    have : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
    let F : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ :=
      fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
        f (chartInvMap (I := I) p y)
    have hF_smooth : ContDiffOn ℝ ∞ F d.Ω :=
      (((contMDiffOn_chartVolumeDensity (I := I) (n := ∞) p).comp hψ_smooth hψ_base).contDiffOn).mul
        ((hf.comp_contMDiffOn hψ_smooth).contDiffOn)
    have hu_test : ∀ φ : 𝓓(d.Ω, ℝ),
        PDE.energyFormH1 (chartMatrix (I := I) p) 0 0 (d.T w)
            (W1p.ofTestFunctionₗ volume d.Ω 2 φ) =
          ∫ y in (d.Ω : Set _), F y * φ y := fun φ ↦ by
      obtain ⟨Φ, hD, hI⟩ := d.htest φ
      exact (hD w).symm.trans ((hw Φ).trans (hI f))
    have hu_H10 := PDE.forall_energyFormH1_restrictL_eq_setIntegral
      (le_rfl : d.Ω ≤ d.Ω) d.hcoeff hu_test (d.hF_memLp2 hf.continuous)
    have h_id : W1p.restrictL (le_rfl : d.Ω ≤ d.Ω) (d.T w) = d.T w :=
      W1p.ext_value (Lp.ext (W1p.value_restrictL_ae le_rfl (d.T w)))
    rw [h_id] at hu_H10
    have hF_Wkp : ∀ y ∈ d.Ω,
        ∃ V : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E))), y ∈ V ∧
          ∀ k, ∃ G : Wkp volume V 2 k,
            (Wkp.value k G : _ → ℝ) =ᵐ[volume.restrict (V : Set _)] F := by
      intro y hy
      obtain ⟨ε, hε, hεΩ⟩ := nhds_basis_closedBall.mem_iff.1 (d.Ω.isOpen.mem_nhds hy)
      refine ⟨⟨ball y ε, isOpen_ball⟩, mem_ball_self hε, fun k ↦ ?_⟩
      exact Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
        (Omega := ⟨ball y ε, isOpen_ball⟩) (p := 2) k d.Ω.isOpen
        (hF_smooth.of_le (by exact_mod_cast le_top))
        (isCompact_closedBall y ε) ball_subset_closedBall hεΩ
    obtain ⟨g₀, hg₀_smooth, hg₀_ae⟩ := d.hell.exists_contDiffOn_ae_eq_of_contDiffOn
      (contDiffOn_chartMatrix p d.hΩt) contDiffOn_const contDiffOn_const hF_Wkp hu_H10
    let g : M → ℝ := fun x ↦ g₀ (coordEquiv E (extChartAt I p x))
    have hg_smooth : ContMDiffOn I 𝓘(ℝ) ∞ g (chartNbhd (I := I) p d.Ω) := by
      refine hg₀_smooth.contMDiffOn.comp ((coordEquiv E).contDiff.contMDiff.comp_contMDiffOn
        ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := p)).mono
          (extChartAt_source I p ▸ inter_subset_left))) ?_
      rintro x ⟨-, y, hyΩ, hyx⟩
      rw [mem_preimage, ← hyx, (coordEquiv E).apply_symm_apply]
      exact hyΩ
    have hae_coord : (fun y ↦ (toLp w : M → ℝ) (chartInvMap (I := I) p y)) =ᵐ[
        volume.restrict (d.Ω : Set _)]
        fun y ↦ g (chartInvMap (I := I) p y) := by
      filter_upwards [ae_restrict_mem d.Ω.isOpen.measurableSet,
        (d.hTv w).symm, hg₀_ae] with y hy h1 h2
      have hψg : g (chartInvMap (I := I) p y) = g₀ y := by
        dsimp only [g, chartInvMap]
        rw [(extChartAt I p).right_inv (d.hΩt hy), (coordEquiv E).apply_symm_apply]
      rw [h1, h2, hψg]
    exact ⟨chartNbhd (I := I) p d.Ω, isOpen_chartNbhd p d.Ω, mem_chartNbhd_self p d.hpΩ, g,
      hg_smooth, (ae_eq_restrict_chart_iff p d.hΩt).2 hae_coord⟩
  obtain ⟨u₀, hu₀, hwu₀⟩ := exists_contMDiff_ae_eq_of_locally hloc
  obtain ⟨hw_eq, hΔ⟩ := eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq
    (u := ⟨u₀, hu₀⟩) hf.continuous hwu₀ hw
  exact ⟨⟨u₀, hu₀⟩, hw_eq, hΔ⟩

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
  have hRHS_cont : Continuous fun x ↦ A x * Φ (u x) + C x :=
    (hA.continuous.mul (hΦ.continuous.comp hu_cont)).add hC.continuous
  have hu_smooth : ContMDiff I 𝓘(ℝ) ∞ u := by
    intro p
    obtain ⟨d⟩ := nonempty_chartPDEData (I := I) p
    have hψ_smooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) I ∞
        (chartInvMap (I := I) p) d.Ω :=
      (contMDiffOn_extChartAt_symm p).comp (coordEquiv E).symm.contDiff.contMDiff.contMDiffOn d.hΩt
    have hψ_base : MapsTo (chartInvMap (I := I) p) d.Ω
        (trivializationAt E (TangentSpace I) p).baseSet := fun y hy ↦ by
      rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
      exact (extChartAt I p).map_target (d.hΩt hy)
    have : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
    have hρ_smooth : ContDiffOn ℝ ∞
        (fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y)) d.Ω :=
      ((contMDiffOn_chartVolumeDensity (I := I) (n := ∞) p).comp hψ_smooth hψ_base).contDiffOn
    let A₀ : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ :=
      fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
        A (chartInvMap (I := I) p y)
    let C₀ : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ :=
      fun y ↦ chartVolumeDensity (I := I) p (chartInvMap (I := I) p y) *
        C (chartInvMap (I := I) p y)
    have hA₀ : ContDiffOn ℝ ∞ A₀ d.Ω :=
      hρ_smooth.mul ((hA.comp_contMDiffOn hψ_smooth).contDiffOn)
    have hC₀ : ContDiffOn ℝ ∞ C₀ d.Ω :=
      hρ_smooth.mul ((hC.comp_contMDiffOn hψ_smooth).contDiffOn)
    let F : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ :=
      fun y ↦ A₀ y * Φ (u (chartInvMap (I := I) p y)) + C₀ y
    have hF_L2 : MemLp F 2 (volume.restrict (d.Ω : Set _)) :=
      (d.hF_memLp2 hRHS_cont).ae_eq (Filter.Eventually.of_forall fun y ↦ by
        dsimp only [F, A₀, C₀]
        ring)
    have hu_test : ∀ φ : 𝓓(d.Ω, ℝ),
        PDE.energyFormH1 (chartMatrix (I := I) p) 0 0 (d.T w)
            (W1p.ofTestFunctionₗ volume d.Ω 2 φ) =
          ∫ y in (d.Ω : Set _), F y * φ y := fun φ ↦ by
      obtain ⟨Φt, hD, hI⟩ := d.htest φ
      refine (hD w).symm.trans ((hw Φt).trans ((hI fun x ↦ A x * Φ (u x) + C x).trans ?_))
      refine setIntegral_congr_fun d.Ω.isOpen.measurableSet fun y _ ↦ ?_
      dsimp only [F, A₀, C₀]
      ring
    have hu_H10 := PDE.forall_energyFormH1_restrictL_eq_setIntegral
      (le_rfl : d.Ω ≤ d.Ω) d.hcoeff hu_test hF_L2
    have h_id : W1p.restrictL (le_rfl : d.Ω ≤ d.Ω) (d.T w) = d.T w :=
      W1p.ext_value (Lp.ext (W1p.value_restrictL_ae le_rfl (d.T w)))
    rw [h_id] at hu_H10
    have hTv_u : W1p.value (d.T w) =ᵐ[volume.restrict (d.Ω : Set _)]
        fun y ↦ u (chartInvMap (I := I) p y) :=
      (d.hTv w).trans ((ae_eq_restrict_chart_iff p d.hΩt).1 (ae_restrict_of_ae hwu))
    have hu_coord_smooth : ContDiffOn ℝ ∞ (fun y ↦ u (chartInvMap (I := I) p y)) d.Ω :=
      d.hell.contDiffOn_of_energyFormH1_eq (by simpa using hE) (contDiffOn_chartMatrix p d.hΩt)
        hA₀ hC₀ hΦ (hu_cont.continuousOn.comp hψ_smooth.continuousOn (mapsTo_univ _ _))
        hTv_u hu_H10
    have hu_on_U : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x ↦ u (chartInvMap (I := I) p (coordEquiv E (extChartAt I p x))))
        (chartNbhd (I := I) p d.Ω) := by
      refine hu_coord_smooth.contMDiffOn.comp ((coordEquiv E).contDiff.contMDiff.comp_contMDiffOn
        ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := p)).mono
          (extChartAt_source I p ▸ inter_subset_left))) ?_
      rintro x ⟨-, y, hyΩ, hyx⟩
      rw [mem_preimage, ← hyx, (coordEquiv E).apply_symm_apply]
      exact hyΩ
    refine (hu_on_U.congr fun x hx ↦ ?_).contMDiffAt
      ((isOpen_chartNbhd p d.Ω).mem_nhds (mem_chartNbhd_self p d.hpΩ))
    dsimp only [chartInvMap]
    rw [(coordEquiv E).symm_apply_apply, (extChartAt I p).left_inv hx.1]
  exact ⟨hu_smooth, (eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq
    (u := ⟨u, hu_smooth⟩) hRHS_cont hwu hw).2⟩

end SmoothRegularity

end SobolevH1

end TauCeti.Manifold
