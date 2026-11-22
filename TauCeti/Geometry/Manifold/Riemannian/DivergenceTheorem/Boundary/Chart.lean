/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.OutwardUnitNormal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Divergence
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Boundary
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorField.Chart.Flux
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame
import TauCeti.LinearAlgebra.Alternating.Uncurry.Fin
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.HalfSpace

/-!
# Single-chart boundary divergence theorem

This module proves the single-chart Riemannian divergence theorem on a manifold with boundary
modeled on `EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`), in every dimension `n ≥ 0` and without
global orientability assumptions.

## Main result

* `TauCeti.Manifold.integral_divergence_eq_boundaryFlux_of_tsupport_subset_chart`: the single-chart
  Riemannian divergence theorem on a half-space chart centered at the boundary or disjoint from the
  boundary.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 16.32.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

public section

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Riemannian.Tensor Set
open scoped ContDiff Manifold Matrix Topology

namespace TauCeti.Manifold

private abbrev Espace (m : ℕ) := EuclideanSpace ℝ (Fin m)
private abbrev bdryI (n : ℕ) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
private abbrev stdBasis (m : ℕ) := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis

/-! ### Single-chart divergence theorem on a half-space chart -/

private abbrev piToE (m : ℕ) := (EuclideanSpace.equiv (Fin m) ℝ).symm
private abbrev piHalfSpace (n : ℕ) : Set (Fin (n + 1) → ℝ) := {x | 0 ≤ x 0}

section HalfSpaceChart

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]

local instance instIsManifoldOneHalfSpaceChart : IsManifold (𝓡∂ (n + 1)) 1 M :=
  IsManifold.of_le (n := 2) (by norm_num)
local instance instIsManifoldAddOneHalfSpaceChart : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by
  rw [one_add_one_eq_two]; infer_instance
local instance instIsManifoldBoundaryHalfSpaceChart :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M

private abbrev ambTriv (α : M) := trivializationAt (Espace (n + 1)) (TangentSpace (𝓡∂ (n + 1))) α
private abbrev bdryTriv (α : (𝓡∂ (n + 1)).boundary M) :=
  trivializationAt (Espace n) (TangentSpace (bdryI n)) α
private abbrev ambTsupport (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) : Set M :=
  tsupport (α := Espace (n + 1)) X

variable [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- At `q ∈ ∂M` in a boundary chart at `α`, `ρ X⁰ = -ρ_∂ ⟪X, N⟫` (all `n ≥ 0`). -/
private theorem stdChartVolumeDensity_mul_localFrameCoeff_zero_boundary
    (α q : (𝓡∂ (n + 1)).boundary M) (hq : q ∈ (extChartAt (bdryI n) α).source)
    (u : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    stdChartVolumeDensity (I := 𝓡∂ (n + 1)) (α : M) (q : M) *
      (ambTriv (α : M)).localFrameCoeff (𝓡∂ (n + 1)) (stdBasis (n + 1)) 0 (q : M) u =
      -(stdChartVolumeDensity (I := bdryI n) α q * inner ℝ u (outwardUnitNormal q)) := by
  have _ : Fact (Module.finrank ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) = n + 1) :=
    ⟨by rw [TauCeti.finrank_tangentSpace]; simp⟩
  have _ : Fact (Module.finrank ℝ (TangentSpace (bdryI n) q) = n) :=
    ⟨by rw [TauCeti.finrank_tangentSpace]; simp⟩
  set e' := ambTriv (n := n) (α : M); set e := bdryTriv α
  have hq_chart : q ∈ (chartAt (Espace n) α).source := (extChartAt_source (I := bdryI n) α) ▸ hq
  have hq_base : q ∈ e.baseSet := by simpa [e, bdryTriv] using hq_chart
  have hq'_base : (q : M) ∈ e'.baseSet := by
    simpa [e', ambTriv, boundaryChartedSpace_chartAt_source] using hq_chart
  set B := e.basisAt (stdBasis n) hq_base; set B' := e'.basisAt (stdBasis (n + 1)) hq'_base
  set dι := mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) q
  set o_q := B'.orientation; set o_b := _root_.Orientation.halfSpaceBoundaryOrientation o_q
  -- Evaluate both sides of `volumeForm_cons_mfderiv_subtypeVal_boundary` on `(u, dι B)`.
  have hlhs : o_q.volumeForm (Fin.cons u fun i ↦ dι (B i)) =
      stdChartVolumeDensity (I := 𝓡∂ (n + 1)) (α : M) (q : M) *
        e'.localFrameCoeff (𝓡∂ (n + 1)) (stdBasis (n + 1)) 0 (q : M) u := by
    have hcons : (Fin.cons u fun i ↦ dι (B i)) =
        Matrix.vecCons u ((0 : Fin (n + 1)).removeNth B') := by
      ext k; refine Fin.cases rfl (fun i ↦ ?_) k
      simpa [Fin.tail] using mfderiv_subtypeVal_boundary_basisAt_stdBasis α q hq hq_base hq'_base i
    rw [hcons, o_q.volumeForm.map_vecCons_removeNth_basis B' u 0,
      o_q.volumeForm_apply_eq_sqrt_det_gram B' rfl,
      ← stdChartVolumeDensity_eq_sqrt_det_gram (α : M) hq'_base,
      e'.localFrameCoeff_apply_of_mem_baseSet (stdBasis (n + 1)) hq'_base (fun _ ↦ u) 0]
    simp [B', mul_comm]
  have hrhs_vol : _root_.Orientation.volumeForm (E := TangentSpace (bdryI n) q) o_b B =
      -stdChartVolumeDensity (I := bdryI n) α q := by
    rw [_root_.Orientation.volumeForm_apply_eq_neg_sqrt_det_gram (E := TangentSpace (bdryI n) q)
        o_b B ((orientation_boundary_basisAt_stdBasis_eq_neg α q hq hq_base hq'_base) ▸
          (Module.Ray.ne_neg_self o_b).symm), stdChartVolumeDensity_eq_sqrt_det_gram α hq_base]
  have hmain := volumeForm_cons_mfderiv_subtypeVal_boundary q o_q u B
  rw [hlhs, hrhs_vol] at hmain; linarith

/-- The `i`-th standard-frame flux of `X` in `extChartAt` at `α`, extended by zero off target. -/
private abbrev stdChartFluxE (α : M) (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x)
    (i : Fin (n + 1)) : Espace (n + 1) → ℝ :=
  TauCeti.chartFlux (stdBasis (n + 1)) (stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α) α X i

/-- Boundary trace of the zeroth chart flux on `x₀ = 0` equals the negated boundary flux density. -/
private theorem stdChartFluxE_zero_boundaryParam (α₀ : (𝓡∂ (n + 1)).boundary M)
    (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) (w : Espace n) :
    stdChartFluxE (α₀ : M) X 0 (euclideanHalfSpaceBoundaryParam n w) =
      -((extChartAt (bdryI n) α₀).target.indicator (fun w ↦
        stdChartVolumeDensity (I := bdryI n) α₀ ((extChartAt (bdryI n) α₀).symm w) *
        inner ℝ (X (((extChartAt (bdryI n) α₀).symm w : (𝓡∂ (n + 1)).boundary M) : M))
          (outwardUnitNormal ((extChartAt (bdryI n) α₀).symm w))) w) := by
  set e₀ := extChartAt (bdryI n) α₀; set ec := extChartAt (𝓡∂ (n + 1)) (α₀ : M)
  by_cases hw : w ∈ e₀.target
  · have hw' := (boundaryParam_mem_extChartAt_target_iff α₀ w).2 hw
    set q := e₀.symm w; have hq_src : q ∈ e₀.source := e₀.map_target hw
    have hq'_src : (q : M) ∈ ec.source := by
      simpa only [e₀, ec, extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage]
        using hq_src
    have hsymm_eq : ec.symm (euclideanHalfSpaceBoundaryParam n w) = (q : M) := by
      rw [← e₀.right_inv hw, boundaryParam_extChartAt hq_src, ec.left_inv hq'_src]
    rw [indicator_of_mem hw, stdChartFluxE, chartFlux_apply_of_mem _ _ 0 hw', hsymm_eq]
    exact stdChartVolumeDensity_mul_localFrameCoeff_zero_boundary α₀ q hq_src (X (q : M))
  · rw [indicator_of_notMem hw, neg_zero, stdChartFluxE, chartFlux_apply_of_notMem _ _ 0
      (mt (boundaryParam_mem_extChartAt_target_iff α₀ w).1 hw)]

section DiffFlux

variable [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
  (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

private theorem sum_fderivWithin_stdChartFluxE {α : M} {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hKc : IsCompact (extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X))
    (himage : extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).target)
    {z : Espace (n + 1)} (hz_range : z ∈ range (𝓡∂ (n + 1))) :
    ∑ i : Fin (n + 1), fderivWithin ℝ (stdChartFluxE α X i) (range (𝓡∂ (n + 1))) z
        (stdBasis (n + 1) i) =
      (extChartAt (𝓡∂ (n + 1)) α).target.indicator (fun z ↦
        stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
          divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm z)) z := by
  set ec := extChartAt (𝓡∂ (n + 1)) α
  by_cases hz : z ∈ ec.target
  · rw [indicator_of_mem hz]
    have hy : ec.symm z ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source :=
      (extChartAt_source (I := 𝓡∂ (n + 1)) α) ▸ ec.map_target hz
    rw [stdChartVolumeDensity_mul_divergence α (by simpa using hy)
      ((hX _).mdifferentiableAt one_ne_zero)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mvfderiv_localFrame_trivializationAt_eq_fderivWithin (stdBasis (n + 1)) α hy _ i,
      ec.right_inv hz]
    congr 1; exact Filter.EventuallyEq.fderivWithin_eq
      (Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin_of_mem hz) fun _ h ↦
        chartFlux_apply_of_mem _ _ i h) (chartFlux_apply_of_mem _ _ i hz)
  · rw [indicator_of_notMem hz]; refine Finset.sum_eq_zero fun i _ ↦ ?_
    have h0 := ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) z).congr_of_eventuallyEq
      (chartFlux_eventuallyEq_zero (stdBasis (n + 1)) (stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α)
        hKc i fun h ↦ hz (himage h))).hasFDerivWithinAt (s := range (𝓡∂ (n + 1)))
    simp [h0.fderivWithin ((𝓡∂ (n + 1)).uniqueDiffOn z hz_range)]

/-- Pull the chart divergence formula back along `piToE (n + 1)` to `piHalfSpace n`. -/
private theorem sum_fderivWithin_stdChartFlux_pi {α : M} {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hKc : IsCompact (extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X))
    (himage : extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).target)
    (hflux_diff : ∀ i, ContDiffOn ℝ 1 (stdChartFluxE α X i) (range (𝓡∂ (n + 1))))
    (hf_diff : ContDiffOn ℝ 1 (fun y i ↦ stdChartFluxE α X i (piToE (n + 1) y)) (piHalfSpace n))
    {x : Fin (n + 1) → ℝ} (hx : x ∈ piHalfSpace n) :
    (∑ i : Fin (n + 1), fderivWithin ℝ (fun y j ↦ stdChartFluxE α X j (piToE (n + 1) y))
        (piHalfSpace n) x (Pi.single i 1) i) =
      (extChartAt (𝓡∂ (n + 1)) α).target.indicator (fun z ↦
        stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
          divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm z)) (piToE (n + 1) x) := by
  have hL_maps := mapsTo_euclideanSpace_equiv_symm_range_modelWithCornersEuclideanHalfSpace n
  have huniqH := TauCeti.uniqueDiffOn_pi_halfSpace 0 0 x hx
  rw [← sum_fderivWithin_stdChartFluxE hX hKc himage (hL_maps hx)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hfi := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ)
    i).hasFDerivAt.comp_hasFDerivWithinAt x
      (hf_diff.differentiableOn one_ne_zero x hx).hasFDerivWithinAt).fderivWithin huniqH
  have hL_eq := (((hflux_diff i).differentiableOn one_ne_zero (piToE (n + 1) x)
    (hL_maps hx)).hasFDerivWithinAt.comp x (piToE (n + 1)).hasFDerivAt.hasFDerivWithinAt
      hL_maps).fderivWithin huniqH
  have hsingle : piToE (n + 1) (Pi.single i 1) = stdBasis (n + 1) i := by
    ext j; simp [piToE, stdBasis, EuclideanSpace.basisFun_apply]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearEquiv.coe_coe, hsingle] using
      congrArg (· (Pi.single i 1)) (hfi.symm.trans hL_eq)

end DiffFlux

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- Boundary-trace integral transport: the negated `x₀ = 0` slice equals `∫_{∂M} ⟪X, N⟫ dS`. -/
private theorem neg_integral_stdChartFlux_zero_eq_boundaryFlux (α₀ : (𝓡∂ (n + 1)).boundary M)
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hKs : ambTsupport X ⊆ (chartAt (EuclideanHalfSpace (n + 1)) (α₀ : M)).source) :
    -(∫ y : Fin n → ℝ, stdChartFluxE (α₀ : M) X 0 (piToE (n + 1) (Fin.cons 0 y))) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (outwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  set e₀ := extChartAt (bdryI n) α₀
  let bE : Espace n → ℝ := e₀.target.indicator fun w ↦
    stdChartVolumeDensity (I := bdryI n) α₀ (e₀.symm w) *
      inner ℝ (X ((e₀.symm w : (𝓡∂ (n + 1)).boundary M) : M))
        (outwardUnitNormal (e₀.symm w))
  have htrace (y : Fin n → ℝ) :
      stdChartFluxE (α₀ : M) X 0 (piToE (n + 1) (Fin.cons 0 y)) = -bE (piToE n y) :=
    (euclideanSpace_equiv_symm_finCons_zero n y).symm ▸
      stdChartFluxE_zero_boundaryParam α₀ X (piToE n y)
  simp_rw [htrace, integral_neg, neg_neg]
  trans (∫ w, bE w ∂volume)
  · exact (PiLp.volume_preserving_toLp (Fin n)).integral_comp
      (piToE n).toHomeomorph.measurableEmbedding bE
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e₀.target)
      (fun _ hw ↦ indicator_of_notMem hw _), halfSpaceBoundaryVolume_eq_riemannianVolume,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (chartAt (Espace n) α₀).source)
      fun q hq ↦ by
        have h0 : X (q : M) = 0 := image_eq_zero_of_notMem_tsupport (α := Espace (n + 1))
          fun h ↦ hq (by simpa [boundaryChartedSpace_chartAt_source] using hKs h)
        simp [h0],
    setIntegral_riemannianVolume_std_of_subset subset_rfl
      (chartAt (Espace n) α₀).open_source.measurableSet,
    ← extChartAt_source (I := bdryI n), e₀.image_source_eq_target]
  exact setIntegral_congr_fun (isOpen_extChartAt_target α₀).measurableSet fun _ hw ↦
    indicator_of_mem hw _

/-- Both the `x₀ = 0` slice integral and boundary flux vanish when `tsupport X` misses `∂M`. -/
private theorem neg_integral_stdChartFlux_zero_eq_boundaryFlux_of_disjoint {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hdisj : Disjoint (ambTsupport X) ((𝓡∂ (n + 1)).boundary M)) :
    -(∫ y : Fin n → ℝ, stdChartFluxE α X 0 (piToE (n + 1) (Fin.cons 0 y))) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (outwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  set ec := extChartAt (𝓡∂ (n + 1)) α
  have htrace_zero (y : Fin n → ℝ) : stdChartFluxE α X 0 (piToE (n + 1) (Fin.cons 0 y)) = 0 := by
    rw [euclideanSpace_equiv_symm_finCons_zero]
    set w := euclideanHalfSpaceBoundaryParam n (piToE n y)
    by_cases hw' : w ∈ ec.target
    · have hp_src : ec.symm w ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source :=
        (extChartAt_source (I := 𝓡∂ (n + 1)) α) ▸ ec.map_target hw'
      have hp_bdry : ec.symm w ∈ (𝓡∂ (n + 1)).boundary M := by
        rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hp_src]
        simpa [ec, w, extChartAt, modelWithCornersEuclideanHalfSpace_toFun,
          euclideanHalfSpaceBoundaryParam_apply_zero] using
          congrArg (fun v : Espace (n + 1) ↦ v 0) (ec.right_inv hw')
      have h0 : X (ec.symm w) = 0 := image_eq_zero_of_notMem_tsupport (α := Espace (n + 1))
        (disjoint_right.1 hdisj hp_bdry)
      rw [stdChartFluxE, chartFlux_apply_of_mem _ _ 0 hw', h0, map_zero, mul_zero]
    · exact chartFlux_apply_of_notMem _ _ 0 hw'
  have hbdry_zero (q : (𝓡∂ (n + 1)).boundary M) :
      inner ℝ (X (q : M)) (outwardUnitNormal q) = 0 := by
    have h0 : X (q : M) = 0 := image_eq_zero_of_notMem_tsupport (α := Espace (n + 1))
      (disjoint_right.1 hdisj q.property)
    simp [h0]
  simp_rw [htrace_zero, hbdry_zero]; simp

variable [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
  (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- Coordinate-integral transport: `∫ div X dV` equals the coordinate divergence integral on
`piHalfSpace n`. -/
private theorem integral_divergence_eq_setIntegral_pi_halfSpace {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hKc : IsCompact (extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X))
    (hKs : ambTsupport X ⊆ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (himage : extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).target)
    (hflux_diff : ∀ i, ContDiffOn ℝ 1 (stdChartFluxE α X i) (range (𝓡∂ (n + 1))))
    (hf_diff : ContDiffOn ℝ 1 (fun y i ↦ stdChartFluxE α X i (piToE (n + 1) y)) (piHalfSpace n)) :
    (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x in piHalfSpace n, ∑ i : Fin (n + 1),
        fderivWithin ℝ (fun y j ↦ stdChartFluxE α X j (piToE (n + 1) y))
          (piHalfSpace n) x (Pi.single i 1) i := by
  set ec := extChartAt (𝓡∂ (n + 1)) α
  let dE : Espace (n + 1) → ℝ := ec.target.indicator fun z ↦
    stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α (ec.symm z) * divergence (𝓡∂ (n + 1)) X (ec.symm z)
  have hTm : MeasurableSet (range (𝓡∂ (n + 1))) :=
    (range_modelWithCornersEuclideanHalfSpace (n + 1)).symm ▸
      (isClosed_le continuous_const (EuclideanSpace.proj 0).continuous).measurableSet
  have hHm : MeasurableSet (piHalfSpace n) :=
    (isClosed_le continuous_const (continuous_apply 0)).measurableSet
  have hpre := preimage_euclideanSpace_equiv_symm_range_modelWithCornersEuclideanHalfSpace n
  have hp := hpre ▸ (PiLp.volume_preserving_toLp (Fin (n + 1))).restrict_preimage hTm
  have htm : MeasurableSet ec.target :=
    ec.image_source_eq_target ▸ (isOpen_extChartAt_source α).measurableSet.image_extChartAt
      α subset_rfl
  calc (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M)
      = ∫ x in (chartAt (EuclideanHalfSpace (n + 1)) α).source,
          divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
            divergence_eq_zero_of_notMem_tsupport (𝓡∂ (n + 1)) fun h ↦ hx (hKs h)).symm
    _ = ∫ z in ec.target, stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α (ec.symm z) *
          divergence (𝓡∂ (n + 1)) X (ec.symm z) ∂volume := by
          rw [setIntegral_riemannianVolume_std_of_subset subset_rfl
            (chartAt _ α).open_source.measurableSet, ← extChartAt_source (I := 𝓡∂ (n + 1)),
            ec.image_source_eq_target]
          simp_rw [smul_eq_mul]; dsimp only [ec]
    _ = ∫ z in range (𝓡∂ (n + 1)), dE z ∂volume := by
          rw [setIntegral_indicator htm, inter_eq_right.2 (extChartAt_target_subset_range α)]
    _ = ∫ x in piHalfSpace n, dE (piToE (n + 1) x) :=
          (hp.integral_comp (piToE (n + 1)).toHomeomorph.measurableEmbedding dE).symm
    _ = _ := setIntegral_congr_fun hHm fun x hx ↦
          (sum_fderivWithin_stdChartFlux_pi hX hKc himage hflux_diff hf_diff hx).symm

/-- **Single-chart divergence theorem on a manifold with boundary.** For a compactly supported `C¹`
vector field `X` supported in `(chartAt _ α).source`, where either `α` lies on the boundary or the
support of `X` is disjoint from the boundary, `∫ div X dV = ∫_{∂M} ⟪X, N⟫ dS`. -/
theorem integral_divergence_eq_boundaryFlux_of_tsupport_subset_chart {α : M}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hK : IsCompact (tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X))
    (hKs : tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X ⊆
      (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (hcase : α ∈ (𝓡∂ (n + 1)).boundary M ∨
      Disjoint (tsupport (α := EuclideanSpace ℝ (Fin (n + 1))) X) ((𝓡∂ (n + 1)).boundary M)) :
    (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (outwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have hKs' : ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).source := by rwa [extChartAt_source]
  have hKc := hK.image_of_continuousOn ((continuousOn_extChartAt α).mono hKs')
  have himage := ((extChartAt (𝓡∂ (n + 1)) α).mapsTo.mono_left hKs').image_subset
  -- Stage 1: apply the coordinate half-space divergence theorem to the chart fluxes `f`.
  let f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun x i ↦ stdChartFluxE α X i (piToE (n + 1) x)
  have hflux_diff (i) := contDiffOn_chartFlux (stdBasis (n + 1))
    (contMDiffOn_stdChartVolumeDensity α) hX.contMDiffOn hKc himage i
  have hf_diff : ContDiffOn ℝ 1 f (piHalfSpace n) := contDiffOn_pi.2 fun i ↦
    (hflux_diff i).comp (piToE (n + 1)).contDiff.contDiffOn
      (mapsTo_euclideanSpace_equiv_symm_range_modelWithCornersEuclideanHalfSpace n)
  have hsupp_i (i : Fin (n + 1)) : HasCompactSupport fun x ↦ f x i :=
    (hasCompactSupport_chartFlux (stdBasis (n + 1))
      (stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α) hKc i).comp_homeomorph
        (piToE (n + 1)).toHomeomorph
  have hf_supp : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_iUnion fun i ↦ (hsupp_i i).isCompact) fun x hx ↦
      funext fun i ↦ image_eq_zero_of_notMem_tsupport (f := fun x ↦ f x i) fun h ↦
        hx (mem_iUnion.2 ⟨i, h⟩)
  obtain ⟨-, -, hdiv_coord⟩ := hf_diff.integral_divergence_coordinate_halfSpace hf_supp
  -- Stage 2: transport `∫ div X dV` to the coordinate half-space divergence integral.
  rw [integral_divergence_eq_setIntegral_pi_halfSpace hX hKc hKs himage hflux_diff hf_diff,
    hdiv_coord]
  -- Stage 3: identify the `x₀ = 0` trace integral with the Riemannian boundary flux.
  exact hcase.elim (fun h ↦ neg_integral_stdChartFlux_zero_eq_boundaryFlux ⟨α, h⟩ hKs)
    neg_integral_stdChartFlux_zero_eq_boundaryFlux_of_disjoint

end HalfSpaceChart

end TauCeti.Manifold
