/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Divergence
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Boundary
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Chart.Flux
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame
import TauCeti.LinearAlgebra.Alternating.Uncurry.Fin
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.HalfSpace
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

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

/-! ### Standard-basis chart volume density and coordinate divergence -/

private abbrev Espace (m : ℕ) := EuclideanSpace ℝ (Fin m)
private abbrev bdryI (n : ℕ) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

section StdChartDensity

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]

private abbrev stdBasis (m : ℕ) := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
private abbrev finB (m : ℕ) := Module.finBasis ℝ (Espace m)
private abbrev finσ (m : ℕ) := finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m))
private abbrev finBasisReindex (m : ℕ) := (finB m).reindex (finσ m)
private abbrev trivAt (α : N) := trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α
private def stdBasisDet (m : ℕ) : ℝ := |(stdBasis m).det (finBasisReindex m)|
private theorem stdBasisDet_pos (m : ℕ) : 0 < stdBasisDet m :=
  abs_pos.2 ((stdBasis m).isUnit_det (finBasisReindex m)).ne_zero

/-- Express the `finBasis` chart local frame in the `EuclideanSpace.basisFun` chart frame. -/
private theorem chartLocalFrame_eq_sum_stdLocalFrame (α : N) {y : N}
    (hy : y ∈ (trivAt (I := I) α).baseSet) (j : Fin m) :
    chartLocalFrame (I := I) α ((finσ m).symm j) y =
      ∑ i : Fin m, (stdBasis m).repr (finBasisReindex m j) i •
        (trivAt (I := I) α).localFrame (stdBasis m) i y := by
  rw [chartLocalFrame_eq_symmL, (Module.Basis.reindex_apply (finB m) _ j).symm]
  conv_lhs => rw [← (stdBasis m).sum_repr (finBasisReindex m j)]
  rw [map_sum]; simp_rw [map_smul, symmL_basis_eq_localFrame _ hy]

variable [RiemannianBundle (fun x : N ↦ TangentSpace I x)]

/-- The Riemannian volume density in the chart frame induced by `EuclideanSpace.basisFun`. -/
private def stdChartVolumeDensity (α y : N) : ℝ :=
  (stdBasisDet m)⁻¹ * chartVolumeDensity (I := I) α y

private theorem stdChartVolumeDensity_eq_sqrt_det_gram (α : N) {y : N}
    (hy : y ∈ (trivAt (I := I) α).baseSet) :
    stdChartVolumeDensity (I := I) α y =
      √(Matrix.gram ℝ ((trivAt (I := I) α).basisAt (stdBasis m) hy)).det := by
  set e := trivAt (I := I) α; set bil := innerₗ (TangentSpace I y)
  set B_std := e.basisAt (stdBasis m) hy; set B_fin := e.basisAt (finBasisReindex m) hy
  have hmat : B_std.toMatrix B_fin = (stdBasis m).toMatrix (finBasisReindex m) := by
    ext i j; simp [Module.Basis.toMatrix_apply, B_std, B_fin, Trivialization.basisAt,
      e.apply_mk_symm hy]
  have hgram_std : LinearMap.BilinForm.toMatrix B_std bil = Matrix.gram ℝ B_std := by
    ext i j; simp [LinearMap.BilinForm.toMatrix_apply, Matrix.gram_apply, bil]
  have hgram_fin : (LinearMap.BilinForm.toMatrix B_fin bil).det =
      (chartGramMatrix (I := I) α y).det := by
    rw [← Matrix.det_submatrix_equiv_self (finσ m).symm (chartGramMatrix (I := I) α y)]; congr 1
    rw [← gram_basisAt_finBasis_reindex (finσ m) α hy]
    ext i j; simp [LinearMap.BilinForm.toMatrix_apply, Matrix.gram_apply, B_fin, e, trivAt, bil]
  have hdet : (chartGramMatrix (I := I) α y).det =
      (stdBasisDet m) ^ 2 * (Matrix.gram ℝ B_std).det := by
    rw [← hgram_fin, ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix B_std B_fin bil, hgram_std,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmat, ← Module.Basis.det_apply]
    simp only [stdBasisDet, sq_abs]; ring
  rw [stdChartVolumeDensity, chartVolumeDensity_def, hdet, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (stdBasisDet_pos m).le, inv_mul_cancel_left₀ (stdBasisDet_pos m).ne']

private theorem setIntegral_riemannianVolume_std_of_subset [MeasurableSpace N] [BorelSpace N]
    [LindelofSpace N] [IsContinuousRiemannianBundle (Espace m) (fun x : N ↦ TangentSpace I x)]
    {α : N} {s : Set N} (hs : s ⊆ (chartAt H α).source) (hs' : MeasurableSet s) (φ : N → ℝ) :
    ∫ x in s, φ x ∂riemannianVolume I N = ∫ z in (extChartAt I α) '' s,
      stdChartVolumeDensity (I := I) α ((extChartAt I α).symm z) *
        φ ((extChartAt I α).symm z) ∂volume := by
  have hhaar : (finB m).addHaar = ENNReal.ofReal (stdBasisDet m)⁻¹ • (volume : Measure _) := by
    rw [← Module.Basis.addHaar_reindex _ (finσ m),
      Module.Basis.addHaar_eq_smul_of_basis (stdBasis m), stdBasis,
      OrthonormalBasis.addHaar_eq_volume, abs_inv, stdBasisDet]
  rw [setIntegral_riemannianVolume_of_subset hs hs' φ]; simp_rw [smul_eq_mul]
  rw [Module.Basis.setIntegral_addHaar_congr_measurableSpace (finB m)
      (@extChartAtMeasurableSpaceE (Espace m) _) inferInstance
      (@extChartAtBorelSpaceE (Espace m) _) inferInstance,
    hhaar, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 (stdBasisDet_pos m).le)]
  simp_rw [smul_eq_mul, ← integral_const_mul, ← mul_assoc, stdChartVolumeDensity]

/-- Near `y`, each standard-frame flux coefficient is a linear combination of `finBasis` ones. -/
private theorem stdChartVolumeDensity_mul_localFrameCoeff_eventuallyEq_sum [IsManifold I 2 N]
    (α : N) {y : N} (hy : y ∈ (trivAt (I := I) α).baseSet) (X : (x : N) → TangentSpace I x)
    (i : Fin m) :
    (fun z ↦ stdChartVolumeDensity (I := I) α z *
        (trivAt (I := I) α).localFrameCoeff I (stdBasis m) i z (X z)) =ᶠ[𝓝 y]
      fun z ↦ ∑ j : Fin m, ((stdBasisDet m)⁻¹ * (stdBasis m).repr (finBasisReindex m j) i) •
        (chartVolumeDensity (I := I) α z * (trivAt (I := I) α).localFrameCoeff I
          (finB m) ((finσ m).symm j) z (X z)) := by
  set e := trivAt (I := I) α
  filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
  rw [e.localFrameCoeff_apply_of_mem_baseSet (stdBasis m) hz]
  have hw : (e.basisAt (stdBasis m) hz).repr (X z) i = ∑ j : Fin m,
      (stdBasis m).repr (finBasisReindex m j) i *
        (e.basisAt (finB m) hz).repr (X z) ((finσ m).symm j) := by
    rw [← Finsupp.lapply_apply (R := ℝ) i]
    conv_lhs => rw [← (e.basisAt (finBasisReindex m) hz).sum_repr (X z)]
    rw [map_sum, map_sum]; exact Finset.sum_congr rfl fun j _ ↦ by
      simp [Trivialization.basisAt, e.apply_mk_symm hz, mul_comm]
  rw [hw, stdChartVolumeDensity, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by
    rw [← e.localFrameCoeff_apply_of_mem_baseSet (I := I) (finB m) hz X ((finσ m).symm j),
      smul_eq_mul]; ring

/-- Chart divergence formula `ρ_std div X = ∑ᵢ ∂ᵢ (ρ_std Xⁱ)` in the standard basis frame. -/
private theorem stdChartVolumeDensity_mul_divergence [IsManifold I 2 N]
    [IsContMDiffRiemannianBundle I 1 (Espace m) (fun x : N ↦ TangentSpace I x)] (α : N) {y : N}
    (hy : y ∈ (trivAt (I := I) α).baseSet) {X : (x : N) → TangentSpace I x}
    (hX : MDiffAt (T% X) y) :
    stdChartVolumeDensity (I := I) α y * divergence I X y =
      ∑ i : Fin m, mvfderiv I (fun z ↦ stdChartVolumeDensity (I := I) α z *
        (trivAt (I := I) α).localFrameCoeff I (stdBasis m) i z (X z)) y
        ((trivAt (I := I) α).localFrame (stdBasis m) i y) := by
  have : IsManifold I (1 + 1) N := by norm_num; infer_instance
  let _ : ContMDiffVectorBundle 1 (Espace m) (TangentSpace I : N → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  set e := trivAt (I := I) α
  let A (i j : Fin m) : ℝ := (stdBasis m).repr (finBasisReindex m j) i
  let g (k) (z : N) : ℝ := chartVolumeDensity (I := I) α z * e.localFrameCoeff I (finB m) k z (X z)
  have hρ := ((contMDiffOn_chartVolumeDensity (n := 1) α).contMDiffAt
    (e.open_baseSet.mem_nhds hy)).mdifferentiableAt one_ne_zero
  have hfk (k) : MDiffAt (g k) y := hρ.mul (mdifferentiableAt_localFrameCoeff (finB m) hy hX k)
  -- Reindex the `finBasis` divergence formula, expand the frame in `stdBasis`, and recombine
  -- the differentiated `stdBasis` coefficients.
  calc stdChartVolumeDensity (I := I) α y * divergence I X y
      = (stdBasisDet m)⁻¹ * ∑ j : Fin m,
          mvfderiv I (g ((finσ m).symm j)) y (chartLocalFrame (I := I) α ((finσ m).symm j) y) := by
          rw [stdChartVolumeDensity, mul_assoc, chartVolumeDensity_mul_divergence α hy hX]
          congr 1; exact (Equiv.sum_comp (finσ m).symm fun k ↦
            mvfderiv I (g k) y (chartLocalFrame (I := I) α k y)).symm
    _ = ∑ i : Fin m, ∑ j : Fin m, ((stdBasisDet m)⁻¹ * A i j) *
          mvfderiv I (g ((finσ m).symm j)) y (e.localFrame (stdBasis m) i y) := by
          rw [Finset.mul_sum, Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [chartLocalFrame_eq_sum_stdLocalFrame α hy j, map_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]; ring
    _ = _ := by
          refine Finset.sum_congr rfl fun i _ ↦ Eq.symm ?_
          rw [(stdChartVolumeDensity_mul_localFrameCoeff_eventuallyEq_sum α hy X i).mvfderiv_eq,
            TauCeti.mvfderiv_fun_sum (f := fun j z ↦ ((stdBasisDet m)⁻¹ * A i j) •
              g ((finσ m).symm j) z) (fun j _ ↦ (hfk ((finσ m).symm j)).const_smul _), sum_apply]
          exact Finset.sum_congr rfl fun j _ ↦ by
            rw [TauCeti.mvfderiv_const_smul (hfk ((finσ m).symm j)), smul_apply, smul_eq_mul]

end StdChartDensity

/-! ### Single-chart divergence theorem on a half-space chart -/

private abbrev piToE (m : ℕ) := (EuclideanSpace.equiv (Fin m) ℝ).symm
private abbrev piHalfSpace (n : ℕ) : Set (Fin (n + 1) → ℝ) := {x | 0 ≤ x 0}

private theorem piToE_cons_zero (n : ℕ) (y : Fin n → ℝ) :
    piToE (n + 1) (Fin.cons 0 y) = euclideanHalfSpaceBoundaryParam n (piToE n y) := by
  ext k; refine Fin.cases ?_ (fun j ↦ ?_) k <;>
    simp [piToE, euclideanHalfSpaceBoundaryParam_apply_zero,
      euclideanHalfSpaceBoundaryParam_apply_succ]

private theorem piToE_mapsTo_range (n : ℕ) :
    MapsTo (piToE (n + 1)) (piHalfSpace n) (range (𝓡∂ (n + 1))) := fun _ hy ↦ by
  simpa [piToE, piHalfSpace, range_modelWithCornersEuclideanHalfSpace] using hy

section HalfSpaceChart

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]

local instance : IsManifold (𝓡∂ (n + 1)) 1 M := IsManifold.of_le (n := 2) (by norm_num)
local instance : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M

private abbrev ambTriv (α : M) := trivializationAt (Espace (n + 1)) (TangentSpace (𝓡∂ (n + 1))) α
private abbrev bdryTriv (α : (𝓡∂ (n + 1)).boundary M) :=
  trivializationAt (Espace n) (TangentSpace (bdryI n)) α
private abbrev ambTsupport (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) : Set M :=
  tsupport (α := Espace (n + 1)) X

omit [IsManifold (𝓡∂ (n + 1)) 2 M] in
private theorem apply_eq_zero_of_notMem_ambTsupport {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    {x : M} (hx : x ∉ ambTsupport X) : X x = 0 :=
  image_eq_zero_of_notMem_tsupport (α := Espace (n + 1)) hx

/-- `dι` sends the standard boundary chart frame at `α` to the last `n` ambient frame vectors. -/
private theorem mfderiv_subtypeVal_boundary_basisAt_stdBasis
    (α q : (𝓡∂ (n + 1)).boundary M) (hq : q ∈ (extChartAt (bdryI n) α).source)
    (hq_base : q ∈ (bdryTriv α).baseSet) (hq'_base : (q : M) ∈ (ambTriv (α : M)).baseSet)
    (i : Fin n) :
    mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) q
        ((bdryTriv α).basisAt (stdBasis n) hq_base i) =
      (ambTriv (α : M)).basisAt (stdBasis (n + 1)) hq'_base i.succ := by
  have hq_chart : q ∈ (chartAt (Espace n) α).source := (extChartAt_source (I := bdryI n) α) ▸ hq
  have hq'_chart : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (α : M)).source := by
    simpa only [boundaryChartedSpace_chartAt_source, mem_preimage] using hq_chart
  have hparam : euclideanHalfSpaceBoundaryParam n (stdBasis n i) = stdBasis (n + 1) i.succ := by
    ext k; refine Fin.cases ?_ (fun j ↦ ?_) k <;>
      simp [stdBasis, euclideanHalfSpaceBoundaryParam_apply_zero,
        euclideanHalfSpaceBoundaryParam_apply_succ, Fin.succ_inj]
  have htcc := congrArg (· (stdBasis n i))
    (tangentCoordChange_boundaryParam hq (mem_extChartAt_source q))
  simp only [ContinuousLinearMap.comp_apply, hparam] at htcc
  rw [basisAt_apply, basisAt_apply, TangentBundle.symmL_trivializationAt_eq_core hq_chart,
    TangentBundle.symmL_trivializationAt_eq_core hq'_chart, tangentBundleCore_coordChange_achart,
    tangentBundleCore_coordChange_achart, mfderiv_subtypeVal_boundary]; exact htcc.symm

/-- Since the zeroth ambient chart vector points inward (`x₀ ≥ 0`), the standard boundary chart
basis has the opposite orientation to `halfSpaceBoundaryOrientation` of the ambient basis. -/
private theorem orientation_boundary_basisAt_stdBasis_eq_neg
    (α q : (𝓡∂ (n + 1)).boundary M) (hq : q ∈ (extChartAt (bdryI n) α).source)
    (hq_base : q ∈ (bdryTriv α).baseSet) (hq'_base : (q : M) ∈ (ambTriv (α : M)).baseSet) :
    ((bdryTriv α).basisAt (stdBasis n) hq_base).orientation =
      -(_root_.Orientation.halfSpaceBoundaryOrientation
        ((ambTriv (α : M)).basisAt (stdBasis (n + 1)) hq'_base).orientation) := by
  set e' := ambTriv (n := n) (α : M); set B := (bdryTriv α).basisAt (stdBasis n) hq_base
  set B' := e'.basisAt (stdBasis (n + 1)) hq'_base
  -- Flip the inward zeroth basis vector to an outward vector, reversing the ambient orientation.
  let w : Fin (n + 1) → ℝˣ := Fin.cons (-1) fun _ ↦ 1; let B_neg := B'.unitsSMul w
  have hB_neg0 : (fun v : Espace (n + 1) ↦ v 0) (B_neg 0) < 0 := by
    have hB0 : B_neg 0 = e'.symmL ℝ (q : M) (-EuclideanSpace.single 0 1) := by
      simp only [B_neg, w, Module.Basis.unitsSMul_apply, Fin.cons_zero, Units.smul_def,
        Units.val_neg, Units.val_one, neg_one_smul, map_neg, B', basisAt_apply, stdBasis,
        OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    have h := (hB0 ▸ isOutwardPointing_trivializationAt_symmL_neg_single_zero
      hq'_base).coordinate_deriv_neg
    rwa [mfderiv_extChartAt_self] at h
  have hB_neg_orient : B_neg.orientation = -B'.orientation := by
    rw [← B'.orientation_ne_iff_eq_neg, ne_comm, B_neg.orientation_ne_iff_eq_neg,
      B'.orientation_eq_neg_iff_det_neg B_neg, Module.Basis.det_apply]
    have hdiag : B'.toMatrix B_neg = Matrix.diagonal fun k ↦ (w k : ℝ) := by
      ext i j; by_cases hij : i = j <;> simp [B_neg, hij, Module.Basis.toMatrix_apply,
        Module.Basis.unitsSMul_apply, Units.smul_def]
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_succ]; simp [w]
  have hspec := _root_.Orientation.halfSpaceBoundaryOrientation_spec
    (-B'.orientation) hB_neg0 B B_neg (funext fun k ↦ Fin.cases rfl (fun i ↦ by
      have h1 : B_neg i.succ = B' i.succ := by simp [B_neg, w, Module.Basis.unitsSMul_apply]
      have h2 := (mfderiv_subtypeVal_boundary_basisAt_stdBasis α q hq hq_base hq'_base i).symm
      rw [mfderiv_subtypeVal_boundary] at h2; exact h1.trans h2) k)
  exact (hspec.2 hB_neg_orient).trans (_root_.Orientation.halfSpaceBoundaryOrientation_neg _)

variable [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- At `q ∈ ∂M` in a boundary chart at `α`, `ρ X⁰ = -ρ_∂ ⟪X, N⟫` (all `n ≥ 0`). -/
private theorem stdChartVolumeDensity_mul_localFrameCoeff_zero_boundary
    (α q : (𝓡∂ (n + 1)).boundary M) (hq : q ∈ (extChartAt (bdryI n) α).source)
    (u : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    stdChartVolumeDensity (I := 𝓡∂ (n + 1)) (α : M) (q : M) *
      (ambTriv (α : M)).localFrameCoeff (𝓡∂ (n + 1)) (stdBasis (n + 1)) 0 (q : M) u =
      -(stdChartVolumeDensity (I := bdryI n) α q * inner ℝ u (halfSpaceOutwardUnitNormal q)) := by
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
          (halfSpaceOutwardUnitNormal ((extChartAt (bdryI n) α₀).symm w))) w) := by
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

private theorem contMDiffOn_stdChartVolumeDensity (α : M) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) 1 (stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α)
      (chartAt (EuclideanHalfSpace (n + 1)) α).source :=
  contMDiffOn_const.mul (by simpa only [TangentBundle.trivializationAt_baseSet] using
    contMDiffOn_chartVolumeDensity (I := 𝓡∂ (n + 1)) (n := 1) α)

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
    {x : Fin (n + 1) → ℝ} (hx : x ∈ piHalfSpace n) :
    (∑ i : Fin (n + 1), fderivWithin ℝ (fun y j ↦ stdChartFluxE α X j (piToE (n + 1) y))
        (piHalfSpace n) x (Pi.single i 1) i) =
      (extChartAt (𝓡∂ (n + 1)) α).target.indicator (fun z ↦
        stdChartVolumeDensity (I := 𝓡∂ (n + 1)) α ((extChartAt (𝓡∂ (n + 1)) α).symm z) *
          divergence (𝓡∂ (n + 1)) X ((extChartAt (𝓡∂ (n + 1)) α).symm z)) (piToE (n + 1) x) := by
  have hL_maps := piToE_mapsTo_range n
  have hflux_diff (i) := contDiffOn_chartFlux (stdBasis (n + 1))
    (contMDiffOn_stdChartVolumeDensity α) hX.contMDiffOn hKc himage i
  have hf_diff : ContDiffOn ℝ 1 (fun y i ↦ stdChartFluxE α X i (piToE (n + 1) y)) (piHalfSpace n) :=
    contDiffOn_pi.2 fun i ↦ (hflux_diff i).comp (piToE (n + 1)).contDiff.contDiffOn hL_maps
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
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  let _ : LindelofSpace ((𝓡∂ (n + 1)).boundary M) :=
    ((𝓡∂ (n + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.LindelofSpace
  set e₀ := extChartAt (bdryI n) α₀
  let bE : Espace n → ℝ := e₀.target.indicator fun w ↦
    stdChartVolumeDensity (I := bdryI n) α₀ (e₀.symm w) *
      inner ℝ (X ((e₀.symm w : (𝓡∂ (n + 1)).boundary M) : M))
        (halfSpaceOutwardUnitNormal (e₀.symm w))
  have htrace (y : Fin n → ℝ) :
      stdChartFluxE (α₀ : M) X 0 (piToE (n + 1) (Fin.cons 0 y)) = -bE (piToE n y) :=
    piToE_cons_zero n y ▸ stdChartFluxE_zero_boundaryParam α₀ X (piToE n y)
  simp_rw [htrace, integral_neg, neg_neg]
  trans (∫ w, bE w ∂volume)
  · exact (PiLp.volume_preserving_toLp (Fin n)).integral_comp
      (piToE n).toHomeomorph.measurableEmbedding bE
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e₀.target)
      (fun _ hw ↦ indicator_of_notMem hw _), halfSpaceBoundaryVolume_eq_riemannianVolume,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (chartAt (Espace n) α₀).source)
      fun q hq ↦ by simp [apply_eq_zero_of_notMem_ambTsupport
        fun h ↦ hq (by simpa [boundaryChartedSpace_chartAt_source] using hKs h)],
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
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  set ec := extChartAt (𝓡∂ (n + 1)) α
  have htrace_zero (y : Fin n → ℝ) : stdChartFluxE α X 0 (piToE (n + 1) (Fin.cons 0 y)) = 0 := by
    rw [piToE_cons_zero]; set w := euclideanHalfSpaceBoundaryParam n (piToE n y)
    by_cases hw' : w ∈ ec.target
    · have hp_src : ec.symm w ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source :=
        (extChartAt_source (I := 𝓡∂ (n + 1)) α) ▸ ec.map_target hw'
      have hp_bdry : ec.symm w ∈ (𝓡∂ (n + 1)).boundary M := by
        rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hp_src]
        simpa [ec, w, extChartAt, modelWithCornersEuclideanHalfSpace_toFun,
          euclideanHalfSpaceBoundaryParam_apply_zero] using
          congrArg (fun v : Espace (n + 1) ↦ v 0) (ec.right_inv hw')
      rw [stdChartFluxE, chartFlux_apply_of_mem _ _ 0 hw',
        apply_eq_zero_of_notMem_ambTsupport (disjoint_right.1 hdisj hp_bdry), map_zero, mul_zero]
    · exact chartFlux_apply_of_notMem _ _ 0 hw'
  have hbdry_zero (q : (𝓡∂ (n + 1)).boundary M) :
      inner ℝ (X (q : M)) (halfSpaceOutwardUnitNormal q) = 0 := by
    simp [apply_eq_zero_of_notMem_ambTsupport (disjoint_right.1 hdisj q.property)]
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
    (himage : extChartAt (𝓡∂ (n + 1)) α '' ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).target) :
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
  have hpre : WithLp.toLp 2 ⁻¹' range (𝓡∂ (n + 1)) = piHalfSpace n := by
    ext x; simp [piHalfSpace, range_modelWithCornersEuclideanHalfSpace]
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
    _ = ∫ z in range (𝓡∂ (n + 1)), dE z ∂volume := by
          rw [setIntegral_indicator htm, inter_eq_right.2 (extChartAt_target_subset_range α)]
    _ = ∫ x in piHalfSpace n, dE (piToE (n + 1) x) :=
          (hp.integral_comp (piToE (n + 1)).toHomeomorph.measurableEmbedding dE).symm
    _ = _ := setIntegral_congr_fun hHm fun x hx ↦
          (sum_fderivWithin_stdChartFlux_pi hX hKc himage hx).symm

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
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (halfSpaceOutwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have hKs' : ambTsupport X ⊆ (extChartAt (𝓡∂ (n + 1)) α).source := by rwa [extChartAt_source]
  have hKc := hK.image_of_continuousOn ((continuousOn_extChartAt α).mono hKs')
  have himage := ((extChartAt (𝓡∂ (n + 1)) α).mapsTo.mono_left hKs').image_subset
  -- Stage 1: apply the coordinate half-space divergence theorem to the chart fluxes `f`.
  let f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun x i ↦ stdChartFluxE α X i (piToE (n + 1) x)
  have hf_diff : ContDiffOn ℝ 1 f (piHalfSpace n) := contDiffOn_pi.2 fun i ↦
    (contDiffOn_chartFlux (stdBasis (n + 1)) (contMDiffOn_stdChartVolumeDensity α)
      hX.contMDiffOn hKc himage i).comp (piToE (n + 1)).contDiff.contDiffOn (piToE_mapsTo_range n)
  have hf_supp : HasCompactSupport f := HasCompactSupport.intro
    (hKc.image (piToE (n + 1)).symm.continuous) fun x hx ↦ funext fun i ↦
      chartFlux_eq_zero _ _ i fun h ↦ hx ⟨piToE (n + 1) x, h, (piToE (n + 1)).symm_apply_apply x⟩
  obtain ⟨-, -, hdiv_coord⟩ := hf_diff.integral_divergence_coordinate_halfSpace hf_supp
  -- Stage 2: transport `∫ div X dV` to the coordinate half-space divergence integral.
  rw [integral_divergence_eq_setIntegral_pi_halfSpace hX hKc hKs himage, hdiv_coord]
  -- Stage 3: identify the `x₀ = 0` trace integral with the Riemannian boundary flux.
  exact hcase.elim (fun h ↦ neg_integral_stdChartFlux_zero_eq_boundaryFlux ⟨α, h⟩ hKs)
    neg_integral_stdChartFlux_zero_eq_boundaryFlux_of_disjoint

end HalfSpaceChart

end TauCeti.Manifold
