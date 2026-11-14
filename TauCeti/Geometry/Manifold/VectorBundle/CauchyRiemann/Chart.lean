/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
import Mathlib.Geometry.Manifold.Notation

/-!
# Real Cauchy–Riemann operators read in the charts of a finite bundle atlas

Let `M` be a complex manifold modelled on `E`, let `V → M` be a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, and let `A` be a finite bundle
atlas of `V`. A real Cauchy–Riemann operator `D` on `V` is read in chart `i` through the preferred
trivializations of the tangent bundle and of `V` at the centre of the chart
(`TauCeti.FiniteBundleAtlas.coord_tangentHom`). This file computes that reading:

`(D s)ᵢ = ∂bar sᵢ + Zᵢ sᵢ`,

where `sᵢ = A.coord i s` is the reading of the section, `∂bar sᵢ` is the complex antilinear part of
its derivative, and `Zᵢ = A.chartZeroOrder D i` is the zeroth-order term of chart `i`, the reading
of `D` on the frame of chart `i`. It follows from the local frame formula
`TauCeti.IsRealCauchyRiemannOperator.eq_frameCauchyRiemannOperator_add_sum`, because the flat
Cauchy–Riemann operator of the frame of chart `i` reads as `∂bar` of the reading. The zeroth-order
terms of two charts differ by `∂bar` of the coordinate change of `V`
(`TauCeti.FiniteBundleAtlas.chartZeroOrder_transition`). For an operator sending smooth sections
to smooth one-forms, the zeroth-order term of a chart is smooth, and bounded on the closure of the
image of the chart.

This is the chart calculus behind the realization of a smooth real Cauchy–Riemann operator as a
bounded operator between Sobolev spaces of sections, whose chart data are
`∂bar uᵢ + Zᵢ uᵢ` for the chart data `uᵢ` of a Sobolev section.

## Main definitions

* `TauCeti.FiniteBundleAtlas.chartZeroOrder`: the zeroth-order term of a real Cauchy–Riemann
  operator in chart `i`.

## Main results

* `TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_dbar_add_chartZeroOrder`: the chart formula.
* `TauCeti.FiniteBundleAtlas.chartZeroOrder_apply_eq_coord_tangentHom`: `Zᵢ v` is the reading of
  `D` on the section reading as the constant `v` in the trivialization of chart `i`, so it does not
  depend on the basis used to define it.
* `TauCeti.FiniteBundleAtlas.chartZeroOrder_transition`: the zeroth-order terms of two charts on
  their overlap.
* `TauCeti.FiniteBundleAtlas.contDiffOn_chartZeroOrder`,
  `TauCeti.FiniteBundleAtlas.exists_norm_chartZeroOrder_apply_le`: smoothness and boundedness of
  the zeroth-order term of a smooth operator.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 and C.2.
-/

public section

noncomputable section

open Bundle Module Set
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold

universe u

namespace TauCeti

namespace FiniteBundleAtlas

section Constant

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V)

/-- The section of `V` which reads as the constant `v` in the trivialization of chart `i` is
differentiable on the base set of that trivialization. -/
theorem mdifferentiableAt_triv_symm [IsManifold 𝓘(ℝ, E) 1 M]
    [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)] (i : Fin A.n) (v : F)
    {x : M} (hx : x ∈ (A.triv i).baseSet) :
    MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x ((A.triv i).symm x v)) x := by
  have h : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) 1
      (fun x ↦ TotalSpace.mk' F x ((A.triv i).symm x v)) (A.triv i).baseSet :=
    ((A.triv i).contMDiffOn_section_baseSet_iff (IB := 𝓘(ℝ, E))).2
      ((contMDiffOn_const (c := v)).congr fun y hy ↦ by simp [(A.triv i).apply_mk_symm hy])
  exact (h.contMDiffAt ((A.triv i).open_baseSet.mem_nhds hx)).mdifferentiableAt one_ne_zero

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- The section reading as the constant `v` in the trivialization of chart `i` reads as `v` on the
image of chart `i`. -/
theorem coord_triv_symm {i : Fin A.n} (v : F) {z : E} (hz : z ∈ A.image i) :
    A.coord i (fun x ↦ (A.triv i).symm x v) z = v := by
  rw [coord_def, (A.triv i).apply_mk_symm (A.dom_subset_baseSet i (A.symm_mem_dom hz))]

end Constant

section Complex

open SmoothAlmostComplexStructure

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  (A : FiniteBundleAtlas E M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}

/-- The zeroth-order term of an operator `D` from sections of `V` to `V`-valued one-forms in chart
`i` of `A`: at `z`, the map sending `v = ∑ k, vᵏ bₖ` to `∑ k, vᵏ • (D eₖ)ᵢ z`, where `b` is the
basis `Module.finBasis ℝ F`, `eₖ` is the frame section of chart `i` reading as `bₖ`, and
`(D eₖ)ᵢ` is the reading of `D eₖ` in chart `i`. For a real Cauchy–Riemann operator it does not
depend on the basis (`TauCeti.FiniteBundleAtlas.chartZeroOrder_apply_eq_coord_tangentHom`). -/
def chartZeroOrder (D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x)
    (i : Fin A.n) (z : E) : F →L[ℝ] E →L[ℝ] F :=
  ∑ k, (LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord k)).smulRight
    (A.tangentHom.coord i (D ((A.triv i).localFrame (finBasis ℝ F) k)) z)

variable [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)]

/-- The reading in chart `i` of the flat Cauchy–Riemann operator of the frame of chart `i` is
the complex antilinear part of the derivative of the reading of the section. -/
theorem inCoordinates_frameCauchyRiemannOperator (i : Fin A.n) {z : E} (hz : z ∈ A.image i)
    {s : Π x, V x} (hs : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) ((A.chart i).symm z)) :
    ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E)) F V (A.center i)
        ((A.chart i).symm z) (A.center i) ((A.chart i).symm z)
        (Manifold.frameCauchyRiemannOperator (ofComplexManifold E M) (finBasis ℝ F) (A.triv i) s
          ((A.chart i).symm z)) =
      complexAntilinearPartL (fderiv ℝ (A.coord i s) z) := by
  set x := (A.chart i).symm z
  set e := A.triv i
  have hxd : x ∈ A.dom i := A.symm_mem_dom hz
  have hx : x ∈ e.baseSet := A.dom_subset_baseSet i hxd
  have hxc : x ∈ (chartAt E (A.center i)).source := A.dom_subset_chart_source i hxd
  have hzt : z ∈ (extChartAt 𝓘(ℝ, E) (A.center i)).target := by
    obtain ⟨y, hy, rfl⟩ := A.mem_image.1 hz
    simpa using (A.chart i).map_source (A.dom_subset_chart_source i hy)
  set g : M → F := fun y ↦ (e ⟨y, s y⟩).2
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) g x := (e.mdifferentiableAt_section_iff _ s hx).1 hs
  have hcoeff (k : Fin (finrank ℝ F)) :
      (fun y ↦ e.localFrameCoeff 𝓘(ℝ, E) (finBasis ℝ F) k y (s y)) =ᶠ[𝓝 x]
        fun y ↦ (finBasis ℝ F).coord k (g y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [e.localFrameCoeff_eq_coeff hy, Basis.coord_apply]
  rw [Manifold.frameCauchyRiemannOperator_apply,
    inCoordinates_zeroOnePart _ (inTangentCoordinates_ofComplexManifold hxc),
    Manifold.frameCovariantDerivative_eq_symmL_comp (finBasis ℝ F) hg.hasMFDerivAt hcoeff hx]
  congr 1
  have hφ := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) hzt
  rw [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] at hφ
  have hφz : (extChartAt 𝓘(ℝ, E) (A.center i)).symm z = x := by simp [x]
  have hcomp : A.coord i s = g ∘ (extChartAt 𝓘(ℝ, E) (A.center i)).symm := by
    ext y
    simp [g, coord_def, e]
  have hd := (hφz ▸ hg).hasMFDerivAt.comp z hφ.hasMFDerivAt
  have hd' : HasFDerivAt (g ∘ (extChartAt 𝓘(ℝ, E) (A.center i)).symm)
      (show E →L[ℝ] F from (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (A.center i)).symm z)) z :=
    hasMFDerivAt_iff_hasFDerivAt.1 hd
  rw [hcomp, hd'.fderiv, ContinuousLinearMap.inCoordinates,
    ← ContinuousLinearMap.comp_assoc, TangentBundle.symmL_trivializationAt hxc]
  have hzx : extChartAt 𝓘(ℝ, E) (A.center i) x = z := by
    simpa [x] using (A.chart i).right_inv (by simpa using hzt)
  rw [hzx]
  ext v
  change (trivializationAt F V (A.center i)).continuousLinearMapAt ℝ x
      ((trivializationAt F V (A.center i)).symmL ℝ x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x
        (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (A.center i)).symm
          (range 𝓘(ℝ, E)) z v))) =
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (A.center i)).symm z v)
  rw [modelWithCornersSelf_coe, range_id, mfderivWithin_univ]
  exact (trivializationAt F V (A.center i)).continuousLinearMapAt_symmL hx _

/-- **The chart formula.** In chart `i`, a real Cauchy–Riemann operator on a complex manifold
reads as `∂bar` of the reading of the section plus the zeroth-order term `chartZeroOrder`. -/
theorem coord_tangentHom_eq_dbar_add_chartZeroOrder
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold E M) D) {i : Fin A.n} {z : E}
    (hz : z ∈ A.image i) {s : Π x, V x}
    (hs : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) ((A.chart i).symm z)) :
    A.tangentHom.coord i (D s) z = complexAntilinearPartL (fderiv ℝ (A.coord i s) z) +
      A.chartZeroOrder D i z (A.coord i s z) := by
  have hx : (A.chart i).symm z ∈ (A.triv i).baseSet := A.dom_subset_baseSet i (A.symm_mem_dom hz)
  rw [coord_tangentHom, hD.eq_frameCauchyRiemannOperator_add_sum (finBasis ℝ F) hx hs,
    ← A.inCoordinates_frameCauchyRiemannOperator i hz hs]
  ext v
  simp only [ContinuousLinearMap.inCoordinates, chartZeroOrder, coord_tangentHom,
    ContinuousLinearMap.comp_apply, add_apply, FunLike.coe_sum,
    Finset.sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    LinearMap.coe_toContinuousLinearMap', map_add, map_sum, map_smul, add_right_inj]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [(A.triv i).localFrameCoeff_eq_coeff hx, Basis.coord_apply, coord_def]

/-- The zeroth-order term of chart `i` applied to `v` is the reading of the operator on the section
reading as the constant `v` in the trivialization of chart `i`. In particular it does not depend on
the basis of `F` used to define it. -/
theorem chartZeroOrder_apply_eq_coord_tangentHom
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold E M) D) {i : Fin A.n} {z : E}
    (hz : z ∈ A.image i) (v : F) :
    A.chartZeroOrder D i z v = A.tangentHom.coord i (D fun x ↦ (A.triv i).symm x v) z := by
  have hc : A.coord i (fun x ↦ (A.triv i).symm x v) =ᶠ[𝓝 z] fun _ ↦ v := by
    filter_upwards [(A.image i).isOpen.mem_nhds hz] with y hy using A.coord_triv_symm v hy
  rw [A.coord_tangentHom_eq_dbar_add_chartZeroOrder hD hz
    (A.mdifferentiableAt_triv_symm i v (A.dom_subset_baseSet i (A.symm_mem_dom hz))),
    hc.fderiv_eq, fderiv_const_apply, map_zero, zero_add, A.coord_triv_symm v hz]

/-- **Change of chart.** On the overlap of charts `i` and `i'`, let `g` be the coordinate change of
`V` from the trivialization of chart `i` to that of chart `i'`, read in chart `i'`, and let `τ` be
the chart transition. The zeroth-order terms of the two charts are related by
`∂bar (g v) + Z' (g v) = g ∘ Z v ∘ dτ`: the frame of chart `i` is not flat for the frame of chart
`i'`, and `∂bar g` is the difference. -/
theorem chartZeroOrder_transition
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold E M) D) {i i' : Fin A.n} {z : E}
    (hz : z ∈ A.overlap i i') (v : F) :
    complexAntilinearPartL (fderiv ℝ
        (fun y ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) v) z) +
      A.chartZeroOrder D i' z ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) v) =
    ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) : F →L[ℝ] F).comp
      ((A.chartZeroOrder D i (A.transition i i' z) v).comp (fderiv ℝ (A.transition i i') z)) := by
  have hz' : z ∈ A.image i' := A.overlap_subset_image i i' hz
  have hτ : A.transition i i' z ∈ A.image i :=
    A.overlap_subset_image i' i (A.transition_mem_overlap hz)
  have hx : (A.chart i').symm z ∈ (A.triv i).baseSet := by
    obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 hz
    rw [(A.chart i').left_inv (A.dom_subset_chart_source i' hx.2)]
    exact A.dom_subset_baseSet i hx.1
  have hc : A.coord i' (fun x ↦ (A.triv i).symm x v) =ᶠ[𝓝 z]
      fun y ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) v := by
    filter_upwards [(A.isOpen_overlap i i').mem_nhds hz] with y hy
    rw [A.coord_eq_coordChange _ hy,
      A.coord_triv_symm v (A.overlap_subset_image i' i (A.transition_mem_overlap hy))]
  rw [← hc.fderiv_eq, ← hc.eq_of_nhds,
    ← A.coord_tangentHom_eq_dbar_add_chartZeroOrder hD hz' (A.mdifferentiableAt_triv_symm i v hx),
    A.coord_tangentHom_of_mem_overlap _ hz, A.chartZeroOrder_apply_eq_coord_tangentHom hD hτ]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℂ F V] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)] in
/-- The readings of the operator on the frame sections of chart `i` are `C^n` where the operator
is. -/
private theorem contDiffOn_coord_tangentHom_localFrame [FiniteDimensional ℝ E] [T2Space M]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold E M) D) {n : ℕ∞} {u : Set M}
    (hDs : ContMDiffCovariantDerivativeOn F n D u) (hu : IsOpen u) (i : Fin A.n)
    (k : Fin (finrank ℝ F)) :
    ContDiffOn ℝ n (A.tangentHom.coord i (D ((A.triv i).localFrame (finBasis ℝ F) k)))
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' ((A.triv i).baseSet ∩ u)) := by
  set a : Set M := (A.chart i).source ∩ ((A.triv i).baseSet ∩ u)
  have ha : IsOpen a := (A.chart i).open_source.inter ((A.triv i).open_baseSet.inter hu)
  have hDa : ContMDiffCovariantDerivativeOn F n D a :=
    hD.contMDiffCovariantDerivativeOn_mono_of_isOpen hDs ha fun x hx ↦ hx.2.2
  have hframe := (((A.triv i).contMDiffOn_localFrame_baseSet (I := 𝓘(ℝ, E)) ∞
    (finBasis ℝ F) k).of_le
      (show (n : ℕ∞ω) + 1 ≤ ∞ from mod_cast (le_top : n + 1 ≤ ⊤))).mono
      (show a ⊆ (A.triv i).baseSet from fun x hx ↦ hx.2.1)
  have hω := ((A.tangentHom.triv i).contMDiffOn_section_iff ha ?_).1 (hDa.contMDiff hframe)
  · exact ((hω.contDiffOn_comp_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas _)).congr fun y _ ↦ (A.tangentHom.coord_def i _ y)).mono
        fun y hy ↦ ⟨hy.1, (A.chart i).map_target hy.1, hy.2⟩
  · intro x hx
    simp only [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet]
    exact ⟨hx.1, hx.2.1⟩

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℂ F V] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)] in
/-- **Smoothness of the zeroth-order term.** If a real Cauchy–Riemann operator is `C^n` on an open
set `u`, its zeroth-order term in chart `i` is `C^n` on the points of the chart target lying over
`u` and the base set of the trivialization of chart `i`. -/
theorem contDiffOn_chartZeroOrder [FiniteDimensional ℝ E] [T2Space M]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold E M) D) {n : ℕ∞} {u : Set M}
    (hDs : ContMDiffCovariantDerivativeOn F n D u) (hu : IsOpen u) (i : Fin A.n) :
    ContDiffOn ℝ n (A.chartZeroOrder D i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' ((A.triv i).baseSet ∩ u)) :=
  ContDiffOn.sum fun k _ ↦ contDiffOn_const.smulRight
    (A.contDiffOn_coord_tangentHom_localFrame hD hDs hu i k)

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℂ F V] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)] in
/-- **Boundedness of the zeroth-order term.** The zeroth-order term in chart `i` of a real
Cauchy–Riemann operator which is `C^n` on `M` is bounded on the closure of the image of chart `i`,
a compact subset of the open set where it is continuous. -/
theorem exists_norm_chartZeroOrder_apply_le [FiniteDimensional ℝ E] [T2Space M]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold E M) D) {n : ℕ∞}
    (hDs : ContMDiffCovariantDerivativeOn F n D univ) (i : Fin A.n) :
    ∃ C, ∀ z ∈ closure (A.image i : Set E), ∀ v, ‖A.chartZeroOrder D i z v‖ ≤ C * ‖v‖ := by
  set c : Fin (finrank ℝ F) → F →L[ℝ] ℝ := fun k ↦
    LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord k)
  have hT (k : Fin (finrank ℝ F)) : ∃ C, ∀ z ∈ A.chart i '' closure (A.dom i),
      ‖A.tangentHom.coord i (D ((A.triv i).localFrame (finBasis ℝ F) k)) z‖ ≤ C := by
    have hc := (A.contDiffOn_coord_tangentHom_localFrame hD hDs isOpen_univ i k).continuousOn
    rw [inter_univ] at hc
    exact (A.isCompact_chart_image_closure_dom i).exists_bound_of_continuousOn
      (hc.mono (A.chart_image_closure_dom_subset i))
  choose C hC using hT
  refine ⟨∑ k, ‖c k‖ * max (C k) 0, fun z hz v ↦ ?_⟩
  have hzK := A.closure_image_subset_chart_image_closure_dom i hz
  calc ‖A.chartZeroOrder D i z v‖
      = ‖∑ k, c k v • A.tangentHom.coord i (D ((A.triv i).localFrame (finBasis ℝ F) k)) z‖ := by
        simp [chartZeroOrder, c]
    _ ≤ ∑ k, ‖c k v‖ * ‖A.tangentHom.coord i (D ((A.triv i).localFrame (finBasis ℝ F) k)) z‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ (norm_smul (c k v) _).le)
    _ ≤ ∑ k, (‖c k‖ * ‖v‖) * max (C k) 0 :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul ((c k).le_opNorm v)
          ((hC k z hzK).trans (le_max_left _ _)) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ k, ‖c k‖ * max (C k) 0) * ‖v‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ ↦ by ring

end Complex

end FiniteBundleAtlas

end TauCeti
