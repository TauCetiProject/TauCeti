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
covariant derivative of the frame of chart `i` reads as the derivative of the reading
(`TauCeti.FiniteBundleAtlas.inCoordinates_frameCovariantDerivative`). On the overlap of two
charts, the zeroth-order terms are related through the coordinate change `g` of `V` and the
derivative of the chart transition, up to `∂bar g`
(`TauCeti.FiniteBundleAtlas.complexAntilinearPartL_fderiv_coordChangeL_add_chartZeroOrder`).
For a real Cauchy–Riemann operator on a real manifold with any smooth almost complex structure,
sending smooth sections to smooth one-forms, the zeroth-order term of a chart is smooth, and
bounded on the closure of the image of the chart.

This is the chart calculus behind the realization of a smooth real Cauchy–Riemann operator as a
bounded operator between Sobolev spaces of sections, whose chart data are
`∂bar uᵢ + Zᵢ uᵢ` for the chart data `uᵢ` of a Sobolev section.

## Main definitions

* `TauCeti.FiniteBundleAtlas.chartZeroOrder`: the zeroth-order term of an operator from sections
  of `V` to `V`-valued one-forms in chart `i`.

## Main results

* `TauCeti.FiniteBundleAtlas.inCoordinates_frameCovariantDerivative`: the flat covariant derivative
  of the frame of chart `i` reads in chart `i` as the derivative of the reading of the section.
* `TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder`:
  the chart formula.
* `TauCeti.FiniteBundleAtlas.chartZeroOrder_apply_eq_coord_tangentHom`: on the image of chart `i`,
  `Zᵢ v` is the reading of `D` on the section reading as the constant `v` in the trivialization of
  chart `i`, so it does not depend on the basis used to define it.
* `TauCeti.FiniteBundleAtlas.complexAntilinearPartL_fderiv_coordChangeL_add_chartZeroOrder`: the
  zeroth-order terms of two charts on their overlap.
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

section Real

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V)

/-- The zeroth-order term of an operator `D` from sections of `V` to `V`-valued one-forms in chart
`i` of `A`: at `z`, the map sending `v = ∑ k, vᵏ bₖ` to `∑ k, vᵏ • (D eₖ)ᵢ z`, where `b` is the
basis `Module.finBasis ℝ F`, `eₖ` is the frame section of chart `i` reading as `bₖ`, and
`(D eₖ)ᵢ` is the reading of `D eₖ` in chart `i`. For a real Cauchy–Riemann operator on a complex
manifold, its values on the image of chart `i` do not depend on the basis
(`TauCeti.FiniteBundleAtlas.chartZeroOrder_apply_eq_coord_tangentHom`). -/
def chartZeroOrder (D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x)
    (i : Fin A.n) (z : E) : F →L[ℝ] E →L[ℝ] F :=
  ∑ k, (LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord k)).smulRight
    (A.tangentHom.coord i (D ((A.triv i).localFrame (finBasis ℝ F) k)) z)

theorem chartZeroOrder_apply (D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x)
    (i : Fin A.n) (z : E) (v : F) :
    A.chartZeroOrder D i z v =
      ∑ k, (finBasis ℝ F).coord k v •
        A.tangentHom.coord i (D ((A.triv i).localFrame (finBasis ℝ F) k)) z := by
  simp [chartZeroOrder]

omit [FiniteDimensional ℝ F] in
/-- The reading in chart `i` of the flat covariant derivative of the frame of chart `i` is the
derivative of the reading of the section. -/
theorem inCoordinates_frameCovariantDerivative [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)]
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ F) (i : Fin A.n) {z : E} (hz : z ∈ A.image i)
    {s : Π x, V x} (hs : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) ((A.chart i).symm z)) :
    ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E)) F V (A.center i)
        ((A.chart i).symm z) (A.center i) ((A.chart i).symm z)
        (Manifold.frameCovariantDerivative 𝓘(ℝ, E) b (A.triv i) s ((A.chart i).symm z)) =
      fderiv ℝ (A.coord i s) z := by
  set x := (A.chart i).symm z
  set e := A.triv i
  have hxd : x ∈ A.dom i := A.symm_mem_dom hz
  have hx : x ∈ e.baseSet := A.dom_subset_baseSet i hxd
  have hxc : x ∈ (chartAt E (A.center i)).source := A.dom_subset_chart_source i hxd
  have hzt : z ∈ (extChartAt 𝓘(ℝ, E) (A.center i)).target := by
    simpa using A.closure_image_subset_target i (subset_closure hz)
  -- First, the frame derivative is the derivative of the fibre coordinate `g` of `s` in `e`,
  -- carried back to `V` by `e`.
  set g : M → F := fun y ↦ (e ⟨y, s y⟩).2
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) g x := (e.mdifferentiableAt_section_iff _ s hx).1 hs
  have hcoeff (k : ι) : (fun y ↦ e.localFrameCoeff 𝓘(ℝ, E) b k y (s y)) =ᶠ[𝓝 x]
      fun y ↦ b.coord k (g y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [e.localFrameCoeff_eq_coeff hy, Basis.coord_apply]
  rw [Manifold.frameCovariantDerivative_eq_symmL_comp b hg.hasMFDerivAt hcoeff hx]
  -- Second, the reading of `s` is `g` composed with the inverse of the extended chart, so its
  -- derivative is the chain rule composite.
  have hφ := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) hzt
  rw [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] at hφ
  have hφz : (extChartAt 𝓘(ℝ, E) (A.center i)).symm z = x := by simp [x]
  have hcomp : A.coord i s = g ∘ (extChartAt 𝓘(ℝ, E) (A.center i)).symm := by
    ext y
    simp [g, coord_def, e]
  have hd := (hφz ▸ hg).hasMFDerivAt.comp z hφ.hasMFDerivAt
  -- The manifold derivatives between model spaces are maps `E →L[ℝ] F` up to the `TangentSpace`
  -- type synonyms, which `hasMFDerivAt_iff_hasFDerivAt` needs to see through.
  have hd' : HasFDerivAt (g ∘ (extChartAt 𝓘(ℝ, E) (A.center i)).symm)
      (show E →L[ℝ] F from (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (A.center i)).symm z)) z :=
    hasMFDerivAt_iff_hasFDerivAt.1 hd
  -- Third, the trivializations of the tangent bundle and of `V` at the centre cancel the chart
  -- derivative and `e` in the reading.
  rw [hcomp, hd'.fderiv, ContinuousLinearMap.inCoordinates,
    ← ContinuousLinearMap.comp_assoc, TangentBundle.symmL_trivializationAt hxc]
  have hzx : extChartAt 𝓘(ℝ, E) (A.center i) x = z := by
    simpa [x] using (A.chart i).right_inv (by simpa using hzt)
  rw [hzx]
  ext v
  -- Unfold the compositions; the tangent space of the model space is `E` by definition.
  change (trivializationAt F V (A.center i)).continuousLinearMapAt ℝ x
      ((trivializationAt F V (A.center i)).symmL ℝ x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x
        (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (A.center i)).symm
          (range 𝓘(ℝ, E)) z v))) =
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (A.center i)).symm z v)
  rw [modelWithCornersSelf_coe, range_id, mfderivWithin_univ]
  exact (trivializationAt F V (A.center i)).continuousLinearMapAt_symmL hx _

end Real

section Smooth

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {j : SmoothAlmostComplexStructure 𝓘(ℝ, E) M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}
  {n : ℕ∞ω} [ENat.LEInfty n]

/-- **Smoothness of the zeroth-order term.** If a real Cauchy–Riemann operator is `C^n` on an open
set `u`, its zeroth-order term in chart `i` is `C^n` on the points of the chart target lying over
`u` and the base set of the trivialization of chart `i`. -/
theorem contDiffOn_chartZeroOrder (hD : IsRealCauchyRiemannOperator F j D) {u : Set M}
    (hDs : ContMDiffCovariantDerivativeOn F n D u) (hu : IsOpen u) (i : Fin A.n) :
    ContDiffOn ℝ n (A.chartZeroOrder D i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' ((A.triv i).baseSet ∩ u)) := by
  lift n to ℕ∞ using ne_top_of_le_ne_top WithTop.coe_ne_top ENat.LEInfty.out
  set a : Set M := (A.chart i).source ∩ ((A.triv i).baseSet ∩ u)
  have ha : IsOpen a := (A.chart i).open_source.inter ((A.triv i).open_baseSet.inter hu)
  have hDa : ContMDiffCovariantDerivativeOn F n D a :=
    hD.contMDiffCovariantDerivativeOn_mono_of_isOpen hDs ha fun x hx ↦ hx.2.2
  -- Each frame section is smooth over the base set, so `D` sends it to a `C^n` one-form on `a`,
  -- whose reading in chart `i` is `C^n`.
  refine ContDiffOn.sum fun k _ ↦ contDiffOn_const.smulRight ?_
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

/-- **Boundedness of the zeroth-order term.** The zeroth-order term in chart `i` of a real
Cauchy–Riemann operator which is `C^n` on `M` is bounded on the closure of the image of chart `i`,
a compact subset of the open set where it is continuous. -/
theorem exists_norm_chartZeroOrder_apply_le (hD : IsRealCauchyRiemannOperator F j D)
    (hDs : ContMDiffCovariantDerivativeOn F n D univ) (i : Fin A.n) :
    ∃ C, ∀ z ∈ closure (A.image i : Set E), ∀ v, ‖A.chartZeroOrder D i z v‖ ≤ C * ‖v‖ := by
  have hc := (A.contDiffOn_chartZeroOrder hD hDs isOpen_univ i).continuousOn
  rw [inter_univ] at hc
  obtain ⟨C, hC⟩ := (A.isCompact_chart_image_closure_dom i).exists_bound_of_continuousOn
    (f := A.chartZeroOrder D i) (hc.mono (A.chart_image_closure_dom_subset i))
  exact ⟨C, fun z hz v ↦ (A.chartZeroOrder D i z).le_of_opNorm_le
    (hC z (A.closure_image_subset_chart_image_closure_dom i hz)) v⟩

end Smooth

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
  [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}

/-- **The chart formula.** In chart `i`, a real Cauchy–Riemann operator on a complex manifold
reads as `∂bar` of the reading of the section plus the zeroth-order term `chartZeroOrder`. -/
theorem coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold E M) D) {i : Fin A.n} {z : E}
    (hz : z ∈ A.image i) {s : Π x, V x}
    (hs : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) ((A.chart i).symm z)) :
    A.tangentHom.coord i (D s) z = complexAntilinearPartL (fderiv ℝ (A.coord i s) z) +
      A.chartZeroOrder D i z (A.coord i s z) := by
  have hxd : (A.chart i).symm z ∈ A.dom i := A.symm_mem_dom hz
  have hx : (A.chart i).symm z ∈ (A.triv i).baseSet := A.dom_subset_baseSet i hxd
  rw [coord_tangentHom, hD.eq_frameCauchyRiemannOperator_add_sum (finBasis ℝ F) hx hs,
    ← A.inCoordinates_frameCovariantDerivative (finBasis ℝ F) i hz hs,
    ← inCoordinates_zeroOnePart _
      (inTangentCoordinates_ofComplexManifold (A.dom_subset_chart_source i hxd)),
    ← Manifold.frameCauchyRiemannOperator_apply]
  ext v
  simp only [ContinuousLinearMap.inCoordinates, chartZeroOrder_apply, coord_tangentHom,
    ContinuousLinearMap.comp_apply, add_apply, FunLike.coe_sum, Finset.sum_apply, smul_apply,
    map_add, map_sum, map_smul, add_right_inj]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [(A.triv i).localFrameCoeff_eq_coeff hx, Basis.coord_apply, coord_def]

/-- On the image of chart `i`, the zeroth-order term of chart `i` applied to `v` is the reading of
the operator on the section reading as the constant `v` in the trivialization of chart `i`. In
particular it does not depend on the basis of `F` used to define it. -/
theorem chartZeroOrder_apply_eq_coord_tangentHom
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold E M) D) {i : Fin A.n} {z : E}
    (hz : z ∈ A.image i) (v : F) :
    A.chartZeroOrder D i z v = A.tangentHom.coord i (D fun x ↦ (A.triv i).symm x v) z := by
  have hc : A.coord i (fun x ↦ (A.triv i).symm x v) =ᶠ[𝓝 z] fun _ ↦ v := by
    filter_upwards [(A.image i).isOpen.mem_nhds hz] with y hy using A.coord_triv_symm v hy
  rw [A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hz
    (Manifold.mdifferentiableAt_symm_of_mem_baseSet v
      (A.dom_subset_baseSet i (A.symm_mem_dom hz))),
    hc.fderiv_eq, fderiv_const_apply, map_zero, zero_add, A.coord_triv_symm v hz]

/-- **Change of chart.** On the overlap of charts `i` and `i'`, let `g` be the coordinate change of
`V` from the trivialization of chart `i` to that of chart `i'`, read in chart `i'`, and let `τ` be
the chart transition. The zeroth-order terms of the two charts are related by
`∂bar (g v) + Z' (g v) = g ∘ Z v ∘ dτ`. -/
theorem complexAntilinearPartL_fderiv_coordChangeL_add_chartZeroOrder
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
    ← A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hz'
      (Manifold.mdifferentiableAt_symm_of_mem_baseSet v hx),
    A.coord_tangentHom_eq_coordChange _ hz, A.chartZeroOrder_apply_eq_coord_tangentHom hD hτ]

end Complex

end FiniteBundleAtlas

end TauCeti
