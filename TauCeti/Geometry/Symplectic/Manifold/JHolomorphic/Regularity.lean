/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import TauCeti.Geometry.Manifold.Complex.Isothermal
import TauCeti.Geometry.Symplectic.JHolomorphic.Regularity
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# Smoothness of `C¹` pseudoholomorphic curves between almost complex manifolds

Let `M` be a smooth real surface equipped with a smooth almost complex structure `j`, and let `M'`
be a finite-dimensional smooth manifold without boundary equipped with a smooth almost complex
structure `J`. This file proves that every `C¹` `(j, J)`-holomorphic map `u : M → M'` on an open
subset of `M` is `C^n` for every `n : ℕ∞`, and in particular smooth (`ContMDiffOn 𝓘(ℝ, ℂ) I' ∞`).

The proof reduces manifold regularity to the planar nonlinear elliptic bootstrap
(`TauCeti.IsJHolomorphicOn.contDiffOn` in `TauCeti.Geometry.Symplectic.JHolomorphic.Regularity`) in
two steps:

1. For curves from `(ℂ, SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ)` into `M'`, composing
   `u` with an extended chart `φ := extChartAt I' (u z₀)` yields a `C¹` map `φ ∘ u` satisfying the
   varying-structure normed-space Cauchy–Riemann equation on `s ∩ u ⁻¹' φ.source` for the chart
   coefficient `J.inChart (u z₀)` (smooth on `φ.target`), which bootstraps to `C^∞`.
2. For an isothermal chart `e : OpenPartialHomeomorph M ℂ` of `(M, j)`
   (`SmoothAlmostComplexStructure.exists_isIsothermalChart`), `e` belongs to the `C^∞` maximal
   atlas (`TauCeti.IsIsothermalChart.mem_maximalAtlas_infty`). Hence `u ∘ e.symm` is `C¹` and
   pseudoholomorphic from `ℂ`, so `C^∞` by step 1, and composing with `e` makes
   `u = (u ∘ e.symm) ∘ e` smooth near every point of the open domain.

## Main results

* `TauCeti.IsPseudoholomorphicOn.contMDiffOn`, `TauCeti.IsPseudoholomorphic.contMDiff`: a `C¹`
  pseudoholomorphic map from an open subset (or all) of an almost complex surface into a
  finite-dimensional smooth almost complex manifold without boundary is `C^n` for every `n : ℕ∞`.
* `TauCeti.IsPseudoholomorphicOn.contDiffOn`, `TauCeti.IsPseudoholomorphic.contDiff`: the planar
  specializations for maps `ℂ → V` into a finite-dimensional real normed space `V`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1 and Remark B.4.3).
-/

public noncomputable section

open Complex Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

private theorem contMDiffOn_of_isPseudoholomorphicOn_ofComplexManifold
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {s : Set ℂ} {u : ℂ → M'}
    (h : IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) J u s)
    (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I' 1 u s) :
    ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ u s := by
  classical
  intro z₀ hz₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  let φ := extChartAt I' (u z₀)
  let U : Set ℂ := s ∩ u ⁻¹' φ.source
  let W : Set E' := φ.target
  let v : ℂ → E' := φ ∘ u
  have hφ_src : IsOpen φ.source := isOpen_extChartAt_source (I := I') (u z₀)
  have hW : IsOpen W := isOpen_extChartAt_target (I := I') (u z₀)
  have hU : IsOpen U := hu.continuousOn.isOpen_inter_preimage hs hφ_src
  have hz₀U : z₀ ∈ U := ⟨hz₀, mem_extChartAt_source (u z₀)⟩
  have hvW : MapsTo v U W := fun z hz => φ.map_source hz.2
  have hφ_c1 : ContMDiffOn I' 𝓘(ℝ, E') 1 φ φ.source := by
    rw [extChartAt_source]
    exact (contMDiffOn_extChartAt (I := I') (x := u z₀)).of_le (WithTop.coe_le_coe.2 le_top)
  have hv_c1 : ContDiffOn ℝ 1 v U :=
    contMDiffOn_iff_contDiffOn.1 (hφ_c1.comp (hu.mono inter_subset_left) inter_subset_right)
  let J₀ : AlmostComplexStructure E' :=
    ⟨(J.inChart (u z₀) (φ (u z₀))).toLinearMap,
      LinearMap.ext fun w => J.inChart_inChart (u z₀) (mem_extChartAt_target (u z₀)) w⟩
  let J_chart : E' → AlmostComplexStructure E' := fun y =>
    if hy : y ∈ W then
      ⟨(J.inChart (u z₀) y).toLinearMap,
        LinearMap.ext fun w => J.inChart_inChart (u z₀) hy w⟩
    else J₀
  have hJ_chart_eq : EqOn (fun y => LinearMap.toContinuousLinearMap (J_chart y).toLinearMap)
      (J.inChart (u z₀)) W := fun y hy => by
    ext w
    simp [J_chart, hy]
  have hJ_chart_smooth :
      ContDiffOn ℝ ∞ (fun y => LinearMap.toContinuousLinearMap (J_chart y).toLinearMap) W :=
    (J.contDiffOn_inChart (u z₀)).congr hJ_chart_eq
  have hv_hol :
      IsJHolomorphicOn (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J_chart v U := by
    refine (isJHolomorphicOn_iff _ _ _ _).2 fun z hz => ?_
    have hv_diff : DifferentiableAt ℝ v z :=
      (hv_c1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz)
    have hu_at : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) J u z :=
      (h.isPseudoholomorphicWithinAt hz.1).isPseudoholomorphicAt_of_mem_nhds (hs.mem_nhds hz.1)
    refine (isJHolomorphicAt_of_hasFDerivAt hv_diff.hasFDerivAt ?_).isJHolomorphicWithinAt
    refine (isComplexLinearMap_iff_apply _ _ _).2 fun w => ?_
    have hchart := J.fderiv_extChartAt_comp_apply_eq_inChart (u z₀) hu_at.continuousAt hz.2
      (hu_at.mfderiv_apply_commute w)
    have hI : AlmostComplexStructure.ofComplexModule ℂ w =
        SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ z w := by
      rw [AlmostComplexStructure.ofComplexModule_apply,
        SmoothAlmostComplexStructure.ofComplexManifold_apply]
    have hJy : J_chart (v z) (fderiv ℝ v z w) = J.inChart (u z₀) (v z) (fderiv ℝ v z w) := by
      simp [J_chart, hvW hz]
    rw [ContinuousLinearMap.coe_coe, hI, hJy]
    exact hchart
  have hv_smooth : ContDiffOn ℝ ∞ v U := hv_hol.contDiffOn hU hW hJ_chart_smooth hv_c1 hvW
  have hv_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E') ∞ v z₀ :=
    contMDiffAt_iff_contDiffAt.2 (hv_smooth.contDiffAt (hU.mem_nhds hz₀U))
  have hφ_symm : ContMDiffAt 𝓘(ℝ, E') I' ∞ φ.symm (v z₀) :=
    (contMDiffOn_extChartAt_symm (I := I') (u z₀)).contMDiffAt (hW.mem_nhds (hvW hz₀U))
  have h_eq : u =ᶠ[nhds z₀] φ.symm ∘ v := by
    filter_upwards [hU.mem_nhds hz₀U] with z hz
    exact (φ.left_inv hz.2).symm
  exact (hφ_symm.comp z₀ hv_at).congr_of_eventuallyEq h_eq

/-- **Smoothness of `C¹` pseudoholomorphic curves between almost complex manifolds.** Let `M` be a
smooth real surface carrying a smooth almost complex structure `j`, and let `M'` be a
finite-dimensional smooth manifold without boundary carrying a smooth almost complex structure `J`.
If `u : M → M'` is `C¹` and `(j, J)`-holomorphic on an open set `s ⊆ M`, then `u` is `C^n` on `s`
for every `n : ℕ∞` (McDuff–Salamon, Theorem B.4.1). -/
theorem IsPseudoholomorphicOn.contMDiffOn
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M}
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {s : Set M} {n : ℕ∞} {u : M → M'}
    (h : IsPseudoholomorphicOn j J u s) (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I' 1 u s) :
    ContMDiffOn 𝓘(ℝ, ℂ) I' n u s := by
  suffices ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ u s from this.of_le (WithTop.coe_le_coe.2 le_top)
  intro x₀ hx₀s
  refine ContMDiffAt.contMDiffWithinAt ?_
  obtain ⟨e, he, hx₀⟩ := j.exists_isIsothermalChart x₀
  let T : Set ℂ := e.target ∩ e.symm ⁻¹' s
  have hT : IsOpen T := e.isOpen_inter_preimage_symm hs
  have h_comp_c1 : ContMDiffOn 𝓘(ℝ, ℂ) I' 1 (u ∘ e.symm) T :=
    hu.comp ((contMDiffOn_symm_of_mem_maximalAtlas he.mem_maximalAtlas).mono inter_subset_left)
      inter_subset_right
  have h_comp_hol :
      IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) J
        (u ∘ e.symm) T :=
    isPseudoholomorphicOn_iff.2 fun z hz =>
      (((h.isPseudoholomorphicWithinAt hz.2).isPseudoholomorphicAt_of_mem_nhds
        (hs.mem_nhds hz.2)).comp
          (he.isPseudoholomorphicAt_symm hz.1)).isPseudoholomorphicWithinAt
  have h_comp_smooth : ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ (u ∘ e.symm) T :=
    contMDiffOn_of_isPseudoholomorphicOn_ofComplexManifold h_comp_hol hT h_comp_c1
  have hz₀T : e x₀ ∈ T := ⟨e.map_source hx₀, by simpa [e.left_inv hx₀] using hx₀s⟩
  have h_comp_at : ContMDiffAt 𝓘(ℝ, ℂ) I' ∞ (u ∘ e.symm) (e x₀) :=
    h_comp_smooth.contMDiffAt (hT.mem_nhds hz₀T)
  have he_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e x₀ :=
    contMDiffAt_of_mem_maximalAtlas he.mem_maximalAtlas_infty hx₀
  have hu_eq : u =ᶠ[nhds x₀] (u ∘ e.symm) ∘ e := by
    filter_upwards [e.open_source.mem_nhds hx₀] with x hx
    simp [e.left_inv hx]
  exact (h_comp_at.comp x₀ he_at).congr_of_eventuallyEq hu_eq

/-- **Smoothness of global `C¹` pseudoholomorphic curves between almost complex manifolds.** If `M`
is a smooth real surface with a smooth almost complex structure `j`, `M'` is a finite-dimensional
smooth manifold without boundary with a smooth almost complex structure `J`, and `u : M → M'` is
`C¹` and `(j, J)`-holomorphic, then `u` is `C^n` for every `n : ℕ∞`. -/
theorem IsPseudoholomorphic.contMDiff
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M}
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {n : ℕ∞} {u : M → M'}
    (h : IsPseudoholomorphic j J u) (hu : ContMDiff 𝓘(ℝ, ℂ) I' 1 u) :
    ContMDiff 𝓘(ℝ, ℂ) I' n u :=
  contMDiffOn_univ.1 <| (h.isPseudoholomorphicOn univ).contMDiffOn isOpen_univ hu.contMDiffOn

section Planar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Smoothness of `C¹` pseudoholomorphic maps on planar open sets.** If `j` is a smooth almost
complex structure on `ℂ`, `J` is a smooth almost complex structure on a finite-dimensional real
normed space `V`, and `u : ℂ → V` is `C¹` and `(j, J)`-holomorphic on an open set `s ⊆ ℂ`, then
`u` is `C^n` on `s` for every `n : ℕ∞`. -/
theorem IsPseudoholomorphicOn.contDiffOn [FiniteDimensional ℝ V]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ}
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {s : Set ℂ} {n : ℕ∞} {u : ℂ → V}
    (h : IsPseudoholomorphicOn j J u s) (hs : IsOpen s) (hu : ContDiffOn ℝ 1 u s) :
    ContDiffOn ℝ n u s :=
  contMDiffOn_iff_contDiffOn.1 (h.contMDiffOn hs (contMDiffOn_iff_contDiffOn.2 hu))

/-- **Smoothness of global `C¹` pseudoholomorphic maps from `ℂ`.** If `j` is a smooth almost
complex structure on `ℂ`, `J` is a smooth almost complex structure on a finite-dimensional real
normed space `V`, and `u : ℂ → V` is `C¹` and `(j, J)`-holomorphic, then `u` is `C^n` for every
`n : ℕ∞`. -/
theorem IsPseudoholomorphic.contDiff [FiniteDimensional ℝ V]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ}
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {n : ℕ∞} {u : ℂ → V}
    (h : IsPseudoholomorphic j J u) (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ n u :=
  contMDiff_iff_contDiff.1 (h.contMDiff (contMDiff_iff_contDiff.2 hu))

end Planar

end TauCeti
