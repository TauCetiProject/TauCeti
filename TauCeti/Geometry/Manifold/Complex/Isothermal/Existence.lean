/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Isothermal.Basic
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Complex.Beltrami.Isothermal
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# Existence of isothermal charts on an almost complex surface

Let `M` be a real surface, a smooth manifold modelled on `𝓘(ℝ, ℂ)`, with a smooth almost complex
structure `j`. This file proves that every point of `M` lies in the source of an isothermal chart
of `j`, a chart of the real `C¹` maximal atlas in which `j` is multiplication by `i`
(`TauCeti.exists_isIsothermalChart`). That is, every almost complex structure on a surface is
integrable: the instance `TauCeti.SmoothAlmostComplexStructure.hasIsothermalCharts` makes
`TauCeti.IsothermalSurface j` a complex analytic curve, and the identity of `M` a real `C¹`
diffeomorphism from it carrying its complex structure to `j`, for every `j`
(`TauCeti.IsothermalSurface.diffeomorph`,
`TauCeti.IsothermalSurface.isPseudoholomorphic_homeomorph`).
No orientability hypothesis is needed: `j` itself orients `M`.

The proof reads `j` in the chart `ψ` of `M` at a point `x`: the pushforward `A = dψ ∘ j ∘ dψ⁻¹`
(`TauCeti.SmoothAlmostComplexStructure.chartPushforward`) is a smooth field of complex structures
on the open target of `ψ`. The Beltrami equation gives a planar `C¹` chart `e` at `ψ x` with
invertible derivative in which `A` is multiplication by `i`
(`TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt`). By the inverse function theorem its
inverse is `C¹` as well, so `ψ` followed by `e` is a chart of the real `C¹` maximal atlas, and its
derivative intertwines `j` with `i` by the chain rule.

## Main results

* `TauCeti.exists_isIsothermalChart`: every point of an almost complex surface lies in the source of
  an isothermal chart.
* `TauCeti.SmoothAlmostComplexStructure.hasIsothermalCharts`: every smooth almost complex structure
  on a surface has isothermal charts.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix E.
* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
-/

public section

open Complex IsManifold Set
open scoped ContDiff Manifold

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
  (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M)

/-- **`j` read in a chart.** In the chart `ψ` of `M` at `x`, the derivative of `ψ` carries `j` to a
field `J` of complex structures on the plane which is `C¹` at `ψ x`: `J` is the pushforward
`dψ ∘ j ∘ dψ⁻¹` on the target of `ψ`, extended arbitrarily outside it. -/
private theorem exists_almostComplexStructure_mfderiv_chartAt (x : M) :
    ∃ J : ℂ → AlmostComplexStructure ℂ,
      ContDiffAt ℝ 1 (fun p ↦ LinearMap.toContinuousLinearMap (J p).toLinearMap) (chartAt ℂ x x) ∧
      ∀ y ∈ (chartAt ℂ x).source, ∀ w : TangentSpace 𝓘(ℝ, ℂ) y,
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ x) y (j y w) =
          J (chartAt ℂ x y) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ x) y w) := by
  classical
  set ψ := chartAt ℂ x
  have hψ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ ψ.source := contMDiffOn_chart
  have hψs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ.symm ψ.target := contMDiffOn_chart_symm
  have hdψ (y : M) (hy : y ∈ ψ.source) : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ y :=
    (hψ.contMDiffAt (ψ.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
  have hdψs (p : ℂ) (hp : p ∈ ψ.target) : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm p :=
    (hψs.contMDiffAt (ψ.open_target.mem_nhds hp)).mdifferentiableAt (by simp)
  have hx : ψ x ∈ ψ.target := ψ.map_source (mem_chart_source ℂ x)
  -- `j` read in `ψ` is a smooth field of complex structures `A` on the target of `ψ`.
  set A := j.chartPushforward ψ
  have hA : ContDiffOn ℝ ∞ A ψ.target := j.contDiffOn_chartPushforward hψ hψs
  have hAsq (p : ℂ) (hp : p ∈ ψ.target) (w : ℂ) : A p (A p w) = -w := by
    simpa only [A, SmoothAlmostComplexStructure.toContMDiff_chartPushforward] using
      (j.toContMDiff ⊤).chartPushforward_apply_chartPushforward_apply ψ hp
        (by simpa only [ψ.right_inv hp] using hdψ _ (ψ.map_target hp)) (hdψs p hp) w
  -- Extend `A` off the target of `ψ` to a field of complex structures on the whole plane.
  let J : ℂ → AlmostComplexStructure ℂ := fun p ↦
    if hp : p ∈ ψ.target then ⟨(A p).toLinearMap, LinearMap.ext fun w ↦ by simp [hAsq p hp]⟩
    else AlmostComplexStructure.ofComplexModule ℂ
  have hJA (p : ℂ) (hp : p ∈ ψ.target) (w : ℂ) : J p w = A p w := by
    simp [J, hp]
  refine ⟨J, ?_, fun y hy w ↦ ?_⟩
  · refine ((hA.contDiffAt (ψ.open_target.mem_nhds hx)).of_le (by simp)).congr_of_eventuallyEq ?_
    filter_upwards [ψ.open_target.mem_nhds hx] with p hp
    ext1 w
    exact hJA p hp w
  · -- The derivative of `ψ` carries `j` to `A`, which is `J` on the target of `ψ`.
    have h := (j.toContMDiff ⊤).mfderiv_comp_toEndomorphism ψ hy (hdψ y hy)
      (hdψs _ (ψ.map_source hy))
    rw [SmoothAlmostComplexStructure.toContMDiff_chartPushforward] at h
    have h' := DFunLike.congr_fun h w
    rw [SmoothAlmostComplexStructure.toContMDiff_toEndomorphism_apply] at h'
    exact h'.trans (hJA _ (ψ.map_source hy) _).symm

/-- **Isothermal charts exist.** Every point of a surface with a smooth almost complex structure `j`
lies in the source of an isothermal chart of `j`: a chart of the real `C¹` maximal atlas in which
`j` is multiplication by `i`. -/
theorem exists_isIsothermalChart (x : M) :
    ∃ e : OpenPartialHomeomorph M ℂ, IsIsothermalChart j e ∧ x ∈ e.source := by
  set ψ := chartAt ℂ x
  obtain ⟨J, hJ, hψJ⟩ := exists_almostComplexStructure_mfderiv_chartAt j x
  -- A planar isothermal chart `e` for `J` at `ψ x`; its inverse is `C¹` too.
  obtain ⟨e, hce, heC, -, heinv, heJ⟩ :=
    Beltrami.exists_isothermal_chart_of_contDiffAt (α := 1 / 2) (by norm_num) (by norm_num) hJ
  have heCA (p : ℂ) (hp : p ∈ e.source) : ContDiffAt ℝ 1 e p :=
    heC.contDiffAt (e.open_source.mem_nhds hp)
  have hes := e.contDiffOn_symm_of_isInvertible_fderiv heC heinv
  have hsrc (y : M) : y ∈ (ψ.trans e).source ↔ y ∈ ψ.source ∧ ψ y ∈ e.source := by
    rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
  -- The chart is `ψ` followed by `e`.
  refine ⟨ψ.trans e, ⟨trans_mem_maximalAtlas_of_contDiffAt (chart_mem_maximalAtlas x) heCA
    fun p hp ↦ hes.contDiffAt (e.open_target.mem_nhds hp), fun y hy ↦ ?_⟩,
      (hsrc x).2 ⟨mem_chart_source ℂ x, hce⟩⟩
  -- Its derivative `de ∘ dψ` at `y` carries `j` to `J` and then to `i`, by the chain rule.
  obtain ⟨hyψ, hye⟩ := (hsrc y).1 hy
  have hdψ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ y :=
    (contMDiffAt_of_mem_maximalAtlas (n := 1) (chart_mem_maximalAtlas x) hyψ).mdifferentiableAt
      one_ne_zero
  refine isPseudoholomorphicAt_of_hasMFDerivAt
    (u' := (fderiv ℝ e (ψ y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ y))
    (((heCA _ hye).differentiableAt one_ne_zero).hasFDerivAt.hasMFDerivAt.comp y
      hdψ.hasMFDerivAt) fun w ↦ ?_
  exact ((congrArg (fderiv ℝ e (ψ y)) (hψJ y hyψ w)).trans (heJ _ hye _)).trans
    ((smul_eq_mul I _).symm.trans
      (SmoothAlmostComplexStructure.ofComplexManifold_apply (E := ℂ) _ _).symm)

/-- **Every almost complex structure on a surface is integrable.** A smooth almost complex
structure on a surface has isothermal charts, so its isothermal surface
`TauCeti.IsothermalSurface j` is a complex analytic curve. -/
instance SmoothAlmostComplexStructure.hasIsothermalCharts : j.HasIsothermalCharts :=
  ⟨exists_isIsothermalChart j⟩

end TauCeti
