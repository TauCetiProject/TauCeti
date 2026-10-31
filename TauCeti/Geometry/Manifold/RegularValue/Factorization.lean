/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Functions of a map near its regular points

Let `F : M → V` be a map from a boundaryless manifold to a finite-dimensional space, `C^n` with
`n ≠ 0`, and let `x` be a regular point of `F`, so that `dF_x` is surjective. Read in a chart at
`x`, the implicit function theorem straightens `F` into a linear projection. Two consequences are
recorded here.

* `F` is open at `x`: it maps the neighbourhoods of `x` onto the neighbourhoods of `F x`.
* A `C^n` function `g` on `M` whose differential vanishes on the kernel of `dF` at every point near
  `x` is, near `x`, a function `h ∘ F` of `F`, with `h` of class `C^n` at `F x`. The kernel of `dF`
  is the tangent space of the level sets of `F`, so this says that a function which is stationary
  along the level sets of `F` is locally a function of `F`.

Globally such a `g` is only constant on the connected components of the level sets. On an open set
of regular points whose fibres are connected, the local factors glue to a single function of `F`,
which is `C^n` at every value of `F` there.

For a completely integrable system `F` on a symplectic manifold, the functions whose differentials
vanish on `ker dF` at regular points are those in involution with every component of `F`, and the
results below say that such a function is a function of the integrals.

## Main results

* `TauCeti.IsRegularPoint.map_nhds_eq`: a map is open at its regular points.
* `TauCeti.IsRegularPoint.exists_eventuallyEq_comp_of_ker_mfderiv_le`: near a regular point of `F`,
  a function whose differential vanishes on `ker dF` is a `C^n` function of `F`.
* `TauCeti.exists_eqOn_comp_of_ker_mfderiv_le`: on an open set of regular points with
  preconnected fibres, such a function is a single function of `F`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 4 (the rank theorem and the local structure of submersions).
-/

public section

open Filter Function Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {F : M → V} {g : M → W} {x : M} {n : ℕ∞ω}

omit [IsManifold I 1 M] in
/-- **A map is open at a regular point.** On a boundaryless manifold, a map into a
finite-dimensional space which is `C^n`, `n ≠ 0`, at a regular point `x` sends the neighbourhoods
of `x` onto the neighbourhoods of its value. -/
theorem IsRegularPoint.map_nhds_eq (hreg : IsRegularPoint I 𝓘(𝕜, V) F x)
    (hF : ContMDiffAt I 𝓘(𝕜, V) n F x) (hn : n ≠ 0) : map F (𝓝 x) = 𝓝 (F x) := by
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  set e := extChartAt I x
  have hFc := hF.contDiffAt_comp_extChartAt_symm
  have hmap := (hFc.hasStrictFDerivAt hn).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.2 hreg.surjective_fderiv_comp_extChartAt_symm)
  have hFe : F =ᶠ[𝓝 x] (F ∘ e.symm) ∘ e := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
    rw [comp_apply, comp_apply, e.left_inv hy]
  rw [map_congr hFe, ← map_map, map_extChartAt_nhds_of_boundaryless, hmap, comp_apply,
    extChartAt_to_inv]

/-- **A function whose differential kills the kernel of `dF` is locally a function of `F`.** Let
`F` be a map from a boundaryless manifold to a finite-dimensional space, `C^n` (`n ≠ 0`) at a
regular point `x`, and let `g` be `C^n` at `x`. If at every point near `x` the differential of `g`
vanishes on the kernel of the differential of `F`, then near `x` the function `g` is `h ∘ F` for a
function `h` which is `C^n` at `F x`. -/
theorem IsRegularPoint.exists_eventuallyEq_comp_of_ker_mfderiv_le
    (hreg : IsRegularPoint I 𝓘(𝕜, V) F x) (hF : ContMDiffAt I 𝓘(𝕜, V) n F x)
    (hg : ContMDiffAt I 𝓘(𝕜, W) n g x) (hn : n ≠ 0)
    (hFg : ∀ᶠ y in 𝓝 x, (mfderiv I 𝓘(𝕜, V) F y).ker ≤ (mfderiv I 𝓘(𝕜, W) g y).ker) :
    ∃ h : V → W, ContDiffAt 𝕜 n h (F x) ∧ g =ᶠ[𝓝 x] h ∘ F := by
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  set e := extChartAt I x
  have hFc := hF.contDiffAt_comp_extChartAt_symm
  have hgc := hg.contDiffAt_comp_extChartAt_symm
  have h1 : (1 : ℕ∞ω) ≤ n := ENat.one_le_iff_ne_zero_withTop.2 hn
  -- Read in the chart, the kernel inclusion survives at the chart image of every point near `x`,
  -- because both manifold derivatives factor through the same invertible chart derivative.
  have hker : ∀ᶠ z in 𝓝 (e x), (fderiv 𝕜 (F ∘ e.symm) z).ker ≤ (fderiv 𝕜 (g ∘ e.symm) z).ker := by
    have hsymm : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have := continuousAt_extChartAt_symm (I := I) x
      rwa [ContinuousAt, extChartAt_to_inv] at this
    filter_upwards [extChartAt_target_mem_nhds x, hsymm.eventually hFg,
      (hFc.of_le h1).eventually (by simp), (hgc.of_le h1).eventually (by simp)]
      with z hz hk hFz hgz
    have hy : e.symm z ∈ e.source := e.map_target hz
    rw [← e.right_inv hz] at hFz hgz ⊢
    obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
    have hFm := mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy (hFz.differentiableAt one_ne_zero)
    have hgm := mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy (hgz.differentiableAt one_ne_zero)
    intro w hw
    obtain ⟨v, rfl⟩ := L.surjective w
    have hv : mfderiv I 𝓘(𝕜, V) F (e.symm z) v = 0 := by
      rw [hFm, ← hL]
      exact LinearMap.mem_ker.1 hw
    have := LinearMap.mem_ker.1 (hk (LinearMap.mem_ker.2 hv))
    rw [hgm, ← hL] at this
    exact LinearMap.mem_ker.2 this
  obtain ⟨h, hh, hgh⟩ := hFc.exists_eventuallyEq_comp_of_ker_fderiv_le hgc hn
    (LinearMap.range_eq_top.2 hreg.surjective_fderiv_comp_extChartAt_symm)
    (ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _) hker
  rw [comp_apply, extChartAt_to_inv] at hh
  refine ⟨h, hh, ?_⟩
  filter_upwards [extChartAt_source_mem_nhds (I := I) x,
    (continuousAt_extChartAt (I := I) x).eventually hgh] with y hy hyh
  have hyy : (extChartAt I x).symm (extChartAt I x y) = y := (extChartAt I x).left_inv hy
  simpa only [comp_apply, hyy] using hyh

/-- **A function whose differential kills the kernel of `dF` is a function of `F` on a set with
connected fibres.** Let `U` be an open set of regular points of a map `F` from a boundaryless
manifold to a finite-dimensional space, and let `F` and `g` be `C^n` (`n ≠ 0`) on `U`. If at each
point of `U` the differential of `g` vanishes on the kernel of the differential of `F`, and every
fibre `U ∩ F ⁻¹' {c}` of `F` in `U` is preconnected, then on `U` the function `g` is `h ∘ F` for a
single function `h` which is `C^n` at every value of `F` on `U`.

Connectedness of the fibres is needed: on a disconnected fibre `g` may take a different constant
value on each component. -/
theorem exists_eqOn_comp_of_ker_mfderiv_le {U : Set M} (hU : IsOpen U)
    (hreg : ∀ y ∈ U, IsRegularPoint I 𝓘(𝕜, V) F y) (hF : ContMDiffOn I 𝓘(𝕜, V) n F U)
    (hg : ContMDiffOn I 𝓘(𝕜, W) n g U) (hn : n ≠ 0)
    (hFg : ∀ y ∈ U, (mfderiv I 𝓘(𝕜, V) F y).ker ≤ (mfderiv I 𝓘(𝕜, W) g y).ker)
    (hconn : ∀ c, IsPreconnected (U ∩ F ⁻¹' {c})) :
    ∃ h : V → W, EqOn g (h ∘ F) U ∧ ∀ y ∈ U, ContDiffAt 𝕜 n h (F y) := by
  have hloc (y : M) (hy : y ∈ U) : ∃ h : V → W, ContDiffAt 𝕜 n h (F y) ∧ g =ᶠ[𝓝 y] h ∘ F :=
    (hreg y hy).exists_eventuallyEq_comp_of_ker_mfderiv_le (hF.contMDiffAt (hU.mem_nhds hy))
      (hg.contMDiffAt (hU.mem_nhds hy)) hn
      (eventually_of_mem (hU.mem_nhds hy) hFg)
  -- `g` is locally constant on each connected fibre of `F` in `U`, hence constant there.
  have hfib (y : M) (hy : y ∈ U) (y' : M) (hy' : y' ∈ U) (hyy' : F y = F y') : g y = g y' := by
    set S : Set M := U ∩ F ⁻¹' {F y}
    have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.1 (hconn (F y))
    have hlc : IsLocallyConstant (S.domRestrict g) := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun z ↦ ?_
      obtain ⟨h, -, hgh⟩ := hloc z z.2.1
      filter_upwards [(continuous_subtype_val.tendsto z).eventually hgh] with z' hz'
      have hz : F z = F y := z.2.2
      have hz'' : F z' = F y := z'.2.2
      rw [domRestrict_apply, domRestrict_apply, hz', hgh.self_of_nhds, comp_apply, comp_apply, hz,
        hz'']
    exact hlc.apply_eq_of_preconnectedSpace ⟨y, hy, rfl⟩ ⟨y', hy', hyy'.symm⟩
  have hfac : (U.domRestrict g).FactorsThrough (U.domRestrict F) :=
    fun a b hab ↦ hfib a a.2 b b.2 hab
  refine ⟨extend (U.domRestrict F) (U.domRestrict g) 0,
    fun y hy ↦ (hfac.extend_apply 0 ⟨y, hy⟩).symm, fun y hy ↦ ?_⟩
  -- Near `F y`, every value is taken near `y`, where `g` agrees with a local `C^n` factor.
  obtain ⟨h, hh, hgh⟩ := hloc y hy
  have hmem := image_mem_map (m := F) ((hU.eventually_mem hy).and hgh)
  rw [(hreg y hy).map_nhds_eq (hF.contMDiffAt (hU.mem_nhds hy)) hn] at hmem
  refine hh.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with c ⟨y', ⟨hy'U, hy'g⟩, hc⟩
  subst hc
  exact (hfac.extend_apply 0 ⟨y', hy'U⟩).trans hy'g

end TauCeti

end
