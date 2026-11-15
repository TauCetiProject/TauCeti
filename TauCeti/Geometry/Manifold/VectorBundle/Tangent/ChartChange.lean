/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Submersion

/-!
# Changes of preferred charts on a boundaryless manifold and its tangent bundle

On a boundaryless manifold `M` the range of the model `I` is the whole model space, so the change
`φ = extChartAt I x' ∘ (extChartAt I x).symm` between two preferred extended charts is an
ordinary `C^n` map near every point of the common domain
(`TauCeti.Manifold.contDiffAt_extChartAt_comp_extChartAt_symm`), and the derivatives within
`range I` defining tangent coordinate changes are ordinary derivatives. The preferred charts of
the tangent bundle then change by the tangent map of `φ`: a point with coordinates `(q, u)` in the
chart at `z` has coordinates `(φ q, Dφ_q u)` in the chart at `z'`
(`TauCeti.Manifold.extChartAt_tangent_extChartAt_symm`), and near such a point a function on `TM`
read in the chart at `z` is the function read in the chart at `z'` composed with this change
(`TauCeti.Manifold.eventuallyEq_comp_extChartAt_tangent_symm`). A curve in `TM`
which is continuous at `t` and lies at `t` in both chart domains has its two chart readings
related in this way at all times near `t` (`TauCeti.Manifold.eventually_extChartAt_tangent_eq`).
So if its base coordinate has derivative its fibre coordinate at `t` in one such chart, the same
holds in the other (`TauCeti.Manifold.hasDerivAt_extChartAt_tangent_fst`).

This is how a function on `TM` read in two bundle charts, such as a Lagrangian, is compared: the
two coordinate expressions differ by the change of variables `(q, u) ↦ (φ q, Dφ_q u)`.
-/

public section

open scoped Topology

open Bundle Set Filter

namespace TauCeti.Manifold

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]

/-- On a boundaryless `C^n` manifold, the change between the preferred extended charts at `x` and
at `x'` is `C^n` at the `x`-coordinates of every point `y` of their common domain. -/
theorem contDiffAt_extChartAt_comp_extChartAt_symm {n : WithTop ℕ∞} [IsManifold I n M]
    {x x' y : M} (hy : y ∈ (extChartAt I x).source) (hy' : y ∈ (extChartAt I x').source) :
    ContDiffAt 𝕜 n (extChartAt I x' ∘ (extChartAt I x).symm) (extChartAt I x y) := by
  have h := contDiffWithinAt_ext_coord_change (I := I) (n := n) x' x (y := extChartAt I x y)
    ⟨(extChartAt I x).map_source hy, by
      rw [mem_preimage, PartialEquiv.symm_symm, (extChartAt I x).left_inv hy]
      exact hy'⟩
  rwa [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at h

variable [IsManifold I 1 M]

/-- **Changes of charts of the tangent bundle.** On a boundaryless manifold, a point of `TM` with
coordinates `a = (q, u)` in the preferred chart at `z`, lying in the domain of the preferred chart
at `z'`, has coordinates `(φ q, Dφ_q u)` there, where `φ` is the change from the chart of `M` at
`z.proj` to the chart at `z'.proj`. -/
theorem extChartAt_tangent_extChartAt_symm (z z' : TangentBundle I M) {a : E × E}
    (ha : a ∈ (extChartAt I.tangent z).target)
    (ha' : (extChartAt I.tangent z).symm a ∈ (extChartAt I.tangent z').source) :
    extChartAt I.tangent z' ((extChartAt I.tangent z).symm a) =
      ((extChartAt I z'.proj ∘ (extChartAt I z.proj).symm) a.1,
        fderiv 𝕜 (extChartAt I z'.proj ∘ (extChartAt I z.proj).symm) a.1 a.2) := by
  set y := (extChartAt I z.proj).symm a.1
  have hw := (mem_extChartAt_source_iff z _).1 ((extChartAt I.tangent z).map_target ha)
  rw [proj_extChartAt_symm z ha] at hw
  -- The point is the vector over `y` with fibre coordinate `a.2` in the trivialization at `z`.
  have h := extChartAt_symm_apply_of_mem_baseSet z hw.1 a.2
  rw [Prod.mk.eta] at h
  rw [h] at ha' ⊢
  have hw' := (mem_extChartAt_source_iff z' _).1 ha'
  rw [extChartAt_apply_of_mem_baseSet z' hw'.1]
  refine Prod.ext rfl ?_
  dsimp only
  -- Its fibre coordinate at `z'` is the tangent coordinate change, an ordinary derivative here.
  rw [← (trivializationAt E (TangentSpace I) z'.proj).continuousLinearMapAt_apply_of_mem (R := 𝕜)
      hw'.1, ← Trivialization.symmL_apply (R := 𝕜) _ hw.1, continuousLinearMapAt_symmL_coordChange
      (by simpa [extChartAt_source] using hw.2) (by simpa [extChartAt_source] using hw'.2),
    tangentCoordChange_def, (extChartAt I z.proj).right_inv (fst_mem_extChartAt_target z ha),
    ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]

/-- Near a point `a` of the chart at `z` whose point of `TM` lies in the chart at `z'`, a function
on `TM` read in the chart at `z` is the function read in the chart at `z'`, composed with the
change of tangent-bundle charts `(q, u) ↦ (φ q, Dφ_q u)`. -/
theorem eventuallyEq_comp_extChartAt_tangent_symm {F : Type*} {f : TangentBundle I M → F}
    {z z' : TangentBundle I M} {a : E × E} (ha : a ∈ (extChartAt I.tangent z).target)
    (ha' : (extChartAt I.tangent z).symm a ∈ (extChartAt I.tangent z').source) :
    (fun p ↦ f ((extChartAt I.tangent z).symm p)) =ᶠ[𝓝 a] fun y ↦
      f ((extChartAt I.tangent z').symm
        ((extChartAt I z'.proj ∘ (extChartAt I z.proj).symm) y.1,
          fderiv 𝕜 (extChartAt I z'.proj ∘ (extChartAt I z.proj).symm) y.1 y.2)) := by
  have hW : IsOpen ((extChartAt I.tangent z).target ∩
      (extChartAt I.tangent z).symm ⁻¹' (extChartAt I.tangent z').source) :=
    (continuousOn_extChartAt_symm z).isOpen_inter_preimage (isOpen_extChartAt_target z)
      (isOpen_extChartAt_source z')
  filter_upwards [hW.mem_nhds ⟨ha, ha'⟩] with y hy
  rw [← extChartAt_tangent_extChartAt_symm z z' hy.1 hy.2,
    (extChartAt I.tangent z').left_inv hy.2]

/-- Near `t`, a curve in `TM` continuous at `t` and read in the preferred charts at `z` and at `z'`
is related by the change of tangent-bundle charts `(q, u) ↦ (φ q, Dφ_q u)`. -/
theorem eventually_extChartAt_tangent_eq {γ : 𝕜 → TangentBundle I M} {t : 𝕜}
    (hγ : ContinuousAt γ t) {z z' : TangentBundle I M}
    (hz : γ t ∈ (extChartAt I.tangent z).source) (hz' : γ t ∈ (extChartAt I.tangent z').source) :
    ∀ᶠ s in 𝓝 t, extChartAt I.tangent z' (γ s) =
      ((extChartAt I z'.proj ∘ (extChartAt I z.proj).symm) (extChartAt I.tangent z (γ s)).1,
        fderiv 𝕜 (extChartAt I z'.proj ∘ (extChartAt I z.proj).symm)
          (extChartAt I.tangent z (γ s)).1 (extChartAt I.tangent z (γ s)).2) := by
  filter_upwards [hγ.preimage_mem_nhds
    (inter_mem (extChartAt_source_mem_nhds' hz) (extChartAt_source_mem_nhds' hz'))] with s hs
  have h := extChartAt_tangent_extChartAt_symm z z' ((extChartAt I.tangent z).map_source hs.1)
    (by rw [(extChartAt I.tangent z).left_inv hs.1]; exact hs.2)
  rwa [(extChartAt I.tangent z).left_inv hs.1] at h

/-- **Second-order curves do not depend on the chart.** Let `γ` be a curve in `TM`, continuous at
`t`, whose base coordinate in the preferred chart at `z` has derivative its fibre coordinate at
`t`. Then the same holds in the preferred chart at any `z'` whose domain contains `γ t`, on a
`C²` boundaryless manifold. -/
theorem hasDerivAt_extChartAt_tangent_fst [IsManifold I 2 M] {γ : 𝕜 → TangentBundle I M} {t : 𝕜}
    (hγ : ContinuousAt γ t) {z z' : TangentBundle I M}
    (hz : γ t ∈ (extChartAt I.tangent z).source) (hz' : γ t ∈ (extChartAt I.tangent z').source)
    (hq : HasDerivAt (fun s ↦ (extChartAt I.tangent z (γ s)).1)
      (extChartAt I.tangent z (γ t)).2 t) :
    HasDerivAt (fun s ↦ (extChartAt I.tangent z' (γ s)).1)
      (extChartAt I.tangent z' (γ t)).2 t := by
  set ψ := extChartAt I z'.proj ∘ (extChartAt I z.proj).symm
  have hc := eventually_extChartAt_tangent_eq hγ hz hz'
  have hb := (mem_extChartAt_source_iff z (γ t)).1 hz
  have hb' := (mem_extChartAt_source_iff z' (γ t)).1 hz'
  have hψ : ContDiffAt 𝕜 2 ψ (extChartAt I.tangent z (γ t)).1 := by
    rw [extChartAt_apply_of_mem_baseSet z hb.1]
    exact contDiffAt_extChartAt_comp_extChartAt_symm hb.2 hb'.2
  rw [hc.self_of_nhds]
  exact ((hψ.differentiableAt two_ne_zero).hasFDerivAt.comp_hasDerivAt t hq).congr_of_eventuallyEq
    (hc.mono fun s hs ↦ congrArg Prod.fst hs)

end TauCeti.Manifold
