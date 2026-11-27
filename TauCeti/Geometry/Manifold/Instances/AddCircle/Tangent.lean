/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.Covering.AddCircle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-!
# The tangent bundle of the circle

The charts of the circle `AddCircle p` are local lifts to `ℝ`, so any two of them differ near each
point by a translation by a multiple of `p`, whose derivative is the identity. Reading a tangent
vector in the trivialization of the tangent bundle at any point therefore does not change it
(`AddCircle.trivializationAt_tangent_snd`). So the tangent bundle of the circle is trivial in its
charts: a map into the tangent bundle, `y ↦ (f y, g y)` with base point `f y` and real coordinate
`g y`, is `C^n` exactly when `f` and `g` are (`AddCircle.contMDiff_totalSpace_mk_iff`). In
particular a vector field on the circle, read as a real function, is as smooth as the field.

The tangent lines of the circle carry the norm of `ℝ`, and a curve whose velocity has norm at most
`L` moves by at most `L` per unit time for the distance of the circle
(`AddCircle.dist_le_mul_of_hasMFDerivAt`): a continuous lift of the curve to `ℝ` has the same
velocity, and the quotient map does not increase distances.

## Main results

* `AddCircle.trivializationAt_tangent_snd`: the trivializations of the tangent bundle of the
  circle do not change tangent vectors.
* `AddCircle.contMDiffAt_totalSpace_mk_iff`, `AddCircle.contMDiff_totalSpace_mk_iff`: a map into
  the tangent bundle of the circle is `C^n` exactly when its base point and its real coordinate
  are.
* `AddCircle.dist_le_mul_of_hasMFDerivAt`: a curve of the circle with velocity bounded by `L`
  moves by at most `L |t - s|` between the times `s` and `t`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

/-- **The trivializations of the tangent bundle of the circle are the identity on the fibres.** The
charts of the circle are local lifts to `ℝ`, which near each point of a common source differ by a
translation by a multiple of `p`, so a tangent vector at a point of the source of the chart at `x`
is not changed by the trivialization of the tangent bundle at `x`. -/
theorem trivializationAt_tangent_snd {x : AddCircle p} {z : TangentBundle 𝓘(ℝ) (AddCircle p)}
    (hz : z.proj ∈ (chartAt ℝ x).source) :
    (trivializationAt ℝ (TangentSpace 𝓘(ℝ)) x z).2 = z.snd := by
  have hc (y : AddCircle p) : ∀ w ∈ (chartAt ℝ y).source, (chartAt ℝ y w : AddCircle p) = w :=
    fun _ hw ↦ coe_apply_of_mem_atlas (chart_mem_atlas ℝ y) hw
  obtain ⟨k, hk⟩ := exists_eventuallyEq_add_zsmul (hc z.proj) (hc x)
    (mem_chart_source ℝ z.proj) hz
  -- Near the chart value of `z.proj`, the change of charts is the translation by `k • p`.
  have hchange : (chartAt ℝ x ∘ (chartAt ℝ z.proj).symm) =ᶠ[𝓝 (chartAt ℝ z.proj z.proj)]
      fun w ↦ w + k • p := by
    have hcont : ContinuousAt (chartAt ℝ z.proj).symm (chartAt ℝ z.proj z.proj) :=
      (chartAt ℝ z.proj).continuousAt_symm (mem_chart_target ℝ z.proj)
    have hk' := hcont.eventually (by rwa [(chartAt ℝ z.proj).left_inv (mem_chart_source ℝ _)])
    filter_upwards [hk', (chartAt ℝ z.proj).open_target.mem_nhds (mem_chart_target ℝ z.proj)]
      with w hw hwt
    simp only [Function.comp_apply, hw, (chartAt ℝ z.proj).right_inv hwt]
  rw [TangentBundle.trivializationAt_apply]
  simp only [OpenPartialHomeomorph.extend, modelWithCornersSelf_coe, range_id,
    fderivWithin_univ, PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.toFun_eq_coe, PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, ModelWithCorners.toPartialEquiv_coe_symm,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq]
  rw [hchange.fderiv_eq, fderiv_add_const, fderiv_fun_id]
  -- The tangent line at `z.proj` is `ℝ`, on which the identity acts trivially.
  rfl

variable {n : ℕ∞ω} {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace N] [ChartedSpace H N]
  {f : N → AddCircle p} {g : N → ℝ} {y₀ : N}

/-- **Maps into the tangent bundle of the circle, at a point.** The map `y ↦ (f y, g y)` into the
tangent bundle of the circle, with base point `f y` and coordinate `g y` in the tangent line `ℝ`,
is `C^n` at `y₀` exactly when `f` and `g` are. -/
theorem contMDiffAt_totalSpace_mk_iff :
    ContMDiffAt I 𝓘(ℝ).tangent n
        (fun y ↦ (⟨f y, g y⟩ : TangentBundle 𝓘(ℝ) (AddCircle p))) y₀ ↔
      ContMDiffAt I 𝓘(ℝ) n f y₀ ∧ ContMDiffAt I 𝓘(ℝ) n g y₀ := by
  rw [contMDiffAt_totalSpace_iff]
  refine and_congr_right fun hf ↦ Filter.EventuallyEq.contMDiffAt_iff ?_
  -- Near `y₀` the base point stays in the source of the chart at `f y₀`, where the trivialization
  -- does not change the coordinate.
  filter_upwards [hf.continuousAt.preimage_mem_nhds
    ((chartAt ℝ (f y₀)).open_source.mem_nhds (mem_chart_source ℝ (f y₀)))] with y hy
  exact trivializationAt_tangent_snd hy

/-- **Maps into the tangent bundle of the circle.** The map `y ↦ (f y, g y)` into the tangent bundle
of the circle, with base point `f y` and coordinate `g y` in the tangent line `ℝ`, is `C^n` exactly
when `f` and `g` are. In particular a vector field on the circle is `C^n` exactly when it is as a
real function. -/
theorem contMDiff_totalSpace_mk_iff :
    ContMDiff I 𝓘(ℝ).tangent n (fun y ↦ (⟨f y, g y⟩ : TangentBundle 𝓘(ℝ) (AddCircle p))) ↔
      ContMDiff I 𝓘(ℝ) n f ∧ ContMDiff I 𝓘(ℝ) n g :=
  ⟨fun h ↦ ⟨fun y ↦ (contMDiffAt_totalSpace_mk_iff.1 (h y)).1,
    fun y ↦ (contMDiffAt_totalSpace_mk_iff.1 (h y)).2⟩,
    fun h y ↦ contMDiffAt_totalSpace_mk_iff.2 ⟨h.1 y, h.2 y⟩⟩

/-- **A curve of the circle with bounded velocity is Lipschitz.** If the curve `γ` of the circle has
velocity `v u` at every time `u`, read in the tangent line `ℝ`, and `|v u| ≤ L` for the times `u`
between `s` and `t`, then `dist (γ t) (γ s) ≤ L |t - s|`. -/
theorem dist_le_mul_of_hasMFDerivAt {γ : ℝ → AddCircle p} {v : ℝ → ℝ} {L s t : ℝ}
    (hγ : ∀ u, HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) γ u ((1 : ℝ →L[ℝ] ℝ).smulRight (v u)))
    (hv : ∀ u ∈ uIcc s t, |v u| ≤ L) :
    dist (γ t) (γ s) ≤ L * |t - s| := by
  -- Lift the curve continuously to `ℝ` through the covering map.
  obtain ⟨Γ, ⟨-, hΓ⟩, -⟩ := (isCoveringMap_coe p).existsUnique_continuousMap_lifts
    ⟨γ, continuous_iff_continuousAt.2 fun u ↦ (hγ u).continuousAt⟩ 0
    (Classical.choose (QuotientAddGroup.mk_surjective (γ 0)))
    (Classical.choose_spec (QuotientAddGroup.mk_surjective (γ 0)))
  have hlift (u : ℝ) : (Γ u : AddCircle p) = γ u := congrFun hΓ u
  -- The lift has the velocity of the curve as its derivative.
  have hΓγ : (fun u ↦ (Γ u : AddCircle p)) = γ := funext hlift
  have hderiv (u : ℝ) : HasDerivAt Γ (v u) u :=
    hasDerivAt_of_hasMFDerivAt_coe_comp Γ.continuous.continuousAt (hΓγ ▸ hγ u)
  have hbound : ‖Γ t - Γ s‖ ≤ L * ‖t - s‖ := by
    rcases le_total s t with hst | hst
    · exact norm_image_sub_le_of_norm_deriv_le_segment' (fun u _ ↦ (hderiv u).hasDerivWithinAt)
        (fun u hu ↦ hv u (Icc_subset_uIcc (Ico_subset_Icc_self hu))) t (right_mem_Icc.2 hst)
        |>.trans_eq (by rw [Real.norm_of_nonneg (sub_nonneg.2 hst)])
    · rw [norm_sub_rev, norm_sub_rev t s]
      exact norm_image_sub_le_of_norm_deriv_le_segment' (fun u _ ↦ (hderiv u).hasDerivWithinAt)
        (fun u hu ↦ hv u (Icc_subset_uIcc' (Ico_subset_Icc_self hu))) s (right_mem_Icc.2 hst)
        |>.trans_eq (by rw [Real.norm_of_nonneg (sub_nonneg.2 hst)])
  rw [← hlift t, ← hlift s, dist_eq_norm, ← coe_sub, ← Real.norm_eq_abs]
  exact (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples p)).trans hbound

end AddCircle
