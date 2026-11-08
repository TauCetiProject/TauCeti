/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# Pullback of forms in the weak Whitney topology, and closed stabilizers

At a point `x`, the pullback `(f^* φ)_x = φ_(f x) ∘ (df_x)^k` of a continuous differential form
`φ` depends only on the value and the first derivative of the map `f` at `x`. Both are controlled
by the weak Whitney `C^1` topology, so for `1 ≤ n` the map `f ↦ (f^* φ)_x` is continuous on the
space `C^n⟮I, M; J, N⟯` of `C^n` maps
(`TauCeti.IsSmoothForm.continuous_mpullback_apply_manifoldWeakWhitney`). In the chart at `f₀ x`
this is the formula of `TauCeti.RoughForm.mpullback_eq_compContinuousLinearMap`: the coordinate
expression of `φ` at the moving point `f x` precomposed with the coordinate differential of `f`,
each of which varies continuously with `f`.

Consequently, on a compact manifold `M`, the diffeomorphisms preserving a smooth form `σ`,
`φ^* σ = σ`, form a closed subgroup of the diffeomorphism group with its weak Whitney `C^∞`
topology (`TauCeti.SmoothForm.isClosed_diffeomorphStabilizer`,
`TauCeti.SmoothForm.closedDiffeomorphStabilizer`): it is the intersection, over the points `x`,
of the sets where the continuous map `φ ↦ (φ^* σ)_x` takes the value `σ_x`. Since the
diffeomorphism group of a compact Hausdorff manifold with locally compact model is a topological
group (`Diffeomorph.isTopologicalGroup`), so is this subgroup. For a symplectic form `ω` it is the
symplectomorphism group `Symp(M, ω)`, a closed topological subgroup of `Diff(M)`; for a volume form
it is the group of volume-preserving diffeomorphisms. Neither closedness nor nondegeneracy of `σ`
is used.

## Main results

* `TauCeti.IsSmoothForm.continuous_mpullback_apply_manifoldWeakWhitney`: for `1 ≤ n`, the value
  at a fixed point of the pullback of a continuous form along a `C^n` map is continuous in the
  map.
* `TauCeti.SmoothForm.isClosed_diffeomorphStabilizer`: the stabilizer of a smooth form in the
  diffeomorphism group of a compact manifold is closed.
* `TauCeti.SmoothForm.closedDiffeomorphStabilizer`: the stabilizer as a closed subgroup.

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 2, §1 (the weak `C^r` topology).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 10 (the group of symplectomorphisms).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {E H M E' H' N F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} [LocallyCompactSpace E]

/-- For `1 ≤ n`, the value at a fixed point `x` of the pullback of a continuous (for instance
smooth) form `φ` along a `C^n` map `f` is continuous in `f` for the weak Whitney topology,
provided the source model is locally compact. The `C^1` structure of `N` is the one on which the
regularity of `φ` is measured. -/
theorem IsSmoothForm.continuous_mpullback_apply_manifoldWeakWhitney {n : ℕ∞ω}
    [IsManifold I n M] [IsManifold J n N] [IsManifold J 1 N] (hn : 1 ≤ n) {m : WithTop ℕ∞}
    {φ : RoughForm J N F k} (hφ : IsSmoothForm J m φ) (x : M) :
    Continuous fun f : C^n⟮I, M; J, N⟯ ↦ TauCeti.mpullback I J f φ x := by
  have : IsManifold I 1 M := IsManifold.of_le hn
  refine continuous_iff_continuousAt.2 fun f₀ ↦ ?_
  set ψ := extChartAt J (f₀ x)
  have hx : extChartAt I x x ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hf₀ : f₀ ((extChartAt I x).symm (extChartAt I x x)) ∈ ψ.source := by
    rw [extChartAt_to_inv]
    exact mem_extChartAt_source _
  -- Nearby maps send `x` into the chart at `f₀ x`, and the coordinate of `f x` moves
  -- continuously inside the chart target.
  have hev := (ContMDiffMap.continuous_eval_const_manifoldWeakWhitney x).continuousAt (x := f₀)
  have hsrc : ∀ᶠ f : C^n⟮I, M; J, N⟯ in 𝓝 f₀, f x ∈ ψ.source :=
    hev.preimage_mem_nhds ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source _))
  have hP : Tendsto (fun f : C^n⟮I, M; J, N⟯ ↦ ψ (f x)) (𝓝 f₀) (𝓝[ψ.target] (ψ (f₀ x))) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuousAt_extChartAt _).tendsto.comp hev,
      hsrc.mono fun _ hf ↦ ψ.map_source hf⟩
  -- The coordinate expression of `φ` at `f x` and the coordinate differential of `f` at `x`.
  have hA : ContinuousAt (fun f : C^n⟮I, M; J, N⟯ ↦ φ.inChartAt (f₀ x) (ψ (f x))) f₀ :=
    ((hφ.continuousOn_inChartAt (f₀ x)) _
      (ψ.map_source (mem_extChartAt_source _))).tendsto.comp hP
  have hD : ContinuousAt (fun f : C^n⟮I, M; J, N⟯ ↦ fderivWithin ℝ
      (ψ ∘ f ∘ (extChartAt I x).symm) (extChartAt I x).target (extChartAt I x x)) f₀ :=
    (tendsto_fderivWithin_extChartAt hn hx hf₀).comp (tendsto_id.prodMk
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds, .of_forall fun _ ↦ hx⟩))
  refine ((ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.continuousAt.comp
    hD).clm_apply hA).congr ?_
  filter_upwards [hsrc] with f hf
  -- Near the base point the chart target is the range of the model.
  rw [RoughForm.mpullback_eq_compContinuousLinearMap φ (f₀ x)
    (f.contMDiff.contMDiffAt.mdifferentiableAt (by rintro rfl; simp at hn)) hf,
    fderivWithin_congr_set extChartAt_target_eventuallyEqSet.symm,
    Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]

namespace SmoothForm

open scoped TauCeti.DiffeomorphWeakWhitney

variable [IsManifold I ∞ M] [CompactSpace M]

/-- The stabilizer of a smooth form in the diffeomorphism group of a compact manifold is closed
for the weak Whitney topology, provided the model space is locally compact. For a symplectic form
this is the closedness of the symplectomorphism group `Symp(M, ω)` in `Diff(M)`. -/
theorem isClosed_diffeomorphStabilizer (σ : SmoothForm I M F k) :
    IsClosed (diffeomorphStabilizer σ : Set (M ≃ₘ⟮I, I⟯ M)) := by
  have hset : (diffeomorphStabilizer σ : Set (M ≃ₘ⟮I, I⟯ M)) =
      ⋂ x, {φ : M ≃ₘ⟮I, I⟯ M | TauCeti.mpullback I I φ σ.1 x = σ.1 x} := by
    ext φ
    simp only [SetLike.mem_coe, mem_diffeomorphStabilizer_iff_forall, mem_iInter, mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun x ↦ isClosed_eq
    (((isSmoothForm σ).continuous_mpullback_apply_manifoldWeakWhitney (n := ∞) (by simp)
      x).comp Diffeomorph.continuous_toContMDiffMap) continuous_const

/-- The stabilizer of a smooth form, as a closed subgroup of the diffeomorphism group of a compact
manifold with its weak Whitney topology. For a symplectic form `ω` this is `Symp(M, ω)`. -/
def closedDiffeomorphStabilizer (σ : SmoothForm I M F k) : ClosedSubgroup (M ≃ₘ⟮I, I⟯ M) :=
  ⟨diffeomorphStabilizer σ, isClosed_diffeomorphStabilizer σ⟩

@[simp]
theorem coe_closedDiffeomorphStabilizer (σ : SmoothForm I M F k) :
    (closedDiffeomorphStabilizer σ : Subgroup (M ≃ₘ⟮I, I⟯ M)) = diffeomorphStabilizer σ :=
  (rfl)

@[simp]
theorem mem_closedDiffeomorphStabilizer {σ : SmoothForm I M F k} {φ : M ≃ₘ⟮I, I⟯ M} :
    φ ∈ closedDiffeomorphStabilizer σ ↔ mpullback φ φ.contMDiff σ = σ :=
  mem_diffeomorphStabilizer

end SmoothForm

end TauCeti
