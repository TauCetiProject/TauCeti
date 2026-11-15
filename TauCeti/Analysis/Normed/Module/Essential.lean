/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Bounded approximate identities on essential left modules

Let `A` be a possibly nonunital normed algebra acting on a normed space `E` on the left through a
bounded bilinear map `L : A →L[𝕜] E →L[𝕜] E` with `L (a * b) x = L a (L b x)`. A left
approximate identity of `A` is a filter `l` on `A` with `e * a → a` along `l` for every `a`; it is
bounded by `C` when `‖e‖ ≤ C` eventually along `l`.

The *essential part* of `E` is the closed linear span of `A · E`. This file proves that a bounded
left approximate identity converges to the identity pointwise on the essential part, and that,
for a proper filter, the essential part consists exactly of the points where it does.

## Main results

* `ContinuousLinearMap.tendsto_apply_of_mem_topologicalClosure_span`: convergence on the
  essential part.
* `ContinuousLinearMap.tendsto_apply_iff_mem_topologicalClosure_span`: the essential part is the
  set of points of convergence.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
-/

public section

open Filter Topology Submodule

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A bounded left approximate identity of `A` converges to the identity at every point of the
essential part `closure (span (A · E))` of a left `A`-module `E`. -/
theorem tendsto_apply_of_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E}
    (hz : z ∈ (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure) :
    Tendsto (fun e ↦ L e z) l (𝓝 z) := by
  let S : Submodule 𝕜 E :=
    { carrier := {z | Tendsto (fun e ↦ L e z) l (𝓝 z)}
      add_mem' := fun hz hw ↦ by simpa using hz.add hw
      zero_mem' := by simpa using tendsto_const_nhds
      smul_mem' := fun c _ hz ↦ by simpa using hz.const_smul c }
  have hspan : span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2) ≤ S := by
    rw [span_le]
    rintro _ ⟨⟨a, w⟩, rfl⟩
    have : Tendsto (fun e ↦ L e (L a w)) l (𝓝 (L a w)) := by
      simpa [Function.comp_def, hL] using ((L.flip w).continuous.tendsto a).comp (hl a)
    exact this
  have hclosed : IsClosed (S : Set E) := by
    refine isClosed_of_closure_subset fun z hz ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    have hB : 0 < ‖L‖ * |C| + 1 := by positivity
    obtain ⟨s, hs, hzs⟩ := Metric.mem_closure_iff.mp hz (ε / 2 / (‖L‖ * |C| + 1)) (by positivity)
    have hzs' : (‖L‖ * |C| + 1) * dist z s < ε / 2 := by
      rwa [lt_div_iff₀ hB, mul_comm] at hzs
    filter_upwards [hC, Metric.tendsto_nhds.mp hs _ (half_pos hε)] with e he hes
    have hLe : dist (L e z) (L e s) ≤ ‖L‖ * |C| * dist z s := by
      rw [dist_eq_norm, ← map_sub, dist_eq_norm]
      calc ‖L e (z - s)‖ ≤ ‖L‖ * ‖e‖ * ‖z - s‖ := L.le_opNorm₂ e (z - s)
        _ ≤ ‖L‖ * |C| * ‖z - s‖ := by gcongr; exact he.trans (le_abs_self C)
    calc dist (L e z) z ≤ dist (L e z) (L e s) + dist (L e s) s + dist s z := dist_triangle4 ..
      _ < ε := by rw [dist_comm s z]; nlinarith [dist_nonneg (x := z) (y := s)]
  exact topologicalClosure_minimal _ hspan hclosed hz

/-- The essential part `closure (span (A · E))` of a left `A`-module `E` consists exactly of the
points at which a bounded left approximate identity of `A` converges to the identity. -/
theorem tendsto_apply_iff_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E} :
    Tendsto (fun e ↦ L e z) l (𝓝 z) ↔
      z ∈ (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure :=
  ⟨fun h ↦ (isClosed_topologicalClosure _).mem_of_tendsto h <| .of_forall fun e ↦
      le_topologicalClosure _ <| subset_span ⟨(e, z), rfl⟩,
    tendsto_apply_of_mem_topologicalClosure_span L hL hC hl⟩

end ContinuousLinearMap
