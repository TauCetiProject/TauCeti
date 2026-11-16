/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Bounded approximate identities on essential modules

Let `A` be a possibly nonunital normed algebra acting on a normed space `E` on the left through a
bounded bilinear map `L : A →L[𝕜] E →L[𝕜] E` with `L (a * b) x = L a (L b x)`, or on the right
through `R : A →L[𝕜] E →L[𝕜] E` with `R (a * b) x = R b (R a x)`. A left approximate identity of
`A` is a filter `l` on `A` with `e * a → a` along `l` for every `a`, and a right approximate
identity satisfies `a * e → a`; it is bounded by `C` when `‖e‖ ≤ C` eventually along `l`.

The *essential part* of a left module `E` is the closed linear span of `A · E`, and for a right
module it is the closed linear span of `E · A`. This file proves that a bounded one-sided
approximate identity converges to the identity pointwise on the corresponding essential part, and
that, for a proper filter, the essential part consists exactly of the points where it does.

## Main results

* `ContinuousLinearMap.tendsto_apply_of_mem_topologicalClosure_span` and
  `ContinuousLinearMap.tendsto_apply_iff_mem_topologicalClosure_span`: convergence and
  characterization on the left essential part.
* `ContinuousLinearMap.tendsto_apply_of_mem_topologicalClosure_span_right` and
  `ContinuousLinearMap.tendsto_apply_iff_mem_topologicalClosure_span_right`: convergence and
  characterization on the right essential part.
* `ContinuousLinearMap.apply_mem_topologicalClosure_span` and
  `ContinuousLinearMap.apply_mem_topologicalClosure_span_of_comm`: invariance of the essential part
  under the action itself and under any commuting bounded bilinear action.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
-/

public section

open Filter Topology Submodule

namespace ContinuousLinearMap

section Invariance

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every image `M a x` lies in the closed linear span of `M · ·`. -/
theorem apply_mem_topologicalClosure_span (M : A →L[𝕜] E →L[𝕜] E) (a : A) (x : E) :
    M a x ∈ (span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)).topologicalClosure :=
  le_topologicalClosure _ (subset_span ⟨(a, x), rfl⟩)

/-- If two bounded bilinear actions `M` and `N` commute (`M a (N b x) = N b (M a x)`), then `N b`
leaves invariant the closed linear span of `M · ·`. -/
theorem apply_mem_topologicalClosure_span_of_comm {M N : A →L[𝕜] E →L[𝕜] E}
    (hMN : ∀ a b x, M a (N b x) = N b (M a x)) (b : A) {x : E}
    (hx : x ∈ (span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)).topologicalClosure) :
    N b x ∈ (span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)).topologicalClosure := by
  set S := span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)
  have hmap : S.map (N b).toLinearMap ≤ S := by
    rw [Submodule.map_span_le]
    rintro _ ⟨⟨a, y⟩, rfl⟩
    change N b (M a y) ∈ S
    rw [← hMN]
    exact subset_span ⟨(a, N b y), rfl⟩
  have hsub : (N b) '' (S : Set E) ⊆ (S : Set E) := fun _ ⟨y, hy, hy'⟩ ↦
    hy' ▸ hmap ⟨y, hy, rfl⟩
  exact closure_mono hsub (image_closure_subset_closure_image (N b).continuous ⟨x, hx, rfl⟩)

end Invariance

section ApproximateIdentity

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Shared convergence argument: if an eventually bounded filter `l` acts as the identity in the
limit on every generator `M a w`, then it does so on the entire closed linear span of `M · ·`. -/
private theorem tendsto_apply_of_mem_topologicalClosure_span_aux (M : A →L[𝕜] E →L[𝕜] E)
    {l : Filter A} {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hgen : ∀ a w, Tendsto (fun e ↦ M e (M a w)) l (𝓝 (M a w))) {z : E}
    (hz : z ∈ (span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)).topologicalClosure) :
    Tendsto (fun e ↦ M e z) l (𝓝 z) := by
  let S : Submodule 𝕜 E :=
    { carrier := {z | Tendsto (fun e ↦ M e z) l (𝓝 z)}
      add_mem' := fun hz hw ↦ by simpa using hz.add hw
      zero_mem' := by simpa using tendsto_const_nhds
      smul_mem' := fun c _ hz ↦ by simpa using hz.const_smul c }
  have hspan : span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2) ≤ S := by
    rw [span_le]
    rintro _ ⟨⟨a, w⟩, rfl⟩
    exact hgen a w
  have hclosed : IsClosed (S : Set E) := by
    refine isClosed_of_closure_subset fun z hz ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    have hB : 0 < ‖M‖ * |C| + 1 := by positivity
    obtain ⟨s, hs, hzs⟩ := Metric.mem_closure_iff.mp hz (ε / 2 / (‖M‖ * |C| + 1)) (by positivity)
    have hzs' : (‖M‖ * |C| + 1) * dist z s < ε / 2 := by
      rwa [lt_div_iff₀ hB, mul_comm] at hzs
    filter_upwards [hC, Metric.tendsto_nhds.mp hs _ (half_pos hε)] with e he hes
    have hMe : dist (M e z) (M e s) ≤ ‖M‖ * |C| * dist z s := by
      rw [dist_eq_norm, ← map_sub, dist_eq_norm]
      calc ‖M e (z - s)‖ ≤ ‖M‖ * ‖e‖ * ‖z - s‖ := M.le_opNorm₂ e (z - s)
        _ ≤ ‖M‖ * |C| * ‖z - s‖ := by gcongr; exact he.trans (le_abs_self C)
    calc dist (M e z) z ≤ dist (M e z) (M e s) + dist (M e s) s + dist s z := dist_triangle4 ..
      _ < ε := by rw [dist_comm s z]; nlinarith [dist_nonneg (x := z) (y := s)]
  exact topologicalClosure_minimal _ hspan hclosed hz

/-- A bounded left approximate identity of `A` converges to the identity at every point of the
essential part `closure (span (A · E))` of a left `A`-module `E`. -/
theorem tendsto_apply_of_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E}
    (hz : z ∈ (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure) :
    Tendsto (fun e ↦ L e z) l (𝓝 z) :=
  tendsto_apply_of_mem_topologicalClosure_span_aux L hC
    (fun a w ↦ by simpa [Function.comp_def, hL] using ((L.flip w).continuous.tendsto a).comp (hl a))
    hz

/-- The essential part `closure (span (A · E))` of a left `A`-module `E` consists exactly of the
points at which a bounded left approximate identity of `A` converges to the identity. -/
theorem tendsto_apply_iff_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E} :
    Tendsto (fun e ↦ L e z) l (𝓝 z) ↔
      z ∈ (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure :=
  ⟨fun h ↦ (isClosed_topologicalClosure _).mem_of_tendsto h <| .of_forall fun e ↦
      apply_mem_topologicalClosure_span L e z,
    tendsto_apply_of_mem_topologicalClosure_span L hL hC hl⟩

/-- A bounded right approximate identity of `A` converges to the identity at every point of the
essential part `closure (span (E · A))` of a right `A`-module `E`. -/
theorem tendsto_apply_of_mem_topologicalClosure_span_right (R : A →L[𝕜] E →L[𝕜] E)
    (hR : ∀ a b z, R (a * b) z = R b (R a z)) {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) {z : E}
    (hz : z ∈ (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure) :
    Tendsto (fun e ↦ R e z) l (𝓝 z) :=
  tendsto_apply_of_mem_topologicalClosure_span_aux R hC
    (fun a w ↦ by simpa [Function.comp_def, hR] using ((R.flip w).continuous.tendsto a).comp (hl a))
    hz

/-- The essential part `closure (span (E · A))` of a right `A`-module `E` consists exactly of the
points at which a bounded right approximate identity of `A` converges to the identity. -/
theorem tendsto_apply_iff_mem_topologicalClosure_span_right (R : A →L[𝕜] E →L[𝕜] E)
    (hR : ∀ a b z, R (a * b) z = R b (R a z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) {z : E} :
    Tendsto (fun e ↦ R e z) l (𝓝 z) ↔
      z ∈ (span 𝕜 (Set.range fun p : A × E ↦ R p.1 p.2)).topologicalClosure :=
  ⟨fun h ↦ (isClosed_topologicalClosure _).mem_of_tendsto h <| .of_forall fun e ↦
      apply_mem_topologicalClosure_span R e z,
    tendsto_apply_of_mem_topologicalClosure_span_right R hR hC hl⟩

end ApproximateIdentity

end ContinuousLinearMap
