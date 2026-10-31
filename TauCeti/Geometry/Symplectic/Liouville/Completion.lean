/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Symplectic.Liouville.Domain
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Completions of Liouville domains

The **completion** of a Liouville domain `(W, α)` attaches to `W` the positive half of the
symplectization of its boundary: it is `W ∪ (∂W × [1, ∞))`, glued along `∂W = ∂W × {1}`, with
the primitive `r α|∂W` on the cylindrical end. Symplectic homology, Hamiltonians linear at infinity
and the Viterbo transfer maps are defined on completions.

A Liouville domain here is a compact sublevel set `W = {f ≤ c}` inside an ambient manifold `M`
(`TauCeti.IsLiouvilleDomain`), and the completion is likewise realized inside `M`
(`TauCeti.IsLiouvilleCompletion`): `M` is a completion of `W` when the Liouville field `Z` of `α`,
the vector field with `ι_Z ω = α`, is complete, and its flow carries every point of `M` into `W`.
For instance, the cotangent bundle `T*M` of a compact Riemannian manifold without boundary is the
completion of its unit codisc bundle
(`TauCeti.CotangentBundle.isLiouvilleCompletion_codiscBundle`).

The Liouville field is unique, because the form is nondegenerate, and it points strictly out of
`W` along the boundary. So a trajectory of `Z` crosses `∂W` only outwards: a point that is not in
the interior of `W` never returns to `W` under the forward flow
(`TauCeti.IsLiouvilleDomain.flowOf_notMem`), and when `Z` is complete the trajectories through
distinct boundary points are disjoint, each meeting the boundary only once
(`TauCeti.IsLiouvilleDomain.injOn_flowOf`). For a completion this
gives the cylindrical end in coordinates: every point `x` outside `W` is `ψ_t(y)` for exactly one
point `y` of the boundary `∂W` and one time `t > 0`, where `ψ` is the Liouville flow
(`TauCeti.IsLiouvilleCompletion.existsUnique_flowOf_eq`). So `M` is the disjoint union of `W` and
the flow-out `(y, t) ↦ ψ_t(y)` of `∂W × (0, ∞)`, which is the end `∂W × (1, ∞)` of the completion
in the coordinate `r = e^t`. This file proves this point-set description of the end; the
identification of the primitive on it with `r α|∂W` is not treated here.

## Main definitions

* `TauCeti.IsLiouvilleCompletion`: `M` is a completion of the Liouville domain `W`.

## Main results

* `TauCeti.IsLiouvilleDomain.flowOf_notMem`: the forward Liouville flow of a point outside the
  interior of a Liouville domain stays outside the domain.
* `TauCeti.IsLiouvilleDomain.injOn_flowOf`: for a complete Liouville field, the trajectories
  through the boundary are disjoint.
* `TauCeti.IsLiouvilleCompletion.existsUnique_flowOf_eq`: the cylindrical end of a completion,
  each point outside `W` lies on exactly one outgoing Liouville trajectory from `∂W`.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (Liouville domains and their completions).
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1.
-/

public section

open Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M}
  {Z : (x : M) → TangentSpace I x}

namespace IsLiouvilleDomain

variable [CompleteSpace E] [T2Space M] [BoundarylessManifold I M]

/-- **The Liouville flow never enters a Liouville domain.** Let `Z` be the Liouville field,
`ι_Z ω = α`. If `x` is not an interior point of the Liouville domain `W`, then its trajectory under
the flow of `Z` lies outside `W` at every positive time `t` at which it is defined. -/
theorem flowOf_notMem (h : IsLiouvilleDomain ω α W) (hZ : RoughForm.interior Z ω.1 = α.1) {x : M}
    (hx : x ∉ interior W) {t : ℝ} (ht : 0 < t) (htx : (t, x) ∈ flowDomain Z) :
    flowOf Z t x ∉ W := by
  have hZs : ContMDiff I I.tangent 1 (T% Z) := (h.contMDiff_of_interior_eq hZ).of_le (by simp)
  obtain ⟨f, c, hf, rfl, hfc⟩ := h.exists_sublevel_of_interior_eq hZ
  -- The open set `{f < c}` lies in the interior of `W = {f ≤ c}`, so `c ≤ f x`.
  have hcx : c ≤ f x := not_lt.1 fun hlt ↦ hx <|
    interior_maximal (fun _ hy ↦ le_of_lt hy) (isOpen_lt hf continuous_const) hlt
  -- The trajectory is an integral curve on its open interval of existence, which contains
  -- `[0, t]`, and it crosses the level `f⁻¹(c)` only upwards.
  have hdom : {τ | (τ, x) ∈ flowDomain Z} = maximalIntegralCurveInterval Z x :=
    ext fun _ ↦ mem_flowDomain
  have hs : IsOpen {τ | (τ, x) ∈ flowDomain Z} := hdom ▸ isOpen_maximalIntegralCurveInterval
  have hIcc : Icc 0 t ⊆ {τ | (τ, x) ∈ flowDomain Z} := hdom ▸
    ordConnected_maximalIntegralCurveInterval.out (mem_flowDomain.1 (mem_flowDomain_zero hZs x))
      (mem_flowDomain.1 htx)
  have hlt := (isMIntegralCurveOn_flowOf hZs x).lt_apply_of_le_apply hs hIcc
    (hf.comp_continuousOn ((isMIntegralCurveOn_flowOf hZs x).continuousOn.mono hIcc))
    (fun τ _ hτ ↦ ⟨(hfc _ hτ).1.mdifferentiableAt (by simp), (hfc _ hτ).2⟩)
    (by rwa [flowOf_zero hZs]) ⟨ht, le_rfl⟩
  exact not_le.2 hlt

/-- **The Liouville trajectories through the boundary are disjoint.** If the Liouville field `Z`
of a Liouville domain `W` is complete, then `(y, t) ↦ ψ_t(y)` is injective on `∂W × ℝ`, where `ψ`
is the flow of `Z`. -/
theorem injOn_flowOf [FiniteDimensional ℝ E] (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hc : IsCompleteVectorField Z) :
    InjOn (fun p : M × ℝ ↦ flowOf Z p.2 p.1) (frontier W ×ˢ univ) := by
  have hZs : ContMDiff I I.tangent 1 (T% Z) := (h.contMDiff_of_interior_eq hZ).of_le (by simp)
  -- On a complete field, `flowOf` is the global flow `ψ`, which satisfies the group law.
  set ψ := globalFlow Z hZs hc
  have hψ : ∀ t y, flowOf Z t y = ψ t y := fun t y ↦
    (flowOf_apply Z t y).trans (globalFlow_apply hZs hc t y).symm
  -- If the times differ, the boundary point with the earlier time is the other one flowed forward
  -- for a positive time, which leaves `W`; so the times agree, and then so do the points.
  have hlt : ∀ ⦃p q : M × ℝ⦄, p.1 ∈ frontier W → q.1 ∈ frontier W → ψ p.2 p.1 = ψ q.2 q.1 →
      ¬p.2 < q.2 := fun p q hp hq hpq hpq₂ ↦ by
    have hp₁ : p.1 = ψ (q.2 - p.2) q.1 := by
      rw [← ψ.map_zero_apply p.1, ← neg_add_cancel p.2, Flow.map_add, hpq, ← Flow.map_add,
        neg_add_eq_sub]
    refine h.flowOf_notMem hZ hq.2 (sub_pos.2 hpq₂) (hc.mem_flowDomain _ _) ?_
    rw [hψ, ← hp₁]
    exact h.isClosed.frontier_subset hp
  rintro p ⟨hp, -⟩ q ⟨hq, -⟩ hpq
  simp only [hψ] at hpq
  have h₂ : p.2 = q.2 := le_antisymm (not_lt.1 (hlt hq hp hpq.symm)) (not_lt.1 (hlt hp hq hpq))
  refine Prod.ext ?_ h₂
  rw [← ψ.map_zero_apply p.1, ← ψ.map_zero_apply q.1, ← neg_add_cancel p.2, Flow.map_add,
    Flow.map_add, hpq, h₂]

end IsLiouvilleDomain

/-- A manifold `M` is a **completion** of the Liouville domain `W ⊆ M`, for the form `ω` with
primitive `α`, when the Liouville field `Z` of `α`, the vector field with `ι_Z ω = α`, is complete
and its flow carries every point of `M` into `W` in some time. Then `M` is the union of `W` and of
the forward flow-out of its boundary, a cylindrical end
(`TauCeti.IsLiouvilleCompletion.existsUnique_flowOf_eq`). -/
structure IsLiouvilleCompletion (ω : SmoothTwoForm I M) (α : SmoothForm I M ℝ 1) (W : Set M) :
    Prop extends IsLiouvilleDomain ω α W where
  /-- The Liouville field of a completion is complete, and its flow carries every point into the
  Liouville domain. -/
  exists_isCompleteVectorField : ∃ Z : (x : M) → TangentSpace I x,
    RoughForm.interior Z ω.1 = α.1 ∧ IsCompleteVectorField Z ∧ ∀ x, ∃ t, flowOf Z t x ∈ W

namespace IsLiouvilleCompletion

/-- The Liouville field of a completion is complete. -/
theorem isCompleteVectorField (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) :
    IsCompleteVectorField Z := by
  obtain ⟨Z', hZ', hc, -⟩ := h.exists_isCompleteVectorField
  rwa [h.isNondegenerate.interior_injective (hZ.trans hZ'.symm)]

/-- The Liouville flow of a completion carries every point into the Liouville domain. -/
theorem exists_flowOf_mem (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.1 = α.1)
    (x : M) : ∃ t, flowOf Z t x ∈ W := by
  obtain ⟨Z', hZ', -, hW⟩ := h.exists_isCompleteVectorField
  rw [h.isNondegenerate.interior_injective (hZ.trans hZ'.symm)]
  exact hW x

variable [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless]

/-- Every point outside the Liouville domain of a completion lies on an outgoing Liouville
trajectory from the boundary, at a positive time. -/
private theorem exists_flowOf_eq (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1)
    {x : M} (hx : x ∉ W) : ∃ y ∈ frontier W, ∃ t, 0 < t ∧ flowOf Z t y = x := by
  have hZs : ContMDiff I I.tangent 1 (T% Z) := (h.contMDiff_of_interior_eq hZ).of_le (by simp)
  have hc := h.isCompleteVectorField hZ
  set ψ := globalFlow Z hZs hc
  have hψ : ∀ t y, flowOf Z t y = ψ t y := fun t y ↦
    (flowOf_apply Z t y).trans (globalFlow_apply hZs hc t y).symm
  obtain ⟨t₀, ht₀⟩ := h.exists_flowOf_mem hZ x
  -- The time `t₀` is negative: the forward flow of `x ∉ W` stays outside `W`.
  have ht₀neg : t₀ < 0 := by
    refine lt_of_not_ge fun ht₀pos ↦ ?_
    rcases ht₀pos.lt_or_eq with ht₀pos | rfl
    · exact h.flowOf_notMem hZ (fun hxi ↦ hx (interior_subset hxi)) ht₀pos
        (hc.mem_flowDomain t₀ x) ht₀
    · exact hx (by rwa [hψ, Flow.map_zero_apply] at ht₀)
  obtain ⟨f, c, hf, rfl, hfc⟩ := h.exists_sublevel_of_interior_eq hZ
  have hcx : c < f x := not_le.1 hx
  rw [hψ] at ht₀
  -- By the intermediate value theorem, the trajectory meets the level `f⁻¹(c)`, the boundary,
  -- at some time `τ ∈ [t₀, 0]`, which is negative since `f x > c`.
  have hcont : ContinuousOn (fun τ ↦ f (ψ τ x)) (Icc t₀ 0) :=
    (hf.comp (ψ.continuous continuous_id continuous_const)).continuousOn
  obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Icc ht₀neg.le hcont
    ⟨ht₀, by simpa only [Flow.map_zero_apply] using hcx.le⟩
  have hτ0 : τ < 0 := hτ.2.lt_of_ne fun h0 ↦ by
    simp only [h0, Flow.map_zero_apply] at hfτ
    exact hcx.ne' hfτ
  refine ⟨ψ τ x, ?_, -τ, neg_pos.2 hτ0, ?_⟩
  · rw [frontier_setOf_le_eq_of_mvfderiv_pos hf fun y hy ↦ (hfc y hy).2]
    exact hfτ
  · rw [hψ, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]

/-- **The cylindrical end of a completion.** Let `M` be a completion of the Liouville domain `W`,
with Liouville flow `ψ`. Every point `x` outside `W` is `ψ_t(y)` for exactly one point `y` of the
boundary of `W` and one time `t > 0`. -/
theorem existsUnique_flowOf_eq (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1)
    {x : M} (hx : x ∉ W) : ∃! p : M × ℝ, p.1 ∈ frontier W ∧ 0 < p.2 ∧ flowOf Z p.2 p.1 = x := by
  obtain ⟨y, hy, t, ht, hyx⟩ := h.exists_flowOf_eq hZ hx
  exact ⟨(y, t), ⟨hy, ht, hyx⟩, fun q ⟨hq, hqt, hqx⟩ ↦
    h.injOn_flowOf hZ (h.isCompleteVectorField hZ) ⟨hq, mem_univ _⟩ ⟨hy, mem_univ _⟩
      (hqx.trans hyx.symm)⟩

end IsLiouvilleCompletion

end TauCeti
