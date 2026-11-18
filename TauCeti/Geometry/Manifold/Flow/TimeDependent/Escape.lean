/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent

/-!
# The escape criterion for time-dependent flows

Let `X` be a jointly `C¹` time-dependent vector field on a boundaryless manifold `M` modelled on a
complete space, and let `φ_{s,t} = TauCeti.timeDependentFlowOf X s t` be its maximal
time-dependent flow. A solution can fail to exist up to a finite time `b` only by leaving every
compact subset of `M` before `b`. This file proves the resulting **escape criterion**: if, at every
time `u` between `s` and `b` at which it is defined, the solution `φ_{s,u}(x)` lies in a fixed
compact set `K`, then it is defined at time `b`, and in fact a little beyond `b`.

On a compact manifold the hypothesis holds with `K = M`, so the flow is defined at all times; this
is also the case `K = univ` of `TauCeti.isCompleteVectorField_timeDependentSuspensionField`. On a
noncompact manifold a solution of an equation as simple as `y' = y²` on `ℝ` reaches infinity in
finite time, and the compact containment of the solution is the hypothesis under which its
existence through a given time interval, for instance `[0, 1]` in Moser's argument, can be
asserted.

The proof applies the autonomous escape lemma `eventually_notMem_nhdsLT_maximalIntegralCurve` to
the suspension `(t, x) ↦ (1, X t x)` of `X` on `ℝ × M` and to the compact set `[s, b] × K`: the
maximal integral curve of the suspension through `(s, x)` runs at unit speed in the clock
coordinate, so it stays in `[s, b] × K` up to the time at which it would leave the domain of the
flow.

## Main results

* `TauCeti.mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ico`: a solution confined to a
  compact set on `[s, b)` is defined at time `b ≥ s`.
* `TauCeti.mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ioc`: the same backwards in time.
* `TauCeti.mem_timeDependentFlowDomain_of_isCompact_of_mapsTo`: a solution confined to a compact
  set at every time between `s` and `t` is defined at time `t`.
* `TauCeti.exists_gt_Icc_subset_setOf_mem_timeDependentFlowDomain` and
  `TauCeti.exists_lt_Icc_subset_setOf_mem_timeDependentFlowDomain`: such a solution extends across
  the endpoint.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 9.19
  (the escape lemma) and Theorem 9.48 (the fundamental theorem on time-dependent flows).
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {X : ℝ → (x : M) → TangentSpace I x} {s t : ℝ} {x : M} {K : Set M}

omit [CompleteSpace E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
/-- At a time `s + τ` at which the flow from `(s, x)` is defined, the maximal integral curve of the
suspension through `(s, x)` is at `(s + τ, φ_{s, s + τ}(x))`. -/
private theorem maximalIntegralCurve_timeDependentSuspensionField {τ : ℝ}
    (hτ : τ ∈ maximalIntegralCurveInterval (timeDependentSuspensionField X) (s, x)) :
    ((s, s + τ), x) ∈ timeDependentFlowDomain X ∧
      maximalIntegralCurve (timeDependentSuspensionField X) (s, x) τ =
        (s + τ, timeDependentFlowOf X s (s + τ) x) := by
  have hD : ((s, s + τ), x) ∈ timeDependentFlowDomain X := by
    rw [mem_timeDependentFlowDomain, add_sub_cancel_left]
    exact mem_flowDomain.2 hτ
  refine ⟨hD, ?_⟩
  have hpt := flowOf_timeDependentSuspensionField hD
  rwa [add_sub_cancel_left, flowOf_apply] at hpt

section Escape

variable (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- **The escape criterion, forwards in time.** If the solution of the time-dependent equation
through `x` at time `s` lies in a fixed compact set `K` at every time of `[s, b)` at which it is
defined, then it is defined at time `b`. -/
theorem mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ico (hK : IsCompact K) {b : ℝ}
    (hsb : s ≤ b)
    (hmaps : MapsTo (fun u ↦ timeDependentFlowOf X s u x)
      ({u | ((s, u), x) ∈ timeDependentFlowDomain X} ∩ Ico s b) K) :
    ((s, b), x) ∈ timeDependentFlowDomain X := by
  have hW := contMDiff_timeDependentSuspensionField hX
  set W := timeDependentSuspensionField X
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval W (s, x) :=
    zero_mem_maximalIntegralCurveInterval hW.contMDiffAt
  by_contra hb
  rw [mem_timeDependentFlowDomain, mem_flowDomain] at hb
  -- The maximal interval contains `0` but not `b - s ≥ 0`, so `b - s` bounds it above.
  have hub : b - s ∈ upperBounds (maximalIntegralCurveInterval W (s, x)) := fun τ hτ ↦ by
    by_contra hlt
    exact hb (ordConnected_maximalIntegralCurveInterval.out h0 hτ
      ⟨by linarith, (not_le.1 hlt).le⟩)
  have hlub := isLUB_csSup ⟨0, h0⟩ ⟨b - s, hub⟩
  have hcb := csSup_le ⟨0, h0⟩ hub
  obtain ⟨a, ha, hc0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB hlub
  -- Just before the supremum the curve is outside `[s, b] × K`, but it is defined there and the
  -- hypothesis puts it inside.
  have hC : IsCompact (Icc s b ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨τ, hτ, hτK⟩ := (Filter.Eventually.and (Ioo_mem_nhdsLT hc0)
    (eventually_notMem_nhdsLT_maximalIntegralCurve hW hlub hC)).exists
  obtain ⟨hD, hpt⟩ :=
    maximalIntegralCurve_timeDependentSuspensionField (hsub ⟨ha.trans hτ.1, hτ.2⟩)
  rw [hpt] at hτK
  exact hτK ⟨⟨by linarith [hτ.1], by linarith [hτ.2]⟩,
    hmaps ⟨hD, by linarith [hτ.1], by linarith [hτ.2]⟩⟩

/-- **The escape criterion, backwards in time.** If the solution of the time-dependent equation
through `x` at time `s` lies in a fixed compact set `K` at every time of `(a, s]` at which it is
defined, then it is defined at time `a`. -/
theorem mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ioc (hK : IsCompact K) {a : ℝ}
    (has : a ≤ s)
    (hmaps : MapsTo (fun u ↦ timeDependentFlowOf X s u x)
      ({u | ((s, u), x) ∈ timeDependentFlowDomain X} ∩ Ioc a s) K) :
    ((s, a), x) ∈ timeDependentFlowDomain X := by
  have hW := contMDiff_timeDependentSuspensionField hX
  set W := timeDependentSuspensionField X
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval W (s, x) :=
    zero_mem_maximalIntegralCurveInterval hW.contMDiffAt
  by_contra ha
  rw [mem_timeDependentFlowDomain, mem_flowDomain] at ha
  -- The maximal interval contains `0` but not `a - s ≤ 0`, so `a - s` bounds it below.
  have hlb : a - s ∈ lowerBounds (maximalIntegralCurveInterval W (s, x)) := fun τ hτ ↦ by
    by_contra hlt
    exact ha (ordConnected_maximalIntegralCurveInterval.out hτ h0
      ⟨(not_le.1 hlt).le, by linarith⟩)
  have hglb := isGLB_csInf ⟨0, h0⟩ ⟨a - s, hlb⟩
  have hca := le_csInf ⟨0, h0⟩ hlb
  obtain ⟨b, hb, hc0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB hglb
  -- Just after the infimum the curve is outside `[a, s] × K`, but it is defined there and the
  -- hypothesis puts it inside.
  have hC : IsCompact (Icc a s ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨τ, hτ, hτK⟩ := (Filter.Eventually.and (Ioo_mem_nhdsGT hc0)
    (eventually_notMem_nhdsGT_maximalIntegralCurve hW hglb hC)).exists
  obtain ⟨hD, hpt⟩ :=
    maximalIntegralCurve_timeDependentSuspensionField (hsub ⟨hτ.1, hτ.2.trans hb⟩)
  rw [hpt] at hτK
  exact hτK ⟨⟨by linarith [hτ.1], by linarith [hτ.2]⟩,
    hmaps ⟨hD, by linarith [hτ.1], by linarith [hτ.2]⟩⟩

/-- **Existence through a time interval by compact containment.** If the solution of the
time-dependent equation through `x` at time `s` lies in a fixed compact set at every time between
`s` and `t` at which it is defined, then it is defined at time `t`, and so at every time between
`s` and `t`. -/
theorem mem_timeDependentFlowDomain_of_isCompact_of_mapsTo (hK : IsCompact K)
    (hmaps : MapsTo (fun u ↦ timeDependentFlowOf X s u x)
      ({u | ((s, u), x) ∈ timeDependentFlowDomain X} ∩ uIcc s t) K) :
    ((s, t), x) ∈ timeDependentFlowDomain X := by
  rcases le_total s t with hst | hts
  · exact mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ico hX hK hst
      (hmaps.mono_left (inter_subset_inter_right _ (Ico_subset_Icc_self.trans Icc_subset_uIcc)))
  · exact mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ioc hX hK hts
      (hmaps.mono_left (inter_subset_inter_right _ (Ioc_subset_Icc_self.trans Icc_subset_uIcc')))

/-- **Extension across the right endpoint.** A solution of the time-dependent equation through `x`
at time `s` which lies in a fixed compact set at every time of `[s, b)` at which it is defined
extends beyond `b`: it is defined on `[s, c]` for some `c > b`. -/
theorem exists_gt_Icc_subset_setOf_mem_timeDependentFlowDomain (hK : IsCompact K) {b : ℝ}
    (hmaps : MapsTo (fun u ↦ timeDependentFlowOf X s u x)
      ({u | ((s, u), x) ∈ timeDependentFlowDomain X} ∩ Ico s b) K) :
    ∃ c, b < c ∧ Icc s c ⊆ {u | ((s, u), x) ∈ timeDependentFlowDomain X} := by
  rcases lt_or_ge b s with hbs | hsb
  · -- Before the initial time there is nothing to extend: `[s, s]` already works.
    exact ⟨s, hbs, by simpa using mem_timeDependentFlowDomain_self hX s x⟩
  have hb := mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ico hX hK hsb hmaps
  obtain ⟨a, c, -, hbc, hsub⟩ := exists_Ioo_of_mem_timeDependentFlowDomain hb
  obtain ⟨d, hbd, hdc⟩ := exists_between hbc.2
  exact ⟨d, hbd, (ordConnected_setOf_mem_timeDependentFlowDomain s x).out
    (mem_timeDependentFlowDomain_self_of_mem hb) (hsub d ⟨hbc.1.trans hbd, hdc⟩)⟩

/-- **Extension across the left endpoint.** A solution of the time-dependent equation through `x`
at time `s` which lies in a fixed compact set at every time of `(a, s]` at which it is defined
extends beyond `a`: it is defined on `[c, s]` for some `c < a`. -/
theorem exists_lt_Icc_subset_setOf_mem_timeDependentFlowDomain (hK : IsCompact K) {a : ℝ}
    (hmaps : MapsTo (fun u ↦ timeDependentFlowOf X s u x)
      ({u | ((s, u), x) ∈ timeDependentFlowDomain X} ∩ Ioc a s) K) :
    ∃ c, c < a ∧ Icc c s ⊆ {u | ((s, u), x) ∈ timeDependentFlowDomain X} := by
  rcases lt_or_ge s a with hsa | has
  · -- After the initial time there is nothing to extend: `[s, s]` already works.
    exact ⟨s, hsa, by simpa using mem_timeDependentFlowDomain_self hX s x⟩
  have ha := mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ioc hX hK has hmaps
  obtain ⟨c, b, -, hac, hsub⟩ := exists_Ioo_of_mem_timeDependentFlowDomain ha
  obtain ⟨d, hcd, hda⟩ := exists_between hac.1
  exact ⟨d, hda, (ordConnected_setOf_mem_timeDependentFlowDomain s x).out
    (hsub d ⟨hcd, hda.trans hac.2⟩) (mem_timeDependentFlowDomain_self_of_mem ha)⟩

end Escape

end TauCeti
