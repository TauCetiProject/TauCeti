/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Fixed points of families of contractions

Let `T r`, for `r` in a set `S` of a pseudometric space, be maps sending a complete nonempty set
`s` into itself, contracting on `s` with a common constant `K < 1`, and depending
Lipschitz-continuously on `r` with constant `C`, uniformly on `s`. By the Banach fixed-point theorem
each `T r` has a unique fixed point `y r` in `s`, and `r ↦ y r` is Lipschitz on `S` with constant
`C / (1 - K)` (`TauCeti.exists_lipschitzOnWith_forall_fixedPt`).

If instead a family of maps `F a`, for `a` in a set `S` of a topological space, contracts one set
`s` with one constant `K`, and `a ↦ F a y` is merely continuous on `S` for every `y ∈ s`, then the
fixed points of the maps `F a` depend continuously on `a`
(`TauCeti.continuousOn_of_forall_contractingWith`). The proof uses Mathlib's a posteriori estimate
`ContractingWith.dist_le_of_fixedPoint`. Mathlib's `ContractingWith.fixedPoint_lipschitz_in_map`
compares the fixed points of two contractions of a complete space; here the maps are restricted to
`s` and the family is indexed by a topological space.
-/

public section

open Filter Set Topology
open scoped NNReal

namespace TauCeti

/-- **Fixed points of a Lipschitz family of contractions.** Let `T r`, for `r ∈ S`, send a complete
nonempty set `s` into itself, with `dist (T r x) (T r y) ≤ K * dist x y` on `s` for a common
`K < 1`, and `dist (T r x) (T r' x) ≤ C * dist r r'` on `s`. Then each `T r` has a unique fixed
point `y r` in `s`, and `y` is Lipschitz on `S` with constant `C / (1 - K)`. -/
theorem exists_lipschitzOnWith_forall_fixedPt {α P : Type*} [MetricSpace α]
    [PseudoMetricSpace P] {s : Set α} (hs : IsComplete s) (hsne : s.Nonempty) {S : Set P}
    {T : P → α → α} {K : ℝ≥0} {C : ℝ} (hK : K < 1) (hmaps : ∀ r ∈ S, MapsTo (T r) s s)
    (hT : ∀ r ∈ S, ∀ x ∈ s, ∀ y ∈ s, dist (T r x) (T r y) ≤ K * dist x y)
    (hTr : ∀ r ∈ S, ∀ r' ∈ S, ∀ x ∈ s, dist (T r x) (T r' x) ≤ C * dist r r') :
    ∃ y : P → α, LipschitzOnWith (C / (1 - K)).toNNReal y S ∧
      ∀ r ∈ S, y r ∈ s ∧ T r (y r) = y r ∧ ∀ v ∈ s, T r v = v → v = y r := by
  have hcontr (r : P) (hr : r ∈ S) : ContractingWith K ((hmaps r hr).restrict _ s s) :=
    ⟨hK, LipschitzWith.of_dist_le_mul fun x x' ↦ hT r hr x x.property x' x'.property⟩
  have hchoice (r : P) : ∃ y, r ∈ S → y ∈ s ∧ T r y = y := by
    by_cases hr : r ∈ S
    · obtain ⟨x, hx⟩ := hsne
      obtain ⟨y, hy, hfy, -⟩ :=
        (hcontr r hr).exists_fixedPoint' hs (hmaps r hr) hx (edist_ne_top _ _)
      exact ⟨y, fun _ ↦ ⟨hy, hfy⟩⟩
    · exact ⟨hsne.some, fun h ↦ absurd h hr⟩
  choose y hy using hchoice
  refine ⟨y, LipschitzOnWith.of_dist_le_mul fun r hr r' hr' ↦ ?_, fun r hr ↦
    ⟨(hy r hr).1, (hy r hr).2, fun v hv hfv ↦ ?_⟩⟩
  · -- The fixed points of the restrictions of `T r` and `T r'` to `s`, uniformly close.
    have h := (hcontr r hr).dist_fixedPoint_fixedPoint_of_dist_le'
      ((hmaps r' hr').restrict _ s s) (x := ⟨y r, (hy r hr).1⟩) (y := ⟨y r', (hy r' hr').1⟩)
      (Subtype.ext (hy r hr).2) (Subtype.ext (hy r' hr').2) fun v ↦ hTr r hr r' hr' v v.property
    rw [Subtype.dist_eq] at h
    calc dist (y r) (y r') ≤ C * dist r r' / (1 - K) := h
      _ = C / (1 - K) * dist r r' := by ring
      _ ≤ (C / (1 - K)).toNNReal * dist r r' :=
          mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg
  · exact congrArg Subtype.val ((hcontr r hr).fixedPoint_unique' (x := ⟨v, hv⟩)
      (y := ⟨y r, (hy r hr).1⟩) (Subtype.ext hfv) (Subtype.ext (hy r hr).2))

/-- **The fixed points of a uniformly contracting family depend continuously on the parameter.**
If every map `F a`, for `a ∈ S`, maps `s` to itself as a contraction with one constant `K` and
fixes a point `v a` of `s`, and `a ↦ F a y` is continuous on `S` for every `y ∈ s`, then `v` is
continuous on `S`: by the a posteriori estimate `ContractingWith.dist_le_of_fixedPoint`,
`dist (v a) (v a')` is at most `dist (F a (v a')) (F a' (v a')) / (1 - K)`. -/
theorem continuousOn_of_forall_contractingWith {α X : Type*} [TopologicalSpace α]
    [MetricSpace X] {S : Set α} {s : Set X} {F : α → X → X} {v : α → X} {K : ℝ≥0}
    (hmaps : ∀ a ∈ S, MapsTo (F a) s s)
    (hF : ∀ a (ha : a ∈ S), ContractingWith K ((hmaps a ha).restrict _ _ _))
    (hv : ∀ a ∈ S, v a ∈ s ∧ F a (v a) = v a)
    (hc : ∀ y ∈ s, ContinuousOn (fun a ↦ F a y) S) : ContinuousOn v S := by
  intro a' ha'
  have hdist : ∀ a ∈ S, dist (v a) (v a') ≤ dist (F a (v a')) (F a' (v a')) / (1 - K) := by
    intro a ha
    have h := (hF a ha).dist_le_of_fixedPoint ⟨v a', (hv a' ha').1⟩
      (y := ⟨v a, (hv a ha).1⟩) (Subtype.ext (hv a ha).2)
    rw [(hv a' ha').2, dist_comm, dist_comm (F a _)]
    simpa only [Subtype.dist_eq, MapsTo.val_restrict_apply] using h
  have hlim : Tendsto (fun a ↦ dist (F a (v a')) (F a' (v a')) / (1 - K)) (𝓝[S] a') (𝓝 0) := by
    simpa using ((hc _ (hv a' ha').1 a' ha').tendsto.dist
      (tendsto_const_nhds (x := F a' (v a')))).div_const (1 - K)
  exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (.of_forall fun _ ↦ dist_nonneg)
    (eventually_nhdsWithin_of_forall hdist) hlim)

end TauCeti
