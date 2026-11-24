/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Fixed points of a Lipschitz family of contractions

Let `T r`, for `r` in a set `S` of a pseudometric space, be maps sending a complete nonempty set
`s` into itself, contracting on `s` with a common constant `K < 1`, and depending
Lipschitz-continuously on `r` with constant `C`, uniformly on `s`. By the Banach fixed-point theorem
each `T r` has a unique fixed point `y r` in `s`, and `r ↦ y r` is Lipschitz on `S` with constant
`C / (1 - K)` (`TauCeti.exists_lipschitzOnWith_forall_fixedPt`).
-/

public section

open Set
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

end TauCeti
