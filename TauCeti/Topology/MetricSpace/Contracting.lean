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
    {T : P → α → α} {K C : ℝ} (hK : K < 1) (hmaps : ∀ r ∈ S, MapsTo (T r) s s)
    (hT : ∀ r ∈ S, ∀ x ∈ s, ∀ y ∈ s, dist (T r x) (T r y) ≤ K * dist x y)
    (hTr : ∀ r ∈ S, ∀ r' ∈ S, ∀ x ∈ s, dist (T r x) (T r' x) ≤ C * dist r r') :
    ∃ y : P → α, LipschitzOnWith (C / (1 - K)).toNNReal y S ∧
      ∀ r ∈ S, y r ∈ s ∧ T r (y r) = y r ∧ ∀ v ∈ s, T r v = v → v = y r := by
  have hK' : 0 < 1 - K := sub_pos.2 hK
  have hchoice (r : P) : ∃ y, r ∈ S → y ∈ s ∧ T r y = y := by
    by_cases hr : r ∈ S
    · have hcontr : ContractingWith K.toNNReal ((hmaps r hr).restrict _ s s) :=
        ⟨Real.toNNReal_lt_one.2 hK, LipschitzWith.of_dist_le_mul fun x x' ↦
          (hT r hr x x.property x' x'.property).trans
            (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) dist_nonneg)⟩
      obtain ⟨x, hx⟩ := hsne
      obtain ⟨y, hy, hfy, -⟩ := hcontr.exists_fixedPoint' hs (hmaps r hr) hx (edist_ne_top _ _)
      exact ⟨y, fun _ ↦ ⟨hy, hfy⟩⟩
    · exact ⟨hsne.some, fun h ↦ absurd h hr⟩
  choose y hy using hchoice
  -- Two fixed points `y r` of `T r` and `v` of `T r'` satisfy
  -- `dist (y r) v ≤ K * dist (y r) v + dist (T r v) (T r' v)`.
  have hdist (r : P) (hr : r ∈ S) (r' : P) (v : α) (hv : v ∈ s) (hfv : T r' v = v) :
      (1 - K) * dist (y r) v ≤ dist (T r v) (T r' v) := by
    have h : dist (y r) v ≤ dist (T r (y r)) (T r v) + dist (T r v) (T r' v) := by
      simpa only [(hy r hr).2, hfv] using dist_triangle (T r (y r)) (T r v) (T r' v)
    linarith [hT r hr _ (hy r hr).1 v hv]
  refine ⟨y, LipschitzOnWith.of_dist_le_mul fun r hr r' hr' ↦ ?_, fun r hr ↦
    ⟨(hy r hr).1, (hy r hr).2, fun v hv hfv ↦ ?_⟩⟩
  · have h := (le_div_iff₀' hK').2 (hdist r hr r' _ (hy r' hr').1 (hy r' hr').2)
    calc dist (y r) (y r') ≤ C * dist r r' / (1 - K) :=
          h.trans (div_le_div_of_nonneg_right (hTr r hr r' hr' _ (hy r' hr').1) hK'.le)
      _ = C / (1 - K) * dist r r' := by ring
      _ ≤ (C / (1 - K)).toNNReal * dist r r' :=
          mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg
  · have h := hdist r hr r v hv hfv
    rw [dist_self] at h
    exact (dist_eq_zero.1 (le_antisymm (nonpos_of_mul_nonpos_right h hK') dist_nonneg)).symm

end TauCeti
