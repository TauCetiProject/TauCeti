/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Jump

/-!
# Hyperplane jump obstruction for local Sobolev classes

The indicator `{x | 0 < ℓ x}.indicator (fun _ => (1 : ℝ))` of an open half-space defined by a
nonzero continuous linear functional `ℓ : E →L[ℝ] ℝ` on a finite-dimensional real normed space `E`
lies in every local `Lᵖ` class everywhere (`TauCeti.memLpLoc_indicator_pos`), yet lies in no local
Sobolev class `TauCeti.MemWkpLoc p U (k + 1)` of positive order when `interior U` meets `ker ℓ`
(`TauCeti.not_memWkpLoc_indicator_pos`).

## Main declarations

* `TauCeti.not_memWkpLoc_indicator_pos`: the indicator of `{x | 0 < ℓ x}` (`ℓ ≠ 0`) lies in no
  positive-order `MemWkpLoc p U (k + 1)` when `interior U` meets `ker ℓ`.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace

namespace TauCeti

/-- The indicator of an open half-space `{x | 0 < ℓ x}` (for `ℓ ≠ 0`) lies in no local Sobolev
class of positive order on any set whose interior meets `ker ℓ`, although it is locally `Lᵖ`
there (`TauCeti.memLpLoc_indicator_pos`). -/
theorem not_memWkpLoc_indicator_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {p : ENNReal} {U : Set E} {k : ℕ} {ℓ : E →L[ℝ] ℝ}
    (hℓ : ℓ ≠ 0) {x₀ : E} (hx₀ : x₀ ∈ interior U) (hx₀' : ℓ x₀ = 0) :
    ¬ MemWkpLoc p U (k + 1) ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := fun h => by
  obtain ⟨-, D, hD, -⟩ := memWkpLoc_succ_iff.1 h
  exact not_hasWeakFDerivOn_indicator_pos hℓ (Ω := Opens.interior U) hx₀ hx₀' D hD

end TauCeti
