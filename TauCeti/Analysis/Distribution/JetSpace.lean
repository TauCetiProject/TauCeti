/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.JetSpace

/-!
# Distributional pullback of jet restriction

Composing `TestFunction.jetRestrictionCLM` with any continuous linear map
`ℓ : TauCeti.JetSpace E F K m →L[ℝ] G` produces a continuous linear map on `𝓓^{n}(Ω, F)` (in
particular, a `G`-valued distribution of order at most `n` when `F = ℝ`) whose distributional
support is contained in `K` whenever `K` is closed.

## Main declarations

* `Distribution.dsupport_comp_jetRestrictionCLM_subset`: pulling back a continuous linear map on
  `TauCeti.JetSpace E F K m` along `TestFunction.jetRestrictionCLM` yields a map supported in `K`
  when `K` is closed.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]

/-- Pulling back a continuous linear map `ℓ` on `TauCeti.JetSpace E F K m` along
`TestFunction.jetRestrictionCLM` produces a continuous linear map on `𝓓^{n}(Ω, F)` (in particular,
a distribution when `F = ℝ`) whose distributional support lies in `K` whenever `K` is closed. -/
theorem dsupport_comp_jetRestrictionCLM_subset {Ω : Opens E} {K : Set E} (hK : IsClosed K)
    (m : ℕ) {n : ℕ∞} (hm : (m : ℕ∞) ≤ n) (ℓ : TauCeti.JetSpace E F K m →L[ℝ] G) :
    dsupport (ℓ ∘L TestFunction.jetRestrictionCLM Ω K m hm) ⊆ K := by
  have hvan : IsVanishingOn (ℓ ∘L TestFunction.jetRestrictionCLM Ω K m hm) Kᶜ := fun φ hφ ↦ by
    simp [TestFunction.jetRestrictionCLM_eq_zero_of_tsupport_subset_compl m hm hφ]
  exact Disjoint.subset_right_of_subset_union
    (by simp) (hvan.disjoint_dsupport hK.isOpen_compl).symm

end Distribution
