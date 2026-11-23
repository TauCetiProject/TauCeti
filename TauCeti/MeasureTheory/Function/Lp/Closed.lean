/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Closed sets of `Lᵖ` classes defined by vanishing

For a predicate `P` on the underlying space, the `Lᵖ` classes vanishing almost everywhere on the
set where `P` holds form a closed subset of `Lᵖ` (`TauCeti.isClosed_setOf_ae_imp_eq_zero`):
convergence in `Lᵖ` implies almost everywhere convergence along a subsequence.
-/

public section

open Filter MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- The `Lᵖ` classes vanishing almost everywhere on the set where `P` holds form a closed set:
convergence in `Lᵖ` gives almost everywhere convergence along a subsequence. -/
theorem isClosed_setOf_ae_imp_eq_zero {X G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup G] {ν : Measure X} (p : ℝ≥0∞) [Fact (1 ≤ p)] (P : X → Prop) :
    IsClosed {f : Lp G p ν | ∀ᵐ y ∂ν, P y → f y = 0} := by
  refine IsSeqClosed.isClosed fun {f f₀} hf hlim ↦ ?_
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂ν, ∀ m, P y → f (ns m) y = 0 := ae_all_iff.2 fun m ↦ hf (ns m)
  filter_upwards [hae, hall] with y hy hm hP
  exact tendsto_nhds_unique hy (tendsto_const_nhds.congr fun m ↦ (hm m hP).symm)

end TauCeti
