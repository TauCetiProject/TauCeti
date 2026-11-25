/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# Regularity estimates from qualitative regularity

Let `T : X → Lᵖ(U)` be a continuous linear map from a Banach space. If every `T x` is, on `U`, the
value of a `W^{k,p}(U)` function, then this representation is bounded: there is a constant `C`
with `‖v‖_{W^{k,p}(U)} ≤ C ‖x‖` for the representative `v` of `T x`
(`TauCeti.Wkp.exists_norm_le_of_forall_exists_value_ae_eq`). It is the closed graph theorem in the
form `ContinuousLinearMap.exists_norm_le_of_range_le_range`, applied to the injective value map
`TauCeti.Wkp.valueL`. This turns qualitative interior regularity of the solutions of a linear
equation into an a priori estimate, without tracking constants through the regularity proof.

## Main results

* `TauCeti.Wkp.exists_norm_le_of_forall_exists_value_ae_eq`: the closed graph estimate.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti.Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {k : ℕ}

/-- **The closed graph estimate.** Let `T : X → Lᵖ(U)` be a continuous linear map from a Banach
space such that every `T x` agrees almost everywhere on `U` with the value of an element of
`W^{k,p}(U)`. Then there is a constant `C` such that every `T x` is represented on `U` by an
element `v` with `‖v‖ ≤ C ‖x‖`. -/
theorem exists_norm_le_of_forall_exists_value_ae_eq {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (T : X →L[ℝ] Lp ℝ p (mu.restrict (U : Set E)))
    (h : ∀ x, ∃ v : Wkp mu U p k, (value k v : E → ℝ) =ᵐ[mu.restrict (U : Set E)] T x) :
    ∃ C : ℝ, ∀ x, ∃ v : Wkp mu U p k,
      (value k v : E → ℝ) =ᵐ[mu.restrict (U : Set E)] T x ∧ ‖v‖ ≤ C * ‖x‖ := by
  -- The value map is injective, and its range contains that of `T`.
  have hval {x : X} {v : Wkp mu U p k}
      (hv : (value k v : E → ℝ) =ᵐ[mu.restrict (U : Set E)] T x) : valueL k v = T x := by
    rw [valueL_apply]
    exact Lp.ext hv
  obtain ⟨C, -, hC⟩ := T.exists_norm_le_of_range_le_range (valueL k) (valueL_injective k)
    fun _ ⟨x, hx⟩ ↦ hx ▸ (h x).elim fun v hv ↦ ⟨v, hval hv⟩
  exact ⟨C, fun x ↦ (h x).elim fun v hv ↦ ⟨v, hv, hC x v (hval hv)⟩⟩

end TauCeti.Wkp
