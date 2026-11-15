/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.Homotopy.Basic

/-!
# Moving points along flow lines is homotopic to the identity

Let `ϕ` be a continuous flow on a space `α` and `S` a subset of `α`. A map of `S` which moves each
point `x` along its flow line for a time `τ x` depending continuously on `x` is homotopic to the
identity of `S`, as long as the flow line of `x` stays in `S` between the times `0` and `τ x`
(`Flow.homotopic_id_of_apply_mem`): the homotopy moves `x` for the time `t τ x` at time `t`.

Such maps arise when the flow of a gradient-like vector field is used to move points between the
levels of a function, as in Morse theory.
-/

public section

namespace Flow

variable {α : Type*} [TopologicalSpace α]

/-- **Moving points along flow lines is homotopic to the identity.** Let `ϕ` be a flow on `α` and
`τ` a continuous function on a subset `S` of `α` such that the flow line of each `x ∈ S` stays in
`S` up to the time `τ x`. Then a map `F` of `S` which sends `x` to `ϕ (τ x) x` is homotopic to the
identity of `S`. -/
theorem homotopic_id_of_apply_mem (ϕ : Flow ℝ α) {S : Set α} {τ : S → ℝ} (hτ : Continuous τ)
    (hS : ∀ (x : S) (t : ℝ), 0 ≤ t → t ≤ 1 → ϕ (t * τ x) x ∈ S) (F : C(S, S))
    (hF : ∀ x, (F x : α) = ϕ (τ x) x) :
    F.Homotopic (ContinuousMap.id S) :=
  ⟨.symm
    { toFun p := ⟨ϕ (p.1 * τ p.2) p.2, hS p.2 p.1 p.1.2.1 p.1.2.2⟩
      continuous_toFun :=
        (ϕ.continuous (continuous_subtype_val.fst'.mul (hτ.comp continuous_snd))
          continuous_subtype_val.snd').subtype_mk _
      map_zero_left x := Subtype.ext <| by simp
      map_one_left x := Subtype.ext <| by simp [hF] }⟩

end Flow
