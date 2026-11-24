/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Universe-lifting induction across iterated operator spaces

For normed spaces `E : Type u` and `F : Type v` over a nontrivially normed field `𝕜`, the space
`E →L[𝕜] F` lives in `Type (max u v)`. Inductive arguments on `k : ℕ` that pass from `F` at step
`k + 1` to `E →L[𝕜] F` at step `k` therefore cannot directly generalize over `F : Type v`, since
`E →L[𝕜] F` leaves `Type v`.

`TauCeti.nat_induction_clm_ulift` performs the induction on `k` over spaces in `Type (max u v)`
and specializes to `ULift.{u} F`, while `TauCeti.nat_induction_clm_ulift₂` does the same for
predicates on two codomains `F` and `G`.
-/

public section

namespace TauCeti

universe u v w

/-- An induction principle on `k : ℕ` for predicates indexed by a normed space
`F : Type (max u v)` over `𝕜`, whose inductive step passes from `E →L[𝕜] F` at `k` to `F` at
`k + 1`, concluding the property at `ULift.{u} F` for an arbitrary `F : Type v`. -/
theorem nat_induction_clm_ulift (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (motive : ℕ → ∀ (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace 𝕜 F], Prop)
    (h0 : ∀ (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace 𝕜 F], motive 0 F)
    (hsucc : ∀ (k : ℕ) (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace 𝕜 F],
      motive k (E →L[𝕜] F) → motive (k + 1) F)
    (k : ℕ) (F : Type v) [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    motive k (ULift.{u} F) := by
  have aux : ∀ (k : ℕ) (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace 𝕜 F],
      motive k F := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => exact fun F _ _ => hsucc k F (ih (E →L[𝕜] F))
  exact aux k (ULift.{u} F)

/-- Two-codomain counterpart of `TauCeti.nat_induction_clm_ulift`: the inductive step passes from
`E →L[𝕜] F` and `E →L[𝕜] G` at `k` to `F` and `G` at `k + 1`, concluding at `ULift.{u} F` and
`ULift.{u} G` for arbitrary `F : Type v` and `G : Type w`. -/
theorem nat_induction_clm_ulift₂ (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (motive : ℕ → ∀ (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
      (G : Type (max u w)) [NormedAddCommGroup G] [NormedSpace 𝕜 G], Prop)
    (h0 : ∀ (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
      (G : Type (max u w)) [NormedAddCommGroup G] [NormedSpace 𝕜 G], motive 0 F G)
    (hsucc : ∀ (k : ℕ) (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
      (G : Type (max u w)) [NormedAddCommGroup G] [NormedSpace 𝕜 G],
      motive k (E →L[𝕜] F) (E →L[𝕜] G) → motive (k + 1) F G)
    (k : ℕ) (F : Type v) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (G : Type w) [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    motive k (ULift.{u} F) (ULift.{u} G) := by
  have aux : ∀ (k : ℕ) (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
      (G : Type (max u w)) [NormedAddCommGroup G] [NormedSpace 𝕜 G], motive k F G := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => exact fun F _ _ G _ _ => hsucc k F G (ih (E →L[𝕜] F) (E →L[𝕜] G))
  exact aux k (ULift.{u} F) (ULift.{u} G)

end TauCeti
