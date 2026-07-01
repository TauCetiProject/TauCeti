module

public import TauCeti.Probability.Exchangeability.PathSpace.Shift

/-!
# Process shift operation

The process-level path shift for a process `X : ℕ → Ω → α`, used to build the de Finetti
block-product factorisation:

* `processShift X m` — the shifted random path `ω ↦ (n ↦ X (m + n) ω)`, defined as the `m`-fold
  merged path-space shift `(shift α)^[m]` of the process's path.

The `processCons` / `processTail` operations on sequence-valued random variables, together with
their σ-algebra-contraction lemmas, live in `TauCeti.Probability.Process.Tail`.

Its exported API is the `@[simp]` coordinate equation `processShift_apply`.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/ShiftOperations.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The shifted random path of a process, as the `m`-fold path-space shift `(shift α)^[m]` of the
process's path (reusing the merged path shift): `ω ↦ (n ↦ X (m + n) ω)`. -/
def processShift (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω => (shift α)^[m] fun n => X n ω

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Coordinate equation for `processShift`: its `n`th coordinate is `X (m + n)`. -/
@[simp]
theorem processShift_apply (X : ℕ → Ω → α) (m n : ℕ) (ω : Ω) :
    processShift X m ω n = X (m + n) ω := by
  simp only [processShift, shift_iterate_apply, Nat.add_comm]

/-- The shifted process is measurable when its tail coordinates `X (m + ·)` are. -/
@[fun_prop]
theorem measurable_processShift {X : ℕ → Ω → α} {m : ℕ} (hX : ∀ n, Measurable (X (m + n))) :
    Measurable (processShift X m) := by
  refine measurable_pi_lambda _ fun n => ?_
  simpa only [processShift_apply] using hX n

end Probability

end TauCeti
