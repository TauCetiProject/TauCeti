module

public import TauCeti.Probability.Exchangeability.PathSpace.Shift

/-!
# Process shift, cons, and tail operations

Process-level path operations for a process `X : ℕ → Ω → α`, used to build the de Finetti
block-product factorisation:

* `processShift X m` — the shifted random path `ω ↦ (n ↦ X (m + n) ω)` (the `m`-fold path shift of
  the process, see `processShift_eq`);
* `processCons x t` / `processTail t` — prepend / drop the leading coordinate of a sequence-valued
  random variable.

The `comap` contraction lemmas (`comap_processTail_le`, `comap_le_comap_processCons`) record that
the tail of a sequence-valued random variable generates a coarser σ-algebra; they feed the
Kallenberg conditional independence step of the factorisation.

The definitions are not `@[expose]`; their characteristic API is the `@[simp]` `_apply` /
interaction lemmas below (proved through the equation lemmas), so downstream code reasons through
those rather than the definition bodies.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/ShiftOperations.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The shifted random path of a process: `ω ↦ (n ↦ X (m + n) ω)`. -/
def processShift (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω n => X (m + n) ω

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
theorem processShift_apply (X : ℕ → Ω → α) (m n : ℕ) (ω : Ω) :
    processShift X m ω n = X (m + n) ω := by
  simp only [processShift]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- `processShift X m` is the `m`-fold path-space shift `(shift α)^[m]` of the process's path. -/
theorem processShift_eq (X : ℕ → Ω → α) (m : ℕ) :
    processShift X m = fun ω => (shift α)^[m] fun n => X n ω := by
  funext ω n
  simp [processShift, shift_iterate_apply, Nat.add_comm]

/-- Cons a head random variable onto a sequence-valued one: `processCons x t = [x, t 0, t 1, …]`. -/
def processCons (x : Ω → α) (t : Ω → ℕ → α) : Ω → ℕ → α
  | ω, 0 => x ω
  | ω, (n + 1) => t ω n

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
theorem processCons_zero (x : Ω → α) (t : Ω → ℕ → α) (ω : Ω) : processCons x t ω 0 = x ω := by
  simp only [processCons]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
theorem processCons_succ (x : Ω → α) (t : Ω → ℕ → α) (ω : Ω) (n : ℕ) :
    processCons x t ω (n + 1) = t ω n := by
  simp only [processCons]

/-- Drop the leading coordinate of a sequence-valued random variable: `processTail t ω n =
t ω (n+1)`. -/
def processTail (t : Ω → ℕ → α) : Ω → ℕ → α := fun ω n => t ω (n + 1)

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
theorem processTail_apply (t : Ω → ℕ → α) (ω : Ω) (n : ℕ) : processTail t ω n = t ω (n + 1) := by
  simp only [processTail]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The tail of a cons recovers the original sequence. -/
@[simp]
theorem processTail_processCons (x : Ω → α) (t : Ω → ℕ → α) :
    processTail (processCons x t) = t := by
  funext ω n
  simp only [processTail, processCons]

/-- The shifted process is measurable when its tail coordinates `X (m + ·)` are. -/
@[fun_prop]
theorem measurable_processShift {X : ℕ → Ω → α} {m : ℕ} (hX : ∀ n, Measurable (X (m + n))) :
    Measurable (processShift X m) :=
  measurable_pi_lambda _ hX

/-- Consing a measurable head onto a measurable process is measurable. -/
@[fun_prop]
theorem measurable_processCons {x : Ω → α} {t : Ω → ℕ → α} (hx : Measurable x) (ht : Measurable t) :
    Measurable (processCons x t) := by
  refine measurable_pi_lambda _ fun n => ?_
  cases n with
  | zero => exact hx
  | succ n => exact (measurable_pi_apply n).comp ht

/-- The tail of a measurable process is measurable. -/
@[fun_prop]
theorem measurable_processTail {t : Ω → ℕ → α} (ht : Measurable t) :
    Measurable (processTail t) :=
  measurable_pi_lambda _ fun n => (measurable_pi_apply (n + 1)).comp ht

omit [MeasurableSpace Ω] in
/-- The tail of a sequence-valued random variable generates a coarser σ-algebra. It is the
composition of the measurable index shift with `t`. -/
theorem comap_processTail_le {t : Ω → ℕ → α} :
    MeasurableSpace.comap (processTail t) inferInstance
      ≤ MeasurableSpace.comap t inferInstance := by
  have hcomp : processTail t = (fun s : ℕ → α => fun n => s (n + 1)) ∘ t := by
    funext ω n; simp only [processTail, Function.comp_apply]
  rw [hcomp, ← MeasurableSpace.comap_comp]
  have hshift : Measurable fun s : ℕ → α => fun n => s (n + 1) := by fun_prop
  exact MeasurableSpace.comap_mono hshift.comap_le

omit [MeasurableSpace Ω] in
/-- Consing a head onto a sequence-valued random variable refines its σ-algebra: `σ(t) ≤
σ(processCons x t)`. -/
theorem comap_le_comap_processCons (x : Ω → α) (t : Ω → ℕ → α) :
    MeasurableSpace.comap t inferInstance ≤ MeasurableSpace.comap (processCons x t) inferInstance :=
  calc MeasurableSpace.comap t inferInstance
      = MeasurableSpace.comap (processTail (processCons x t)) inferInstance := by
        rw [processTail_processCons]
    _ ≤ MeasurableSpace.comap (processCons x t) inferInstance := comap_processTail_le

end Probability

end TauCeti
