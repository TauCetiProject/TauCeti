module

public import TauCeti.Probability.Exchangeability.Basic

/-!
# Process shift, cons, and tail operations

Process-level path operations for a process `X : ℕ → Ω → α`, used to build the de Finetti
block-product factorisation:

* `shiftRV X m` — the shifted random path `ω ↦ (n ↦ X (m + n) ω)`;
* `consRV x t` / `tailRV t` — prepend / drop the leading coordinate of a sequence-valued random
  variable.

The `comap` contraction lemmas (`comap_tailRV_le`, `comap_le_comap_consRV`) record that the tail of
a sequence-valued random variable generates a coarser σ-algebra; they feed the Kallenberg
conditional independence step of the factorisation.

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
@[expose]
def shiftRV (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω n => X (m + n) ω

/-- Cons a head random variable onto a sequence-valued one: `consRV x t` is `[x, t 0, t 1, …]`. -/
@[expose]
def consRV (x : Ω → α) (t : Ω → ℕ → α) : Ω → ℕ → α
  | ω, 0 => x ω
  | ω, (n + 1) => t ω n

/-- Drop the leading coordinate of a sequence-valued random variable: `tailRV t ω n = t ω (n+1)`. -/
@[expose]
def tailRV (t : Ω → ℕ → α) : Ω → ℕ → α := fun ω n => t ω (n + 1)

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
theorem tailRV_consRV (x : Ω → α) (t : Ω → ℕ → α) : tailRV (consRV x t) = t := rfl

@[fun_prop]
theorem measurable_shiftRV {X : ℕ → Ω → α} (hX : ∀ n, Measurable (X n)) (m : ℕ) :
    Measurable (shiftRV X m) :=
  measurable_pi_lambda _ fun n => hX (m + n)

@[fun_prop]
theorem measurable_consRV {x : Ω → α} {t : Ω → ℕ → α} (hx : Measurable x) (ht : Measurable t) :
    Measurable (consRV x t) := by
  refine measurable_pi_lambda _ fun n => ?_
  cases n with
  | zero => exact hx
  | succ n => exact (measurable_pi_apply n).comp ht

@[fun_prop]
theorem measurable_tailRV {t : Ω → ℕ → α} (ht : Measurable t) : Measurable (tailRV t) :=
  measurable_pi_lambda _ fun n => (measurable_pi_apply (n + 1)).comp ht

omit [MeasurableSpace Ω] in
/-- The tail of a sequence-valued random variable generates a coarser σ-algebra. -/
theorem comap_tailRV_le {t : Ω → ℕ → α} :
    MeasurableSpace.comap (tailRV t) inferInstance ≤ MeasurableSpace.comap t inferInstance := by
  have hshift : Measurable fun s : ℕ → α => fun n => s (n + 1) := by fun_prop
  rintro _ ⟨A, hA, rfl⟩
  exact ⟨_, hA.preimage hshift, rfl⟩

omit [MeasurableSpace Ω] in
/-- Consing a head onto a sequence-valued random variable refines its σ-algebra: `σ(t) ≤
σ(consRV x t)`. -/
theorem comap_le_comap_consRV (x : Ω → α) (t : Ω → ℕ → α) :
    MeasurableSpace.comap t inferInstance ≤ MeasurableSpace.comap (consRV x t) inferInstance :=
  calc MeasurableSpace.comap t inferInstance
      = MeasurableSpace.comap (tailRV (consRV x t)) inferInstance := by rw [tailRV_consRV]
    _ ≤ MeasurableSpace.comap (consRV x t) inferInstance := comap_tailRV_le

end Probability

end TauCeti
