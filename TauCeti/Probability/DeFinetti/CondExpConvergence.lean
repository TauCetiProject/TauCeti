module

public import TauCeti.MeasureTheory.Function.ConditionalExpectation
public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Process.Tail

/-!
# Conditional law of a contractable coordinate given the tail

For a contractable process `X`, the conditional law of a coordinate `X m` given the future is the
same as that of a lower coordinate `X k`. Two results, both consumed by the de Finetti
directing-measure construction:

* `Contractable.condExp_indicator_future_eq` — for `k ≤ m`, the conditional expectations of
  `𝟙_B ∘ X m` and `𝟙_B ∘ X k` given the future σ-algebra `tailFamily X (m + 1)` agree a.e.
* `Contractable.condExp_indicator_tailProcess_eq` — the same equality conditioning on the process
  tail σ-algebra `tailProcess X`. The "extreme members agree on the tail" step.

Notably the tail-level result avoids the reverse-martingale (Lévy downward) machinery the
reference's Kallenberg route uses: the conditional-expectation tower over
`tailProcess X ≤ tailFamily X (m + 1)` reaches the same conclusion directly.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/CondExpConvergence.lean`,
`condexp_convergence` and `extreme_members_equal_on_tail_via_tower`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Conditional law of a future coordinate.** For a contractable process and `k ≤ m`, the
conditional expectations of `𝟙_B ∘ X m` and `𝟙_B ∘ X k` given the future σ-algebra
`tailFamily X (m + 1)` agree almost everywhere. -/
theorem Contractable.condExp_indicator_future_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {k m : ℕ} (hk : k ≤ m)
    {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X m | tailFamily X (m + 1)]
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X k | tailFamily X (m + 1)] := by
  rw [tailFamily_eq_comap_shift X (m + 1)]
  exact TauCeti.MeasureTheory.condExp_indicator_eq_of_pair_law_eq (X m) (X k)
    (fun ω n => X (m + 1 + n) ω) (hX_meas m) (hX_meas k)
    (measurable_pi_lambda _ fun n => hX_meas (m + 1 + n))
    (hX.pairLaw_eq (j := m) (k := k) (g := fun n => m + 1 + n)
      (fun n => (hX_meas n).aemeasurable) (fun a b hab => by dsimp only; omega)
      (by omega) (by omega)) hB

/-- **Extreme members agree on the tail.** For a contractable process and `k ≤ m`, the conditional
expectations of `𝟙_B ∘ X m` and `𝟙_B ∘ X k` given the process tail σ-algebra `tailProcess X` agree
almost everywhere. -/
theorem Contractable.condExp_indicator_tailProcess_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {k m : ℕ} (hk : k ≤ m)
    {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X m | tailProcess X]
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X k | tailProcess X] := by
  have htail_le : tailProcess X ≤ tailFamily X (m + 1) := tailProcess_le_tailFamily X (m + 1)
  have hfam_le : tailFamily X (m + 1) ≤ (inferInstance : MeasurableSpace Ω) :=
    tailFamily_le_ambient (m + 1) fun k _ => hX_meas k
  haveI : IsFiniteMeasure (μ.trim hfam_le) := isFiniteMeasure_trim hfam_le
  have hfut := hX.condExp_indicator_future_eq hX_meas hk hB
  have htower : ∀ g : Ω → ℝ,
      μ[μ[g | tailFamily X (m + 1)] | tailProcess X] =ᵐ[μ] μ[g | tailProcess X] :=
    fun g => condExp_condExp_of_le htail_le hfam_le
  exact (htower _).symm.trans ((condExp_congr_ae hfut).trans (htower _))

end Probability

end TauCeti
