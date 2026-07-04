module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# σ-algebra helpers for `AEStronglyMeasurable`

A helper lemma for establishing `AEStronglyMeasurable` with respect to the infimum of an antitone
sequence of σ-algebras, used when working with tail σ-algebras and reverse martingales.

## Main results

- `aestronglyMeasurable_iInf_of_antitone`: if a function is `AEStronglyMeasurable` with respect to
  each σ-algebra in an antitone sequence, then it is `AEStronglyMeasurable` with respect to their
  infimum.

The result holds for a codomain in any second-countable conditionally complete linear order with the
order topology and Borel σ-algebra (`ℝ` qualifies). The witness σ-algebras `m N` need not be related
to the measure's ambient σ-algebra `m₀`.

Adapted from `cameronfreer/exchangeability` (`Probability/SigmaAlgebraHelpers.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). This sub-σ-algebra statement has no Mathlib equivalent.
Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter

namespace TauCeti

namespace MeasureTheory

variable {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
  [SecondCountableTopology β] [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β]
  [BorelSpace β]

/-- `AEStronglyMeasurable` for the infimum of an antitone sequence of σ-algebras.

If `f` is `AEStronglyMeasurable` with respect to each σ-algebra in an antitone (decreasing)
sequence, then `f` is `AEStronglyMeasurable` with respect to their infimum. -/
-- The common representative is built as the `liminf` of the per-σ-algebra witnesses.
lemma aestronglyMeasurable_iInf_of_antitone
    {α : Type*} {m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}
    {m : ℕ → MeasurableSpace α}
    (h_anti : Antitone m)
    (f : α → β)
    (hf : ∀ N, @MeasureTheory.AEStronglyMeasurable α β _ (m N) m₀ f μ) :
    @MeasureTheory.AEStronglyMeasurable α β _ (⨅ N, m N) m₀ f μ := by
  -- Step 1: Extract strongly measurable representatives for each N
  let g : ℕ → α → β := fun N => (hf N).mk f
  have hg_sm : ∀ N, @MeasureTheory.StronglyMeasurable α β _ (m N) (g N) :=
    fun N => (hf N).stronglyMeasurable_mk
  have hg_meas : ∀ N, @Measurable α β (m N) _ (g N) :=
    fun N => (hg_sm N).measurable
  have hg_ae : ∀ N, f =ᵐ[μ] g N := fun N => (hf N).ae_eq_mk
  -- Step 2: Define h as the liminf of the g N
  let h : α → β := fun x => Filter.liminf (fun N => g N x) Filter.atTop
  -- Step 3: Show h is Measurable[⨅ N, m N], i.e. for each N, h is Measurable[m N]
  have h_meas_each : ∀ N, @Measurable α β (m N) _ h := by
    intro N
    -- liminf (g n) = liminf (g (n + N)) by Filter.liminf_nat_add, and for n ≥ 0,
    -- g (n + N) is Measurable[m (n + N)] ≤ Measurable[m N] by antitonicity
    have h_shift : h = fun x => Filter.liminf (fun n => g (n + N) x) Filter.atTop := by
      funext x
      exact (Filter.liminf_nat_add (fun n => g n x) N).symm
    rw [h_shift]
    have hg_meas_shifted : ∀ n, @Measurable α β (m N) _ (g (n + N)) :=
      fun n => (hg_meas (n + N)).mono (h_anti (Nat.le_add_left N n)) le_rfl
    haveI : MeasurableSpace α := m N
    exact Measurable.liminf hg_meas_shifted
  -- Conclude Measurable[⨅ N, m N] h
  have h_meas : @Measurable α β (⨅ N, m N) _ h := by
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun N => h_meas_each N hs
  -- Step 4: Show f =ᵐ h; on the set where f = g N for all N we have h = f
  have h_ae_eq : f =ᵐ[μ] h := by
    have h_all_eq : ∀ᵐ x ∂μ, ∀ N, f x = g N x := MeasureTheory.ae_all_iff.mpr hg_ae
    filter_upwards [h_all_eq] with x hx
    simp [h, fun N => (hx N).symm, Filter.liminf_const]
  -- Step 5: Convert Measurable to StronglyMeasurable
  have h_sm : @MeasureTheory.StronglyMeasurable α β _ (⨅ N, m N) h := by
    haveI : MeasurableSpace α := ⨅ N, m N
    exact h_meas.stronglyMeasurable
  -- Step 6: Conclude AEStronglyMeasurable
  exact ⟨h, h_sm, h_ae_eq⟩

end MeasureTheory

end TauCeti
