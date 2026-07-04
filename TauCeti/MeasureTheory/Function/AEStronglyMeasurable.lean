module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# σ-algebra helpers for `AEStronglyMeasurable`

Helper lemmas for establishing `AEStronglyMeasurable` with respect to infima of σ-algebras and
limits of sequences, used when working with tail σ-algebras and reverse martingales.

## Main results

- `aestronglyMeasurable_iInf_of_antitone`: if a function is `AEStronglyMeasurable` with respect to
  each σ-algebra in an antitone sequence, then it is `AEStronglyMeasurable` with respect to their
  infimum.
- `aestronglyMeasurable_of_tendsto_ae'`: an a.e. pointwise limit of functions that are each
  `AEStronglyMeasurable[m]` for a σ-algebra `m` is itself `AEStronglyMeasurable[m]`.

Both results hold for a codomain in any second-countable conditionally complete linear order with
the order topology and Borel σ-algebra (`ℝ` qualifies). The witness σ-algebra `m` need not be
related to the measure's ambient σ-algebra `m₀`.

Adapted from `cameronfreer/exchangeability` (`Probability/SigmaAlgebraHelpers.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). These sub-σ-algebra statements have no Mathlib
equivalent. Written Mathlib-shaped for eventual upstreaming.
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

/-- `AEStronglyMeasurable` for a σ-algebra is preserved under a.e. pointwise limits.

If each `f n` is `AEStronglyMeasurable[m]` for a σ-algebra `m` (with no assumed relation to the
measure's ambient σ-algebra `m₀`), and `f n → g` a.e., then `g` is `AEStronglyMeasurable[m]`.
Mathlib's `aestronglyMeasurable_of_tendsto_ae` covers only the `m = m₀` case. -/
-- The witness is the pointwise `limsup` of the strongly measurable representatives of the `f n`.
lemma aestronglyMeasurable_of_tendsto_ae'
    {α : Type*} {m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}
    {m : MeasurableSpace α}
    {f : ℕ → α → β} {g : α → β}
    (hf : ∀ n, @MeasureTheory.AEStronglyMeasurable α β _ m m₀ (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    @MeasureTheory.AEStronglyMeasurable α β _ m m₀ g μ := by
  -- Step 1: Extract strongly measurable representatives for each n
  let f' : ℕ → α → β := fun n => (hf n).mk (f n)
  have hf'_sm : ∀ n, @MeasureTheory.StronglyMeasurable α β _ m (f' n) :=
    fun n => (hf n).stronglyMeasurable_mk
  have hf'_meas : ∀ n, @Measurable α β m _ (f' n) := fun n => (hf'_sm n).measurable
  have hf'_ae : ∀ n, f n =ᵐ[μ] f' n := fun n => (hf n).ae_eq_mk
  -- Step 2: Use the limsup of the representatives as the witness
  let h := fun x => Filter.atTop.limsup (fun n => f' n x)
  have h_meas : @Measurable α β m _ h := by
    haveI : MeasurableSpace α := m
    exact Measurable.limsup hf'_meas
  -- Step 3: h = g a.e.; on the set where f n = f' n for all n and f n → g, limsup (f' ·) = g
  have h_ae_eq : h =ᵐ[μ] g := by
    have h_all_eq : ∀ᵐ x ∂μ, ∀ n, f n x = f' n x := MeasureTheory.ae_all_iff.mpr hf'_ae
    filter_upwards [h_all_eq, hlim] with x hx hxlim
    have hlim' : Filter.Tendsto (fun n => f' n x) Filter.atTop (nhds (g x)) := by
      simpa only [fun n => (hx n)] using hxlim
    exact Filter.Tendsto.limsup_eq hlim'
  have h_sm : @MeasureTheory.StronglyMeasurable α β _ m h := by
    haveI : MeasurableSpace α := m
    exact h_meas.stronglyMeasurable
  exact ⟨h, h_sm, h_ae_eq.symm⟩

end MeasureTheory

end TauCeti
