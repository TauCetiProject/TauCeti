module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# σ-algebra helpers for `AEStronglyMeasurable`

Helper lemmas for establishing `AEStronglyMeasurable` with respect to infima of σ-algebras and
limits of sequences, used when working with tail σ-algebras and reverse martingales.

## Main results

- `aestronglyMeasurable_iInf_antitone`: `AEStronglyMeasurable` is preserved under the infimum of an
  antitone sequence of σ-algebras.
- `aestronglyMeasurable_of_tendsto_ae_of_le`: `AEStronglyMeasurable` for a sub-σ-algebra is
  preserved under a.e. pointwise limits.

Adapted from `cameronfreer/exchangeability` (`Probability/SigmaAlgebraHelpers.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). These sub-σ-algebra statements have no Mathlib
equivalent. Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter

namespace TauCeti

namespace MeasureTheory

/-- `AEStronglyMeasurable` for the infimum of an antitone sequence of σ-algebras.

For real-valued functions, if `f` is `AEStronglyMeasurable` with respect to each σ-algebra in an
antitone (decreasing) sequence, then `f` is `AEStronglyMeasurable` with respect to their
infimum. -/
-- The common representative is built as the `liminf` of the per-σ-algebra witnesses.
lemma aestronglyMeasurable_iInf_antitone
    {α : Type*} {m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}
    {m : ℕ → MeasurableSpace α}
    (h_anti : Antitone m)
    (_h_le : ∀ N, m N ≤ m₀)
    (f : α → ℝ)
    (hf : ∀ N, @MeasureTheory.AEStronglyMeasurable α ℝ _ (m N) m₀ f μ) :
    @MeasureTheory.AEStronglyMeasurable α ℝ _ (⨅ N, m N) m₀ f μ := by
  -- Step 1: Extract strongly measurable representatives for each N
  let g : ℕ → α → ℝ := fun N => (hf N).mk f
  have hg_sm : ∀ N, @MeasureTheory.StronglyMeasurable α ℝ _ (m N) (g N) :=
    fun N => (hf N).stronglyMeasurable_mk
  have hg_meas : ∀ N, @Measurable α ℝ (m N) _ (g N) :=
    fun N => (hg_sm N).measurable
  have hg_ae : ∀ N, f =ᵐ[μ] g N := fun N => (hf N).ae_eq_mk
  -- Step 2: Define h as the liminf of the g N
  let h : α → ℝ := fun x => Filter.liminf (fun N => g N x) Filter.atTop
  -- Step 3: Show h is Measurable[⨅ N, m N], i.e. for each N, h is Measurable[m N]
  have h_meas_each : ∀ N, @Measurable α ℝ (m N) _ h := by
    intro N
    -- liminf (g n) = liminf (g (n + N)) by Filter.liminf_nat_add, and for n ≥ 0,
    -- g (n + N) is Measurable[m (n + N)] ≤ Measurable[m N] by antitonicity
    have h_shift : h = fun x => Filter.liminf (fun n => g (n + N) x) Filter.atTop := by
      funext x
      exact (Filter.liminf_nat_add (fun n => g n x) N).symm
    rw [h_shift]
    have hg_meas_shifted : ∀ n, @Measurable α ℝ (m N) _ (g (n + N)) :=
      fun n => (hg_meas (n + N)).mono (h_anti (Nat.le_add_left N n)) le_rfl
    haveI : MeasurableSpace α := m N
    exact Measurable.liminf hg_meas_shifted
  -- Conclude Measurable[⨅ N, m N] h
  have h_meas : @Measurable α ℝ (⨅ N, m N) _ h := by
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun N => h_meas_each N hs
  -- Step 4: Show f =ᵐ h; on the set where f = g N for all N we have h = f
  have h_ae_eq : f =ᵐ[μ] h := by
    have h_all_eq : ∀ᵐ x ∂μ, ∀ N, f x = g N x := MeasureTheory.ae_all_iff.mpr hg_ae
    filter_upwards [h_all_eq] with x hx
    simp [h, fun N => (hx N).symm, Filter.liminf_const]
  -- Step 5: Convert Measurable to StronglyMeasurable (for ℝ)
  have h_sm : @MeasureTheory.StronglyMeasurable α ℝ _ (⨅ N, m N) h := by
    haveI : MeasurableSpace α := ⨅ N, m N
    exact h_meas.stronglyMeasurable
  -- Step 6: Conclude AEStronglyMeasurable
  exact ⟨h, h_sm, h_ae_eq⟩

/-- `AEStronglyMeasurable` for a sub-σ-algebra is preserved under a.e. pointwise limits.

If `f n` are all `Measurable[m]` where `m ≤ m₀`, and `f n → g` a.e., then `g` is
`AEStronglyMeasurable[m]`. Mathlib's `aestronglyMeasurable_of_tendsto_ae` covers only the
`m = m₀` case. -/
-- The witness is the pointwise `limsup` of the `f n`.
lemma aestronglyMeasurable_of_tendsto_ae_of_le
    {α : Type*} {m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}
    {m : MeasurableSpace α} (_hm : m ≤ m₀)
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf_meas : ∀ n, @Measurable α ℝ m _ (f n))
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    @MeasureTheory.AEStronglyMeasurable α ℝ _ m m₀ g μ := by
  -- Use the limsup as the witness
  let h := fun x => Filter.atTop.limsup (fun n => f n x)
  have h_meas : @Measurable α ℝ m _ h := by
    haveI : MeasurableSpace α := m
    exact Measurable.limsup hf_meas
  -- h = g a.e. because on the convergence set, limsup = lim = g
  have h_ae_eq : h =ᵐ[μ] g := hlim.mono fun _ hx => Filter.Tendsto.limsup_eq hx
  have h_sm : @MeasureTheory.StronglyMeasurable α ℝ _ m h := by
    haveI : MeasurableSpace α := m
    exact h_meas.stronglyMeasurable
  exact ⟨h, h_sm, h_ae_eq.symm⟩

end MeasureTheory

end TauCeti
