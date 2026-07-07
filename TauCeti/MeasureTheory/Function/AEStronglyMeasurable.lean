module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# σ-algebra helpers for `AEStronglyMeasurable`

A helper lemma for establishing `AEStronglyMeasurable` with respect to the infimum of an antitone
sequence of σ-algebras, used when working with tail σ-algebras and reverse martingales.

## Main results

- `aestronglyMeasurable_of_tendsto_ae'`: an a.e. pointwise limit of `AEStronglyMeasurable[m]`
  functions is `AEStronglyMeasurable[m]`, for a sub-σ-algebra `m` unrelated to the measure's ambient
  σ-algebra `m₀` (Mathlib's `aestronglyMeasurable_of_tendsto_ae` covers only the `m = m₀` case).
- `aestronglyMeasurable_iInf_of_antitone`: if a function is `AEStronglyMeasurable` with respect to
  each σ-algebra in an antitone sequence, then it is `AEStronglyMeasurable` with respect to their
  infimum.
- `aestronglyMeasurable_iInf_of_tendsto_ae_antitone`: an a.e. limit of a sequence adapted to an
  antitone family `𝔽` is `AEStronglyMeasurable[⨅ n, 𝔽 n]`.

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

open scoped Topology

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

/-- A.e. pointwise limit of `AEStronglyMeasurable[m]` functions is `AEStronglyMeasurable[m]`, for a
sub-σ-algebra `m` with no assumed relation to the measure's ambient σ-algebra `m₀`. Mathlib's
`aestronglyMeasurable_of_tendsto_ae` covers only the `m = m₀` case. -/
-- The witness is the pointwise `limsup` of the strongly measurable representatives of the `f n`.
-- The order-codomain assumptions are inherited from `Measurable.limsup` (`BorelSpace.Order`):
-- unlike the ambient case, Mathlib has no pseudo-metrizable a.e.-limit lemma for a sub-σ-algebra,
-- so the `limsup` witness is the only route. This lemma and the two below are consumed by the
-- reverse-martingale Lévy-downward theorem `MeasureTheory.tendsto_ae_condExp_iInf`.
lemma aestronglyMeasurable_of_tendsto_ae'
    {α : Type*} {m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}
    {m : MeasurableSpace α}
    {f : ℕ → α → β} {g : α → β}
    (hf : ∀ n, @MeasureTheory.AEStronglyMeasurable α β _ m m₀ (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    @MeasureTheory.AEStronglyMeasurable α β _ m m₀ g μ := by
  -- Strongly measurable representatives of the `f n`.
  let f' : ℕ → α → β := fun n => (hf n).mk (f n)
  have hf'_sm : ∀ n, @MeasureTheory.StronglyMeasurable α β _ m (f' n) :=
    fun n => (hf n).stronglyMeasurable_mk
  have hf'_meas : ∀ n, @Measurable α β m _ (f' n) := fun n => (hf'_sm n).measurable
  have hf'_ae : ∀ n, f n =ᵐ[μ] f' n := fun n => (hf n).ae_eq_mk
  -- Use the `limsup` of the representatives as the witness.
  let h := fun x => Filter.atTop.limsup (fun n => f' n x)
  have h_meas : @Measurable α β m _ h := by
    haveI : MeasurableSpace α := m
    exact Measurable.limsup hf'_meas
  -- `h = g` a.e.: on the set where `f n = f' n` for all `n` and `f n → g`, `limsup (f' ·) = g`.
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

/-- A.e. limit of an adapted antitone sequence is `⨅ n, 𝔽 n`-`AEStronglyMeasurable`.

For antitone `𝔽`, if each `g n` is `𝔽 n`-a.e.-strongly-measurable and `g n → Xlim` a.e., then `Xlim`
is `AEStronglyMeasurable[⨅ n, 𝔽 n]`. Codomain `β` at the same order level as the rest of this
section (`ℝ` qualifies). -/
lemma aestronglyMeasurable_iInf_of_tendsto_ae_antitone
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {𝔽 : ℕ → MeasurableSpace Ω} (h_antitone : Antitone 𝔽)
    {g : ℕ → Ω → β} {Xlim : Ω → β}
    (hg_meas : ∀ n, AEStronglyMeasurable[𝔽 n] (g n) μ)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (Xlim ω))) :
    AEStronglyMeasurable[⨅ n, 𝔽 n] Xlim μ := by
  -- Compose the two `AEStronglyMeasurable` helper lemmas: first show
  -- `AEStronglyMeasurable[𝔽 N] Xlim` for each `N` by feeding the shifted sequence `g (n + N)` into
  -- `aestronglyMeasurable_of_tendsto_ae'` (each shifted term is `𝔽 N`-`AEStronglyMeasurable` by
  -- antitonicity — take its `𝔽 (n+N)`-measurable representative, `mono` it up to `𝔽 N`); then
  -- combine over `N` via `aestronglyMeasurable_iInf_of_antitone`.
  refine aestronglyMeasurable_iInf_of_antitone (μ := μ) h_antitone Xlim (fun N => ?_)
  refine aestronglyMeasurable_of_tendsto_ae' (μ := μ) (f := fun n => g (n + N))
    (fun n => (((hg_meas (n + N)).stronglyMeasurable_mk.mono
      (h_antitone (Nat.le_add_left N n))).aestronglyMeasurable).congr
      (hg_meas (n + N)).ae_eq_mk.symm) ?_
  filter_upwards [h_tendsto] with ω hω
  exact hω.comp (Filter.tendsto_add_atTop_nat N)

end MeasureTheory

end TauCeti
