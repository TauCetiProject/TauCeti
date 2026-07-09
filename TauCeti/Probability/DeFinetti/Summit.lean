module

-- Public: the modules whose symbols appear in the exported statements.
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.ConditionallyIID
public import TauCeti.Probability.DeFinetti.DirectingMeasure
-- Non-public: used only inside proofs — the prefix/iCondIndepFun block-law mixtures, the path-law
-- transfer and contractability bridges, and `Tuple.sort` (injective reduction).
import TauCeti.Probability.DeFinetti.BlockFactorization
import TauCeti.Probability.Exchangeability.ConditionallyIIDMap
import TauCeti.Probability.Exchangeability.PathSpace.LawBridge
import Mathlib.Data.Fin.Tuple.Sort

/-!
# de Finetti's theorem via the reverse-martingale route: contractable ⇒ conditionally i.i.d.

Assembles the de Finetti chain. The tail-level factorization
`condExp_blockIndicatorProd_tailProcess_ae_eq_prod` (from `TailFactorization`) discharges the
finite-block rectangle identity for the directing measure `directingProbabilityMeasure μ X`, exactly
what `conditionallyIIDWith_of_forall_rectangles` consumes.

## Main results

* `conditionallyIIDWith_of_contractable` — a contractable process on a standard Borel sample space
  is conditionally i.i.d. with directing measure `directingProbabilityMeasure μ X` (the tail
  conditional law).
* `conditionallyIID_of_contractable` — the existential form, for a contractable process on an
  arbitrary measurable sample space (state space still standard Borel).
* `conditionallyIID_of_exchangeable` — the exchangeable form (via `contractable_of_exchangeable`).

The reverse-martingale ("third") proof follows Kallenberg, *Probabilistic Symmetries and Invariance
Principles*, Theorem 1.1 (pp. 26–28). Adapted from `cameronfreer/exchangeability`
(`DeFinetti/TheoremViaMartingale.lean`: `conditionallyIID_of_contractable`, `deFinetti`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]

/-- For a contractable process and a strictly increasing selection `k`, the block law of the
rectangle `∏ᵢ B i` is the `μ`-average of the directing-measure product. -/
private theorem blockLaw_strictMono_eq_lintegral_prod_directingMeasure
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k)
    {B : Fin m → Set α} (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X k (Set.univ.pi B) = ∫⁻ ω, ∏ i, directingMeasure μ X ω (B i) ∂μ := by
  rw [hX m k hk]
  exact blockLaw_prefix_eq_lintegral_prod_directingMeasure hX hX_meas hB

/-- For a contractable process and any injective (distinct) selection `k`, the block law of the
rectangle `∏ᵢ B i` is the `μ`-average of the directing-measure product. -/
private theorem blockLaw_injective_eq_lintegral_prod_directingMeasure
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {m : ℕ} {k : Fin m → ℕ} (hk : Function.Injective k)
    {B : Fin m → Set α} (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X k (Set.univ.pi B) = ∫⁻ ω, ∏ i, directingMeasure μ X ω (B i) ∂μ := by
  classical
  set e : Equiv.Perm (Fin m) := Tuple.sort k with he
  have hsm : StrictMono (k ∘ e) :=
    (Tuple.monotone_sort k).strictMono_of_injective (hk.comp e.injective)
  have hreindex : blockLaw μ X k (Set.univ.pi B)
      = blockLaw μ X (k ∘ e) (Set.univ.pi fun i => B (e i)) := by
    rw [← map_blockLaw_reindex μ k (e : Fin m → Fin m) (fun j => (hX_meas (k j)).aemeasurable),
      Measure.map_apply (measurable_pi_lambda _ fun i => measurable_pi_apply (e i))
        (MeasurableSet.univ_pi fun i => hB (e i))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i; exact h (e i)
    · intro h j; have hj := h (e.symm j); rwa [e.apply_symm_apply] at hj
  rw [hreindex, blockLaw_strictMono_eq_lintegral_prod_directingMeasure hX hX_meas hsm
    (fun i => hB (e i))]
  refine lintegral_congr fun ω => ?_
  exact Equiv.prod_comp e fun j => directingMeasure μ X ω (B j)

/-- **de Finetti's theorem, directed form.** A contractable process on a
standard Borel space is conditionally i.i.d. **with** directing measure the tail conditional law
`directingProbabilityMeasure μ X`. -/
theorem conditionallyIIDWith_of_contractable
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIIDWith μ X (directingProbabilityMeasure μ X) := by
  have hTail : tailProcess X ≤ mΩ := tailProcess_le_ambient 0 fun j _ => hX_meas j
  refine conditionallyIIDWith_of_forall_rectangles
    (measurable_directingProbabilityMeasure (μ := μ) hTail) ?_
  intro m k hk B hB
  rw [blockLaw_injective_eq_lintegral_prod_directingMeasure hX hX_meas hk hB]
  simp only [directingProbabilityMeasure_toMeasure]

/-- The existential form on a standard Borel sample space (the internal step through which the
general `conditionallyIID_of_contractable` is transferred). -/
private theorem conditionallyIID_of_contractable_standardBorelOmega
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X :=
  ConditionallyIID.of_directing (conditionallyIIDWith_of_contractable hX hX_meas)

/-- **de Finetti's theorem: contractable ⇒ conditionally i.i.d.** A contractable process valued in
a standard Borel space, on an arbitrary measurable sample space, is conditionally i.i.d. -/
theorem conditionallyIID_of_contractable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X := by
  refine conditionallyIID_of_conditionallyIID_pathLaw hX_meas ?_
  haveI : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_def]; infer_instance
  have hcontract : Contractable (pathLaw μ X) (fun n p => p n) := by
    rw [contractable_iff_contractableLaw_pathLaw fun i => (measurable_pi_apply i).aemeasurable]
    have hpl : pathLaw (pathLaw μ X) (fun n p => p n) = pathLaw μ X := by
      rw [pathLaw_def]; exact Measure.map_id
    rw [hpl]
    exact hX.contractableLaw_pathLaw fun i => (hX_meas i).aemeasurable
  exact conditionallyIID_of_contractable_standardBorelOmega hcontract measurable_pi_apply

/-- **de Finetti's theorem: exchangeable ⇒ conditionally i.i.d.** An exchangeable process valued in
a standard Borel space, on an arbitrary measurable sample space, is conditionally i.i.d. -/
theorem conditionallyIID_of_exchangeable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Exchangeable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X :=
  conditionallyIID_of_contractable
    (contractable_of_exchangeable hX fun i => (hX_meas i).aemeasurable) hX_meas

end Probability

end TauCeti
