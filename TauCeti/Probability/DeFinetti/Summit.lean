module

-- Public: the modules whose symbols appear in the exported statements.
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.ConditionallyIID
public import TauCeti.Probability.DeFinetti.DirectingMeasure
-- Non-public: used only inside proofs — the tail factorization, the block-law integration lemma,
-- and `Tuple.sort` (for the injective reduction).
import TauCeti.Probability.DeFinetti.TailFactorization
import TauCeti.Probability.DeFinetti.BlockFactorization
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
* `conditionallyIID_of_conditionallyIID_pathLaw` — path-law transfer to an arbitrary measurable
  sample space.
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

/-- For a contractable process, the conditional expectation of the length-`r` prefix indicator
product given the tail σ-algebra `tailProcess X` is a.e. the product of directing-measure
evaluations `∏ i, (directingMeasure μ X ω).real (C i)` on the coordinate sets. -/
private theorem condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {C : Fin r → Set α} (hC : ∀ i, MeasurableSet (C i)) :
    μ[blockIndicatorProd X (fun i : Fin r => (i : ℕ)) C | tailProcess X]
      =ᵐ[μ] fun ω => ∏ i : Fin r, (directingMeasure μ X ω).real (C i) := by
  have hfac := condExp_blockIndicatorProd_tailProcess_ae_eq_prod X hX hX_meas r C hC
  have key : ∀ᵐ ω ∂μ, ∀ i : Fin r,
      μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ X 0 | tailProcess X] ω
        = (directingMeasure μ X ω).real (C i) :=
    ae_all_iff.mpr fun i => (hX.directingMeasure_ae_eq_condExp_coord hX_meas 0 (hC i)).symm
  filter_upwards [hfac, key] with ω hf hk
  rw [hf]
  exact Finset.prod_congr rfl fun i _ => hk i

/-- For a contractable process, the block law of the length-`r` prefix rectangle `∏ᵢ B i` is the
`μ`-average `∫⁻ ∏ᵢ (directingMeasure μ X ω) (B i)` of the directing-measure product. -/
private theorem blockLaw_prefix_eq_lintegral_prod_directingMeasure
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X (fun i : Fin r => (i : ℕ)) (Set.univ.pi B)
      = ∫⁻ ω, ∏ i, directingMeasure μ X ω (B i) ∂μ :=
  blockLaw_eq_lintegral_prod_directingMeasure_of_condExp_ae_eq hX_meas hB
    (condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure hX hX_meas hB)

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

/-- **Transfer of conditional i.i.d.-ness along the path law.** If the coordinate process on path
space is conditionally i.i.d. under `pathLaw μ X`, then `X` is conditionally i.i.d. under `μ`. -/
theorem conditionallyIID_of_conditionallyIID_pathLaw {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] {μ : Measure Ω} {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n))
    (h : ConditionallyIID (pathLaw μ X) fun n p => p n) :
    ConditionallyIID μ X := by
  obtain ⟨ν, hν⟩ := h.exists_directing
  have hφ : Measurable (fun ω => fun i => X i ω : Ω → ℕ → α) := measurable_pi_lambda _ hX_meas
  refine ConditionallyIID.of_directing
    (ConditionallyIIDWith.intro (hν.measurable_directing.comp hφ) ?_)
  intro m k hk
  have hcoord : Measurable (fun p : ℕ → α => fun i : Fin m => p (k i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (k i)
  have hg : Measurable
      (fun p : ℕ → α => (ProbabilityMeasure.pi fun _ : Fin m => ν p).toMeasure) :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_const_toMeasure ν
      hν.measurable_directing
  calc blockLaw μ X k
      = blockLaw (pathLaw μ X) (fun n p => p n) k := by
          simp only [blockLaw_def, pathLaw_def]
          rw [Measure.map_map hcoord hφ]
          rfl
    _ = (pathLaw μ X).bind fun p => (ProbabilityMeasure.pi fun _ : Fin m => ν p).toMeasure :=
          hν.map k hk
    _ = μ.bind fun ω =>
          (ProbabilityMeasure.pi fun _ : Fin m => ν (fun i => X i ω)).toMeasure := by
          simp only [pathLaw_def, Measure.bind]
          rw [Measure.map_map hg hφ]
          rfl

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

/-- Roadmap-facing alias for `conditionallyIID_of_exchangeable`. -/
alias deFinetti := conditionallyIID_of_exchangeable

end Probability

end TauCeti
