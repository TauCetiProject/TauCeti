module

public import TauCeti.Probability.DeFinetti.TailFactorization
public import TauCeti.Probability.DeFinetti.BlockFactorization
-- Non-public: `Tuple.sort` (sorting an injective selection into increasing order) is used only
-- inside the injective-reduction proof, not in any exported statement.
import Mathlib.Data.Fin.Tuple.Sort

/-!
# de Finetti's theorem via the reverse-martingale route: contractable ⇒ conditionally i.i.d.

Assembles the de Finetti chain. The tail-level factorization
`condExp_blockIndicatorProd_tailProcess_ae_eq_prod` (from `TailFactorization`) discharges the
finite-block rectangle identity for the directing measure `directingProbabilityMeasure μ X`, exactly
what `conditionallyIIDWith_of_forall_rectangles` consumes.

## Main results

* `conditionallyIIDWith_of_contractable` — a contractable process on a standard Borel space is
  conditionally i.i.d. with directing measure `directingProbabilityMeasure μ X` (the tail
  conditional law).
* `conditionallyIID_of_contractable` — the existential form.
* `conditionallyIID_of_exchangeable` — the exchangeable form (via `contractable_of_exchangeable`).

Adapted from `cameronfreer/exchangeability`
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
      = ∫⁻ ω, ∏ i, directingMeasure μ X ω (B i) ∂μ := by
  classical
  have hTail : tailProcess X ≤ mΩ := tailProcess_le_ambient 0 fun j _ => hX_meas j
  haveI : IsFiniteMeasure (μ.trim hTail) := isFiniteMeasure_trim hTail
  set g : Ω → ℝ := fun ω => ∏ i, (directingMeasure μ X ω).real (B i) with hg
  have hg_meas : Measurable g :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_directingMeasure_coe hTail (hB i)).ennreal_toReal
  have hg_bound : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    have hval : g ω = ∏ i, ((directingMeasure μ X ω) (B i)).toReal := by
      simp only [hg, measureReal_def]
    rw [hval, Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
    refine Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg) fun i _ => ?_
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ)
  have hg_int : Integrable g μ :=
    (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable (ae_of_all _ hg_bound)
  have hbl : (blockLaw μ X (fun i : Fin r => (i : ℕ)) (Set.univ.pi B)).toReal = ∫ ω, g ω ∂μ := by
    rw [← integral_blockIndicatorProd (fun i => (hX_meas _).aemeasurable) hB,
      ← integral_condExp hTail]
    exact integral_congr_ae
      (condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure hX hX_meas hB)
  have hbl_ne : blockLaw μ X (fun i : Fin r => (i : ℕ)) (Set.univ.pi B) ≠ ⊤ := by
    rw [blockLaw_blockCylinder X (fun i => (hX_meas _).aemeasurable) hB]
    exact measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hbl_ne, hbl,
    ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ fun ω =>
      Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
  refine lintegral_congr fun ω => ?_
  simp only [hg, measureReal_def]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => ENNReal.toReal_nonneg]
  exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_toReal (measure_ne_top _ _)

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

/-- **de Finetti's theorem (reverse-martingale route), directed form.** A contractable process on a
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

/-- **de Finetti's theorem (reverse-martingale route): contractable ⇒ conditionally i.i.d.** A
contractable process on a standard Borel space is conditionally i.i.d. -/
theorem conditionallyIID_of_contractable
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X :=
  ConditionallyIID.of_directing (conditionallyIIDWith_of_contractable hX hX_meas)

/-- **de Finetti's theorem (reverse-martingale route): exchangeable ⇒ conditionally i.i.d.** An
exchangeable process on a standard Borel space is conditionally i.i.d. -/
theorem conditionallyIID_of_exchangeable
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Exchangeable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X :=
  conditionallyIID_of_contractable
    (contractable_of_exchangeable hX fun i => (hX_meas i).aemeasurable) hX_meas

end Probability

end TauCeti
