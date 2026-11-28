/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Pairing
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The quadratic transport cost and its cyclically monotone sets

On a real inner product space `E`, the quadratic transport cost `c (x, y) = ‖x - y‖ ^ 2 / 2`
differs from the pairing cost `-⟪x, y⟫` of `TauCeti.MeasureTheory.OptimalTransport.Cost.Pairing`
by the split term `‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`. Split terms are invisible to cyclical
monotonicity, so a set is `c`-cyclically monotone for the quadratic cost exactly when it is
cyclically monotone in the classical sense `∑ i, ⟪x i, y (σ i)⟫ ≤ ∑ i, ⟪x i, y i⟫`. The
`c`-transform vocabulary of the quadratic cost is the Legendre–Fenchel vocabulary of the inner
product; that dictionary is recorded in
`TauCeti.MeasureTheory.OptimalTransport.CTransform.Quadratic`. Every statement in this file
accounts for the factor `1 / 2` in the cost. The same factor connects a minimizer of the
half-squared cost to a minimizer of squared ground distance, as used by `W₂`.

## Main statements

* `TauCeti.norm_sub_sq_div_two_eq_pairingCost_add_add` — the quadratic cost is the pairing cost
  of the inner product plus the split term `‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`;
* `TauCeti.isCyclicallyMonotone_norm_sub_sq_div_two_iff` — `c`-cyclical monotonicity for the
  quadratic cost is cyclical monotonicity for the inner-product pairing, with
  `TauCeti.isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le` its classical
  sum form;
* `TauCeti.continuous_ofReal_norm_sub_sq_div_two` — the quadratic cost, as an extended
  nonnegative cost, is continuous, hence measurable;
* `TauCeti.edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two`,
  `TauCeti.isOptimalCoupling_edist_rpow_two_of_norm_sub_sq_div_two` and
  `TauCeti.isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two` — convert between the
  half-squared Brenier cost and the squared-distance cost without changing optimal couplings;
* `TauCeti.IsCoupling.lintegral_norm_sub_sq_div_two`,
  `TauCeti.IsCoupling.transportCost_norm_sub_sq_div_two_ne_top`,
  `TauCeti.transportCost_norm_sub_sq_div_two_ne_top_of_memLp`,
  `TauCeti.transportCost_norm_sub_sq_div_two_ne_top_of_ae_mem_of_isBounded`,
  `TauCeti.transportCost_norm_sub_sq_div_two_ne_top_of_withDensity_isBounded`, and
  `TauCeti.IsCoupling.integral_inner_le` — for marginals with finite second moments, the quadratic
  cost of a plan is a second-moment term minus its correlation, the optimal quadratic cost is
  finite whenever a coupling exists (in particular for equal-mass finite measures via the normalised
  product coupling, or for probability measures carried by bounded sets), and the correlation is at
  most the second-moment term; `ProbabilityTheory.HasLaw.lintegral_norm_sub_sq_div_two` is the
  identity for a pair of random variables.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.1, where the quadratic cost is reduced to the inner-product pairing.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic cost is the inner-product pairing cost plus the split term
`‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2`. -/
theorem norm_sub_sq_div_two_eq_pairingCost_add_add :
    (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) =
      fun p => pairingCost (innerₗ E) p + ‖p.1‖ ^ 2 / 2 + ‖p.2‖ ^ 2 / 2 := by
  funext p
  rw [pairingCost_apply, innerₗ_apply_apply, norm_sub_sq_real]
  ring

/-- `c`-cyclical monotonicity for the quadratic cost is cyclical monotonicity for the
inner-product pairing. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_iff {S : Set (E × E)} :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      IsCyclicallyMonotone (pairingCost (innerₗ E)) S := by
  rw [norm_sub_sq_div_two_eq_pairingCost_add_add,
    isCyclicallyMonotone_add_add_iff (pairingCost (innerₗ E)) (fun x => ‖x‖ ^ 2 / 2)
      fun y => ‖y‖ ^ 2 / 2]

/-- `c`-cyclical monotonicity for the quadratic cost is the classical cyclical monotonicity
condition: rearranging the targets of finitely many points of the set does not increase the
total inner product. -/
theorem isCyclicallyMonotone_norm_sub_sq_div_two_iff_forall_sum_inner_le {S : Set (E × E)} :
    IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      ∀ (n : ℕ) (x y : Fin n → E), (∀ i, (x i, y i) ∈ S) →
        ∀ σ : Equiv.Perm (Fin n), ∑ i, ⟪x i, y (σ i)⟫ ≤ ∑ i, ⟪x i, y i⟫ := by
  rw [isCyclicallyMonotone_norm_sub_sq_div_two_iff, isCyclicallyMonotone_pairingCost_iff]
  simp only [innerₗ_apply_apply]

end TauCeti

namespace TauCeti

variable {F : Type*} [SeminormedAddCommGroup F] [MeasurableSpace F]

omit [MeasurableSpace F] in
/-- The half-squared-displacement cost `‖x - y‖ ^ 2 / 2`, as an extended nonnegative cost, is
continuous. -/
theorem continuous_ofReal_norm_sub_sq_div_two :
    Continuous fun z : F × F => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
  ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const 2)

omit [MeasurableSpace F] in
/-- Squared distance is twice the half-squared-displacement cost. This identity accounts for
the factor `1 / 2` in the quadratic Brenier cost when reading a plan as a `W₂` plan. -/
theorem edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two (z : F × F) :
    edist z.1 z.2 ^ (2 : ℝ) =
      (2 : ℝ≥0∞) * ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) := by
  rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num), dist_eq_norm]
  rw [Real.rpow_ofNat]
  calc
    ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) =
        ENNReal.ofReal (2 * (‖z.1 - z.2‖ ^ 2 / 2)) := congrArg _ (by ring)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- A coupling optimal for the half-squared-displacement cost is optimal for squared distance.
The factor of two is positive, so it preserves the minimizing plans even when the value is
infinite. -/
theorem isOptimalCoupling_edist_rpow_two_of_norm_sub_sq_div_two
    {μ ν : Measure F} {π : Measure (F × F)}
    (hπ : IsOptimalCoupling
      (fun z ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν) :
    IsOptimalCoupling (fun z ↦ edist z.1 z.2 ^ (2 : ℝ)) π μ ν := by
  simpa only [← edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two] using
    hπ.const_mul (a := 2) ENNReal.ofNat_ne_top

/-- A coupling optimal for squared distance is optimal for the half-squared-displacement cost.
The factor of one half is positive and finite, so it preserves the minimizing plans even when the
value is infinite. -/
theorem isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two
    {μ ν : Measure F} {π : Measure (F × F)}
    (hπ : IsOptimalCoupling (fun z ↦ edist z.1 z.2 ^ (2 : ℝ)) π μ ν) :
    IsOptimalCoupling (fun z ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν := by
  simpa only [edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two,
    ENNReal.inv_mul_cancel_left two_ne_zero ENNReal.ofNat_ne_top] using
    hπ.const_mul (a := 2⁻¹) (ENNReal.inv_ne_top.2 two_ne_zero)

/-- **Coupled measures with finite second moments have finite quadratic transport cost.** -/
theorem IsCoupling.transportCost_norm_sub_sq_div_two_ne_top {μ ν : Measure F}
    {σ : Measure (F × F)} (hσ : IsCoupling σ μ ν) (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    transportCost (fun z : F × F => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
  have hnorm {g : Measure F} (hg : MemLp id 2 g) : MemLp (fun x : F => ‖x‖) 2 g :=
    hg.congr_eNorm hg.aestronglyMeasurable.norm (.of_forall fun _ => (eNorm_norm _).symm)
  have h1 := (hnorm hμ).comp_measurePreserving hσ.measurePreserving_fst
  have h2 := (hnorm hν).comp_measurePreserving hσ.measurePreserving_snd
  have hdiff : MemLp (fun z : F × F => ‖z.1 - z.2‖) 2 σ :=
    (h1.add h2).mono
      ((hμ.aestronglyMeasurable.comp_measurePreserving hσ.measurePreserving_fst).sub
        (hν.aestronglyMeasurable.comp_measurePreserving hσ.measurePreserving_snd)).norm
      (.of_forall fun z => by
        simpa [Real.norm_of_nonneg (norm_nonneg _),
          Real.norm_of_nonneg (by positivity : 0 ≤ ‖z.1‖ + ‖z.2‖)] using norm_sub_le z.1 z.2)
  have hint : Integrable (fun z : F × F => ‖z.1 - z.2‖ ^ 2 / 2) σ := by
    simpa [Real.norm_of_nonneg (norm_nonneg _)] using
      (hdiff.integrable_norm_pow two_ne_zero).div_const 2
  exact ((transportCost_le_lintegral hσ _).trans_lt
    ((lintegral_ofReal_ne_top_iff_integrable hint.aestronglyMeasurable
      (.of_forall fun _ => by positivity)).2 hint).lt_top).ne

/-- **Equal-mass finite measures with finite second moments have finite quadratic transport cost.**
-/
theorem transportCost_norm_sub_sq_div_two_ne_top_of_memLp {μ ν : Measure F} [IsFiniteMeasure μ]
    (hμν : μ Set.univ = ν Set.univ) (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    transportCost (fun z : F × F => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ :=
  (isCoupling_inv_smul_prod hμν).transportCost_norm_sub_sq_div_two_ne_top hμ hν

/-- Probability measures carried almost everywhere by bounded sets have finite transport cost for
`‖x - y‖ ^ 2 / 2`. -/
theorem transportCost_norm_sub_sq_div_two_ne_top_of_ae_mem_of_isBounded
    {μ ν : Measure F} {X Y : Set F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXb : Bornology.IsBounded X) (hYb : Bornology.IsBounded Y)
    (hμ : ∀ᵐ x ∂μ, x ∈ X) (hν : ∀ᵐ y ∂ν, y ∈ Y) :
    transportCost (fun z : F × F => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
  obtain ⟨Rx, hRx⟩ := hXb.subset_closedBall 0
  obtain ⟨Ry, hRy⟩ := hYb.subset_closedBall 0
  have hπ := isCoupling_prod μ ν
  have hbdd : ∀ᵐ z ∂(μ.prod ν),
      ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) ≤
        ENNReal.ofReal ((max Rx 0 + max Ry 0) ^ 2 / 2) := by
    filter_upwards [hπ.measurePreserving_fst.quasiMeasurePreserving.ae hμ,
      hπ.measurePreserving_snd.quasiMeasurePreserving.ae hν] with z hz₁ hz₂
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le z.1 z.2).trans <| add_le_add
        ((mem_closedBall_zero_iff.1 (hRx hz₁)).trans (le_max_left Rx 0))
        ((mem_closedBall_zero_iff.1 (hRy hz₂)).trans (le_max_left Ry 0))) 2)
      zero_le_two)
  refine ((transportCost_le_lintegral hπ _).trans_lt ?_).ne
  calc ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) ∂(μ.prod ν)
      ≤ ∫⁻ _ : F × F, ENNReal.ofReal ((max Rx 0 + max Ry 0) ^ 2 / 2) ∂(μ.prod ν) :=
        lintegral_mono_ae hbdd
    _ < ∞ := by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_lt_top

/-- Probability measures given by densities on bounded sets have finite transport cost for
`‖x - y‖ ^ 2 / 2`. Neither set need be measurable. -/
theorem transportCost_norm_sub_sq_div_two_ne_top_of_withDensity_isBounded [OpensMeasurableSpace F]
    {ρ₁ ρ₂ : Measure F} {X Y : Set F} {f g : F → ℝ≥0∞}
    (hXb : Bornology.IsBounded X) (hYb : Bornology.IsBounded Y)
    [IsProbabilityMeasure ((ρ₁.restrict X).withDensity f)]
    [IsProbabilityMeasure ((ρ₂.restrict Y).withDensity g)] :
    transportCost (fun z : F × F => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      ((ρ₁.restrict X).withDensity f) ((ρ₂.restrict Y).withDensity g) ≠ ∞ :=
  have hae (ρ : Measure F) (S : Set F) (h : F → ℝ≥0∞) :
      ∀ᵐ z ∂(ρ.restrict S).withDensity h, z ∈ closure S :=
    (withDensity_absolutelyContinuous (ρ.restrict S) h).ae_le
      (ae_restrict_of_ae_restrict_of_subset subset_closure
        (ae_restrict_mem isClosed_closure.measurableSet))
  transportCost_norm_sub_sq_div_two_ne_top_of_ae_mem_of_isBounded
    hXb.closure hYb.closure (hae ρ₁ X f) (hae ρ₂ Y g)

end TauCeti

namespace TauCeti

/-! ### Second moments and correlation -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ ν : Measure E} {σ : Measure (E × E)}

/-- Against a coupling of two measures with finite second moments, the correlation
`⟪x, y⟫` is integrable. -/
theorem IsCoupling.integrable_inner (hσ : IsCoupling σ μ ν) (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν) : Integrable (fun z : E × E => ⟪z.1, z.2⟫) σ := by
  have hμ2 : Integrable (fun x : E => ‖x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).1 hμ
  have hν2 : Integrable (fun y : E => ‖y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hν.aestronglyMeasurable).1 hν
  refine ((hσ.integrable_comp_fst hμ2).add (hσ.integrable_comp_snd hν2)).mono'
    ((hμ.aestronglyMeasurable.comp_measurePreserving hσ.measurePreserving_fst).inner
      (hν.aestronglyMeasurable.comp_measurePreserving hσ.measurePreserving_snd))
    (.of_forall fun z => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  nlinarith [abs_real_inner_le_norm z.1 z.2, sq_nonneg (‖z.1‖ - ‖z.2‖)]

/-- **The quadratic cost of a plan is a second-moment term minus the correlation.** For a
coupling `σ` of two measures with finite second moments,
`∫ ‖x - y‖ ^ 2 / 2 dσ = (∫ ‖x‖ ^ 2 dμ + ∫ ‖y‖ ^ 2 dν) / 2 - ∫ ⟪x, y⟫ dσ`, so minimising the
quadratic cost over the couplings of `μ` and `ν` is maximising the correlation. -/
theorem IsCoupling.lintegral_norm_sub_sq_div_two (hσ : IsCoupling σ μ ν) (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν) :
    ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) ∂σ =
      ENNReal.ofReal ((∫ x, ‖x‖ ^ 2 ∂μ + ∫ y, ‖y‖ ^ 2 ∂ν) / 2 - ∫ z, ⟪z.1, z.2⟫ ∂σ) := by
  have hμ2 : Integrable (fun x : E => ‖x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).1 hμ
  have hν2 : Integrable (fun y : E => ‖y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hν.aestronglyMeasurable).1 hν
  have h₁ := hσ.integrable_comp_fst hμ2
  have h₂ := hσ.integrable_comp_snd hν2
  have h₃ := hσ.integrable_inner hμ hν
  have heq : (fun z : E × E => ‖z.1 - z.2‖ ^ 2 / 2) =
      fun z => (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) / 2 - ⟪z.1, z.2⟫ := by
    rw [norm_sub_sq_div_two_eq_pairingCost_add_add]
    ext z
    rw [pairingCost_apply, innerₗ_apply_apply]
    ring
  have h₁₂ : Integrable (fun z : E × E => (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) / 2) σ :=
    (h₁.add h₂).div_const 2
  have hint : Integrable (fun z : E × E => ‖z.1 - z.2‖ ^ 2 / 2) σ := heq ▸ h₁₂.sub h₃
  rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun z => by positivity), heq,
    integral_sub h₁₂ h₃, integral_div, integral_add h₁ h₂,
    hσ.integral_comp_fst hμ2.aestronglyMeasurable, hσ.integral_comp_snd hν2.aestronglyMeasurable]

/-- **The correlation of a plan is bounded by the second moments.** For a coupling `σ` of two
measures with finite second moments, `∫ ⟪x, y⟫ dσ ≤ (∫ ‖x‖ ^ 2 dμ + ∫ ‖y‖ ^ 2 dν) / 2`. -/
theorem IsCoupling.integral_inner_le (hσ : IsCoupling σ μ ν) (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν) :
    ∫ z, ⟪z.1, z.2⟫ ∂σ ≤ (∫ x, ‖x‖ ^ 2 ∂μ + ∫ y, ‖y‖ ^ 2 ∂ν) / 2 := by
  -- Integrate `⟪x, y⟫ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2` against `σ`.
  have hμ2 : Integrable (fun x : E => ‖x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).1 hμ
  have hν2 : Integrable (fun y : E => ‖y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hν.aestronglyMeasurable).1 hν
  rw [← hσ.integral_comp_fst hμ2.aestronglyMeasurable,
    ← hσ.integral_comp_snd hν2.aestronglyMeasurable,
    ← integral_add (hσ.integrable_comp_fst hμ2) (hσ.integrable_comp_snd hν2), ← integral_div]
  refine integral_mono (hσ.integrable_inner hμ hν)
    (((hσ.integrable_comp_fst hμ2).add (hσ.integrable_comp_snd hν2)).div_const 2) fun z => ?_
  nlinarith [real_inner_le_norm z.1 z.2, sq_nonneg (‖z.1‖ - ‖z.2‖)]

/-- **The quadratic cost of a pair of random variables.** If `s` and `U` have laws `μ` and `ν`
with finite second moments, then
`∫ ‖s - U‖ ^ 2 / 2 dm = (∫ ‖x‖ ^ 2 dμ + ∫ ‖y‖ ^ 2 dν) / 2 - ∫ ⟪s, U⟫ dm`. -/
theorem _root_.ProbabilityTheory.HasLaw.lintegral_norm_sub_sq_div_two {α : Type*}
    [MeasurableSpace α] {m : Measure α} {s U : α → E} (hs : HasLaw s μ m) (hU : HasLaw U ν m)
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    ∫⁻ ω, ENNReal.ofReal (‖s ω - U ω‖ ^ 2 / 2) ∂m =
      ENNReal.ofReal ((∫ x, ‖x‖ ^ 2 ∂μ + ∫ y, ‖y‖ ^ 2 ∂ν) / 2 - ∫ ω, ⟪s ω, U ω⟫ ∂m) := by
  have hpair := hs.aemeasurable.prodMk hU.aemeasurable
  have hσ := isCoupling_map_prodMk_of_aemeasurable hs.aemeasurable hU.aemeasurable hs.map_eq
    hU.map_eq
  -- Measurability on `E × E` comes from the marginals, pulled back along the projections.
  have h₁ : AEStronglyMeasurable (fun z : E × E => z.1) (m.map fun ω => (s ω, U ω)) :=
    hμ.aestronglyMeasurable.comp_measurePreserving hσ.measurePreserving_fst
  have h₂ : AEStronglyMeasurable (fun z : E × E => z.2) (m.map fun ω => (s ω, U ω)) :=
    hν.aestronglyMeasurable.comp_measurePreserving hσ.measurePreserving_snd
  have hcost : AEMeasurable (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (m.map fun ω => (s ω, U ω)) :=
    (continuous_ofReal_norm_sub_sq_div_two.comp_aestronglyMeasurable (h₁.prodMk h₂)).aemeasurable
  refine (lintegral_map' hcost hpair).symm.trans ?_
  rw [hσ.lintegral_norm_sub_sq_div_two hμ hν, integral_map hpair (h₁.inner h₂)]

end TauCeti

end
