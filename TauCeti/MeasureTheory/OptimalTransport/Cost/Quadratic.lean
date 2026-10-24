/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Pairing
public import TauCeti.MeasureTheory.OptimalTransport.Monge
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
* `TauCeti.IsCoupling.lintegral_norm_sub_sq_div_two` and
  `TauCeti.IsCoupling.integral_inner_le` — for marginals with finite second moments, the quadratic
  cost of a plan is a second-moment term minus its correlation, and the correlation is at most
  that term; `ProbabilityTheory.HasLaw.lintegral_norm_sub_sq_div_two` is the identity for a pair
  of random variables;
* `TauCeti.integral_inner_le_of_ae_eq_comp` — if `U = T ∘ s` almost everywhere for an optimal
  quadratic transport map `T` and a map `s` of law `μ`, then `s` maximises the correlation
  `∫ ⟪s', U⟫` among maps `s'` of law `μ`.

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

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F]

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

end TauCeti

namespace TauCeti

/-! ### Second moments and correlation -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace (E × E)] {μ ν : Measure E} {σ : Measure (E × E)}

/-- Against a coupling of two measures with finite second moments, the correlation
`⟪x, y⟫` is integrable. -/
theorem IsCoupling.integrable_inner (hσ : IsCoupling σ μ ν) (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν) : Integrable (fun z : E × E => ⟪z.1, z.2⟫) σ := by
  have hμ2 : Integrable (fun x : E => ‖x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).1 hμ
  have hν2 : Integrable (fun y : E => ‖y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hν.aestronglyMeasurable).1 hν
  refine ((hσ.integrable_comp_fst hμ2).add (hσ.integrable_comp_snd hν2)).mono'
    (continuous_fst.inner continuous_snd).aestronglyMeasurable (.of_forall fun z => ?_)
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
  refine (lintegral_map' continuous_ofReal_norm_sub_sq_div_two.measurable.aemeasurable
    hpair).symm.trans ?_
  rw [(isCoupling_map_prodMk_of_aemeasurable hs.aemeasurable hU.aemeasurable hs.map_eq
      hU.map_eq).lintegral_norm_sub_sq_div_two hμ hν,
    integral_map hpair (continuous_fst.inner continuous_snd).aestronglyMeasurable]

/-- **A factor through an optimal map maximises the correlation.** On a real inner product space,
let `μ` and the law of `U : α → E` have finite second moments, and let `T` be an optimal transport
map for the cost `‖x - y‖ ^ 2 / 2` from `μ` to the law of `U`. If `s` has law `μ` and `U = T ∘ s`
almost everywhere, then among all maps `s'` of law `μ`, `s` maximises the correlation
`∫ ⟪s', U⟫ dm`. -/
theorem integral_inner_le_of_ae_eq_comp {α : Type*} [MeasurableSpace α] {m : Measure α}
    {T : E → E} {U s s' : α → E} (hμ : MemLp id 2 μ) (hν : MemLp id 2 (m.map U))
    (hT : IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      μ (m.map U) T)
    (hs : HasLaw s μ m) (h : U =ᵐ[m] T ∘ s) (hs' : HasLaw s' μ m) :
    ∫ ω, ⟪s' ω, U ω⟫ ∂m ≤ ∫ ω, ⟪s ω, U ω⟫ ∂m := by
  have hUm : AEMeasurable U m := hs.aemeasurable_of_ae_eq_comp hT.aemeasurable h
  have hle :=
    lintegral_le_of_ae_eq_comp continuous_ofReal_norm_sub_sq_div_two.measurable hT hs h hs'
  beta_reduce at hle
  have hle' : ∫ ω, ⟪s' ω, U ω⟫ ∂m ≤ (∫ x, ‖x‖ ^ 2 ∂μ + ∫ y, ‖y‖ ^ 2 ∂m.map U) / 2 :=
    (integral_map (hs'.aemeasurable.prodMk hUm)
      (continuous_fst.inner continuous_snd).aestronglyMeasurable).symm.trans_le
      ((isCoupling_map_prodMk_of_aemeasurable hs'.aemeasurable hUm hs'.map_eq rfl).integral_inner_le
        hμ hν)
  rw [hs.lintegral_norm_sub_sq_div_two (hasLaw_map hUm) hμ hν,
    hs'.lintegral_norm_sub_sq_div_two (hasLaw_map hUm) hμ hν,
    ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 hle')] at hle
  linarith

end TauCeti

end

end
