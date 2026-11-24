/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Probability.LargeDeviations.Basic
import TauCeti.Analysis.SpecialFunctions.Log.ENNRealLog.Basic
import TauCeti.Data.EReal.Operations
import TauCeti.Analysis.SpecialFunctions.Log.ENNRealLog.LargestTerm
import TauCeti.Probability.LargeDeviations.RateFunction

/-!
# Exponentially equivalent families

Two families of random variables `Z i` and `Z' i` on measure spaces `(Ω i, P i)`, with values in
a pseudo-emetric space, are *exponentially equivalent* at inverse speed `ε` if the probability
that they are more than `δ` apart decays faster than every exponential:
`limsup ε i * log (P i {ENNReal.ofReal δ < edist (Z i) (Z' i)}) = ⊥` for each real `δ > 0`.
The relation is symmetric, reflexive at an eventually positive inverse speed and transitive at an
eventually bounded inverse speed; so it is an equivalence relation at an eventually positive and
eventually bounded inverse speed. Exponential equivalence itself forces an eventually positive
inverse speed. At an inverse speed tending to `0`, exponentially equivalent
families satisfy the same large deviation principles with good rate functions: the lower bound on
open sets transfers without goodness, and the upper bound on closed sets transfers for a good rate
function. This allows a principle to be transferred to truncated, rounded or slightly perturbed
random variables.

## Main definitions

* `TauCeti.Probability.ExponentiallyEquivalent l ε P Z Z'`: exponential equivalence of the
  families `Z` and `Z'`.

## Main results

* `TauCeti.Probability.ExponentiallyEquivalent.refl`,
  `TauCeti.Probability.ExponentiallyEquivalent.symm` and
  `TauCeti.Probability.ExponentiallyEquivalent.trans`: exponential equivalence is reflexive at an
  eventually positive inverse speed, symmetric, and transitive at an eventually bounded inverse
  speed.
* `TauCeti.Probability.ExponentiallyEquivalent.eventually_pos`: the inverse speed of an exponential
  equivalence is eventually positive.
* `TauCeti.Probability.ExponentiallyEquivalent.congr`: exponential equivalence passes to almost
  surely equal versions of the random variables.
* `TauCeti.Probability.ExponentiallyEquivalent.le_liminf_coe_mul_log_map_of_isOpen`: at an inverse
  speed tending to `0`, the large deviation lower bound on open sets passes to exponentially
  equivalent families, for any rate function.
* `TauCeti.Probability.ExponentiallyEquivalent.limsup_coe_mul_log_map_le_of_isClosed`: at an inverse
  speed tending to `0`, the large deviation upper bound on closed sets passes to exponentially
  equivalent families, for a good rate function.
* `TauCeti.Probability.HasLDP.of_exponentiallyEquivalent`: at an inverse speed tending to `0`, a
  large deviation principle with a good rate function passes to exponentially equivalent families.

## References

* A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), Definition 4.2.10 and Theorem 4.2.13.
-/

public section

open Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X : Type*} [PseudoEMetricSpace X] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- The families `Z i` and `Z' i` of random variables on `(Ω i, P i)` are *exponentially
equivalent* at inverse speed `ε` along `l`: for every `δ > 0`, the probability that `Z i` and `Z' i`
are more than `δ` apart has limsup rate `⊥`. This relation is symmetric; it is reflexive at an
eventually positive inverse speed and transitive at an eventually bounded inverse speed, see
`ExponentiallyEquivalent.refl` and `ExponentiallyEquivalent.trans`. -/
def ExponentiallyEquivalent (l : Filter ι) (ε : ι → ℝ≥0) (P : ∀ i, Measure (Ω i))
    (Z Z' : ∀ i, Ω i → X) : Prop :=
  ∀ δ : ℝ, 0 < δ → limsup (fun i => ((ε i : ℝ) : EReal) *
    ENNReal.log (P i {ω | ENNReal.ofReal δ < edist (Z i ω) (Z' i ω)})) l = ⊥

variable {l : Filter ι} {ε : ι → ℝ≥0} {P : ∀ i, Measure (Ω i)} {Z Z' : ∀ i, Ω i → X}

/-- Unfolding of `ExponentiallyEquivalent`. -/
theorem exponentiallyEquivalent_iff : ExponentiallyEquivalent l ε P Z Z' ↔
    ∀ δ : ℝ, 0 < δ → limsup (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (P i {ω | ENNReal.ofReal δ < edist (Z i ω) (Z' i ω)})) l = ⊥ :=
  Iff.rfl

/-- Exponential equivalence is symmetric. -/
theorem ExponentiallyEquivalent.symm (h : ExponentiallyEquivalent l ε P Z Z') :
    ExponentiallyEquivalent l ε P Z' Z := by
  intro δ hδ
  simpa only [edist_comm] using h δ hδ

/-- Exponential equivalence forces the inverse speed to be eventually positive: at a zero inverse
speed the probability that the two families are apart would have rate `0` instead of `⊥`. -/
theorem ExponentiallyEquivalent.eventually_pos (h : ExponentiallyEquivalent l ε P Z Z') :
    ∀ᶠ i in l, 0 < ε i :=
  ENNReal.eventually_pos_of_limsup_coe_mul_log_lt_zero ((h 1 one_pos).trans_lt EReal.bot_lt_zero)

/-- Exponential equivalence depends on the random variables only almost surely and eventually
along `l`: it passes to families `W` and `W'` with `Z i = W i` and `Z' i = W' i` almost everywhere
for eventually all `i`. -/
theorem ExponentiallyEquivalent.congr {W W' : ∀ i, Ω i → X}
    (h : ExponentiallyEquivalent l ε P Z Z') (hW : ∀ᶠ i in l, Z i =ᵐ[P i] W i)
    (hW' : ∀ᶠ i in l, Z' i =ᵐ[P i] W' i) : ExponentiallyEquivalent l ε P W W' := by
  intro δ hδ
  refine (limsup_congr ?_).trans (h δ hδ)
  filter_upwards [hW, hW'] with i hi hi'
  -- The two exceptional events agree almost everywhere.
  have hset : {ω | ENNReal.ofReal δ < edist (W i ω) (W' i ω)} =ᵐ[P i]
      {ω | ENNReal.ofReal δ < edist (Z i ω) (Z' i ω)} :=
    ((hi.and hi').mono fun ω hω => by simp only [Set.mem_ofPred_eq, hω.1, hω.2]).set_eq
  rw [measure_congr hset]

/-- Exponential equivalence is transitive at an eventually bounded inverse speed. -/
theorem ExponentiallyEquivalent.trans {Z'' : ∀ i, Ω i → X} (h : ExponentiallyEquivalent l ε P Z Z')
    (h' : ExponentiallyEquivalent l ε P Z' Z'') (hε : IsBoundedUnder (· ≤ ·) l ε) :
    ExponentiallyEquivalent l ε P Z Z'' := by
  intro δ hδ
  -- If `Z i` and `Z'' i` are more than `δ` apart, one of the two pairs is more than `δ / 2` apart.
  have hsub (i : ι) : P i {ω | ENNReal.ofReal δ < edist (Z i ω) (Z'' i ω)} ≤
      P i {ω | ENNReal.ofReal (δ / 2) < edist (Z i ω) (Z' i ω)} +
        P i {ω | ENNReal.ofReal (δ / 2) < edist (Z' i ω) (Z'' i ω)} := by
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
    by_contra! hd
    refine hω.not_ge ((edist_triangle _ (Z' i ω) _).trans ((add_le_add hd.1 hd.2).trans_eq ?_))
    rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le, add_halves]
  exact le_bot_iff.1 ((ENNReal.limsup_coe_mul_log_mono (.of_forall hsub)).trans_eq
    (ENNReal.limsup_coe_mul_log_add_eq_bot hε (h _ (half_pos hδ)) (h' _ (half_pos hδ))))

/-- Random variables that, eventually along `l`, are almost surely within every positive
distance of each other are exponentially equivalent at an eventually positive inverse speed. -/
theorem ExponentiallyEquivalent.of_eventually_ae_edist_le
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, ∀ᵐ ω ∂(P i), edist (Z i ω) (Z' i ω) ≤ ENNReal.ofReal δ)
    (hpos : ∀ᶠ i in l, 0 < ε i) :
    ExponentiallyEquivalent l ε P Z Z' := by
  intro δ hδ
  refine (limsup_congr ?_).trans limsup_const_bot
  filter_upwards [hpos, h δ hδ] with i hi hδi
  have hnull : P i {ω | ENNReal.ofReal δ < edist (Z i ω) (Z' i ω)} = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hδi.mono fun ω hω => Set.notMem_ofPred_iff.2 hω.not_gt)
  simpa [hnull] using EReal.mul_bot_of_pos (by exact_mod_cast hi)

/-- Exponential equivalence is reflexive at an eventually positive inverse speed. -/
protected theorem ExponentiallyEquivalent.refl (Z : ∀ i, Ω i → X) (hpos : ∀ᶠ i in l, 0 < ε i) :
    ExponentiallyEquivalent l ε P Z Z :=
  .of_eventually_ae_edist_le
    (fun _ _ => .of_forall fun i => ae_of_all _ fun ω => (edist_self (Z i ω)).trans_le zero_le)
    hpos

variable [MeasurableSpace X] [OpensMeasurableSpace X] {I : X → ℝ≥0∞}

/-- The lower bound for an exponentially equivalent family at a point of an open set. -/
private theorem ExponentiallyEquivalent.neg_le_liminf_coe_mul_log_map
    (he : ExponentiallyEquivalent l ε P Z Z')
    (hZ : ∀ᶠ i in l, AEMeasurable (Z i) (P i))
    (hZ' : ∀ᶠ i in l, AEMeasurable (Z' i) (P i))
    (hε : Tendsto ε l (𝓝 0))
    (hlower : ∀ G : Set X, IsOpen G → -((⨅ x ∈ G, I x : ℝ≥0∞) : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z i) G)) l)
    {G : Set X} (hG : IsOpen G) {x : X} (hx : x ∈ G) :
    -(I x : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) G)) l := by
  obtain ⟨r, hr, hball⟩ := EMetric.isOpen_iff.1 hG x hx
  -- A real radius `ρ` with `ρ < r / 2`.
  obtain ⟨ρ, -, hρ0, hρr⟩ := ENNReal.lt_iff_exists_real_btwn.1 (ENNReal.half_pos hr.ne')
  have hρ : 0 < ρ := ENNReal.ofReal_pos.1 hρ0
  -- A ball of radius `ρ` around `x` is caught by `G` up to an exponentially small error.
  have hsub : ∀ᶠ i in l, (P i).map (Z i) (eball x (ENNReal.ofReal ρ)) ≤
      (P i).map (Z' i) G + P i {ω | ENNReal.ofReal ρ < edist (Z i ω) (Z' i ω)} := by
    filter_upwards [hZ, hZ'] with i hZi hZ'i
    rw [Measure.map_apply_of_aemeasurable hZi isOpen_eball.measurableSet,
      Measure.map_apply_of_aemeasurable hZ'i hG.measurableSet]
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, mem_eball] at hω ⊢
    by_cases hd : ENNReal.ofReal ρ < edist (Z i ω) (Z' i ω)
    · exact Or.inr hd
    · refine Or.inl (hball ?_)
      rw [not_lt] at hd
      calc edist (Z' i ω) x ≤ edist (Z i ω) (Z' i ω) + edist (Z i ω) x := edist_triangle_left _ _ _
        _ < ENNReal.ofReal ρ + ENNReal.ofReal ρ :=
          ENNReal.add_lt_add_of_le_of_lt (hd.trans_lt ENNReal.ofReal_lt_top).ne hd hω
        _ ≤ r / 2 + r / 2 := add_le_add hρr.le hρr.le
        _ = r := ENNReal.add_halves r
  calc -(I x : EReal) ≤ -((⨅ y ∈ eball x (ENNReal.ofReal ρ), I y : ℝ≥0∞) : EReal) :=
        EReal.neg_le_neg_iff.2 <| EReal.coe_ennreal_le_coe_ennreal_iff.2 <|
          biInf_le _ (mem_eball_self hρ0)
    _ ≤ liminf (fun i => ((ε i : ℝ) : EReal) *
          ENNReal.log ((P i).map (Z i) (eball x (ENNReal.ofReal ρ)))) l := hlower _ isOpen_eball
    _ ≤ liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) G +
          P i {ω | ENNReal.ofReal ρ < edist (Z i ω) (Z' i ω)})) l :=
        ENNReal.liminf_coe_mul_log_mono hsub
    _ ≤ _ := by
      have := ENNReal.liminf_coe_mul_log_add_le (fun i => (P i).map (Z' i) G)
        (fun i => P i {ω | ENNReal.ofReal ρ < edist (Z i ω) (Z' i ω)}) hε
      rwa [he _ hρ, max_bot_right] at this

/-- **Transfer of the lower bound.** At an inverse speed tending to `0`, the large deviation lower
bound on open sets passes from the laws of `Z i` to the laws of every exponentially equivalent
family `Z' i`, with the same function `I`. No goodness or semicontinuity of `I` is needed. -/
theorem ExponentiallyEquivalent.le_liminf_coe_mul_log_map_of_isOpen
    (he : ExponentiallyEquivalent l ε P Z Z')
    (hZ : ∀ᶠ i in l, AEMeasurable (Z i) (P i))
    (hZ' : ∀ᶠ i in l, AEMeasurable (Z' i) (P i))
    (hε : Tendsto ε l (𝓝 0))
    (hlower : ∀ G : Set X, IsOpen G → -((⨅ x ∈ G, I x : ℝ≥0∞) : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z i) G)) l)
    {G : Set X} (hG : IsOpen G) :
    -((⨅ x ∈ G, I x : ℝ≥0∞) : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) G)) l :=
  TauCeti.EReal.neg_coe_ennreal_biInf_le_iff.2 fun _ hx =>
    he.neg_le_liminf_coe_mul_log_map hZ hZ' hε hlower hG hx

/-- **Transfer of the upper bound.** At an inverse speed tending to `0`, the large deviation upper
bound on closed sets passes from the laws of `Z i` to the laws of every exponentially equivalent
family `Z' i`, with the same good rate function `I`. -/
theorem ExponentiallyEquivalent.limsup_coe_mul_log_map_le_of_isClosed
    (he : ExponentiallyEquivalent l ε P Z Z') (hZ : ∀ᶠ i in l, AEMeasurable (Z i) (P i))
    (hZ' : ∀ᶠ i in l, AEMeasurable (Z' i) (P i)) (hε : Tendsto ε l (𝓝 0))
    (hI : IsGoodRateFunction I)
    (hupper : ∀ F : Set X, IsClosed F →
      limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z i) F)) l ≤
        -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal))
    {F : Set X} (hF : IsClosed F) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) F)) l ≤
      -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal) := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨δ, hδ, hδc⟩ := hI.exists_neg_coe_biInf_cthickening_lt hF hc
  -- Up to an exponentially small error, `F` is caught by the thickening `cthickening δ F`.
  have hsub : ∀ᶠ i in l, (P i).map (Z' i) F ≤
      (P i).map (Z i) (cthickening δ F) + P i {ω | ENNReal.ofReal δ < edist (Z i ω) (Z' i ω)} := by
    filter_upwards [hZ, hZ'] with i hZi hZ'i
    rw [Measure.map_apply_of_aemeasurable hZ'i hF.measurableSet,
      Measure.map_apply_of_aemeasurable hZi isClosed_cthickening.measurableSet]
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
    by_cases hd : ENNReal.ofReal δ < edist (Z i ω) (Z' i ω)
    · exact Or.inr hd
    · exact Or.inl (mem_cthickening_of_edist_le _ _ δ F hω (not_lt.1 hd))
  calc limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) F)) l
      ≤ limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z i) (cthickening δ F) +
          P i {ω | ENNReal.ofReal δ < edist (Z i ω) (Z' i ω)})) l :=
        ENNReal.limsup_coe_mul_log_mono hsub
    _ ≤ limsup (fun i => ((ε i : ℝ) : EReal) *
          ENNReal.log ((P i).map (Z i) (cthickening δ F))) l := by
      rw [ENNReal.limsup_coe_mul_log_add _ _ hε, he δ hδ, max_bot_right]
    _ ≤ -((⨅ x ∈ cthickening δ F, I x : ℝ≥0∞) : EReal) := hupper _ isClosed_cthickening
    _ < c := hδc

/-- **Exponential equivalence.** If the laws of `Z i` satisfy a large deviation principle with a
good rate function at an inverse speed tending to `0`, then so do the laws of every exponentially
equivalent family `Z' i`, with the same rate function. -/
theorem HasLDP.of_exponentiallyEquivalent (h : HasLDP l ε (fun i => (P i).map (Z i)) I)
    (hI : IsGoodRateFunction I) (hZ : ∀ᶠ i in l, AEMeasurable (Z i) (P i))
    (hZ' : ∀ᶠ i in l, AEMeasurable (Z' i) (P i)) (he : ExponentiallyEquivalent l ε P Z Z')
    (hε : Tendsto ε l (𝓝 0)) :
    HasLDP l ε (fun i => (P i).map (Z' i)) I :=
  ⟨h.lowerSemicontinuous,
    fun _ hG => he.le_liminf_coe_mul_log_map_of_isOpen hZ hZ' hε h.lower_bound hG,
    fun _ hF => he.limsup_coe_mul_log_map_le_of_isClosed hZ hZ' hε hI h.upper_bound hF⟩

end TauCeti.Probability
