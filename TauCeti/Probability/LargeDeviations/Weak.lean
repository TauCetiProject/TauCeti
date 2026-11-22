/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.LargeDeviations.Basic
import Mathlib.Data.EReal.Inv
import TauCeti.Data.EReal.Operations
import TauCeti.Probability.LargeDeviations.LargestTerm

/-!
# Weak large deviation principles and exponential tightness

A *weak* large deviation principle asks for the upper bound only on compact sets. A family of
measures is *exponentially tight* if, for every level `L`, a single compact set carries all but
an `exp (-L / ε)` fraction of the mass. The two notions combine to the full principle: an
exponentially tight family satisfying a weak principle satisfies the full one, and the rate
function is then good.

Weak principles are usually obtained from local estimates. If the measures of small
neighbourhoods of each point `x` decay at the rate `I x`, from above and from below, then the
weak principle holds with rate `I`. Together with exponential tightness, this is how the
large deviation principles for empirical spectral measures and extreme eigenvalues of Gaussian
ensembles are proved.

## Main definitions

* `TauCeti.Probability.HasWeakLDP l ε μ I`: the open-set lower bound and the compact-set upper
  bound.
* `TauCeti.Probability.IsExponentiallyTight l ε μ`: for every real `L` there is a compact `K` with
  `limsup ε i * log (μ i Kᶜ) ≤ -L`.

## Main results

* `TauCeti.Probability.HasLDP.hasWeakLDP`: a large deviation principle is a weak one.
* `TauCeti.Probability.IsExponentiallyTight.limsup_le_of_isClosed`: under exponential tightness
  the compact-set upper bound extends to closed sets.
* `TauCeti.Probability.IsExponentiallyTight.isGoodRateFunction`: under exponential tightness the
  open-set lower bound forces the rate function to be good.
* `TauCeti.Probability.HasWeakLDP.hasLDP`: an exponentially tight family satisfying a weak
  principle satisfies the full principle.
* `TauCeti.Probability.hasWeakLDP_of_forall_nhds`: local estimates at every point give the weak
  principle.

## References

* A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), §1.2 (Lemma 1.2.18) and Theorem 4.1.11.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Appendix D.
-/

public section

open Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The family `μ i`, `i` along the filter `l`, satisfies a *weak* large deviation principle with
speed `ε` and rate function `I`. The rate function is lower semicontinuous, and the bounds are
`-inf_G I ≤ liminf ε i * log (μ i G)` for open `G` and
`limsup ε i * log (μ i K) ≤ -inf_K I` for compact `K`. -/
structure HasWeakLDP (l : Filter ι) (ε : ι → ℝ≥0) (μ : ι → Measure X) (I : X → ℝ≥0∞) :
    Prop where
  lowerSemicontinuous : LowerSemicontinuous I
  lower_bound : ∀ G : Set X, IsOpen G →
    -((⨅ x ∈ G, I x : ℝ≥0∞) : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i G)) l
  upper_bound : ∀ K : Set X, IsCompact K →
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i K)) l ≤
      -((⨅ x ∈ K, I x : ℝ≥0∞) : EReal)

/-- The family `μ i` is *exponentially tight* at speed `ε`: for every real `L` there is a compact
set `K` with `limsup ε i * log (μ i Kᶜ) ≤ -L`. -/
def IsExponentiallyTight (l : Filter ι) (ε : ι → ℝ≥0) (μ : ι → Measure X) : Prop :=
  ∀ L : ℝ, ∃ K : Set X, IsCompact K ∧
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i Kᶜ)) l ≤ -(L : EReal)

variable {l : Filter ι} {ε : ι → ℝ≥0} {μ : ι → Measure X} {I : X → ℝ≥0∞}

/-- Unfolding of `IsExponentiallyTight`. -/
theorem isExponentiallyTight_iff : IsExponentiallyTight l ε μ ↔ ∀ L : ℝ, ∃ K : Set X,
    IsCompact K ∧ limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i Kᶜ)) l ≤ -(L : EReal) :=
  Iff.rfl

/-- In a Hausdorff space a large deviation principle is a weak one. -/
theorem HasLDP.hasWeakLDP [T2Space X] (h : HasLDP l ε μ I) : HasWeakLDP l ε μ I :=
  ⟨h.lowerSemicontinuous, h.lower_bound, fun K hK => h.upper_bound K hK.isClosed⟩

namespace IsExponentiallyTight

/-- Under exponential tightness at a speed tending to `0`, the large deviation upper bound on
compact sets extends to closed sets. -/
theorem limsup_le_of_isClosed (ht : IsExponentiallyTight l ε μ) (hε : Tendsto ε l (𝓝 0))
    (hK : ∀ K : Set X, IsCompact K →
      limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i K)) l ≤
        -((⨅ x ∈ K, I x : ℝ≥0∞) : EReal))
    {F : Set X} (hF : IsClosed F) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i F)) l ≤
      -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal) := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨L, hL⟩ : ∃ L : ℝ, -(L : EReal) < c := by
    obtain ⟨y, -, hy⟩ := EReal.exists_between_coe_real (bot_le.trans_lt hc)
    exact ⟨-y, by simpa using hy⟩
  obtain ⟨K, hKc, hKL⟩ := ht L
  -- Split `F` into its compact part `F ∩ K` and the exponentially small remainder `Kᶜ`.
  have hsplit (i : ι) : ((ε i : ℝ) : EReal) * ENNReal.log (μ i F) ≤
      ((ε i : ℝ) : EReal) * ENNReal.log (μ i (F ∩ K) + μ i Kᶜ) := by
    refine mul_le_mul_of_nonneg_left (ENNReal.log_monotone ?_) (by exact_mod_cast (ε i).coe_nonneg)
    refine (measure_mono fun x hx => ?_).trans (measure_union_le (F ∩ K) Kᶜ)
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx, hxK⟩
    · exact Or.inr hxK
  have hFK : -((⨅ x ∈ F ∩ K, I x : ℝ≥0∞) : EReal) ≤ -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal) :=
    EReal.neg_le_neg_iff.2 <| EReal.coe_ennreal_le_coe_ennreal_iff.2 <|
      biInf_mono fun _ hx => hx.1
  calc limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i F)) l
      ≤ limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i (F ∩ K) + μ i Kᶜ)) l :=
        limsup_le_limsup (.of_forall hsplit)
    _ ≤ max (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i (F ∩ K))) l)
          (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i Kᶜ)) l) :=
        (limsup_coe_mul_log_add _ _ hε).le
    _ < c := max_lt (((hK _ (hKc.inter_left hF)).trans hFK).trans_lt hc) (hKL.trans_lt hL)

/-- Under exponential tightness in an `R₁` space, for instance a Hausdorff space, a lower
semicontinuous function satisfying the large deviation lower bound on open sets is a good rate
function. -/
theorem isGoodRateFunction [R1Space X] [l.NeBot] (ht : IsExponentiallyTight l ε μ)
    (hI : LowerSemicontinuous I)
    (hlower : ∀ G : Set X, IsOpen G →
      -((⨅ x ∈ G, I x : ℝ≥0∞) : EReal) ≤
        liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i G)) l) :
    IsGoodRateFunction I := by
  refine ⟨hI, fun α hα => ?_⟩
  obtain ⟨K, hK, hKL⟩ := ht (α.toReal + 1)
  -- The lower bound on the open set `(closure K)ᶜ` forces `I > α` off the compact `closure K`.
  have hKL' : limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i (closure K)ᶜ)) l ≤
      -((α.toReal + 1 : ℝ) : EReal) :=
    (limsup_le_limsup (.of_forall fun i => mul_le_mul_of_nonneg_left (ENNReal.log_monotone
      (measure_mono (Set.compl_subset_compl.2 subset_closure)))
      (by exact_mod_cast (ε i).coe_nonneg))).trans hKL
  have hrate : ((α.toReal + 1 : ℝ) : EReal) ≤ ((⨅ x ∈ (closure K)ᶜ, I x : ℝ≥0∞) : EReal) :=
    EReal.neg_le_neg_iff.1 <|
      ((hlower _ isClosed_closure.isOpen_compl).trans liminf_le_limsup).trans hKL'
  have hsub : {x | I x ≤ α} ⊆ closure K := fun x hx => by
    by_contra hxK
    have hle : ((α.toReal + 1 : ℝ) : EReal) ≤ ((α.toReal : ℝ) : EReal) := by
      refine hrate.trans ?_
      rw [EReal.coe_ennreal_toReal hα]
      exact EReal.coe_ennreal_le_coe_ennreal_iff.2 ((biInf_le _ hxK).trans hx)
    linarith [EReal.coe_le_coe_iff.1 hle]
  exact hK.closure.of_isClosed_subset (hI.isClosed_preimage α) hsub

end IsExponentiallyTight

namespace HasWeakLDP

/-- An exponentially tight family satisfying a weak large deviation principle, at a speed tending
to `0`, satisfies the full large deviation principle. -/
theorem hasLDP (h : HasWeakLDP l ε μ I) (ht : IsExponentiallyTight l ε μ)
    (hε : Tendsto ε l (𝓝 0)) : HasLDP l ε μ I :=
  ⟨h.lowerSemicontinuous, h.lower_bound, fun _ hF => ht.limsup_le_of_isClosed hε h.upper_bound hF⟩

/-- The rate function of a weak large deviation principle for an exponentially tight family in an
`R₁` space is good. -/
theorem isGoodRateFunction [R1Space X] [l.NeBot] (h : HasWeakLDP l ε μ I)
    (ht : IsExponentiallyTight l ε μ) : IsGoodRateFunction I :=
  ht.isGoodRateFunction h.lowerSemicontinuous h.lower_bound

end HasWeakLDP

/-- **Local criterion for the weak large deviation principle.** Suppose that, at an eventually
positive speed tending to `0`, the measures of sufficiently small neighbourhoods of every point
`x` decay at least at the rate `I x`, while the measures of all neighbourhoods of `x` decay at
most at that rate. Then a lower semicontinuous `I` is the rate function of a weak large deviation
principle. -/
theorem hasWeakLDP_of_forall_nhds
    (hupper : ∀ x, ⨅ U ∈ 𝓝 x,
      limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i U)) l ≤ -(I x : EReal))
    (hlower : ∀ x, ∀ U ∈ 𝓝 x,
      -(I x : EReal) ≤ liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i U)) l)
    (hI : LowerSemicontinuous I) (hε : Tendsto ε l (𝓝 0)) (hpos : ∀ᶠ i in l, 0 < ε i) :
    HasWeakLDP l ε μ I := by
  refine ⟨hI, fun G hG => ?_, fun K hK => le_of_forall_gt fun c hc => ?_⟩
  · rw [EReal.neg_le]
    simp_rw [EReal.coe_ennreal_iInf]
    exact le_iInf₂ fun x hx => EReal.neg_le.1 (hlower x G (hG.mem_nhds hx))
  -- Cover `K` by finitely many neighbourhoods whose rates are below `c`.
  have hU (x : X) (hx : x ∈ K) : ∃ U ∈ 𝓝 x,
      limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i U)) l < c := by
    have hxc : -(I x : EReal) < c :=
      (EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2 (biInf_le _ hx))).trans_lt hc
    simpa only [iInf_lt_iff, exists_prop] using (hupper x).trans_lt hxc
  choose! U hUx hUc using hU
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover U hUx
  have hcover (i : ι) : ((ε i : ℝ) : EReal) * ENNReal.log (μ i K) ≤
      ((ε i : ℝ) : EReal) * ENNReal.log (∑ x ∈ t, μ i (U x)) :=
    mul_le_mul_of_nonneg_left (ENNReal.log_monotone <|
      (measure_mono hKt).trans (measure_biUnion_finset_le t U)) (by exact_mod_cast (ε i).coe_nonneg)
  calc limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i K)) l
      ≤ limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (∑ x ∈ t, μ i (U x))) l :=
        limsup_le_limsup (.of_forall hcover)
    _ ≤ ⨆ x ∈ t, limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i (U x))) l :=
        (limsup_coe_mul_log_sum _ t hε hpos).le
    _ < c := by
      rw [← Finset.sup_eq_iSup]
      exact (Finset.sup_lt_iff (bot_le.trans_lt hc)).2 fun x hx => hUc x (htK x hx)

end TauCeti.Probability
