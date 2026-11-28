/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.WeightedCosetSelection
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.GroupTheory.Coset.Fiber
import TauCeti.NumberTheory.Chebyshev.Mertens

/-!
# Selecting tops for cyclic Frobenius averages

Select positions independently, at a rate four thirds as high in the identity coset as in
other cosets. This profile gives nontrivial cyclic characters positive weight in the
Frobenius average. At the dyadic host scales, the same selection gives the required
precision in the coset counts and a small logarithmically weighted count of bad positions.

The weighted bad-orbit count follows Levent Alpöge's `Formalism.MainNotions.J.tops_exist_of`
in [`GandSa.lean`][alpoege-rh], where the sampling profile is uniform.

[alpoege-rh]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSa.lean
-/

public section

open Finset Filter MeasureTheory ProbabilityTheory Real Set

namespace Subgroup

variable {A : Type*} [Group A]

open Classical in
/-- The independent selection measure on subsets of `A` (represented by Boolean functions),
with inclusion probability `δ` on `H` and `3δ/4` off `H`. -/
noncomputable def cyclicTopSelectionMeasure [Fintype A] (H : Subgroup A) (δ : unitInterval) :
    Measure (A → Bool) :=
  Measure.pi fun a ↦ bernoulliMeasure true false
    (δ * if a ∈ H then 1 else ⟨3 / 4, by norm_num⟩)

open Classical in
/-- The product formula for the cyclic top selection measure. -/
theorem cyclicTopSelectionMeasure_def [Fintype A] (H : Subgroup A) (δ : unitInterval) :
    H.cyclicTopSelectionMeasure δ = Measure.pi fun a ↦ bernoulliMeasure true false
      (δ * if a ∈ H then 1 else ⟨3 / 4, by norm_num⟩) :=
  (rfl)

open Classical in
/-- The marginal probability of selecting a position is its prescribed inclusion rate. -/
@[simp]
theorem measureReal_cyclicTopSelectionMeasure_eval_eq_true [Fintype A]
    (H : Subgroup A) (δ : unitInterval) (a : A) :
    (H.cyclicTopSelectionMeasure δ).real {s | s a = true} =
      (δ : ℝ) * (if a ∈ H then 1 else 3 / 4) := by
  rw [cyclicTopSelectionMeasure_def,
    TauCeti.Probability.measureReal_pi_bernoulliMeasure_eval_eq_true, Set.Icc.coe_mul]
  split_ifs <;> simp

/-- The cyclic top selection measure is a probability measure. -/
instance isProbabilityMeasure_cyclicTopSelectionMeasure [Fintype A]
    (H : Subgroup A) (δ : unitInterval) : IsProbabilityMeasure (H.cyclicTopSelectionMeasure δ) := by
  rw [cyclicTopSelectionMeasure_def]
  infer_instance

open Classical in
/-- The two inclusion-rate multipliers, before normalizing to coset shares. -/
private noncomputable def cyclicTopProfile {Q : Type*} [One Q] (q : Q) : unitInterval :=
  if q = 1 then 1 else ⟨3 / 4, by norm_num⟩

open Classical in
/-- Write the profile as its constant part plus its excess at the identity. -/
private theorem coe_cyclicTopProfile {Q : Type*} [One Q] (q : Q) :
    (cyclicTopProfile q : ℝ) = 3 / 4 + if q = 1 then 1 / 4 else 0 := by
  by_cases h : q = 1 <;> norm_num [cyclicTopProfile, h]

/-- In quotient coordinates the independent draws use the two-level profile. -/
private theorem cyclicTopSelectionMeasure_eq_pi [Fintype A] (H : Subgroup A) [H.Normal]
    (δ : unitInterval) : H.cyclicTopSelectionMeasure δ = Measure.pi fun a ↦
      bernoulliMeasure true false (δ * cyclicTopProfile (QuotientGroup.mk' H a)) := by
  rw [cyclicTopSelectionMeasure_def]
  congr 1
  funext a
  have ha : QuotientGroup.mk' H a = 1 ↔ a ∈ H := QuotientGroup.eq_one_iff a
  by_cases h : a ∈ H
  · simp only [cyclicTopProfile, ite_eq_left h, ite_eq_left (ha.mpr h)]
  · simp only [cyclicTopProfile, ite_eq_right h, ite_eq_right (ha.not.mpr h)]

open Classical in
/-- The expected size for the two-level profile is between `3D/4` and `D`, where
`D = δ * |A|`. Express its normalizing sum in terms of the index. -/
private theorem cyclicTopProfile_sum_and_mean_bounds [Fintype A] (H : Subgroup A) [H.Normal]
    [Fintype (A ⧸ H)] (δ : unitInterval) :
    let s := ∑ q : A ⧸ H, (cyclicTopProfile q : ℝ)
    let D := (δ : ℝ) * Fintype.card A
    s = (3 * (H.index : ℝ) + 1) / 4 ∧
      3 / 4 * D ≤ (δ : ℝ) * Nat.card H * s ∧ (δ : ℝ) * Nat.card H * s ≤ D := by
  have hq : Fintype.card (A ⧸ H) = H.index := Nat.card_eq_fintype_card.symm
  have hcard : (Fintype.card A : ℝ) = (H.index : ℝ) * Nat.card H := by
    exact_mod_cast (Nat.card_eq_fintype_card (α := A)).symm.trans
      H.card_eq_card_quotient_mul_card_subgroup
  have hextra : (∑ q : A ⧸ H, if q = 1 then (1 / 4 : ℝ) else 0) = 1 / 4 := by
    rw [sum_eq_single 1]
    · simp
    · intro q _ hq
      simp [hq]
    · simp
  have hsum : (∑ q : A ⧸ H, (cyclicTopProfile q : ℝ)) = (3 * (H.index : ℝ) + 1) / 4 := by
    simp only [coe_cyclicTopProfile, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hq]
    calc
      _ = (H.index : ℝ) * (3 / 4) + 1 / 4 := by
        congr 1
        convert hextra using 2
        split_ifs <;> rfl
      _ = _ := by ring
  have ho : (1 : ℝ) ≤ H.index := by
    rw [← hq, Nat.one_le_cast]
    exact Fintype.card_pos
  have hδm : 0 ≤ (δ : ℝ) * Nat.card H := mul_nonneg δ.prop.1 (Nat.cast_nonneg _)
  dsimp only
  refine ⟨hsum, ?_, ?_⟩ <;> rw [hsum, hcard]
  · nlinarith only [hδm]
  · nlinarith only [mul_nonneg hδm (sub_nonneg.mpr ho)]

open Classical in
/-- If the total sampling scale `δ * |A|` is at least `64 * [A : H]²`, with probability
at least `1/2` the sample has size between `δ * |A| / 2` and `3 * δ * |A| / 2`. Its coset
counts approximate the shares in ratio `4 : 3`, and its weighted bad count is at most
`8 * p * |S|` times the total weight. The probability of being selected and bad at an index
must be at most `p` times the selection probability. Bad events may depend on the entire sample. -/
theorem half_le_measureReal_cyclicTopSelection [Fintype A] (H : Subgroup A) [H.Normal]
    (δ : unitInterval) (hsize : 64 * (H.index : ℝ) ^ 2 ≤ (δ : ℝ) * Fintype.card A)
    {ι : Type*} (I : Finset ι) {w : ι → ℝ} (hw : ∀ i ∈ I, 0 ≤ w i)
    (B : ι → A → Set (A → Bool)) (p : NNReal)
    (hbad : ∀ i ∈ I, ∀ a, (H.cyclicTopSelectionMeasure δ).real ({s | s a = true} ∩ B i a) ≤
      (p : ℝ) * (H.cyclicTopSelectionMeasure δ).real {s | s a = true}) :
    (1 / 2 : ℝ) ≤ (H.cyclicTopSelectionMeasure δ).real {s |
      let S := univ.filter fun a ↦ s a = true
      let D := (δ : ℝ) * Fintype.card A
      D / 2 ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ 3 * D / 2 ∧
      (∀ q : A ⧸ H, |((S.filter fun a ↦ QuotientGroup.mk' H a = q).card : ℝ) -
        ((if q = 1 then 4 else 3) / (3 * (H.index : ℝ) + 1)) * S.card| ≤
        (112 / 9 / √D) * S.card) ∧
      S.weightedEventCount I w B s ≤ 8 * (p : ℝ) * S.card * ∑ i ∈ I, w i} := by
  let Q := A ⧸ H
  let : Fintype Q := Fintype.ofFinite Q
  let f : A →* Q := QuotientGroup.mk' H
  let ω : Q → unitInterval := cyclicTopProfile
  have hf (q : Q) : (univ.filter fun a ↦ f a = q).card = Nat.card H := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective H q
    have h := (QuotientGroup.mk' H).card_fiber_eq_card_ker ha
    simpa only [QuotientGroup.ker_mk', Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  have hq : Fintype.card Q = H.index := Nat.card_eq_fintype_card.symm
  have hμ : H.cyclicTopSelectionMeasure δ = Measure.pi fun a ↦
      bernoulliMeasure true false (δ * ω (f a)) := cyclicTopSelectionMeasure_eq_pi H δ
  obtain ⟨hsum, hmeanlo, hmeanhi⟩ := cyclicTopProfile_sum_and_mean_bounds H δ
  have hscale₁ : 16 * (Fintype.card Q : ℝ) ^ 2 / (3 / 4) ^ 2 ≤ (δ : ℝ) * Fintype.card A := by
    rw [hq]
    norm_num
    linarith [sq_nonneg (H.index : ℝ)]
  have hscale₂ : 36 * (Fintype.card Q : ℝ) ^ 2 / (3 / 4) ^ 2 ≤ (δ : ℝ) * Fintype.card A := by
    rw [hq]
    convert hsize using 1
    ring
  have hs := TauCeti.half_le_measureReal_bernoulli_card_fiber_and_weightedEventCount
    (Q := Q) f (m := Nat.card H) (fun q ↦ by
      convert hf q using 1
      congr 1
      apply filter_congr_decidable) δ ω
    (by norm_num : (0 : ℝ) < 3 / 4)
    (fun q ↦ by rw [coe_cyclicTopProfile]; split_ifs <;> norm_num) hscale₁ I hw B p (fun i hi a ↦ by
      have hm := TauCeti.Probability.measureReal_pi_bernoulliMeasure_eval_eq_true
        (fun a' ↦ δ * ω (f a')) a
      rw [← Set.Icc.coe_mul, ← hm, ← hμ]
      exact hbad i hi a)
  rw [← hμ] at hs
  refine hs.trans (measureReal_mono fun s hs ↦ ?_)
  obtain ⟨_, hup, hlo, hdisc, hbad₁, hbad₂⟩ := hs
  refine ⟨by linarith only [hlo hscale₂, hmeanlo], by linarith only [hup, hmeanhi],
    fun q ↦ ?_, hbad₁.trans hbad₂⟩
  have hν : (ω q : ℝ) / ∑ j, (ω j : ℝ) = (if q = 1 then 4 else 3) / (3 * (H.index : ℝ) + 1) := by
    rw [hsum, div_div_eq_mul_div, coe_cyclicTopProfile]
    congr 1
    split_ifs <;> norm_num
  have hd := hdisc q
  have hconst : (4 * (1 + 3 / 4) / (3 / 4) ^ 2 : ℝ) = 112 / 9 := by norm_num
  rw [hν, hconst] at hd
  convert hd using 5
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]

end Subgroup

namespace TauCeti

open Classical in
/-- At the dyadic host scales, the `4 : 3` selection simultaneously attains the top density,
coset precision and weighted bad-top bound. Here `I` is any set of primes up to the thin
cutoff `exp (x ^ (ε / 3))`; the joint probability that a position is selected and bad at
`p ∈ I` is at most `C / x²` times its probability of selection. The threshold depends
only on `ε`, the index `o` and this constant `C`, not on the group, the primes or the events. -/
theorem eventually_half_le_measureReal_cyclicTopSelection (o : ℕ) (C : NNReal) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop, ∃ δ : unitInterval, (δ : ℝ) = x ^ (-ε / 8) ∧
      ∀ {A : Type*} [Group A] [Fintype A] (H : Subgroup A) [H.Normal],
        H.index = o → x ^ (2 + 8 * ε) ≤ Fintype.card A →
        ∀ (I : Finset ℕ), I ⊆ Nat.primesLE ⌊exp (x ^ (ε / 3))⌋₊ →
        ∀ (B : ℕ → A → Set (A → Bool)),
        (∀ p ∈ I, ∀ a, (H.cyclicTopSelectionMeasure δ).real ({s | s a = true} ∩ B p a) ≤
          ((C : ℝ) / x ^ 2) * (H.cyclicTopSelectionMeasure δ).real {s | s a = true}) →
        (1 / 2 : ℝ) ≤ (H.cyclicTopSelectionMeasure δ).real {s |
          let S := univ.filter fun a ↦ s a = true
          x ^ (-ε / 8) * Fintype.card A / 2 ≤ (S.card : ℝ) ∧
          (S.card : ℝ) ≤ 3 * (x ^ (-ε / 8) * Fintype.card A) / 2 ∧
          (∀ q : A ⧸ H, |((S.filter fun a ↦ QuotientGroup.mk' H a = q).card : ℝ) -
            ((if q = 1 then 4 else 3) / (3 * (o : ℝ) + 1)) * S.card| ≤
            x ^ (-1 + ε) * S.card) ∧
          S.weightedEventCount I (fun p ↦ log p / p) B s ≤ S.card * x ^ (-2 + ε)} := by
  have h₁ := (tendsto_rpow_atTop (by linarith : 0 < 2 + 63 * ε / 8)).eventually_ge_atTop
    (64 * (o : ℝ) ^ 2)
  have h₂ := (tendsto_rpow_atTop (by linarith : 0 < 79 * ε / 16)).eventually_ge_atTop (112 / 9)
  have h₃ := (tendsto_rpow_atTop (by linarith : 0 < 2 * ε / 3)).eventually_ge_atTop
    (8 * (C : ℝ) * (1 + (log 4 + 4)))
  filter_upwards [eventually_ge_atTop (1 : ℝ), h₁, h₂, h₃] with x hx hsize hprec hcost
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  let δ : unitInterval := ⟨x ^ (-ε / 8), rpow_nonneg hx₀.le _,
    rpow_le_one_of_one_le_of_nonpos hx (by linarith)⟩
  refine ⟨δ, rfl, ?_⟩
  intro A _ _ H _ ho hA I hI B hbad
  have hD : x ^ (2 + 63 * ε / 8) ≤ (δ : ℝ) * Fintype.card A := calc
    _ = x ^ (-ε / 8) * x ^ (2 + 8 * ε) := by rw [← rpow_add hx₀]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hA δ.prop.1
  have hη : 112 / 9 / √((δ : ℝ) * Fintype.card A) ≤ x ^ (-1 + ε) := by
    apply (div_le_iff₀ (sqrt_pos_of_pos ((rpow_pos_of_pos hx₀ _).trans_le hD))).2
    calc
      112 / 9 ≤ x ^ (79 * ε / 16) := hprec
      _ = x ^ (-1 + ε) * √(x ^ (2 + 63 * ε / 8)) := by
        rw [sqrt_eq_rpow, ← rpow_mul hx₀.le, ← rpow_add hx₀]
        congr 1
        ring
      _ ≤ _ := by gcongr
  -- The logarithmic weight of the thin primes costs only a power `x ^ (ε / 3)`.
  have hbudget : 8 * ((C : ℝ) / x ^ 2) * (∑ p ∈ I, log p / p) ≤ x ^ (-2 + ε) := by
    have hy : 1 ≤ exp (x ^ (ε / 3)) := one_le_exp (rpow_nonneg hx₀.le _)
    have hsum := (sum_le_sum_of_subset_of_nonneg hI (fun p _ _ ↦ by positivity)).trans
      (Chebyshev.sum_primesLE_log_div_le hy)
    rw [log_exp] at hsum
    have hu := one_le_rpow hx (by linarith : 0 ≤ ε / 3)
    have hc : 0 ≤ log 4 + 4 := by positivity
    have ht : ∑ p ∈ I, log p / p ≤ (1 + (log 4 + 4)) * x ^ (ε / 3) := by
      linarith only [hsum, mul_le_mul_of_nonneg_left hu hc]
    calc
      _ ≤ 8 * ((C : ℝ) / x ^ 2) * ((1 + (log 4 + 4)) * x ^ (ε / 3)) := by gcongr
      _ = (8 * (C : ℝ) * (1 + (log 4 + 4))) * x ^ (ε / 3) / x ^ 2 := by ring
      _ ≤ x ^ (2 * ε / 3) * x ^ (ε / 3) / x ^ 2 := by gcongr
      _ = _ := by rw [← rpow_add hx₀, ← rpow_natCast, ← rpow_sub hx₀]; congr 1; push_cast; ring
  let pbad : NNReal := ⟨(C : ℝ) / x ^ 2, by positivity⟩
  have hs := H.half_le_measureReal_cyclicTopSelection δ (ho ▸ hsize.trans hD) I
    (w := fun p ↦ log p / p) (fun p _ ↦ by positivity) B pbad hbad
  refine hs.trans (measureReal_mono fun s hs ↦ ?_)
  obtain ⟨hlo, hup, hdisc, hcount⟩ := hs
  refine ⟨hlo, hup, fun q ↦ ?_, hcount.trans ?_⟩
  · rw [← ho]
    exact (hdisc q).trans (mul_le_mul_of_nonneg_right hη (by positivity))
  · have hpbad : (pbad : ℝ) = (C : ℝ) / x ^ 2 := rfl
    simpa only [hpbad, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hbudget
        (Nat.cast_nonneg (α := ℝ) (univ.filter fun a ↦ s a = true).card)

end TauCeti
