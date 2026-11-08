/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.CDF

/-!
# Elementary real-measure identities and maps

This file records elementary identities about measures on the real line. The absolute-value map
folds the negative half-line onto the positive half-line. Squaring loses the sign of a real number
and nothing else, so it determines a measure on the line as soon as the measure cannot tell the two
signs apart. For a reflection-invariant finite measure, the pushforward under squaring is a complete
invariant: the square records the mass of intervals symmetric about zero, while reflection
invariance makes the two complementary tails equal. For a measure carried by the nonnegative
half-line, squaring is undone by `Real.sqrt`, so the pushforward determines the measure outright.

## Main results

* `TauCeti.volume_Ioc_inter_Ioo_zero_one` — the portion of an interval in the open unit interval;
* `MeasureTheory.Measure.map_abs_eq_restrict_add_restrict` — decomposition of the image under
  absolute value into the two half-lines;
* `MeasureTheory.Measure.map_abs_apply_zero` — the image under absolute value preserves the atom
  at zero;
* `MeasureTheory.Measure.ae_eq_preimage_Ioc`,
  `MeasureTheory.Measure.measureReal_eq_sub_of_preimage_Ioo_subset` — for a law without atoms,
  endpoint conventions of an interval with extended bounds do not matter;
* `MeasureTheory.Measure.eq_of_map_sq_eq_of_map_neg_eq_self` — two symmetric finite real
  measures with the same pushforward after squaring are equal.
* `MeasureTheory.Measure.map_sqrt_map_sq` — on the nonnegative half-line, taking square roots
  undoes squaring.
-/

public section

open MeasureTheory ProbabilityTheory Set

private theorem measurable_abs : Measurable fun x : ℝ => |x| := continuous_abs.measurable

namespace MeasureTheory.Measure

/-- **The folded law.** Folding keeps the nonnegative half of `μ` in place and reflects its
negative half onto the positive half-line. -/
theorem map_abs_eq_restrict_add_restrict (μ : Measure ℝ) :
    μ.map (|·|) = μ.restrict (Ici 0) + μ.neg.restrict (Ioi 0) := by
  ext s hs
  have hpre : (|·|) ⁻¹' s = (s ∩ Ici 0) ∪ (-s ∩ Iio 0) := by
    ext x
    rcases le_or_gt 0 x with hx | hx
    · simp [hx, abs_of_nonneg hx, not_lt.2 hx]
    · simp [hx, abs_of_neg hx, not_le.2 hx]
  have hdisj : Disjoint (s ∩ Ici 0) (-s ∩ Iio 0) :=
    disjoint_left.2 fun x hx hx' => not_le.2 hx'.2 hx.2
  rw [Measure.map_apply measurable_abs hs, hpre,
    measure_union hdisj (hs.neg.inter measurableSet_Iio), _root_.add_apply,
    Measure.restrict_apply hs, Measure.restrict_apply hs, MeasureTheory.Measure.neg_apply,
    (by ext x; simp : -(s ∩ Ioi (0 : ℝ)) = -s ∩ Iio 0)]

/-- The atom of the folded law at `0` is the atom of `μ` at `0`. -/
@[simp]
theorem map_abs_apply_zero (μ : Measure ℝ) : μ.map (|·|) {0} = μ {0} := by
  rw [Measure.map_apply measurable_abs (measurableSet_singleton 0)]
  congr 1
  ext x
  simp

section NullSingleton

variable {μ : Measure ℝ} [NullSingletonClass μ] {s : Set ℝ} {l r : EReal}

/-- For a law without atoms, a set between the open and the closed interval with extended bounds
`l, r` agrees with the half-open interval `(l, r]` off a null set: the two candidate endpoints
carry no mass. -/
theorem ae_eq_preimage_Ioc (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s)
    (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    s =ᵐ[μ] Real.toEReal ⁻¹' Ioc l r := by
  have hnull : μ (Real.toEReal ⁻¹' Icc l r \ Real.toEReal ⁻¹' Ioo l r) = 0 := by
    refine measure_mono_null (t := {l.toReal, r.toReal}) ?_ ((toFinite _).measure_zero _)
    rintro x ⟨⟨hlx, hxr⟩, hx⟩
    by_contra hne
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
    exact hx ⟨hlx.lt_of_ne fun h => hne.1 (by rw [h, EReal.toReal_coe]),
      hxr.lt_of_ne fun h => hne.2 (by rw [← h, EReal.toReal_coe])⟩
  have hopen {t : Set ℝ} (h₁ : Real.toEReal ⁻¹' Ioo l r ⊆ t)
      (h₂ : t ⊆ Real.toEReal ⁻¹' Icc l r) :
      t =ᵐ[μ] Real.toEReal ⁻¹' Ioo l r :=
    (ae_le_set.2 (measure_mono_null (sdiff_subset_sdiff_left h₂) hnull)).antisymm h₁.eventuallyLE
  exact (hopen hs₁ hs₂).trans (hopen (preimage_mono Ioo_subset_Ioc_self)
    (preimage_mono Ioc_subset_Icc_self)).symm

/-- For a finite law without atoms, the mass of a set between the open and the closed interval
with extended bounds `l ≤ r` is the difference of the masses up to the two bounds. -/
theorem measureReal_eq_sub_of_preimage_Ioo_subset [IsFiniteMeasure μ] (hlr : l ≤ r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    μ.real s = μ.real (Real.toEReal ⁻¹' Iic r) - μ.real (Real.toEReal ⁻¹' Iic l) := by
  rw [measureReal_congr (μ.ae_eq_preimage_Ioc hs₁ hs₂), ← Iic_sdiff_Iic, preimage_sdiff,
    measureReal_sdiff (preimage_mono (Iic_subset_Iic.2 hlr))
      (measurableSet_Iic.preimage measurable_coe_real_ereal)]

end NullSingleton

end MeasureTheory.Measure

namespace TauCeti

/-- The pushforward of Lebesgue measure under an invertible affine map.
Translation preserves volume, while scaling contributes the reciprocal absolute slope. -/
theorem map_volume_mul_add {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    volume.map (fun t ↦ c * t + d) = ENNReal.ofReal |c⁻¹| • volume := by
  have hcomp : (fun t : ℝ ↦ c * t + d) = (fun t ↦ t + d) ∘ (fun t ↦ c * t) := rfl
  rw [hcomp, ← Measure.map_map (measurable_add_const d) (measurable_const_mul c),
    Real.map_volume_mul_left hc, Measure.map_smul, map_add_right_eq_self]
  exact (measurable_add_const d).aemeasurable

/-- The part of a subinterval `Ioc a b` of `[0, 1]` lying in the open unit interval has the full
length `b - a`: the two intervals differ at most at the endpoint `1`. -/
@[simp]
theorem volume_Ioc_inter_Ioo_zero_one {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    volume (Ioc a b ∩ Ioo 0 1) = ENNReal.ofReal (b - a) := by
  refine le_antisymm ((measure_mono inter_subset_left).trans_eq Real.volume_Ioc) ?_
  rw [← Real.volume_Ioo]
  exact measure_mono fun t ht ↦ ⟨Ioo_subset_Ioc_self ht, ha.trans_lt ht.1, ht.2.trans_le hb⟩

/-- Two reflection-invariant finite measures on `ℝ` are equal if their pushforwards under
squaring are equal. -/
theorem _root_.MeasureTheory.Measure.eq_of_map_sq_eq_of_map_neg_eq_self (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμneg : μ.map (fun x : ℝ ↦ -x) = μ) (hνneg : ν.map (fun x : ℝ ↦ -x) = ν)
    (hsq : μ.map (fun x : ℝ ↦ x ^ 2) = ν.map (fun x : ℝ ↦ x ^ 2)) :
    μ = ν := by
  apply Measure.ext_of_Iic
  intro x
  rw [← measureReal_eq_measureReal_iff]
  -- For a reflection-invariant finite measure `ρ`, twice the mass of `Iic x` is read off the
  -- squared law: through the central interval `[-x, x]` when `0 ≤ x`, and through `(x, -x)` when
  -- `x < 0`, the two complementary tails being equal by symmetry.
  suffices h : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ → ρ.map (fun y : ℝ ↦ -y) = ρ →
      2 * ρ.real (Iic x) = if 0 ≤ x then
        (ρ.map (· ^ 2)).real univ + (ρ.map (· ^ 2)).real (Iic (x ^ 2))
      else (ρ.map (· ^ 2)).real univ - (ρ.map (· ^ 2)).real (Iio (x ^ 2)) by
    have h' := h μ inferInstance hμneg
    rw [hsq, ← h ν inferInstance hνneg] at h'
    linarith
  intro ρ _ hρ
  have : ρ.IsNegInvariant := ⟨hρ⟩
  rw [map_measureReal_apply (by fun_prop) MeasurableSet.univ, preimage_univ]
  split_ifs with hx
  · rw [map_measureReal_apply (by fun_prop) measurableSet_Iic,
      show (fun y : ℝ ↦ y ^ 2) ⁻¹' Iic (x ^ 2) = Icc (-x) x by
        ext y; simp [sq_le_sq, abs_of_nonneg hx, abs_le]]
    have htail : ρ.real (-Ioi x) = ρ.real (Ioi x) := by
      rw [measureReal_def, Measure.measure_neg, ← measureReal_def]
    have htot := measureReal_add_measureReal_compl (μ := ρ) (measurableSet_Iic (a := x))
    rw [Set.neg_Ioi] at htail
    rw [compl_Iic] at htot
    rw [← Iio_union_Icc_eq_Iic (by linarith : -x ≤ x), measureReal_union
      ((Iio_disjoint_Ici le_rfl).mono_right Icc_subset_Ici_self) measurableSet_Icc] at htot ⊢
    linarith
  · rw [map_measureReal_apply (by fun_prop) measurableSet_Iio,
      show (fun y : ℝ ↦ y ^ 2) ⁻¹' Iio (x ^ 2) = Ioo x (-x) by
        ext y; simp [sq_lt_sq, abs_of_neg (not_le.1 hx), abs_lt]]
    have htail : ρ.real (-Ici (-x)) = ρ.real (Ici (-x)) := by
      rw [measureReal_def, Measure.measure_neg, ← measureReal_def]
    have htot := measureReal_add_measureReal_compl (μ := ρ) (measurableSet_Ici (a := -x))
    rw [Set.neg_Ici, neg_neg] at htail
    rw [compl_Ici, ← Iic_union_Ioo_eq_Iio (by linarith : x < -x),
      measureReal_union ((Iic_disjoint_Ioi le_rfl).mono_right Ioo_subset_Ioi_self)
        measurableSet_Ioo] at htot
    linarith

/-- **Square roots undo squaring** for a measure carried by the nonnegative half-line: the
pushforward of `μ` under `x ↦ x ^ 2` returns to `μ` under `Real.sqrt`. -/
theorem _root_.MeasureTheory.Measure.map_sqrt_map_sq (μ : Measure ℝ) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) :
    (μ.map fun t : ℝ ↦ t ^ 2).map Real.sqrt = μ := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  refine (Measure.map_congr ?_).trans Measure.map_id
  filter_upwards [hμ] with t ht
  simpa using Real.sqrt_sq ht

end TauCeti
