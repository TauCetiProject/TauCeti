/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Elementary real-measure identities and maps

This file records elementary identities about measures on the real line. The absolute-value map
folds the negative half-line onto the positive half-line. Squaring loses the sign of a real number
and nothing else, so it determines a measure on the line as soon as the measure cannot tell the two
signs apart. For a reflection-invariant measure, the pushforward under squaring is a complete
invariant: such a measure is determined by its mass on subsets of `(0, ∞)` and on `{0}`, and the
squared pushforward records both. For a measure carried by the nonnegative
half-line, squaring is undone by `Real.sqrt`, so the pushforward determines the measure outright.

## Main results

* `TauCeti.volume_Ioc_inter_Ioo_of_le_of_le` — the portion of an interval inside a larger open
  interval keeps its full length;
* `MeasureTheory.Measure.map_abs_eq_restrict_add_restrict` — decomposition of the image under
  absolute value into the two half-lines;
* `MeasureTheory.Measure.map_abs_apply_zero` — the image under absolute value preserves the atom
  at zero;
* `MeasureTheory.Measure.ae_eq_preimage_Ioc`,
  `MeasureTheory.Measure.measureReal_eq_sub_of_preimage_Ioo_subset` — for a law without atoms,
  endpoint conventions of an interval with extended bounds do not matter;
* `MeasureTheory.Measure.eq_of_map_sq_eq_of_map_neg_eq_self` — two symmetric real
  measures with the same pushforward after squaring are equal.
* `MeasureTheory.Measure.map_sqrt_map_sq` — on the nonnegative half-line, taking square roots
  undoes squaring.
-/

public section

open MeasureTheory Set

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
  rw [Measure.map_apply (by fun_prop) hs, hpre,
    measure_union hdisj (hs.neg.inter measurableSet_Iio)]
  simp [Measure.restrict_apply hs]

/-- The atom of the folded law at `0` is the atom of `μ` at `0`. -/
@[simp]
theorem map_abs_apply_zero (μ : Measure ℝ) : μ.map (|·|) {0} = μ {0} := by
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
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
    (ae_subset.2 (measure_mono_null (sdiff_subset_sdiff_left h₂) hnull)).antisymm
        h₁.eventuallySubset
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

/-- Two reflection-invariant measures on `ℝ` are equal if their pushforwards under squaring are
equal. Neither measure needs to be finite. -/
theorem eq_of_map_sq_eq_of_map_neg_eq_self (μ ν : Measure ℝ)
    (hμneg : μ.map (fun x : ℝ ↦ -x) = μ) (hνneg : ν.map (fun x : ℝ ↦ -x) = ν)
    (hsq : μ.map (fun x : ℝ ↦ x ^ 2) = ν.map (fun x : ℝ ↦ x ^ 2)) :
    μ = ν := by
  have hmeas : Measurable fun x : ℝ ↦ x ^ 2 := by fun_prop
  -- A reflection-invariant measure is determined by its masses of measurable subsets of the open
  -- positive half-line and of the origin: the negative half-line is the reflection of the former.
  have hsplit : ∀ ρ : Measure ℝ, ρ.map (fun x : ℝ ↦ -x) = ρ → ∀ s, MeasurableSet s →
      ρ s = ρ (s ∩ Ioi 0) + ρ (-s ∩ Ioi 0) + ρ (s ∩ {0}) := by
    intro ρ hρ s hs
    have : ρ.IsNegInvariant := ⟨hρ⟩
    have hneg : ρ (s ∩ Iio 0) = ρ (-s ∩ Ioi 0) := by
      rw [← Measure.measure_neg (μ := ρ) (s ∩ Iio 0), inter_neg, neg_Iio, neg_zero]
    have hdiff : s \ Ioi 0 = (s ∩ {0}) ∪ (s ∩ Iio 0) := by
      rw [sdiff_eq, compl_Ioi, ← Iio_union_right, inter_union_distrib_left, union_comm]
    rw [← measure_inter_add_sdiff s (measurableSet_Ioi (a := (0 : ℝ))), hdiff,
      measure_union ((disjoint_singleton_left.2 self_notMem_Iio).mono inter_subset_right
        inter_subset_right) (hs.inter measurableSet_Iio), hneg]
    ring
  -- Squaring followed by `Real.sqrt` is folding, so the squared pushforward determines the folded
  -- law, which records the atom at zero and twice the mass of a subset of the positive half-line.
  have hfold : ∀ ρ : Measure ℝ, (ρ.map (fun x : ℝ ↦ x ^ 2)).map Real.sqrt = ρ.map (|·|) :=
    fun ρ ↦ by
      rw [Measure.map_map (by fun_prop) hmeas]
      exact congrArg ρ.map (funext Real.sqrt_sq_eq_abs)
  have hpos : ∀ ρ : Measure ℝ, ρ.map (fun x : ℝ ↦ -x) = ρ → ∀ t ⊆ Ioi 0,
      ρ.map (|·|) t = 2 * ρ t := by
    intro ρ hρ t hts
    have hneg : ρ.neg = ρ := hρ
    rw [Measure.map_abs_eq_restrict_add_restrict, hneg, _root_.add_apply,
      Measure.restrict_eq_self _ (hts.trans Ioi_subset_Ici_self), Measure.restrict_eq_self _ hts,
      two_mul]
  have habs : μ.map (|·|) = ν.map (|·|) := by rw [← hfold μ, ← hfold ν, hsq]
  ext s hs
  have hμν : ∀ t ⊆ Ioi 0, μ t = ν t := fun t hts ↦ by
    refine (ENNReal.mul_right_inj two_ne_zero (by finiteness)).1 ?_
    rw [← hpos μ hμneg t hts, ← hpos ν hνneg t hts, habs]
  have h0 : μ (s ∩ {0}) = ν (s ∩ {0}) := by
    by_cases h : (0 : ℝ) ∈ s
    · rw [inter_singleton_of_mem h, ← Measure.map_abs_apply_zero μ, ← Measure.map_abs_apply_zero ν,
        habs]
    · rw [inter_singleton_eq_empty.2 h]
      simp
  rw [hsplit μ hμneg s hs, hsplit ν hνneg s hs, hμν _ inter_subset_right,
    hμν _ inter_subset_right, h0]

/-- **Square roots undo squaring** for a measure carried by the nonnegative half-line: the
pushforward of `μ` under `x ↦ x ^ 2` returns to `μ` under `Real.sqrt`. -/
theorem map_sqrt_map_sq (μ : Measure ℝ) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) :
    (μ.map fun t : ℝ ↦ t ^ 2).map Real.sqrt = μ := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  refine (Measure.map_congr ?_).trans Measure.map_id
  filter_upwards [hμ] with t ht
  simpa using Real.sqrt_sq ht

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

/-- For `c ≤ a` and `b ≤ d`, the part of `Ioc a b` lying in the open interval `Ioo c d` has the
full length `b - a`: the two sets differ at most at the endpoint `d`. -/
@[simp]
theorem volume_Ioc_inter_Ioo_of_le_of_le {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    volume (Ioc a b ∩ Ioo c d) = ENNReal.ofReal (b - a) := by
  refine le_antisymm ((measure_mono inter_subset_left).trans_eq Real.volume_Ioc) ?_
  rw [← Real.volume_Ioo]
  exact measure_mono fun t ht ↦ ⟨Ioo_subset_Ioc_self ht, hca.trans_lt ht.1, ht.2.trans_le hbd⟩

end TauCeti
