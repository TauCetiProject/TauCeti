/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Injective pieces of a differentiable map

A measurable set on which a map has injective derivative admits a countable measurable
partition on which the map is bi-Lipschitz. This decomposition permits summation of
injective change-of-variables and area formulas with multiplicity, without requiring
the original map to be injective.

The construction uses Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §3.3 (decomposition into injective pieces in the area formula).
-/

public section

open Set Function MeasureTheory Metric Module
open scoped NNReal ENNReal

namespace TauCeti

/-- A measurable set on which the derivative is injective has a countable measurable
partition into bi-Lipschitz pieces. No global Lipschitz assumption is needed. -/
theorem exists_partition_lipschitz_antilipschitz_of_hasFDerivWithinAt
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [SecondCountableTopology V]
    {f : U → V} {s : Set U} {f' : U → U →L[ℝ] V}
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, Injective (f' x)) :
    ∃ (p : ℕ → Set U) (L K : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (p n)) ∧ Pairwise (Disjoint on p) ∧ (⋃ n, p n) = s ∧
      ∀ n, LipschitzWith (L n) ((p n).domRestrict f) ∧
        AntilipschitzWith (K n) ((p n).domRestrict f) := by
  classical
  have hA (A : U →L[ℝ] V) : ∃ K : ℝ≥0, 0 < K ∧ (Injective A → AntilipschitzWith K A) := by
    by_cases h : Injective A
    · obtain ⟨K, hK, hAK⟩ := (A : U →ₗ[ℝ] V).injective_iff_antilipschitz.mp h
      exact ⟨K, hK, fun _ ↦ hAK⟩
    · exact ⟨1, zero_lt_one, fun h' ↦ (h h').elim⟩
  choose K hK hAK using hA
  let r (A : U →L[ℝ] V) : ℝ≥0 := (2 * K A)⁻¹
  have hr (A : U →L[ℝ] V) : r A ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) (hK A).ne')
  obtain ⟨t, A, ht, htm, hcover, happ, hder⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hd r hr
  refine ⟨fun n ↦ s ∩ t n, fun n ↦ ‖A n‖₊ + r (A n),
    fun n ↦ ((K (A n))⁻¹ - r (A n))⁻¹,
    fun n ↦ hs.inter (htm n), ?_, ?_, ?_⟩
  · exact fun i j hij ↦ (ht hij).mono inter_subset_right inter_subset_right
  · simpa only [← inter_iUnion, inter_eq_left] using hcover
  · intro n
    refine ⟨(happ n).lipschitzWith, ?_⟩
    by_cases hne : s.Nonempty
    · obtain ⟨x, hx, hAx⟩ := hder hne n
      have hanti := hAK (A n) (hAx ▸ hinj x hx)
      have hsmall : r (A n) < (K (A n))⁻¹ := by
        dsimp [r]
        rw [mul_inv_rev]
        simpa using mul_lt_mul_of_pos_left (by norm_num : (2 : ℝ≥0)⁻¹ < 1)
          (inv_pos.mpr (hK (A n)))
      convert hanti.domRestrict (s ∩ t n) |>.add_lipschitzWith
        (happ n).lipschitzWith_sub hsmall using 1
      ext x
      simp only [domRestrict_apply, add_sub_cancel]
    · intro x
      exact (hne ⟨x, x.property.1⟩).elim

end TauCeti
