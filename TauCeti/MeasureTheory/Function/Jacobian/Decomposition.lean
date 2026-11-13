/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.Analysis.Normed.Module.RelativeApproximation

/-!
# Injective pieces of a differentiable map

A measurable set on which a map has injective derivative admits a countable measurable
partition on which the map is bi-Lipschitz. This decomposition permits summation of
injective change-of-variables and area formulas with multiplicity, without requiring
the original map to be injective.

The construction uses Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, with an absolute error scaled to
each candidate linear map, so that on every piece the map is within any prescribed relative error
`δ` of an injective linear map
(`TauCeti.exists_partition_linear_approximation_of_hasFDerivWithinAt`).
For `δ < 1` such a piece has a Lipschitz inverse
(`TauCeti.exists_antilipschitzWith_domRestrict_of_approx`), which gives the bi-Lipschitz partition
`TauCeti.exists_partition_lipschitz_antilipschitz_of_hasFDerivWithinAt`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §3.3 (decomposition into injective pieces in the area formula).
-/

public section

open Set Function MeasureTheory Metric Module
open scoped NNReal ENNReal

namespace TauCeti

/-- A measurable set on which the derivative is injective has, for every `δ > 0`, a countable
measurable partition into pieces `p n`, each with a linear map `A n` that is injective whenever
the piece is nonempty and satisfies `‖f x - f y - A n (x - y)‖ ≤ δ ‖A n (x - y)‖` on the piece.
No global Lipschitz assumption is needed. -/
theorem exists_partition_linear_approximation_of_hasFDerivWithinAt
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [SecondCountableTopology V]
    {f : U → V} {s : Set U} {f' : U → U →L[ℝ] V} {δ : ℝ}
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, Injective (f' x)) (hδ : 0 < δ) :
    ∃ (p : ℕ → Set U) (A : ℕ → U →L[ℝ] V),
      (∀ n, MeasurableSet (p n)) ∧ Pairwise (Disjoint on p) ∧ (⋃ n, p n) = s ∧
      (∀ n, (p n).Nonempty → Injective (A n)) ∧
      ∀ n, ∀ x ∈ p n, ∀ y ∈ p n, ‖f x - f y - A n (x - y)‖ ≤ δ * ‖A n (x - y)‖ := by
  classical
  -- Each injective linear map has a positive antilipschitz constant `c A`; the admissible error
  -- for approximating by `A` is `δ / c A`.
  have hA (A : U →L[ℝ] V) : ∃ c : ℝ≥0, 0 < c ∧ (Injective A → AntilipschitzWith c A) := by
    by_cases h : Injective A
    · obtain ⟨c, hc, hAc⟩ := (A : U →ₗ[ℝ] V).injective_iff_antilipschitz.mp h
      exact ⟨c, hc, fun _ ↦ hAc⟩
    · exact ⟨1, zero_lt_one, fun h' ↦ (h h').elim⟩
  choose c hc hAc using hA
  let r (A : U →L[ℝ] V) : ℝ≥0 := Real.toNNReal δ / c A
  have hr (A : U →L[ℝ] V) : r A ≠ 0 :=
    div_ne_zero (Real.toNNReal_pos.2 hδ).ne' (hc A).ne'
  obtain ⟨t, A, ht, htm, hcover, happ, hder⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hd r hr
  have hinj' (n : ℕ) (hn : (s ∩ t n).Nonempty) : Injective (A n) := by
    obtain ⟨z, hz, hAz⟩ := hder ⟨hn.some, hn.some_mem.1⟩ n
    rw [hAz]
    exact hinj z hz
  refine ⟨fun n ↦ s ∩ t n, A, fun n ↦ hs.inter (htm n),
    fun i j hij ↦ (ht hij).mono inter_subset_right inter_subset_right,
    by simpa only [← inter_iUnion, inter_eq_left] using hcover, hinj', fun n x hx y hy ↦ ?_⟩
  have hxy : ‖x - y‖ ≤ c (A n) * ‖A n (x - y)‖ := by
    simpa using (hAc (A n) (hinj' n ⟨x, hx⟩)).le_mul_dist (x - y) 0
  calc ‖f x - f y - A n (x - y)‖ ≤ r (A n) * ‖x - y‖ := happ n x hx y hy
    _ ≤ r (A n) * (c (A n) * ‖A n (x - y)‖) := by gcongr
    _ = δ * ‖A n (x - y)‖ := by
        have hc0 := (NNReal.coe_pos.2 (hc (A n))).ne'
        simp only [r, NNReal.coe_div, Real.coe_toNNReal _ hδ.le]
        field_simp

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
  -- On pieces within relative error `1 / 2` of a linear map `A n`, `f` is `2 ‖A n‖`-Lipschitz.
  obtain ⟨p, A, hpm, hdisj, hcover, hAinj, happ⟩ :=
    exists_partition_linear_approximation_of_hasFDerivWithinAt hs hd hinj (δ := 2⁻¹)
      (by norm_num)
  choose K hK using fun n ↦
    exists_antilipschitzWith_domRestrict_of_approx (hAinj n) (by norm_num) (happ n)
  refine ⟨p, fun n ↦ 2 * ‖A n‖₊, K, hpm, hdisj, hcover, fun n ↦
    ⟨LipschitzWith.of_dist_le_mul fun x y ↦ ?_, hK n⟩⟩
  simp only [Subtype.dist_eq, domRestrict_apply, dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat,
    coe_nnNorm]
  calc ‖f x - f y‖ ≤ (1 + 2⁻¹) * ‖A n x - A n y‖ :=
        norm_sub_le_one_add_mul_norm_sub (happ n) x.2 y.2
    _ ≤ 2 * ‖A n x - A n y‖ := by linarith [norm_nonneg (A n x - A n y)]
    _ ≤ 2 * (‖A n‖ * ‖(x : U) - y‖) := by rw [← map_sub]; gcongr; exact (A n).le_opNorm _
    _ = 2 * ‖A n‖ * ‖(x : U) - y‖ := by ring

end TauCeti
