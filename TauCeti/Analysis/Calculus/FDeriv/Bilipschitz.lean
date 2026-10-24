/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Bi-Lipschitz pieces of differentiable maps

A map with an injective derivative at each point of a set admits a countable partition into
relatively Borel pieces on which it is bi-Lipschitz. The set itself need not be measurable,
and derivatives within that set suffice. In particular, this applies to the regular part of
a Lipschitz parametrization when constructing inverse charts for rectifiable sets.

The proof uses Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`: choose the approximation error
smaller than the lower bound of the approximating injective linear map.

## References

* H. Federer, *Geometric Measure Theory*, §3.2 (decomposition of parametrizations).
-/

public section

open Set MeasureTheory
open scoped NNReal Function

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [SecondCountableTopology F] {f : E → F} {s : Set E} {f' : E → E →L[ℝ] F}

/-- A map whose derivatives within `s` are injective is bi-Lipschitz on countably many
relatively Borel pieces partitioning `s`. No measurability of `s` is required. -/
theorem exists_partition_bilipschitz_of_hasFDerivWithinAt
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hi : ∀ x ∈ s, Function.Injective (f' x)) :
    ∃ t : ℕ → Set E, Pairwise (Disjoint on t) ∧ (∀ n, MeasurableSet (t n)) ∧
      s ⊆ ⋃ n, t n ∧ ∀ n, ∃ K L : ℝ≥0,
        LipschitzWith K ((s ∩ t n).domRestrict f) ∧
        AntilipschitzWith L ((s ∩ t n).domRestrict f) := by
  classical
  -- Choose positive lower bounds even for maps not used in the partition.
  have hK (A : E →L[ℝ] F) : ∃ K : ℝ≥0, 0 < K ∧
      (Function.Injective A → AntilipschitzWith K A) := by
    by_cases hA : Function.Injective A
    · obtain ⟨K, hK, hanti⟩ := (A : E →ₗ[ℝ] F).exists_antilipschitzWith
        (LinearMap.ker_eq_bot.mpr hA)
      exact ⟨K, hK, fun _ ↦ hanti⟩
    · exact ⟨1, zero_lt_one, fun h ↦ (hA h).elim⟩
  choose K hKpos hKanti using hK
  let r : (E →L[ℝ] F) → ℝ≥0 := fun A ↦ (K A)⁻¹ / 2
  have hr (A : E →L[ℝ] F) : 0 < r A := by
    exact div_pos (inv_pos.mpr (hKpos A)) (by norm_num)
  obtain ⟨t, A, hdisj, hmeas, hcover, happ, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hd r
      (fun A ↦ (hr A).ne')
  refine ⟨t, hdisj, hmeas, hcover, fun n ↦ ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, 0, by simp [LipschitzWith], by simp [AntilipschitzWith]⟩
  obtain ⟨x, hx, hAx⟩ := hA hs n
  have hanti : AntilipschitzWith (K (A n)) (A n) :=
    hKanti _ (hAx ▸ hi x hx)
  have hsmall : r (A n) < (K (A n))⁻¹ := by
    exact half_lt_self (inv_pos.mpr (hKpos _))
  refine ⟨‖A n‖₊ + r (A n), ((K (A n))⁻¹ - r (A n))⁻¹,
    (happ n).lipschitzWith, ?_⟩
  convert (hanti.domRestrict (s ∩ t n)).add_lipschitzWith
    (happ n).lipschitzWith_sub hsmall using 1
  ext x
  simp

end TauCeti
