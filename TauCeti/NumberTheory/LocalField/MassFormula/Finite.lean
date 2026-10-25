/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.NumberTheory.LocalField.Different.Wild

/-!
# Finiteness of the totally ramified extensions of given degree

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, and let
`0 < n`. Serre's mass formula `∑_{L ∈ σ_K(n)} q ^ (-c(L)) = n` decides whether the family
`σ_K(n) = totallyRamifiedOfDegree K n` is finite. Outside the case where `K` has characteristic
`p > 0` and `p ∣ n`, that is when `(n : K) ≠ 0`, the wild exponents of the members of `σ_K(n)`
are bounded: by the upper bound of Dedekind's different theorem, `d(L) ≤ n - 1 + v_L(n)`, and
`v_L(n) = n · v_K(n)` since `L / K` is totally ramified of degree `n`, so
`c(L) ≤ n · v_K(n)`. Every weight `q ^ (-c(L))` is then at least `q ^ (-n · v_K(n))`, and the
weighted sum is finite exactly when `σ_K(n)` is finite. In the tame case, when the residue
characteristic does not divide `n`, every weight is `1` and the weighted sum is the cardinality
of `σ_K(n)`.

Together with the mass formula, these give the forward half of Serre's finiteness dichotomy and
the tame count `#σ_K(n) = n`. The converse half, that `σ_K(n)` is infinite when `(n : K) = 0`,
is `TauCeti.infinite_totallyRamifiedOfDegree`.

## Main results

* `IntermediateField.discriminantExponent_le_sub_one_add_mul_natCastValuation`: for
  `L ∈ σ_K(n)` and `(n : K) ≠ 0`, `d(L) ≤ n - 1 + n · v_K(n)`.
* `IntermediateField.wildExponent_le_mul_natCastValuation`: for `L ∈ σ_K(n)` and `(n : K) ≠ 0`,
  `c(L) ≤ n · v_K(n)`.
* `TauCeti.tsum_one_div_natCard_residueField_pow_wildExponent_ne_top_iff_finite`: for
  `(n : K) ≠ 0`, `∑_{L ∈ σ_K(n)} q ^ (-c(L))` is finite exactly when `σ_K(n)` is finite.
* `TauCeti.tsum_one_div_natCard_residueField_pow_wildExponent_eq_encard`: if the residue
  characteristic does not divide `n`, `∑_{L ∈ σ_K(n)} q ^ (-c(L))` is the cardinality of
  `σ_K(n)`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Remarque 1°.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 13.
-/

public section

open ValuativeRel

open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The discriminant bound for `σ_K(n)` away from equal characteristic `p ∣ n`**: if `n` is
nonzero in `K`, the discriminant exponent of `L ∈ σ_K(n)` is at most `n - 1 + n · v_K(n)`. Since
`L / K` is totally ramified, `d(L)` is the different exponent, so this is
`differentExponent_le_ramificationIndex_sub_one_add_natCastValuation` with `e(L / K) = n`, together
with `v_L(n) = n · v_K(n)`. -/
theorem _root_.IntermediateField.discriminantExponent_le_sub_one_add_mul_natCastValuation
    {n : ℕ} {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ totallyRamifiedOfDegree K n) (hnK : (n : K) ≠ 0) :
    L.discriminantExponent ≤ n - 1 + n * natCastValuation K n hnK := by
  obtain ⟨hn, htr⟩ := mem_totallyRamifiedOfDegree_iff.1 hL
  have := htr.finite
  rw [IntermediateField.isTotallyRamified_iff] at htr
  rw [IntermediateField.discriminantExponent_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent, htr.inertiaDegree_eq_one,
    one_mul]
  have hre : ramificationIndex K L = n :=
    ((isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 htr).trans hn
  -- The upper bound at `e(L / K) = n`, then `v_L(n) = n · v_K(n)`.
  have h : ∀ he : (ramificationIndex K L : L) ≠ 0, differentExponent K L ≤
      ramificationIndex K L - 1 + natCastValuation L (ramificationIndex K L) he :=
    differentExponent_le_ramificationIndex_sub_one_add_natCastValuation
  rw [hre] at h
  refine (h ?_).trans_eq ?_
  · simpa using (map_ne_zero (algebraMap K L)).2 hnK
  · rw [natCastValuation_eq_ramificationIndex_mul n hnK, hre]

/-- **The wild exponent is bounded on `σ_K(n)` away from equal characteristic `p ∣ n`**: if `n`
is nonzero in `K`, every `L ∈ σ_K(n)` has `c(L) ≤ n · v_K(n)`. In equal characteristic, where
`v_K(n) = 0`, this recovers `c(L) = 0` for `p ∤ n`. -/
theorem _root_.IntermediateField.wildExponent_le_mul_natCastValuation {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (hnK : (n : K) ≠ 0) :
    L.wildExponent ≤ n * natCastValuation K n hnK := by
  have := IntermediateField.discriminantExponent_le_sub_one_add_mul_natCastValuation hL hnK
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hL
  rw [IntermediateField.wildExponent_def, (mem_totallyRamifiedOfDegree_iff.1 hL).1]
  omega

/-- **Finiteness of `σ_K(n)` away from equal characteristic `p ∣ n`**: if `n` is nonzero in `K`,
the weighted count `∑_{L ∈ σ_K(n)} q ^ (-c(L))` of Serre's mass formula is finite exactly when
`σ_K(n)` is finite. With the mass formula, this makes `σ_K(n)` finite. -/
theorem tsum_one_div_natCard_residueField_pow_wildExponent_ne_top_iff_finite {n : ℕ}
    (hnK : (n : K) ≠ 0) :
    ∑' L : totallyRamifiedOfDegree K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent ≠ ∞ ↔
      (totallyRamifiedOfDegree K n).Finite := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- Every weight is at least `q ^ (-n · v_K(n))`, which is nonzero.
    have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n * natCastValuation K n hnK) ≠ ∞ :=
      ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    have hfin := ENNReal.finite_const_le_of_tsum_ne_top h (ENNReal.div_pos one_ne_zero hq).ne'
    refine Set.finite_coe_iff.1 (Set.finite_univ_iff.1 (hfin.subset fun L _ ↦ ?_))
    exact ENNReal.div_le_div_left (pow_le_pow_right₀ (Nat.one_le_cast.2 Nat.card_pos)
      (IntermediateField.wildExponent_le_mul_natCastValuation L.2 hnK)) 1
  · -- Every weight is at most `1`.
    refine ne_top_of_le_ne_top (b := ∑' _ : totallyRamifiedOfDegree K n, (1 : ℝ≥0∞)) ?_
      (ENNReal.tsum_le_tsum fun L ↦ ?_)
    · rw [ENNReal.tsum_set_one, Ne, ENat.toENNReal_eq_top]
      exact h.encard_lt_top.ne
    · rw [one_div]
      exact ENNReal.inv_le_one.2 (one_le_pow₀ (Nat.one_le_cast.2 Nat.card_pos))

/-- **The tame count, weighted form**: if the residue characteristic of `K` does not divide `n`,
every member of `σ_K(n)` has weight `q ^ (-c(L)) = 1`, so the weighted count
`∑_{L ∈ σ_K(n)} q ^ (-c(L))` of Serre's mass formula is the cardinality of `σ_K(n)`. With the mass
formula, `σ_K(n)` has exactly `n` elements. -/
theorem tsum_one_div_natCard_residueField_pow_wildExponent_eq_encard {n : ℕ}
    (hn : ¬ ringChar 𝓀[K] ∣ n) :
    ∑' L : totallyRamifiedOfDegree K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent =
      (totallyRamifiedOfDegree K n).encard := by
  rw [← ENNReal.tsum_set_one]
  refine tsum_congr fun L ↦ ?_
  rw [(IntermediateField.wildExponent_eq_zero_iff L.2).2 hn, pow_zero, div_one]

end TauCeti
