/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Main
public import TauCeti.NumberTheory.LocalField.MassFormula.Quadratic.PadicTwo
import TauCeti.FieldTheory.IntermediateField.Quadratic

/-!
# Checks: the étale mass in degree two over `ℚ_2`

Checks of Bhargava's mass formula for étale algebras in its smallest wildly ramified case,
degree two over `ℚ_2`, where the residue field has `q = 2` elements. Every value is computed from
the explicit quadratic extensions of `ℚ_2`, independently of the general mass formulas.

* The subextensions of degree two of the separable closure of `ℚ_2` are the seven fields
  `ℚ_2(√a)` for `a = -3, -1, -5, 2, -2, 10, -10`: the unramified quadratic extension
  `ℚ_4 = ℚ_2(√-3)`, of residue degree `2`, and the six totally ramified quadratic extensions of
  `TauCeti.totallyRamifiedOfDegree_two_eq_padicTwo`, of residue degree `1`
  (`TauCeti.setOf_finrank_eq_two_padicTwo`, `TauCeti.encard_setOf_finrank_eq_two_padicTwo`).
  Only `ℚ_4` has residue degree `2`.
* Their discriminant weights sum to `1 + 2 · 2⁻² + 4 · 2⁻³ = 2`: `ℚ_4` has `d = 0`, and a
  ramified quadratic field has `d = c + 1`, where the wild exponents `c` are those of
  `TauCeti.tsum_one_div_pow_wildExponent_two_padicTwo`
  (`TauCeti.tsum_finrank_eq_two_one_div_pow_discriminantExponent_padicTwo`).
* Each quadratic field is the stabilizer fixed field of `1! = 1` labelled transitive Galois set,
  so the transitive Galois sets of size two also have total weight `2`.
* A Galois set of size two is transitive or trivial, and the trivial one has weight `1`, so the
  étale mass is `M_2(ℚ_2) = (1 + 2) / 2! = 3 / 2`, the value `1 + q⁻¹` of `TauCeti.etaleMass_two`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Thm. 1.1.
* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3, for the square classes of `ℚ_2`.
-/

public section
noncomputable section

open ValuativeRel IntermediateField
open scoped ENNReal

namespace TauCeti

/-- **The unramified quadratic extension of `ℚ_2`** is `ℚ_4 = ℚ_2(√-3)`. -/
theorem unramifiedExtension_two_padicTwo {x : SeparableClosure ℚ_[2]} (hx : x ^ 2 = -3) :
    unramifiedExtension ℚ_[2] (SeparableClosure ℚ_[2]) 2 = ℚ_[2]⟮x⟯ := by
  have hx' : x ^ 2 = algebraMap ℚ_[2] (SeparableClosure ℚ_[2]) (-3) := by
    rw [hx, map_neg, map_ofNat]
  -- The residue characteristic `2` does not divide `3`.
  have h3 : ¬ ringChar 𝓀[ℚ_[2]] ∣ 3 := IsLocalRing.isUnit_natCast_iff_not_dvd.1 <| by
    exact_mod_cast Padic.isUnit_intCast_integerRing (p := 2) (m := 3) (by norm_num)
  have hle : ℚ_[2]⟮x⟯ ≤ maximalUnramifiedExtension ℚ_[2] (SeparableClosure ℚ_[2]) :=
    adjoin_simple_le_iff.2 (mem_maximalUnramifiedExtension_of_sq_eq_neg_three h3 hx)
  have hmem : ℚ_[2]⟮x⟯ ∈
      {L : IntermediateField ℚ_[2] (SeparableClosure ℚ_[2]) | Module.finrank ℚ_[2] L = 2} :=
    IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare hx'
      Padic.not_isSquare_neg_three_padicTwo
  rw [setOf_finrank_eq_of_prime Nat.prime_two] at hmem
  refine hmem.elim Eq.symm fun h ↦ ?_
  have := eq_one_of_mem_totallyRamifiedOfDegree_of_le_maximalUnramifiedExtension h hle
  omega

/-- **The quadratic extensions of `ℚ_2`.** If `x₀, …, x₆` are square roots of
`-3, -1, -5, 2, -2, 10, -10` in the separable closure of `ℚ_2`, then its subextensions of degree
two are `ℚ_2(x₀), …, ℚ_2(x₆)`: the unramified `ℚ_4 = ℚ_2(x₀)` and the six totally ramified
quadratic extensions. -/
theorem setOf_finrank_eq_two_padicTwo {x₀ x₁ x₂ x₃ x₄ x₅ x₆ : SeparableClosure ℚ_[2]}
    (h₀ : x₀ ^ 2 = -3) (h₁ : x₁ ^ 2 = -1) (h₂ : x₂ ^ 2 = -5) (h₃ : x₃ ^ 2 = 2) (h₄ : x₄ ^ 2 = -2)
    (h₅ : x₅ ^ 2 = 10) (h₆ : x₆ ^ 2 = -10) :
    {L : IntermediateField ℚ_[2] (SeparableClosure ℚ_[2]) | Module.finrank ℚ_[2] L = 2} =
      {ℚ_[2]⟮x₀⟯, ℚ_[2]⟮x₁⟯, ℚ_[2]⟮x₂⟯, ℚ_[2]⟮x₃⟯, ℚ_[2]⟮x₄⟯, ℚ_[2]⟮x₅⟯, ℚ_[2]⟮x₆⟯} := by
  rw [setOf_finrank_eq_of_prime Nat.prime_two, unramifiedExtension_two_padicTwo h₀,
    totallyRamifiedOfDegree_two_eq_padicTwo h₁ h₂ h₃ h₄ h₅ h₆]

/-- `ℚ_2` has exactly seven quadratic subextensions: `ℚ_4` and six totally ramified ones. -/
theorem encard_setOf_finrank_eq_two_padicTwo :
    {L : IntermediateField ℚ_[2] (SeparableClosure ℚ_[2]) |
      Module.finrank ℚ_[2] L = 2}.encard = 7 := by
  rw [setOf_finrank_eq_of_prime Nat.prime_two,
    Set.encard_insert_of_notMem (unramifiedExtension_notMem_totallyRamifiedOfDegree one_lt_two),
    encard_totallyRamifiedOfDegree_two_padicTwo]
  rfl

/-- The residue degrees split the quadratic extensions of `ℚ_2`: `ℚ_4` alone has residue
degree `2`. -/
example : {L : IntermediateField ℚ_[2] (SeparableClosure ℚ_[2]) |
    Module.finrank ℚ_[2] L = 2 ∧ L.inertiaDegree = 2} =
      {unramifiedExtension ℚ_[2] (SeparableClosure ℚ_[2]) 2} := by
  ext L
  refine ⟨fun ⟨hL, hf⟩ ↦ ?_, ?_⟩
  · have : Module.Finite ℚ_[2] L := Module.finite_of_finrank_pos (by omega)
    have h := L.inertiaDegree_eq_finrank_iff.1 (hf.trans hL.symm)
    rwa [hL] at h
  · rintro rfl
    exact ⟨finrank_unramifiedExtension two_ne_zero, inertiaDegree_unramifiedExtension two_ne_zero⟩

/-- **The transitive mass in degree two over `ℚ_2`**, from the fields:
`∑_{[L : ℚ_2] = 2} 2 ^ (-d(L)) = 1 + 2 · 2⁻² + 4 · 2⁻³ = 2`. -/
theorem tsum_finrank_eq_two_one_div_pow_discriminantExponent_padicTwo :
    ∑' L : {L : IntermediateField ℚ_[2] (SeparableClosure ℚ_[2]) // Module.finrank ℚ_[2] L = 2},
      1 / (2 : ℝ≥0∞) ^ L.val.discriminantExponent = 2 := by
  -- The ramified fields have `d = c + 1`, so their weights are half their wild weights.
  have hram : ∑' L : totallyRamifiedOfDegree ℚ_[2] 2, 1 / (2 : ℝ≥0∞) ^ L.val.discriminantExponent =
      2⁻¹ * ∑' L : totallyRamifiedOfDegree ℚ_[2] 2, 1 / (2 : ℝ≥0∞) ^ L.val.wildExponent := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun L ↦ ?_
    have h := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one L.property
    rw [show L.val.discriminantExponent = L.val.wildExponent + 1 by omega, pow_succ,
      one_div, one_div, ENNReal.mul_inv (by simp) (by simp), mul_comm]
  -- Read the subtype as the coercion of a set, so that the set can be rewritten.
  change ∑' L : ({L | Module.finrank ℚ_[2] L = 2} :
    Set (IntermediateField ℚ_[2] (SeparableClosure ℚ_[2]))),
      1 / (2 : ℝ≥0∞) ^ (L : IntermediateField ℚ_[2] (SeparableClosure ℚ_[2])).discriminantExponent
    = 2
  rw [setOf_finrank_eq_of_prime Nat.prime_two,
    tsum_insert (f := fun L : IntermediateField ℚ_[2] (SeparableClosure ℚ_[2]) ↦
      1 / (2 : ℝ≥0∞) ^ L.discriminantExponent)
      (unramifiedExtension_notMem_totallyRamifiedOfDegree one_lt_two),
    discriminantExponent_unramifiedExtension, hram, tsum_one_div_pow_wildExponent_two_padicTwo,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  norm_num

/-- The transitive Galois sets of size two over `ℚ_2` carry total weight `1! · 2 = 2`. -/
theorem tsum_isTransitive_two_one_div_pow_discriminantExponent_padicTwo :
    ∑' ρ : {ρ : GaloisSet ℚ_[2] 2 // ρ.IsTransitive},
      1 / (2 : ℝ≥0∞) ^ ρ.val.discriminantExponent = 2 := by
  have h := tsum_isTransitive_one_div_natCard_residueField_pow_discriminantExponent
    (K := ℚ_[2]) two_pos
  rw [Padic.natCard_residueField, Nat.cast_ofNat] at h
  rw [h, tsum_finrank_eq_two_one_div_pow_discriminantExponent_padicTwo]
  simp

/-- **Bhargava's mass formula in degree two over `ℚ_2`**, from the fields: the trivial Galois set
has weight `1` and the transitive ones weight `2`, so `M_2(ℚ_2) = (1 + 2) / 2! = 3 / 2`. -/
theorem etaleMass_two_padicTwo : etaleMass ℚ_[2] 2 = 3 / 2 := by
  have hcompl : {ρ : GaloisSet ℚ_[2] 2 | ρ.IsTransitive}ᶜ = {GaloisSet.trivial ℚ_[2] 2} := by
    ext ρ
    refine ⟨fun h ↦ (ρ.isTransitive_or_eq_trivial).resolve_left h, ?_⟩
    rintro rfl h
    obtain ⟨σ, hσ⟩ := ((GaloisSet.trivial ℚ_[2] 2).isTransitive_iff).1 h 0 1
    simp at hσ
  rw [etaleMass_def, Padic.natCard_residueField, Nat.cast_ofNat,
    ← CompleteLattice.summable.tsum_add_tsum_compl
      (s := {ρ : GaloisSet ℚ_[2] 2 | ρ.IsTransitive}) CompleteLattice.summable, hcompl,
    tsum_singleton (GaloisSet.trivial ℚ_[2] 2)
      fun ρ ↦ 1 / (2 : ℝ≥0∞) ^ ρ.discriminantExponent, GaloisSet.discriminantExponent_trivial]
  -- Read the coercion of the set of transitive Galois sets back as a subtype.
  change (Nat.factorial 2 : ℝ≥0∞)⁻¹ * (∑' ρ : {ρ : GaloisSet ℚ_[2] 2 // ρ.IsTransitive},
    1 / (2 : ℝ≥0∞) ^ ρ.val.discriminantExponent + _) = _
  rw [tsum_isTransitive_two_one_div_pow_discriminantExponent_padicTwo]
  norm_num
  exact ENNReal.div_eq_inv_mul.symm

/-- The independent value agrees with Bhargava's formula `M_2(K) = 1 + q⁻¹` at `q = 2`. -/
example : etaleMass ℚ_[2] 2 = 1 + 1 / (Nat.card 𝓀[ℚ_[2]] : ℝ≥0∞) := by
  rw [etaleMass_two_padicTwo, Padic.natCard_residueField,
    ← ENNReal.toReal_eq_toReal_iff' (ENNReal.div_ne_top (by simp) two_ne_zero) (by simp)]
  norm_num [ENNReal.toReal_add]

end TauCeti
