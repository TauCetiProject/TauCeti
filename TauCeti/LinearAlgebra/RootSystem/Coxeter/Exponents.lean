/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Number

/-!
# Fundamental degrees and additional exponent identities of Dynkin types

Supplements `TauCeti.LinearAlgebra.RootSystem.Coxeter.Number` with the fundamental invariant
degrees `TauCeti.DynkinType.degrees` (`dᵢ = mᵢ + 1`) and the remaining exponent/degree identities
(`sum_exponents`, `sum_degrees`, `coxeterNumber_sub_one_mem_exponents`,
`two_le_of_mem_degrees`, `le_coxeterNumber_of_mem_degrees`, `two_mem_degrees`,
`coxeterNumber_mem_degrees`).

## Main definitions & results

* `TauCeti.DynkinType.degrees`, `degrees_def`, `mem_degrees_iff`, `length_degrees`,
  `sum_exponents`, `sum_degrees`, `coxeterNumber_sub_one_mem_exponents`,
  `two_le_of_mem_degrees`, `le_coxeterNumber_of_mem_degrees`, `two_mem_degrees`,
  `coxeterNumber_mem_degrees`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §§ 3.7, 3.16–3.20.
-/

public section

namespace TauCeti.DynkinType

/-- The exponents of `E₈` are the residues modulo `30` coprime to `30`. -/
theorem exponents_E8_eq_filter : E8.exponents = (List.range 30).filter (Nat.Coprime · 30) :=
  exponents_E8.trans Coxeter.e8Exponents_eq_filter

/-- The exponents of `F₄` are the residues modulo `12` coprime to `12`. -/
theorem exponents_F4_eq_filter : F4.exponents = (List.range 12).filter (Nat.Coprime · 12) :=
  exponents_F4.trans Coxeter.f4Exponents_eq_filter

/-- The exponents of `G₂` are the residues modulo `6` coprime to `6`. -/
theorem exponents_G2_eq_filter : G2.exponents = (List.range 6).filter (Nat.Coprime · 6) :=
  exponents_G2.trans Coxeter.g2Exponents_eq_filter

/-- The **fundamental invariant degrees** `dᵢ = mᵢ + 1` of a Dynkin type. -/
def degrees (t : DynkinType) : List ℕ :=
  t.exponents.map (· + 1)

/-- Unfolded characterization of `TauCeti.DynkinType.degrees` as `t.exponents.map (· + 1)`. -/
lemma degrees_def (t : DynkinType) : t.degrees = t.exponents.map (· + 1) := (rfl)

/-- Membership in `t.degrees` in terms of `t.exponents`. -/
@[simp] lemma mem_degrees_iff {t : DynkinType} {d : ℕ} :
    d ∈ t.degrees ↔ ∃ e ∈ t.exponents, e + 1 = d := by
  rw [degrees_def, List.mem_map]

@[simp] lemma length_degrees (t : DynkinType) : t.degrees.length = t.rank := by
  simp [degrees_def]

/-- The sum of the exponents of any Dynkin type is half its number of roots (`|Φ| / 2`, equal to
`|Φ⁺|` for valid types). -/
@[simp] theorem sum_exponents (t : DynkinType) : t.exponents.sum = t.numRoots / 2 := by
  rw [← t.two_mul_sum_exponents_eq_numRoots, Nat.mul_div_right _ (by norm_num)]

/-- The sum of the fundamental degrees of any Dynkin type is `|Φ| / 2 + r` (`|Φ⁺| + r` for valid
types). -/
@[simp] theorem sum_degrees (t : DynkinType) : t.degrees.sum = t.numRoots / 2 + t.rank := by
  simp [degrees_def, List.sum_map_add]

/-- `h - 1` is always an exponent of a valid Dynkin type. -/
@[simp high] lemma coxeterNumber_sub_one_mem_exponents {t : DynkinType} (ht : t.Valid) :
    t.coxeterNumber - 1 ∈ t.exponents := by
  have h2 := two_le_coxeterNumber ht
  refine mem_exponents_of_coprime ht (by omega) ?_
  have hcop : (t.coxeterNumber - 1).Coprime (t.coxeterNumber - 1 + 1) := by simp
  rwa [Nat.sub_add_cancel (by omega)] at hcop

/-- Every fundamental degree of a valid Dynkin type is at least `2`. -/
lemma two_le_of_mem_degrees {t : DynkinType} (ht : t.Valid) {d : ℕ} (hd : d ∈ t.degrees) :
    2 ≤ d := by
  obtain ⟨e, he, rfl⟩ := mem_degrees_iff.mp hd
  have := pos_of_mem_exponents ht he
  omega

/-- Every fundamental degree of a valid Dynkin type is at most its Coxeter number. -/
lemma le_coxeterNumber_of_mem_degrees {t : DynkinType} (ht : t.Valid) {d : ℕ}
    (hd : d ∈ t.degrees) : d ≤ t.coxeterNumber := by
  obtain ⟨e, he, rfl⟩ := mem_degrees_iff.mp hd
  exact lt_coxeterNumber_of_mem_exponents ht he

/-- `2` is always a fundamental degree of a valid Dynkin type (corresponding to the invariant
quadratic form). -/
@[simp high] lemma two_mem_degrees {t : DynkinType} (ht : t.Valid) : 2 ∈ t.degrees :=
  mem_degrees_iff.mpr ⟨1, one_mem_exponents ht, rfl⟩

/-- The Coxeter number `h` is always a fundamental degree of a valid Dynkin type. -/
@[simp high] lemma coxeterNumber_mem_degrees {t : DynkinType} (ht : t.Valid) :
    t.coxeterNumber ∈ t.degrees := by
  have h2 := two_le_coxeterNumber ht
  exact mem_degrees_iff.mpr ⟨t.coxeterNumber - 1, coxeterNumber_sub_one_mem_exponents ht, by omega⟩

end TauCeti.DynkinType
