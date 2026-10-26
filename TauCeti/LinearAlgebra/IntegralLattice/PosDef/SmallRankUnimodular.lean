/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Hermite
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.UnitNormSplitting

/-!
# Positive definite unimodular lattices of small rank

For a positive definite unimodular lattice `L` of rank `n`, Hermite's inequality
`3 ^ (n choose 2) · (min L)ⁿ ≤ 4 ^ (n choose 2)` bounds the minimum:

* if `1 ≤ n ≤ 5`, then `min L = 1`, since `3 ^ (n choose 2) · 2ⁿ > 4 ^ (n choose 2)`;
* if `n ≤ 8`, then `min L ≤ 2`: in rank zero the minimum is zero, and if `1 ≤ n ≤ 8`, then
  `3 ^ (n choose 2) · 3ⁿ > 4 ^ (n choose 2)`.

Both ranges are the exact ones in which this inequality excludes the next value of the minimum.

Combined with the splitting `L ≅ I_k ⊕ L₀` of the vectors of norm one, the first bound shows
that a positive definite unimodular lattice of rank at most five is the standard lattice `Iₙ`.
Equivalently, a nonzero positive definite unimodular lattice without vectors of norm one has rank
at least six. The second bound shows that such a lattice of rank at most eight has
minimum two, so its vectors of norm two exist; in particular a nonzero even unimodular lattice of
rank at most eight has minimum two. These are the first steps of the classification of positive
definite unimodular lattices of rank at most nine.

## Main declarations

* `TauCeti.IntegralLattice.IsPosDef.minimum_eq_one_of_isUnimodular`: a nonzero lattice of rank
  at most five has minimum one.
* `TauCeti.IntegralLattice.IsPosDef.minimum_le_two_of_isUnimodular`: in rank at most eight the
  minimum is at most two.
* `TauCeti.IntegralLattice.IsPosDef.six_le_finrank_of_vectorsOfNorm_one_eq_empty`: a nonzero
  positive definite unimodular lattice without vectors of norm one has rank at least six.
* `TauCeti.IntegralLattice.IsPosDef.minimum_eq_two_of_vectorsOfNorm_one_eq_empty` and
  `TauCeti.IntegralLattice.IsPosDef.minimum_eq_two_of_isUnimodular_of_isEven`: in rank at most
  eight such a lattice, and in particular a nonzero even unimodular lattice, has minimum two.
* `TauCeti.IntegralLattice.IsPosDef.nonempty_isometry_unitLattice_of_isUnimodular`: a positive
  definite unimodular lattice of rank at most five is `Iₙ`.

## References

* C. Hermite, *Extraits de lettres de M. Ch. Hermite à M. Jacobi sur différents objets de la
  théorie des nombres*, J. Reine Angew. Math. 40 (1850), 261–315.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 16.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

namespace IsPosDef

variable (hL : L.IsPosDef) (hU : L.IsUnimodular)
include hL hU

/-- Hermite's inequality for a unimodular lattice: the minimum lies below every `k` with
`4 ^ (n choose 2) < 3 ^ (n choose 2) · kⁿ`. -/
private theorem minimum_lt_of_four_pow_lt {k : ℕ}
    (hk : 4 ^ (finrank ℤ L).choose 2 < 3 ^ (finrank ℤ L).choose 2 * k ^ finrank ℤ L) :
    L.minimum < k := by
  by_contra! h
  have hH := hL.three_pow_mul_minimum_pow_le
  rw [hL.determinant_eq_one_of_isUnimodular hU, mul_one] at hH
  have hle : (3 : ℤ) ^ (finrank ℤ L).choose 2 * (k : ℤ) ^ finrank ℤ L ≤
      3 ^ (finrank ℤ L).choose 2 * (L.minimum : ℤ) ^ finrank ℤ L := by
    gcongr
  have hk' : ((4 ^ (finrank ℤ L).choose 2 : ℕ) : ℤ) <
      ((3 ^ (finrank ℤ L).choose 2 * k ^ finrank ℤ L : ℕ) : ℤ) := Nat.cast_lt.2 hk
  push_cast at hk'
  omega

/-- **A nonzero positive definite unimodular lattice of rank at most five has minimum one.** -/
theorem minimum_eq_one_of_isUnimodular [Nontrivial L] (hn : finrank ℤ L ≤ 5) :
    L.minimum = 1 := by
  have h1 : 0 < finrank ℤ L := finrank_pos
  have h := hL.minimum_lt_of_four_pow_lt hU (k := 2) <| by
    interval_cases finrank ℤ L <;> norm_num [Nat.choose_two_right]
  have := hL.minimum_pos
  omega

/-- **A positive definite unimodular lattice of rank at most eight has minimum at most two.** -/
theorem minimum_le_two_of_isUnimodular (hn : finrank ℤ L ≤ 8) : L.minimum ≤ 2 := by
  rcases subsingleton_or_nontrivial L with hL0 | hL0
  · rw [minimum_eq_zero_of_subsingleton]
    exact zero_le_two
  have h1 : 0 < finrank ℤ L := finrank_pos
  have h := hL.minimum_lt_of_four_pow_lt hU (k := 3) <| by
    interval_cases finrank ℤ L <;> norm_num [Nat.choose_two_right]
  omega

/-- **A nonzero positive definite unimodular lattice without vectors of norm one has rank at least
six.** -/
theorem six_le_finrank_of_vectorsOfNorm_one_eq_empty [Nontrivial L]
    (h1 : L.vectorsOfNorm 1 = ∅) : 6 ≤ finrank ℤ L := by
  by_contra! hn
  exact hL.isPosSemidef.minimum_ne_of_vectorsOfNorm_eq_empty (n := 1) (by exact_mod_cast h1)
    (hL.minimum_eq_one_of_isUnimodular hU (by omega))

/-- **A nonzero positive definite unimodular lattice of rank at most eight without vectors of norm
one has minimum two.** -/
theorem minimum_eq_two_of_vectorsOfNorm_one_eq_empty [Nontrivial L]
    (h1 : L.vectorsOfNorm 1 = ∅) (hn : finrank ℤ L ≤ 8) : L.minimum = 2 := by
  have hle := hL.minimum_le_two_of_isUnimodular hU hn
  have hpos := hL.minimum_pos
  have hne :=
    hL.isPosSemidef.minimum_ne_of_vectorsOfNorm_eq_empty (n := 1) (by exact_mod_cast h1)
  omega

/-- **A nonzero even positive definite unimodular lattice of rank at most eight has minimum
two.** -/
theorem minimum_eq_two_of_isUnimodular_of_isEven [Nontrivial L] (he : L.IsEven)
    (hn : finrank ℤ L ≤ 8) : L.minimum = 2 :=
  le_antisymm (hL.minimum_le_two_of_isUnimodular hU hn) (hL.two_le_minimum he)

/-- **A positive definite unimodular lattice of rank at most five is the standard lattice
`Iₙ`.** -/
theorem nonempty_isometry_unitLattice_of_isUnimodular (hn : finrank ℤ L ≤ 5) :
    Nonempty (Isometry (unitLattice (Fin (finrank ℤ L))) L) := by
  refine hL.nonempty_isometry_unitLattice_of_unitNormSubmodule_eq_top <|
    (hL.unitNormSubmodule_eq_top_iff).2 ?_
  have hL₀ := hL.isPosDef_unitNormComplement
  have hU₀ := (hL.isUnimodular_unitNormComplement_iff).2 hU
  have hrank := hL.finrank_unitNormSubmodule_add_finrank_unitNormComplement
  by_contra hns
  have : Nontrivial L.unitNormComplement := not_subsingleton_iff_nontrivial.1 hns
  have := hL₀.six_le_finrank_of_vectorsOfNorm_one_eq_empty hU₀
    L.vectorsOfNorm_one_unitNormComplement
  omega

end IsPosDef

end TauCeti.IntegralLattice
