/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Symmetric.Basic
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import TauCeti.Algebra.Polynomial.ChineseRemainder
import TauCeti.FieldTheory.Finite.FactorizationPattern
import TauCeti.FieldTheory.GaloisGroups.Reduction

/-!
# Symmetric groups as Galois groups over the rationals

For every positive degree `n`, there is a monic integral polynomial of degree `n`, irreducible
over `ℚ`, with full symmetric Galois group. For `n ≥ 2`, choose an irreducible reduction
modulo `2`, factor degrees `(1, n - 1)` modulo `3`, and exactly one quadratic factor with
all other degrees odd modulo `5`. The coefficientwise Chinese remainder theorem produces
one polynomial with all three reductions. The reduction criterion then gives every
permutation of its roots. Degree one is witnessed by `X`.

The construction uses the finite-field factorization patterns and monic Chinese remainder
lifting already provided by Tau Ceti, and the criterion
`TauCeti.surjective_galActionHom_of_factorDegrees`.

## References

* B. L. van der Waerden, *Algebra* I, §61.
* J.-P. Serre, *Topics in Galois Theory*, second edition, §4.4.
-/

public section

open Polynomial TauCeti.Polynomial

namespace TauCeti

attribute [local instance] Gal.splits_ℚ_ℂ

/-- Every positive degree occurs for a monic integral polynomial irreducible over `ℚ`
with full symmetric Galois group. -/
theorem exists_monic_int_polynomial_hasFullSymmetricGaloisGroup (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : ℤ[X], f.Monic ∧ f.natDegree = n ∧
      Irreducible (f.map (Int.castRingHom ℚ)) ∧
      HasFullSymmetricGaloisGroup (f.map (Int.castRingHom ℚ)) := by
  obtain rfl | hn := hn.eq_or_lt
  · refine ⟨X, monic_X, natDegree_X, by simpa using (irreducible_X (R := ℚ)), ?_⟩
    rw [map_X, hasFullSymmetricGaloisGroup_iff_natCard_gal_eq_factorial_natDegree separable_X]
    -- Since X splits over ℚ, Mathlib's `uniqueGalX` makes its Galois group a singleton.
    simpa only [natDegree_X, Nat.factorial_one] using
      (Nat.card_unique (α := (X : ℚ[X]).Gal))
  · have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨g2, hm2, hi2, hd2⟩ := exists_monic_irreducible_natDegree_eq (ZMod 2) n (by omega)
    obtain ⟨g3, hm3, hd3, -, ht3⟩ :=
      exists_monic_squarefree_map_natDegree_normalizedFactors_eq_pair_one_sub_one
        (ZMod 3) n (by omega)
    obtain ⟨g5, hm5, hd5, hs5, ht5, ho5⟩ :=
      exists_monic_squarefree_count_two_map_natDegree_normalizedFactors_eq_one_and_odd
        (ZMod 5) n (by omega)
    obtain ⟨f, hf, hd, he2, he3, he5⟩ :=
      exists_monic_int_polynomial_map_two_three_five_eq n g2 g3 g5
        hm2 hm3 hm5 hd2 hd3 hd5
    have hi : Irreducible (f.map (Int.castRingHom ℚ)) :=
      (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hf.isPrimitive).mp
        (Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) _ hf
          (he2.symm ▸ hi2))
    refine ⟨f, hf, hd, hi, (hasFullSymmetricGaloisGroup_iff_of_splits ℂ).mpr
      ⟨PerfectField.separable_of_irreducible hi,
        surjective_galActionHom_of_factorDegrees hf hi 3 ?_ 5 ?_ ?_ ?_⟩⟩
    · simpa only [factorDegrees_def, he3, hd] using ht3
    · apply (hf.separable_map_zmod_iff_not_dvd_discr 5).mp
      rw [he5, PerfectField.separable_iff_squarefree]
      exact hs5
    · simpa only [factorDegrees_def, he5] using ht5
    · simpa only [factorDegrees_def, he5] using ho5

end TauCeti
