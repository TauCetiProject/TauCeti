/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Quartic.Examples
public import TauCeti.FieldTheory.GaloisGroups.Reduction

/-!
# The eighth cyclotomic polynomial modulo primes

The Galois group of `X⁴ + 1` has label `4T2`: it is the Klein four-group, acting on the four
roots by even permutations. An irreducible reduction modulo a prime would give a four-cycle in
this action, which is odd. Thus `X⁴ + 1` is reducible modulo every prime, even though it is
irreducible over `ℚ`.
-/

public section

open Polynomial Equiv.Perm

namespace TauCeti

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

local instance quarticFactSplitsSplittingField (f : ℚ[X]) :
    Fact ((f.map (algebraMap ℚ f.SplittingField)).Splits) :=
  ⟨SplittingField.splits f⟩

/-- The eighth cyclotomic polynomial `X⁴ + 1` becomes reducible modulo every prime. Its
Galois action over `ℚ` has label `4T2`, so every induced permutation is even, whereas an
irreducible reduction would exhibit an odd four-cycle. -/
@[simp]
theorem not_irreducible_X_pow_four_add_one (p : ℕ) [Fact p.Prime] :
    ¬ Irreducible (X ^ 4 + 1 : (ZMod p)[X]) := by
  classical
  have hA₀ :=
    (hasGaloisLabel_X_pow_four_add_one.range_le_alternatingGroup_iff).mpr
      referenceSubgroup_four_one_le_alternatingGroup
  have hmap : (X ^ 4 + 1 : ℤ[X]).map (Int.castRingHom ℚ) =
      (X ^ 4 + 1 : ℚ[X]) := by simp
  have hA :
      (Polynomial.Gal.galActionHom
        ((X ^ 4 + 1 : ℤ[X]).map (Int.castRingHom ℚ)) ℂ).range ≤
        alternatingGroup (((X ^ 4 + 1 : ℤ[X]).map (Int.castRingHom ℚ)).rootSet ℂ) := by
    rw [hmap]
    intro σ hσ
    obtain ⟨g, rfl⟩ := hσ
    rw [Polynomial.Gal.galActionHom_eq_permCongr
      (E := (X ^ 4 + 1 : ℚ[X]).SplittingField) (X ^ 4 + 1 : ℚ[X]) ℂ g]
    rw [mem_alternatingGroup, Equiv.Perm.sign_permCongr]
    exact mem_alternatingGroup.mp (hA₀ ⟨g, rfl⟩)
  have hdeg : (X ^ 4 + 1 : ℤ[X]).natDegree = 4 := by compute_degree!
  have h := not_irreducible_map_of_even_natDegree_of_range_le_alternatingGroup
    (f := X ^ 4 + 1) (by monicity!) (by rw [hdeg]; decide)
    (by rw [hdeg]; decide) hA p
  simpa only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    using h

end TauCeti
