/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Classification
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Residue classification of cyclic dyadic quadratic modules

The coefficient of a nondegenerate cyclic dyadic quadratic module is determined modulo four
at order two and modulo eight at every higher order. Conversely, these congruences suffice
for isometry. Thus there are two cyclic classes of order two, represented by coefficients
`1, 3`, and four of order `2^k` for `k ≥ 2`, represented by `1, 3, 5, 7`.

The uniqueness assertions concern the isometry class, not the isometry itself. They give
canonical choices for the cyclic constituents in orthogonal decompositions. The modulus
four exception is essential: coefficients `1` and `5` agree at order two but not at order four.

The proofs use the unit-square criterion `nonempty_isometry_dyadicCyclic_iff` and the
square-root construction `dyadicCyclicIsometryOfModEqEight`. Necessity follows because
an odd integer has square congruent to one modulo eight.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2, including the small-exponent relation (i) and transfer clause (k).
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

-- These residue criteria are not simp lemmas: the existing general unit-square criterion
-- already simplifies their left-hand sides. Use them explicitly to select the residue form.
/-- At order two, cyclic dyadic quadratic modules are isometric exactly when their
coefficients agree modulo four. This also holds for even coefficients. -/
theorem nonempty_isometry_dyadicCyclic_one_iff (θ η : ℤ) :
    Nonempty (Isometry (dyadicCyclic 1 θ) (dyadicCyclic 1 η)) ↔ θ ≡ η [ZMOD 4] := by
  rw [nonempty_isometry_dyadicCyclic_iff]
  constructor
  · rintro ⟨u, hu⟩
    have hu1 : ∀ v : (ZMod 2)ˣ, v = 1 := by decide
    obtain rfl := hu1 u
    rw [show (1 : (ZMod (2 ^ 1))ˣ).val.val = 1 by decide] at hu
    simpa using (ZMod.intCast_eq_intCast_iff _ _ 4).mp hu
  · intro h
    refine ⟨1, ?_⟩
    rw [show (1 : (ZMod (2 ^ 1))ˣ).val.val = 1 by decide]
    simpa using (ZMod.intCast_eq_intCast_iff _ _ 4).mpr h

/-- At order at least four, nondegenerate cyclic dyadic quadratic modules are isometric
exactly when their coefficients agree modulo eight. Only the source coefficient needs to
be assumed odd; the congruence forces the target coefficient to be odd as well. -/
theorem nonempty_isometry_dyadicCyclic_iff_modEq_eight {k : ℕ} [NeZero k]
    (hk : 2 ≤ k) {θ η : ℤ} (hθ : Odd θ) :
    Nonempty (Isometry (dyadicCyclic k θ) (dyadicCyclic k η)) ↔ θ ≡ η [ZMOD 8] := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (nonempty_isometry_dyadicCyclic_iff θ η).mp h
    have hodd : Odd (u.val.val : ℤ) := by
      have hc := ZMod.val_coe_unit_coprime u
      have ho := Nat.coprime_two_right.mp
        ((Nat.coprime_pow_right_iff (by omega : 0 < k) _ _).mp hc)
      exact_mod_cast ho
    have hs : (u.val.val : ℤ) ^ 2 ≡ 1 [ZMOD 8] := by
      apply Int.modEq_iff_dvd.mpr
      simpa only [neg_sub] using dvd_neg.mpr (Int.eight_dvd_sq_sub_one_of_odd hodd)
    have hm := (ZMod.intCast_eq_intCast_iff _ _ (2 ^ (k + 1))).mp hu
    have hd : (8 : ℤ) ∣ (2 ^ (k + 1) : ℕ) := by
      exact_mod_cast (pow_dvd_pow 2 (by omega : 3 ≤ k + 1))
    simpa only [mul_one] using (hm.of_dvd hd).trans (hs.mul_left η)
  · exact fun h ↦ ⟨dyadicCyclicIsometryOfModEqEight k hθ h⟩

/-- Every nondegenerate cyclic quadratic module of order two has exactly one of the
coefficient representatives `1, 3`. The unique index selects the coefficient `2i + 1`. -/
theorem existsUnique_dyadicCyclic_one_isometry (A : FiniteQuadraticModule) [IsAddCyclic A]
    (hcard : Nat.card A = 2) (hA : A.IsNondegenerate) :
    ∃! i : Fin 2, Nonempty (Isometry (dyadicCyclic 1 (2 * (i : ℤ) + 1)) A) := by
  obtain ⟨θ, hθ, ⟨e⟩⟩ := exists_dyadicCyclic_isometry A (k := 1) (by simpa using hcard) hA
  obtain ⟨t, ht⟩ := hθ
  have hres : θ % 4 = 1 ∨ θ % 4 = 3 := by omega
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, 2 * (i : ℤ) + 1 ≡ θ [ZMOD 4] := by
    rcases hres with h | h
    · exact ⟨0, by norm_num [Int.ModEq, h]⟩
    · exact ⟨1, by norm_num [Int.ModEq, h]⟩
  obtain ⟨f⟩ := (nonempty_isometry_dyadicCyclic_one_iff _ _).mpr hi
  refine ⟨i, ⟨f.trans e⟩, ?_⟩
  rintro j ⟨g⟩
  have hij := (nonempty_isometry_dyadicCyclic_one_iff _ _).mp
    ⟨g.trans (f.trans e).symm⟩
  apply Fin.ext
  simp only [Int.ModEq] at hij
  have hi0 := i.isLt
  have hj0 := j.isLt
  omega

/-- At each order `2^k ≥ 4`, every nondegenerate cyclic quadratic module has exactly one
of the coefficient representatives `1, 3, 5, 7`. The unique index selects `2i + 1`. -/
theorem existsUnique_dyadicCyclic_isometry_of_two_le (A : FiniteQuadraticModule)
    [IsAddCyclic A] {k : ℕ} [NeZero k] (hk : 2 ≤ k) (hcard : Nat.card A = 2 ^ k)
    (hA : A.IsNondegenerate) :
    ∃! i : Fin 4, Nonempty (Isometry (dyadicCyclic k (2 * (i : ℤ) + 1)) A) := by
  obtain ⟨θ, hθ, ⟨e⟩⟩ := exists_dyadicCyclic_isometry A hcard hA
  obtain ⟨t, ht⟩ := hθ
  have hres : θ % 8 = 1 ∨ θ % 8 = 3 ∨ θ % 8 = 5 ∨ θ % 8 = 7 := by omega
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, 2 * (i : ℤ) + 1 ≡ θ [ZMOD 8] := by
    rcases hres with h | h | h | h
    · exact ⟨0, by norm_num [Int.ModEq, h]⟩
    · exact ⟨1, by norm_num [Int.ModEq, h]⟩
    · exact ⟨2, by norm_num [Int.ModEq, h]⟩
    · exact ⟨3, by norm_num [Int.ModEq, h]⟩
  have hodd (j : Fin 4) : Odd (2 * (j : ℤ) + 1) := ⟨j, by ring⟩
  let f := dyadicCyclicIsometryOfModEqEight k (hodd i) hi
  refine ⟨i, ⟨f.trans e⟩, ?_⟩
  rintro j ⟨g⟩
  have hij := (nonempty_isometry_dyadicCyclic_iff_modEq_eight hk (hodd j)).mp
    ⟨g.trans (f.trans e).symm⟩
  apply Fin.ext
  simp only [Int.ModEq] at hij
  have hi0 := i.isLt
  have hj0 := j.isLt
  omega

end TauCeti.FiniteQuadraticModule
