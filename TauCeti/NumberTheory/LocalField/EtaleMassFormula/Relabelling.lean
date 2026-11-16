/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Mass
public import TauCeti.FieldTheory.Galois.GaloisSet.Relabelling
import TauCeti.GroupTheory.GroupAction.Orbit.ENNReal
import Mathlib.Data.Fintype.Perm

/-!
# Étale mass as an automorphism-weighted orbit sum

Relabelling a Galois set preserves its discriminant exponent. Consequently the étale mass,
defined as a sum over labelled Galois sets divided by `n!`, is a sum over relabelling orbits
weighted by the reciprocal order of the group of equivariant permutations. This supplies
the counting step in identifying the étale mass with a sum over isomorphism classes of
finite étale algebras; identifying those algebras with Galois sets is a separate statement.

The orbit space can be infinite, and all sums take values in `ℝ≥0∞`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density
  of number field discriminants*, IMRN 2007, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN 2007, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

/-- Relabelling a Galois set does not change its discriminant exponent. -/
@[simp]
theorem GaloisSet.discriminantExponent_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).discriminantExponent = ρ.discriminantExponent := by
  exact (ρ.discriminantExponent_eq_of_equiv (e • ρ) e (by simp)).symm

/-- The étale mass is a sum over equivariant isomorphism classes of Galois sets, with each
class weighted by the reciprocal order of its equivariant automorphism group. This counts
Galois sets, not yet étale algebras. It includes degree zero and allows infinitely many classes. -/
theorem etaleMass_eq_tsum_orbitRelQuotient :
    etaleMass K n =
      ∑' ω : MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (GaloisSet K n),
        1 / ((Nat.card (MulAction.stabilizer (Equiv.Perm (Fin n)) ω.out) : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ ω.out.discriminantExponent) := by
  have h := MulAction.inv_natCard_mul_tsum_eq_tsum_div_natCard_stabilizer
    (G := Equiv.Perm (Fin n))
    (fun ρ : GaloisSet K n ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent)
    (by simp)
  convert h using 1
  · simp [etaleMass_def, Nat.card_eq_fintype_card, Fintype.card_perm]
  · apply tsum_congr
    intro ω
    have hs : (Nat.card (MulAction.stabilizer (Equiv.Perm (Fin n)) ω.out) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer (Equiv.Perm (Fin n)) ω.out)).ne'
    simp only [div_eq_mul_inv, one_mul]
    rw [ENNReal.mul_inv (Or.inl hs) (Or.inl (by simp)), mul_comm]

end TauCeti
