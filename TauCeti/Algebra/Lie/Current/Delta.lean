/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Field
public import TauCeti.Algebra.Vertex.FormalDistribution

/-!
# The delta expansion of affine current commutators

The mode commutator of smooth currents assembles into the formal-distribution identity

`[J^x(z), J^y(w)] = J^[x,y](w) δ(z,w) - a Φ(x,y) ∂_w δ(z,w)`.

Here `Φ` follows Mathlib's positive-residue convention, and `a` is the scalar by which the
central generator acts. For the affine level form `κ`, take `Φ = -κ`. The simple-pole residue
is the bracket field and the double-pole residue is the constant scalar field `-a Φ(x,y)`.
These are actual equalities of coefficient families, not products of incompatible Hahn series.
The generic uniqueness theorem for delta expansions identifies these two singular coefficients
canonically. No characteristic, finite-dimensionality or nonzero-level hypothesis is required.

## References

* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.5.
-/

public section

noncomputable section

open scoped VertexOperator

namespace TauCeti.CurrentAlgebra

open FormalDistribution

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M]
  (Φ : LinearMap.BilinForm R L) (a : R) {σ : currentAlgebra R L →ₗ[R] Module.End R M}
  (hσ : IsSmooth σ)
  (hσc : ∀ u v, σ u * σ v - σ v * σ u =
    σ ⁅u, v⁆ + algebraMap R (Module.End R M) (a * residuePairing R L Φ u v))

include hσc

/-- The full affine current commutator is the sum of its bracket delta term and its central
first-derivative delta term, with Mathlib's positive-residue sign convention. -/
theorem commutatorDistribution_currentField (x y : L) :
    (currentField σ hσ x).commutatorDistribution (currentField σ hσ y) =
      deltaTerm 0 (fun n ↦ (currentField σ hσ ⁅x, y⁆)[[n]]) +
        deltaTerm 1 (fun n ↦ if n = -1 then
          -algebraMap R (Module.End R M) (a * Φ x y) else 0) := by
  have hc (k : ℤ) : algebraMap R (Module.End R M) (a * k * Φ x y) =
      k • algebraMap R (Module.End R M) (a * Φ x y) := by
    rw [mul_comm a, mul_assoc, ← zsmul_eq_mul, map_zsmul]
  ext m n
  rw [VertexOperator.commutatorDistribution_apply,
    ncoeff_currentField_mul_sub_mul Φ a hσ hσc]
  simp only [Pi.add_apply, deltaTerm_apply, Ring.choose_zero_right, Ring.choose_one_right,
    Nat.cast_zero, Nat.cast_one, sub_zero, one_smul]
  by_cases h : m + n = 0
  · have hn : n = -m := by omega
    simp [hn, hc]
  · have h' : m + n - 1 ≠ -1 := by omega
    simp [h, h']

/-- The simple-pole residue of the current commutator is the bracket field. -/
theorem residue_commutatorDistribution_currentField (x y : L) :
    residue ((currentField σ hσ x).commutatorDistribution (currentField σ hσ y)) =
      fun n ↦ (currentField σ hσ ⁅x, y⁆)[[n]] := by
  rw [commutatorDistribution_currentField Φ a hσ hσc]
  simp only [map_add, residue_deltaTerm_zero, residue_deltaTerm_succ, add_zero]

/-- The double-pole residue of the current commutator is the constant scalar field
`-a Φ(x,y)`. A constant field has its only normalized coefficient at index `-1`. -/
theorem residue_mulSub_commutatorDistribution_currentField (x y : L) :
    residue (mulSub ((currentField σ hσ x).commutatorDistribution (currentField σ hσ y))) =
      fun n ↦ if n = -1 then -algebraMap R (Module.End R M) (a * Φ x y) else 0 := by
  rw [commutatorDistribution_currentField Φ a hσ hσc]
  simp only [map_add, mulSub_deltaTerm_zero, mulSub_deltaTerm_succ, zero_add,
    residue_deltaTerm_zero]

end TauCeti.CurrentAlgebra
