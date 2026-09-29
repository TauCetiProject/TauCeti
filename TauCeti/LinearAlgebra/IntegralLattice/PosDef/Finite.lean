/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Floor
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
public import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Finiteness of bounded-norm sets in a positive definite lattice

A positive definite integral lattice has only finitely many vectors of norm at most any given
bound, and hence only finitely many vectors of any given norm. This is what makes the minimum,
the shells and the representation numbers of a positive definite lattice finite quantities.

Positive definiteness is load-bearing: the hyperbolic plane is nondegenerate, yet its isotropic
vectors form an infinite shell of norm zero
(`TauCeti.IntegralLattice.infinite_vectorsOfNorm_zero_hyperbolicPlane`).

## Main results

* `TauCeti.IntegralLattice.IsPosSemidef.integralNorm_nonneg` and
  `TauCeti.IntegralLattice.IsPosDef.posDef_integralNorm`: the integral norm form of a positive
  semidefinite lattice is nonnegative, and that of a positive definite lattice is positive
  definite.
* `TauCeti.IntegralLattice.IsPosDef.finite_setOf_norm_le`: only finitely many lattice vectors have
  norm at most a given rational bound.
* `TauCeti.IntegralLattice.IsPosDef.finite_vectorsOfNorm`: every shell of a positive definite
  lattice is finite.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §2.
-/

public section

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

variable {L : IntegralLattice V}

/-- The integral norm of a positive semidefinite lattice is nonnegative. -/
theorem IsPosSemidef.integralNorm_nonneg (hL : L.IsPosSemidef) (x : L) :
    0 ≤ L.integralNorm x := by
  have h : (0 : ℚ) ≤ L.norm x := by
    rw [L.norm_apply]
    exact L.isPosSemidef_iff.mp hL x
  rw [← L.integralNorm_cast x] at h
  exact_mod_cast h

/-- The integral norm form of a positive definite lattice is positive definite. -/
theorem IsPosDef.posDef_integralNorm (hL : L.IsPosDef) : L.integralNorm.PosDef := by
  intro x hx
  have h : (0 : ℚ) < L.norm x := by
    rw [L.norm_def]
    exact hL (x : V) (Submodule.coe_eq_zero.not.mpr hx)
  rw [← L.integralNorm_cast x] at h
  exact_mod_cast h

/-- **Bounded-norm sets of a positive definite lattice are finite.** Only finitely many vectors of
a positive definite integral lattice have norm at most a given rational bound. -/
theorem IsPosDef.finite_setOf_norm_le (hL : L.IsPosDef) (C : ℚ) :
    {x : L | L.norm x ≤ C}.Finite := by
  refine (hL.posDef_integralNorm.finite_setOf_apply_le ⌊C⌋).subset fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [Int.le_floor, L.integralNorm_cast]
  exact hx

/-- **Every shell of a positive definite lattice is finite.** -/
theorem IsPosDef.finite_vectorsOfNorm (hL : L.IsPosDef) (n : ℚ) :
    (L.vectorsOfNorm n).Finite :=
  (hL.finite_setOf_norm_le n).subset fun _ hx ↦ (mem_vectorsOfNorm.mp hx).le

end IntegralLattice

end TauCeti
