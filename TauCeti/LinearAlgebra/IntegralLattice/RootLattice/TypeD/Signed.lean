/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Equivalence
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Basic

/-!
# Sign changes preserve the checkerboard lattice

Changing the signs of some coordinates of `ℚⁿ` maps the checkerboard carrier `Dₙ` onto itself:
it keeps a vector integral, and changes its coordinate sum by twice the sum of the negated
coordinates. Together with `TauCeti.dotProduct_signedEquiv`, this makes every such sign change a
symmetry of the checkerboard lattice.

## Main results

* `TauCeti.IntegralLattice.signedEquiv_mem_checkerboardCarrier_iff`: a sign change of
  coordinates preserves membership in `Dₙ`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, §4.7.1.
-/

public section

namespace TauCeti.IntegralLattice

variable {n : ℕ}

/-- A sign change of coordinates maps `Dₙ` into itself: it changes the coordinate sum by an even
integer. -/
theorem signedEquiv_mem_checkerboardCarrier (u : Fin n → ℤˣ) {x : Fin n → ℚ}
    (hx : x ∈ checkerboardCarrier n) : signedEquiv u (Equiv.refl _) x ∈ checkerboardCarrier n := by
  obtain ⟨hxZ, m, hm⟩ := (mem_checkerboardCarrier_iff x).1 hx
  choose w hw using hxZ
  refine mem_checkerboardCarrier_of (fun i ↦ u i * w i) (fun i ↦ by simp [hw i]) ?_
  have hw2 : ∑ i, w i = 2 * m := by
    have : ((∑ i, w i : ℤ) : ℚ) = ((2 * m : ℤ) : ℚ) := by
      push_cast
      rw [← hm]
      exact Finset.sum_congr rfl fun i _ ↦ (hw i).symm
    exact_mod_cast this
  have hsum : ∑ i, (u i : ℤ) * w i = ∑ i, w i + ∑ i, ((u i : ℤ) - 1) * w i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsum, hw2]
  refine (even_two_mul m).add (Finset.even_sum _ fun i _ ↦ (Even.mul_right ?_ _))
  rcases Int.units_eq_one_or (u i) with hu | hu <;> simp [hu]

/-- A sign change of coordinates preserves membership in `Dₙ`. -/
theorem signedEquiv_mem_checkerboardCarrier_iff (u : Fin n → ℤˣ) (x : Fin n → ℚ) :
    signedEquiv u (Equiv.refl _) x ∈ checkerboardCarrier n ↔ x ∈ checkerboardCarrier n :=
  ⟨fun hx ↦ signedEquiv_signedEquiv u x ▸ signedEquiv_mem_checkerboardCarrier u hx,
    signedEquiv_mem_checkerboardCarrier u⟩

end TauCeti.IntegralLattice
