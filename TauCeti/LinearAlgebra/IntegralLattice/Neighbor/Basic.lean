/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction

/-!
# Kneser neighbors

Two integral lattices `L` and `M` on the same rational quadratic space are `p`-neighbors when
their intersection `L ∩ M` has index `p` in each of them. Neighbor steps are the moves of
Kneser's method for exploring a genus. This file defines the relation, proves that it is
symmetric, that `1`-neighbors are equal, and that neighbors have equal determinants: the
determinant of `L ∩ M` is both `p² det L` and `p² det M`.

The intersection of two lattices on the same rational space is again a full lattice, and
`TauCeti.IntegralLattice.inf` packages it as an integral lattice with the form of the first.

## Main definitions

* `TauCeti.IntegralLattice.inf`: the integral lattice on the intersection of two carriers.
* `TauCeti.IntegralLattice.IsNeighbor`: Kneser's `p`-neighbor relation.

## Main results

* `TauCeti.IntegralLattice.IsNeighbor.symm`: the neighbor relation is symmetric.
* `TauCeti.IntegralLattice.isNeighbor_one_iff`: `1`-neighbors are equal.
* `TauCeti.IntegralLattice.IsNeighbor.determinant_eq`: neighbors have equal determinants.

## References

* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
* M. Kneser, *Quadratische Formen*, revised with R. Scharlau, Springer (2002), §28.
* J. Voight, *Kneser's method of neighbors*, arXiv:2308.11566.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L M : IntegralLattice V)

/-- The intersection of the carriers of two integral lattices on the same rational space is a
full lattice. -/
instance isLattice_carrier_inf : (L.carrier ⊓ M.carrier).IsLattice ℚ :=
  have := L.finiteDimensional
  inferInstance

/-- The integral lattice on the intersection of the carriers of `L` and `M`, with the form of
`L`. -/
noncomputable def inf : IntegralLattice V :=
  L.restrictFull (L.carrier ⊓ M.carrier) inf_le_left

/-- The carrier of `L.inf M` is the intersection of the two carriers. -/
@[simp]
theorem inf_carrier : (L.inf M).carrier = L.carrier ⊓ M.carrier :=
  restrictFull_carrier ..

/-- The lattice `L.inf M` carries the form of `L`. -/
@[simp]
theorem inf_form : (L.inf M).form = L.form :=
  restrictFull_form ..

/-- **Kneser neighbors.** Integral lattices `L` and `M` on the same rational quadratic space are
`p`-neighbors when their intersection has index `p` in each of them, that is
`[L : L ∩ M] = [M : L ∩ M] = p`. -/
structure IsNeighbor (p : ℕ) : Prop where
  /-- Neighbors carry the same rational form. -/
  form_eq : L.form = M.form
  /-- The intersection has index `p` in `L`. -/
  relIndex_inf_left : (L.carrier ⊓ M.carrier).toAddSubgroup.relIndex L.carrier.toAddSubgroup = p
  /-- The intersection has index `p` in `M`. -/
  relIndex_inf_right : (L.carrier ⊓ M.carrier).toAddSubgroup.relIndex M.carrier.toAddSubgroup = p

variable {L M} {p : ℕ}

/-- The neighbor relation is symmetric. -/
@[symm]
theorem IsNeighbor.symm (h : L.IsNeighbor M p) : M.IsNeighbor L p where
  form_eq := h.form_eq.symm
  relIndex_inf_left := by rw [inf_comm]; exact h.relIndex_inf_right
  relIndex_inf_right := by rw [inf_comm]; exact h.relIndex_inf_left

/-- `M` is a `p`-neighbor of `L` exactly when `L` is a `p`-neighbor of `M`. -/
theorem isNeighbor_comm : L.IsNeighbor M p ↔ M.IsNeighbor L p :=
  ⟨.symm, .symm⟩

/-- The common index of two neighbors is nonzero, since the intersection of two lattices on the
same rational space has finite index in each. -/
theorem IsNeighbor.ne_zero (h : L.IsNeighbor M p) : p ≠ 0 :=
  h.relIndex_inf_left ▸ Submodule.IsLattice.relIndex_ne_zero inf_le_left

/-- Two integral lattices are `1`-neighbors exactly when they are equal. -/
theorem isNeighbor_one_iff : L.IsNeighbor M 1 ↔ L = M := by
  constructor
  · intro h
    have hLM := AddSubgroup.relIndex_eq_one.mp h.relIndex_inf_left
    have hML := AddSubgroup.relIndex_eq_one.mp h.relIndex_inf_right
    refine ext (le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)) h.form_eq
    · exact (hLM hx).2
    · exact (hML hx).1
  · rintro rfl
    refine ⟨rfl, ?_, ?_⟩ <;> simp

/-- **Neighbors have equal determinants.** The intersection `L ∩ M` has determinant
`[L : L ∩ M]² det L = [M : L ∩ M]² det M`, and both indices equal the nonzero integer `p`. -/
theorem IsNeighbor.determinant_eq (h : L.IsNeighbor M p) : L.determinant = M.determinant := by
  have hL := (L.inf M).determinant_eq_mul_relIndex_sq L (inf_form L M)
    ((inf_carrier L M).trans_le inf_le_left)
  have hM := (L.inf M).determinant_eq_mul_relIndex_sq M ((inf_form L M).trans h.form_eq)
    ((inf_carrier L M).trans_le inf_le_right)
  rw [inf_carrier, h.relIndex_inf_left] at hL
  rw [inf_carrier, h.relIndex_inf_right] at hM
  exact mul_right_cancel₀ (pow_ne_zero 2 (Int.natCast_ne_zero.mpr h.ne_zero)) (hL.symm.trans hM)

/-- Neighbors have equal discriminants. -/
theorem IsNeighbor.discriminant_eq (h : L.IsNeighbor M p) : L.discriminant = M.discriminant := by
  rw [discriminant_def, discriminant_def, h.determinant_eq]

end TauCeti.IntegralLattice
