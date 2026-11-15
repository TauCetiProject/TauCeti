/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Basis
public import TauCeti.Data.Finsupp.Single
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Change of coefficients for graph cycles

The integral cycle lattice determines the incidence kernel over any ring by extension of
scalars. The comparison sends a pure tensor `r ⊗ c` to the chain with coefficients
`r * (c e : R)`. In particular, tensoring with `ZMod 2` identifies integral cycles modulo
two with the binary cycle space, not merely with an abstract vector space of the same rank.

Spanning-forest bases prove the comparison is bijective. The coordinate formula shows that
it is independent of the forest and carries `r ⊗` an integral fundamental cycle to `r` times the
fundamental cycle over the new coefficient ring; the coordinates of a fundamental cycle over any
ring are the casts of the integral ones. The comparison needs no finiteness, connectedness or
orientation assumption; loops and parallel edges are retained. On a loop, the integral unit cycle
reduces to the binary unit cycle on the same loop.

## References

* A. Hatcher, *Algebraic Topology*, §2.2 (incidence boundaries and coefficients).
* R. Diestel, *Graph Theory*, §1.9 (fundamental cycle bases).
-/

public section

open scoped TensorProduct

namespace TauCeti.SerreGraph

variable {Γ : SerreGraph} {O F : Set Γ.E} {R : Type*} [Ring R]

/-- Extension of scalars identifies the integral cycle lattice with the incidence kernel
over any ring. Its action on actual edge coordinates is `cycleBaseChangeEquiv_tmul`.
The spanning forest used to construct the equivalence does not affect this action. -/
noncomputable def cycleBaseChangeEquiv (Γ : SerreGraph) (O : Set Γ.E)
    (R : Type*) [Ring R] :
    R ⊗[ℤ] (Γ.incidenceBoundary O ℤ).ker ≃ₗ[R] (Γ.incidenceBoundary O R).ker :=
  let hF := (Γ.exists_spanningForest O).choose_spec
  ((hF.cycleBasis ℤ).baseChange R).repr.trans (hF.cycleEquiv R).symm

/-- On pure tensors, the comparison scales the cycle obtained by casting its coefficients. -/
theorem cycleBaseChangeEquiv_tmul_eq (r : R) (c : (Γ.incidenceBoundary O ℤ).ker) :
    Γ.cycleBaseChangeEquiv O R (r ⊗ₜ[ℤ] c) =
      r • (⟨c.val.mapRange (Int.cast : ℤ → R) Int.cast_zero,
        Γ.mapRange_intCast_mem_ker_incidenceBoundary O c⟩ :
          (Γ.incidenceBoundary O R).ker) := by
  let hF := (Γ.exists_spanningForest O).choose_spec
  have hcoord : hF.cycleEquiv R
      (Γ.cycleBaseChangeEquiv O R (r ⊗ₜ[ℤ] c)) =
      ((hF.cycleBasis ℤ).baseChange R).repr (r ⊗ₜ[ℤ] c) :=
    (hF.cycleEquiv R).apply_symm_apply _
  apply hF.cycleChordCoordinates_injective
  ext f
  rw [cycleChordCoordinates_apply, ← hF.cycleEquiv_apply, hcoord]
  rw [Module.Basis.baseChange_repr_tmul]
  simp only [IsSpanningForest.cycleBasis_repr, cycleChordCoordinates_apply,
    map_smul, Finsupp.smul_apply, Finsupp.mapRange_apply,
    smul_eq_mul, zsmul_eq_mul]
  exact Int.cast_commute _ _

/-- The comparison is coefficientwise on pure tensors, including on forest edges. -/
@[simp] theorem cycleBaseChangeEquiv_tmul (r : R)
    (c : (Γ.incidenceBoundary O ℤ).ker) (e : O) :
    (Γ.cycleBaseChangeEquiv O R (r ⊗ₜ[ℤ] c)).val e = r * (c.val e : R) := by
  simp [cycleBaseChangeEquiv_tmul_eq]

/-- Extension of scalars sends `r ⊗` an integral fundamental cycle to `r` times the fundamental
cycle on the same chord; for `r = 1`, the integral fundamental cycle becomes the fundamental cycle.
This also expresses compatibility with any choice of spanning forest. -/
@[simp] theorem IsSpanningForest.cycleBaseChangeEquiv_tmul_cycleBasis
    (hF : Γ.IsSpanningForest O F) (r : R) (e : ↥(O \ F)) :
    Γ.cycleBaseChangeEquiv O R (r ⊗ₜ[ℤ] hF.cycleBasis ℤ e) = r • hF.cycleBasis R e := by
  apply hF.cycleChordCoordinates_injective
  ext f
  by_cases h : e = f <;> simp [h]

/-- The coordinates of a fundamental cycle over any ring are the casts of the coordinates of the
integral fundamental cycle on the same chord. -/
@[simp] theorem IsSpanningForest.intCast_cycleBasis_apply (hF : Γ.IsSpanningForest O F)
    (e : ↥(O \ F)) (d : O) : ((hF.cycleBasis ℤ e).val d : R) = (hF.cycleBasis R e).val d := by
  rw [← one_mul ((hF.cycleBasis ℤ e).val d : R), ← cycleBaseChangeEquiv_tmul,
    hF.cycleBaseChangeEquiv_tmul_cycleBasis, one_smul]

/-- Integral cycles modulo two are the binary cycle space, with edgewise coefficient
reduction rather than an unspecified vector-space isomorphism. The named integral and binary
modules are the corresponding incidence kernels. -/
noncomputable def cycleLatticeModTwoEquiv (Γ : SerreGraph) (O : Set Γ.E) :
    (ZMod 2) ⊗[ℤ] Γ.cycleLattice O ≃ₗ[ZMod 2] Γ.modTwoCycleSpace O :=
  ((TensorProduct.AlgebraTensorModule.congr (.refl (ZMod 2) (ZMod 2))
      (LinearEquiv.ofEq _ _ cycleLattice_def)).trans
    (Γ.cycleBaseChangeEquiv O (ZMod 2))).trans
      (LinearEquiv.ofEq _ _ modTwoCycleSpace_def.symm)

/-- On pure tensors, the binary comparison scales the coefficientwise reduction modulo two. -/
@[simp] theorem cycleLatticeModTwoEquiv_tmul (r : ZMod 2) (c : Γ.cycleLattice O) (e : O) :
    (Γ.cycleLatticeModTwoEquiv O (r ⊗ₜ[ℤ] c)).val e = r * (c.val e : ZMod 2) := by
  simp [cycleLatticeModTwoEquiv]

/-- The integral unit cycle on a dart reduces to the binary unit cycle on the same dart. The
unit chain on a dart is an integral cycle exactly when the dart is a loop
(`single_mem_cycleLattice_iff`). -/
@[simp] theorem cycleLatticeModTwoEquiv_one_tmul_single (e : O)
    (hc : Finsupp.single e 1 ∈ Γ.cycleLattice O) :
    (Γ.cycleLatticeModTwoEquiv O (1 ⊗ₜ[ℤ] ⟨Finsupp.single e 1, hc⟩)).val =
      Finsupp.single e 1 := by
  classical
  ext f
  simp [Finsupp.single_apply]

end TauCeti.SerreGraph
