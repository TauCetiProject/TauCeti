/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Change of coefficients for graph cycles

The integral cycle lattice determines the incidence kernel over any ring by extension of
scalars. The comparison sends a pure tensor `r ⊗ c` to the chain with coefficients
`r * (c e : R)`. In particular, tensoring with `ZMod 2` identifies integral cycles modulo
two with the binary cycle space, not merely with an abstract vector space of the same rank.

Spanning-forest bases prove the comparison is bijective. The coordinate formula shows that
it is independent of the forest and carries integral fundamental cycles to the fundamental
cycles over the new coefficient ring. No finiteness, connectedness or orientation assumption
is needed; loops and parallel edges are retained.

## References

* A. Hatcher, *Algebraic Topology*, §2.2 (incidence boundaries and coefficients).
* R. Diestel, *Graph Theory*, §1.9 (fundamental cycle bases).
-/

public section

open scoped TensorProduct

namespace TauCeti.SerreGraph

variable {Γ : SerreGraph} {O F : Set Γ.E} {R : Type*} [Ring R]

/-- Taking integer coefficients into a ring commutes with the signed incidence boundary. -/
theorem incidenceBoundary_intCast (Γ : SerreGraph) (O : Set Γ.E) (c : O →₀ ℤ) :
    Γ.incidenceBoundary O R (c.mapRange (Int.cast : ℤ → R) Int.cast_zero) =
      (Γ.integralCycleBoundary O c).mapRange (Int.cast : ℤ → R) Int.cast_zero := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [Finsupp.mapRange_add (f := (Int.cast : ℤ → R)) (fun x y =>
      Int.cast_add x y), map_add, hc, hd]
  | single e n =>
    ext v
    simp [incidenceBoundary_single, Finsupp.mapRange_single, Finsupp.single_apply,
      smul_sub, Int.cast_sub, Int.cast_ite]

/-- The chain obtained by taking the coefficients of an integral cycle into a ring
is again a cycle. -/
theorem intCast_mem_ker_incidenceBoundary (Γ : SerreGraph) (O : Set Γ.E)
    (c : (Γ.incidenceBoundary O ℤ).ker) :
    c.val.mapRange (Int.cast : ℤ → R) Int.cast_zero ∈ (Γ.incidenceBoundary O R).ker := by
  rw [LinearMap.mem_ker, Γ.incidenceBoundary_intCast, LinearMap.mem_ker.mp c.property]
  simp

/-- Extension of scalars identifies the integral cycle lattice with the incidence kernel
over any ring. Its action on actual edge coordinates is `cycleBaseChangeEquiv_tmul`.
The spanning forest used to construct the equivalence does not affect this action. -/
noncomputable def cycleBaseChangeEquiv (Γ : SerreGraph) (O : Set Γ.E)
    (R : Type*) [Ring R] :
    R ⊗[ℤ] (Γ.incidenceBoundary O ℤ).ker ≃ₗ[R] (Γ.incidenceBoundary O R).ker :=
  let hF := (Γ.exists_spanningForest O).choose_spec
  ((hF.cycleBasis ℤ).baseChange R).repr.trans (hF.cycleEquiv R).symm

/-- The comparison is coefficientwise on pure tensors, including on forest edges. -/
@[simp] theorem cycleBaseChangeEquiv_tmul (r : R)
    (c : (Γ.incidenceBoundary O ℤ).ker) (e : O) :
    (Γ.cycleBaseChangeEquiv O R (r ⊗ₜ[ℤ] c)).val e = r * (c.val e : R) := by
  let hF := (Γ.exists_spanningForest O).choose_spec
  have h : Γ.cycleBaseChangeEquiv O R (r ⊗ₜ[ℤ] c) =
      r • (⟨c.val.mapRange (Int.cast : ℤ → R) Int.cast_zero,
        Γ.intCast_mem_ker_incidenceBoundary O c⟩ : (Γ.incidenceBoundary O R).ker) := by
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
  rw [h]
  simp

/-- An integral fundamental cycle becomes the fundamental cycle on the same chord after
extension of scalars. This also expresses compatibility with any choice of spanning forest. -/
@[simp] theorem IsSpanningForest.cycleBaseChangeEquiv_basis
    (hF : Γ.IsSpanningForest O F) (e : ↥(O \ F)) :
    Γ.cycleBaseChangeEquiv O R (1 ⊗ₜ[ℤ] hF.cycleBasis ℤ e) =
      hF.cycleBasis R e := by
  classical
  apply hF.cycleChordCoordinates_injective
  ext f
  simp only [cycleChordCoordinates_apply, cycleBaseChangeEquiv_tmul,
    one_mul, IsSpanningForest.cycleBasis_apply_chord]
  simp [Finsupp.single_apply]

/-- Integral cycles modulo two are the binary cycle space, with edgewise coefficient
reduction rather than an unspecified vector-space isomorphism. The named integral and binary
modules are the corresponding incidence kernels. -/
noncomputable def cycleLatticeModTwoEquiv (Γ : SerreGraph) (O : Set Γ.E) :
    (ZMod 2) ⊗[ℤ] Γ.cycleLattice O ≃ₗ[ZMod 2] Γ.modTwoCycleSpace O :=
  ((TensorProduct.AlgebraTensorModule.congr (.refl (ZMod 2) (ZMod 2))
      (LinearEquiv.ofEq _ _ cycleLattice_def)).trans
    (Γ.cycleBaseChangeEquiv O (ZMod 2))).trans
      (LinearEquiv.ofEq _ _ modTwoCycleSpace_def.symm)

/-- Tensoring an integral cycle with one reduces each of its coefficients modulo two. -/
@[simp] theorem cycleLatticeModTwoEquiv_one_tmul (c : Γ.cycleLattice O) (e : O) :
    (Γ.cycleLatticeModTwoEquiv O (1 ⊗ₜ[ℤ] c)).val e = (c.val e : ZMod 2) := by
  simp [cycleLatticeModTwoEquiv]

end TauCeti.SerreGraph
