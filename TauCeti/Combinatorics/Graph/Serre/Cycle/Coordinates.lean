/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Algebra.CharP.Two

/-!
# Finite coordinates for binary graph cycles

For a finite vertex and dart set, binary edge chains can be written either as finite
functions or as finitely supported functions. The incidence boundary commutes with this
change of coordinates, including for loops and parallel darts. Restricting the coordinate
equivalence to the kernels identifies the two presentations of the binary cycle space.

## References

* A. Hatcher, *Algebraic Topology*, §2.2 (incidence boundaries).
* R. Diestel, *Graph Theory*, §1.9 (binary cycle spaces).
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph) (O : Set Γ.E)
variable [Finite Γ.V] [Finite O]

/-- The binary incidence boundary in finite-function edge and vertex coordinates. -/
noncomputable def cycleBoundary : (O → ZMod 2) →ₗ[ZMod 2] (Γ.V → ZMod 2) :=
  (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) Γ.V).toLinearMap.comp
    ((Γ.modTwoCycleBoundary O).comp
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm.toLinearMap)

/-- The binary cycle space in finite-function coordinates. -/
noncomputable def cycleSpace : Submodule (ZMod 2) (O → ZMod 2) :=
  (Γ.cycleBoundary O).ker

/-- A finite-function chain is a cycle exactly when its boundary vanishes. -/
@[simp] theorem mem_cycleSpace_iff_cycleBoundary (c : O → ZMod 2) :
    c ∈ Γ.cycleSpace O ↔ Γ.cycleBoundary O c = 0 :=
  LinearMap.mem_ker

/-- The finite-function/Finsupp square commutes with the binary incidence boundary. -/
@[simp] theorem cycleBoundary_finsupp (c : O →₀ ZMod 2) :
    Γ.cycleBoundary O (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O c) =
      Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) Γ.V
        (Γ.modTwoCycleBoundary O c) := by
  simp [cycleBoundary]

/-- Taking Finsupp coordinates of a finite-function boundary recovers the original boundary. -/
@[simp] theorem cycleBoundary_symm (c : O → ZMod 2) :
    (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) Γ.V).symm
      (Γ.cycleBoundary O c) =
        Γ.modTwoCycleBoundary O
          ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c) := by
  simp [cycleBoundary]

/-- A binary dart contributes at both endpoints. A loop contributes twice at the same
vertex, hence contributes zero. -/
@[simp] theorem cycleBoundary_single [DecidableEq Γ.V] [DecidableEq O] (e : O) :
    Γ.cycleBoundary O (Pi.single e 1) =
      Pi.single (Γ.tgt e.1) 1 + Pi.single (Γ.src e.1) 1 := by
  classical
  rw [← Finsupp.linearEquivFunOnFinite_single (ZMod 2) (ZMod 2) O e 1,
    cycleBoundary_finsupp, incidenceBoundary_single, one_smul]
  ext v
  simp [sub_eq_add_neg, CharTwo.neg_eq, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- A finite-function chain is a cycle exactly when its Finsupp coordinates are a cycle. -/
theorem mem_cycleSpace_iff (c : O → ZMod 2) :
    c ∈ Γ.cycleSpace O ↔
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c ∈
        Γ.modTwoCycleSpace O := by
  simp only [mem_cycleSpace_iff_cycleBoundary, mem_modTwoCycleSpace_iff]
  rw [← (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) Γ.V).symm.map_eq_zero_iff,
    cycleBoundary_symm]

/-- A single binary edge is a cycle exactly when it is a loop. -/
theorem single_mem_cycleSpace_iff [DecidableEq O] (e : O) :
    Pi.single e (1 : ZMod 2) ∈ Γ.cycleSpace O ↔
      Γ.src e.1 = Γ.tgt e.1 := by
  classical
  rw [mem_cycleSpace_iff, Finsupp.linearEquivFunOnFinite_symm_single]
  exact Γ.single_mem_modTwoCycleSpace_iff e

/-- The finite-coordinate equivalence maps the Finsupp cycle space onto the function cycle space. -/
theorem map_modTwoCycleSpace :
    (Γ.modTwoCycleSpace O).map
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).toLinearMap =
        Γ.cycleSpace O := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext c
  exact (Γ.mem_cycleSpace_iff O c).symm

/-- The coordinate equivalence restricts to the two binary cycle kernels. -/
noncomputable def cycleSpaceFinsuppEquiv :
    Γ.modTwoCycleSpace O ≃ₗ[ZMod 2] Γ.cycleSpace O :=
  (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).ofSubmodules _ _
    (Γ.map_modTwoCycleSpace O)

@[simp] theorem cycleSpaceFinsuppEquiv_apply (c : Γ.modTwoCycleSpace O) :
    (Γ.cycleSpaceFinsuppEquiv O c).1 =
      Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O c.1 := by
  simp only [cycleSpaceFinsuppEquiv, LinearEquiv.ofSubmodules_apply]

@[simp] theorem cycleSpaceFinsuppEquiv_symm_apply (c : Γ.cycleSpace O) :
    ((Γ.cycleSpaceFinsuppEquiv O).symm c).1 =
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c.1 := by
  simp only [cycleSpaceFinsuppEquiv, LinearEquiv.ofSubmodules_symm_apply]

end TauCeti.SerreGraph
