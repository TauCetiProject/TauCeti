/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle

/-!
# Binary cycles in finite coordinates

When the vertex and chosen-dart types are finite, binary edge and vertex chains may be
represented by functions rather than finitely supported functions. The incidence boundary and its
cycle space in these coordinates agree with the Finsupp construction. In particular, loops
contribute zero columns
and parallel darts retain separate coordinates.

This comparison lets a spanning-forest cycle basis be used in either representation.

## References

* A. Hatcher, *Algebraic Topology*, §2.2 (incidence boundaries).
* R. Diestel, *Graph Theory*, §1.9 (binary cycle spaces).
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph) (O : Set Γ.E) [Finite Γ.V] [Finite O]

/-- The binary incidence boundary on finite-function coordinates. An edge contributes one at
each distinct endpoint; a loop contributes zero. -/
noncomputable def cycleBoundary : (O → ZMod 2) →ₗ[ZMod 2] (Γ.V → ZMod 2) :=
  (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) Γ.V).toLinearMap.comp <|
    (Γ.modTwoCycleBoundary O).comp
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm.toLinearMap

/-- The binary cycle space of a finite Serre graph in finite-function coordinates. -/
noncomputable def cycleSpace : Submodule (ZMod 2) (O → ZMod 2) :=
  (Γ.cycleBoundary O).ker

/-- The finite-coordinate cycle space is the kernel of its incidence boundary. -/
theorem cycleSpace_eq_ker : Γ.cycleSpace O = (Γ.cycleBoundary O).ker := by
  unfold cycleSpace
  rfl

/-- A finite binary edge chain is a cycle exactly when its boundary vanishes. -/
@[simp] theorem mem_cycleSpace_iff (c : O → ZMod 2) :
    c ∈ Γ.cycleSpace O ↔ Γ.cycleBoundary O c = 0 :=
  LinearMap.mem_ker

@[simp] theorem cycleBoundary_apply (c : O → ZMod 2) (v : Γ.V) :
    Γ.cycleBoundary O c v =
      Γ.modTwoCycleBoundary O
        ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c) v :=
  by simp only [cycleBoundary, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Finsupp.linearEquivFunOnFinite_apply]

/-- The incidence column of a dart has a coefficient at each endpoint and vanishes for a loop. -/
@[simp] theorem cycleBoundary_single [DecidableEq O] [DecidableEq Γ.V] (e : O) :
    Γ.cycleBoundary O (Pi.single e 1) =
      Pi.single (Γ.tgt e.1) 1 - Pi.single (Γ.src e.1) 1 := by
  ext v
  simp [cycleBoundary_apply, Finsupp.linearEquivFunOnFinite_symm_single,
    incidenceBoundary_single, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- A finite binary edge chain is a cycle precisely when its Finsupp representation is one. -/
theorem mem_cycleSpace_iff_finsupp (c : O → ZMod 2) :
    c ∈ Γ.cycleSpace O ↔
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c ∈
        Γ.modTwoCycleSpace O := by
  rw [cycleSpace, LinearMap.mem_ker, mem_modTwoCycleSpace_iff]
  simp [cycleBoundary]

/-- The finite-function boundary is the Finsupp boundary transported through the two
coordinate equivalences. -/
theorem cycleBoundary_finsupp :
    (Γ.cycleBoundary O).comp
        (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).toLinearMap =
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) Γ.V).toLinearMap.comp
        (Γ.modTwoCycleBoundary O) := by
  ext c v
  simp [cycleBoundary]

/-- The binary cycle space in finite-function coordinates is linearly equivalent to the
Finsupp kernel, with each edge coordinate preserved. -/
noncomputable def cycleSpaceFinsuppEquiv :
    Γ.cycleSpace O ≃ₗ[ZMod 2] Γ.modTwoCycleSpace O := by
  let e := (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm
  have h : (Γ.cycleSpace O).map e.toLinearMap = Γ.modTwoCycleSpace O := by
    ext c
    rw [Submodule.mem_map_equiv]
    simpa [e] using
      (Γ.mem_cycleSpace_iff_finsupp O (e.symm c))
  exact e.ofSubmodules (Γ.cycleSpace O) (Γ.modTwoCycleSpace O) h

@[simp] theorem cycleSpaceFinsuppEquiv_apply (c : Γ.cycleSpace O) :
    (Γ.cycleSpaceFinsuppEquiv O c : O →₀ ZMod 2) =
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O).symm c :=
  by
    simp only [cycleSpaceFinsuppEquiv, LinearEquiv.ofSubmodules_apply]

@[simp] theorem cycleSpaceFinsuppEquiv_symm_apply (c : Γ.modTwoCycleSpace O) :
    ((Γ.cycleSpaceFinsuppEquiv O).symm c : O → ZMod 2) =
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) O) c := by
  simp only [cycleSpaceFinsuppEquiv, LinearEquiv.ofSubmodules_symm_apply,
    LinearEquiv.symm_symm]

end TauCeti.SerreGraph
