/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.KnotTheory.Grid.CycleSymmetry
public import TauCeti.KnotTheory.Grid.Differential.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Homology

/-!
# Cyclic symmetries of fully blocked grid homology

The chain-level cyclic-permutation theorems identify the fully blocked differentials of a grid
diagram and its row- or column-relabelled diagram. This file carries those identifications through
the cycle and boundary submodules to the quotient that defines fully blocked grid homology.

The construction is phrased through a general intertwining theorem. An invertible linear map that
intertwines two fully blocked differentials maps cycles to cycles and boundaries to boundaries, so
it induces an equivalence of the corresponding homology quotients. The cyclic row and column
permutations are then the two concrete instances needed for the cyclic-permutation moves.

The quotient homology used here is the subquotient from `Homology.lean`; no choice of
representatives is involved. The `_apply_mk` lemmas record the representative-level computation,
which is the characteristic API for using the induced equivalences without unfolding the quotient
construction.

## Main results

* `TauCeti.GridDiagram.fullyBlockedHomologyEquivOfIntertwining`: an invertible intertwining map
  induces an equivalence of fully blocked homology quotients.
* `TauCeti.GridDiagram.fullyBlockedCyclesEquiv`: the same map induces an equivalence of cycle
  submodules, with its action on representatives exposed by `fullyBlockedCyclesEquiv_apply`.
* `TauCeti.GridDiagram.fullyBlockedHomologyEquiv_relabelRows_finRotate` and
  `TauCeti.GridDiagram.fullyBlockedHomologyEquiv_relabelColumns_finRotate`: cyclic row and column
  relabellings induce homology equivalences, with representative formulas given by their
  `_apply_mk` lemmas.

## References

The cyclic grid symmetries follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapters 3--5. The quotient construction uses Mathlib's `Submodule.Quotient.equiv`.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G G' : GridDiagram n)

section Intertwining

variable (e : GridChain (ZMod 2) n ≃ₗ[ZMod 2] GridChain (ZMod 2) n)
variable (he : ∀ c, G'.fullyBlockedDifferential (e c) =
  e (G.fullyBlockedDifferential c))

include he

/-- The chain equivalence induced by `e` between the cycle submodules of two intertwined grid
differentials. -/
noncomputable def fullyBlockedCyclesEquiv :
    G.fullyBlockedCycles ≃ₗ[ZMod 2] G'.fullyBlockedCycles := by
  apply e.ofSubmodules
  rw [G.fullyBlockedCycles_eq_ker, G'.fullyBlockedCycles_eq_ker]
  exact e.map_ker_eq_ker_of_intertwine G.fullyBlockedDifferential
    G'.fullyBlockedDifferential he

/-- The induced cycle equivalence acts on underlying chains by the intertwining map. -/
@[simp]
theorem fullyBlockedCyclesEquiv_apply (c : G.fullyBlockedCycles) :
    (G.fullyBlockedCyclesEquiv G' e he c : GridChain (ZMod 2) n) = e c := by
  exact e.ofSubmodules_apply _ c

/-- The inverse induced cycle equivalence acts on underlying chains by the inverse map. -/
@[simp]
theorem fullyBlockedCyclesEquiv_symm_apply (c : G'.fullyBlockedCycles) :
    ((G.fullyBlockedCyclesEquiv G' e he).symm c : GridChain (ZMod 2) n) =
      e.symm (c : GridChain (ZMod 2) n) := by
  exact e.ofSubmodules_symm_apply _ c

/-- An invertible map intertwining two fully blocked differentials induces a linear equivalence of
their homology quotients. -/
noncomputable def fullyBlockedHomologyEquivOfIntertwining :
    G.fullyBlockedHomology ≃ₗ[ZMod 2] G'.fullyBlockedHomology := by
  apply Submodule.Quotient.equiv
    G.fullyBlockedBoundariesInCycles G'.fullyBlockedBoundariesInCycles
    (G.fullyBlockedCyclesEquiv G' e he)
  ext c
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hd' : (d : GridChain (ZMod 2) n) ∈ G.fullyBlockedBoundaries :=
      (mem_fullyBlockedBoundariesInCycles G d).mp hd
    obtain ⟨b, hb⟩ := (mem_fullyBlockedBoundaries G (d : GridChain (ZMod 2) n)).mp hd'
    apply (mem_fullyBlockedBoundariesInCycles G' _).mpr
    apply (mem_fullyBlockedBoundaries G' _).mpr
    refine ⟨e b, ?_⟩
    calc
      G'.fullyBlockedDifferential (e b) = e (G.fullyBlockedDifferential b) := he b
      _ = e (d : GridChain (ZMod 2) n) := by rw [hb]
      _ = (G.fullyBlockedCyclesEquiv G' e he d : GridChain (ZMod 2) n) :=
        (fullyBlockedCyclesEquiv_apply G G' e he d).symm
  · intro hc
    have hc' : (c : GridChain (ZMod 2) n) ∈ G'.fullyBlockedBoundaries :=
      (mem_fullyBlockedBoundariesInCycles G' c).mp hc
    obtain ⟨b, hb⟩ := (mem_fullyBlockedBoundaries G' (c : GridChain (ZMod 2) n)).mp hc'
    refine ⟨(G.fullyBlockedCyclesEquiv G' e he).symm c, ?_,
      (G.fullyBlockedCyclesEquiv G' e he).apply_symm_apply c⟩
    · apply (mem_fullyBlockedBoundariesInCycles G _).mpr
      apply (mem_fullyBlockedBoundaries G _).mpr
      refine ⟨e.symm b, ?_⟩
      rw [fullyBlockedCyclesEquiv_symm_apply]
      calc
        G.fullyBlockedDifferential (e.symm b) = e.symm
            (G'.fullyBlockedDifferential b) := by
          simpa using (congrArg e.symm (he (e.symm b))).symm
        _ = e.symm c := by rw [hb]
/-- The induced homology equivalence sends the class of a cycle to the class of its image cycle. -/
@[simp]
theorem fullyBlockedHomologyEquivOfIntertwining_apply_mk (c : G.fullyBlockedCycles) :
    G.fullyBlockedHomologyEquivOfIntertwining G' e he (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (G.fullyBlockedCyclesEquiv G' e he c) := by
  rw [fullyBlockedHomologyEquivOfIntertwining, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]
  rfl

end Intertwining

section Cyclic

/-- The cyclic row relabelling intertwines the fully blocked differentials pointwise. -/
theorem fullyBlockedDifferential_relabelRows_finRotate_apply (c : GridChain (ZMod 2) n) :
    (G.relabelRows (finRotate n)).fullyBlockedDifferential
        (GridChain.relabelRowsEquiv (finRotate n) c) =
      GridChain.relabelRowsEquiv (finRotate n) (G.fullyBlockedDifferential c) := by
  have h := DFunLike.congr_fun G.fullyBlockedDifferential_relabelRows_finRotate c
  simpa [LinearMap.comp_apply] using h

/-- The cyclic column relabelling intertwines the fully blocked differentials pointwise. -/
theorem fullyBlockedDifferential_relabelColumns_finRotate_apply
    (c : GridChain (ZMod 2) n) :
    (G.relabelColumns (finRotate n)).fullyBlockedDifferential
        (GridChain.relabelColumnsEquiv (finRotate n) c) =
      GridChain.relabelColumnsEquiv (finRotate n) (G.fullyBlockedDifferential c) := by
  have h := DFunLike.congr_fun G.fullyBlockedDifferential_relabelColumns_finRotate c
  simpa [LinearMap.comp_apply] using h

/-- Cyclic row relabelling induces an equivalence of fully blocked grid homology quotients. -/
noncomputable def fullyBlockedHomologyEquiv_relabelRows_finRotate :
    G.fullyBlockedHomology ≃ₗ[ZMod 2]
      (G.relabelRows (finRotate n)).fullyBlockedHomology :=
  G.fullyBlockedHomologyEquivOfIntertwining (G.relabelRows (finRotate n))
    (GridChain.relabelRowsEquiv (finRotate n))
    (fullyBlockedDifferential_relabelRows_finRotate_apply (G := G))

/-- The cyclic row homology equivalence sends a represented class to the relabelled class. -/
@[simp]
theorem fullyBlockedHomologyEquiv_relabelRows_finRotate_apply_mk
    (c : G.fullyBlockedCycles) :
    G.fullyBlockedHomologyEquiv_relabelRows_finRotate
        (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (G.fullyBlockedCyclesEquiv (G.relabelRows (finRotate n))
          (GridChain.relabelRowsEquiv (finRotate n))
          (fullyBlockedDifferential_relabelRows_finRotate_apply (G := G)) c) := by
  exact fullyBlockedHomologyEquivOfIntertwining_apply_mk
    (G := G) (G' := G.relabelRows (finRotate n))
    (e := GridChain.relabelRowsEquiv (finRotate n))
    (he := fullyBlockedDifferential_relabelRows_finRotate_apply (G := G)) c

/-- Cyclic column relabelling induces an equivalence of fully blocked grid homology quotients. -/
noncomputable def fullyBlockedHomologyEquiv_relabelColumns_finRotate :
    G.fullyBlockedHomology ≃ₗ[ZMod 2]
      (G.relabelColumns (finRotate n)).fullyBlockedHomology :=
  G.fullyBlockedHomologyEquivOfIntertwining (G.relabelColumns (finRotate n))
    (GridChain.relabelColumnsEquiv (finRotate n))
    (fullyBlockedDifferential_relabelColumns_finRotate_apply (G := G))

/-- The cyclic column homology equivalence sends a represented class to the relabelled class. -/
@[simp]
theorem fullyBlockedHomologyEquiv_relabelColumns_finRotate_apply_mk
    (c : G.fullyBlockedCycles) :
    G.fullyBlockedHomologyEquiv_relabelColumns_finRotate
        (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (G.fullyBlockedCyclesEquiv (G.relabelColumns (finRotate n))
          (GridChain.relabelColumnsEquiv (finRotate n))
          (fullyBlockedDifferential_relabelColumns_finRotate_apply (G := G)) c) := by
  exact fullyBlockedHomologyEquivOfIntertwining_apply_mk
    (G := G) (G' := G.relabelColumns (finRotate n))
    (e := GridChain.relabelColumnsEquiv (finRotate n))
    (he := fullyBlockedDifferential_relabelColumns_finRotate_apply (G := G)) c

end Cyclic

end GridDiagram

end TauCeti
