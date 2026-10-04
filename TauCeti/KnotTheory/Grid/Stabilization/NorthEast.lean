/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.HalfTurn
public import TauCeti.KnotTheory.Grid.Stabilization.Homology

/-!
# Stabilization invariance of `GH⁻` for the north-east corner

Up to cyclic permutations and commutations, every grid stabilization is one of two corner types
(`GridDiagram.IsStabilization.exists_commutationMovesTo`): for a column `s` of `G`, either
`G.stabilizeX s.castSucc (G.X s).castSucc s`, whose new `O`-marking is the south-west corner of
the new block, or `G' = G.stabilizeX s.succ (G.X s).succ s`, whose new `O`-marking is the
north-east corner. The first is treated in `Stabilization/Homology.lean`. This file treats the
second by the half-turn of the torus, which exchanges the two corners
(`GridDiagram.rotate_stabilizeX_succ`): the half-turn of `G'` is the south-west stabilization of
`G.rotate` at the column `s.rev`.

Write `A = R[V₀, …, V_{n-1}]` and `S = R[V₀, …, V_n]`. Conjugating the south-west stabilization
chain map of `G.rotate` by the half-turns `GC⁻(G') → GC⁻(G'.rotate)` and
`GC⁻(G.rotate) → GC⁻(G)` gives a chain map `GC⁻(G') → GC⁻(G)`
(`GridDiagram.stabilizeXSuccChainMap`). The renamings of the variables along `Fin.rev` on both
sides cancel against the merging of variables along `s.rev.predAbove`, so the chain map is
semilinear along the renaming `S → A` along `s.predAbove`, which merges the two variables of the
columns `s.castSucc` and `s.succ` of the new block into `V_s`, exactly as for the south-west
corner. The induced map `GH⁻(G') → GH⁻(G)` (`GridDiagram.stabilizeXSuccHomologyMap`) is a
composite of two half-turn equivalences and the south-west stabilization map of `G.rotate`, so
it is bijective.

The Alexander grading, and hence the invariant `τ`, is not treated here: that needs the
invariance of the gradings under the half-turn.

## Main definitions

* `TauCeti.GridDiagram.stabilizeXSuccChainMap`: the chain map `GC⁻(G') → GC⁻(G)` of the
  north-east stabilization, as a semilinear map.
* `TauCeti.GridDiagram.stabilizeXSuccHomologyMap`: the induced semilinear map
  `GH⁻(G') → GH⁻(G)`.

## Main results

* `TauCeti.GridDiagram.stabilizeXSuccChainMap_unblockedDifferential`: `stabilizeXSuccChainMap`
  commutes with the unblocked differentials.
* `TauCeti.GridDiagram.stabilizeXSuccHomologyMap_unblockedHomologyClass`: the class of a cycle
  `z` goes to the class of `stabilizeXSuccChainMap z`.
* `TauCeti.GridDiagram.stabilizeXSuccHomologyMap_bijective`: **stabilization invariance of
  `GH⁻` for the north-east corner**, the map on homology is bijective.

## References

Stabilization invariance of grid homology is Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Section 5.2, where the stabilization types other than the one treated directly are
reduced to it by the symmetries of grid diagrams of Chapter 3.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

local notation "A" => MvPolynomial (Fin n) R
local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- **The chain map of the north-east `X`-stabilization.** On a chain `c` of
`GC⁻(G.stabilizeX s.succ (G.X s).succ s)` it is the half-turn of the south-west stabilization
chain map of `G.rotate` at the column `s.rev`, applied to the half-turn of `c`. It is semilinear
along the renaming `S → A` along `s.predAbove`. -/
noncomputable def stabilizeXSuccChainMap :
    GridChainMinus R (n + 1) →ₛₗ[(↑(rename (R := R) s.predAbove) : S →+* A)]
      GridChainMinus R n where
  toFun c := GridChain.halfTurnRenameEquiv R
    (G.rotate.stabilizeXChainMap s.rev R (GridChain.halfTurnRenameEquiv R c))
  map_add' c d := by simp only [map_add]
  map_smul' p c := by
    simp only [map_smulₛₗ, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, renameEquiv_apply,
      rename_rename, Function.comp_def, Fin.revPerm_apply, Fin.rev_predAbove, Fin.rev_rev]

/-- `stabilizeXSuccChainMap` conjugates the south-west stabilization chain map of `G.rotate` by
the half-turns. -/
theorem stabilizeXSuccChainMap_apply (c : GridChainMinus R (n + 1)) :
    G.stabilizeXSuccChainMap s R c = GridChain.halfTurnRenameEquiv R
      (G.rotate.stabilizeXChainMap s.rev R (GridChain.halfTurnRenameEquiv R c)) :=
  (rfl)

/-- The half-turn intertwines the unblocked differentials of the north-east stabilization of `G`
and of the south-west stabilization of `G.rotate`. -/
private theorem unblockedDifferential_stabilizeX_rotate_halfTurnRenameEquiv
    (c : GridChainMinus R (n + 1)) :
    (G.rotate.stabilizeX s.rev.castSucc (G.rotate.X s.rev).castSucc s.rev).unblockedDifferential R
        (GridChain.halfTurnRenameEquiv R c) =
      GridChain.halfTurnRenameEquiv R
        ((G.stabilizeX s.succ (G.X s).succ s).unblockedDifferential R c) := by
  rw [← rotate_stabilizeX_succ]
  exact unblockedDifferential_rotate_halfTurnRenameEquiv _ R c

variable [CharP R 2]

/-- **`stabilizeXSuccChainMap` is a chain map**: it intertwines the unblocked differentials of
the north-east stabilization `G.stabilizeX s.succ (G.X s).succ s` and of `G`. -/
theorem stabilizeXSuccChainMap_unblockedDifferential (c : GridChainMinus R (n + 1)) :
    G.stabilizeXSuccChainMap s R
        ((G.stabilizeX s.succ (G.X s).succ s).unblockedDifferential R c) =
      G.unblockedDifferential R (G.stabilizeXSuccChainMap s R c) := by
  rw [stabilizeXSuccChainMap_apply, stabilizeXSuccChainMap_apply,
    ← unblockedDifferential_stabilizeX_rotate_halfTurnRenameEquiv,
    stabilizeXChainMap_unblockedDifferential, unblockedDifferential_halfTurnRenameEquiv]

/-- `stabilizeXSuccChainMap` sends cycles to cycles. -/
theorem stabilizeXSuccChainMap_mem_ker {c : GridChainMinus R (n + 1)}
    (hc : c ∈ LinearMap.ker ((G.stabilizeX s.succ (G.X s).succ s).unblockedDifferential R)) :
    G.stabilizeXSuccChainMap s R c ∈ LinearMap.ker (G.unblockedDifferential R) := by
  rw [LinearMap.mem_ker] at hc ⊢
  rw [← stabilizeXSuccChainMap_unblockedDifferential, hc, map_zero]

/-- The half-turn from the homology of the north-east stabilization of `G` to that of the
south-west stabilization of `G.rotate`. -/
private noncomputable def stabilizeXSuccSourceEquiv :
    (G.stabilizeX s.succ (G.X s).succ s).unblockedHomology R ≃ₛₗ[
      ((renameEquiv R (Fin.revPerm (n := n + 1))).toRingEquiv : S →+* S)]
      (G.rotate.stabilizeX s.rev.castSucc (G.rotate.X s.rev).castSucc s.rev).unblockedHomology R :=
  (G.stabilizeX s.succ (G.X s).succ s).unblockedHomologyEquivOfIntertwining R _
    (GridChain.halfTurnRenameEquiv R)
    (G.unblockedDifferential_stabilizeX_rotate_halfTurnRenameEquiv s R)

/-- **The map of the north-east `X`-stabilization on unblocked grid homology**,
`GH⁻(G.stabilizeX s.succ (G.X s).succ s) → GH⁻(G)`: the half-turn of the south-west
stabilization map of `G.rotate`. It is semilinear along the renaming `S → A` along
`s.predAbove`, and it sends the class of a cycle `z` to the class of `stabilizeXSuccChainMap z`
(`stabilizeXSuccHomologyMap_unblockedHomologyClass`). -/
noncomputable def stabilizeXSuccHomologyMap :
    (G.stabilizeX s.succ (G.X s).succ s).unblockedHomology R →ₛₗ[
      (↑(rename (R := R) s.predAbove) : S →+* A)] G.unblockedHomology R where
  toFun y := (G.unblockedHomologyRotateEquiv R).symm
    (G.rotate.stabilizeXHomologyMap s.rev R (G.stabilizeXSuccSourceEquiv s R y))
  map_add' y z := by simp only [map_add]
  map_smul' p y := by
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ]
    congr 1
    simp only [RingHom.coe_coe, AlgEquiv.toRingEquiv_symm, renameEquiv_symm,
      Fin.revPerm_symm, AlgEquiv.coe_toRingEquiv, renameEquiv_apply,
      rename_rename, Function.comp_def, Fin.revPerm_apply, Fin.rev_predAbove, Fin.rev_rev]

/-- `stabilizeXSuccHomologyMap` sends the class of a cycle `z` to the class of
`stabilizeXSuccChainMap z`. -/
@[simp]
theorem stabilizeXSuccHomologyMap_unblockedHomologyClass
    (z : LinearMap.ker ((G.stabilizeX s.succ (G.X s).succ s).unblockedDifferential R)) :
    G.stabilizeXSuccHomologyMap s R
        ((G.stabilizeX s.succ (G.X s).succ s).unblockedHomologyClass R z) =
      G.unblockedHomologyClass R
        ⟨G.stabilizeXSuccChainMap s R z, G.stabilizeXSuccChainMap_mem_ker s R z.2⟩ := by
  simp only [stabilizeXSuccHomologyMap, LinearMap.coe_mk, AddHom.coe_mk,
    stabilizeXSuccSourceEquiv, unblockedHomologyEquivOfIntertwining_unblockedHomologyClass,
    unblockedHomologyRotateEquiv_symm_unblockedHomologyClass,
    stabilizeXHomologyMap_unblockedHomologyClass, stabilizeXSuccChainMap_apply]

/-- **Stabilization invariance of `GH⁻` for the north-east corner.** The map
`GH⁻(G.stabilizeX s.succ (G.X s).succ s) → GH⁻(G)` induced by the stabilization chain map is
bijective. -/
theorem stabilizeXSuccHomologyMap_bijective :
    Function.Bijective (G.stabilizeXSuccHomologyMap s R) :=
  (G.unblockedHomologyRotateEquiv R).symm.bijective.comp
    ((G.rotate.stabilizeXHomologyMap_bijective s.rev R).comp
      (G.stabilizeXSuccSourceEquiv s R).bijective)

end GridDiagram

end TauCeti
