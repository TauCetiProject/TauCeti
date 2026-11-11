/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.FullyBlocked
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Equation

/-!
# The fully blocked commutation homotopy

Setting every marking variable to zero in the hexagon-counting commutation homotopy `H` of a
validated column commutation `C` retains exactly the empty hexagons avoiding every `O`- and
`X`-marking. The result is the hexagon map `H~` of the fully blocked complex `GC~(G)`, which is the
reduction of `H` modulo the variables (`LinearMap.constantCoeffReduction`).

Reducing the two homotopy equations of the unblocked complex modulo the variables gives their
fully blocked versions. Write `Φ~ : GC~(G) → GC~(G')` and `Ψ~ : GC~(G') → GC~(G)` for the fully
blocked pentagon maps of `C` and of its reverse, where `G'` is the commuted diagram, and `H~'` for
the fully blocked hexagon map of the reverse commutation. Then

  `∂~ ∘ H~ + H~ ∘ ∂~ = 1 + Ψ~ ∘ Φ~` and `∂~' ∘ H~' + H~' ∘ ∂~' = 1 + Φ~ ∘ Ψ~`,

so `Φ~` and `Ψ~` are mutually inverse chain homotopy equivalences of the fully blocked complexes.
Reduction modulo the variables needs no identification of the chain modules of `G` and of the
doubly commuted diagram, since the fully blocked chain module `GridChain (ZMod 2) n` does not
depend on the diagram.

## Main definitions

* `TauCeti.GridDiagram.fullyBlockedCommutationHomotopy`: the fully blocked hexagon map.

## Main results

* `TauCeti.GridDiagram.fullyBlockedCommutationHomotopy_mapRange_constantCoeff`: the fully blocked
  hexagon map is the reduction of the unblocked one.
* `TauCeti.GridDiagram.fullyBlockedDifferential_fullyBlockedCommutationHomotopy_add_eq`: the
  homotopy equation `∂~ ∘ H~ + H~ ∘ ∂~ = 1 + Ψ~ ∘ Φ~`.
* `TauCeti.GridDiagram.fullyBlockedDifferential_fullyBlockedCommutationHomotopy_reverse_add_eq`:
  the homotopy equation `∂~' ∘ H~' + H~' ∘ ∂~' = 1 + Φ~ ∘ Ψ~` on the commuted diagram.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.4 and 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The construction reduces the existing `GridDiagram.commutationHomotopy`
modulo the variables, as `GridDiagram.fullyBlockedCommutationMap` reduces the pentagon map.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]
  (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-- The fully blocked commutation homotopy: its matrix entries are the constant coefficients of
the hexagon coefficients of the commutation homotopy. It counts the empty hexagons carrying
neither `X`- nor `O`-markings, over any commutative coefficient semiring. -/
noncomputable def fullyBlockedCommutationHomotopy : GridChain R n →ₗ[R] GridChain R n :=
  (G.commutationHomotopy R C).constantCoeffReduction

/-- On a single generator, the fully blocked homotopy reads the constant hexagon coefficient. -/
theorem fullyBlockedCommutationHomotopy_single_apply (x y : GridState n) (r : R) :
    G.fullyBlockedCommutationHomotopy R C (Finsupp.single x r) y =
      r * constantCoeff (G.commutationHexagonCoefficient R C x y) := by
  rw [fullyBlockedCommutationHomotopy, LinearMap.constantCoeffReduction_single_apply,
    G.commutationHomotopy_single_apply]

/-- Taking constant coefficients commutes with the commutation homotopy. -/
@[simp]
theorem fullyBlockedCommutationHomotopy_mapRange_constantCoeff (c : GridChainMinus R n) :
    G.fullyBlockedCommutationHomotopy R C (c.mapRange constantCoeff (map_zero _)) =
      (G.commutationHomotopy R C c).mapRange constantCoeff (map_zero _) :=
  LinearMap.constantCoeffReduction_mapRange_constantCoeff _ c

/-- **The fully blocked homotopy equation.** The fully blocked hexagon map `H~` is a chain
homotopy between the identity of `GC~(G)` and the round trip `Ψ~ ∘ Φ~` through the commuted
diagram: `∂~ ∘ H~ + H~ ∘ ∂~ = 1 + Ψ~ ∘ Φ~`. -/
theorem fullyBlockedDifferential_fullyBlockedCommutationHomotopy_add_eq
    (c : GridChain (ZMod 2) n) :
    G.fullyBlockedDifferential (G.fullyBlockedCommutationHomotopy (ZMod 2) C c) +
        G.fullyBlockedCommutationHomotopy (ZMod 2) C (G.fullyBlockedDifferential c) =
      c + (G.swapColumns a b).fullyBlockedCommutationMap (ZMod 2) C.reverse
        (G.fullyBlockedCommutationMap (ZMod 2) C c) := by
  obtain ⟨c, rfl⟩ := Finsupp.mapRange_surjective _ (map_zero _)
    (fun r ↦ ⟨(MvPolynomial.C r : MvPolynomial (Fin n) (ZMod 2)), constantCoeff_C _ r⟩) c
  have h := congrArg (Finsupp.mapRange constantCoeff (map_zero _))
    (G.unblockedDifferential_commutationHomotopy_add_eq C (ZMod 2) c)
  simp only [Finsupp.mapRange_add (map_add constantCoeff)] at h
  simpa only [fullyBlockedCommutationHomotopy_mapRange_constantCoeff,
    fullyBlockedDifferential_mapRange_constantCoeff,
    fullyBlockedCommutationMap_mapRange_constantCoeff] using h

/-- **The fully blocked homotopy equation on the commuted diagram.** The fully blocked hexagon
map `H~'` of the reverse commutation is a chain homotopy between the identity of `GC~(G')` and the
round trip `Φ~ ∘ Ψ~` through `G`: `∂~' ∘ H~' + H~' ∘ ∂~' = 1 + Φ~ ∘ Ψ~`. -/
theorem fullyBlockedDifferential_fullyBlockedCommutationHomotopy_reverse_add_eq
    (c : GridChain (ZMod 2) n) :
    (G.swapColumns a b).fullyBlockedDifferential
          ((G.swapColumns a b).fullyBlockedCommutationHomotopy (ZMod 2) C.reverse c) +
        (G.swapColumns a b).fullyBlockedCommutationHomotopy (ZMod 2) C.reverse
          ((G.swapColumns a b).fullyBlockedDifferential c) =
      c + G.fullyBlockedCommutationMap (ZMod 2) C
        ((G.swapColumns a b).fullyBlockedCommutationMap (ZMod 2) C.reverse c) := by
  obtain ⟨c, rfl⟩ := Finsupp.mapRange_surjective _ (map_zero _)
    (fun r ↦ ⟨(MvPolynomial.C r : MvPolynomial (Fin n) (ZMod 2)), constantCoeff_C _ r⟩) c
  have h := congrArg (Finsupp.mapRange constantCoeff (map_zero _))
    (G.unblockedDifferential_commutationHomotopy_reverse_add_eq C (ZMod 2) c)
  simp only [Finsupp.mapRange_add (map_add constantCoeff)] at h
  simpa only [fullyBlockedCommutationHomotopy_mapRange_constantCoeff,
    fullyBlockedDifferential_mapRange_constantCoeff,
    fullyBlockedCommutationMap_mapRange_constantCoeff] using h

end TauCeti.GridDiagram
