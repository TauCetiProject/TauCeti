/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Homology
public import TauCeti.KnotTheory.Grid.SimplyBlocked.Map

/-!
# The simply blocked stabilization chain map

An `X`-stabilization inserts a new `O`-marking and carries each old `O`-marking to its
inserted column. Blocking one of those old markings specializes the unblocked stabilization
map to a semilinear chain map. Its scalar homomorphism first merges the two stabilization
variables and then kills the chosen old variable; it need not be a renaming of variables.

The specialization identity characterizes the map on all chains and proves that it commutes
with the differentials. These constructions apply to arbitrary grid diagrams. For knots,
blocking one `O`-marking gives the simply blocked theory.

The specialized map is again a quasi-isomorphism. Specialization at a variable `V` is the
quotient of `GC⁻` by multiplication by `V`, which is injective, and the unblocked stabilization
map carries the variable of the transported marking to that of the original marking. So the
unblocked and specialized maps form a morphism of short exact sequences of complexes, and the
five lemma for their long exact homology sequences
(`AddMonoidHom.exists_mem_ker_sub_mem_range_of_exact` and
`AddMonoidHom.mem_range_of_map_mem_range_of_exact`) transfers stabilization invariance of `GH⁻`
to the specialized complexes.

## Main results

* `TauCeti.GridDiagram.simplyBlockedStabilizeXMap_simplyBlockedSpecialization`: the specialized
  map is the descent of the unblocked stabilization map through specialization.
* `TauCeti.GridDiagram.simplyBlockedStabilizeXMap_simplyBlockedDifferential`: it is a chain map.
* `TauCeti.GridDiagram.exists_sub_simplyBlockedStabilizeXMap_mem_range` and
  `TauCeti.GridDiagram.mem_range_of_simplyBlockedStabilizeXMap_mem_range`: it induces a bijection
  on homology, in elementwise form.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 3.2 (arXiv:math/0610559).
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram

variable {n : ℕ} (s i : Fin n) (R : Type*)

section Semiring

variable [CommSemiring R]

local notation "j" => s.castSucc.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The coefficient homomorphism of stabilization after blocking the transported old marking.
Merge the stabilization columns using `s.predAbove`, then kill the variable of column `i`. -/
noncomputable def simplyBlockedStabilizeXRingHom : S →+* A :=
  simplyBlockedRingHomAlong R s.predAbove i j

/-- A surviving source variable is merged and then specialized in the old grid. In particular,
when `i = s`, the other variable of the stabilization block also maps to zero. -/
@[simp]
theorem simplyBlockedStabilizeXRingHom_X (c : {c : Fin (n + 1) // c ≠ j}) :
    simplyBlockedStabilizeXRingHom s i R (MvPolynomial.X c) =
      simplyBlockedRingHom R i (MvPolynomial.X (s.predAbove c)) := by
  simp [simplyBlockedStabilizeXRingHom]

/-- Stabilization leaves ground-ring coefficients unchanged after blocking. -/
@[simp]
theorem simplyBlockedStabilizeXRingHom_C (r : R) :
    simplyBlockedStabilizeXRingHom s i R (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [simplyBlockedStabilizeXRingHom]

/-- Merging columns commutes with blocking the transported old marking. -/
theorem simplyBlockedStabilizeXRingHom_specialization (p : MvPolynomial (Fin (n + 1)) R) :
    simplyBlockedStabilizeXRingHom s i R (simplyBlockedRingHom R j p) =
      simplyBlockedRingHom R i (rename s.predAbove p) :=
  simplyBlockedRingHomAlong_specialization R s.predAbove i j (by simp [Fin.predAbove_succAbove]) p

end Semiring

variable (G : GridDiagram n) [CommRing R]

local notation "j" => s.castSucc.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The stabilization comparison with the transported old `O`-marking blocked. Its image on a
generator is the specialization of the unblocked stabilization comparison. -/
noncomputable def simplyBlockedStabilizeXMap :
    GridChainHat R (n + 1) j →ₛₗ[simplyBlockedStabilizeXRingHom s i R] GridChainHat R n i :=
  simplyBlockedMapAlong R s.predAbove i j (G.stabilizeXChainMap s R)

/-- The specialized stabilization map on a single supported coefficient. -/
theorem simplyBlockedStabilizeXMap_single (x : GridState (n + 1)) (p : S) :
    G.simplyBlockedStabilizeXMap s i R (Finsupp.single x p) =
      simplyBlockedStabilizeXRingHom s i R p •
        simplyBlockedSpecialization R i (G.stabilizeXChainMap s R (Finsupp.single x 1)) :=
  simplyBlockedMapAlong_single R s.predAbove i j (G.stabilizeXChainMap s R) x p

/-- The matrix formula for the specialized stabilization comparison. -/
@[simp]
theorem simplyBlockedStabilizeXMap_apply_apply (c : GridChainHat R (n + 1) j)
    (y : GridState n) :
    G.simplyBlockedStabilizeXMap s i R c y = c.sum fun x p =>
      simplyBlockedStabilizeXRingHom s i R p *
        simplyBlockedRingHom R i (G.stabilizeXChainMap s R (Finsupp.single x 1) y) :=
  simplyBlockedMapAlong_apply_apply R s.predAbove i j (G.stabilizeXChainMap s R) c y

/-- The simply blocked comparison is the descent of the unblocked stabilization map through
coefficient specialization. -/
@[simp]
theorem simplyBlockedStabilizeXMap_simplyBlockedSpecialization (c : GridChainMinus R (n + 1)) :
    G.simplyBlockedStabilizeXMap s i R (simplyBlockedSpecialization R j c) =
      simplyBlockedSpecialization R i (G.stabilizeXChainMap s R c) :=
  simplyBlockedMapAlong_specialization R s.predAbove i j (G.stabilizeXChainMap s R)
    (by simp [Fin.predAbove_succAbove]) c

variable [CharP R 2]

/-- Stabilization commutes with the simply blocked differentials. -/
theorem simplyBlockedStabilizeXMap_simplyBlockedDifferential (c : GridChainHat R (n + 1) j) :
    G.simplyBlockedStabilizeXMap s i R
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).simplyBlockedDifferential R j c) =
      G.simplyBlockedDifferential R i (G.simplyBlockedStabilizeXMap s i R c) :=
  simplyBlockedMapAlong_differential R s.predAbove i j (G.stabilizeXChainMap s R) G _
    (by simp [Fin.predAbove_succAbove]) (G.stabilizeXChainMap_unblockedDifferential s R) c

/-! ### Quasi-isomorphism after blocking -/

local notation "G'" => GridDiagram.stabilizeX G (Fin.castSucc s)
  (Fin.castSucc (GridDiagram.X G s)) s

/-- Every simply blocked cycle of `G` differs from the image of a simply blocked cycle of the
stabilized diagram by a boundary. -/
theorem exists_sub_simplyBlockedStabilizeXMap_mem_range {y : GridChainHat R n i}
    (hy : y ∈ LinearMap.ker (G.simplyBlockedDifferential R i)) :
    ∃ x ∈ LinearMap.ker ((G').simplyBlockedDifferential R j),
      y - G.simplyBlockedStabilizeXMap s i R x ∈
        LinearMap.range (G.simplyBlockedDifferential R i) :=
  exists_sub_simplyBlockedMapAlong_mem_range R s.predAbove i j
    (G.stabilizeXChainMap s R) G _ (by simp [Fin.predAbove_succAbove])
    (G.stabilizeXChainMap_unblockedDifferential s R)
    (fun _ hc => G.exists_sub_stabilizeXChainMap_mem_range s R hc)
    (fun _ hx h => G.mem_range_of_stabilizeXChainMap_mem_range s R hx h) hy

/-- A simply blocked cycle of the stabilized diagram whose image in `G` is a boundary is itself a
boundary. -/
theorem mem_range_of_simplyBlockedStabilizeXMap_mem_range {x : GridChainHat R (n + 1) j}
    (hx : x ∈ LinearMap.ker ((G').simplyBlockedDifferential R j))
    (h : G.simplyBlockedStabilizeXMap s i R x ∈
      LinearMap.range (G.simplyBlockedDifferential R i)) :
    x ∈ LinearMap.range ((G').simplyBlockedDifferential R j) :=
  mem_range_of_simplyBlockedMapAlong_mem_range R s.predAbove i j
    (G.stabilizeXChainMap s R) G _ (by simp [Fin.predAbove_succAbove])
    (G.stabilizeXChainMap_unblockedDifferential s R)
    (fun _ hc => G.exists_sub_stabilizeXChainMap_mem_range s R hc)
    (fun _ hx h => G.mem_range_of_stabilizeXChainMap_mem_range s R hx h) hx h

end TauCeti.GridDiagram
