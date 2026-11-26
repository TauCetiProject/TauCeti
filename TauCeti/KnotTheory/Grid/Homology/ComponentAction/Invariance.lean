/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Invariance
public import TauCeti.KnotTheory.Grid.Homology.ComponentAction.Naturality
public import TauCeti.KnotTheory.Grid.Homology.Transpose
public import TauCeti.KnotTheory.Grid.Move.Stabilization
public import TauCeti.KnotTheory.Grid.Stabilization.Components
public import TauCeti.KnotTheory.Grid.Stabilization.Homology
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Basic

/-!
# Invariance of `GH⁻` with one variable per link component

For a grid diagram `G` presenting a link with `ℓ` components, unblocked grid homology `GH⁻(G)` is a
module over the polynomial ring `R[V₁, …, V_ℓ]` with one variable for each link component
(`GridDiagram.unblockedHomologyComponentModule`). This file proves that this module does not
depend on the presenting diagram: grid diagrams connected by grid moves have isomorphic `GH⁻` over
the component polynomial rings, along a bijection of their components
(`GridDiagram.unblockedHomologyComponentIsomorphic_of_movesTo`). For a knot the component ring has
a single variable, which acts as `U` (`GridDiagram.IsKnot.aeval_smul_unblockedHomologyComponent`);
for links the statement keeps the variables of different components apart, which the knot form
`GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_movesTo` cannot express.

Each elementary move already has a specified map on `GH⁻`, semilinear along a renaming
`κ` of the column variables: the cyclic permutations, the pentagon map of a column commutation
(along the exchange of the two columns), the diagonal reflection (along the `O`-marking
permutation), and the two corner `X`-stabilizations (along `Fin.predAbove`, which merges the two
variables of the new block). Each move also comes with a bijection `e` of link components with
`e (componentOfColumn c) = componentOfColumn (κ c)`, so by
`GridDiagram.map_smul_unblockedHomologyComponent` the map is semilinear along the renaming of
component variables by `e`. A row commutation is a column commutation of the diagonal reflections,
and every stabilization is connected to one of the two corner stabilizations by cyclic
permutations and commutations (`GridDiagram.IsStabilization.exists_commutationMovesTo`).

The statement concerns the module structure only. It does not record the Maslov grading or the
Alexander multi-grading, and it does not identify the maps attached to different move sequences.

## Main definitions

* `TauCeti.GridDiagram.UnblockedHomologyComponentIsomorphic`: `GH⁻(G)` and `GH⁻(G')` are
  isomorphic, semilinearly along the renaming of component variables by some bijection of link
  components.

## Main results

* `TauCeti.GridDiagram.UnblockedHomologyComponentIsomorphic.of_bijective`: a bijective map that is
  semilinear along a renaming of column variables compatible with a bijection of components gives
  the relation.
* `TauCeti.GridDiagram.unblockedHomologyComponentIsomorphic_of_isMove`: every elementary grid move
  preserves `GH⁻` with its component action.
* `TauCeti.GridDiagram.unblockedHomologyComponentIsomorphic_of_movesTo`: **invariance of `GH⁻` as
  a module over one variable per component**, for grid diagrams connected by grid moves.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 5 (invariance under grid
moves) and Chapter 8 (grid homology for links, with one variable per link component).
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram

variable {n m l : ℕ} (G : GridDiagram n) (G' : GridDiagram m) (G'' : GridDiagram l)
  (R : Type*) [CommRing R] [CharP R 2]

/-- The unblocked grid homologies of two grid diagrams are **isomorphic over the component
polynomial rings**: for some bijection `e` of link components there is an equivalence
`GH⁻(G) ≃ GH⁻(G')` that is semilinear along the renaming of component variables by `e`. The two
diagrams may have different sizes. -/
def UnblockedHomologyComponentIsomorphic : Prop :=
  letI := G.unblockedHomologyComponentModule R
  letI := G'.unblockedHomologyComponentModule R
  ∃ e : G.Components ≃ G'.Components,
    Nonempty (G.unblockedHomology R ≃ₛₗ[((renameEquiv R e).toRingEquiv :
      MvPolynomial G.Components R →+* MvPolynomial G'.Components R)] G'.unblockedHomology R)

variable {G G' G'' R}

/-- Unfold `UnblockedHomologyComponentIsomorphic` to the existence of a component bijection and a
semilinear equivalence. -/
theorem unblockedHomologyComponentIsomorphic_def :
    G.UnblockedHomologyComponentIsomorphic G' R ↔
      letI := G.unblockedHomologyComponentModule R
      letI := G'.unblockedHomologyComponentModule R
      ∃ e : G.Components ≃ G'.Components,
        Nonempty (G.unblockedHomology R ≃ₛₗ[((renameEquiv R e).toRingEquiv :
          MvPolynomial G.Components R →+* MvPolynomial G'.Components R)]
            G'.unblockedHomology R) :=
  Iff.rfl

namespace UnblockedHomologyComponentIsomorphic

variable (G R) in
/-- Every grid diagram has `GH⁻` isomorphic to itself over its component polynomial ring. -/
theorem refl : G.UnblockedHomologyComponentIsomorphic G R := by
  let _ := G.unblockedHomologyComponentModule R
  refine ⟨Equiv.refl _, ⟨{ LinearEquiv.refl R (G.unblockedHomology R) with
    map_smul' := fun q x ↦ ?_ }⟩⟩
  simp

/-- Isomorphism over the component polynomial rings is symmetric: the inverse equivalence is
semilinear along the inverse renaming. -/
theorem symm (h : G.UnblockedHomologyComponentIsomorphic G' R) :
    G'.UnblockedHomologyComponentIsomorphic G R := by
  let _ := G.unblockedHomologyComponentModule R
  let _ := G'.unblockedHomologyComponentModule R
  obtain ⟨e, ⟨f⟩⟩ := h
  refine ⟨e.symm, ⟨{ f.symm.toAddEquiv with map_smul' := fun q y ↦ ?_ }⟩⟩
  have hσ : (renameEquiv R e).toRingEquiv.symm q = (renameEquiv R e.symm).toRingEquiv q := by
    rw [AlgEquiv.toRingEquiv_symm, renameEquiv_symm]
  exact (f.symm.map_smulₛₗ q y).trans (congrArg (· • f.symm y) hσ)

/-- Isomorphism over the component polynomial rings is transitive: semilinear equivalences
compose along the composite renaming. -/
theorem trans (h : G.UnblockedHomologyComponentIsomorphic G' R)
    (h' : G'.UnblockedHomologyComponentIsomorphic G'' R) :
    G.UnblockedHomologyComponentIsomorphic G'' R := by
  let _ := G.unblockedHomologyComponentModule R
  let _ := G'.unblockedHomologyComponentModule R
  let _ := G''.unblockedHomologyComponentModule R
  obtain ⟨e, ⟨f⟩⟩ := h
  obtain ⟨e', ⟨f'⟩⟩ := h'
  refine ⟨e.trans e', ⟨{ f.toAddEquiv.trans f'.toAddEquiv with map_smul' := fun q x ↦ ?_ }⟩⟩
  simp [rename_rename, Function.comp_def]

/-- A bijection `f : GH⁻(G) → GH⁻(G')` that is semilinear along the renaming of column variables
by `κ` gives isomorphic homologies over the component polynomial rings, provided `κ` is compatible
with a bijection `e` of link components: `e` sends the component of each column `c` to the
component of `κ c`. -/
theorem of_bijective (e : G.Components ≃ G'.Components) {κ : Fin n → Fin m}
    (he : ∀ c, e (G.componentOfColumn c) = G'.componentOfColumn (κ c))
    (f : G.unblockedHomology R →+ G'.unblockedHomology R) (hf : Function.Bijective f)
    (hsmul : ∀ (p : MvPolynomial (Fin n) R) x, f (p • x) = rename κ p • f x) :
    G.UnblockedHomologyComponentIsomorphic G' R := by
  let _ := G.unblockedHomologyComponentModule R
  let _ := G'.unblockedHomologyComponentModule R
  refine ⟨e, ⟨{ AddEquiv.ofBijective f hf with map_smul' := fun q x ↦ ?_ }⟩⟩
  simpa using map_smul_unblockedHomologyComponent f he hsmul q x

end UnblockedHomologyComponentIsomorphic

/-! ### The elementary moves -/

variable (G R)

/-- A cyclic permutation of the rows preserves `GH⁻` with its component action. -/
theorem unblockedHomologyComponentIsomorphic_relabelRows_finRotate :
    G.UnblockedHomologyComponentIsomorphic (G.relabelRows (finRotate n)) R :=
  ⟨_, ⟨G.unblockedHomologyComponentRelabelRowsFinRotateEquiv R⟩⟩

/-- A cyclic permutation of the columns preserves `GH⁻` with its component action. -/
theorem unblockedHomologyComponentIsomorphic_relabelColumns_finRotate :
    G.UnblockedHomologyComponentIsomorphic (G.relabelColumns (finRotate n)) R :=
  ⟨_, ⟨G.unblockedHomologyComponentRelabelColumnsFinRotateEquiv R⟩⟩

/-- The diagonal reflection preserves `GH⁻` with its component action: the reflection map is
semilinear along the renaming of columns by the `O`-marking permutation, which matches the
component equivalence `componentsTransposeEquiv`. -/
theorem unblockedHomologyComponentIsomorphic_transpose :
    G.UnblockedHomologyComponentIsomorphic G.transpose R :=
  .of_bijective G.componentsTransposeEquiv (κ := G.O.toPerm)
    G.componentsTransposeEquiv_componentOfColumn
    (G.unblockedHomologyTransposeEquiv R).toAddEquiv.toAddMonoidHom
    (G.unblockedHomologyTransposeEquiv R).bijective
    fun p x ↦ (G.unblockedHomologyTransposeEquiv R).map_smulₛₗ p x

/-- A validated column commutation preserves `GH⁻` with its component action: the pentagon map is
bijective and semilinear along the exchange of the two columns. -/
theorem unblockedHomologyComponentIsomorphic_swapColumns (C : ColumnCommutationData G) :
    G.UnblockedHomologyComponentIsomorphic (G.swapColumns C.column (finRotate n C.column)) R :=
  .of_bijective (G.componentsRelabelColumnsEquiv (Equiv.swap C.column (finRotate n C.column)))
    (κ := Equiv.swap C.column (finRotate n C.column))
    (G.componentsRelabelColumnsEquiv_componentOfColumn _)
    (G.unblockedHomologyCommutationMap R C).toAddMonoidHom
    (G.unblockedHomologyCommutationMap_bijective C R)
    fun p x ↦ (G.unblockedHomologyCommutationMap R C).map_smulₛₗ p x

variable {G R}

/-- An elementary column commutation preserves `GH⁻` with its component action. -/
theorem unblockedHomologyComponentIsomorphic_of_isColumnCommutation {G' : GridDiagram n}
    (h : IsColumnCommutation G G') : G.UnblockedHomologyComponentIsomorphic G' R := by
  obtain ⟨C, rfl⟩ := isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact unblockedHomologyComponentIsomorphic_swapColumns G R C

/-- An elementary commutation preserves `GH⁻` with its component action; a row commutation is a
column commutation of the diagonal reflections. -/
theorem unblockedHomologyComponentIsomorphic_of_isCommutation {G' : GridDiagram n}
    (h : IsCommutation G G') : G.UnblockedHomologyComponentIsomorphic G' R := by
  rcases (isCommutation_iff G G').mp h with h | h
  · exact (unblockedHomologyComponentIsomorphic_transpose G R).trans
      ((unblockedHomologyComponentIsomorphic_of_isColumnCommutation
        ((isColumnCommutation_transpose G G').mpr h)).trans
        (unblockedHomologyComponentIsomorphic_transpose G' R).symm)
  · exact unblockedHomologyComponentIsomorphic_of_isColumnCommutation h

/-- Cyclic permutations and commutations preserve `GH⁻` with its component action. -/
theorem unblockedHomologyComponentIsomorphic_of_commutationMovesTo {G' : GridDiagram n}
    (h : G.CommutationMovesTo G') : G.UnblockedHomologyComponentIsomorphic G' R :=
  h.induction_on (unblockedHomologyComponentIsomorphic_relabelRows_finRotate · R)
    (unblockedHomologyComponentIsomorphic_relabelColumns_finRotate · R)
    unblockedHomologyComponentIsomorphic_of_isCommutation (.refl · R) (fun _ ih ↦ ih.symm)
    fun _ _ ih ih' ↦ ih.trans ih'

variable (G R)

/-- The south-west `X`-stabilization preserves `GH⁻` with its component action: the stabilization
map is bijective and semilinear along `Fin.predAbove`, which sends both columns of the new block
to the split column. -/
theorem unblockedHomologyComponentIsomorphic_stabilizeX (s : Fin n) :
    G.UnblockedHomologyComponentIsomorphic (G.stabilizeX s.castSucc (G.X s).castSucc s) R := by
  refine (UnblockedHomologyComponentIsomorphic.of_bijective
    (G.componentsStabilizeXEquiv s.castSucc (G.X s).castSucc s).symm (κ := s.predAbove)
    (fun c ↦ ?_) (G.stabilizeXHomologyMap s R).toAddMonoidHom
    (G.stabilizeXHomologyMap_bijective s R)
    fun p x ↦ (G.stabilizeXHomologyMap s R).map_smulₛₗ p x).symm
  by_cases hc : c = s.castSucc
  · subst hc
    simp
  · obtain ⟨d, rfl⟩ := Fin.exists_succAbove_eq hc
    simp [Fin.predAbove_succAbove]

/-- The north-east `X`-stabilization preserves `GH⁻` with its component action. -/
theorem unblockedHomologyComponentIsomorphic_stabilizeX_succ (s : Fin n) :
    G.UnblockedHomologyComponentIsomorphic (G.stabilizeX s.succ (G.X s).succ s) R := by
  refine (UnblockedHomologyComponentIsomorphic.of_bijective
    (G.componentsStabilizeXEquiv s.succ (G.X s).succ s).symm (κ := s.predAbove)
    (fun c ↦ ?_) (G.stabilizeXSuccHomologyMap s R).toAddMonoidHom
    (G.stabilizeXSuccHomologyMap_bijective s R)
    fun p x ↦ (G.stabilizeXSuccHomologyMap s R).map_smulₛₗ p x).symm
  by_cases hc : c = s.succ
  · subst hc
    simp
  · obtain ⟨d, rfl⟩ := Fin.exists_succAbove_eq hc
    simp [Fin.predAbove_succ_succAbove]

variable {G R}

/-- Every elementary stabilization preserves `GH⁻` with its component action. -/
theorem unblockedHomologyComponentIsomorphic_of_isStabilization {G' : GridDiagram (n + 1)}
    (h : IsStabilization G G') : G.UnblockedHomologyComponentIsomorphic G' R := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · exact (unblockedHomologyComponentIsomorphic_stabilizeX G R s).trans
      (unblockedHomologyComponentIsomorphic_of_commutationMovesTo hs.symm)
  · exact (unblockedHomologyComponentIsomorphic_stabilizeX_succ G R s).trans
      (unblockedHomologyComponentIsomorphic_of_commutationMovesTo hs.symm)

/-- Each elementary grid move preserves `GH⁻` with its component action, including a
destabilization. -/
theorem unblockedHomologyComponentIsomorphic_of_isMove (h : IsMove ⟨n, G⟩ ⟨m, G'⟩) :
    G.UnblockedHomologyComponentIsomorphic G' R := by
  cases h with
  | cyclicRows h =>
    rcases h with rfl | rfl
    · exact unblockedHomologyComponentIsomorphic_relabelRows_finRotate G R
    · exact (unblockedHomologyComponentIsomorphic_relabelRows_finRotate _ R).symm
  | cyclicColumns h =>
    rcases h with rfl | rfl
    · exact unblockedHomologyComponentIsomorphic_relabelColumns_finRotate G R
    · exact (unblockedHomologyComponentIsomorphic_relabelColumns_finRotate _ R).symm
  | commutation h => exact unblockedHomologyComponentIsomorphic_of_isCommutation h
  | stabilization h => exact unblockedHomologyComponentIsomorphic_of_isStabilization h
  | destabilization h =>
    exact (unblockedHomologyComponentIsomorphic_of_isStabilization
      ((isDestabilization_iff_isStabilization _ _).mp h)).symm

/-- **Invariance of `GH⁻` with one variable per link component.** Grid diagrams connected by grid
moves have isomorphic unblocked grid homologies over the component polynomial rings, semilinearly
along the renaming of component variables by a bijection of their link components. -/
theorem unblockedHomologyComponentIsomorphic_of_movesTo (h : G.MovesTo G') :
    G.UnblockedHomologyComponentIsomorphic G' R :=
  h.induction_on
    (motive := fun A B ↦ A.2.UnblockedHomologyComponentIsomorphic B.2 R)
    unblockedHomologyComponentIsomorphic_of_isMove (fun A ↦ .refl A.2 R) (fun _ ih ↦ ih.symm)
    fun _ _ ih ih' ↦ ih.trans ih'

end TauCeti.GridDiagram
