/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# Rewriting carrier and base sets of classical relative CW complexes

Given a classical relative CW complex structure `I : Topology.RelCWComplex C D` in a topological
space `X` and set equalities `hC : C = C'` and `hD : D = D'`, `Topology.RelCWComplex.copy`
transports `I` to a `RelCWComplex C' D'` structure with unchanged cell types and characteristic
maps, mirroring `Topology.RelCWComplex.Subcomplex.copy`.

## Main declarations

* `Topology.RelCWComplex.copy`: transport a `RelCWComplex C D` along `C = C'` and `D = D'` while
  keeping `cell` and `map` definitionally unchanged.
* `Topology.RelCWComplex.copyCellEquiv`, `map_copy`, `openCell_copy`, `closedCell_copy`,
  `cellFrontier_copy`: cell equivalences and characteristic-map/cell-set identities for `copy`.
* `Topology.RelCWComplex.finiteDimensional_copy`, `finiteType_copy`, `finite_copy`: preservation
  of finiteness properties under `copy`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0.
-/

public section

noncomputable section

open Set Topology

namespace Topology.RelCWComplex

variable {X : Type*} [TopologicalSpace X] {C D : Set X}

/-- Copy a relative CW complex structure on `(C, D)` to equal sets `(C', D')`, keeping `cell` and
`map` definitionally unchanged. Useful to replace a carrier or base set with a definitionally
preferred equal set. -/
@[instance_reducible]
def copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C') (hD : D = D') :
    RelCWComplex C' D' where
  cell := I.cell
  map := I.map
  source_eq := I.source_eq
  continuousOn := I.continuousOn
  continuousOn_symm := I.continuousOn_symm
  pairwiseDisjoint' := I.pairwiseDisjoint'
  disjointBase' := hD ▸ I.disjointBase'
  mapsTo := hD ▸ I.mapsTo
  closed' := hC ▸ hD ▸ I.closed'
  isClosedBase := hD ▸ I.isClosedBase
  union' := hC ▸ hD ▸ I.union'

/-- The `n`-cells of `I.copy C' D' hC hD` are canonically equivalent to the `n`-cells of `I`. -/
def copyCellEquiv (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C') (hD : D = D') (n : ℕ) :
    @cell X _ C' D' (I.copy C' D' hC hD) n ≃ @cell X _ C D I n :=
  Equiv.refl _

theorem map_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C') (hD : D = D') (n : ℕ)
    (j : @cell X _ C' D' (I.copy C' D' hC hD) n) :
    @map X _ C' D' (I.copy C' D' hC hD) n j =
      @map X _ C D I n (I.copyCellEquiv C' D' hC hD n j) :=
  (rfl)

theorem openCell_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C') (hD : D = D') (n : ℕ)
    (j : @cell X _ C' D' (I.copy C' D' hC hD) n) :
    @openCell X _ C' D' (I.copy C' D' hC hD) n j =
      @openCell X _ C D I n (I.copyCellEquiv C' D' hC hD n j) :=
  (rfl)

theorem closedCell_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C') (hD : D = D') (n : ℕ)
    (j : @cell X _ C' D' (I.copy C' D' hC hD) n) :
    @closedCell X _ C' D' (I.copy C' D' hC hD) n j =
      @closedCell X _ C D I n (I.copyCellEquiv C' D' hC hD n j) :=
  (rfl)

theorem cellFrontier_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C') (hD : D = D')
    (n : ℕ) (j : @cell X _ C' D' (I.copy C' D' hC hD) n) :
    @cellFrontier X _ C' D' (I.copy C' D' hC hD) n j =
      @cellFrontier X _ C D I n (I.copyCellEquiv C' D' hC hD n j) :=
  (rfl)

/-- Copying a finite-dimensional relative CW complex along set equalities preserves
finite-dimensionality. -/
theorem finiteDimensional_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C') (hD : D = D')
    [@FiniteDimensional X _ C D I] :
    @FiniteDimensional X _ C' D' (I.copy C' D' hC hD) :=
  @FiniteDimensional.mk _ _ _ _ (I.copy C' D' hC hD) <| by
    filter_upwards [@FiniteDimensional.eventually_isEmpty_cell _ _ C D I _] with n _
    exact (I.copyCellEquiv C' D' hC hD n).isEmpty_congr.2 inferInstance

/-- Copying a relative CW complex of finite type along set equalities preserves finite type. -/
theorem finiteType_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C') (hD : D = D')
    [@FiniteType X _ C D I] :
    @FiniteType X _ C' D' (I.copy C' D' hC hD) :=
  @FiniteType.mk _ _ _ _ (I.copy C' D' hC hD) fun n ↦
    have := @FiniteType.finite_cell _ _ C D I _ n
    (I.copyCellEquiv C' D' hC hD n).finite_iff.2 inferInstance

/-- Copying a finite relative CW complex along set equalities preserves finiteness. -/
theorem finite_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C') (hD : D = D')
    [@Finite X _ C D I] :
    @Finite X _ C' D' (I.copy C' D' hC hD) :=
  @finite_of_finiteDimensional_finiteType _ _ _ _ (I.copy C' D' hC hD)
    (I.finiteDimensional_copy C' D' hC hD) (I.finiteType_copy C' D' hC hD)

end Topology.RelCWComplex
