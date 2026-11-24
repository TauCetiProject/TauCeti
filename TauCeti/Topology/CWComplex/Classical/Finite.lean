/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.Topology.CWComplex.Classical.Basic

/-!
# Dimension bounds and compactness of CW complexes

A relative or absolute CW complex with no cells in dimensions strictly above `d` is
finite-dimensional (`Topology.RelCWComplex.finiteDimensional_of_isEmpty_cell_gt`,
`Topology.CWComplex.finiteDimensional_of_isEmpty_cell_gt`), regardless of how many cells lie in
dimensions at most `d`.

Finiteness properties (`FiniteDimensional`, `FiniteType`, `Finite`) transport across any
dimensionwise family of cell equivalences (`Topology.RelCWComplex.finiteDimensional_of_cellEquiv`,
`Topology.RelCWComplex.finiteType_of_cellEquiv`, `Topology.RelCWComplex.finite_of_cellEquiv`), and
in particular along `Topology.RelCWComplex.copy`.

A finite relative CW complex `C` over a compact base `D` is compact
(`Topology.RelCWComplex.isCompact_of_finite`): it is the union of `D` and of its finitely many
closed cells, each of which is the image of a closed ball. In particular a finite CW complex is
compact (`Topology.CWComplex.isCompact_of_finite`), and a space carrying a finite CW structure on
`univ` is a compact space, hence normal when it is Hausdorff.
-/

public section

open Set

namespace Topology

/-- A relative CW complex with no cells in dimensions strictly above `d` is finite-dimensional,
regardless of how many cells lie in dimensions at most `d`. -/
@[alias_in CWComplex]
lemma RelCWComplex.finiteDimensional_of_isEmpty_cell_gt {X : Type*} [TopologicalSpace X]
    {D : Set X} (C : Set X) [RelCWComplex C D] {d : ℕ}
    (h : ∀ m, d < m → IsEmpty (RelCWComplex.cell C m)) :
    RelCWComplex.FiniteDimensional C :=
  ⟨Filter.eventually_atTop.2 ⟨d + 1, fun m hm ↦ h m (Nat.lt_of_succ_le hm)⟩⟩

section CellEquiv

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A relative CW complex whose `n`-cells are equivalent to those of a finite-dimensional
relative CW complex is finite-dimensional. -/
theorem RelCWComplex.finiteDimensional_of_cellEquiv {C D : Set X} {C' D' : Set Y}
    (I : RelCWComplex C D) (I' : RelCWComplex C' D')
    (e : ∀ n, @RelCWComplex.cell _ _ C' D' I' n ≃ @RelCWComplex.cell _ _ C D I n)
    [@RelCWComplex.FiniteDimensional _ _ C D I] :
    @RelCWComplex.FiniteDimensional _ _ C' D' I' :=
  @RelCWComplex.FiniteDimensional.mk _ _ _ _ I' <| by
    filter_upwards [@RelCWComplex.FiniteDimensional.eventually_isEmpty_cell _ _ C D I _] with n _
    exact (e n).isEmpty_congr.2 inferInstance

/-- A relative CW complex whose `n`-cells are equivalent to those of a relative CW complex of
finite type has finite type. -/
theorem RelCWComplex.finiteType_of_cellEquiv {C D : Set X} {C' D' : Set Y}
    (I : RelCWComplex C D) (I' : RelCWComplex C' D')
    (e : ∀ n, @RelCWComplex.cell _ _ C' D' I' n ≃ @RelCWComplex.cell _ _ C D I n)
    [@RelCWComplex.FiniteType _ _ C D I] :
    @RelCWComplex.FiniteType _ _ C' D' I' :=
  @RelCWComplex.FiniteType.mk _ _ _ _ I' fun n ↦
    have := @RelCWComplex.FiniteType.finite_cell _ _ C D I _ n
    (e n).finite_iff.2 inferInstance

/-- A relative CW complex whose `n`-cells are equivalent to those of a finite relative CW
complex is finite. -/
theorem RelCWComplex.finite_of_cellEquiv {C D : Set X} {C' D' : Set Y}
    (I : RelCWComplex C D) (I' : RelCWComplex C' D')
    (e : ∀ n, @RelCWComplex.cell _ _ C' D' I' n ≃ @RelCWComplex.cell _ _ C D I n)
    [@RelCWComplex.Finite _ _ C D I] :
    @RelCWComplex.Finite _ _ C' D' I' :=
  @RelCWComplex.finite_of_finiteDimensional_finiteType _ _ _ _ I'
    (RelCWComplex.finiteDimensional_of_cellEquiv I I' e)
    (RelCWComplex.finiteType_of_cellEquiv I I' e)

end CellEquiv

variable {X : Type*} [TopologicalSpace X] {C D : Set X}

/-- Copying a finite-dimensional relative CW complex along set equalities preserves
finite-dimensionality. -/
theorem RelCWComplex.finiteDimensional_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C')
    (hD : D = D') [@RelCWComplex.FiniteDimensional X _ C D I] :
    @RelCWComplex.FiniteDimensional X _ C' D' (I.copy C' D' hC hD) :=
  RelCWComplex.finiteDimensional_of_cellEquiv I (I.copy C' D' hC hD) (I.copyCellEquiv C' D' hC hD)

/-- Copying a relative CW complex of finite type along set equalities preserves finite type. -/
theorem RelCWComplex.finiteType_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C')
    (hD : D = D') [@RelCWComplex.FiniteType X _ C D I] :
    @RelCWComplex.FiniteType X _ C' D' (I.copy C' D' hC hD) :=
  RelCWComplex.finiteType_of_cellEquiv I (I.copy C' D' hC hD) (I.copyCellEquiv C' D' hC hD)

/-- Copying a finite relative CW complex along set equalities preserves finiteness. -/
theorem RelCWComplex.finite_copy (I : RelCWComplex C D) (C' D' : Set X) (hC : C = C')
    (hD : D = D') [@RelCWComplex.Finite X _ C D I] :
    @RelCWComplex.Finite X _ C' D' (I.copy C' D' hC hD) :=
  RelCWComplex.finite_of_cellEquiv I (I.copy C' D' hC hD) (I.copyCellEquiv C' D' hC hD)

/-- **A finite relative CW complex over a compact base is compact.** -/
theorem RelCWComplex.isCompact_of_finite [RelCWComplex C D] [RelCWComplex.Finite C]
    (hD : IsCompact D) : IsCompact C := by
  have := RelCWComplex.finite_cells_of_finite (C := C)
  rw [← RelCWComplex.union (C := C), ← iUnion_sigma (fun p : Σ n, cell C n ↦ closedCell p.1 p.2)]
  exact hD.union (isCompact_iUnion fun _ ↦ isCompact_closedCell)

/-- **A finite CW complex is compact.** -/
theorem CWComplex.isCompact_of_finite [CWComplex C] [RelCWComplex.Finite C] : IsCompact C :=
  RelCWComplex.isCompact_of_finite isCompact_empty

end Topology
