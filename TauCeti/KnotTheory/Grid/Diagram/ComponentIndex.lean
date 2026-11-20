/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Components
import TauCeti.GroupTheory.Perm.Basic

/-!
# Component indices of a grid diagram

`GridDiagram.Components` indexes the link components by the orbits of the component permutation.
The projection `componentOfColumn` identifies exactly the columns on the same component. Row
and column relabelings induce equivalences of these component indices.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The components of a grid diagram, indexed by the orbits of its component permutation. -/
abbrev Components := Quotient (Equiv.Perm.SameCycle.setoid G.componentPerm)

/-- The link component containing the `O`-marking in a column. -/
def componentOfColumn (c : Fin n) : G.Components := Quotient.mk _ c

/-- Two columns index the same component exactly when they lie in the same component cycle. -/
@[simp]
theorem componentOfColumn_eq_iff {c d : Fin n} :
    G.componentOfColumn c = G.componentOfColumn d ↔ G.componentPerm.SameCycle c d :=
  Quotient.eq

/-- Every link component contains an `O`-marking column. -/
theorem componentOfColumn_surjective : Function.Surjective G.componentOfColumn :=
  Quotient.mk_surjective

/-- Projecting the representative of a component recovers that component. -/
@[simp]
theorem componentOfColumn_out (q : G.Components) : G.componentOfColumn q.out = q :=
  Quotient.out_eq q

/-- The cardinality of the component index type is the component count of the diagram. -/
theorem natCard_components : Nat.card G.Components = G.componentCount := by
  rw [componentCount_eq_orbitCount, orbitCount_def]

/-- Row relabeling preserves the component index of each column. -/
def componentsRelabelRowsEquiv (ρ : Equiv.Perm (Fin n)) :
    G.Components ≃ (G.relabelRows ρ).Components :=
  Equiv.sameCycleQuotientCongr (Equiv.refl _) (by
    rw [componentPerm_relabelRows]
    rfl)

/-- Row relabeling sends the component of a column to the component of that same column. -/
@[simp]
theorem componentsRelabelRowsEquiv_componentOfColumn (ρ : Equiv.Perm (Fin n)) (c : Fin n) :
    G.componentsRelabelRowsEquiv ρ (G.componentOfColumn c) =
      (G.relabelRows ρ).componentOfColumn c := by
  unfold componentsRelabelRowsEquiv componentOfColumn
  exact Equiv.sameCycleQuotientCongr_mk _ _ _

/-- The inverse row relabeling equivalence retains the column labeling of components. -/
@[simp]
theorem componentsRelabelRowsEquiv_symm_componentOfColumn
    (ρ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.componentsRelabelRowsEquiv ρ).symm ((G.relabelRows ρ).componentOfColumn c) =
      G.componentOfColumn c := by
  rw [Equiv.symm_apply_eq, componentsRelabelRowsEquiv_componentOfColumn]

/-- Column relabeling induces the corresponding relabeling of component indices. -/
def componentsRelabelColumnsEquiv (κ : Equiv.Perm (Fin n)) :
    G.Components ≃ (G.relabelColumns κ).Components :=
  Equiv.sameCycleQuotientCongr κ (by
    rw [componentPerm_relabelColumns]
    rfl)

/-- Column relabeling sends the component of `c` to the component of its relabeled column. -/
@[simp]
theorem componentsRelabelColumnsEquiv_componentOfColumn (κ : Equiv.Perm (Fin n)) (c : Fin n) :
    G.componentsRelabelColumnsEquiv κ (G.componentOfColumn c) =
      (G.relabelColumns κ).componentOfColumn (κ c) := by
  unfold componentsRelabelColumnsEquiv componentOfColumn
  exact Equiv.sameCycleQuotientCongr_mk _ _ _

/-- The inverse column relabeling equivalence restores the original column labels. -/
@[simp]
theorem componentsRelabelColumnsEquiv_symm_componentOfColumn
    (κ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.componentsRelabelColumnsEquiv κ).symm ((G.relabelColumns κ).componentOfColumn c) =
      G.componentOfColumn (κ.symm c) := by
  rw [Equiv.symm_apply_eq, componentsRelabelColumnsEquiv_componentOfColumn,
    Equiv.apply_symm_apply]

end TauCeti.GridDiagram
