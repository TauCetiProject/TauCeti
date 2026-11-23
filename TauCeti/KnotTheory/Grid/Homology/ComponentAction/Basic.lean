/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Components
public import TauCeti.KnotTheory.Grid.Homology.Unblocked

/-!
# The component polynomial action on unblocked grid homology

The variables belonging to columns on the same link component act identically on unblocked
grid homology. Consequently its column-variable action descends to a polynomial action with
one variable for each element of `GridDiagram.Components`.

`unblockedHomologyComponentModule` constructs this action by choosing a representative column
of each component. The characteristic equation
`rename_componentOfColumn_smul_unblockedHomology` describes the action without mentioning
those choices: renaming each column variable to its component preserves its action on homology.
It also shows compatibility with the coefficient action and, for knots, the existing
single-variable polynomial action.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Remark 8.2.6 and
Definition 11.1.1 describe the polynomial action with one variable per link component.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The polynomial action on unblocked homology with one variable per link component.
Representative columns are used only in the construction; the characteristic renaming equation
describes the resulting action independently of those representatives. -/
@[instance_reducible]
noncomputable def unblockedHomologyComponentModule :
    Module (MvPolynomial G.Components R) (G.unblockedHomology R) :=
  Module.compHom _
    (MvPolynomial.rename (R := R) (Quotient.out : G.Components → Fin n)).toRingHom

/-- Replacing every column variable by its component variable preserves the action on homology.
This characterizes the component action, since the renaming map is surjective. -/
@[simp]
theorem rename_componentOfColumn_smul_unblockedHomology
    (p : MvPolynomial (Fin n) R) (x : G.unblockedHomology R) :
    letI := G.unblockedHomologyComponentModule R
    MvPolynomial.rename G.componentOfColumn p • x = p • x := by
  let _ := G.unblockedHomologyComponentModule R
  -- Restriction of scalars computes the action using the chosen representative columns.
  change MvPolynomial.rename Quotient.out (MvPolynomial.rename G.componentOfColumn p) • x = p • x
  rw [MvPolynomial.rename_rename]
  exact (smul_unblockedHomology_eq_rename_smul _
    (fun c ↦ G.componentOfColumn_eq_iff.mp
      (G.componentOfColumn_out (G.componentOfColumn c)).symm) p x).symm

/-- A component variable acts as the column variable of any column on that component. -/
@[simp]
theorem X_componentOfColumn_smul_unblockedHomology (c : Fin n) (x : G.unblockedHomology R) :
    letI := G.unblockedHomologyComponentModule R
    (MvPolynomial.X (G.componentOfColumn c) : MvPolynomial G.Components R) • x =
      (MvPolynomial.X c : MvPolynomial (Fin n) R) • x := by
  simpa only [MvPolynomial.rename_X] using
    G.rename_componentOfColumn_smul_unblockedHomology R (MvPolynomial.X c) x

/-- The coefficient action agrees with the constants in the component polynomial action. -/
theorem isScalarTower_unblockedHomologyComponent :
    letI := G.unblockedHomologyComponentModule R
    IsScalarTower R (MvPolynomial G.Components R) (G.unblockedHomology R) := by
  let _ := G.unblockedHomologyComponentModule R
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  have h := G.rename_componentOfColumn_smul_unblockedHomology R (MvPolynomial.C r) x
  have hbase : r • x = (MvPolynomial.C r : MvPolynomial (Fin n) R) • x :=
    IsScalarTower.algebraMap_smul (MvPolynomial (Fin n) R) r x
  simpa only [MvPolynomial.rename_C, MvPolynomial.algebraMap_eq, hbase] using h

variable {G R}

/-- For a knot, sending every component variable to `U` recovers the existing `R[U]` action. -/
theorem IsKnot.aeval_smul_unblockedHomologyComponent (hG : G.IsKnot)
    (p : MvPolynomial G.Components R) (x : G.unblockedHomology R) :
    letI := G.unblockedHomologyComponentModule R
    letI := hG.unblockedHomologyModule R
    MvPolynomial.aeval (fun _ ↦ (Polynomial.X : Polynomial R)) p • x = p • x := by
  obtain ⟨q, rfl⟩ := MvPolynomial.rename_surjective G.componentOfColumn
    G.componentOfColumn_surjective p
  simpa only [MvPolynomial.aeval_rename, Function.comp_def] using
    (hG.aeval_smul_unblockedHomology q x).trans
      (G.rename_componentOfColumn_smul_unblockedHomology R q x).symm

end TauCeti.GridDiagram
