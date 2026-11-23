/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.ComponentAction.Basic
public import TauCeti.KnotTheory.Grid.Homology.CyclicPermutation

/-!
# Naturality of the component-variable action in grid homology

A map of unblocked grid homologies that commutes with renaming the column variables also
commutes with renaming the component variables, provided the two renamings agree on the
component of each column. In particular, the usual cyclic row and column move equivalences
are semilinear for the relabeling of components. The underlying grid move maps are those of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 5 and 11.
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
variable {R : Type*} [CommRing R] [CharP R 2]

/-- Compatibility with column-variable renaming implies compatibility with component-variable
renaming whenever the corresponding square of index maps commutes. -/
theorem map_smul_unblockedHomologyComponent
    (f : G.unblockedHomology R → G'.unblockedHomology R) {κ : Fin n → Fin m}
    {e : G.Components → G'.Components}
    (he : ∀ c, e (G.componentOfColumn c) = G'.componentOfColumn (κ c))
    (hf : ∀ (p : MvPolynomial (Fin n) R) x, f (p • x) = rename κ p • f x)
    (q : MvPolynomial G.Components R) (x : G.unblockedHomology R) :
    letI := G.unblockedHomologyComponentModule R
    letI := G'.unblockedHomologyComponentModule R
    f (q • x) = rename e q • f x := by
  let _ := G.unblockedHomologyComponentModule R
  let _ := G'.unblockedHomologyComponentModule R
  obtain ⟨p, rfl⟩ := rename_surjective G.componentOfColumn G.componentOfColumn_surjective q
  have hrename :
      rename e (rename G.componentOfColumn p) =
        rename G'.componentOfColumn (rename κ p) := by
    simp only [rename_rename, Function.comp_def, he]
  rw [G.rename_componentOfColumn_smul_unblockedHomology R p x, hrename,
    G'.rename_componentOfColumn_smul_unblockedHomology R (rename κ p) (f x)]
  exact hf p x

variable (G R)

/-- The row rotation equivalence of unblocked homology is semilinear over the canonical
identification of component variables. -/
noncomputable def unblockedHomologyComponentRelabelRowsFinRotateEquiv :
    let G' := G.relabelRows (finRotate n)
    letI := G.unblockedHomologyComponentModule R
    letI := G'.unblockedHomologyComponentModule R
    G.unblockedHomology R ≃ₛₗ[
      ((renameEquiv R (G.componentsRelabelRowsEquiv (finRotate n))).toRingEquiv :
        MvPolynomial G.Components R →+* MvPolynomial G'.Components R)]
      G'.unblockedHomology R :=
  letI := G.unblockedHomologyComponentModule R
  letI := (G.relabelRows (finRotate n)).unblockedHomologyComponentModule R
  { (G.unblockedHomologyRelabelRowsFinRotateEquiv R).toAddEquiv with
    map_smul' := fun q x ↦
      map_smul_unblockedHomologyComponent (G.unblockedHomologyRelabelRowsFinRotateEquiv R)
        (κ := id) (e := G.componentsRelabelRowsEquiv (finRotate n))
        (fun c ↦ G.componentsRelabelRowsEquiv_componentOfColumn (finRotate n) c)
        (fun p y ↦ by simpa only [rename_id_apply] using
          (G.unblockedHomologyRelabelRowsFinRotateEquiv R).map_smul p y) q x }

-- Match applications before simp normalizes the ring homomorphisms in the semilinear types.

/-- The component-semilinear row rotation acts by the usual row rotation on homology. -/
@[simp↓]
theorem unblockedHomologyComponentRelabelRowsFinRotateEquiv_apply
    (x : G.unblockedHomology R) :
    G.unblockedHomologyComponentRelabelRowsFinRotateEquiv R x =
      G.unblockedHomologyRelabelRowsFinRotateEquiv R x :=
  (rfl)

/-- The inverse component-semilinear row rotation acts by the inverse of the usual row
rotation on homology. -/
@[simp↓]
theorem unblockedHomologyComponentRelabelRowsFinRotateEquiv_symm_apply
    (x : (G.relabelRows (finRotate n)).unblockedHomology R) :
    (G.unblockedHomologyComponentRelabelRowsFinRotateEquiv R).symm x =
      (G.unblockedHomologyRelabelRowsFinRotateEquiv R).symm x :=
  (rfl)

/-- The column rotation equivalence of unblocked homology is semilinear over the induced
permutation of component variables. -/
noncomputable def unblockedHomologyComponentRelabelColumnsFinRotateEquiv :
    let G' := G.relabelColumns (finRotate n)
    letI := G.unblockedHomologyComponentModule R
    letI := G'.unblockedHomologyComponentModule R
    G.unblockedHomology R ≃ₛₗ[
      ((renameEquiv R (G.componentsRelabelColumnsEquiv (finRotate n))).toRingEquiv :
        MvPolynomial G.Components R →+* MvPolynomial G'.Components R)]
      G'.unblockedHomology R :=
  letI := G.unblockedHomologyComponentModule R
  letI := (G.relabelColumns (finRotate n)).unblockedHomologyComponentModule R
  { (G.unblockedHomologyRelabelColumnsFinRotateEquiv R).toAddEquiv with
    map_smul' := fun q x ↦
      map_smul_unblockedHomologyComponent (G.unblockedHomologyRelabelColumnsFinRotateEquiv R)
        (κ := finRotate n) (e := G.componentsRelabelColumnsEquiv (finRotate n))
        (G.componentsRelabelColumnsEquiv_componentOfColumn (finRotate n))
        (G.unblockedHomologyRelabelColumnsFinRotateEquiv R).map_smulₛₗ q x }

/-- The component-semilinear column rotation acts by the usual column rotation on homology. -/
@[simp↓]
theorem unblockedHomologyComponentRelabelColumnsFinRotateEquiv_apply
    (x : G.unblockedHomology R) :
    G.unblockedHomologyComponentRelabelColumnsFinRotateEquiv R x =
      G.unblockedHomologyRelabelColumnsFinRotateEquiv R x :=
  (rfl)

/-- The inverse component-semilinear column rotation acts by the inverse of the usual column
rotation on homology. -/
@[simp↓]
theorem unblockedHomologyComponentRelabelColumnsFinRotateEquiv_symm_apply
    (x : (G.relabelColumns (finRotate n)).unblockedHomology R) :
    (G.unblockedHomologyComponentRelabelColumnsFinRotateEquiv R).symm x =
      (G.unblockedHomologyRelabelColumnsFinRotateEquiv R).symm x :=
  (rfl)

end TauCeti.GridDiagram
