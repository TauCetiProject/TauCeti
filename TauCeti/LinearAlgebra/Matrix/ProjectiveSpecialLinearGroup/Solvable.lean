/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Solvability of `PSL(n, R)`

`PSL(n, R)` is the quotient of `SL(n, R)` by its abelian center, so `PSL(n, R)` is solvable if
and only if `SL(n, R)` is solvable (`TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_iff`).

Over a finite field `F` with at most three elements (`𝔽₂` or `𝔽₃`), the projective line `ℙ¹(F)` has
at most four points, so `PSL₂(F)` embeds faithfully into a solvable symmetric group and is solvable
(`TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three`).
-/

public section

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace TauCeti.Matrix.ProjectiveSpecialLinearGroup

/-- Since `PSL(n, R)` is the quotient of `SL(n, R)` by its abelian center, `PSL(n, R)` is solvable
if and only if `SL(n, R)` is solvable. -/
theorem isSolvable_iff (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
    Group.IsSolvable (_root_.Matrix.ProjectiveSpecialLinearGroup n R) ↔
      Group.IsSolvable (_root_.Matrix.SpecialLinearGroup n R) :=
  ⟨fun _ ↦ Group.isSolvable_of_subgroup_quotient
    (Subgroup.center (_root_.Matrix.SpecialLinearGroup n R)), fun _ ↦ inferInstance⟩

/-- Over a finite field `F` with at most three elements, `PSL₂(F)` acts faithfully on the
projective line `ℙ¹(F)` of cardinality `|F| + 1 ≤ 4`, hence embeds into a solvable symmetric group
and is solvable. -/
theorem isSolvable_fin_two_of_natCard_le_three (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F ≤ 3) : Group.IsSolvable PSL(2, F) := by
  have hcard : Nat.card (ℙ F (Fin 2 → F)) ≤ 4 := by
    rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (Module.finrank_fin_fun F)]; omega
  have : Group.IsSolvable (Equiv.Perm (ℙ F (Fin 2 → F))) := Equiv.Perm.isSolvable hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := MulAction.toPermHom PSL(2, F) (ℙ F (Fin 2 → F)))
    fun _ _ h ↦ eq_of_smul_eq_smul fun p ↦ Equiv.ext_iff.mp h p

end TauCeti.Matrix.ProjectiveSpecialLinearGroup
