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
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.Solvable
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Solvable

/-!
# Exact solvability classification of `SL₂(F)` and `PSL₂(F)` over fields

Over a finite field `F` with at most three elements (`𝔽₂` or `𝔽₃`), the projective line `ℙ¹(F)`
has at most four points, so `PSL₂(F)` embeds faithfully into a solvable symmetric group and both
`PSL₂(F)` and its central extension `SL₂(F)` are solvable. Combining this with the
nonsolvability results for fields with an element outside `{0, ±1}`, `SL₂(F)` (equivalently
`PSL₂(F)`) is solvable if and only if `F` is finite and `Nat.card F ≤ 3`.

## Main declarations

* `TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three` and
  `TauCeti.Matrix.SpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three`: `PSL₂(F)` and
  `SL₂(F)` are solvable when `F` is finite with `Nat.card F ≤ 3`.
* `TauCeti.Matrix.SpecialLinearGroup.isSolvable_fin_two_iff` and
  `TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_fin_two_iff`: `SL₂(F)` and `PSL₂(F)`
  are solvable if and only if `F` is finite and `Nat.card F ≤ 3`.

## References

* E. Artin, *Geometric Algebra*, Interscience, 1957, Chapter IV, §9 (solvability of `PSL₂(𝔽₂)`,
  `PSL₂(𝔽₃)` and nonsolvability for `|F| ≥ 4`).
-/

public section

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace TauCeti.Matrix.ProjectiveSpecialLinearGroup

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

namespace TauCeti.Matrix.SpecialLinearGroup

/-- Over a finite field `F` with at most three elements (`𝔽₂` or `𝔽₃`), `SL₂(F)` is solvable. -/
theorem isSolvable_fin_two_of_natCard_le_three (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F ≤ 3) : Group.IsSolvable SL(2, F) :=
  (ProjectiveSpecialLinearGroup.isSolvable_iff (Fin 2) F).mp
    (ProjectiveSpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three F hF)

/-- **Characterization of solvability of `SL₂` over fields**: `SL₂(F)` is solvable if and only if
`F` is finite and has at most three elements. -/
theorem isSolvable_fin_two_iff (F : Type*) [Field F] :
    Group.IsSolvable SL(2, F) ↔ Finite F ∧ Nat.card F ≤ 3 := by
  refine ⟨fun hS ↦ ?_, fun ⟨_, hle⟩ ↦ isSolvable_fin_two_of_natCard_le_three F hle⟩
  have hFin : Finite F :=
    not_infinite_iff_finite.mp fun _ ↦ not_isSolvable_fin_two_of_infinite F hS
  refine ⟨hFin, by_contra fun hgt ↦ ?_⟩
  classical
  cases nonempty_fintype F
  have hcard3 : ({0, 1, -1} : Finset F).card ≤ 3 := by
    grw [Finset.card_insert_le, Finset.card_insert_le]; simp
  have hlt : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact not_isSolvable_fin_two F ⟨a, ha.1, sq_ne_one_iff.mpr ha.2⟩ hS

end TauCeti.Matrix.SpecialLinearGroup

namespace TauCeti.Matrix.ProjectiveSpecialLinearGroup

/-- **Characterization of solvability of `PSL₂` over fields**: `PSL₂(F)` is solvable if and only if
`F` is finite and has at most three elements. -/
theorem isSolvable_fin_two_iff (F : Type*) [Field F] :
    Group.IsSolvable PSL(2, F) ↔ Finite F ∧ Nat.card F ≤ 3 :=
  (isSolvable_iff (Fin 2) F).trans (SpecialLinearGroup.isSolvable_fin_two_iff F)

end TauCeti.Matrix.ProjectiveSpecialLinearGroup
