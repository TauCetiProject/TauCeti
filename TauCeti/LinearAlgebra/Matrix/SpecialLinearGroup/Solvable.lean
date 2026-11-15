/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Solvability and nonnilpotence of `SL₂` and `PSL₂`

If a field contains an element `a` with `a ≠ 0` and `a² ≠ 1`, then `SL₂` is nonsolvable.
It is therefore also not nilpotent. In particular, these statements hold over every infinite field
and over every finite field with at least four elements. Conversely, over a finite field `F` with
at most three elements (`𝔽₂` or `𝔽₃`), the projective line `ℙ¹(F)` has at most four points, so
`PSL₂(F)` embeds faithfully into a solvable symmetric group and both `PSL₂(F)` and its central
extension `SL₂(F)` are solvable. Thus `SL₂(F)` (equivalently `PSL₂(F)`) is solvable if and only if
`F` is finite and `Nat.card F ≤ 3`.

## Main declarations

* `TauCeti.Matrix.SpecialLinearGroup.not_isSolvable_fin_two`: `SL₂` is not solvable when the
  field contains an element outside the roots of `X * (X² - 1)`.
* `TauCeti.Matrix.SpecialLinearGroup.not_isSolvable_fin_two_of_infinite`: the infinite-field
  specialization.
* `TauCeti.Matrix.SpecialLinearGroup.not_isNilpotent_fin_two`: the corresponding
  nonnilpotence statement.
* `TauCeti.Matrix.SpecialLinearGroup.not_isNilpotent_fin_two_of_infinite`: its infinite-field
  specialization.
* `TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_iff`: `PSL(n, R)` is solvable iff
  `SL(n, R)` is solvable.
* `TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three` and
  `TauCeti.Matrix.SpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three`: `PSL₂(F)` and
  `SL₂(F)` are solvable when `F` is finite with `Nat.card F ≤ 3`.
* `TauCeti.Matrix.SpecialLinearGroup.isSolvable_fin_two_iff` and
  `TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_fin_two_iff`: `SL₂(F)` and `PSL₂(F)`
  are solvable if and only if `F` is finite and `Nat.card F ≤ 3`.

## References

* E. Artin, *Geometric Algebra*, Interscience, 1957, Chapter IV, §9 (solvability of `PSL₂(𝔽₂)`,
  `PSL₂(𝔽₃)` and nonsolvability for `|F| ≥ 4`).
* Mathlib, `GroupTheory/IsPerfect.lean`, for nonsolvability of nontrivial perfect groups.
* Mathlib, `GroupTheory/Nilpotent.lean`, for solvability of nilpotent groups.
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
    (hF : Nat.card F ≤ 3) :
    Group.IsSolvable PSL(2, F) := by
  have hcard : Nat.card (ℙ F (Fin 2 → F)) ≤ 4 := by
    rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (Module.finrank_fin_fun F)]
    omega
  have : Group.IsSolvable (Equiv.Perm (ℙ F (Fin 2 → F))) := Equiv.Perm.isSolvable hcard
  have hinj : Function.Injective (MulAction.toPermHom PSL(2, F) (ℙ F (Fin 2 → F))) :=
    fun _ _ h ↦ eq_of_smul_eq_smul fun p ↦ Equiv.ext_iff.mp h p
  exact Group.isSolvable_of_isSolvable_injective hinj

end TauCeti.Matrix.ProjectiveSpecialLinearGroup

namespace TauCeti.Matrix.SpecialLinearGroup

/-- The special linear group `SL₂(F)` is not solvable if `F` contains a nonzero element whose
square is not one. -/
theorem not_isSolvable_fin_two (F : Type*) [Field F]
    (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) : ¬ Group.IsSolvable SL(2, F) := by
  obtain ⟨a, ha0, ha1⟩ := hF
  have : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top ha0 ha1⟩
  -- The transvection with off-diagonal entry `1` witnesses that `SL₂(F)` is nontrivial.
  have : Nontrivial SL(2, F) := ⟨Matrix.SpecialLinearGroup.transvection zero_ne_one 1, 1,
    fun h ↦ by simpa [Matrix.SpecialLinearGroup.transvection_coe] using congr($h.1 0 1)⟩
  exact Group.IsPerfect.not_isSolvable _

/-- The special linear group `SL₂` over an infinite field is not solvable. -/
theorem not_isSolvable_fin_two_of_infinite (F : Type*) [Field F] [Infinite F] :
    ¬ Group.IsSolvable SL(2, F) := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset F)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact not_isSolvable_fin_two F ⟨a, ha.1, sq_ne_one_iff.mpr ha.2⟩

/-- The special linear group `SL₂(F)` is not nilpotent if `F` contains a nonzero element whose
square is not one. -/
theorem not_isNilpotent_fin_two (F : Type*) [Field F]
    (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) : ¬ Group.IsNilpotent SL(2, F) := by
  intro h
  exact not_isSolvable_fin_two F hF (Group.IsNilpotent.to_isSolvable (h := h))

/-- The special linear group `SL₂` over an infinite field is not nilpotent. -/
theorem not_isNilpotent_fin_two_of_infinite (F : Type*) [Field F] [Infinite F] :
    ¬ Group.IsNilpotent SL(2, F) := by
  intro h
  exact not_isSolvable_fin_two_of_infinite F (Group.IsNilpotent.to_isSolvable (h := h))

/-- Over a finite field `F` with at most three elements (`𝔽₂` or `𝔽₃`), `SL₂(F)` is solvable. -/
theorem isSolvable_fin_two_of_natCard_le_three (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F ≤ 3) :
    Group.IsSolvable SL(2, F) :=
  (ProjectiveSpecialLinearGroup.isSolvable_iff (Fin 2) F).mp
    (ProjectiveSpecialLinearGroup.isSolvable_fin_two_of_natCard_le_three F hF)

/-- **Characterization of solvability of `SL₂` over fields**: `SL₂(F)` is solvable if and only if
`F` is finite and has at most three elements. -/
theorem isSolvable_fin_two_iff (F : Type*) [Field F] :
    Group.IsSolvable SL(2, F) ↔ Finite F ∧ Nat.card F ≤ 3 := by
  refine ⟨fun hS ↦ ?_, fun ⟨hFin, hle⟩ ↦ isSolvable_fin_two_of_natCard_le_three F hle⟩
  have hFin : Finite F := by
    by_contra hInf
    have : Infinite F := not_finite_iff_infinite.mp hInf
    exact not_isSolvable_fin_two_of_infinite F hS
  refine ⟨hFin, ?_⟩
  by_contra! hgt
  classical
  cases nonempty_fintype F
  have hcard3 : ({0, 1, -1} : Finset F).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans <|
      Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))
  have hlt : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
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
