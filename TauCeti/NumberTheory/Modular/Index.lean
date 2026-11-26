/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import TauCeti.GroupTheory.Index.TorsionFree
import TauCeti.NumberTheory.Modular.Generators

/-!
# Index divisibility for torsion-free subgroups of `PSL(2, ℤ)`

Since `PSL(2, ℤ)` contains the order-two element `S` and the order-three element `R = S T`, the
order of each divides the index of any torsion-free subgroup `Γ' ≤ PSL(2, ℤ)`, so `6 ∣ Γ'.index`.

## Main results

* `TauCeti.ModularGroup.six_dvd_index_of_isMulTorsionFree`: every torsion-free subgroup
  `Γ' ≤ PSL(2, ℤ)` has index divisible by `6`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  Chapter VII, §1.
-/

public section

open scoped MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-- Every torsion-free subgroup `Γ' ≤ PSL(2, ℤ)` has index divisible by `6`. -/
theorem six_dvd_index_of_isMulTorsionFree (Γ' : Subgroup PSL(2, ℤ)) [IsMulTorsionFree Γ'] :
    6 ∣ Γ'.index := by
  have h2 := Γ'.orderOf_dvd_index_of_isMulTorsionFree
    (orderOf_pos_iff.mp (by rw [orderOf_coe_S]; decide))
  rw [orderOf_coe_S] at h2
  have h3 := Γ'.orderOf_dvd_index_of_isMulTorsionFree
    (orderOf_pos_iff.mp (by rw [orderOf_coe_R]; decide))
  rw [orderOf_coe_R] at h3
  exact (by decide : 6 = Nat.lcm 2 3) ▸ Nat.lcm_dvd h2 h3

end TauCeti.ModularGroup
