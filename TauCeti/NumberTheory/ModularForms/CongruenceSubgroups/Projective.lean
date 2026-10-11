/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The projective image of `Γ₀(N)`

The compactified modular curve is a quotient by a subgroup of `PSL₂(ℤ)`, while congruence
subgroups are defined inside `SL₂(ℤ)`. Since `Γ₀(N)` contains the center `{±I}`, passing to its
projective image does not change its index. This identifies the arithmetic index with the degree
input used by the compactified quotient map.
-/

public section

open scoped MatrixGroups

namespace CongruenceSubgroup

/-- The image of `Γ₀(N)` in `PSL₂(ℤ)`, the group acting effectively on the upper half-plane. -/
def Gamma0Projective (N : ℕ) : Subgroup PSL(2, ℤ) :=
  (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- The projective image of `Γ₀(N)` has the same index as `Γ₀(N)`: the quotient map's kernel,
the center of `SL₂(ℤ)`, is already contained in `Γ₀(N)`. -/
theorem Gamma0Projective_index (N : ℕ) :
    (Gamma0Projective N).index = (Gamma0 N).index := by
  unfold Gamma0Projective
  exact Subgroup.index_map_eq (H := Gamma0 N)
    (f := QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))
    (QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℤ))) (by
      rw [QuotientGroup.ker_mk']
      intro A hA
      rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hA with hA | hA
      · subst A
        simp
      · subst A
        simp)

end CongruenceSubgroup
