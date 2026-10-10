/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Homomorphisms from special linear groups with exponent-two image

Over a field of characteristic different from two, a homomorphism from `SLₙ` whose
images square to one is trivial. Every elementary transvection is the square of the
transvection with half its coefficient, and elementary transvections generate `SLₙ`.
This applies in particular to the determinant character of an orthogonal representation.
-/

public section

namespace MonoidHom

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [NeZero (2 : K)]
  [Monoid H]

/-- A homomorphism from a special linear group over a field of characteristic different
from two is trivial if every element in its image squares to one. -/
theorem eq_one_of_sq_eq_one_on_specialLinearGroup
    (f : Matrix.SpecialLinearGroup ι K →* H) (hf : ∀ g, f g ^ 2 = 1) : f = 1 := by
  have htransvection {i j : ι} (hij : i ≠ j) (c : K) :
      f (Matrix.SpecialLinearGroup.transvection hij c) = 1 := by
    have hc : c / 2 + c / 2 = c := by
      field_simp
      ring
    calc
      f (Matrix.SpecialLinearGroup.transvection hij c) =
          f (Matrix.SpecialLinearGroup.transvection hij (c / 2)) ^ 2 := by
        rw [pow_two, ← map_mul, ← Matrix.SpecialLinearGroup.transvection_add, hc]
      _ = 1 := hf _
  have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct ι K → Matrix.SpecialLinearGroup ι K)) ≤ f.ker := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    exact htransvection hij c
  rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field] at hle
  ext g
  exact hle (Subgroup.mem_top g)

end MonoidHom
