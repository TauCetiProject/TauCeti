/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Rank

/-!
# Containment of finite flat closed subschemes of equal rank

An inclusion of closed subschemes finite and flat over the same base is equality when their
rank functions agree. In ideal-sheaf notation the direction of containment is reversed:
`I ≤ J` gives the closed immersion `J.subscheme ⟶ I.subscheme`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X S : Scheme.{u}}

/-- Comparable ideal sheaves cutting out finite flat schemes of the same rank over the base
are equal. -/
theorem eq_of_le_of_finrank_eq {I J : X.IdealSheafData} (h : I ≤ J) (f : X ⟶ S)
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [Flat (J.subschemeι ≫ f)]
    (hrank : (I.subschemeι ≫ f).finrank = (J.subschemeι ≫ f).finrank) : I = J := by
  have : IsClosedImmersion (inclusion h ≫ I.subschemeι) := by
    rw [inclusion_subschemeι]; infer_instance
  have : IsClosedImmersion (inclusion h) :=
    IsClosedImmersion.of_comp_isClosedImmersion (inclusion h) I.subschemeι
  have : Flat (inclusion h ≫ I.subschemeι ≫ f) := by
    rw [← Category.assoc, inclusion_subschemeι]; infer_instance
  have : IsIso (inclusion h) :=
    ((inclusion h).isIso_iff_finrank_comp_eq (I.subschemeι ≫ f)).mpr (by
      rw [← Category.assoc, inclusion_subschemeι]; exact hrank.symm)
  rw [← ker_subschemeι I, ← ker_subschemeι J, ← inclusion_subschemeι h,
    Hom.ker_comp_of_isIso]

end AlgebraicGeometry.Scheme.IdealSheafData
