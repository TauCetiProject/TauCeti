/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Closed subschemes of a scheme over a base

If `X` is a scheme over `S` and `I` is an ideal sheaf on `X`, the closed subscheme `V(I)` is a
scheme over `S` through its inclusion `V(I) ⟶ X ⟶ S`, and the inclusion is then an
`S`-morphism.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.instOverSubscheme`: the structure of scheme over `S`
  on `V(I)`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.over_eq_subschemeι_comp`: the structure morphism of
  `V(I)` is the inclusion followed by the structure morphism of `X`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isFinite_subschemeι_comp_of_finite_support`: a closed
  subscheme with finitely many points of a scheme locally of finite type over a field is finite
  over the field.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}} [X.Over S] (I : X.IdealSheafData)

/-- A closed subscheme of a scheme over `S` is a scheme over `S` through its inclusion. -/
instance instOverSubscheme : I.subscheme.Over S :=
  ⟨I.subschemeι ≫ X ↘ S⟩

/-- The structure morphism of a closed subscheme over `S` is its inclusion followed by the
structure morphism of the ambient scheme. -/
-- Not `@[simp]`: `CategoryTheory.comp_over` with `isOver_subschemeι` rewrites the right side
-- back to the left side.
theorem over_eq_subschemeι_comp : I.subscheme ↘ S = I.subschemeι ≫ X ↘ S :=
  (rfl)

/-- The inclusion of a closed subscheme is a morphism over `S`. -/
instance isOver_subschemeι : I.subschemeι.IsOver S :=
  ⟨rfl⟩

/-- A closed subscheme with finitely many points of a scheme locally of finite type over a field is
finite over the field. -/
theorem isFinite_subschemeι_comp_of_finite_support (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] (I : X.IdealSheafData)
    (hI : (I.support : Set X).Finite) : IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)) := by
  -- The closed immersion `V(I) ⟶ X` maps the points of `V(I)` injectively into `I.support`.
  have : Finite I.subscheme := by
    have := hI.to_subtype
    refine Finite.of_injective (β := I.support)
      (fun z ↦ ⟨I.subschemeι z, by
        rw [← SetLike.mem_coe, ← I.range_subschemeι]; exact Set.mem_range_self z⟩) fun _ _ h ↦ ?_
    exact I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val h)
  have := LocallyQuasiFinite.of_finite_preimage_singleton (I.subschemeι ≫ X ↘ Spec (.of k))
    fun _ ↦ Set.toFinite _
  -- `V(I)` is finite, hence compact, so its morphism to the affine `Spec k` is quasi-compact.
  exact IsFinite.of_locallyQuasiFinite _

end AlgebraicGeometry.Scheme.IdealSheafData

end
