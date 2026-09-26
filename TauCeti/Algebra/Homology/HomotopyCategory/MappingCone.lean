/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The mapping cone of a homotopy equivalence is contractible

A morphism of cochain complexes `f : K ⟶ L` sits in the distinguished triangle
`K ⟶ L ⟶ cone f ⟶ K⟦1⟧` of the homotopy category. In a pretriangulated category the third
object of a distinguished triangle is zero exactly when its first morphism is an isomorphism, so
the mapping cone of `f` is zero in the homotopy category as soon as `f` becomes an isomorphism
there, in particular when `f` is a homotopy equivalence. Being zero in the homotopy category means
that the identity is null-homotopic, which is the form in which this file records the statement.

## Main results

* `CochainComplex.mappingCone.nonempty_homotopy_id_zero_of_isIso_quotient_map`: the mapping cone
  of a morphism inverted by the homotopy category is contractible.
* `CochainComplex.mappingCone.nonempty_homotopy_id_zero_of_homotopyEquiv`: the mapping cone of a
  homotopy equivalence is contractible.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ}

/-- The mapping cone of a morphism which becomes an isomorphism in the homotopy category is
contractible. -/
theorem nonempty_homotopy_id_zero_of_isIso_quotient_map (f : K ⟶ L)
    [IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)] :
    Nonempty (Homotopy (𝟙 (mappingCone f)) 0) :=
  (HomotopyCategory.isZero_quotient_obj_iff _).1
    (Triangle.isZero₃_of_isIso₁ _ (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (inferInstanceAs (IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f))))

/-- The mapping cone of a homotopy equivalence is contractible. -/
theorem nonempty_homotopy_id_zero_of_homotopyEquiv (e : HomotopyEquiv K L) :
    Nonempty (Homotopy (𝟙 (mappingCone e.hom)) 0) :=
  have : IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map e.hom) :=
    inferInstanceAs (IsIso (HomotopyCategory.isoOfHomotopyEquiv e).hom)
  nonempty_homotopy_id_zero_of_isIso_quotient_map e.hom

end CochainComplex.mappingCone
