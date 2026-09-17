/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Opposite

/-!
# Naturality of the homology of an unopposite complex

For a homological complex `K` in an opposite category `Vᵒᵖ`, Mathlib identifies the homology of
the complex `K.unop` in `V` with the unopposite of the homology of `K`
(`HomologicalComplex.homologyUnop`), and proves that the analogous identification
`HomologicalComplex.homologyOp` is natural (`HomologicalComplex.homologyOp_hom_naturality`).
This file records the naturality of `homologyUnop` itself.

It is what lets a morphism of chain complexes of projectives, read through the contravariant
functor `Hom(-, Y)`, be compared with the induced map on the cohomology of the `Hom`-complexes:
Mathlib's computation of `Ext` from a projective resolution passes through `homologyUnop`.

## Main results

* `TauCeti.HomologicalComplex.homologyUnop_inv_naturality`: the inverse of `homologyUnop` is
  natural in the complex.
-/

public section

open CategoryTheory

namespace TauCeti.HomologicalComplex

variable {V : Type*} [Category* V] [Limits.HasZeroMorphisms V] {ι : Type*} {c : ComplexShape ι}

/-- **`homologyUnop` is natural.** For a morphism `φ : K ⟶ L` of complexes in `Vᵒᵖ`, the square
comparing the unopposite of `homologyMap φ` with the homology map of the unopposite morphism
`L.unop ⟶ K.unop` commutes. -/
theorem homologyUnop_inv_naturality {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    (HomologicalComplex.homologyMap φ i).unop ≫ (K.homologyUnop i).inv =
      (L.homologyUnop i).inv ≫ HomologicalComplex.homologyMap
        ((HomologicalComplex.unopFunctor _ _).map φ.op) i := by
  have h := (Iso.eq_comp_inv (L.unop.homologyOp i)).2
    (HomologicalComplex.homologyOp_hom_naturality
      ((HomologicalComplex.unopFunctor _ _).map φ.op) i)
  exact congrArg Quiver.Hom.unop
    ((Iso.inv_comp_eq (K.unop.homologyOp i)).2 (h.trans (Category.assoc _ _ _)))

end TauCeti.HomologicalComplex
