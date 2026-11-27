/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Discrete
public import TauCeti.Analysis.CStarAlgebra.UniversalUnitary

/-!
# The full group C⋆-algebra of a free group

The universal unital C⋆-algebra `UniversalUnitaryCStarAlgebra ι` on unitary generators indexed
by `ι` is the full group C⋆-algebra `C*(F_ι)` of the free group `F_ι = FreeGroup ι`, that is, the
full crossed product of the trivial action of the discrete group `F_ι` on `ℂ` with counting
measure. For `ι = ℕ` this identifies `C*(F_∞)` with the full C⋆-algebra of the free group on
countably many generators.

The two universal properties induce the inverse maps. The generators of
`UniversalUnitaryCStarAlgebra ι` determine the unital ⋆-homomorphism sending the generator `i` to
the canonical unitary `groupUnitary (FreeGroup.of i)` of `C*(F_ι)`
(`UniversalUnitaryCStarAlgebra.lift`). In the other direction, the free group homomorphism
extending the generators is a unitary representation of `F_ι` in
`UniversalUnitaryCStarAlgebra ι`, which integrates to `C*(F_ι)`
(`TauCeti.CStarAction.FullCrossedProduct.liftUnitary`). Both composites fix the generators, so
they are the identities.

The discrete topology and the Borel σ-algebra on `FreeGroup ι` are taken as instance arguments,
since Mathlib puts no topology on free groups.

## Main definitions

* `TauCeti.UniversalUnitaryCStarAlgebra.equivFullCrossedProduct`: the ⋆-isomorphism between the
  universal unital C⋆-algebra on unitary generators indexed by `ι` and the full group
  C⋆-algebra of `FreeGroup ι`, sending each generator to the canonical unitary of the
  corresponding basis element.

## References

* B. Blackadar, *Operator Algebras*, II.8.3.1–II.8.3.2.
* K. R. Davidson, *C*-Algebras by Example*, Chapter VII.
-/

public section

noncomputable section

open MeasureTheory TauCeti.CStarAction TauCeti.CStarAction.FullCrossedProduct

namespace TauCeti.UniversalUnitaryCStarAlgebra

variable (ι : Type*) [TopologicalSpace (FreeGroup ι)] [DiscreteTopology (FreeGroup ι)]
  [MeasurableSpace (FreeGroup ι)] [BorelSpace (FreeGroup ι)]

/-- **The universal unital C⋆-algebra on unitary generators indexed by `ι` is the full group
C⋆-algebra of the free group on `ι`**: the generator `i` corresponds to the canonical unitary
`groupUnitary (FreeGroup.of i)`. For `ι = ℕ` this is `C*(F_∞)`. The map and its inverse are given
by the two universal properties (`toStarAlgHom_equivFullCrossedProduct` and
`toStarAlgHom_equivFullCrossedProduct_symm`). -/
def equivFullCrossedProduct :
    UniversalUnitaryCStarAlgebra ι ≃⋆ₐ[ℂ]
      FullCrossedProduct (trivial : CStarAction (FreeGroup ι) ℂ) Measure.count :=
  StarAlgEquiv.ofStarAlgHom
    (lift ι _ fun i => groupUnitary (trivial : CStarAction (FreeGroup ι) ℂ) (FreeGroup.of i))
    (liftUnitary _ _ (FreeGroup.lift (generator ι)))
    (hom_ext fun i => by simp)
    ((liftUnitary _ _).symm.injective <| FreeGroup.ext_hom _ _ fun i => Subtype.ext (by simp))

/-- The ⋆-isomorphism `equivFullCrossedProduct` is the unital ⋆-homomorphism given by the
universal property of `UniversalUnitaryCStarAlgebra ι` on the canonical unitaries of the basis
elements. -/
theorem toStarAlgHom_equivFullCrossedProduct :
    (equivFullCrossedProduct ι).toStarAlgHom =
      lift ι _ fun i => groupUnitary (trivial : CStarAction (FreeGroup ι) ℂ) (FreeGroup.of i) :=
  (rfl)

/-- The inverse of `equivFullCrossedProduct` is the unital ⋆-homomorphism given by the universal
property of the full group C⋆-algebra on the free group homomorphism extending the
generators. -/
theorem toStarAlgHom_equivFullCrossedProduct_symm :
    (equivFullCrossedProduct ι).symm.toStarAlgHom =
      liftUnitary _ _ (FreeGroup.lift (generator ι)) :=
  (rfl)

variable {ι}

/-- `equivFullCrossedProduct` sends the generator `i` to the canonical unitary of the basis
element `FreeGroup.of i`. -/
@[simp]
theorem equivFullCrossedProduct_generator (i : ι) :
    equivFullCrossedProduct ι (generator ι i) =
      groupUnitary (trivial : CStarAction (FreeGroup ι) ℂ) (FreeGroup.of i) :=
  lift_generator _ i

/-- The inverse of `equivFullCrossedProduct` sends the canonical unitary of a free group element
`w` to the word in the generators that `w` represents. -/
@[simp]
theorem equivFullCrossedProduct_symm_groupUnitary (w : FreeGroup ι) :
    (equivFullCrossedProduct ι).symm (groupUnitary (trivial : CStarAction (FreeGroup ι) ℂ) w) =
      FreeGroup.lift (generator ι) w :=
  liftUnitary_groupUnitary _ w

end TauCeti.UniversalUnitaryCStarAlgebra
