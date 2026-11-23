/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat
public import TauCeti.Topology.Category.BasedTopologicalSpace.WedgeSum

/-!
# The wedge sum is the coproduct in the pointed homotopy category

The wedge sum `⋁ᵢ Xᵢ` of a family of based spaces, with the classes of the inclusions of the
summands, is the coproduct of the `Xᵢ` in the pointed homotopy category
(`TauCeti.PointedHomotopyCat.wedgeSumCofanIsColimit`). Existence of the induced map is the strict
universal property of the wedge sum among based spaces, applied to representatives. Uniqueness
holds because two based maps out of a wedge sum are pointed homotopic as soon as their
restrictions to every summand are (`TauCeti.BasedTopologicalSpace.homotopicRel_wedgeSum_iff`):
pointed homotopies of the summands fix the base points, so they glue along the wedge point. No
hypothesis on the summands is needed, since the cylinder `I × ⋁ᵢ Xᵢ` is a quotient of the
cylinders `I × Xᵢ`, the interval being locally compact.

Consequently the pointed homotopy category has all coproducts indexed by types of its universe,
and the quotient functor from based spaces preserves them. This is the coproduct against which
the wedge axiom of a reduced cohomology theory is stated: a reduced theory, a functor on the
pointed homotopy category, sends this coproduct to the product of its values on the summands.

## Main declarations

* `TauCeti.BasedTopologicalSpace.homotopicRel_wedgeSum_iff`: two based maps out of a wedge sum are
  pointed homotopic exactly when their restrictions to every summand are.
* `TauCeti.PointedHomotopyCat.wedgeSumCofanIsColimit`: the wedge sum is the coproduct in the
  pointed homotopy category.
* `TauCeti.PointedHomotopyCat.instHasCoproducts`: the pointed homotopy category has coproducts.
* `TauCeti.PointedHomotopyCat.instPreservesColimitsOfShapeDiscreteQuotient`: the quotient functor
  from based spaces preserves coproducts.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 for the wedge
  sum, and Section 4.E, p. 448, for the wedge axiom of reduced cohomology theories.
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti

namespace BasedTopologicalSpace

variable {ι : Type u} {X : ι → BasedTopologicalSpace.{u}} {Y : BasedTopologicalSpace.{u}}

/-- **Pointed homotopy of based maps out of a wedge sum is detected on the summands.** Two based
maps out of `⋁ᵢ Xᵢ` are homotopic relative to the wedge point exactly when their restrictions to
every summand `Xᵢ` are homotopic relative to its base point. -/
theorem homotopicRel_wedgeSum_iff {f g : wedgeSum X ⟶ Y} :
    homotopicRel f g ↔ ∀ i, homotopicRel (wedgeSumι X i ≫ f) (wedgeSumι X i ≫ g) := by
  simp only [homotopicRel_iff, comp_eq_hom_comp, Hom.toContinuousMap_comp,
    wedgeSumι_toContinuousMap]
  -- The base point of `wedgeSum X` is the wedge point, and the base points of the summands are
  -- the points at which they are glued.
  exact WedgeSum.homotopicRel_iff.trans (and_iff_right (f.map_basepoint.trans g.map_basepoint.symm))

end BasedTopologicalSpace

namespace PointedHomotopyCat

open BasedTopologicalSpace

variable {ι : Type u} (X : ι → BasedTopologicalSpace.{u})

/-- **The wedge sum is the coproduct in the pointed homotopy category**, with the classes of the
inclusions of the summands as coprojections. -/
noncomputable def wedgeSumCofanIsColimit :
    IsColimit (Cofan.mk (quotient.obj (wedgeSum X)) fun i ↦ quotient.map (wedgeSumι X i)) :=
  -- The cocone point `s.pt` of a cofan is `quotient.obj s.pt.as` only up to structure eta, so the
  -- equations below are assembled as terms, which are checked up to definitional equality.
  Cofan.IsColimit.mk _ (fun s ↦ quotient.map (wedgeSumDesc fun i ↦ quotient.preimage (s.inj i)))
    (fun s i ↦ (quotient.map_comp _ _).symm.trans
      ((congrArg quotient.map (wedgeSumι_wedgeSumDesc _ i)).trans (quotient.map_preimage _)))
    fun s m hm ↦ by
      obtain ⟨m, rfl⟩ := quotient.map_surjective m
      refine (quotient_map_eq_iff _ _).2
        (homotopicRel_iff.1 (homotopicRel_wedgeSum_iff.2 fun i ↦ ?_))
      rw [homotopicRel_iff, ← quotient_map_eq_iff]
      have h := wedgeSumι_wedgeSumDesc (fun i ↦ quotient.preimage (s.inj i)) i
      exact (quotient.map_comp _ _).trans ((hm i).trans ((quotient.map_preimage _).symm.trans
        (congrArg quotient.map h.symm)))

/-- The pointed homotopy category has all coproducts indexed by types of its universe, given by
the wedge sums. -/
instance instHasCoproducts : HasCoproducts.{u} PointedHomotopyCat.{u} :=
  hasCoproducts_of_colimit_cofans _ fun X ↦ wedgeSumCofanIsColimit fun i ↦ (X i).as

/-- The quotient functor from based spaces to the pointed homotopy category preserves coproducts:
it carries the wedge sum to the coproduct of the summands. -/
instance instPreservesColimitsOfShapeDiscreteQuotient (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) quotient.{u} :=
  have (X : ι → BasedTopologicalSpace.{u}) : PreservesColimit (Discrete.functor X) quotient :=
    preservesColimit_of_preserves_colimit_cocone (BasedTopologicalSpace.wedgeSumCofanIsColimit X)
      ((isColimitMapCoconeCofanMkEquiv _ _ _).symm
        (PointedHomotopyCat.wedgeSumCofanIsColimit X))
  preservesColimitsOfShape_of_discrete _

end PointedHomotopyCat

end TauCeti
