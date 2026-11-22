/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.BasedTopologicalSpace
public import TauCeti.Topology.WedgeSum

/-!
# The wedge sum is the coproduct of based spaces

The wedge sum `⋁ᵢ Xᵢ` of a family of based spaces, based at its wedge point
(`TauCeti.BasedTopologicalSpace.wedgeSum`), is their coproduct in the category of based spaces.
The coprojections are the inclusions of the summands, and a family of based maps `Xᵢ ⟶ Y`
assembles into a based map out of the wedge sum through the universal property
`TauCeti.WedgeSum.lift` of the underlying space. In particular, the category of based spaces has
all coproducts indexed by types of its universe.

The wedge sum is also the coproduct in the pointed homotopy category, which is the form in which
it enters the wedge axiom of reduced cohomology theories; see
`TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat.WedgeSum`.

## Main declarations

* `TauCeti.BasedTopologicalSpace.wedgeSum`: the wedge sum of a family of based spaces.
* `TauCeti.BasedTopologicalSpace.wedgeSumι` and `TauCeti.BasedTopologicalSpace.wedgeSumDesc`: the
  inclusions of the summands, and the based map out of the wedge sum induced by a family of based
  maps.
* `TauCeti.BasedTopologicalSpace.wedgeSum_hom_ext`: based maps out of a wedge sum agreeing on every
  summand are equal.
* `TauCeti.BasedTopologicalSpace.wedgeSumCofanIsColimit`: the wedge sum is a coproduct.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, the wedge sum in
  "Operations on spaces".
-/

public section

noncomputable section

universe u

open CategoryTheory Limits

namespace TauCeti.BasedTopologicalSpace

variable {ι : Type u} (X : ι → BasedTopologicalSpace.{u})

/-- The **wedge sum** `⋁ᵢ Xᵢ` of a family of based spaces: the wedge sum of the underlying spaces
at their base points, based at the wedge point. -/
@[expose, implicit_reducible] def wedgeSum : BasedTopologicalSpace.{u} where
  carrier := WedgeSum fun i ↦ (X i).basepoint
  basepoint := WedgeSum.base _

/-- The base point of the wedge sum is the wedge point. -/
@[simp]
lemma wedgeSum_basepoint : (wedgeSum X).basepoint = WedgeSum.base fun i ↦ (X i).basepoint :=
  (rfl)

/-- The inclusion `Xᵢ ⟶ ⋁ᵢ Xᵢ` of a summand into the wedge sum, a based map. -/
def wedgeSumι (i : ι) : X i ⟶ wedgeSum X :=
  ⟨WedgeSum.incl (fun i ↦ (X i).basepoint) i, WedgeSum.incl_apply_self i⟩

@[simp]
lemma wedgeSumι_toContinuousMap (i : ι) :
    (wedgeSumι X i).toContinuousMap = WedgeSum.incl (fun i ↦ (X i).basepoint) i :=
  (rfl)

/-- The inclusion of a summand sends a point `y` of `Xᵢ` to its image in the wedge sum. -/
@[simp]
lemma wedgeSumι_apply (i : ι) (y : (X i).carrier) :
    DFunLike.coe (F := Hom (X i) (wedgeSum X)) (wedgeSumι X i) y =
      WedgeSum.incl (fun i ↦ (X i).basepoint) i y :=
  (rfl)

variable {X} {Y : BasedTopologicalSpace.{u}}

/-- The based map `⋁ᵢ Xᵢ ⟶ Y` which is `f i` on the summand `Xᵢ`. -/
def wedgeSumDesc (f : ∀ i, X i ⟶ Y) : wedgeSum X ⟶ Y :=
  ⟨WedgeSum.lift (fun i ↦ (f i).toContinuousMap) Y.basepoint fun i ↦ (f i).map_basepoint,
    WedgeSum.lift_base _ _ _⟩

@[simp]
lemma wedgeSumDesc_toContinuousMap (f : ∀ i, X i ⟶ Y) :
    (wedgeSumDesc f).toContinuousMap =
      WedgeSum.lift (fun i ↦ (f i).toContinuousMap) Y.basepoint fun i ↦ (f i).map_basepoint :=
  (rfl)

/-- The based map out of the wedge sum is `f i` on the image of the summand `Xᵢ`.

The domain of the coercion is stated as the carrier `(wedgeSum X).carrier`, the form produced by
`Hom.coe_toContinuousMap`, rather than the underlying `WedgeSum`, so that `simp` can match it. -/
@[simp]
lemma wedgeSumDesc_apply_incl (f : ∀ i, X i ⟶ Y) (i : ι) (y : (X i).carrier) :
    DFunLike.coe (F := Hom (wedgeSum X) Y) (α := (wedgeSum X).carrier) (wedgeSumDesc f)
        (WedgeSum.incl (fun i ↦ (X i).basepoint) i y) =
      DFunLike.coe (F := Hom (X i) Y) (f i) y := by
  rw [← Hom.coe_toContinuousMap, wedgeSumDesc_toContinuousMap, WedgeSum.lift_incl,
    Hom.coe_toContinuousMap]

/-- The based map out of the wedge sum sends the wedge point to the base point. -/
@[simp]
lemma wedgeSumDesc_apply_base (f : ∀ i, X i ⟶ Y) :
    DFunLike.coe (F := Hom (wedgeSum X) Y) (α := (wedgeSum X).carrier) (wedgeSumDesc f)
      (WedgeSum.base fun i ↦ (X i).basepoint) = Y.basepoint := by
  rw [← Hom.coe_toContinuousMap, wedgeSumDesc_toContinuousMap, WedgeSum.lift_base]

/-- The based map out of the wedge sum restricts to `f i` on the summand `Xᵢ`. -/
@[reassoc]
lemma wedgeSumι_wedgeSumDesc (f : ∀ i, X i ⟶ Y) (i : ι) : wedgeSumι X i ≫ wedgeSumDesc f = f i :=
  Hom.ext <| (Hom.toContinuousMap_comp _ _).trans <|
    ContinuousMap.ext fun _ ↦ WedgeSum.lift_incl _ _ _ i _

/-- The based map out of the wedge sum restricts to `f i` on the summand `Xᵢ`, in the simp normal
form `Hom.comp` of composition of based maps. -/
@[simp]
lemma wedgeSumDesc_comp_wedgeSumι (f : ∀ i, X i ⟶ Y) (i : ι) :
    (wedgeSumDesc f).comp (wedgeSumι X i) = f i :=
  wedgeSumι_wedgeSumDesc f i

/-- **Based maps out of a wedge sum are determined by their restrictions to the summands.** -/
@[ext]
theorem wedgeSum_hom_ext {f g : wedgeSum X ⟶ Y}
    (h : ∀ i, wedgeSumι X i ≫ f = wedgeSumι X i ≫ g) : f = g :=
  Hom.ext <| WedgeSum.hom_ext (f.map_basepoint.trans g.map_basepoint.symm) fun i ↦ by
    simpa [Hom.toContinuousMap_comp] using congrArg Hom.toContinuousMap (h i)

variable (X) in
/-- **The wedge sum is the coproduct of based spaces**, with the inclusions of the summands as
coprojections. -/
def wedgeSumCofanIsColimit : IsColimit (Cofan.mk (wedgeSum X) (wedgeSumι X)) :=
  Cofan.IsColimit.mk _ (fun s ↦ wedgeSumDesc s.inj) (fun s i ↦ wedgeSumι_wedgeSumDesc s.inj i)
    fun s _ hm ↦ wedgeSum_hom_ext fun i ↦ (hm i).trans (wedgeSumι_wedgeSumDesc s.inj i).symm

/-- The category of based spaces has all coproducts indexed by types of its universe, given by the
wedge sums. -/
instance : HasCoproducts.{u} BasedTopologicalSpace.{u} :=
  hasCoproducts_of_colimit_cofans _ fun X ↦ wedgeSumCofanIsColimit X

end TauCeti.BasedTopologicalSpace
