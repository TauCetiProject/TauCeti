/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtration.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Algebra.Order.Group.Int

/-!
# Quotients of filtered objects

For a `FilteredObject`, the cokernels of the inclusions into its underlying object form
its quotient diagram. The underlying object maps to this diagram via the cokernel
projections. For an individual transition, taking the cokernel instead yields the
subquotient of the two steps, functorially in the filtered object. In particular,
for an integer-indexed decreasing filtration this yields the graded pieces
`Fᵖ / Fᵖ⁺¹`.

See [Stacks, Tag 0121](https://stacks.math.columbia.edu/tag/0121) for the associated graded
of a filtered object. The constructions use Mathlib's cokernel functor `coker`.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.FilteredObject

variable {C I : Type*} [Category* C] [Category* I] [HasZeroMorphisms C] [HasCokernels C]

/-- The diagram of inclusions of the steps of `F` into its underlying object. -/
private def quotientArrows (F : FilteredObject C I) : I ⥤ Arrow C where
  obj i := Arrow.mk (F.filtration.ι.app i)
  map f := Arrow.homMk (F.filtrationDiagram.map f) (𝟙 _) (by
    simpa using F.filtration.ι.naturality f)
  map_id i := by ext <;> simp
  map_comp f g := by ext <;> simp

/-- The diagram of quotients of the underlying object by the filtration steps. -/
def quotientDiagram (F : FilteredObject C I) : I ⥤ C := F.quotientArrows ⋙ coker C

@[simp]
lemma quotientDiagram_obj (F : FilteredObject C I) (i : I) :
    F.quotientDiagram.obj i = cokernel (F.filtration.ι.app i) := (rfl)

/-- The pointwise projections from the underlying object onto its quotients. -/
def quotientπ (F : FilteredObject C I) : (Functor.const I).obj F.X ⟶ F.quotientDiagram where
  app i := (coker.π C).app (F.quotientArrows.obj i)
  naturality _ _ f := (coker.π C).naturality (F.quotientArrows.map f)

/-- The canonical cone over the quotients, with the underlying object as cone point. -/
abbrev quotientCone (F : FilteredObject C I) : Cone F.quotientDiagram := ⟨F.X, F.quotientπ⟩

@[reassoc (attr := simp)]
lemma ι_quotientπ_app (F : FilteredObject C I) (i : I) :
    F.filtration.ι.app i ≫ F.quotientπ.app i = 0 := cokernel.condition _

/-- Each leg of the quotient cone is a cokernel projection of the corresponding inclusion. -/
def quotientπIsCokernel (F : FilteredObject C I) (i : I) :
    IsColimit (CokernelCofork.ofπ (F.quotientπ.app i) (F.ι_quotientπ_app i)) :=
  cokernelIsCokernel _

instance (F : FilteredObject C I) (i : I) : Epi (F.quotientπ.app i) :=
  inferInstanceAs (Epi (cokernel.π (F.filtration.ι.app i)))

/-- The transition of the quotient diagram is induced by the identity of the underlying object. -/
@[reassoc (attr := simp)]
lemma π_quotientDiagram_map (F : FilteredObject C I) {i j : I} (f : i ⟶ j) :
    F.quotientπ.app i ≫ F.quotientDiagram.map f = F.quotientπ.app j :=
  F.quotientCone.w f

/-- The filtration transition `f`, regarded as an arrow functorial in the filtered object. -/
private def transitionArrow {i j : I} (f : i ⟶ j) : FilteredObject C I ⥤ Arrow C where
  obj F := Arrow.mk (F.filtrationDiagram.map f)
  map g := Arrow.homMk (g.natTrans.app i) (g.natTrans.app j) (g.natTrans.naturality f).symm
  map_id F := by ext <;> simp
  map_comp g h := by ext <;> simp

/-- The quotient of step `j` by step `i` along `f`, as a functor of filtered objects. -/
def subquotientFunctor {i j : I} (f : i ⟶ j) : FilteredObject C I ⥤ C :=
  transitionArrow f ⋙ coker C

@[simp]
lemma subquotientFunctor_obj {i j : I} (f : i ⟶ j) (F : FilteredObject C I) :
    (subquotientFunctor f).obj F = cokernel (F.filtrationDiagram.map f) := (rfl)

/-- The projection from step `j` onto its quotient by step `i`. -/
def subquotientπ {i j : I} (f : i ⟶ j) (F : FilteredObject C I) :
    F.filtration.obj j ⟶ (subquotientFunctor f).obj F :=
  (coker.π C).app ((transitionArrow f).obj F)

/-- The transition followed by the projection onto its cokernel is zero. -/
@[reassoc]
lemma map_subquotientπ {i j : I} (f : i ⟶ j) (F : FilteredObject C I) :
    F.filtrationDiagram.map f ≫ subquotientπ f F = 0 := cokernel.condition _

/-- The projection onto the subquotient is a cokernel of the transition. -/
def subquotientπIsCokernel {i j : I} (f : i ⟶ j) (F : FilteredObject C I) :
    IsColimit (CokernelCofork.ofπ (subquotientπ f F) (map_subquotientπ f F)) :=
  cokernelIsCokernel _

instance {i j : I} (f : i ⟶ j) (F : FilteredObject C I) : Epi (subquotientπ f F) :=
  inferInstanceAs (Epi (cokernel.π (F.filtrationDiagram.map f)))

/-- The map on the quotient commutes with the projection from the larger step. -/
@[reassoc (attr := simp)]
lemma subquotientπ_naturality {i j : I} (f : i ⟶ j) {F G : FilteredObject C I} (g : F ⟶ G) :
    subquotientπ f F ≫ (subquotientFunctor f).map g = g.natTrans.app j ≫ subquotientπ f G :=
  ((coker.π C).naturality ((transitionArrow f).map g)).symm

/-- The `p`th graded-piece functor of an integer-indexed decreasing filtration:
`Fᵖ / Fᵖ⁺¹`. -/
abbrev gradedPieceFunctor (p : ℤ) : FilteredObject C ℤᵒᵖ ⥤ C :=
  subquotientFunctor ((homOfLE (Int.le_add_one (le_refl p))).op)

end CategoryTheory.FilteredObject
