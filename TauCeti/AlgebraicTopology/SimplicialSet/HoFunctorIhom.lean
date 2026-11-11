/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal
public import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# The homotopy category of an internal hom

For simplicial sets `A` and `B`, the homotopy category functor preserves binary products, so
Mathlib's exponential comparison `expComparison hoFunctor A` gives a functor
`ho Fun(A, B) ⥤ (ho A ⥤ ho B)`, adjoint to the image `ho A × ho Fun(A, B) ⥤ ho B` of the
evaluation map `A ⊗ Fun(A, B) ⟶ B`. A vertex of `Fun(A, B)`, that is a map `f : A ⟶ B`, is sent to
the induced functor `ho f`, and an edge, that is a homotopy, to a natural transformation.

This describes how the homotopy category functor acts on the hom-categories `ho Fun(A, B)` of
the bicategory of quasicategories. In particular, an invertible natural transformation between
maps of quasicategories gives a natural isomorphism between the induced functors of homotopy
categories.

## Main declarations

* `SSet.ihomHoFunctor A B`: the functor `ho Fun(A, B) ⥤ (ho A ⥤ ho B)`.
* `SSet.ihomHoFunctor_obj_mk`: its value on a vertex of `Fun(A, B)` is the functor of homotopy
  categories induced by the corresponding map `A ⟶ B`.
* `SSet.ihomHoFunctor_obj_mk_obj_mk`: the functor induced by a vertex `f` of `Fun(A, B)` sends
  a vertex `a` to the evaluation of `f` at `a`.
* `SSet.ihomHoFunctor_map_homMk_app`: the component at `a` of the natural transformation
  induced by an edge `h` of `Fun(A, B)` is the evaluation of `h` at `a`.
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

variable {A B : SSet.{u}}

/-- The functor `ho Fun(A, B) ⥤ (ho A ⥤ ho B)` induced by the evaluation map
`A ⊗ Fun(A, B) ⟶ B`: the component at `B` of the exponential comparison of the homotopy category
functor, which preserves binary products. -/
noncomputable def ihomHoFunctor (A B : SSet.{u}) :
    hoFunctor.obj ((ihom A).obj B) ⥤ hoFunctor.obj A ⥤ hoFunctor.obj B :=
  ((expComparison hoFunctor A).app B).toFunctor

/-- The exponential comparison is the currying of the image of the evaluation map under the
homotopy category functor, precomposed with the binary product structure of that functor. -/
private lemma ihomHoFunctor_eq (A B : SSet.{u}) :
    ihomHoFunctor A B =
      (Functor.curry.obj ((Functor.LaxMonoidal.μ hoFunctor A ((ihom A).obj B)).toFunctor ⋙
        (hoFunctor.map ((ihom.ev A).app B)).toFunctor)).flip := by
  have hμ : Functor.LaxMonoidal.μ hoFunctor A ((ihom A).obj B) =
      inv (CartesianMonoidalCategory.prodComparison hoFunctor A ((ihom A).obj B)) := by
    rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory]
    exact IsIso.eq_inv_of_hom_inv_id (CartesianMonoidalCategory.prodComparisonIso _ _ _).hom_inv_id
  refine congrArg Cat.Hom.toFunctor (MonoidalClosed.uncurry_injective
    ((uncurry_expComparison hoFunctor A B).trans ?_))
  rw [← hμ]
  ext1
  exact (Functor.uncurry_obj_curry_obj _).symm

/-- The functor induced by a vertex `f` of `Fun(A, B)` sends a vertex `a` of `A` to the
evaluation of `f` at `a`. -/
@[simp]
lemma ihomHoFunctor_obj_mk_obj_mk (f : ((ihom A).obj B) _⦋0⦌) (a : A _⦋0⦌) :
    ((ihomHoFunctor A B).obj (.mk f)).obj (.mk a) = .mk (((ihom.ev A).app B).app _ (a, f)) := by
  rw [ihomHoFunctor_eq]
  rfl

/-- The component at a vertex `a` of `A` of the natural transformation induced by an edge `h`
of `Fun(A, B)` is the edge of `B` obtained by evaluating `h` at `a`, that is, the image of the
edge `(σ₀ a, h)` of `A ⊗ Fun(A, B)` under the evaluation map. -/
@[simp]
lemma ihomHoFunctor_map_homMk_app {f g : ((ihom A).obj B) _⦋0⦌} (h : Edge f g) (a : A _⦋0⦌) :
    ((ihomHoFunctor A B).map (HomotopyCategory.homMk h)).app (.mk a) =
      eqToHom (ihomHoFunctor_obj_mk_obj_mk f a) ≫
        HomotopyCategory.homMk ((Edge.mk (X := A ⊗ (ihom A).obj B) (x₀ := (a, f)) (x₁ := (a, g))
          (A.σ 0 a, h.edge) (Prod.ext (Edge.id a).src_eq h.src_eq)
          (Prod.ext (Edge.id a).tgt_eq h.tgt_eq)).map ((ihom.ev A).app B)) ≫
        eqToHom (ihomHoFunctor_obj_mk_obj_mk g a).symm := by
  rw [Functor.congr_hom (ihomHoFunctor_eq A B), NatTrans.comp_app, NatTrans.comp_app,
    eqToHom_app, eqToHom_app]
  rfl

private lemma ihomHoFunctor_obj_mk_map_homMk (φ : 𝟙_ SSet ⟶ (ihom A).obj B) {x y : A _⦋0⦌}
    (e : Edge x y) :
    ((Functor.curry.obj ((Functor.LaxMonoidal.μ hoFunctor A ((ihom A).obj B)).toFunctor ⋙
      (hoFunctor.map ((ihom.ev A).app B)).toFunctor)).flip.obj
        (.mk (unitHomEquiv _ φ))).map (HomotopyCategory.homMk e) =
      HomotopyCategory.homMk (e.map (MonoidalClosed.uncurry' φ)) := by
  have h : ((ihom A).obj B).σ 0 (unitHomEquiv _ φ) = φ.app _ PUnit.unit :=
    (NatTrans.naturality_apply φ _ PUnit.unit).symm
  refine congrArg Truncated.HomotopyCategory.homMk (Truncated.Edge.ext ?_)
  -- By definition of the binary product structure of the homotopy category functor, the
  -- left-hand edge is the evaluation of `e` against the degenerate edge on the vertex `φ`.
  change ((ihom.ev A).app B).app _ (e.edge, ((ihom A).obj B).σ 0 (unitHomEquiv _ φ)) = _
  rw [h]
  rfl

/-- On the vertex of `Fun(A, B)` classified by `φ`, the functor `ihomHoFunctor A B` takes the
value `ho f`, where `f : A ⟶ B` corresponds to `φ`. -/
@[simp]
lemma ihomHoFunctor_obj_mk (φ : 𝟙_ SSet ⟶ (ihom A).obj B) :
    (ihomHoFunctor A B).obj (.mk (unitHomEquiv _ φ)) =
      mapHomotopyCategory (MonoidalClosed.uncurry' φ) := by
  -- Both functors agree on objects by definition; on edges this is the previous lemma.
  rw [ihomHoFunctor_eq]
  refine Functor.ext_of_iso (Truncated.HomotopyCategory.mkNatIso (fun _ ↦ Iso.refl _)
    (fun x y e ↦ ?_)) (fun _ ↦ rfl)
  obtain ⟨e, rfl⟩ : ∃ e' : Edge x y, e'.toTruncated = e := ⟨⟨e.edge, e.src_eq, e.tgt_eq⟩, rfl⟩
  have := ihomHoFunctor_obj_mk_map_homMk φ e
  simp only [Iso.refl_hom]
  exact this

end SSet
