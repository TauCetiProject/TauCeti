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
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.EssImage
public import TauCeti.CategoryTheory.Monoidal.Closed.Curry

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

Into the nerve of a category the comparison is an isomorphism of categories, so that
`ho Fun(A, N C)` is the category of functors `ho A ⥤ ho (N C)`. Indeed `Fun(A, N C)` is strict
Segal, hence the nerve of its homotopy category, and maps `Y ⟶ Fun(A, N C)` correspond to functors
`ho A × ho Y ⥤ C` because the homotopy category functor preserves binary products; by the Yoneda
lemma, the comparison is therefore an isomorphism after taking nerves.

## Main declarations

* `SSet.ihomHoFunctor A B`: the functor `ho Fun(A, B) ⥤ (ho A ⥤ ho B)`.
* `SSet.ihomHoFunctor_obj_mk`: its value on a vertex of `Fun(A, B)` is the functor of homotopy
  categories induced by the corresponding map `A ⟶ B`.
* `SSet.ihomHoFunctor_obj_mk_obj_mk`: the functor induced by a vertex `f` of `Fun(A, B)` sends
  a vertex `a` to the evaluation of `f` at `a`.
* `SSet.ihomHoFunctor_map_homMk_app`: the component at `a` of the natural transformation
  induced by an edge `h` of `Fun(A, B)` is the evaluation of `h` at `a`.
* `SSet.ihomHoFunctor_obj_mapHomotopyCategory_pre_app`: the comparison is natural in the source,
  turning precomposition with `f` into precomposition with `ho f`.
* `SSet.isIso_expComparison_app_nerve`, `SSet.isEquivalence_ihomHoFunctor_nerve`: into a nerve,
  the comparison is an isomorphism of categories.
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

/-- On the vertex corresponding to `g : A ⟶ B` under `ihomObj₀Equiv`, the comparison is the
induced functor `ho g`. -/
@[simp]
lemma ihomHoFunctor_obj_mk_ihomObj₀Equiv_symm (g : A ⟶ B) :
    (ihomHoFunctor A B).obj (.mk ((ihomObj₀Equiv A B).symm g)) = mapHomotopyCategory g := by
  rw [ihomObj₀Equiv_symm_eq_unitHomEquiv, ihomHoFunctor_obj_mk, MonoidalClosed.uncurry'_curry']

/-- **Naturality of the comparison in the source**: under the comparisons
`ho Fun(-, B) ⥤ (ho - ⥤ ho B)`, precomposition with `f : A' ⟶ A` on `Fun(A, B)` corresponds to
precomposition with `ho f`. -/
lemma ihomHoFunctor_obj_mapHomotopyCategory_pre_app {A' : SSet.{u}} (f : A' ⟶ A)
    (a : ((ihom A).obj B).HomotopyCategory) :
    (ihomHoFunctor A' B).obj
        ((mapHomotopyCategory ((MonoidalClosed.pre f).app B)).obj a) =
      mapHomotopyCategory f ⋙ (ihomHoFunctor A B).obj a := by
  induction a with | mk v =>
    obtain ⟨g, rfl⟩ := (ihomObj₀Equiv A B).symm.surjective v
    rw [mapHomotopyCategory_obj_mk, pre_app_app_ihomObj₀Equiv_symm,
      ihomHoFunctor_obj_mk_ihomObj₀Equiv_symm, ihomHoFunctor_obj_mk_ihomObj₀Equiv_symm]
    exact congrArg Cat.Hom.toFunctor (hoFunctor.map_comp f g)

open CartesianMonoidalCategory MonoidalClosed in
/-- Under the comparison `ho Fun(A, N C) ⥤ (ho A ⥤ ho (N C))` followed by the counit
`ho (N C) ⥤ C`, the functor `ho Y ⥤ ho Fun(A, N C)` induced by a map `σ : Y ⟶ Fun(A, N C)` is
the curried form of the functor `ho A × ho Y ⥤ C` adjoint to the uncurried form of `σ`. -/
private lemma map_comp_expComparison_app_nerve (C : Cat.{u, u}) {Y : SSet.{u}}
    (σ : Y ⟶ (ihom A).obj (nerveFunctor.obj C)) :
    hoFunctor.map σ ≫ (expComparison hoFunctor A).app (nerveFunctor.obj C) ≫
      (ihom (hoFunctor.obj A)).map (nerveAdjunction.counit.app C) =
    curry (inv (prodComparison hoFunctor A Y) ≫
      (nerveAdjunction.homEquiv _ _).symm (uncurry σ)) := by
  apply uncurry_injective
  -- Uncurrying both sides, the left side becomes `ho A ◁ ho σ` followed by the uncurried comparison
  -- `inv (prodComparison hoFunctor A Fun(A, N C)) ≫ ho ev` and the counit, and the right side
  -- becomes `inv (prodComparison hoFunctor A Y) ≫ ho (A ◁ σ ≫ ev)` followed by the counit.
  rw [uncurry_curry, uncurry_natural_left, uncurry_natural_right, uncurry_expComparison,
    Adjunction.homEquiv_counit, uncurry_eq, Functor.map_comp]
  simp only [← Category.assoc]
  congr 2
  -- It remains to see `ho A ◁ ho σ ≫ inv (prodComparison _ A _) =
  -- inv (prodComparison _ A Y) ≫ ho (A ◁ σ)`, the naturality of the product comparison.
  rw [IsIso.comp_inv_eq, Category.assoc, prodComparison_natural_whiskerLeft,
    IsIso.inv_hom_id_assoc]

open CartesianMonoidalCategory MonoidalClosed in
/-- Into the nerve of a category `C`, the comparison `ho Fun(A, N C) ⟶ (ho A ⥤ ho (N C))` is an
isomorphism of categories. -/
instance isIso_expComparison_app_nerve (C : Cat.{u, u}) :
    IsIso ((expComparison hoFunctor A).app (nerveFunctor.obj C)) := by
  -- It suffices that the composite `θ` with the counit `ho (N C) ⟶ C` is an isomorphism, and so
  -- that its adjoint `ψ : Fun(A, N C) ⟶ N(ho A ⥤ C)` is: the unit at the strict Segal
  -- simplicial set `Fun(A, N C)` is an isomorphism and the nerve reflects isomorphisms.
  let θ := (expComparison hoFunctor A).app (nerveFunctor.obj C) ≫
    (ihom (hoFunctor.obj A)).map (nerveAdjunction.counit.app C)
  -- By the Yoneda lemma, `ψ` is an isomorphism since postcomposition with it is a composite of
  -- bijections: uncurrying, the nerve adjunction, the binary product comparison of the homotopy
  -- category functor, currying and the nerve adjunction again.
  have hψ : IsIso (nerveAdjunction.homEquiv _ _ θ) := by
    refine isIso_of_yoneda_map_bijective _ fun Y ↦ ?_
    have h : (fun σ : Y ⟶ _ ↦ σ ≫ nerveAdjunction.homEquiv _ _ θ) = fun σ ↦
        nerveAdjunction.homEquiv _ _ (curry (inv (prodComparison hoFunctor A Y) ≫
          (nerveAdjunction.homEquiv _ _).symm (uncurry σ))) := by
      ext1 σ
      rw [← map_comp_expComparison_app_nerve, ← Adjunction.homEquiv_naturality_left]
      -- The two sides differ only by the identity functor of `Cat` applied to `C`.
      rfl
    rw [h]
    exact (nerveAdjunction.homEquiv _ _).bijective.comp
      (((ihom.adjunction _).homEquiv _ _).bijective.comp
        ((asIso (prodComparison hoFunctor A Y)).homFromEquiv.bijective.comp
        ((nerveAdjunction.homEquiv _ _).symm.bijective.comp
          ((ihom.adjunction A).homEquiv _ _).symm.bijective)))
  have : IsIso (nerveFunctor.map θ) := by
    rw [Adjunction.homEquiv_unit] at hψ
    have : ((ihom A).obj (nerveFunctor.obj C)).IsStrictSegal := isStrictSegal_ihom_nerve A C
    exact IsIso.of_isIso_comp_left (nerveAdjunction.unit.app _) _
  have := isIso_of_fully_faithful nerveFunctor θ
  exact IsIso.of_isIso_comp_right _ ((ihom (hoFunctor.obj A)).map (nerveAdjunction.counit.app C))

/-- Into the nerve of a category `C`, the comparison `ho Fun(A, N C) ⥤ (ho A ⥤ ho (N C))` is an
equivalence of categories. -/
instance isEquivalence_ihomHoFunctor_nerve (C : Type u) [Category.{u} C] :
    (ihomHoFunctor A (nerve C)).IsEquivalence :=
  (Cat.equivOfIso
    (asIso ((expComparison hoFunctor A).app (nerveFunctor.obj (Cat.of C))))).isEquivalence_functor

end SSet
