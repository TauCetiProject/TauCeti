/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import TauCeti.AlgebraicTopology.SimplicialNerve.SimplicialThickening
public import TauCeti.CategoryTheory.Enriched.EnrichedCat

/-!
# The simplicial nerve as a functor, and its low-dimensional simplices

This file makes Mathlib's simplicial (homotopy coherent) nerve `SimplicialNerve C` of a
simplicial category `C` functorial in simplicial functors, and identifies its vertices and edges.

A functor `G : J ⥤ C` out of a linear order induces a simplicial functor
`SimplicialThickening.ofFunctor G : C[Δ^J] ⥤ C`, which sends every chain of paths from `i` to `j`
to the image of the unique morphism `i ⟶ j`. Applied to `J = Fin (n + 1)` this gives a map of
simplicial sets `SimplicialNerve.fromNerve C : nerve C ⟶ SimplicialNerve C` from the ordinary nerve
of the underlying category. When no element of `J` lies strictly between two others, every poset
of paths is a subsingleton and `ofFunctor` is a bijection (`SimplicialThickening.functorEquiv`).
Hence `fromNerve C` is bijective in degrees `0` and `1`: the vertices of `SimplicialNerve C` are
the objects of `C` and its edges are the morphisms of `C`. In higher degrees `fromNerve C` need not
be surjective: a `2`-simplex of `SimplicialNerve C` with edges `f`, `g` and `h` records an edge
from `g ∘ f` to `h` in a mapping simplicial set, not an equality.

## Main declarations

* `CategoryTheory.simplicialNerveMap`: the map of simplicial nerves induced by a simplicial
  functor.
* `CategoryTheory.simplicialNerveFunctor`: the simplicial nerve as a functor from the category of
  small simplicial categories to simplicial sets.
* `CategoryTheory.SimplicialThickening.functorEquiv`: simplicial functors out of `C[Δ^J]` are
  ordinary functors out of `J`, when all posets of paths are subsingletons.
* `CategoryTheory.SimplicialNerve.fromNerve`: the comparison map from the ordinary nerve of the
  underlying category, with `bijective_fromNerve_app` in degrees at most one.
* `CategoryTheory.SimplicialNerve.vertexEquiv`: vertices of `SimplicialNerve C` are objects of `C`.
* `CategoryTheory.SimplicialNerve.homEquiv`: edges of `SimplicialNerve C` are morphisms of `C`.

## References

* [Jacob Lurie, *Higher Topos Theory*, Section 1.1.5][LurieHTT]
-/

public section

open CategoryTheory EnrichedCategory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial

universe v u

namespace CategoryTheory

section Functoriality

variable {C D E : Type u} [Category.{v} C] [SimplicialCategory C] [Category.{v} D]
  [SimplicialCategory D] [Category.{v} E] [SimplicialCategory E]

/-- The map of simplicial nerves induced by a simplicial functor, given by postcomposition. -/
def simplicialNerveMap (F : EnrichedFunctor SSet C D) : SimplicialNerve C ⟶ SimplicialNerve D where
  app _ := ↾fun G ↦ G.comp SSet F
  naturality _ _ _ := by
    ext G
    exact EnrichedFunctor.comp_assoc (V := SSet) _ _ _

@[simp]
lemma simplicialNerveMap_app (F : EnrichedFunctor SSet C D) (n : SimplexCategoryᵒᵖ)
    (G : (SimplicialNerve C).obj n) :
    (simplicialNerveMap F).app n G = EnrichedFunctor.comp SSet G F :=
  (rfl)

@[simp]
lemma simplicialNerveMap_id : simplicialNerveMap (EnrichedFunctor.id SSet C) = 𝟙 _ := by
  ext n G
  exact EnrichedFunctor.comp_id (V := SSet) _

lemma simplicialNerveMap_comp (F : EnrichedFunctor SSet C D) (G : EnrichedFunctor SSet D E) :
    simplicialNerveMap (F.comp SSet G) = simplicialNerveMap F ≫ simplicialNerveMap G := by
  ext n H
  exact (EnrichedFunctor.comp_assoc (V := SSet) _ _ _).symm

/-- The simplicial nerve, as a functor from the category of simplicial categories and simplicial
functors to simplicial sets. -/
@[expose]
def simplicialNerveFunctor : EnrichedCat.{v, v + 1, u} SSet.{v} ⥤ SSet.{max u v} where
  obj C := SimplicialNerve (ForgetEnrichment SSet C)
  map F := simplicialNerveMap F
  map_id _ := simplicialNerveMap_id
  map_comp {X Y Z} F G := simplicialNerveMap_comp (C := ForgetEnrichment SSet X)
    (D := ForgetEnrichment SSet Y) (E := ForgetEnrichment SSet Z) F G

end Functoriality

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

namespace SimplicialThickening

variable {J : Type v} [LinearOrder J]

/-- The map of mapping simplicial sets underlying `ofFunctor G`: a chain of paths from `i` to `j`
is sent to the image under `G` of the morphism `i ⟶ j`. -/
def ofFunctorMap (G : J ⥤ C) (i j : SimplicialThickening J) :
    (i ⟶[SSet] j) ⟶ (G.obj i.as ⟶[SSet] G.obj j.as) where
  app n := ↾fun p ↦ (eHomEquiv SSet (G.map (homOfLE (Path.le (p.obj 0))))).app n PUnit.unit
  naturality _ _ f := by
    ext p
    simpa using ConcreteCategory.congr_hom
      ((eHomEquiv SSet (G.map (homOfLE (Path.le (p.obj 0))))).naturality f) PUnit.unit

/-- On a pair `i ≤ j`, the map `ofFunctorMap G i j` is constant at the image of `i ⟶ j`. -/
lemma ofFunctorMap_eq {G : J ⥤ C} {i j : SimplicialThickening J} (h : i.as ≤ j.as) :
    ofFunctorMap G i j = toUnit _ ≫ eHomEquiv SSet (G.map (homOfLE h)) :=
  (rfl)

/-- The maps `ofFunctorMap G` preserve identities. -/
lemma eId_comp_ofFunctorMap (G : J ⥤ C) (i : SimplicialThickening J) :
    eId SSet i ≫ ofFunctorMap G i i = eId SSet (G.obj i.as) := by
  rw [ofFunctorMap_eq le_rfl, Subsingleton.elim (homOfLE _) (𝟙 i.as), Functor.map_id,
    eHomEquiv_id, comp_toUnit_assoc]
  exact Category.id_comp _

/-- The maps `ofFunctorMap G` preserve composition. -/
lemma eComp_comp_ofFunctorMap (G : J ⥤ C) (i j k : SimplicialThickening J) :
    eComp SSet i j k ≫ ofFunctorMap G i k =
      (ofFunctorMap G i j ⊗ₘ ofFunctorMap G j k) ≫ eComp SSet _ _ _ := by
  by_cases hij : i.as ≤ j.as
  · by_cases hjk : j.as ≤ k.as
    · rw [ofFunctorMap_eq hij, ofFunctorMap_eq hjk, ofFunctorMap_eq (hij.trans hjk),
        ← tensorHom_comp_tensorHom_assoc, ← homOfLE_comp hij hjk, Functor.map_comp,
        eHomEquiv_comp, comp_toUnit_assoc, ← Category.assoc]
      -- The remaining factors are the two maps into the terminal object `𝟙_ SSet ⊗ 𝟙_ SSet`.
      congr 1
    · ext n ⟨p, q⟩
      exact absurd (Path.le (q.obj 0)) hjk
  · ext n ⟨p, q⟩
    exact absurd (Path.le (p.obj 0)) hij

/-- The simplicial functor `C[Δ^J] ⥤ C` induced by an ordinary functor `G : J ⥤ C`. It sends
every chain of paths from `i` to `j` to the image under `G` of the morphism `i ⟶ j`, so it only
depends on the endpoints of the chains. -/
@[expose, implicit_reducible]
def ofFunctor (G : J ⥤ C) : EnrichedFunctor SSet (SimplicialThickening J) C where
  obj i := G.obj i.as
  map := ofFunctorMap G
  map_id := eId_comp_ofFunctorMap G
  map_comp := eComp_comp_ofFunctorMap G

@[simp]
lemma ofFunctor_obj (G : J ⥤ C) (i : SimplicialThickening J) : (ofFunctor G).obj i = G.obj i.as :=
  rfl

lemma ofFunctor_map_eq (G : J ⥤ C) {i j : SimplicialThickening J} (h : i.as ≤ j.as) :
    (ofFunctor G).map i j = toUnit _ ≫ eHomEquiv SSet (G.map (homOfLE h)) :=
  ofFunctorMap_eq h

/-- The vertex of the mapping simplicial set from `i` to `j` given by the path through every
element in between. -/
def pathVertex {i j : SimplicialThickening J} (h : i.as ≤ j.as) : 𝟙_ SSet.{v} ⟶ (i ⟶[SSet] j) :=
  (SSet.unitHomEquiv _).symm (ComposableArrows.mk₀ (Path.Icc h))

/-- Maps into a mapping simplicial set of the simplicial thickening are equal when there is at
most one path between its endpoints. -/
lemma hom_ext_of_subsingleton {X : SSet.{v}} {i j : SimplicialThickening J}
    [Subsingleton (Path i.as j.as)] (f g : X ⟶ (i ⟶[SSet] j)) : f = g := by
  ext n : 2
  ext x
  exact nerve.ext_of_isThin (C := Path i.as j.as) (funext fun _ ↦ Subsingleton.elim _ _)

section Subsingleton

variable [∀ i j : J, Subsingleton (Path i j)]

/-- The ordinary functor underlying a simplicial functor `C[Δ^J] ⥤ C`, when there is at most one
path between any two elements of `J`. -/
@[expose, implicit_reducible]
def toFunctor (F : EnrichedFunctor SSet (SimplicialThickening J) C) : J ⥤ C where
  obj i := F.obj ⟨i⟩
  map {i j} h :=
    (eHomEquiv SSet).symm (pathVertex (i := ⟨i⟩) (j := ⟨j⟩) (leOfHom h) ≫ F.map ⟨i⟩ ⟨j⟩)
  map_id i := by
    rw [hom_ext_of_subsingleton (pathVertex _) (eId SSet (⟨i⟩ : SimplicialThickening J)),
      EnrichedFunctor.map_id, ← eHomEquiv_id, Equiv.symm_apply_apply]
  map_comp {i j k} f g := by
    apply (eHomEquiv SSet).injective
    rw [eHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      ← tensorHom_comp_tensorHom_assoc, ← EnrichedFunctor.map_comp, ← Category.assoc,
      ← Category.assoc]
    congr 1
    exact hom_ext_of_subsingleton _ _

@[simp]
lemma toFunctor_obj (F : EnrichedFunctor SSet (SimplicialThickening J) C) (i : J) :
    (toFunctor F).obj i = F.obj ⟨i⟩ :=
  rfl

lemma eHomEquiv_toFunctor_map (F : EnrichedFunctor SSet (SimplicialThickening J) C) {i j : J}
    (h : i ⟶ j) :
    eHomEquiv SSet ((toFunctor F).map h) =
      pathVertex (i := ⟨i⟩) (j := ⟨j⟩) (leOfHom h) ≫ F.map ⟨i⟩ ⟨j⟩ :=
  Equiv.apply_symm_apply _ _

/-- When there is at most one path between any two elements of `J`, simplicial functors out of
the simplicial thickening `C[Δ^J]` are ordinary functors out of `J`. This applies to linear orders
with at most two elements, which give the vertices and edges of the simplicial nerve. -/
def functorEquiv : (J ⥤ C) ≃ EnrichedFunctor SSet (SimplicialThickening J) C where
  toFun := ofFunctor
  invFun := toFunctor
  left_inv G := Functor.ext (fun _ ↦ rfl) fun i j h ↦ by
    dsimp only [toFunctor]
    rw [ofFunctor_map_eq _ (leOfHom h), comp_toUnit_assoc, toUnit_unit, Category.id_comp]
    exact (Equiv.symm_apply_apply _ _).trans (by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact congrArg G.map (Subsingleton.elim _ _))
  right_inv F := by
    refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) fun ⟨i⟩ ⟨j⟩ ↦ ?_
    by_cases h : i ≤ j
    · rw [ofFunctor_map_eq _ h]
      dsimp only [toFunctor]
      rw [Equiv.apply_symm_apply, ← Category.assoc,
        hom_ext_of_subsingleton (toUnit _ ≫ pathVertex _) (𝟙 _), Category.id_comp]
      simp
    · ext n p
      exact absurd (Path.le (p.obj 0)) h

@[simp]
lemma functorEquiv_apply (G : J ⥤ C) : functorEquiv G = ofFunctor G :=
  (rfl)

@[simp]
lemma functorEquiv_symm_apply (F : EnrichedFunctor SSet (SimplicialThickening J) C) :
    functorEquiv.symm F = toFunctor F :=
  (rfl)

end Subsingleton

end SimplicialThickening

namespace SimplicialNerve

variable (C)

/-- The comparison map from the ordinary nerve of the underlying category of a simplicial
category `C` to its simplicial nerve. An `n`-simplex `G : Fin (n + 1) ⥤ C` is sent to the
simplicial functor `SimplicialThickening.ofFunctor G`. -/
def fromNerve : nerve C ⟶ SimplicialNerve C where
  app n := ↾fun G ↦ SimplicialThickening.ofFunctor
    ((Monotone.functor (f := (ULift.down : ULift.{v} (Fin (n.unop.len + 1)) → _))
      fun _ _ h ↦ h) ⋙ G)
  naturality _ _ _ := by
    ext G
    refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) fun _ _ ↦ ?_
    ext k p
    rfl

lemma fromNerve_app_apply (n : SimplexCategoryᵒᵖ) (G : (nerve C).obj n) :
    (fromNerve C).app n G = SimplicialThickening.ofFunctor
      ((Monotone.functor (f := (ULift.down : ULift.{v} (Fin (n.unop.len + 1)) → _))
        fun _ _ h ↦ h) ⋙ G) :=
  (rfl)

/-- The comparison map from the ordinary nerve is bijective on vertices and on edges. -/
theorem bijective_fromNerve_app {n : SimplexCategoryᵒᵖ} (hn : n.unop.len ≤ 1) :
    Function.Bijective ((fromNerve C).app n) := by
  have (i j : ULift.{v} (Fin (n.unop.len + 1))) :
      Subsingleton (SimplicialThickening.Path i j) :=
    SimplicialThickening.Path.subsingleton_of_forall_not_lt fun k hik hkj ↦ by
      have h₁ : i.down.val < k.down.val := hik
      have h₂ : k.down.val < j.down.val := hkj
      have h₃ := j.down.isLt
      omega
  let U := Monotone.functor (f := (ULift.down : ULift.{v} (Fin (n.unop.len + 1)) → _))
    fun _ _ h ↦ h
  let U' := Monotone.functor (f := (ULift.up : Fin (n.unop.len + 1) → ULift.{v} _)) fun _ _ h ↦ h
  refine Function.bijective_iff_has_inverse.2
    ⟨fun F ↦ U' ⋙ SimplicialThickening.toFunctor F, fun G ↦ ?_, fun F ↦ ?_⟩
  · exact congrArg (U' ⋙ ·) (SimplicialThickening.functorEquiv.left_inv (U ⋙ G))
  · exact SimplicialThickening.functorEquiv.right_inv F

/-- The vertices of the simplicial nerve of `C` are the objects of `C`. -/
def vertexEquiv : SimplicialNerve C _⦋0⦌ ≃ C where
  toFun x := x.obj ⟨⟨0⟩⟩
  invFun x := (fromNerve C).app (op ⦋0⦌) (nerveEquiv.symm x)
  left_inv x := by
    obtain ⟨G, rfl⟩ := (bijective_fromNerve_app C (n := op ⦋0⦌) zero_le_one).2 x
    exact congrArg ((fromNerve C).app _) (nerveEquiv.left_inv G)
  right_inv _ := rfl

@[simp]
lemma vertexEquiv_apply (x : SimplicialNerve C _⦋0⦌) : vertexEquiv C x = x.obj ⟨⟨0⟩⟩ :=
  (rfl)

lemma vertexEquiv_symm_apply (x : C) :
    (vertexEquiv C).symm x = (fromNerve C).app (op ⦋0⦌) (nerveEquiv.symm x) :=
  (rfl)

variable {C}

/-- The edge of the simplicial nerve given by a morphism of the underlying category. -/
def edgeMk {x y : C} (f : x ⟶ y) :
    (SimplicialNerve C).Edge ((vertexEquiv C).symm x) ((vertexEquiv C).symm y) :=
  (nerve.edgeMk f).map (fromNerve C)

@[simp]
lemma edgeMk_edge {x y : C} (f : x ⟶ y) :
    (edgeMk f).edge = (fromNerve C).app (op ⦋1⦌) (ComposableArrows.mk₁ f) :=
  (rfl)

lemma edgeMk_injective {x y : C} : Function.Injective (edgeMk : (x ⟶ y) → _) := fun f g h ↦ by
  have := (bijective_fromNerve_app C (n := op ⦋1⦌) le_rfl).1 (congrArg SSet.Edge.edge h)
  have h' := congrArg nerve.homEquiv (SSet.Edge.ext this : nerve.edgeMk f = nerve.edgeMk g)
  rwa [nerve.homEquiv_edgeMk, nerve.homEquiv_edgeMk] at h'

lemma edgeMk_surjective {x y : C} : Function.Surjective (edgeMk : (x ⟶ y) → _) := fun e ↦ by
  have h₀ := (bijective_fromNerve_app C (n := op ⦋0⦌) zero_le_one).1
  obtain ⟨g, hg⟩ := (bijective_fromNerve_app C (n := op ⦋1⦌) le_rfl).2 e.edge
  have hsrc : (nerve C).δ 1 g = nerveEquiv.symm x :=
    h₀ (by rw [SSet.δ_naturality_apply, hg, e.src_eq]; rfl)
  have htgt : (nerve C).δ 0 g = nerveEquiv.symm y :=
    h₀ (by rw [SSet.δ_naturality_apply, hg, e.tgt_eq]; rfl)
  obtain ⟨f, hf⟩ := nerve.edgeMk_surjective (SSet.Edge.mk g hsrc htgt)
  exact ⟨f, SSet.Edge.ext (by rw [edgeMk_edge, ← nerve.edgeMk_edge, hf]; exact hg)⟩

/-- The edges of the simplicial nerve between the vertices given by two objects are the
morphisms between these objects. -/
noncomputable def homEquiv {x y : C} :
    (SimplicialNerve C).Edge ((vertexEquiv C).symm x) ((vertexEquiv C).symm y) ≃ (x ⟶ y) :=
  (Equiv.ofBijective _ ⟨edgeMk_injective, edgeMk_surjective⟩).symm

@[simp]
lemma homEquiv_edgeMk {x y : C} (f : x ⟶ y) : homEquiv (edgeMk f) = f :=
  (Equiv.ofBijective _ ⟨edgeMk_injective, edgeMk_surjective⟩).symm_apply_apply f

@[simp]
lemma edgeMk_homEquiv {x y : C}
    (e : (SimplicialNerve C).Edge ((vertexEquiv C).symm x) ((vertexEquiv C).symm y)) :
    edgeMk (homEquiv e) = e :=
  (Equiv.ofBijective _ ⟨edgeMk_injective, edgeMk_surjective⟩).apply_symm_apply e

end SimplicialNerve

end CategoryTheory
