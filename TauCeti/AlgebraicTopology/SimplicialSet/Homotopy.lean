/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.SSetPair
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom.Basic

/-!
# Homotopies of simplicial sets and of pairs of simplicial sets

This file supplements `Mathlib/AlgebraicTopology/SimplicialSet/Homotopy.lean` with API for
simplicial homotopies `SSet.Homotopy`, and defines homotopies of morphisms of pairs.

## The cylinder

* `SSet.whiskerLeft_stdSimplex_δ_one`, `SSet.whiskerLeft_stdSimplex_δ_zero`: the two faces
  `X ⊗ Δ[0] ⟶ X ⊗ Δ[1]` are the ends `ι₀` and `ι₁` of the cylinder, after the projection to `X`;
  `SSet.fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_one` and `_zero` state the same after
  the inverse isomorphism `X ≅ X ⊗ Δ[0]`.
* `SSet.whiskerLeft_horn_one_zero_ι`: the inclusion
  `X ⊗ Λ[1, 0] ⟶ X ⊗ Δ[1]` is the end `ι₀`.
* `SSet.lift_const_zero_eq_comp_ι₀`, `SSet.lift_const_one_eq_comp_ι₁`: a map into the cylinder
  which is constant on the interval factors through an end.
* `SSet.range_ι₀_inf_range_ι₁`: the two ends of the cylinder are disjoint.
* `SSet.verticalEdge`: the edge `{v} × Δ[1]` of the cylinder over a vertex `v`, along which a
  homotopy moves the image of `v`; its endpoints are `(v, 0)` and `(v, 1)`
  (`SSet.δ_one_verticalEdge` and `SSet.δ_zero_verticalEdge`).

## Constructions on homotopies

* `SSet.Homotopy.mk'`: the homotopy given by a morphism on the cylinder with prescribed ends.
* `SSet.Homotopy.precomp`, `SSet.Homotopy.postcomp`: composition of a homotopy with a map.
* `SSet.Homotopy.curry`, `SSet.Homotopy.uncurry`: homotopies correspond under the tensor-hom
  adjunction.
* `SSet.Homotopy.op`: opposite reverses a simplicial homotopy.
* `SSet.stdSimplex.contractionLast`: the dual standard-simplex contraction, from the identity
  to the constant map at the last vertex, fixing that vertex. For `Δ[1]` it is maximum.
* `SSet.Homotopy.ulift`, `SSet.Homotopy.ofUlift`, `SSet.Homotopy.uliftEquiv`: homotopies
  transport bijectively along `SSet.uliftFunctor`.
* `SSet.ihomEdgeEquiv`: the vertices of the simplicial set `Fun(X, Z) = (ihom X).obj Z` are the
  maps `X ⟶ Z` (`SSet.ihomObj₀Equiv`, from
  `TauCeti/AlgebraicTopology/SimplicialSet/InternalHom/Basic.lean`), and its edges between two such
  vertices are the homotopies between them.

## The combinatorial homotopy

For the combinatorial homotopy `h` that `SSet.Homotopy.toSimplicialObjectHomotopy` extracts from a
homotopy from `f` to `g`, the file records

* a formula for its values (`SSet.Homotopy.toSimplicialObjectHomotopy_h_apply`);
* its compatibility with a commuting square of homotopies
  (`SSet.Homotopy.toSimplicialObjectHomotopy_h_comm`), which is what makes the chain homotopies of
  the absolute case descend to relative chains;
* where it starts: the initial vertex of `h i x` is the image under `f` of the initial vertex of
  `x`, the first edge of `h (i + 1) x` is the image under `f` of the first edge of `x`, and the
  first edge of `h 0 x` is the track `h 0 x₀` of the initial vertex `x₀` of `x`.  These are what a
  construction transporting data along the initial vertices of simplices, such as twisted chains,
  needs to lift the combinatorial homotopy.

## Homotopies of pairs

A homotopy between morphisms of a pair of simplicial sets, `SSetPair.Homotopy`, consists of a
homotopy on the subcomplexes and a homotopy on the total complexes which agree on the
subcomplexes.  This is the simplicial analogue of `TopPair.Homotopy` in
`Mathlib/Topology/Category/TopPair.lean` (J. Scharmberg), with the same two homotopies and the
same whiskered commuting square.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

open scoped Simplicial

universe w w'

namespace SSet

/-- The face `X ⊗ Δ[0] ⟶ X ⊗ Δ[1]` omitting the vertex `1` is the end `X ⊗ {0}` of the cylinder,
after the projection `X ⊗ Δ[0] ⟶ X`. -/
lemma whiskerLeft_stdSimplex_δ_one (X : SSet.{w}) :
    X ◁ stdSimplex.δ (1 : Fin 2) = fst X Δ[0] ≫ ι₀ := by
  ext : 1 <;> simp [ι₀, stdSimplex.δ_one_eq_const]

/-- The face `X ⊗ Δ[0] ⟶ X ⊗ Δ[1]` omitting the vertex `0` is the end `X ⊗ {1}` of the cylinder,
after the projection `X ⊗ Δ[0] ⟶ X`. -/
lemma whiskerLeft_stdSimplex_δ_zero (X : SSet.{w}) :
    X ◁ stdSimplex.δ (0 : Fin 2) = fst X Δ[0] ≫ ι₁ := by
  ext : 1 <;> simp [ι₁, stdSimplex.δ_zero_eq_const]

/-- The end `X ⊗ {0}` of the cylinder is the face `X ⊗ Δ[0] ⟶ X ⊗ Δ[1]` omitting the vertex `1`,
after the isomorphism `X ≅ X ⊗ Δ[0]`. -/
@[reassoc]
lemma fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_one (X : SSet.{w}) :
    (fstStdSimplexZeroIso X).inv ≫ X ◁ stdSimplex.δ (1 : Fin 2) = ι₀ := by
  rw [whiskerLeft_stdSimplex_δ_one, ← fstStdSimplexZeroIso_hom, Iso.inv_hom_id_assoc]

/-- The end `X ⊗ {1}` of the cylinder is the face `X ⊗ Δ[0] ⟶ X ⊗ Δ[1]` omitting the vertex `0`,
after the isomorphism `X ≅ X ⊗ Δ[0]`. -/
@[reassoc]
lemma fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_zero (X : SSet.{w}) :
    (fstStdSimplexZeroIso X).inv ≫ X ◁ stdSimplex.δ (0 : Fin 2) = ι₁ := by
  rw [whiskerLeft_stdSimplex_δ_zero, ← fstStdSimplexZeroIso_hom, Iso.inv_hom_id_assoc]

/-- The product with the inclusion of the horn `Λ[1, k]` factors through the constant
interval coordinate at `k`. -/
lemma whiskerLeft_horn_one_ι (X : SSet.{w}) (k : Fin 2) :
    X ◁ Λ[1, k].ι = fst X _ ≫ lift (𝟙 X) (const (stdSimplex.obj₀Equiv.symm k)) :=
  CartesianMonoidalCategory.hom_ext _ _ (by simp)
    (by simp [horn_one_ι_eq_const, comp_const])

/-- A map into the cylinder `X ⊗ Δ[1]` whose second component is constant at the vertex `0`
factors through the end `X ⊗ {0}`. -/
lemma lift_const_zero_eq_comp_ι₀ {Z X : SSet.{w}} (f : Z ⟶ X) :
    lift f (const (stdSimplex.obj₀Equiv.symm 0)) = f ≫ ι₀ :=
  CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp [comp_const])

/-- A map into the cylinder `X ⊗ Δ[1]` whose second component is constant at the vertex `1`
factors through the end `X ⊗ {1}`. -/
lemma lift_const_one_eq_comp_ι₁ {Z X : SSet.{w}} (f : Z ⟶ X) :
    lift f (const (stdSimplex.obj₀Equiv.symm 1)) = f ≫ ι₁ :=
  CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp [comp_const])

/-- The inclusion `X ⊗ Λ[1, 0] ⟶ X ⊗ Δ[1]` is the end `X ⊗ {0}` of the cylinder, after the
projection `X ⊗ Λ[1, 0] ⟶ X`. -/
lemma whiskerLeft_horn_one_zero_ι (X : SSet.{w}) : X ◁ Λ[1, 0].ι = fst X _ ≫ ι₀ := by
  simpa only [lift_const_zero_eq_comp_ι₀, Category.id_comp] using whiskerLeft_horn_one_ι X 0

/-- The path coordinate `(a, z, τ) ↦ (z, a)` of a product with a cylinder. -/
@[no_expose]
noncomputable def cylinderPathCoordinate (A Z : SSet.{w}) : A ⊗ (Z ⊗ Δ[1]) ⟶ Z ⊗ A :=
  lift (snd _ _ ≫ fst _ _) (fst _ _)

/-- The two time coordinates `(σ, z, τ) ↦ (σ, τ)` of an iterated cylinder. -/
@[no_expose]
noncomputable def cylinderTimeCoordinates (Z : SSet.{w}) : Δ[1] ⊗ (Z ⊗ Δ[1]) ⟶ Δ[1] ⊗ Δ[1] :=
  lift (fst _ _) (snd _ _ ≫ snd _ _)

/-- The first component of the path coordinate retains the `Z` coordinate. -/
@[reassoc (attr := simp)]
lemma cylinderPathCoordinate_fst (A Z : SSet.{w}) :
    cylinderPathCoordinate A Z ≫ fst _ _ = snd _ _ ≫ fst _ _ :=
  lift_fst _ _

/-- The time component of the path coordinate is the outer parameter. -/
@[reassoc (attr := simp)]
lemma cylinderPathCoordinate_snd (A Z : SSet.{w}) :
    cylinderPathCoordinate A Z ≫ snd _ _ = fst _ _ :=
  lift_snd _ _

/-- The first time coordinate is the outer interval parameter. -/
@[reassoc (attr := simp)]
lemma cylinderTimeCoordinates_fst (Z : SSet.{w}) :
    cylinderTimeCoordinates Z ≫ fst _ _ = fst _ _ :=
  lift_fst _ _

/-- The second time coordinate is the cylinder parameter. -/
@[reassoc (attr := simp)]
lemma cylinderTimeCoordinates_snd (Z : SSet.{w}) :
    cylinderTimeCoordinates Z ≫ snd _ _ = snd _ _ ≫ snd _ _ :=
  lift_snd _ _

/-- Fixing the path time at zero takes the path coordinate to its initial endpoint. -/
@[reassoc]
lemma whiskerRight_δ_one_cylinderPathCoordinate (Z : SSet.{w}) :
    stdSimplex.δ 1 ▷ (Z ⊗ Δ[1]) ≫ cylinderPathCoordinate Δ[1] Z = snd _ _ ≫ fst _ _ ≫ ι₀ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [cylinderPathCoordinate,
    stdSimplex.δ_one_eq_const, comp_const]

/-- Fixing the path time at one takes the path coordinate to its final endpoint. -/
@[reassoc]
lemma whiskerRight_δ_zero_cylinderPathCoordinate (Z : SSet.{w}) :
    stdSimplex.δ 0 ▷ (Z ⊗ Δ[1]) ≫ cylinderPathCoordinate Δ[1] Z = snd _ _ ≫ fst _ _ ≫ ι₁ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [cylinderPathCoordinate,
    stdSimplex.δ_zero_eq_const, comp_const]

/-- Fixing the path time at zero fixes the first of the two time coordinates. -/
@[reassoc]
lemma whiskerRight_δ_one_cylinderTimeCoordinates (Z : SSet.{w}) :
    stdSimplex.δ 1 ▷ (Z ⊗ Δ[1]) ≫ cylinderTimeCoordinates Z =
      lift (const (stdSimplex.obj₀Equiv.symm 0)) (snd _ _ ≫ snd _ _) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [cylinderTimeCoordinates,
    stdSimplex.δ_one_eq_const, comp_const]

/-- Fixing the path time at one fixes the first of the two time coordinates. -/
@[reassoc]
lemma whiskerRight_δ_zero_cylinderTimeCoordinates (Z : SSet.{w}) :
    stdSimplex.δ 0 ▷ (Z ⊗ Δ[1]) ≫ cylinderTimeCoordinates Z =
      lift (const (stdSimplex.obj₀Equiv.symm 1)) (snd _ _ ≫ snd _ _) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [cylinderTimeCoordinates,
    stdSimplex.δ_zero_eq_const, comp_const]

/-- Fixing the homotopy time at zero gives the initial endpoint of the time cylinder. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ι₀_cylinderTimeCoordinates (Z : SSet.{w}) :
    Δ[1] ◁ (ι₀ : Z ⟶ _) ≫ cylinderTimeCoordinates Z = fst _ _ ≫ ι₀ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [cylinderTimeCoordinates, comp_const]

/-- Fixing the homotopy time at one gives the final endpoint of the time cylinder. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ι₁_cylinderTimeCoordinates (Z : SSet.{w}) :
    Δ[1] ◁ (ι₁ : Z ⟶ _) ≫ cylinderTimeCoordinates Z = fst _ _ ≫ ι₁ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [cylinderTimeCoordinates, comp_const]

/-- For a section `g` of the projection `X ⊗ Δ[1] ⟶ X` of the cylinder, applying `g` to the second
factor of `A ⊗ X` and then forgetting the interval coordinate is the braiding `A ⊗ X ⟶ X ⊗ A`. -/
@[reassoc]
lemma whiskerLeft_comp_cylinderPathCoordinate {A X : SSet.{w}} (g : X ⟶ X ⊗ Δ[1])
    (hg : g ≫ fst _ _ = 𝟙 X) :
    A ◁ g ≫ cylinderPathCoordinate A X = (β_ _ _).hom := by
  rw [cylinderPathCoordinate, comp_lift, whiskerLeft_snd_assoc, hg, Category.comp_id,
    whiskerLeft_fst, lift_snd_fst]

/-- The associator identifies the cylinder `A ⊗ (X ⊗ Δ[1])` with `(A ⊗ X) ⊗ Δ[1]`, carrying the
inclusion of `A ⊗ (X ⊗ {0})` to that of `(A ⊗ X) ⊗ {0}`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ι₀_associator_inv (A X : SSet.{w}) :
    A ◁ ι₀ ≫ (α_ A X Δ[1]).inv = ι₀ := by
  ext : 1 <;> [ext : 1; skip] <;> simp [ι₀]

/-- The associator identifies the cylinder `A ⊗ (X ⊗ Δ[1])` with `(A ⊗ X) ⊗ Δ[1]`, carrying the
inclusion of `A ⊗ (X ⊗ {1})` to that of `(A ⊗ X) ⊗ {1}`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ι₁_associator_inv (A X : SSet.{w}) :
    A ◁ ι₁ ≫ (α_ A X Δ[1]).inv = ι₁ := by
  ext : 1 <;> [ext : 1; skip] <;> simp [ι₁]

/-- The two ends `X ⊗ {0}` and `X ⊗ {1}` of the cylinder `X ⊗ Δ[1]` are disjoint. -/
lemma range_ι₀_inf_range_ι₁ {X : SSet.{w}} :
    Subcomplex.range (ι₀ : X ⟶ X ⊗ Δ[1]) ⊓ Subcomplex.range ι₁ = ⊥ := by
  ext ⟨n⟩ z
  induction n using SimplexCategory.rec with | _ n
  simp only [Subfunctor.min_obj, Set.mem_inter_iff, Subfunctor.range_obj, Set.mem_range,
    Subfunctor.bot_obj, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨x, rfl⟩ ⟨y, h⟩
  simpa using congr(($h).2 0)

/-- The edge `{v} × Δ[1]` of the cylinder `X ⊗ Δ[1]` over a vertex `v` of `X`, from `(v, 0)` to
`(v, 1)`. -/
@[no_expose]
noncomputable def verticalEdge {X : SSet.{w}} (v : X _⦋0⦌) : (X ⊗ Δ[1] : SSet.{w}) _⦋1⦌ :=
  (X.σ 0 v, stdSimplex.edge 1 0 1 (by decide))

/-- The component of `verticalEdge v` in `X` is the degenerate edge at `v`. -/
lemma verticalEdge_fst {X : SSet.{w}} (v : X _⦋0⦌) : (verticalEdge v).1 = X.σ 0 v := (rfl)

/-- The component of `verticalEdge v` in `Δ[1]` is the edge from `0` to `1`. -/
lemma verticalEdge_snd {X : SSet.{w}} (v : X _⦋0⦌) :
    (verticalEdge v).2 = stdSimplex.edge 1 0 1 (by decide) := (rfl)

/-- The vertical edge over `v` starts at `(v, 0)`. -/
lemma δ_one_verticalEdge {X : SSet.{w}} (v : X _⦋0⦌) :
    (X ⊗ Δ[1]).δ 1 (verticalEdge v) = ι₀.app _ v :=
  Prod.ext (δ_comp_σ_succ_apply 0 v) (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)

/-- The vertical edge over `v` ends at `(v, 1)`. -/
lemma δ_zero_verticalEdge {X : SSet.{w}} (v : X _⦋0⦌) :
    (X ⊗ Δ[1]).δ 0 (verticalEdge v) = ι₁.app _ v :=
  Prod.ext (δ_comp_σ_self_apply 0 v) (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)

/-- Reversing the interval in an opposite cylinder exchanges its two endpoints. -/
@[reassoc]
lemma lift_const_comp_opIso_inv (X : SSet.{w}) (i : Fin 2) :
    lift (𝟙 X.op) (SSet.const (SSet.stdSimplex.obj₀Equiv.symm i)) ≫
      X.op ◁ (SSet.stdSimplex.opIso ⦋1⦌).inv =
      SSet.opFunctor.map (lift (𝟙 X) (SSet.const (SSet.stdSimplex.obj₀Equiv.symm i.rev))) := by
  apply NatTrans.ext
  funext ⟨m⟩
  apply ConcreteCategory.hom_ext
  intro x
  induction m using SimplexCategory.rec with | _ m
  apply Prod.ext
  · rfl
  · apply SSet.opObjEquiv.injective
    ext j
    fin_cases i <;> rfl

end SSet

namespace SSet.Homotopy

variable {X Y X' Y' : SSet.{w}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} {u : X ⟶ X'} {v : Y ⟶ Y'}

/-- The simplicial homotopy from `f` to `g` given by a morphism `h : X ⊗ Δ[1] ⟶ Y` which is `f`
on `X ⊗ {0}` and `g` on `X ⊗ {1}`. -/
@[simps h]
def mk' (h : X ⊗ Δ[1] ⟶ Y) (h₀ : ι₀ ≫ h = f) (h₁ : ι₁ ≫ h = g) : SSet.Homotopy f g where
  h := h
  h₀ := h₀
  h₁ := h₁
  rel := by
    ext _ ⟨⟨_, hx⟩, _⟩
    simp at hx

/-- Precomposing a homotopy from `f` to `g` with `e : W ⟶ X` gives a homotopy from `e ≫ f` to
`e ≫ g`. This is the absolute case of `SSet.RelativeMorphism.Homotopy.precomp`. -/
@[no_expose]
noncomputable def precomp {W : SSet.{w}} (H : SSet.Homotopy f g) (e : W ⟶ X) :
    SSet.Homotopy (e ≫ f) (e ≫ g) :=
  RelativeMorphism.Homotopy.precomp H (RelativeMorphism.botEquiv.symm e)
    (Subcomplex.isInitialBot.hom_ext _ _)

/-- The precomposite of a homotopy `H` with `e` is `e ▷ Δ[1] ≫ H.h`. -/
@[simp]
lemma precomp_h {W : SSet.{w}} (H : SSet.Homotopy f g) (e : W ⟶ X) :
    (H.precomp e).h = e ▷ Δ[1] ≫ H.h :=
  (rfl)

/-- Postcomposing a homotopy from `f` to `g` with `e : Y ⟶ Z` gives a homotopy from `f ≫ e` to
`g ≫ e`. This is the absolute case of `SSet.RelativeMorphism.Homotopy.postcomp`. -/
@[no_expose]
noncomputable def postcomp {Z : SSet.{w}} (H : SSet.Homotopy f g) (e : Y ⟶ Z) :
    SSet.Homotopy (f ≫ e) (g ≫ e) :=
  RelativeMorphism.Homotopy.postcomp H (RelativeMorphism.botEquiv.symm e)
    (Subcomplex.isInitialBot.hom_ext _ _)

/-- The postcomposite of a homotopy `H` with `e` is `H.h ≫ e`. -/
@[simp]
lemma postcomp_h {Z : SSet.{w}} (H : SSet.Homotopy f g) (e : Y ⟶ Z) :
    (H.postcomp e).h = H.h ≫ e :=
  (rfl)

/-- A homotopy between maps `A ⊗ X ⟶ Y` curries to a homotopy between the adjoint maps
`X ⟶ Fun(A, Y)`. -/
@[no_expose]
noncomputable def curry {A : SSet.{w}} {f g : A ⊗ X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (MonoidalClosed.curry f) (MonoidalClosed.curry g) :=
  mk' (MonoidalClosed.curry ((α_ A X Δ[1]).inv ≫ H.h))
    (by rw [← MonoidalClosed.curry_natural_left, whiskerLeft_ι₀_associator_inv_assoc, H.h₀])
    (by rw [← MonoidalClosed.curry_natural_left, whiskerLeft_ι₁_associator_inv_assoc, H.h₁])

/-- The curried homotopy is the curried map on the reassociated cylinder. -/
@[simp]
lemma curry_h {A : SSet.{w}} {f g : A ⊗ X ⟶ Y} (H : SSet.Homotopy f g) :
    H.curry.h = MonoidalClosed.curry ((α_ A X Δ[1]).inv ≫ H.h) :=
  (rfl)

/-- A homotopy between maps `X ⟶ Fun(A, Y)` uncurries to a homotopy between the adjoint maps
`A ⊗ X ⟶ Y`. -/
@[no_expose]
noncomputable def uncurry {A : SSet.{w}} {f g : X ⟶ (ihom A).obj Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (MonoidalClosed.uncurry f) (MonoidalClosed.uncurry g) :=
  mk' ((α_ A X Δ[1]).hom ≫ MonoidalClosed.uncurry H.h)
    (by rw [← whiskerLeft_ι₀_associator_inv, Category.assoc, Iso.inv_hom_id_assoc,
      ← MonoidalClosed.uncurry_natural_left, H.h₀])
    (by rw [← whiskerLeft_ι₁_associator_inv, Category.assoc, Iso.inv_hom_id_assoc,
      ← MonoidalClosed.uncurry_natural_left, H.h₁])

/-- The uncurried homotopy is the reassociated uncurried map. -/
@[simp]
lemma uncurry_h {A : SSet.{w}} {f g : X ⟶ (ihom A).obj Y} (H : SSet.Homotopy f g) :
    H.uncurry.h = (α_ A X Δ[1]).hom ≫ MonoidalClosed.uncurry H.h :=
  (rfl)

/-- Lifting a simplicial homotopy along `SSet.uliftFunctor`. -/
@[no_expose]
noncomputable def ulift (H : SSet.Homotopy f g) :
    SSet.Homotopy (uliftFunctor.{w', w}.map f) (uliftFunctor.{w', w}.map g) :=
  mk'
    { app m := ↾fun p ↦ ULift.up
        (H.h.app m ⟨p.1.down, stdSimplex.objEquiv.{w}.symm (stdSimplex.objEquiv p.2)⟩)
      naturality m _ α := by
        ext ⟨⟨x⟩, t⟩
        apply ULift.ext
        dsimp
        exact NatTrans.naturality_apply H.h α
          (⟨x, stdSimplex.objEquiv.{w}.symm (stdSimplex.objEquiv t)⟩ :
            (X ⊗ Δ[1]).obj m) }
    (by
      ext m ⟨x⟩
      exact ULift.ext congr($(H.h₀).app m x))
    (by
      ext m ⟨x⟩
      exact ULift.ext congr($(H.h₁).app m x))

/-- On simplices, lifting a homotopy along `SSet.uliftFunctor` evaluates the original homotopy
after unwrapping `ULift` and reindexing the `Δ[1]` coordinate. -/
@[simp]
lemma ulift_h_app_apply (H : SSet.Homotopy f g) (m : SimplexCategoryᵒᵖ)
    (p : (uliftFunctor.{w', w}.obj X).obj m ⊗ (Δ[1] : SSet.{max w w'}).obj m) :
    dsimp% H.ulift.{w, w'}.h.app m p =
      ULift.up (H.h.app m ⟨p.1.down, stdSimplex.objEquiv.{w}.symm (stdSimplex.objEquiv p.2)⟩) :=
  (rfl)

/-- Lowering a simplicial homotopy along `SSet.uliftFunctor`. -/
@[no_expose]
noncomputable def ofUlift
    (H : SSet.Homotopy (uliftFunctor.{w', w}.map f) (uliftFunctor.{w', w}.map g)) :
    SSet.Homotopy f g :=
  mk'
    { app m := ↾fun p ↦
        (H.h.app m ⟨ULift.up p.1,
          stdSimplex.objEquiv.{max w w'}.symm (stdSimplex.objEquiv p.2)⟩).down
      naturality m _ α := by
        ext ⟨x, t⟩
        exact congrArg ULift.down (NatTrans.naturality_apply H.h α
          (⟨ULift.up x, stdSimplex.objEquiv.{max w w'}.symm (stdSimplex.objEquiv t)⟩ :
            (uliftFunctor.{w', w}.obj X ⊗ Δ[1]).obj m)) }
    (by
      ext m x
      exact congrArg ULift.down congr($(H.h₀).app m (ULift.up x)))
    (by
      ext m x
      exact congrArg ULift.down congr($(H.h₁).app m (ULift.up x)))

/-- On simplices, lowering a homotopy along `SSet.uliftFunctor` evaluates the lifted homotopy on
the wrapped simplex and unwraps `ULift`. -/
@[simp]
lemma ofUlift_h_app_apply
    (H : SSet.Homotopy (uliftFunctor.{w', w}.map f) (uliftFunctor.{w', w}.map g))
    (m : SimplexCategoryᵒᵖ) (p : X.obj m ⊗ (Δ[1] : SSet.{w}).obj m) :
    dsimp% H.ofUlift.h.app m p =
      (H.h.app m ⟨ULift.up p.1,
        stdSimplex.objEquiv.{max w w'}.symm (stdSimplex.objEquiv p.2)⟩).down :=
  (rfl)

/-- Lowering a lifted simplicial homotopy recovers the original homotopy. -/
@[simp]
lemma ofUlift_ulift (H : SSet.Homotopy f g) : H.ulift.{w, w'}.ofUlift = H := by
  apply RelativeMorphism.Homotopy.ext
  ext m p
  exact (ofUlift_h_app_apply H.ulift.{w, w'} m p).trans <|
    (congrArg ULift.down (ulift_h_app_apply.{w, w'} H m _)).trans (by simp; rfl)

/-- Lifting a lowered simplicial homotopy recovers the lifted homotopy. -/
@[simp]
lemma ulift_ofUlift
    (H : SSet.Homotopy (uliftFunctor.{w', w}.map f) (uliftFunctor.{w', w}.map g)) :
    H.ofUlift.ulift = H := by
  apply RelativeMorphism.Homotopy.ext
  ext m p
  exact (ulift_h_app_apply H.ofUlift m p).trans <|
    (congrArg ULift.up (ofUlift_h_app_apply H m _)).trans (by simp; rfl)

/-- Simplicial homotopies between maps correspond bijectively to simplicial homotopies between
their universe lifts along `SSet.uliftFunctor`. -/
@[no_expose]
noncomputable def uliftEquiv :
    SSet.Homotopy f g ≃
      SSet.Homotopy (uliftFunctor.{w', w}.map f) (uliftFunctor.{w', w}.map g) where
  toFun := ulift
  invFun := ofUlift
  left_inv := ofUlift_ulift
  right_inv := ulift_ofUlift

/-- Applying `SSet.Homotopy.uliftEquiv` lifts a homotopy along `SSet.uliftFunctor`. -/
@[simp]
lemma uliftEquiv_apply (H : SSet.Homotopy f g) :
    uliftEquiv.{w, w'} H = H.ulift.{w, w'} :=
  (rfl)

/-- Applying `SSet.Homotopy.uliftEquiv.symm` lowers a homotopy along `SSet.uliftFunctor`. -/
@[simp]
lemma uliftEquiv_symm_apply
    (H : SSet.Homotopy (uliftFunctor.{w', w}.map f) (uliftFunctor.{w', w}.map g)) :
    uliftEquiv.{w, w'}.symm H = H.ofUlift :=
  (rfl)

/-- The combinatorial homotopy extracted from a simplicial homotopy sends an `n`-simplex `x` to
the value of the homotopy at the pair formed by the `i`-th degeneracy of `x` and the `n + 1`-simplex
of `Δ[1]` taking the value `0` exactly `i + 1` times. -/
lemma toSimplicialObjectHomotopy_h_apply (H : SSet.Homotopy f g) {n : ℕ} (i : Fin (n + 1))
    (x : X _⦋n⦌) :
    H.toSimplicialObjectHomotopy.h i x =
      H.h.app (op ⦋n + 1⦌) ⟨X.map (SimplexCategory.σ i).op x,
        stdSimplex.objMk₁ i.succ.castSucc⟩ := rfl

/-- Simplicial homotopies which fit into a commutative square induce compatible families of
morphisms `Xₙ ⟶ Y'ₙ₊₁`. -/
lemma toSimplicialObjectHomotopy_h_comm (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (hu : u ▷ Δ[1] ≫ H'.h = H.h ≫ v) (n : ℕ) (i : Fin (n + 1)) :
    u.app (op ⦋n⦌) ≫ H'.toSimplicialObjectHomotopy.h i =
      H.toSimplicialObjectHomotopy.h i ≫ v.app (op ⦋n + 1⦌) := by
  ext x
  simp only [TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
    toSimplicialObjectHomotopy_h_apply, ← NatTrans.naturality_apply u]
  exact congr(($hu).app _ ⟨X.map (SimplexCategory.σ i).op x, stdSimplex.objMk₁ i.succ.castSucc⟩)

/-- The value of the homotopy at a pair whose second component is constant at `0` after
reindexing is the value of `f`. -/
private lemma map_h_app_eq_app (H : SSet.Homotopy f g) {m : SimplexCategoryᵒᵖ} {n : ℕ}
    (φ : m ⟶ op ⦋n⦌) (x : X.obj m) (b : (Δ[1] : SSet.{w}).obj m) (y : X _⦋n⦌)
    (hx : X.map φ x = y) (hb : (Δ[1] : SSet.{w}).map φ b = (ι₀.app _ y).2) :
    Y.map φ (H.h.app m ⟨x, b⟩) = f.app _ y := by
  have e : ((X ⊗ Δ[1]).map φ ⟨x, b⟩ : X _⦋n⦌ × (Δ[1] : SSet.{w}) _⦋n⦌) = ι₀.app _ y :=
    Prod.ext hx hb
  exact (NatTrans.naturality_apply H.h φ _).symm.trans
    ((congrArg (H.h.app _) e).trans congr($(H.h₀).app _ y))

/-- The combinatorial homotopy starts at `f`: the initial vertex of `h i x` is the image under `f`
of the initial vertex of `x`. -/
lemma map_const_toSimplicialObjectHomotopy_h (H : SSet.Homotopy f g) {n : ℕ} (i : Fin (n + 1))
    (x : X _⦋n⦌) :
    Y.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (H.toSimplicialObjectHomotopy.h i x) =
      f.app _ (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op x) := by
  rw [toSimplicialObjectHomotopy_h_apply]
  refine map_h_app_eq_app H _ _ _ _ ?_ ?_
  · rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp]
    rfl
  · ext _ : 1
    exact stdSimplex.objMk₁_of_castSucc_lt.{w} i.succ.castSucc (0 : Fin (n + 2)) (by simp)

/-- For `i ≥ 1`, the first edge of `h i x` is the image under `f` of the first edge of `x`. -/
lemma map_mkOfLe_toSimplicialObjectHomotopy_h_succ (H : SSet.Homotopy f g) {n : ℕ}
    (j : Fin (n + 1)) (x : X _⦋n + 1⦌) :
    Y.map (SimplexCategory.mkOfLe 0 1 (by simp)).op (H.toSimplicialObjectHomotopy.h j.succ x) =
      f.app _ (X.map (SimplexCategory.mkOfLe 0 1 (by simp)).op x) := by
  rw [toSimplicialObjectHomotopy_h_apply]
  refine map_h_app_eq_app H _ _ _ _ ?_ ?_
  · rw [← Functor.map_comp_apply, ← op_comp]
    congr 4
    ext k : 3
    fin_cases k <;> rfl
  · ext k : 1
    fin_cases k <;> rfl

/-- The first edge of `h 0 x` is the track of the homotopy at the initial vertex of `x`. -/
lemma map_mkOfLe_toSimplicialObjectHomotopy_h_zero (H : SSet.Homotopy f g) {n : ℕ}
    (x : X _⦋n⦌) :
    Y.map (SimplexCategory.mkOfLe 0 1 (by simp)).op (H.toSimplicialObjectHomotopy.h 0 x) =
      H.toSimplicialObjectHomotopy.h 0 (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op x) := by
  rw [toSimplicialObjectHomotopy_h_apply, toSimplicialObjectHomotopy_h_apply]
  refine (NatTrans.naturality_apply H.h _ _).symm.trans (congrArg (H.h.app _) ?_)
  refine Prod.ext (α := X _⦋1⦌) (β := (Δ[1] : SSet.{w}) _⦋1⦌) ?_ ?_
  · -- The first components of the two pairs, both iterated reindexings of `x`.
    refine (prod_map_fst X Δ[1] _ _).trans ?_
    rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp]
    congr 4
    ext k : 3
    fin_cases k <;> rfl
  · ext k : 1
    fin_cases k <;> rfl

/-- Opposite reverses the direction of a simplicial homotopy. -/
noncomputable def op (H : SSet.Homotopy f g) :
    SSet.Homotopy (SSet.opFunctor.map g) (SSet.opFunctor.map f) := by
  -- Tensor products are pointwise, so opposite commutes definitionally with the cylinder product.
  refine mk' (X.op ◁ (SSet.stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map H.h) ?_ ?_
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ SSet.opFunctor.map H.h) (lift_const_comp_opIso_inv X 0)).trans
        ((SSet.opFunctor.map_comp _ _).symm.trans (congrArg _ H.h₁)))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ SSet.opFunctor.map H.h) (lift_const_comp_opIso_inv X 1)).trans
        ((SSet.opFunctor.map_comp _ _).symm.trans (congrArg _ H.h₀)))

/-- The opposite homotopy is obtained by reversing the interval in the opposite cylinder. -/
@[simp]
lemma op_h (H : SSet.Homotopy f g) :
    H.op.h = X.op ◁ (SSet.stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map H.h :=
  (rfl)

end SSet.Homotopy

namespace SSet

section MappingSpace

open MonoidalClosed

variable {X Z : SSet.{w}} (f g : X ⟶ Z)

/-- The edges of `Fun(X, Z)` between the vertices corresponding to maps `f` and `g` are the
simplicial homotopies from `f` to `g`, through the tensor-hom adjunction. -/
@[no_expose]
noncomputable def ihomEdgeEquiv :
    Edge ((ihomObj₀Equiv X Z).symm f) ((ihomObj₀Equiv X Z).symm g) ≃ Homotopy f g where
  toFun e := Homotopy.mk' (uncurry (yonedaEquiv.symm e.edge))
    (by
      have h := whiskerLeft_δ_uncurry_yonedaEquiv_symm e.edge 1
      rw [e.src_eq, Equiv.apply_symm_apply, whiskerLeft_stdSimplex_δ_one, Category.assoc] at h
      simpa using lift (𝟙 X) (stdSimplex.isTerminalObj₀.from X) ≫= h)
    (by
      have h := whiskerLeft_δ_uncurry_yonedaEquiv_symm e.edge 0
      rw [e.tgt_eq, Equiv.apply_symm_apply, whiskerLeft_stdSimplex_δ_zero, Category.assoc] at h
      simpa using lift (𝟙 X) (stdSimplex.isTerminalObj₀.from X) ≫= h)
  invFun H := Edge.mk (yonedaEquiv (curry H.h))
    (by
      apply yonedaEquiv.symm.injective
      rw [yonedaEquiv_symm_δ_yonedaEquiv_curry, whiskerLeft_stdSimplex_δ_one, Category.assoc,
        H.h₀, yonedaEquiv_symm_ihomObj₀Equiv_symm])
    (by
      apply yonedaEquiv.symm.injective
      rw [yonedaEquiv_symm_δ_yonedaEquiv_curry, whiskerLeft_stdSimplex_δ_zero, Category.assoc,
        H.h₁, yonedaEquiv_symm_ihomObj₀Equiv_symm])
  left_inv e := by
    ext
    simp
  right_inv H := by
    apply RelativeMorphism.Homotopy.ext
    simp

/-- The homotopy defined by an edge of `Fun(X, Z)` is its uncurried `1`-simplex. -/
@[simp]
lemma ihomEdgeEquiv_apply_h
    (e : Edge ((ihomObj₀Equiv X Z).symm f) ((ihomObj₀Equiv X Z).symm g)) :
    (ihomEdgeEquiv f g e).h = uncurry (yonedaEquiv.symm e.edge) :=
  (rfl)

/-- The edge defined by a homotopy is its curried form. -/
@[simp]
lemma ihomEdgeEquiv_symm_apply_edge (H : Homotopy f g) :
    ((ihomEdgeEquiv f g).symm H).edge = yonedaEquiv (curry H.h) :=
  (rfl)

end MappingSpace

end SSet

namespace SSetPair

/-- A homotopy between morphisms of pairs of simplicial sets consists of a homotopy on the
subcomplexes and a homotopy on the total complexes which agree on the subcomplexes. -/
@[ext]
structure Homotopy {P P' : SSetPair.{w}} (f g : P ⟶ P') where
  /-- The homotopy on the subcomplexes. -/
  left : SSet.Homotopy f.left g.left
  /-- The homotopy on the total complexes. -/
  right : SSet.Homotopy f.right g.right
  /-- The two homotopies agree on the subcomplexes. -/
  w : P.hom ▷ Δ[1] ≫ right.h = left.h ≫ P'.hom

end SSetPair

namespace SSet.stdSimplex

/-- The contraction of the standard simplex `Δ[n]` onto its last vertex: the homotopy from the
identity to the constant map at `Fin.last n` which is the identity over the vertex `0` of `Δ[1]`
and the constant map at `Fin.last n` over the vertex `1`. -/
@[no_expose]
noncomputable def contractionLast (n : ℕ) :
    Homotopy (𝟙 Δ[n]) (SSet.const (obj₀Equiv.symm (Fin.last n))) := by
  let H := ((contraction n).op.precomp (opIso ⦋n⦌).inv).postcomp (opIso ⦋n⦌).hom
  refine Homotopy.mk' H.h ?_ ?_
  · refine H.h₀.trans ?_
    have hi : opFunctor.map (𝟙 (Δ[n] : SSet)) = 𝟙 _ := opFunctor.map_id _
    rw [hi, Category.comp_id, Iso.inv_hom_id]
  · refine H.h₁.trans ?_
    have hc : opFunctor.map (SSet.const (obj₀Equiv.symm (0 : Fin (n + 1))) : Δ[n] ⟶ Δ[n]) ≫
        (opIso ⦋n⦌).hom = SSet.const (obj₀Equiv.symm (Fin.last n)) :=
      opFunctor_map_const_comp_opIso_hom 0
    rw [Category.assoc, hc, comp_const]

/-- Vertexwise evaluation of the standard simplex contraction. -/
@[simp]
lemma contractionLast_h_app_apply {n m : ℕ} (σ : Δ[n] _⦋m⦌) (e : Δ[1] _⦋m⦌)
    (i : Fin (m + 1)) :
    dsimp% (contractionLast n).h.app (op ⦋m⦌) (σ, e) i = if e i = 0 then σ i else Fin.last n :=
by
  simp only [contractionLast, Homotopy.mk'_h, Homotopy.postcomp_h, Homotopy.precomp_h,
    Homotopy.op_h]
  -- The opposite cylinder and the standard-simplex isomorphisms reverse all vertex indices.
  change ((contraction n).h.app (op ⦋m⦌)
    (opObjEquiv ((opIso ⦋n⦌).inv.app _ σ),
      opObjEquiv ((opIso ⦋1⦌).inv.app _ e)) i.rev).rev = _
  refine (congrArg Fin.rev (contraction_h_app_apply
    (opObjEquiv ((opIso ⦋n⦌).inv.app _ σ))
    (opObjEquiv ((opIso ⦋1⦌).inv.app _ e)) i.rev)).trans ?_
  rw [opIso_inv_app_hom_apply, opIso_inv_app_hom_apply,
    opObjEquiv_opObjEquiv_symm_apply, opObjEquiv_opObjEquiv_symm_apply, Fin.rev_rev]
  by_cases h : e i = 0
  · simp [h]
  · have h' : e i = 1 := Fin.eq_one_of_ne_zero (e i) h
    simp [h']

/-- The contraction of `Δ[n]` onto its last vertex fixes that vertex. -/
@[reassoc]
lemma lift_const_last_contractionLast_h {Z : SSet.{w}} (n : ℕ) (f : Z ⟶ Δ[1]) :
    lift (SSet.const (obj₀Equiv.symm (Fin.last n))) f ≫ (contractionLast n).h =
      SSet.const (obj₀Equiv.symm (Fin.last n)) := by
  ext ⟨⟨m⟩⟩ z i
  -- Evaluate the pairing, keeping the contraction behind its component API.
  refine congrArg Fin.val ((contractionLast_h_app_apply
    ((SSet.const (obj₀Equiv.symm (Fin.last n)) : Z ⟶ Δ[n]).app _ z) (f.app _ z) i).trans ?_)
  have hc : (SSet.const (obj₀Equiv.symm (Fin.last n)) : Z ⟶ Δ[n]).app _ z i = Fin.last n :=
    const_app_apply _ z i
  simp only [hc, ite_self]
  exact hc.symm

end SSet.stdSimplex
