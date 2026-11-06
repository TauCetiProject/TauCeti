/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom
import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits

/-!
# Morphism spaces of simplicial sets

For vertices `x` and `y` of a simplicial set `X`, the morphism space `Hom_X(x, y)` is the fibre
product `{x} ×_{Fun({0}, X)} Fun(Δ[1], X) ×_{Fun({1}, X)} {y}`, that is, the fibre over `(x, y)`
of the evaluation of `Fun(Δ[1], X)` at the two endpoints of `Δ[1]`. Its `n`-simplices are the maps
`Δ[1] ⊗ Δ[n] ⟶ X` which are constant at `x` on `{0} ⊗ Δ[n]` and constant at `y` on
`{1} ⊗ Δ[n]`, and its vertices are the edges from `x` to `y`. When `X` is a quasicategory, this is
the space of morphisms from `x` to `y`, the mapping space of the higher category `X`. The right
mapping space `Hom^R_X(x, y)` of `TauCeti/AlgebraicTopology/Quasicategory/RightMappingSpace.lean`
is another model of it, which maps to `Hom_X(x, y)` by the right-pinch inclusion below.

We realise `Hom_X(x, y)` as a subcomplex of the internal hom `Δ[1] ⟶[SSet] X`, as the intersection
of the fibres of the restrictions to `{0}` and `{1}`. It is also the fibre of the restriction
`Fun(Δ[1], X) ⟶ Fun(∂Δ[1], X)` along the boundary inclusion over the map `∂Δ[1] ⟶ X` with values
`x` and `y`. That restriction is an inner fibration when `X` is a quasicategory and a Kan fibration
when `X` is a Kan complex, so `Hom_X(x, y)` is then a quasicategory, respectively a Kan complex.
(That it is a Kan complex as soon as `X` is a quasicategory needs the pointwise criterion for
natural isomorphisms and Joyal's theorem on special outer horns, and is not proved here.)

A map of simplicial sets `f : X ⟶ Y` induces maps `Hom_X(x, y) ⟶ Hom_Y(f x, f y)` by
postcomposition, which on vertices are the maps of edges induced by `f`.

The right mapping space `Hom^R_X(x, y)` maps to `Hom_X(x, y)` by the right-pinch inclusion: an
`n`-simplex of `Hom^R_X(x, y)` is an `(n + 1)`-simplex `s` of `X`, and it goes to the restriction
of `s` along the map `Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` which is the identity of `Δ[n]` on `{0} ⊗ Δ[n]` and
collapses `{1} ⊗ Δ[n]` to the final vertex. On vertices it is the identity of the edges from `x`
to `y`. (That it is a homotopy equivalence when `X` is a quasicategory is not proved here.)

## Main definitions

* `SSet.morphismSpace X x y`: the morphism space `Hom_X(x, y)`.
* `SSet.morphismSpace.homEquiv`: maps `Z ⟶ Hom_X(x, y)` are the maps `Δ[1] ⊗ Z ⟶ X` which are
  constant at `x` on `{0} ⊗ Z` and at `y` on `{1} ⊗ Z`.
* `SSet.morphismSpace.objEquiv`: the corresponding description of the `n`-simplices.
* `SSet.morphismSpace.obj₀Equiv`: the vertices of `Hom_X(x, y)` are the edges from `x` to `y`.
* `SSet.morphismSpace.map x y f`: the map `Hom_X(x, y) ⟶ Hom_Y(f x, f y)` induced by
  `f : X ⟶ Y`.
* `SSet.rightMappingSpace.toMorphismSpace x y`: the right-pinch inclusion
  `Hom^R_X(x, y) ⟶ Hom_X(x, y)`.

## Main results

* `SSet.mem_morphismSpace_iff`: the description of the simplices of `Hom_X(x, y)`.
* `SSet.morphismSpace_eq_fiber`: `Hom_X(x, y)` is the fibre of the restriction along
  `∂Δ[1] ⟶ Δ[1]`.
* `SSet.morphismSpace.quasicategory`, `SSet.morphismSpace.kanComplex`: the morphism spaces of a
  quasicategory are quasicategories, and those of a Kan complex are Kan complexes.
* `SSet.morphismSpace.obj₀Equiv_map_app`: on vertices, `morphismSpace.map x y f` is the map of
  edges induced by `f`.
* `SSet.rightMappingSpace.obj₀Equiv_toMorphismSpace_app`: the right-pinch inclusion is the
  identity on vertices.
* `SSet.rightMappingSpace.objEquiv_toMorphismSpace_app_coe_app`: the right-pinch inclusion on
  simplices, as the restriction along `Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]`.

## References

* J. Lurie, *Kerodon*, Construction 4.6.1.1 (tag 01J5), Remark 4.6.1.2 (tag 01J6), Construction
  4.6.5.7 (tag 01L2) and Remark 4.6.5.9 (tag 01L4).
-/

public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite Simplicial

namespace SSet

variable (X : SSet.{u}) {Y Z : SSet.{u}}

/-- The morphism space `Hom_X(x, y)` between vertices `x` and `y` of a simplicial set `X`: the
fibre product `{x} ×_{Fun({0}, X)} Fun(Δ[1], X) ×_{Fun({1}, X)} {y}`, as the subcomplex of
`Δ[1] ⟶[SSet] X` whose `n`-simplices are the maps `Δ[1] ⊗ Δ[n] ⟶ X` which are constant at `x`
on `{0} ⊗ Δ[n]` and constant at `y` on `{1} ⊗ Δ[n]` (`SSet.mem_morphismSpace_iff`). Here `{0}`
and `{1}` are the faces `stdSimplex.δ 1` and `stdSimplex.δ 0` of `Δ[1]`. -/
def morphismSpace (x y : X _⦋0⦌) : ((ihom Δ[1]).obj X).Subcomplex :=
  fiber ((pre (stdSimplex.δ 1)).app X) ((ihomObj₀Equiv Δ[0] X).symm (yonedaEquiv.symm x)) ⊓
    fiber ((pre (stdSimplex.δ 0)).app X) ((ihomObj₀Equiv Δ[0] X).symm (yonedaEquiv.symm y))

variable {X} {x y : X _⦋0⦌}

/-- A map lands in the fibre of the restriction to a vertex `stdSimplex.δ i` of `Δ[1]` over a
vertex `v` of `X` exactly when its uncurried form is constant at `v` on that vertex. -/
private lemma range_le_fiber_pre_iff (g : Z ⟶ (ihom Δ[1]).obj X) (i : Fin 2) (v : X _⦋0⦌) :
    Subcomplex.range g ≤
        fiber ((pre (stdSimplex.δ i)).app X) ((ihomObj₀Equiv Δ[0] X).symm (yonedaEquiv.symm v)) ↔
      stdSimplex.δ i ▷ Z ≫ uncurry g = fst Δ[0] Z ≫ yonedaEquiv.symm v := by
  rw [range_le_fiber_iff, const_ihomObj₀Equiv_symm, eq_curry_iff, uncurry_pre_app]

/-- A map `g : Z ⟶ (Δ[1] ⟶[SSet] X)` lands in `Hom_X(x, y)` exactly when its uncurried form
`Δ[1] ⊗ Z ⟶ X` is constant at `x` on `{0} ⊗ Z` and constant at `y` on `{1} ⊗ Z`. -/
lemma range_le_morphismSpace_iff (g : Z ⟶ (ihom Δ[1]).obj X) :
    Subcomplex.range g ≤ X.morphismSpace x y ↔
      stdSimplex.δ 1 ▷ Z ≫ uncurry g = fst Δ[0] Z ≫ yonedaEquiv.symm x ∧
        stdSimplex.δ 0 ▷ Z ≫ uncurry g = fst Δ[0] Z ≫ yonedaEquiv.symm y := by
  rw [morphismSpace, le_inf_iff, range_le_fiber_pre_iff, range_le_fiber_pre_iff]

/-- An `n`-simplex of `Δ[1] ⟶[SSet] X` lies in `Hom_X(x, y)` exactly when the corresponding map
`Δ[1] ⊗ Δ[n] ⟶ X` is constant at `x` on `{0} ⊗ Δ[n]` and constant at `y` on `{1} ⊗ Δ[n]`. -/
@[simp]
lemma mem_morphismSpace_iff {n : ℕ} (σ : ((ihom Δ[1]).obj X) _⦋n⦌) :
    σ ∈ (X.morphismSpace x y).obj _ ↔
      stdSimplex.δ 1 ▷ Δ[n] ≫ ihomObjEquiv Δ[1] X σ = fst Δ[0] Δ[n] ≫ yonedaEquiv.symm x ∧
        stdSimplex.δ 0 ▷ Δ[n] ≫ ihomObjEquiv Δ[1] X σ = fst Δ[0] Δ[n] ≫ yonedaEquiv.symm y := by
  have := range_le_morphismSpace_iff (x := x) (y := y) (yonedaEquiv.symm σ)
  rwa [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply, Subcomplex.ofSimplex_le_iff,
    ← ihomObjEquiv_apply] at this

/-- A vertex of `Δ[1] ⟶[SSet] X` lies in `Hom_X(x, y)` exactly when the corresponding edge of `X`
goes from `x` to `y`. -/
lemma mem_morphismSpace_obj₀_iff (σ : ((ihom Δ[1]).obj X) _⦋0⦌) :
    σ ∈ (X.morphismSpace x y).obj _ ↔
      X.δ 1 (yonedaEquiv (ihomObj₀Equiv Δ[1] X σ)) = x ∧
        X.δ 0 (yonedaEquiv (ihomObj₀Equiv Δ[1] X σ)) = y := by
  simp only [mem_morphismSpace_iff, ← fst_comp_ihomObj₀Equiv, whiskerRight_fst_assoc,
    cancel_epi, ← stdSimplex.yonedaEquiv_δ_comp, Equiv.eq_symm_apply]

/-- **`Hom_X(x, y)` is a fibre of the restriction along the boundary inclusion**: it is the fibre
of `Fun(Δ[1], X) ⟶ Fun(∂Δ[1], X)` over any vertex `v`, a map `∂Δ[1] ⟶ X`, with values `x` at `0`
and `y` at `1`. -/
lemma morphismSpace_eq_fiber (v : ((ihom (∂Δ[1] : SSet.{u})).obj X) _⦋0⦌)
    (hx : boundary.ι 1 ≫ ihomObj₀Equiv _ X v = yonedaEquiv.symm x)
    (hy : boundary.ι 0 ≫ ihomObj₀Equiv _ X v = yonedaEquiv.symm y) :
    X.morphismSpace x y = fiber ((pre ∂Δ[1].ι).app X) v := by
  -- Both subcomplexes are characterised by the maps landing in them.
  suffices h : ∀ {Z : SSet.{u}} (g : Z ⟶ (ihom Δ[1]).obj X),
      Subcomplex.range g ≤ X.morphismSpace x y ↔
        Subcomplex.range g ≤ fiber ((pre ∂Δ[1].ι).app X) v by
    apply le_antisymm
    · simpa using (h (X.morphismSpace x y).ι).1
    · simpa using (h (fiber ((pre ∂Δ[1].ι).app X) v).ι).2
  intro Z g
  rw [range_le_morphismSpace_iff, range_le_fiber_iff, ← (ihomObj₀Equiv _ X).symm_apply_apply v,
    const_ihomObj₀Equiv_symm, eq_curry_iff, uncurry_pre_app]
  constructor
  · rintro ⟨h₁, h₀⟩
    refine boundary.tensor_hom_ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
      rw [← comp_whiskerRight_assoc, boundary.ι_ι, whiskerRight_fst_assoc]
    exacts [h₀.trans (congrArg (fst Δ[0] Z ≫ ·) hy.symm),
      h₁.trans (congrArg (fst Δ[0] Z ≫ ·) hx.symm)]
  · intro h
    have h' (j : Fin 2) := boundary.ι j ▷ Z ≫= h
    simp only [← comp_whiskerRight_assoc, boundary.ι_ι, whiskerRight_fst_assoc] at h'
    exact ⟨(h' 1).trans (congrArg (fst Δ[0] Z ≫ ·) hx),
      (h' 0).trans (congrArg (fst Δ[0] Z ≫ ·) hy)⟩

/-- There is a vertex of `Fun(∂Δ[1], X)` with values `x` at `0` and `y` at `1`, so that
`SSet.morphismSpace_eq_fiber` applies. -/
private lemma exists_morphismSpace_eq_fiber :
    ∃ v, X.morphismSpace x y = fiber ((pre ∂Δ[1].ι).app X) v := by
  have hf := (boundary.isCompatible_zero_iff_true ![yonedaEquiv.symm y, yonedaEquiv.symm x]).2
    trivial
  exact ⟨_, morphismSpace_eq_fiber ((ihomObj₀Equiv _ X).symm hf.desc)
    (by simp) (by simp)⟩

namespace morphismSpace

/-- The morphism spaces of a quasicategory are quasicategories. -/
instance quasicategory [X.Quasicategory] : Quasicategory (X.morphismSpace x y) := by
  obtain ⟨v, hv⟩ := exists_morphismSpace_eq_fiber (x := x) (y := y)
  rw [hv]
  infer_instance

/-- The morphism spaces of a Kan complex are Kan complexes. -/
instance kanComplex [KanComplex X] : KanComplex (X.morphismSpace x y) := by
  obtain ⟨v, hv⟩ := exists_morphismSpace_eq_fiber (x := x) (y := y)
  rw [hv]
  infer_instance

/-- **The universal property of `Hom_X(x, y)`**: maps `Z ⟶ Hom_X(x, y)` are the maps
`Δ[1] ⊗ Z ⟶ X` which are constant at `x` on `{0} ⊗ Z` and constant at `y` on `{1} ⊗ Z`, through
uncurrying. -/
def homEquiv :
    (Z ⟶ X.morphismSpace x y) ≃ {g : Δ[1] ⊗ Z ⟶ X //
      stdSimplex.δ 1 ▷ Z ≫ g = fst Δ[0] Z ≫ yonedaEquiv.symm x ∧
        stdSimplex.δ 0 ▷ Z ≫ g = fst Δ[0] Z ≫ yonedaEquiv.symm y} where
  toFun φ := ⟨uncurry (φ ≫ (X.morphismSpace x y).ι), (range_le_morphismSpace_iff _).1
    (by rintro _ _ ⟨z, rfl⟩; exact (φ.app _ z).2)⟩
  invFun g := Subcomplex.lift (curry g.1)
    ((range_le_morphismSpace_iff _).2 (by rw [uncurry_curry]; exact g.2))
  left_inv φ := (cancel_mono (X.morphismSpace x y).ι).1 (by simp)
  right_inv g := Subtype.ext (by simp)

/-- The map `Δ[1] ⊗ Z ⟶ X` attached to `φ : Z ⟶ Hom_X(x, y)` is the uncurried form of `φ`. -/
lemma homEquiv_apply_coe (φ : Z ⟶ X.morphismSpace x y) :
    (homEquiv φ).1 = uncurry (φ ≫ (X.morphismSpace x y).ι) :=
  (rfl)

/-- The map `Z ⟶ Hom_X(x, y)` attached to `g : Δ[1] ⊗ Z ⟶ X` is the curried form of `g`. -/
@[reassoc (attr := simp)]
lemma homEquiv_symm_apply_ι (g : {g : Δ[1] ⊗ Z ⟶ X //
      stdSimplex.δ 1 ▷ Z ≫ g = fst Δ[0] Z ≫ yonedaEquiv.symm x ∧
        stdSimplex.δ 0 ▷ Z ≫ g = fst Δ[0] Z ≫ yonedaEquiv.symm y}) :
    homEquiv.symm g ≫ (X.morphismSpace x y).ι = curry g.1 :=
  (rfl)

/-- The universal property is natural in the source. -/
@[simp]
lemma homEquiv_comp_coe {Z' : SSet.{u}} (h : Z' ⟶ Z) (φ : Z ⟶ X.morphismSpace x y) :
    (homEquiv (h ≫ φ)).1 = Δ[1] ◁ h ≫ (homEquiv φ).1 := by
  rw [homEquiv_apply_coe, homEquiv_apply_coe, Category.assoc, uncurry_natural_left]

/-- The `n`-simplices of `Hom_X(x, y)` are the maps `Δ[1] ⊗ Δ[n] ⟶ X` which are constant at `x`
on `{0} ⊗ Δ[n]` and constant at `y` on `{1} ⊗ Δ[n]`. -/
def objEquiv {n : ℕ} :
    (X.morphismSpace x y : SSet) _⦋n⦌ ≃ {g : Δ[1] ⊗ Δ[n] ⟶ X //
      stdSimplex.δ 1 ▷ Δ[n] ≫ g = fst Δ[0] Δ[n] ≫ yonedaEquiv.symm x ∧
        stdSimplex.δ 0 ▷ Δ[n] ≫ g = fst Δ[0] Δ[n] ≫ yonedaEquiv.symm y} :=
  (ihomObjEquiv Δ[1] X).subtypeEquiv mem_morphismSpace_iff

/-- The map `Δ[1] ⊗ Δ[n] ⟶ X` attached to an `n`-simplex of `Hom_X(x, y)` is the one attached to
it as a simplex of `Δ[1] ⟶[SSet] X`. -/
@[simp]
lemma objEquiv_apply_coe {n : ℕ} (σ : (X.morphismSpace x y : SSet) _⦋n⦌) :
    dsimp% (objEquiv σ).1 = ihomObjEquiv Δ[1] X σ.1 :=
  (rfl)

/-- **The vertices of `Hom_X(x, y)` are the edges from `x` to `y`**: a vertex is a map
`Δ[1] ⟶ X`, that is, a `1`-simplex of `X`, with source `x` and target `y`. -/
def obj₀Equiv : (X.morphismSpace x y : SSet) _⦋0⦌ ≃ Edge x y where
  toFun σ := Edge.mk (yonedaEquiv (ihomObj₀Equiv Δ[1] X σ.1))
    ((mem_morphismSpace_obj₀_iff _).1 σ.2).1 ((mem_morphismSpace_obj₀_iff _).1 σ.2).2
  invFun e := ⟨(ihomObj₀Equiv Δ[1] X).symm (yonedaEquiv.symm e.edge),
    (mem_morphismSpace_obj₀_iff _).2 (by simp)⟩
  left_inv σ := Subtype.ext (by simp)
  right_inv e := Edge.ext (by simp)

/-- The edge attached to a vertex of `Hom_X(x, y)` is the corresponding map `Δ[1] ⟶ X`, as a
`1`-simplex of `X`. -/
@[simp]
lemma obj₀Equiv_apply_edge (σ : (X.morphismSpace x y : SSet) _⦋0⦌) :
    dsimp% (obj₀Equiv σ).edge = yonedaEquiv (ihomObj₀Equiv Δ[1] X σ.1) :=
  (rfl)

/-- The vertex of `Hom_X(x, y)` attached to an edge is the vertex of `Δ[1] ⟶[SSet] X` given by
the edge as a map `Δ[1] ⟶ X`. -/
@[simp]
lemma obj₀Equiv_symm_apply_coe (e : Edge x y) :
    dsimp% (obj₀Equiv.symm e).1 = (ihomObj₀Equiv Δ[1] X).symm (yonedaEquiv.symm e.edge) :=
  (rfl)

/-! ### Functoriality -/

section map

variable (f : X ⟶ Y)

/-- Postcomposition with `f : X ⟶ Y` sends `Hom_X(x, y)` into `Hom_Y(f x, f y)`. -/
lemma range_le_morphismSpace :
    Subcomplex.range ((X.morphismSpace x y).ι ≫ (ihom Δ[1]).map f) ≤
      Y.morphismSpace (f.app _ x) (f.app _ y) := by
  obtain ⟨h₁, h₀⟩ := (range_le_morphismSpace_iff (X.morphismSpace x y).ι).1
    (Subfunctor.range_ι _).le
  rw [range_le_morphismSpace_iff, uncurry_natural_right, reassoc_of% h₁, reassoc_of% h₀]
  simp

variable (x y) in
/-- The map `Hom_X(x, y) ⟶ Hom_Y(f x, f y)` induced by a map of simplicial sets `f : X ⟶ Y`,
by postcomposition with `f`. -/
def map : (X.morphismSpace x y : SSet.{u}) ⟶
    (Y.morphismSpace (f.app _ x) (f.app _ y) : SSet.{u}) :=
  Subcomplex.lift _ (range_le_morphismSpace f)

variable (x y) in
/-- The map induced on morphism spaces is the restriction of postcomposition with `f`. -/
@[reassoc (attr := simp)]
lemma map_ι :
    map x y f ≫ (Y.morphismSpace (f.app _ x) (f.app _ y)).ι =
      (X.morphismSpace x y).ι ≫ (ihom Δ[1]).map f :=
  (rfl)

/-- The map induced on morphism spaces sends a simplex to its image under postcomposition with
`f`. -/
@[simp]
lemma map_app_coe {n : SimplexCategoryᵒᵖ} (σ : (X.morphismSpace x y : SSet).obj n) :
    dsimp% ((map x y f).app _ σ).1 = ((ihom Δ[1]).map f).app _ σ.1 :=
  (rfl)

/-- The map induced on morphism spaces postcomposes a map `Δ[1] ⊗ Δ[n] ⟶ X` with `f`. -/
lemma objEquiv_map_app_coe {n : ℕ} (σ : (X.morphismSpace x y : SSet) _⦋n⦌) :
    dsimp% (objEquiv ((map x y f).app _ σ)).1 = (objEquiv σ).1 ≫ f :=
  ihomObjEquiv_ihom_map_app _ f σ.1

/-- On vertices, the map induced on morphism spaces is the map of edges induced by `f`. -/
@[simp]
lemma obj₀Equiv_map_app (σ : (X.morphismSpace x y : SSet) _⦋0⦌) :
    dsimp% obj₀Equiv ((map x y f).app _ σ) = (obj₀Equiv σ).map f := by
  ext
  rw [Edge.map_edge, obj₀Equiv_apply_edge, obj₀Equiv_apply_edge]
  simp only [map_app_coe, ihomObj₀Equiv_ihom_map_app, yonedaEquiv_comp]

variable (x y) in
/-- The identity induces the identity of morphism spaces. -/
@[simp]
lemma map_id : map x y (𝟙 X) = 𝟙 _ :=
  (cancel_mono (Subcomplex.ι _)).1 (by rw [map, Subcomplex.lift_ι]; simp)

variable (x y) in
/-- The maps induced on morphism spaces are compatible with composition. -/
@[simp]
lemma map_comp {W : SSet.{u}} (g : Y ⟶ W) :
    map x y (f ≫ g) = map x y f ≫ map (f.app _ x) (f.app _ y) g := by
  ext n σ
  exact Subtype.ext (by simp)

end map

/-- The vertex of `Hom_X(x, y)` given by a map `g : Δ[1] ⊗ Z ⟶ X` at a vertex `z` of `Z` is the
edge obtained by restricting `g` to `Δ[1] ⊗ {z}`. -/
lemma obj₀Equiv_homEquiv_symm_app_edge (g : {g : Δ[1] ⊗ Z ⟶ X //
      stdSimplex.δ 1 ▷ Z ≫ g = fst Δ[0] Z ≫ yonedaEquiv.symm x ∧
        stdSimplex.δ 0 ▷ Z ≫ g = fst Δ[0] Z ≫ yonedaEquiv.symm y}) (z : Z _⦋0⦌) :
    (obj₀Equiv ((homEquiv.symm g).app _ z)).edge =
      yonedaEquiv (lift (𝟙 Δ[1]) (const z) ≫ g.1) := by
  rw [obj₀Equiv_apply_edge]
  exact congrArg yonedaEquiv (ihomObj₀Equiv_curry_app Δ[1] g.1 z)

end morphismSpace

/-! ### The right-pinch inclusion -/

namespace rightMappingSpace

open SimplexCategory

/-- For `a : m ⟶ ⦋1⦌`, the map `m ⟶ m ⋆ ⦋0⦌` which is the inclusion on the vertices sent to `0`
and sends the vertices sent to `1` to the final vertex. -/
private def pinch {m : SimplexCategory} (a : m ⟶ ⦋1⦌) : m ⟶ joinVertex.obj m :=
  Hom.mk ⟨fun k ↦ if a.toOrderHom k = 0 then k.castSucc else Fin.last _, fun k l hkl ↦ by
    by_cases hk : a.toOrderHom k = 0
    · by_cases hl : a.toOrderHom l = 0
      · simp only [hk, hl, ↓reduceIte]
        exact Fin.castSucc_le_castSucc_iff.2 hkl
      · simp only [hk, hl, ↓reduceIte]
        exact Fin.le_last _
    · have hl : a.toOrderHom l ≠ 0 := fun hl ↦
        hk (Fin.le_zero_iff.1 (hl ▸ a.toOrderHom.monotone hkl))
      simp only [hk, hl, ↓reduceIte]
      exact le_rfl⟩

private lemma pinch_toOrderHom_apply {m : SimplexCategory} (a : m ⟶ ⦋1⦌) (k : Fin (m.len + 1)) :
    (pinch a).toOrderHom k = if a.toOrderHom k = 0 then k.castSucc else Fin.last _ :=
  (rfl)

private lemma pinch_comp {m m' : SimplexCategory} (θ : m' ⟶ m) (a : m ⟶ ⦋1⦌) :
    pinch (θ ≫ a) ≫ joinVertex.map θ = θ ≫ pinch a := by
  ext k : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, pinch_toOrderHom_apply]
  split_ifs
  exacts [joinVertex_map_castSucc θ _, joinVertex_map_last θ]

private lemma pinch_eq_joinVertexInl {m : SimplexCategory} (a : m ⟶ ⦋1⦌)
    (h : ∀ k, a.toOrderHom k = 0) : pinch a = joinVertexInl m := by
  obtain ⟨m⟩ := m
  ext k : 3
  rw [joinVertexInl_mk, pinch_toOrderHom_apply]
  simp only [h k, ↓reduceIte]
  exact (Fin.succAbove_last_apply k).symm

private lemma pinch_eq_joinVertexInr {m : SimplexCategory} (a : m ⟶ ⦋1⦌)
    (h : ∀ k, a.toOrderHom k = 1) : pinch a = m.const ⦋0⦌ 0 ≫ joinVertexInr m := by
  obtain ⟨m⟩ := m
  ext k : 3
  have hr : (joinVertexInr ⦋m⦌).toOrderHom 0 = Fin.last (m + 1) := by
    rw [joinVertexInr_mk]
    exact const_apply _ _ _ _
  rw [pinch_toOrderHom_apply, comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, const_apply,
    hr]
  have hk : a.toOrderHom k ≠ 0 := by simp [h k]
  simp only [hk, ↓reduceIte]
  rfl

private lemma pinch_id_comp :
    pinch (𝟙 ⦋1⦌) ≫ joinVertex.map (⦋1⦌.const ⦋0⦌ 0) = 𝟙 (joinVertex.obj ⦋0⦌) := by
  ext k : 3
  fin_cases k
  · exact joinVertex_map_castSucc (⦋1⦌.const ⦋0⦌ 0) 0
  · exact joinVertex_map_last (⦋1⦌.const ⦋0⦌ 0)

variable (x y) in
/-- The map `Δ[1] ⊗ Hom^R_X(x, y) ⟶ X` sending a pair of a simplex `a` of `Δ[1]` and an
`n`-simplex `s` of `Hom^R_X(x, y)`, an `(n + 1)`-simplex of `X`, to the face of `s` which is the
inclusion on the vertices `a` sends to `0` and the final vertex on those it sends to `1`. -/
private def pinchMap : Δ[1] ⊗ (X.rightMappingSpace x y : SSet.{u}) ⟶ X where
  app n := ↾fun p ↦ X.map (pinch (stdSimplex.objEquiv p.1)).op
    (p.2.1 : X.obj (op (joinVertex.obj n.unop)))
  naturality n n' f := by
    ext ⟨a, s⟩
    -- `change` unfolds the action of `f` on `Δ[1] ⊗ Hom^R_X(x, y)` and the components of
    -- `pinchMap`.
    change X.map (pinch (f.unop ≫ stdSimplex.objEquiv a)).op
        (X.map (joinVertex.map f.unop).op s.1) =
      X.map f (X.map (pinch (stdSimplex.objEquiv a)).op s.1)
    rw [← Functor.map_comp_apply, ← op_comp, pinch_comp, op_comp, Functor.map_comp_apply,
      Quiver.Hom.op_unop]

/-- On `{0} ⊗ Hom^R_X(x, y)`, `pinchMap` is constant at `x`. -/
private lemma pinchMap_δ_one :
    stdSimplex.δ 1 ▷ _ ≫ pinchMap x y = fst Δ[0] _ ≫ yonedaEquiv.symm x := by
  ext ⟨⟨n⟩⟩ ⟨b, s⟩
  -- `change` unfolds the components of `pinchMap` and of the action of `stdSimplex.δ 1`.
  change X.map (pinch (stdSimplex.objEquiv b ≫ SimplexCategory.δ 1)).op s.1 =
    X.map (stdSimplex.objEquiv b).op x
  rw [pinch_eq_joinVertexInl _ fun k ↦ ?_, joinVertexInl_mk,
    Subsingleton.elim (stdSimplex.objEquiv b) (⦋n⦌.const ⦋0⦌ 0)]
  · exact ((mem_rightMappingSpace_iff _).1 s.2).1
  · rw [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      Fin.fin_one_eq_zero ((stdSimplex.objEquiv b).toOrderHom k)]
    rfl

/-- On `{1} ⊗ Hom^R_X(x, y)`, `pinchMap` is constant at `y`. -/
private lemma pinchMap_δ_zero :
    stdSimplex.δ 0 ▷ _ ≫ pinchMap x y = fst Δ[0] _ ≫ yonedaEquiv.symm y := by
  ext ⟨⟨n⟩⟩ ⟨b, s⟩
  -- `change` unfolds the components of `pinchMap` and of the action of `stdSimplex.δ 0`.
  change X.map (pinch (stdSimplex.objEquiv b ≫ SimplexCategory.δ 0)).op s.1 =
    X.map (stdSimplex.objEquiv b).op y
  rw [pinch_eq_joinVertexInr _ fun k ↦ ?_, op_comp, Functor.map_comp_apply, joinVertexInr_mk,
    Subsingleton.elim (stdSimplex.objEquiv b) (⦋n⦌.const ⦋0⦌ 0)]
  · exact congrArg _ ((mem_rightMappingSpace_iff _).1 s.2).2
  · rw [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      Fin.fin_one_eq_zero ((stdSimplex.objEquiv b).toOrderHom k)]
    rfl

variable (x y) in
/-- The *right-pinch inclusion* `Hom^R_X(x, y) ⟶ Hom_X(x, y)`. An `n`-simplex of `Hom^R_X(x, y)`,
an `(n + 1)`-simplex `s` of `X`, goes to the map `Δ[1] ⊗ Δ[n] ⟶ X` restricting `s` along the map
`Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` which is the identity of `Δ[n]` on `{0} ⊗ Δ[n]` and collapses
`{1} ⊗ Δ[n]` to the final vertex. -/
noncomputable def toMorphismSpace :
    (X.rightMappingSpace x y : SSet.{u}) ⟶ (X.morphismSpace x y : SSet.{u}) :=
  morphismSpace.homEquiv.symm ⟨pinchMap x y, pinchMap_δ_one, pinchMap_δ_zero⟩

/-- **The right-pinch inclusion is the identity on vertices**: it sends an edge from `x` to `y`,
viewed as a vertex of `Hom^R_X(x, y)`, to the same edge, viewed as a vertex of `Hom_X(x, y)`. -/
@[simp]
lemma obj₀Equiv_toMorphismSpace_app (σ : (X.rightMappingSpace x y : SSet) _⦋0⦌) :
    dsimp% morphismSpace.obj₀Equiv ((toMorphismSpace x y).app _ σ) = obj₀Equiv σ := by
  ext
  rw [toMorphismSpace, morphismSpace.obj₀Equiv_homEquiv_symm_app_edge, obj₀Equiv_apply_edge,
    yonedaEquiv_comp]
  -- `change` unfolds the component of `pinchMap` at the pair of the nondegenerate edge of `Δ[1]`
  -- and the degenerate edge of `Hom^R_X(x, y)` at `σ`.
  change X.map (pinch (𝟙 ⦋1⦌)).op (X.map (joinVertex.map (⦋1⦌.const ⦋0⦌ 0)).op σ.1) = σ.1
  rw [← Functor.map_comp_apply, ← op_comp, pinch_id_comp]
  exact ConcreteCategory.congr_hom (X.map_id (op (joinVertex.obj ⦋0⦌))) σ.1

/-- **The right-pinch inclusion on simplices**: the map `Δ[1] ⊗ Δ[n] ⟶ X` attached to the image
of an `n`-simplex `s` of `Hom^R_X(x, y)`, an `(n + 1)`-simplex of `X`, sends a pair of
`m`-simplices `a` of `Δ[1]` and `b` of `Δ[n]` to the face of `s` along the map
`g : ⦋m⦌ ⟶ ⦋n + 1⦌` which is `b` on the vertices `a` sends to `0` and the final vertex on those
it sends to `1`. -/
lemma objEquiv_toMorphismSpace_app_coe_app {n m : ℕ} (s : (X.rightMappingSpace x y : SSet) _⦋n⦌)
    (a : Δ[1] _⦋m⦌) (b : Δ[n] _⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (hg : ∀ k, g.toOrderHom k = if (stdSimplex.objEquiv a).toOrderHom k = 0 then
      ((stdSimplex.objEquiv b).toOrderHom k).castSucc else Fin.last _) :
    (morphismSpace.objEquiv ((toMorphismSpace x y).app _ s)).1.app _ (a, b) =
      X.map g.op (s.1 : X _⦋n + 1⦌) := by
  have h : (morphismSpace.objEquiv ((toMorphismSpace x y).app _ s)).1 =
      Δ[1] ◁ yonedaEquiv.symm s ≫ pinchMap x y := by
    -- `toMorphismSpace` is by definition the curried form of `pinchMap`.
    have h' : ((toMorphismSpace x y).app _ s).1 = (curry (pinchMap x y)).app _ s := (rfl)
    rw [morphismSpace.objEquiv_apply_coe, h', ihomObjEquiv_apply, ← yonedaEquiv_symm_comp,
      uncurry_natural_left, uncurry_curry]
  have hg' : pinch (stdSimplex.objEquiv a) ≫ joinVertex.map (stdSimplex.objEquiv b) = g := by
    ext k : 3
    refine Eq.trans ?_ (hg k).symm
    rw [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, pinch_toOrderHom_apply]
    split_ifs
    exacts [joinVertex_map_castSucc _ _, joinVertex_map_last _]
  rw [h]
  -- `change` unfolds the components of `pinchMap` and of the action of `b` on `Hom^R_X(x, y)`.
  change X.map (pinch (stdSimplex.objEquiv a)).op
      (X.map (joinVertex.map (stdSimplex.objEquiv b)).op s.1) = _
  rw [← Functor.map_comp_apply, ← op_comp]
  exact congrArg (fun f ↦ X.map (Quiver.Hom.op f) s.1) hg'

end rightMappingSpace

end SSet
