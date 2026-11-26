/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom
public import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplex.JoinVertex
import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits
import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplex.One
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
import TauCeti.AlgebraicTopology.SimplicialSet.Vertex

/-!
# Two-sided mapping spaces

For vertices `x` and `y` of a simplicial set `X`, the (two-sided) mapping space `Hom_X(x, y)` is
the fibre over `(x, y)` of the restriction map `Fun(Δ[1], X) ⟶ Fun(∂Δ[1], X)` to the two
endpoints: its `n`-simplices are the maps `Δ[1] ⊗ Δ[n] ⟶ X` which are constant at `x` on
`{0} × Δ[n]` and constant at `y` on `{1} × Δ[n]`, and its vertices are the edges from `x` to `y`.
When `X` is a quasicategory, the restriction map is an inner fibration, so `Hom_X(x, y)` is again a
quasicategory. Unlike the right mapping space `Hom^R_X(x, y)` of
`TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace`, its definition is symmetric in the two
endpoints and is functorial through the internal hom `Fun(Δ[1], X)`.

The two models are compared by a natural monomorphism `Hom^R_X(x, y) ⟶ Hom_X(x, y)`: an
`n`-simplex of `Hom^R_X(x, y)`, an `(n + 1)`-simplex of `X`, is precomposed with the collapse
`Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` of `{1} × Δ[n]` to the last vertex
(`SSet.prodStdSimplex.toJoinVertex`). It is the identity of the edges from `x` to `y` on vertices.
For a quasicategory it is moreover a bijection on connected components. An edge of `Hom_X(x, y)` is
a square `Δ[1] ⊗ Δ[1] ⟶ X` with degenerate vertical sides; its two `2`-simplices, together with the
coincidence of the left and right homotopy relations in a quasicategory, show that its endpoints are
joined in `Hom^R_X(x, y)`. That the comparison is a homotopy equivalence of Kan complexes
(HTT, §4.2.1) is not proved here.

## Main definitions

* `SSet.mappingSpace X x y`: the mapping space `Hom_X(x, y)`, a subcomplex of `Fun(Δ[1], X)`.
* `SSet.mappingSpace.objEquiv`, `SSet.mappingSpace.obj₀Equiv`: its `n`-simplices are the maps
  `Δ[1] ⊗ Δ[n] ⟶ X` with constant ends, and its vertices are the edges from `x` to `y`.
* `SSet.mappingSpace.map x y f`: the map `Hom_X(x, y) ⟶ Hom_Y(f x, f y)` induced by `f : X ⟶ Y`.
* `SSet.rightMappingSpace.toMappingSpace x y`: the comparison `Hom^R_X(x, y) ⟶ Hom_X(x, y)`.

## Main results

* `SSet.range_le_mappingSpace_iff`, `SSet.mem_mappingSpace_iff`: the universal property of
  `Hom_X(x, y)` and the description of its simplices.
* `SSet.mappingSpace.quasicategory`: the mapping spaces of a quasicategory are quasicategories.
* `SSet.rightMappingSpace.mono_toMappingSpace`,
  `SSet.rightMappingSpace.toMappingSpace_comp_map`: the comparison is a natural monomorphism.
* `SSet.rightMappingSpace.bijective_toMappingSpace_app_zero`: it is a bijection on vertices.
* `SSet.rightMappingSpace.bijective_mapπ₀_toMappingSpace`: for a quasicategory, it is a bijection
  on connected components.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 (the mapping spaces `Hom_S(x, y)` and `Hom^R_S(x, y)`)
  and §4.2.1 (their comparison).
* J. Lurie, *Kerodon*, Section 4.6 (morphism spaces of `∞`-categories).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite Simplicial

universe u

namespace SSet

variable (X : SSet.{u})

/-- The (two-sided) mapping space `Hom_X(x, y)` between vertices `x` and `y` of a simplicial set
`X`: the fibre over `(x, y)` of the restriction map `Fun(Δ[1], X) ⟶ Fun(∂Δ[1], X)` to the two
endpoints. Its `n`-simplices are the maps `Δ[1] ⊗ Δ[n] ⟶ X` which are constant at `x` on
`{0} × Δ[n]` and constant at `y` on `{1} × Δ[n]` (`SSet.mem_mappingSpace_iff`). -/
noncomputable def mappingSpace (x y : X _⦋0⦌) : ((ihom Δ[1]).obj X).Subcomplex :=
  fiber ((pre ∂Δ[1].ι).app X) ((ihomObj₀Equiv _ X).symm (boundary.descOne x y))

variable {X} {x y : X _⦋0⦌}

/-- **The universal property of `Hom_X(x, y)`**: a map `g : Z ⟶ Fun(Δ[1], X)` lands in
`Hom_X(x, y)` exactly when its uncurried form `Δ[1] ⊗ Z ⟶ X` is constant at `x` on `{0} × Z` and
constant at `y` on `{1} × Z`. -/
lemma range_le_mappingSpace_iff {Z : SSet.{u}} (g : Z ⟶ (ihom Δ[1]).obj X) :
    Subcomplex.range g ≤ X.mappingSpace x y ↔
      stdSimplex.δ 1 ▷ Z ≫ uncurry g = const x ∧ stdSimplex.δ 0 ▷ Z ≫ uncurry g = const y := by
  rw [mappingSpace, range_le_fiber_iff, const_ihomObj₀Equiv_symm, eq_curry_iff, uncurry_pre_app]
  -- Restricted to the face `ι i` of `∂Δ[1]`, the composite `fst ≫ boundary.descOne x y` is
  -- constant at the vertex `1 - i`.
  have key (i : Fin 2) :
      boundary.ι i ▷ Z ≫ ∂Δ[1].ι ▷ Z ≫ uncurry g = stdSimplex.δ i ▷ Z ≫ uncurry g := by
    rw [← comp_whiskerRight_assoc, boundary.ι_ι]
  have key' (i : Fin 2) : boundary.ι i ▷ Z ≫ fst _ Z ≫ boundary.descOne x y =
      ![const y, const x] i := by
    rw [whiskerRight_fst_assoc, boundary.ι_descOne]
    fin_cases i <;> exact comp_const _ _
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₀⟩ ↦ boundary.hom_ext_whiskerRight fun i ↦ ?_⟩
  · simpa [key, key'] using boundary.ι 1 ▷ Z ≫= h
  · simpa [key, key'] using boundary.ι 0 ▷ Z ≫= h
  · rw [key, key']
    fin_cases i
    · exact h₀
    · exact h₁

/-- An `n`-simplex of `Fun(Δ[1], X)` lies in `Hom_X(x, y)` exactly when the corresponding map
`Δ[1] ⊗ Δ[n] ⟶ X` is constant at `x` on `{0} × Δ[n]` and constant at `y` on `{1} × Δ[n]`. -/
lemma mem_mappingSpace_iff {n : ℕ} (σ : ((ihom Δ[1]).obj X) _⦋n⦌) :
    σ ∈ (X.mappingSpace x y).obj _ ↔
      stdSimplex.δ 1 ▷ Δ[n] ≫ ihomObjEquiv _ X σ = const x ∧
        stdSimplex.δ 0 ▷ Δ[n] ≫ ihomObjEquiv _ X σ = const y := by
  have := range_le_mappingSpace_iff (x := x) (y := y) (yonedaEquiv.symm σ)
  rwa [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply, Subcomplex.ofSimplex_le_iff,
    ← ihomObjEquiv_apply] at this

/-- A vertex of `Fun(Δ[1], X)` lies in `Hom_X(x, y)` exactly when the corresponding map
`Δ[1] ⟶ X` is an edge from `x` to `y`. -/
lemma mem_mappingSpace_obj₀_iff (σ : ((ihom Δ[1]).obj X) _⦋0⦌) :
    σ ∈ (X.mappingSpace x y).obj _ ↔
      stdSimplex.δ 1 ≫ ihomObj₀Equiv _ X σ = const x ∧
        stdSimplex.δ 0 ≫ ihomObj₀Equiv _ X σ = const y := by
  rw [mem_mappingSpace_iff, ← fst_comp_ihomObj₀Equiv, whiskerRight_fst_assoc,
    whiskerRight_fst_assoc, ← comp_const (fst Δ[0] Δ[0]) x, ← comp_const (fst Δ[0] Δ[0]) y,
    cancel_epi, cancel_epi]

namespace mappingSpace

variable (x y)

/-- The uncurried form `Δ[1] ⊗ Hom_X(x, y) ⟶ X` of the inclusion of `Hom_X(x, y)` is constant at
`x` on `{0} × Hom_X(x, y)`. -/
@[reassoc (attr := simp)]
lemma whiskerRight_δ_one_uncurry_ι :
    stdSimplex.δ 1 ▷ _ ≫ uncurry (X.mappingSpace x y).ι = const x :=
  ((range_le_mappingSpace_iff _).1 (Subfunctor.range_ι _).le).1

/-- The uncurried form `Δ[1] ⊗ Hom_X(x, y) ⟶ X` of the inclusion of `Hom_X(x, y)` is constant at
`y` on `{1} × Hom_X(x, y)`. -/
@[reassoc (attr := simp)]
lemma whiskerRight_δ_zero_uncurry_ι :
    stdSimplex.δ 0 ▷ _ ≫ uncurry (X.mappingSpace x y).ι = const y :=
  ((range_le_mappingSpace_iff _).1 (Subfunctor.range_ι _).le).2

/-- A family `g : Z ⟶ Hom_X(x, y)` of edges, uncurried to `Δ[1] ⊗ Z ⟶ X`, is constant at `x` on
`{0} × Z`. -/
@[reassoc (attr := simp)]
lemma whiskerRight_δ_one_uncurry_comp_ι {Z : SSet.{u}} (g : Z ⟶ (X.mappingSpace x y : SSet.{u})) :
    stdSimplex.δ 1 ▷ Z ≫ uncurry (g ≫ (X.mappingSpace x y).ι) = const x := by
  rw [uncurry_natural_left, ← whisker_exchange_assoc, whiskerRight_δ_one_uncurry_ι, comp_const]

/-- A family `g : Z ⟶ Hom_X(x, y)` of edges, uncurried to `Δ[1] ⊗ Z ⟶ X`, is constant at `y` on
`{1} × Z`. -/
@[reassoc (attr := simp)]
lemma whiskerRight_δ_zero_uncurry_comp_ι {Z : SSet.{u}} (g : Z ⟶ (X.mappingSpace x y : SSet.{u})) :
    stdSimplex.δ 0 ▷ Z ≫ uncurry (g ≫ (X.mappingSpace x y).ι) = const y := by
  rw [uncurry_natural_left, ← whisker_exchange_assoc, whiskerRight_δ_zero_uncurry_ι, comp_const]

/-- The mapping spaces of a quasicategory are quasicategories: `Hom_X(x, y)` is a fibre of the
restriction `Fun(Δ[1], X) ⟶ Fun(∂Δ[1], X)`, which is an inner fibration. -/
instance quasicategory [X.Quasicategory] : (X.mappingSpace x y : SSet.{u}).Quasicategory :=
  fiber.quasicategory _ _

variable {x y}

/-- **The simplex description of `Hom_X(x, y)`**: its `n`-simplices are the maps
`Δ[1] ⊗ Δ[n] ⟶ X` which are constant at `x` on `{0} × Δ[n]` and constant at `y` on
`{1} × Δ[n]`. -/
def objEquiv {n : ℕ} :
    (X.mappingSpace x y : SSet) _⦋n⦌ ≃ {g : Δ[1] ⊗ Δ[n] ⟶ X //
      stdSimplex.δ 1 ▷ Δ[n] ≫ g = const x ∧ stdSimplex.δ 0 ▷ Δ[n] ≫ g = const y} :=
  (ihomObjEquiv _ X).subtypeEquiv fun _ ↦ mem_mappingSpace_iff _

/-- The map `Δ[1] ⊗ Δ[n] ⟶ X` attached to an `n`-simplex of `Hom_X(x, y)` is the corresponding
map of `Fun(Δ[1], X)`. -/
@[simp]
lemma objEquiv_apply_coe {n : ℕ} (σ : (X.mappingSpace x y : SSet) _⦋n⦌) :
    dsimp% (objEquiv σ).val = ihomObjEquiv _ X σ.val :=
  (rfl)

/-- The vertices of `Hom_X(x, y)` are the edges from `x` to `y`. -/
noncomputable def obj₀Equiv : (X.mappingSpace x y : SSet.{u}) _⦋0⦌ ≃ Edge x y where
  toFun σ := Edge.mk (yonedaEquiv (ihomObj₀Equiv _ X σ.val))
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ((mem_mappingSpace_obj₀_iff _).1 σ.property).1,
        yonedaEquiv_const])
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ((mem_mappingSpace_obj₀_iff _).1 σ.property).2,
        yonedaEquiv_const])
  invFun e := ⟨(ihomObj₀Equiv _ X).symm (yonedaEquiv.symm e.edge),
    (mem_mappingSpace_obj₀_iff _).2 (by
      simp only [Equiv.apply_symm_apply, stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq, e.tgt_eq,
        yonedaEquiv_symm_zero, and_self])⟩
  left_inv σ := Subtype.ext (by simp)
  right_inv e := Edge.ext (by simp)

/-- The edge attached to a vertex of `Hom_X(x, y)` is that vertex, as a map `Δ[1] ⟶ X`. -/
lemma obj₀Equiv_apply_edge (σ : (X.mappingSpace x y : SSet.{u}) _⦋0⦌) :
    (obj₀Equiv σ).edge = yonedaEquiv (ihomObj₀Equiv _ X σ.val) :=
  (rfl)

/-- The vertex of `Hom_X(x, y)` attached to an edge is that edge, as a vertex of
`Fun(Δ[1], X)`. -/
lemma obj₀Equiv_symm_apply_coe (e : Edge x y) :
    (obj₀Equiv.symm e).val = (ihomObj₀Equiv _ X).symm (yonedaEquiv.symm e.edge) :=
  (rfl)

/-- The family of identity edges at `x`, uncurried to `Δ[1] ⊗ Z ⟶ X`, is constant at `x`. -/
lemma uncurry_const_obj₀Equiv_symm_id_comp_ι {Z : SSet.{u}} :
    uncurry ((const (obj₀Equiv.symm (Edge.id x)) : Z ⟶ (X.mappingSpace x x : SSet.{u})) ≫
      (X.mappingSpace x x).ι) = const x := by
  have h : (const (obj₀Equiv.symm (Edge.id x)) : Z ⟶ (X.mappingSpace x x : SSet.{u})) ≫
      (X.mappingSpace x x).ι =
        const ((ihomObj₀Equiv _ X).symm (yonedaEquiv.symm (Edge.id x).edge)) := by
    rw [const_comp]
    exact congrArg const (obj₀Equiv_symm_apply_coe _)
  rw [h, const_ihomObj₀Equiv_symm, uncurry_curry, ← yonedaEquiv_const_one, Equiv.symm_apply_apply,
    comp_const]

/-! ### Functoriality -/

section map

variable {Y Z : SSet.{u}}

/-- Postcomposition with a map `f : X ⟶ Y` sends `Hom_X(x, y)` into `Hom_Y(f x, f y)`. -/
private lemma range_le_mappingSpace (f : X ⟶ Y) (x y : X _⦋0⦌) :
    Subcomplex.range ((X.mappingSpace x y).ι ≫ (ihom Δ[1]).map f) ≤
      Y.mappingSpace (f.app _ x) (f.app _ y) := by
  rw [range_le_mappingSpace_iff, uncurry_natural_right, whiskerRight_δ_one_uncurry_ι_assoc,
    whiskerRight_δ_zero_uncurry_ι_assoc, const_comp, const_comp]
  exact ⟨rfl, rfl⟩

variable (x y) in
/-- The map `Hom_X(x, y) ⟶ Hom_Y(f x, f y)` induced by a map of simplicial sets `f : X ⟶ Y`:
it sends a map `Δ[1] ⊗ Δ[n] ⟶ X` to its composite with `f`. -/
noncomputable def map (f : X ⟶ Y) :
    (X.mappingSpace x y : SSet.{u}) ⟶ (Y.mappingSpace (f.app _ x) (f.app _ y) : SSet.{u}) :=
  Subcomplex.lift _ (range_le_mappingSpace f x y)

variable (x y) in
/-- The map induced on mapping spaces is the restriction of postcomposition
`Fun(Δ[1], X) ⟶ Fun(Δ[1], Y)` with `f`. -/
@[reassoc (attr := simp)]
lemma map_ι (f : X ⟶ Y) :
    map x y f ≫ (Y.mappingSpace (f.app _ x) (f.app _ y)).ι =
      (X.mappingSpace x y).ι ≫ (ihom Δ[1]).map f :=
  (rfl)

/-- The map induced on mapping spaces sends a map `Δ[1] ⊗ Δ[n] ⟶ X` to its composite with
`f`. -/
@[simp]
lemma ihomObjEquiv_map_app_coe (f : X ⟶ Y) {n : ℕ} (σ : (X.mappingSpace x y : SSet.{u}) _⦋n⦌) :
    dsimp% ihomObjEquiv _ Y ((map x y f).app _ σ).val = ihomObjEquiv _ X σ.val ≫ f :=
  ihomObjEquiv_ihom_map_app _ f σ.val

variable (x y) in
/-- The identity induces the identity of mapping spaces. -/
@[simp]
lemma map_id : map x y (𝟙 X) = 𝟙 _ := by
  ext ⟨⟨n⟩⟩ σ
  refine Subtype.ext ((ihomObjEquiv _ X).injective ?_)
  exact (ihomObjEquiv_map_app_coe _ σ).trans (Category.comp_id _)

variable (x y) in
/-- The maps induced on mapping spaces are compatible with composition. -/
@[simp]
lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    map x y (f ≫ g) = map x y f ≫ map (f.app _ x) (f.app _ y) g := by
  ext ⟨⟨n⟩⟩ σ
  refine Subtype.ext ((ihomObjEquiv _ Z).injective ?_)
  exact (ihomObjEquiv_map_app_coe _ σ).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ g) (ihomObjEquiv_map_app_coe f σ).symm |>.trans
      (ihomObjEquiv_map_app_coe g _).symm))

/-- On vertices, the map induced on mapping spaces is the map of edges induced by `f`. -/
@[simp]
lemma obj₀Equiv_map_app (f : X ⟶ Y) (σ : (X.mappingSpace x y : SSet.{u}) _⦋0⦌) :
    dsimp% obj₀Equiv ((map x y f).app _ σ) = (obj₀Equiv σ).map f :=
  Edge.ext ((congrArg yonedaEquiv (ihomObj₀Equiv_ihom_map_app _ f σ.val)).trans
    (yonedaEquiv_comp _ _))

end map

end mappingSpace

/-! ### The comparison with the right mapping space -/

namespace rightMappingSpace

open prodStdSimplex

/-- The map `Δ[1] ⊗ Δ[n] ⟶ X` attached to an `n`-simplex `s` of `Hom^R_X(x, y)` lies in
`Hom_X(x, y)`. -/
private lemma toJoinVertex_comp_mem {n : ℕ} (t : X _⦋n + 1⦌)
    (ht : t ∈ (X.rightMappingSpace x y).obj (op ⦋n⦌)) :
    (ihomObjEquiv _ X).symm (toJoinVertex n ≫ yonedaEquiv.symm t) ∈
      (X.mappingSpace x y).obj _ := by
  obtain ⟨h₁, h₂⟩ := (mem_rightMappingSpace_iff t).1 ht
  rw [mem_mappingSpace_iff, Equiv.apply_symm_apply, whiskerRight_δ_one_toJoinVertex_assoc,
    whiskerRight_δ_zero_toJoinVertex_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, h₁, const_comp,
    ← yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_zero, comp_const, comp_const]
  exact ⟨rfl, congrArg _ h₂⟩

variable (x y) in
/-- The comparison map `Hom^R_X(x, y) ⟶ Hom_X(x, y)` from the right mapping space to the
mapping space. An `n`-simplex of `Hom^R_X(x, y)`, an `(n + 1)`-simplex `σ : Δ[n + 1] ⟶ X`, is
sent to the composite of `σ` with the map `Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` which collapses
`{1} × Δ[n]` to the last vertex (`SSet.prodStdSimplex.toJoinVertex`). -/
noncomputable def toMappingSpace :
    (X.rightMappingSpace x y : SSet.{u}) ⟶ (X.mappingSpace x y : SSet.{u}) where
  app m := TypeCat.ofHom fun s ↦ ⟨(ihomObjEquiv _ X).symm
    (toJoinVertex m.unop.len ≫ yonedaEquiv.symm (s.val : X _⦋m.unop.len + 1⦌)),
    toJoinVertex_comp_mem _ s.property⟩
  naturality m m' f := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext s
    refine Subtype.ext ((ihomObjEquiv _ X).injective ?_)
    -- The simplicial operator `f` acts on `Hom^R_X(x, y)` through `joinVertex.map f.unop`, and on
    -- `Fun(Δ[1], X)` by precomposition with `Δ[1] ◁ stdSimplex.map f.unop`.
    change ihomObjEquiv _ X ((ihomObjEquiv _ X).symm (toJoinVertex b ≫ yonedaEquiv.symm
        (X.map (SimplexCategory.joinVertex.map f.unop).op (s.val : X _⦋a + 1⦌)))) =
      ihomObjEquiv _ X (((ihom Δ[1]).obj X).map f.unop.op
        ((ihomObjEquiv _ X).symm (toJoinVertex a ≫ yonedaEquiv.symm (s.val : X _⦋a + 1⦌))))
    rw [ihomObjEquiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      whiskerLeft_map_toJoinVertex_assoc]
    exact congrArg (toJoinVertex b ≫ ·) (yonedaEquiv_symm_naturality_left _ _).symm

/-- The comparison map sends an `n`-simplex `σ : Δ[n + 1] ⟶ X` of `Hom^R_X(x, y)` to the map
`Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1] ⟶ X`. -/
@[simp]
lemma ihomObjEquiv_toMappingSpace_app_coe {n : ℕ}
    (s : (X.rightMappingSpace x y : SSet.{u}) _⦋n⦌) :
    dsimp% ihomObjEquiv _ X ((toMappingSpace x y).app _ s).val =
      toJoinVertex n ≫ yonedaEquiv.symm (s.val : X _⦋n + 1⦌) :=
  Equiv.apply_symm_apply _ _

/-- The comparison map `Hom^R_X(x, y) ⟶ Hom_X(x, y)` is a monomorphism, since
`toJoinVertex n : Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` is an epimorphism. -/
instance mono_toMappingSpace : Mono (toMappingSpace x y) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro s t hst
  have h : ihomObjEquiv _ X ((toMappingSpace x y).app _ s).val =
      ihomObjEquiv _ X ((toMappingSpace x y).app _ t).val :=
    congrArg _ (congrArg Subtype.val hst)
  rw [ihomObjEquiv_toMappingSpace_app_coe, ihomObjEquiv_toMappingSpace_app_coe, cancel_epi] at h
  exact Subtype.ext ((yonedaEquiv (X := X)).symm.injective h)

/-- On vertices, the comparison map is the identity of the edges from `x` to `y`. -/
@[simp]
lemma obj₀Equiv_toMappingSpace_app (s : (X.rightMappingSpace x y : SSet.{u}) _⦋0⦌) :
    dsimp% mappingSpace.obj₀Equiv ((toMappingSpace x y).app _ s) = obj₀Equiv s := by
  refine Edge.ext ?_
  rw [mappingSpace.obj₀Equiv_apply_edge, obj₀Equiv_apply_edge]
  -- The map `Δ[1] ⟶ X` of the image of `s` is `s` itself, since `toJoinVertex 0` is the first
  -- projection `Δ[1] ⊗ Δ[0] ⟶ Δ[1]`.
  have h : fst _ Δ[0] ≫ ihomObj₀Equiv _ X ((toMappingSpace x y).app _ s).val =
      fst _ Δ[0] ≫ (yonedaEquiv (X := X) (n := ⦋1⦌)).symm (s.val : X _⦋1⦌) := by
    rw [fst_comp_ihomObj₀Equiv, ihomObjEquiv_toMappingSpace_app_coe, toJoinVertex_zero]
  rw [cancel_epi] at h
  rw [h]
  exact (yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply _

/-- The comparison map is a bijection on vertices: both sets of vertices are the edges from `x`
to `y`. -/
lemma bijective_toMappingSpace_app_zero :
    Function.Bijective ((toMappingSpace x y).app (op ⦋0⦌)) := by
  have h : ⇑((toMappingSpace x y).app (op ⦋0⦌)) =
      mappingSpace.obj₀Equiv.symm ∘ obj₀Equiv := by
    funext s
    exact mappingSpace.obj₀Equiv.injective (by simp)
  rw [h]
  exact mappingSpace.obj₀Equiv.symm.bijective.comp obj₀Equiv.bijective

variable (x y) in
/-- The comparison maps are natural in the simplicial set. -/
@[reassoc]
lemma toMappingSpace_comp_map {Y : SSet.{u}} (f : X ⟶ Y) :
    toMappingSpace x y ≫ mappingSpace.map x y f =
      map x y f ≫ toMappingSpace (f.app _ x) (f.app _ y) := by
  ext ⟨⟨n⟩⟩ s
  refine Subtype.ext ((ihomObjEquiv _ Y).injective ?_)
  -- Evaluating the composites at `s` exposes the simp normal forms of the two comparison maps and
  -- of the two maps induced by `f`.
  change ihomObjEquiv _ Y ((mappingSpace.map x y f).app _ ((toMappingSpace x y).app _ s)).val =
    ihomObjEquiv _ Y ((toMappingSpace (f.app _ x) (f.app _ y)).app _ ((map x y f).app _ s)).val
  rw [mappingSpace.ihomObjEquiv_map_app_coe, ihomObjEquiv_toMappingSpace_app_coe,
    ihomObjEquiv_toMappingSpace_app_coe, Category.assoc]
  exact congrArg (toJoinVertex n ≫ ·)
    ((yonedaEquiv_symm_comp (X := X) (n := ⦋n + 1⦌) s.val f).trans
      (congrArg _ (map_app_coe f s).symm))

/-! ### Connected components -/

section π₀

variable [X.Quasicategory]

/-- The two endpoints of an edge of `Hom_X(x, y)` correspond to vertices in the same connected
component of `Hom^R_X(x, y)`. The edge is a square `Δ[1] ⊗ Δ[1] ⟶ X` from `e₀` to `e₁` whose
vertical sides are degenerate at `x` and `y`. Its two `2`-simplices exhibit its diagonal `d` as
`id x ≫ e₁` and as `e₀ ≫ id y`; the first is an edge of `Hom^R_X(x, y)` from `d` to `e₁`, and in a
quasicategory the second can be traded for a `2`-simplex exhibiting `d` as `id x ≫ e₀`. -/
private lemma π₀_mk_eq_of_edge {v₀ v₁ : (X.mappingSpace x y : SSet.{u}) _⦋0⦌} (E : Edge v₀ v₁) :
    π₀.mk (obj₀Equiv.symm (mappingSpace.obj₀Equiv v₀)) =
      π₀.mk (obj₀Equiv.symm (mappingSpace.obj₀Equiv v₁)) := by
  set h := ihomObjEquiv _ X E.edge.val with hh
  obtain ⟨hx, hy⟩ := (mem_mappingSpace_iff _).1 E.edge.property
  rw [← hh] at hx hy
  -- The bottom and top sides of the square are the edges given by `v₀` and `v₁`.
  have h₀ : Δ[1] ◁ stdSimplex.δ 1 ≫ h = fst _ _ ≫ ihomObj₀Equiv _ X v₀.val := by
    rw [fst_comp_ihomObj₀Equiv, ← E.src_eq]
    exact (ihomObjEquiv_map _ (SimplexCategory.δ 1) E.edge.val).symm
  have h₁ : Δ[1] ◁ stdSimplex.δ 0 ≫ h = fst _ _ ≫ ihomObj₀Equiv _ X v₁.val := by
    rw [fst_comp_ihomObj₀Equiv, ← E.tgt_eq]
    exact (ihomObjEquiv_map _ (SimplexCategory.δ 0) E.edge.val).symm
  -- The square is the union of the `2`-simplices `ι 0` and `ι 1`; the endpoints of their common
  -- diagonal lie on the vertical sides.
  have e₁ : stdSimplex.δ.{u} (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ 1 ≫ stdSimplex.δ 2 :=
    stdSimplex.δ_comp_δ_self
  have e₀ : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ 0 ≫ stdSimplex.δ 1 :=
    stdSimplex.δ_comp_δ_self
  -- The diagonal of the square.
  let d : Edge x y := Edge.mk (yonedaEquiv (stdSimplex.δ 1 ≫ prodStdSimplex₁.ι 0 ≫ h))
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, reassoc_of% e₁, prodStdSimplex₁.δ_two_ι_zero_assoc, hx,
        comp_const, comp_const, yonedaEquiv_const])
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, prodStdSimplex₁.δ_one_ι_zero_assoc, ← reassoc_of% e₀,
        prodStdSimplex₁.δ_zero_ι_one_assoc, hy, comp_const, comp_const, yonedaEquiv_const])
  have t₀ : Edge.CompStruct (.id x) (mappingSpace.obj₀Equiv v₁) d :=
    Edge.CompStruct.mk (yonedaEquiv (prodStdSimplex₁.ι 0 ≫ h))
      (by
        rw [← stdSimplex.yonedaEquiv_δ_comp, prodStdSimplex₁.δ_two_ι_zero_assoc, hx, comp_const,
          yonedaEquiv_const_one])
      (by
        rw [← stdSimplex.yonedaEquiv_δ_comp, prodStdSimplex₁.δ_zero_ι_zero_assoc, h₁,
          lift_fst_assoc, Category.id_comp, mappingSpace.obj₀Equiv_apply_edge])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp]; rfl)
  have t₁ : Edge.CompStruct (mappingSpace.obj₀Equiv v₀) (.id y) d :=
    Edge.CompStruct.mk (yonedaEquiv (prodStdSimplex₁.ι 1 ≫ h))
      (by
        rw [← stdSimplex.yonedaEquiv_δ_comp, prodStdSimplex₁.δ_two_ι_one_assoc, h₀, lift_fst_assoc,
          Category.id_comp, mappingSpace.obj₀Equiv_apply_edge])
      (by
        rw [← stdSimplex.yonedaEquiv_δ_comp, prodStdSimplex₁.δ_zero_ι_one_assoc, hy, comp_const,
          yonedaEquiv_const_one])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← prodStdSimplex₁.δ_one_ι_zero_assoc]; rfl)
  -- In a quasicategory, the left homotopy `t₁` from `e₀` to `d` is also a right homotopy.
  have t₁' : Edge.CompStruct (.id x) (mappingSpace.obj₀Equiv v₀) d :=
    .ofTruncated (Truncated.Edge.HomotopyL.homotopyR t₁.toTruncated)
  exact (π₀_mk_eq_of_compStruct t₁').symm.trans (π₀_mk_eq_of_compStruct t₀)

variable (x y) in
/-- **The comparison of mapping spaces on connected components**: for a quasicategory `X`, the
comparison map `Hom^R_X(x, y) ⟶ Hom_X(x, y)` induces a bijection on connected components. -/
theorem bijective_mapπ₀_toMappingSpace :
    Function.Bijective (mapπ₀ (toMappingSpace x y)) := by
  -- A left inverse sends the component of a vertex of `Hom_X(x, y)` to the component of the
  -- vertex of `Hom^R_X(x, y)` given by the same edge.
  let φ : π₀ (X.mappingSpace x y : SSet.{u}) → π₀ (X.rightMappingSpace x y : SSet.{u}) :=
    π₀.lift (fun v ↦ π₀.mk (obj₀Equiv.symm (mappingSpace.obj₀Equiv v)))
      fun _ _ E ↦ π₀_mk_eq_of_edge E
  have hφ : Function.LeftInverse φ (mapπ₀ (toMappingSpace x y)) := by
    intro c
    induction c with | mk s => simp [φ]
  refine ⟨hφ.injective, fun c ↦ ?_⟩
  induction c with | mk v =>
  obtain ⟨s, rfl⟩ := bijective_toMappingSpace_app_zero.2 v
  exact ⟨π₀.mk s, rfl⟩

end π₀

end rightMappingSpace

end SSet
