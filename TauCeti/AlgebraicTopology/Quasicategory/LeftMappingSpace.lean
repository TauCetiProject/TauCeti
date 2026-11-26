/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.MappingSpace
import TauCeti.AlgebraicTopology.SimplicialSet.Vertex

/-!
# Left mapping spaces of simplicial sets

For vertices `x` and `y` of a simplicial set `X`, the left mapping space `Hom^L_X(x, y)` is the
simplicial set whose `n`-simplices are the `(n + 1)`-simplices of `X` with initial vertex `x` whose
face opposite to the initial vertex is the constant simplex at `y`. Its vertices are the edges from
`x` to `y`. It is the fibre over `y` of the projection `X_{x/} ⟶ X` from the coslice under `x`
(`SSet.leftMappingSpace.cosliceFiberIso`, through `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`). It is the dual of the
right mapping space `Hom^R_X(x, y)` of `TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace`.

We realise it as a subcomplex of `SimplexCategory.vertexJoin.op ⋙ X`, the simplicial set whose
`n`-simplices are the `(n + 1)`-simplices of `X`, with simplicial operators acting on the last
`n + 1` vertices and fixing the initial one. Since `SimplexCategory.vertexJoin` is the conjugate of
`SimplexCategory.joinVertex` by the reversal of the vertices, reversing the vertices identifies
`Hom^L_X(x, y)` with the opposite of the right mapping space `Hom^R_{Xᵒᵖ}(y, x)`
(`SSet.leftMappingSpace.rightMappingSpaceOpIso`). As the opposite of a Kan complex is a Kan complex,
`Hom^L_X(x, y)` is a Kan complex when `X` is a quasicategory (`SSet.leftMappingSpace.kanComplex`).

An edge of `Hom^L_X(x, y)` from `s₀` to `s₁` is a `2`-simplex of `X` exhibiting `s₁` as a
composite of `s₀` and the identity of `y`, that is, a left homotopy from `s₀` to `s₁`. When `X` is
a quasicategory, the connected components of `Hom^L_X(x, y)` are therefore the morphisms from `x`
to `y` in the homotopy category of `X`.

Precomposition with the collapse `Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` of `{0} × Δ[n]` to the initial vertex
(`SSet.prodStdSimplex.toVertexJoin`) is a natural monomorphism `Hom^L_X(x, y) ⟶ Hom_X(x, y)` to the
two-sided mapping space of `TauCeti.AlgebraicTopology.Quasicategory.MappingSpace`. It is the
identity of the edges from `x` to `y` on vertices, and, for a quasicategory, a bijection on
connected components.

## Main definitions

* `SSet.leftMappingSpace X x y`: the left mapping space `Hom^L_X(x, y)`.
* `SSet.leftMappingSpace.obj₀Equiv`: its vertices are the edges from `x` to `y`.
* `SSet.leftMappingSpace.map x y f`: the map `Hom^L_X(x, y) ⟶ Hom^L_Y(f x, f y)` induced by
  `f : X ⟶ Y`.
* `SSet.leftMappingSpace.rightMappingSpaceOpIso x y`: the isomorphism
  `Hom^L_X(x, y) ≅ (Hom^R_{Xᵒᵖ}(y, x))ᵒᵖ`.
* `SSet.leftMappingSpace.edgeEquiv`: the edges of `Hom^L_X(x, y)` from `s₀` to `s₁` are the
  `2`-simplices of `X` exhibiting `s₁` as a composite of `s₀` and the identity of `y`.
* `SSet.leftMappingSpace.π₀Equiv x y`: for a quasicategory `X`, the connected components of
  `Hom^L_X(x, y)` are the morphisms from `x` to `y` in the homotopy category of `X`.
* `SSet.leftMappingSpace.cosliceFiberIso x y`: `Hom^L_X(x, y)` is the fibre over `y` of the
  projection `X_{x/} ⟶ X` from the coslice under `x`.
* `SSet.leftMappingSpace.toMappingSpace x y`: the comparison `Hom^L_X(x, y) ⟶ Hom_X(x, y)`.

## Main results

* `SSet.leftMappingSpace.kanComplex`: the left mapping spaces of a quasicategory are Kan
  complexes.
* `SSet.leftMappingSpace.mono_toMappingSpace`, `SSet.leftMappingSpace.toMappingSpace_comp_map`:
  the comparison with the two-sided mapping space is a natural monomorphism.
* `SSet.leftMappingSpace.bijective_toMappingSpace_app_zero`: it is a bijection on vertices.
* `SSet.leftMappingSpace.bijective_mapπ₀_toMappingSpace`: for a quasicategory, it is a bijection
  on connected components.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 (the left mapping space `Hom^L_S(x, y)`, the opposite
  of `Hom^R_{Sᵒᵖ}(y, x)`) and §4.2.1 (the comparison of the mapping spaces).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite Simplicial

universe u

namespace SSet

open SimplexCategory

variable (X : SSet.{u})

/-- The left mapping space `Hom^L_X(x, y)` between vertices `x` and `y` of a simplicial set `X`.
It is the subcomplex of `vertexJoin.op ⋙ X` whose `n`-simplices are the `(n + 1)`-simplices of `X`
with initial vertex `x` whose face opposite to the initial vertex is the constant simplex at `y`.
Equivalently, it is the fibre over `y` of the projection to `X` of the coslice `X_{x/}`. -/
def leftMappingSpace (x y : X _⦋0⦌) : Subcomplex (vertexJoin.op ⋙ X) where
  obj m := {σ | X.map (SimplexCategory.const ⦋0⦌ ⦋m.unop.len + 1⦌ 0).op σ = x ∧
      X.δ (n := m.unop.len) 0 σ = X.map (SimplexCategory.const ⦋m.unop.len⦌ ⦋0⦌ 0).op y}
  map {m m'} f σ hσ := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    -- `f` acts on `vertexJoin.op ⋙ X` as `vertexJoin.map f.unop` acts on `X`, which fixes the
    -- initial vertex and commutes with the face `δ 0` opposite to it. The simplex `σ` lies in
    -- `X _⦋a + 1⦌` only up to unfolding `vertexJoin`, so the steps are composed with `Eq.trans`.
    refine ⟨?_, ?_⟩
    · have h := congrArg (fun g ↦ X.map g.op σ)
        (const_zero_comp_vertexJoin_map (x := ⦋0⦌) f.unop)
      exact (Functor.map_comp_apply X _ _ σ).symm.trans (h.trans hσ.1)
    · have h := congrArg (fun g ↦ X.map g.op σ) (δ_zero_comp_vertexJoin_map f.unop)
      exact (Functor.map_comp_apply X _ _ σ).symm.trans (h.trans
        ((Functor.map_comp_apply X _ _ σ).trans ((congrArg _ hσ.2).trans
          (map_map_const_zero X _ y))))

variable {X} {x y : X _⦋0⦌}

/-- An `(n + 1)`-simplex of `X` is an `n`-simplex of `Hom^L_X(x, y)` exactly when its initial
vertex is `x` and its face opposite to the initial vertex is the constant simplex at `y`. -/
theorem mem_leftMappingSpace_iff {n : ℕ} (σ : X _⦋n + 1⦌) :
    σ ∈ (X.leftMappingSpace x y).obj (op ⦋n⦌) ↔
      X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op σ = x ∧
        X.δ 0 σ = X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op y :=
  Iff.rfl

namespace leftMappingSpace

/-- The vertices of the left mapping space `Hom^L_X(x, y)` are the edges from `x` to `y`. -/
def obj₀Equiv : (X.leftMappingSpace x y : SSet.{u}) _⦋0⦌ ≃ Edge x y where
  toFun σ := Edge.mk (σ.val : X _⦋1⦌)
    (by
      simpa [SimplicialObject.δ, SimplexCategory.δ_one_eq_const] using
        ((mem_leftMappingSpace_iff (n := 0) _).1 σ.property).1)
    (by simpa [const_eq_id] using ((mem_leftMappingSpace_iff (n := 0) _).1 σ.property).2)
  invFun e := ⟨e.edge, (mem_leftMappingSpace_iff (n := 0) _).2
    ⟨by simpa [SimplicialObject.δ, SimplexCategory.δ_one_eq_const] using e.src_eq,
      by simp [const_eq_id]⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The edge attached to a vertex of `Hom^L_X(x, y)` is that vertex, as a `1`-simplex of `X`. -/
@[simp]
theorem obj₀Equiv_apply_edge (σ : (X.leftMappingSpace x y : SSet.{u}) _⦋0⦌) :
    dsimp% (obj₀Equiv σ).edge = σ.val :=
  (rfl)

/-- The vertex of `Hom^L_X(x, y)` attached to an edge is that edge, as a `1`-simplex of `X`. -/
@[simp]
theorem obj₀Equiv_symm_apply_coe (e : Edge x y) :
    dsimp% (obj₀Equiv.symm e).val = e.edge :=
  (rfl)

/-- The `j`-th face of an `(n + 1)`-simplex of `Hom^L_X(x, y)` is the `(j + 1)`-th face of the
corresponding `(n + 2)`-simplex of `X`. -/
@[simp]
theorem coe_δ {n : ℕ} (j : Fin (n + 2)) (s : (X.leftMappingSpace x y : SSet.{u}) _⦋n + 1⦌) :
    dsimp% (SimplicialObject.δ (X.leftMappingSpace x y : SSet.{u}) j s).val =
      X.δ j.succ (s.val : X _⦋n + 2⦌) :=
  (ConcreteCategory.congr_hom (X.vertexJoin_op_comp_δ j) s.val :)

/-- The `j`-th degeneracy of an `n`-simplex of `Hom^L_X(x, y)` is the `(j + 1)`-th degeneracy of
the corresponding `(n + 1)`-simplex of `X`. -/
@[simp]
theorem coe_σ {n : ℕ} (j : Fin (n + 1)) (s : (X.leftMappingSpace x y : SSet.{u}) _⦋n⦌) :
    dsimp% (SimplicialObject.σ (X.leftMappingSpace x y : SSet.{u}) j s).val =
      X.σ j.succ (s.val : X _⦋n + 1⦌) :=
  (ConcreteCategory.congr_hom (X.vertexJoin_op_comp_σ j) s.val :)

/-- The initial vertex of an `n`-simplex of `Hom^L_X(x, y)`, an `(n + 1)`-simplex of `X`, is
`x`. -/
@[simp]
theorem map_const_zero {n : ℕ} (s : (X.leftMappingSpace x y : SSet.{u}) _⦋n⦌) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (s.val : X _⦋n + 1⦌) = x :=
  ((mem_leftMappingSpace_iff _).1 s.property).1

/-! ### Functoriality -/

section map

variable {Y Z : SSet.{u}}

/-- A map of simplicial sets `f : X ⟶ Y` sends the simplices of `Hom^L_X(x, y)` to simplices of
`Hom^L_Y(f x, f y)`. -/
private theorem range_le_leftMappingSpace (f : X ⟶ Y) (x y : X _⦋0⦌) :
    Subcomplex.range ((X.leftMappingSpace x y).ι ≫ Functor.whiskerLeft vertexJoin.op f) ≤
      Y.leftMappingSpace (f.app _ x) (f.app _ y) := by
  rintro m _ ⟨s, rfl⟩
  -- The faces and vertices of `f σ` are the images under `f` of those of `σ`, by naturality.
  exact ⟨(NatTrans.naturality_apply f _ s.val).symm.trans (congrArg (f.app _) s.property.1),
    (NatTrans.naturality_apply f _ s.val).symm.trans
      ((congrArg (f.app _) s.property.2).trans (NatTrans.naturality_apply f _ y))⟩

variable (x y) in
/-- The map `Hom^L_X(x, y) ⟶ Hom^L_Y(f x, f y)` induced by a map of simplicial sets
`f : X ⟶ Y`: it sends an `n`-simplex of `Hom^L_X(x, y)`, an `(n + 1)`-simplex of `X`, to its image
under `f`. -/
def map (f : X ⟶ Y) :
    (X.leftMappingSpace x y : SSet.{u}) ⟶ (Y.leftMappingSpace (f.app _ x) (f.app _ y) : SSet.{u}) :=
  Subcomplex.lift _ (range_le_leftMappingSpace f x y)

variable (x y) in
/-- The map induced on left mapping spaces is the restriction of the map induced by `f` on
`vertexJoin.op ⋙ X`. -/
@[reassoc (attr := simp)]
theorem map_ι (f : X ⟶ Y) :
    map x y f ≫ (Y.leftMappingSpace (f.app _ x) (f.app _ y)).ι =
      (X.leftMappingSpace x y).ι ≫ Functor.whiskerLeft vertexJoin.op f :=
  (rfl)

/-- The map induced on left mapping spaces sends an `(n + 1)`-simplex of `X` to its image under
`f`. -/
@[simp]
theorem map_app_coe (f : X ⟶ Y) {n : ℕ} (s : (X.leftMappingSpace x y : SSet.{u}) _⦋n⦌) :
    dsimp% ((map x y f).app _ s).val = f.app _ (s.val : X _⦋n + 1⦌) :=
  (rfl)

variable (x y) in
/-- The identity induces the identity of left mapping spaces. -/
@[simp]
theorem map_id : map x y (𝟙 X) = 𝟙 _ :=
  (rfl)

variable (x y) in
/-- The maps induced on left mapping spaces are compatible with composition. -/
@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    map x y (f ≫ g) = map x y f ≫ map (f.app _ x) (f.app _ y) g :=
  (rfl)

/-- On vertices, the map induced on left mapping spaces is the map of edges induced by `f`. -/
@[simp]
theorem obj₀Equiv_map_app (f : X ⟶ Y) (s : (X.leftMappingSpace x y : SSet.{u}) _⦋0⦌) :
    dsimp% obj₀Equiv ((map x y f).app _ s) = (obj₀Equiv s).map f :=
  Edge.ext (rfl)

/-- A monomorphism induces monomorphisms of left mapping spaces. -/
instance mono_map (f : X ⟶ Y) [Mono f] : Mono (map x y f) := by
  have : Mono (Functor.whiskerLeft vertexJoin.op f) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    exact (NatTrans.mono_iff_mono_app f).1 inferInstance _
  exact mono_of_mono_fac (map_ι x y f)

/-- The map induced on left mapping spaces by an isomorphism is an isomorphism. -/
instance isIso_map (f : X ⟶ Y) [IsIso f] : IsIso (map x y f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  refine ⟨(CategoryTheory.mono_iff_injective _).1 inferInstance, fun s ↦ ?_⟩
  -- The preimage of `s` is its image under the inverse of `f`, which lies in `Hom^L_X(x, y)`
  -- because the inverse of `f` sends `f x` and `f y` back to `x` and `y`.
  have hs : (inv f).app _ (s.val : Y _⦋n + 1⦌) ∈ (X.leftMappingSpace ((inv f).app _ (f.app _ x))
      ((inv f).app _ (f.app _ y))).obj (op ⦋n⦌) :=
    ((map (f.app _ x) (f.app _ y) (inv f)).app _ s).property
  have hx (z : X _⦋0⦌) : (inv f).app _ (f.app _ z) = z := by simp
  rw [hx, hx] at hs
  exact ⟨⟨_, hs⟩, Subtype.ext ((map_app_coe f _).trans (by simp))⟩

end map

/-! ### Left mapping spaces as opposites of right mapping spaces -/

section op

variable (x y)

/-- An `(n + 1)`-simplex `σ` of `X` is a simplex of `Hom^L_X(x, y)` exactly when the same simplex
of `Xᵒᵖ` is a simplex of `Hom^R_{Xᵒᵖ}(y, x)`: reversal exchanges the initial and the last vertex,
and the faces opposite to them. -/
private theorem mem_rightMappingSpace_op_iff {n : ℕ} (σ : X _⦋n + 1⦌) :
    X.opObjEquiv.symm σ ∈
        (X.op.rightMappingSpace (X.opObjEquiv.symm y) (X.opObjEquiv.symm x)).obj (op ⦋n⦌) ↔
      σ ∈ (X.leftMappingSpace x y).obj (op ⦋n⦌) := by
  have h₁ : rev.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last _)) =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 :=
    Hom.ext_zero_left _ _ (by simp [rev_map_apply])
  have h₂ : rev.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) = SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 :=
    eq_const_to_zero _
  refine (mem_rightMappingSpace_iff _).trans (Iff.trans ?_ (mem_leftMappingSpace_iff σ).symm)
  -- Reversal turns the last vertex and the face opposite to it into the initial ones.
  simp only [op_δ, op_map, Quiver.Hom.unop_op, h₁, h₂, Fin.rev_last, Equiv.apply_symm_apply,
    Equiv.apply_eq_iff_eq]
  exact and_comm

/-- **The left mapping space is the opposite of a right mapping space of the opposite**:
`Hom^L_X(x, y) ≅ (Hom^R_{Xᵒᵖ}(y, x))ᵒᵖ`. Both sides have the `(n + 1)`-simplices of `X` as
`n`-simplices; reversing their vertices exchanges the conditions defining the two mapping spaces. -/
noncomputable def rightMappingSpaceOpIso :
    (X.leftMappingSpace x y : SSet.{u}) ≅
      (X.op.rightMappingSpace (X.opObjEquiv.symm y) (X.opObjEquiv.symm x) : SSet.{u}).op :=
  NatIso.ofComponents (fun m ↦ Equiv.toIso
    { toFun s := opObjEquiv.symm ⟨X.opObjEquiv.symm s.val,
        (mem_rightMappingSpace_op_iff x y (n := m.unop.len) s.val).2 s.property⟩
      invFun t := ⟨X.opObjEquiv (opObjEquiv t).val,
        (mem_rightMappingSpace_op_iff x y (n := m.unop.len) _).1 (opObjEquiv t).property⟩
      left_inv _ := rfl
      right_inv _ := rfl })
    -- `vertexJoin` is by definition the conjugate of `joinVertex` by `rev`, through which
    -- simplicial operators act on `Xᵒᵖ`, so both actions of an operator are the same map of `X`.
    (fun _ ↦ rfl)

/-- The simplex of `Xᵒᵖ` underlying the image of a simplex of `Hom^L_X(x, y)` in
`(Hom^R_{Xᵒᵖ}(y, x))ᵒᵖ` is the same simplex, viewed in `Xᵒᵖ`. -/
@[simp]
theorem coe_opObjEquiv_rightMappingSpaceOpIso_hom_app {n : ℕ}
    (s : (X.leftMappingSpace x y : SSet.{u}) _⦋n⦌) :
    dsimp% ((opObjEquiv ((rightMappingSpaceOpIso x y).hom.app _ s)).val : X.op _⦋n + 1⦌) =
      X.opObjEquiv.symm (s.val : X _⦋n + 1⦌) :=
  (rfl)

/-- The simplex of `X` underlying the image of a simplex of `(Hom^R_{Xᵒᵖ}(y, x))ᵒᵖ` in
`Hom^L_X(x, y)` is the same simplex, viewed in `X`. -/
@[simp]
theorem coe_rightMappingSpaceOpIso_inv_app {n : ℕ}
    (t : (X.op.rightMappingSpace (X.opObjEquiv.symm y) (X.opObjEquiv.symm x) : SSet.{u}).op _⦋n⦌) :
    dsimp% (((rightMappingSpaceOpIso x y).inv.app _ t).val : X _⦋n + 1⦌) =
      X.opObjEquiv ((opObjEquiv t).val : X.op _⦋n + 1⦌) :=
  (rfl)

open modelCategoryQuillen in
/-- **The left mapping spaces of a quasicategory are Kan complexes**: `Hom^L_X(x, y)` is isomorphic
to the opposite of the Kan complex `Hom^R_{Xᵒᵖ}(y, x)`. -/
instance kanComplex [X.Quasicategory] : KanComplex (X.leftMappingSpace x y : SSet.{u}) :=
  HomotopicalAlgebra.isFibrant_of_fibration (rightMappingSpaceOpIso x y).hom

end op

/-! ### Edges and connected components -/

section π₀

/-- An edge of `Hom^L_X(x, y)` from `s₀` to `s₁`, a `2`-simplex of `X`, is the same as a
`2`-simplex exhibiting the edge `s₁` as a composite of the edge `s₀` and the identity of `y`. -/
def edgeEquiv (s₀ s₁ : (X.leftMappingSpace x y : SSet.{u}) _⦋0⦌) :
    Edge s₀ s₁ ≃ Edge.CompStruct (obj₀Equiv s₀) (Edge.id y) (obj₀Equiv s₁) where
  toFun e := Edge.CompStruct.mk (e.edge.val : X _⦋2⦌)
    ((coe_δ 1 e.edge).symm.trans (congrArg Subtype.val e.src_eq))
    (by
      -- The degeneracy `⦋1⦌ ⟶ ⦋0⦌` is the constant map.
      rw [Edge.id_edge, SimplicialObject.σ,
        Subsingleton.elim (SimplexCategory.σ 0) (SimplexCategory.const _ _ 0)]
      exact ((mem_leftMappingSpace_iff (n := 1) _).1 e.edge.property).2)
    ((coe_δ 0 e.edge).symm.trans (congrArg Subtype.val e.tgt_eq))
  invFun h := Edge.mk ⟨h.simplex, (mem_leftMappingSpace_iff (n := 1) _).2
      ⟨-- The initial vertex of `h.simplex` is the initial vertex of its face `s₀`.
        (map_const_map (SimplexCategory.δ 2).op h.simplex 0).symm.trans (by
          rw [← SimplicialObject.δ_def, h.d₂]
          exact map_const_zero s₀),
        by
          rw [← Subsingleton.elim (SimplexCategory.σ 0) (SimplexCategory.const _ _ 0),
            ← SimplicialObject.σ, ← Edge.id_edge]
          exact h.d₀⟩⟩
    (Subtype.ext ((coe_δ 1 _).trans h.d₂)) (Subtype.ext ((coe_δ 0 _).trans h.d₁))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `2`-simplex attached to an edge of `Hom^L_X(x, y)` is that edge. -/
@[simp]
theorem edgeEquiv_apply_simplex {s₀ s₁ : (X.leftMappingSpace x y : SSet.{u}) _⦋0⦌}
    (e : Edge s₀ s₁) : dsimp% (edgeEquiv s₀ s₁ e).simplex = e.edge.val :=
  (rfl)

/-- The edge of `Hom^L_X(x, y)` attached to a `2`-simplex is that `2`-simplex. -/
@[simp]
theorem coe_edgeEquiv_symm_apply_edge {s₀ s₁ : (X.leftMappingSpace x y : SSet.{u}) _⦋0⦌}
    (h : Edge.CompStruct (obj₀Equiv s₀) (Edge.id y) (obj₀Equiv s₁)) :
    dsimp% ((edgeEquiv s₀ s₁).symm h).edge.val = h.simplex :=
  (rfl)

variable [X.Quasicategory]

variable (x y) in
/-- For a quasicategory `X`, the connected components of the left mapping space `Hom^L_X(x, y)`
are the morphisms from `x` to `y` in the homotopy category of `X`: a vertex of `Hom^L_X(x, y)`,
an edge from `x` to `y`, is sent to its class. -/
noncomputable def π₀Equiv :
    π₀ (X.leftMappingSpace x y : SSet.{u}) ≃ (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) :=
  Equiv.ofBijective (π₀.lift (fun s ↦ HomotopyCategory.homMk (obj₀Equiv s))
      fun s₀ s₁ e ↦ (HomotopyCategory.homMk_eq_homMk_iff _ _).2
        ⟨Edge.HomotopyL.homotopyR (edgeEquiv s₀ s₁ e)⟩)
    ⟨fun c₀ c₁ h ↦ by
      induction c₀ with | mk s₀ => ?_
      induction c₁ with | mk s₁ => ?_
      obtain ⟨h⟩ := (HomotopyCategory.homMk_eq_homMk_iff _ _).1 h
      exact π₀.sound ((edgeEquiv s₀ s₁).symm (Edge.HomotopyR.homotopyL h)),
    fun φ ↦ by
      obtain ⟨e, rfl⟩ := HomotopyCategory.homMk_surjective φ
      exact ⟨π₀.mk (obj₀Equiv.symm e), by simp⟩⟩

/-- The connected component of a vertex of `Hom^L_X(x, y)` corresponds to the class of the edge
it is. -/
@[simp]
theorem π₀Equiv_mk (s : (X.leftMappingSpace x y : SSet.{u}) _⦋0⦌) :
    π₀Equiv x y (π₀.mk s) = HomotopyCategory.homMk (obj₀Equiv s) :=
  (rfl)

/-- The class of an edge corresponds to the connected component of the corresponding vertex of
`Hom^L_X(x, y)`. -/
@[simp]
theorem π₀Equiv_symm_homMk (e : Edge x y) :
    (π₀Equiv x y).symm (HomotopyCategory.homMk e) = π₀.mk (obj₀Equiv.symm e) :=
  (Equiv.symm_apply_eq _).2 (by simp)

variable {Y : SSet.{u}} [Y.Quasicategory]

/-- Under `π₀Equiv`, the map induced by `f : X ⟶ Y` on connected components of left mapping
spaces is the action of the functor of homotopy categories induced by `f`. -/
@[simp]
theorem π₀Equiv_mapπ₀_map (f : X ⟶ Y) (c : π₀ (X.leftMappingSpace x y : SSet.{u})) :
    π₀Equiv (f.app _ x) (f.app _ y) (mapπ₀ (map x y f) c) =
      (mapHomotopyCategory f).map (π₀Equiv x y c) := by
  induction c with | mk s => simp

end π₀

/-! ### Left mapping spaces as fibres of coslices -/

section cosliceFiber

variable (x y)

/-- The `n`-simplices of the fibre over `y` of `X_{x/} ⟶ X` are those of `Hom^L_X(x, y)`, through
`Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
private noncomputable def cosliceFiberEquiv (n : ℕ) :
    (fiber (coslice.π (yonedaEquiv.symm x)) y : SSet.{u}) _⦋n⦌ ≃
      (X.leftMappingSpace x y : SSet.{u}) _⦋n⦌ where
  toFun s := ⟨(yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s.val).val) : X _⦋n + 1⦌),
    (mem_leftMappingSpace_iff _).2 ⟨by
      rw [yonedaEquiv_naturality, join.const_zero_comp_coneIso_inv_assoc,
        (coslice.objEquiv s.val).property, Equiv.apply_symm_apply], by
      rw [← stdSimplex.yonedaEquiv_δ_comp, join.δ_zero_comp_coneIso_inv_assoc, ← coslice.π_app,
        ← mem_fiber_iff]
      exact s.property⟩⟩
  invFun t := ⟨coslice.objEquiv.symm
      ⟨(join.coneIso n).hom ≫ yonedaEquiv.symm (t.val : X _⦋n + 1⦌),
        (join.inl_comp_coneIso_hom_assoc _).trans
          ((yonedaEquiv_symm_naturality_left (X := X) (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0)
            (t.val : X _⦋n + 1⦌)).trans
            (congrArg yonedaEquiv.symm ((mem_leftMappingSpace_iff _).1 t.property).1))⟩, by
    rw [mem_fiber_iff, coslice.π_app, Equiv.apply_symm_apply, join.inr_comp_coneIso_hom_assoc]
    -- The simplex `t.val` lies in `X _⦋n + 1⦌` only up to unfolding `vertexJoin`, so the last
    -- steps are composed with `Eq.trans` rather than rewritten.
    exact (congrArg yonedaEquiv (stdSimplex.δ_comp_yonedaEquiv_symm (t.val : X _⦋n + 1⦌) 0)).trans
      ((Equiv.apply_symm_apply _ _).trans ((mem_leftMappingSpace_iff _).1 t.property).2)⟩
  left_inv s := Subtype.ext (coslice.objEquiv.injective (Subtype.ext (by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc])))
  right_inv t := Subtype.ext (by
    simp only [Equiv.apply_symm_apply, Iso.inv_hom_id_assoc]
    exact yonedaEquiv.apply_symm_apply _)

/-- **The left mapping space `Hom^L_X(x, y)` is the fibre over `y` of the projection
`X_{x/} ⟶ X`** of the coslice under `x`. Through `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`, an `n`-simplex
`Δ[0] ⋆ Δ[n] ⟶ X` of the coslice is an `(n + 1)`-simplex of `X` with initial vertex `x`, and it lies
over `y` exactly when its face opposite to the initial vertex is constant at `y`. -/
noncomputable def cosliceFiberIso :
    (fiber (coslice.π (yonedaEquiv.symm x)) y : SSet.{u}) ≅ (X.leftMappingSpace x y : SSet.{u}) :=
  NatIso.ofComponents (fun m ↦ (cosliceFiberEquiv x y m.unop.len).toIso) (fun {m m'} f ↦ by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext s : 3
    refine Subtype.ext ?_
    -- Both sides are, by definition, the `(n + 1)`-simplices below; they agree by the naturality
    -- of `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`.
    have key : (yonedaEquiv ((join.coneIso b).inv ≫
        (coslice.objEquiv ((coslice (yonedaEquiv.symm x)).map f s.val)).val) : X _⦋b + 1⦌) =
        X.map (vertexJoin.map f.unop).op
          (yonedaEquiv ((join.coneIso a).inv ≫ (coslice.objEquiv s.val).val)) := by
      rw [coslice.objEquiv_map_coe, yonedaEquiv_naturality]
      exact congrArg yonedaEquiv (join.vertexJoin_map_comp_coneIso_inv_assoc f.unop _).symm
    -- `key` is the goal, with the maps of the fibre and of `Hom^L_X(x, y)` applied; the trailing
    -- `rfl` unfolds the action of `f` on `Hom^L_X(x, y)` once the fibre side is matched.
    exact key.trans rfl)

/-- The simplex of `Hom^L_X(x, y)` attached to a simplex `Δ[0] ⋆ Δ[n] ⟶ X` of the fibre of
`X_{x/} ⟶ X` is its composite with `Δ[n + 1] ≅ Δ[0] ⋆ Δ[n]`. -/
@[simp]
theorem cosliceFiberIso_hom_app_coe {n : ℕ}
    (s : (fiber (coslice.π (yonedaEquiv.symm x)) y : SSet.{u}) _⦋n⦌) :
    dsimp% ((cosliceFiberIso x y).hom.app _ s).val =
      (yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s.val).val) : X _⦋n + 1⦌) :=
  (rfl)

/-- The simplex `Δ[0] ⋆ Δ[n] ⟶ X` of the fibre of `X_{x/} ⟶ X` attached to a simplex of
`Hom^L_X(x, y)` is its composite with `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
@[simp]
theorem cosliceFiberIso_inv_app_coe {n : ℕ} (t : (X.leftMappingSpace x y : SSet.{u}) _⦋n⦌) :
    dsimp% (coslice.objEquiv ((cosliceFiberIso x y).inv.app _ t).val).val =
      (join.coneIso n).hom ≫ yonedaEquiv.symm (t.val : X _⦋n + 1⦌) :=
  congrArg Subtype.val (coslice.objEquiv.apply_symm_apply _)

end cosliceFiber

/-! ### The comparison with the mapping space -/

open prodStdSimplex

/-- The map `Δ[1] ⊗ Δ[n] ⟶ X` attached to an `n`-simplex of `Hom^L_X(x, y)` lies in
`Hom_X(x, y)`. -/
private lemma toVertexJoin_comp_mem {n : ℕ} (t : X _⦋n + 1⦌)
    (ht : t ∈ (X.leftMappingSpace x y).obj (op ⦋n⦌)) :
    (ihomObjEquiv _ X).symm (toVertexJoin n ≫ yonedaEquiv.symm t) ∈
      (X.mappingSpace x y).obj _ := by
  obtain ⟨h₁, h₂⟩ := (mem_leftMappingSpace_iff t).1 ht
  rw [mem_mappingSpace_iff, Equiv.apply_symm_apply, whiskerRight_δ_one_toVertexJoin_assoc,
    whiskerRight_δ_zero_toVertexJoin_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, h₂, const_comp,
    ← yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_zero, comp_const, comp_const]
  exact ⟨congrArg _ h₁, rfl⟩

variable (x y) in
/-- The comparison map `Hom^L_X(x, y) ⟶ Hom_X(x, y)` from the left mapping space to the
mapping space. An `n`-simplex of `Hom^L_X(x, y)`, an `(n + 1)`-simplex `σ : Δ[n + 1] ⟶ X`, is
sent to the composite of `σ` with the map `Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` which collapses
`{0} × Δ[n]` to the initial vertex (`SSet.prodStdSimplex.toVertexJoin`). -/
noncomputable def toMappingSpace :
    (X.leftMappingSpace x y : SSet.{u}) ⟶ (X.mappingSpace x y : SSet.{u}) where
  app m := TypeCat.ofHom fun s ↦ ⟨(ihomObjEquiv _ X).symm
    (toVertexJoin m.unop.len ≫ yonedaEquiv.symm (s.val : X _⦋m.unop.len + 1⦌)),
    toVertexJoin_comp_mem _ s.property⟩
  naturality m m' f := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext s
    refine Subtype.ext ((ihomObjEquiv _ X).injective ?_)
    -- The simplicial operator `f` acts on `Hom^L_X(x, y)` through `vertexJoin.map f.unop`, and on
    -- `Fun(Δ[1], X)` by precomposition with `Δ[1] ◁ stdSimplex.map f.unop`.
    change ihomObjEquiv _ X ((ihomObjEquiv _ X).symm (toVertexJoin b ≫ yonedaEquiv.symm
        (X.map (SimplexCategory.vertexJoin.map f.unop).op (s.val : X _⦋a + 1⦌)))) =
      ihomObjEquiv _ X (((ihom Δ[1]).obj X).map f.unop.op
        ((ihomObjEquiv _ X).symm (toVertexJoin a ≫ yonedaEquiv.symm (s.val : X _⦋a + 1⦌))))
    rw [ihomObjEquiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      whiskerLeft_map_toVertexJoin_assoc]
    exact congrArg (toVertexJoin b ≫ ·) (yonedaEquiv_symm_naturality_left _ _).symm

/-- The comparison map sends an `n`-simplex `σ : Δ[n + 1] ⟶ X` of `Hom^L_X(x, y)` to the map
`Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1] ⟶ X`. -/
@[simp]
lemma ihomObjEquiv_toMappingSpace_app_coe {n : ℕ}
    (s : (X.leftMappingSpace x y : SSet.{u}) _⦋n⦌) :
    dsimp% ihomObjEquiv _ X ((toMappingSpace x y).app _ s).val =
      toVertexJoin n ≫ yonedaEquiv.symm (s.val : X _⦋n + 1⦌) :=
  Equiv.apply_symm_apply _ _

/-- The comparison map `Hom^L_X(x, y) ⟶ Hom_X(x, y)` is a monomorphism, since
`toVertexJoin n : Δ[1] ⊗ Δ[n] ⟶ Δ[n + 1]` is an epimorphism. -/
instance mono_toMappingSpace : Mono (toMappingSpace x y) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [CategoryTheory.mono_iff_injective]
  intro s t hst
  have h : ihomObjEquiv _ X ((toMappingSpace x y).app _ s).val =
      ihomObjEquiv _ X ((toMappingSpace x y).app _ t).val :=
    congrArg _ (congrArg Subtype.val hst)
  rw [ihomObjEquiv_toMappingSpace_app_coe, ihomObjEquiv_toMappingSpace_app_coe, cancel_epi] at h
  exact Subtype.ext ((yonedaEquiv (X := X)).symm.injective h)

/-- On vertices, the comparison map is the identity of the edges from `x` to `y`. -/
@[simp]
lemma obj₀Equiv_toMappingSpace_app (s : (X.leftMappingSpace x y : SSet.{u}) _⦋0⦌) :
    dsimp% mappingSpace.obj₀Equiv ((toMappingSpace x y).app _ s) = obj₀Equiv s := by
  refine Edge.ext ?_
  rw [mappingSpace.obj₀Equiv_apply_edge, obj₀Equiv_apply_edge]
  -- The map `Δ[1] ⟶ X` of the image of `s` is `s` itself, since `toVertexJoin 0` is the first
  -- projection `Δ[1] ⊗ Δ[0] ⟶ Δ[1]`.
  have h : fst _ Δ[0] ≫ ihomObj₀Equiv _ X ((toMappingSpace x y).app _ s).val =
      fst _ Δ[0] ≫ (yonedaEquiv (X := X) (n := ⦋1⦌)).symm (s.val : X _⦋1⦌) := by
    rw [fst_comp_ihomObj₀Equiv, ihomObjEquiv_toMappingSpace_app_coe, toVertexJoin_zero]
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
  exact congrArg (toVertexJoin n ≫ ·)
    ((yonedaEquiv_symm_comp (X := X) (n := ⦋n + 1⦌) s.val f).trans
      (congrArg _ (map_app_coe f s).symm))

variable (x y) in
/-- **The comparison of mapping spaces on connected components**: for a quasicategory `X`, the
comparison map `Hom^L_X(x, y) ⟶ Hom_X(x, y)` induces a bijection on connected components. Both
sets of components are the morphisms from `x` to `y` in the homotopy category of `X`. -/
theorem bijective_mapπ₀_toMappingSpace [X.Quasicategory] :
    Function.Bijective (mapπ₀ (toMappingSpace x y)) := by
  -- Through the homotopy category, the comparison on components factors as the comparison
  -- `Hom^R_X(x, y) ⟶ Hom_X(x, y)` on components after a bijection.
  have h : mapπ₀ (toMappingSpace x y) = mapπ₀ (rightMappingSpace.toMappingSpace x y) ∘
      (rightMappingSpace.π₀Equiv x y).symm ∘ π₀Equiv x y := by
    funext c
    induction c with | mk s =>
    simp only [Function.comp_apply, π₀Equiv_mk, rightMappingSpace.π₀Equiv_symm_homMk, mapπ₀_mk]
    exact congrArg π₀.mk (mappingSpace.obj₀Equiv.injective (by simp))
  rw [h]
  exact (rightMappingSpace.bijective_mapπ₀_toMappingSpace x y).comp
    ((rightMappingSpace.π₀Equiv x y).symm.bijective.comp (π₀Equiv x y).bijective)

end leftMappingSpace

end SSet
