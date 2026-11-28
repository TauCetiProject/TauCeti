/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Contraction
public import TauCeti.AlgebraicTopology.Quasicategory.Slice
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

The comparison `Hom^L_X(x, y) ⟶ Hom_X(x, y)` with the two-sided mapping space
(`SSet.leftMappingSpace.toMappingSpace`) is constructed in
`TauCeti.AlgebraicTopology.Quasicategory.MappingSpace`, beside the comparison for the right mapping
space.

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

## Main results

* `SSet.leftMappingSpace.kanComplex`: the left mapping spaces of a quasicategory are Kan
  complexes.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 (the left mapping space `Hom^L_S(x, y)`, the opposite
  of `Hom^R_{Sᵒᵖ}(y, x)`).
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

/-- The last `n + 1` vertices of an `n`-simplex of `Hom^L_X(x, y)`, an `(n + 1)`-simplex of `X`,
are `y`. -/
@[simp]
theorem map_const_succ {n : ℕ} (s : (X.leftMappingSpace x y : SSet.{u}) _⦋n⦌) (j : Fin (n + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ j.succ).op (s.val : X _⦋n + 1⦌) = y :=
  map_const_succ_of_δ_zero ((mem_leftMappingSpace_iff _).1 s.property).2 j

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

open MonoidalCategory CartesianMonoidalCategory

variable (x)

variable (X) in
/-- The simplices of `vertexJoin.op ⋙ X` with initial vertex `x`. -/
def coneSpace (x : X _⦋0⦌) : Subcomplex (vertexJoin.op ⋙ X) where
  obj m := {σ | X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj m.unop) 0).op σ = x}
  map {m m'} f σ hσ := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    have h := congrArg (fun g ↦ X.map g.op σ) (const_zero_comp_vertexJoin_map (x := ⦋0⦌) f.unop)
    exact (Functor.map_comp_apply X _ _ σ).symm.trans (h.trans hσ)

/-- Membership in the cone model says that its distinguished vertex is `x`. -/
@[simp]
lemma mem_coneSpace_obj_iff {m : SimplexCategoryᵒᵖ} (σ : (vertexJoin.op ⋙ X).obj m) :
    σ ∈ (coneSpace X x).obj m ↔
      X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj m.unop) 0).op σ = x :=
  Iff.rfl

variable (X) in
/-- The restriction of a simplex of `vertexJoin.op ⋙ X` to the face opposite to the initial
vertex. -/
private def base : (vertexJoin.op ⋙ X) ⟶ X where
  app m := X.map (SimplexCategory.δ (n := m.unop.len) 0).op
  naturality m m' f := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext σ
    have h := congrArg (fun g ↦ X.map g.op σ) (δ_zero_comp_vertexJoin_map f.unop)
    exact (Functor.map_comp_apply X _ _ σ).symm.trans (h.trans (Functor.map_comp_apply X _ _ σ))

variable (X) in
/-- The projection `(coneSpace X x) ⟶ X`: the restriction to the face opposite to the initial
vertex. -/
noncomputable def coneπ : (coneSpace X x : SSet.{u}) ⟶ X := (coneSpace X x).ι ≫ base X

/-- The projection from the cone model restricts the underlying simplex to its base face. -/
@[simp]
lemma coneπ_app {m : SimplexCategoryᵒᵖ} (s : (coneSpace X x : SSet.{u}).obj m) :
    dsimp% (coneπ X x).app m s = X.map (SimplexCategory.δ (n := m.unop.len) 0).op s.val :=
  (rfl)

/-- The `n`-simplices of the coslice `X_{x/}` are those of `coneSpace X x`, through
`Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
private noncomputable def cosliceEquiv (n : ℕ) :
    (coslice (yonedaEquiv.symm x)) _⦋n⦌ ≃ (coneSpace X x : SSet.{u}) _⦋n⦌ where
  toFun s := ⟨(yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s).val) : X _⦋n + 1⦌), by
    -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op _ = x
    rw [yonedaEquiv_naturality, join.const_zero_comp_coneIso_inv_assoc,
      (coslice.objEquiv s).property, Equiv.apply_symm_apply]⟩
  invFun t := coslice.objEquiv.symm
      ⟨(join.coneIso n).hom ≫ yonedaEquiv.symm (t.val : X _⦋n + 1⦌),
        (join.inl_comp_coneIso_hom_assoc _).trans
          ((yonedaEquiv_symm_naturality_left (X := X) (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0)
            (t.val : X _⦋n + 1⦌)).trans (congrArg yonedaEquiv.symm t.property))⟩
  left_inv s := coslice.objEquiv.injective (Subtype.ext (by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]))
  right_inv t := Subtype.ext (by
    simp only [Equiv.apply_symm_apply, Iso.inv_hom_id_assoc]
    exact yonedaEquiv.apply_symm_apply _)

/-- The coslice `X_{x/}` is isomorphic to `coneSpace X x`. -/
noncomputable def cosliceIso : coslice (yonedaEquiv.symm x) ≅ (coneSpace X x : SSet.{u}) :=
  NatIso.ofComponents (fun m ↦ (cosliceEquiv x m.unop.len).toIso) (fun {m m'} f ↦ by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext s : 3
    refine Subtype.ext ?_
    have key : (yonedaEquiv ((join.coneIso b).inv ≫
        (coslice.objEquiv ((coslice (yonedaEquiv.symm x)).map f s)).val) : X _⦋b + 1⦌) =
        X.map (vertexJoin.map f.unop).op
          (yonedaEquiv ((join.coneIso a).inv ≫ (coslice.objEquiv s).val)) := by
      rw [coslice.objEquiv_map_coe, yonedaEquiv_naturality]
      exact congrArg yonedaEquiv (join.vertexJoin_map_comp_coneIso_inv_assoc f.unop _).symm
    -- The subcomplex map acts by the ambient restriction map.
    exact key)

/-- The coslice isomorphism transports a simplex along `Δ[n + 1] ≅ Δ[0] ⋆ Δ[n]`. -/
@[simp]
lemma cosliceIso_hom_app_val {n : ℕ} (s : (coslice (yonedaEquiv.symm x)) _⦋n⦌) :
    dsimp% ((cosliceIso x).hom.app _ s).val =
      (yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s).val) : X _⦋n + 1⦌) :=
  (rfl)

/-- The inverse coslice isomorphism transports a cone simplex along `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
@[simp]
lemma cosliceIso_inv_app_val {n : ℕ} (s : (coneSpace X x : SSet.{u}) _⦋n⦌) :
    dsimp% (coslice.objEquiv ((cosliceIso x).inv.app _ s)).val =
      (join.coneIso n).hom ≫ yonedaEquiv.symm (s.val : X _⦋n + 1⦌) :=
  congrArg Subtype.val (coslice.objEquiv.apply_symm_apply _)

/-- The coslice isomorphism commutes with the projections to `X`. -/
@[reassoc]
lemma cosliceIso_hom_coneπ : (cosliceIso x).hom ≫ coneπ X x = coslice.π _ := by
  ext ⟨⟨n⟩⟩ s
  -- State the evaluated composite in applied form.
  change (coneπ X x).app _ ((cosliceIso x).hom.app _ s) = (coslice.π _).app _ s
  rw [coneπ_app, cosliceIso_hom_app_val, coslice.π_app, yonedaEquiv_naturality]
  exact congrArg yonedaEquiv (join.δ_zero_comp_coneIso_inv_assoc _)

/-- The contraction maps the simplices with initial vertex `x` to simplices with initial
vertex `x`. -/
noncomputable def coneContraction :
    (coneSpace X x : SSet.{u}) ⊗ Δ[1] ⟶ (coneSpace X x : SSet.{u}) :=
  Subcomplex.lift ((coneSpace X x).ι ▷ Δ[1] ≫ vertexJoinContraction X) (by
    rintro ⟨⟨n⟩⟩ _ ⟨⟨⟨σ, hσ⟩, e⟩, rfl⟩
    rw [mem_coneSpace_obj_iff]
    -- Whiskering the inclusion applies it to the first coordinate; expose that pair so the
    -- contraction evaluation lemma applies without unfolding the contraction.
    change X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0).op
      ((vertexJoinContraction X).app _ (σ, e)) = x
    calc
      _ = X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0).op
          (X.map (vertexJoinCollapse (stdSimplex.objEquiv e)).op σ) :=
        congrArg _ (vertexJoinContraction_app_apply (X := X) (n := n) (σ, e))
      _ = x := by
        have h₁ := congrArg (fun g ↦ X.map (Quiver.Hom.op g) σ)
          (const_zero_comp_vertexJoinCollapse (stdSimplex.objEquiv e))
        exact (Functor.map_comp_apply X _ _ σ).symm.trans
          (h₁.trans ((mem_coneSpace_obj_iff x σ).1 hσ)))

/-- Evaluation of the pointed cone contraction. -/
@[simp]
lemma coneContraction_app_val {n : ℕ}
    (z : ((coneSpace X x : SSet.{u}) ⊗ Δ[1]).obj (op ⦋n⦌)) :
    dsimp% ((coneContraction x).app _ z).val =
      X.map (vertexJoinCollapse (stdSimplex.objEquiv z.2)).op z.1.val :=
  vertexJoinContraction_app_apply (X := X) (n := n) (z.1.val, z.2)

/-- The pointed cone contraction is the restriction of the join contraction. -/
@[reassoc]
lemma coneContraction_ι :
    coneContraction x ≫ (coneSpace X x).ι = (coneSpace X x).ι ▷ Δ[1] ≫ vertexJoinContraction X :=
  (rfl)

/-- The final endpoint of the pointed cone contraction. -/
@[reassoc (attr := simp)]
lemma ι₁_coneContraction : ι₁ ≫ coneContraction x = 𝟙 _ := by
  rw [← cancel_mono (coneSpace X x).ι, Category.assoc, coneContraction_ι, ι₁_comp_assoc,
    ι₁_vertexJoinContraction, Category.comp_id, Category.id_comp]

/-- The initial vertex `x`, as the vertex of `vertexJoin.op ⋙ X` given by the identity edge of
`x`. -/
noncomputable def coneVertex : (coneSpace X x : SSet.{u}) _⦋0⦌ :=
  ⟨X.map (SimplexCategory.const (vertexJoin.obj ⦋0⦌) ⦋0⦌ 0).op x, by
    rw [mem_coneSpace_obj_iff, map_map_const_zero, SimplexCategory.const_eq_id,
      op_id, CategoryTheory.Functor.map_id, types_id_apply]⟩

/-- The distinguished cone vertex is the degenerate edge. -/
@[simp]
lemma coneVertex_val :
    (coneVertex x).val = X.map (SimplexCategory.const (vertexJoin.obj ⦋0⦌) ⦋0⦌ 0).op x :=
  (rfl)

/-- A constant family at the distinguished cone vertex consists of degenerate simplices. -/
lemma const_coneVertex_app_val {Z : SSet.{u}} {n : ℕ} (z : Z _⦋n⦌) :
    dsimp% ((SSet.const (coneVertex x)).app _ z).val =
      X.map (SimplexCategory.const (vertexJoin.obj ⦋n⦌) ⦋0⦌ 0).op x := by
  simp only [const_app, Subfunctor.toFunctor_map, Functor.comp_map, Functor.op_map,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, coneVertex_val]
  exact map_map_const_zero X _ x

/-- The initial endpoint of the pointed cone contraction. -/
@[reassoc (attr := simp)]
lemma ι₀_coneContraction : ι₀ ≫ coneContraction x = SSet.const (coneVertex x) := by
  apply NatTrans.ext
  funext ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  -- Record the cylinder endpoint as a product before using the normalized evaluation API.
  let z : (coneSpace X x : SSet.{u}) _⦋n⦌ × Δ[1] _⦋n⦌ := ι₀.app _ s
  have hz : z.1 = s := ι₀_app_fst s
  have he : stdSimplex.objEquiv z.2 = SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
    ext i : 3
    exact ι₀_app_snd_apply s i
  refine (coneContraction_app_val x (n := n) z).trans ?_
  rw [he, hz, const_coneVertex_app_val, vertexJoinCollapse_const_zero,
    op_comp, Functor.map_comp_apply]
  exact congrArg _ ((mem_coneSpace_obj_iff x s.val).1 s.property)

/-- The cone projection inherits the left fibration structure of the coslice. -/
instance leftFibration_coneπ [X.Quasicategory] : LeftFibration (coneπ X x) := by
  rw [← Iso.inv_hom_id_assoc (cosliceIso x) (coneπ X x), cosliceIso_hom_coneπ]
  infer_instance

/-- Contracting the constant family at the identity of `x` gives the constant family. -/
@[reassoc]
lemma lift_const_coneVertex_coneContraction {Z : SSet.{u}} (f : Z ⟶ Δ[1]) :
    lift (SSet.const (coneVertex x)) f ≫ coneContraction x = SSet.const (coneVertex x) := by
  ext ⟨⟨n⟩⟩ z : 4
  apply Subtype.ext
  -- Evaluate the pairing before applying the component formula for the contraction.
  change ((coneContraction x).app _ ((SSet.const (coneVertex x)).app _ z, f.app _ z)).val =
    ((SSet.const (coneVertex x)).app _ z).val
  refine (coneContraction_app_val x (n := n)
    ((SSet.const (coneVertex x)).app _ z, f.app _ z)).trans ?_
  rw [const_coneVertex_app_val, map_map_const_zero]

/-- **The contraction forgets the part of a family which is collapsed.** For a family `G` of
simplices of `coneSpace X x` parametrized by `Z ⊗ Δ[1]`, contracting `G (z, e)` along `e`, or the
value `G (z, 1)` at the end of the path, gives the same result. -/
@[reassoc]
lemma lift_snd_coneContraction {Z : SSet.{u}} (G : Z ⊗ Δ[1] ⟶ (coneSpace X x : SSet.{u})) :
    lift G (snd _ _) ≫ coneContraction x =
      lift (fst _ _ ≫ ι₁ ≫ G) (snd _ _) ≫ coneContraction x := by
  ext ⟨⟨n⟩⟩ ⟨z, e⟩ : 4
  apply Subtype.ext
  -- Evaluate the products and compositions; the contraction itself is rewritten by its API.
  change ((coneContraction x).app _ (G.app _ (z, e), e)).val =
    ((coneContraction x).app _ (G.app _ (ι₁.app _ z), e)).val
  obtain ⟨k, rfl⟩ := stdSimplex.objMk₁_surjective e
  induction k using Fin.lastCases with
  | last =>
    have he (s : (coneSpace X x : SSet.{u}) _⦋n⦌) :
        (s, stdSimplex.objMk₁.{u} (Fin.last (n + 1))) = ι₀.app _ s := by
      refine Prod.ext (α := (coneSpace X x : SSet.{u}) _⦋n⦌) (β := Δ[1] _⦋n⦌)
        (ι₀_app_fst s).symm ?_
      apply stdSimplex.objEquiv.injective
      refine (stdSimplex.objEquiv_objMk₁_last n).trans ?_
      ext i : 3
      exact (ι₀_app_snd_apply s i).symm
    have hc (s : (coneSpace X x : SSet.{u}) _⦋n⦌) :
        ((coneContraction x).app _ (s, stdSimplex.objMk₁.{u} (Fin.last (n + 1)))).val =
          X.map (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0).op x := by
      have h := congrArg (fun f ↦ (f.app (op ⦋n⦌) s).val) (ι₀_coneContraction x)
      exact (congrArg (fun t ↦ ((coneContraction x).app _ t).val) (he s)).trans
        (h.trans (const_coneVertex_app_val x s))
    exact (hc _).trans (hc _).symm
  | cast j =>
    refine (coneContraction_app_val x (n := n)
      (G.app _ (z, stdSimplex.objMk₁ _), stdSimplex.objMk₁ _)).trans
        (Eq.trans ?_ (coneContraction_app_val x (n := n)
          (G.app _ (ι₁.app _ z), stdSimplex.objMk₁ _)).symm)
    rw [← stdSimplex.vertexJoinCollapse_comp_vertexJoin_map_maxRetraction j, op_comp,
      Functor.map_comp_apply,
      Functor.map_comp_apply]
    congr 1
    have h₁ := congrArg Subtype.val (NatTrans.naturality_apply G (maxRetraction j).op
      (show (Z ⊗ Δ[1] : SSet.{u}) _⦋n⦌ from (z, stdSimplex.objMk₁ j.castSucc)))
    have h₂ := congrArg Subtype.val (NatTrans.naturality_apply G (maxRetraction j).op (ι₁.app _ z))
    refine h₁.symm.trans (Eq.trans ?_ h₂)
    congr 2
    refine Prod.ext rfl (stdSimplex.objEquiv.injective
      ((stdSimplex.maxRetraction_comp_objMk₁.{u} j).trans ?_))
    ext i : 3
    simp only [stdSimplex.objEquiv_toOrderHom_apply, SimplexCategory.const_apply]
    -- Restriction of a constant interval simplex is still constant.
    exact ((congrArg (fun e : Δ[1] _⦋n⦌ ↦ e i)
      (SSet.prod_map_snd Z Δ[1] (maxRetraction j).op (ι₁.app _ z))).trans
        (SSet.ι₁_app_snd_apply z _)).symm

variable {x}

/-- The distinguished cone point projects to its defining vertex. -/
@[reassoc]
lemma const_coneVertex_coneπ {Z : SSet.{u}} : SSet.const (coneVertex x) ≫ coneπ X x =
    (SSet.const x : Z ⟶ X) := by
  rw [const_comp, coneπ_app, coneVertex_val]
  congr 1
  exact (map_map_const_zero X (SimplexCategory.δ (n := 0) 0) x).trans (by simp)

variable (x y) in
private lemma leftMappingSpace_le_coneSpace : X.leftMappingSpace x y ≤ coneSpace X x := by
  rintro ⟨⟨n⟩⟩ σ hσ
  exact (mem_coneSpace_obj_iff x σ).2 ((mem_leftMappingSpace_iff σ).1 hσ).1

variable (x y) in
/-- The inclusion of `Hom^L_X(x, y)` into `coneSpace X x`. -/
noncomputable def toConeSpace :
    (X.leftMappingSpace x y : SSet.{u}) ⟶ (coneSpace X x : SSet.{u}) :=
  Subcomplex.homOfLE (leftMappingSpace_le_coneSpace x y)

/-- Inclusion into the cone model preserves the underlying simplex. -/
@[simp]
lemma toConeSpace_app_val {m : SimplexCategoryᵒᵖ}
    (s : (X.leftMappingSpace x y : SSet.{u}).obj m) :
    dsimp% ((toConeSpace x y).app m s).val = s.val :=
  (rfl)

/-- The inclusion of a mapping space into its cone model is a monomorphism. -/
instance mono_toConeSpace : Mono (toConeSpace x y) :=
  inferInstanceAs (Mono (Subcomplex.homOfLE (leftMappingSpace_le_coneSpace x y)))

/-- The mapping space inclusion lies over its fixed endpoint. -/
@[reassoc]
lemma toConeSpace_coneπ : toConeSpace x y ≫ coneπ X x = SSet.const y := by
  ext ⟨⟨n⟩⟩ s
  dsimp only [TypeCat.Fun.toFun_apply]
  rw [NatTrans.comp_app_apply, coneπ_app]
  exact ((mem_leftMappingSpace_iff (s.val : X _⦋n + 1⦌)).1 s.property).2

variable (x y)

/-- The fibre of the cone projection is the left mapping space. -/
noncomputable def coneFiberIso :
    (fiber (coneπ X x) y : SSet.{u}) ≅ (X.leftMappingSpace x y : SSet.{u}) where
  hom := Subcomplex.lift ((fiber (coneπ X x) y).ι ≫ (coneSpace X x).ι) (by
    rintro ⟨⟨n⟩⟩ _ ⟨s, rfl⟩
    have hs := (mem_fiber_iff _ _ _).1 s.property
    rw [coneπ_app] at hs
    exact (mem_leftMappingSpace_iff _).2
      ⟨s.val.property, hs⟩)
  inv := fiber.lift (toConeSpace x y) (coneπ X x) y toConeSpace_coneπ
  -- Both maps only package the same underlying simplex in the fibre and mapping subtypes.
  hom_inv_id := by
    rw [← cancel_mono (fiber (coneπ X x) y).ι, Category.assoc, fiber.lift_ι,
      Category.id_comp, ← cancel_mono (coneSpace X x).ι, Category.assoc,
      toConeSpace, Subcomplex.homOfLE_ι, Subcomplex.lift_ι]
  inv_hom_id := by
    rw [← cancel_mono (X.leftMappingSpace x y).ι, Category.assoc, Subcomplex.lift_ι,
      ← Category.assoc, fiber.lift_ι, toConeSpace, Subcomplex.homOfLE_ι, Category.id_comp]

/-- The cone fibre isomorphism commutes with the inclusions into the cone model. -/
@[reassoc (attr := simp)]
lemma coneFiberIso_hom_toConeSpace :
    (coneFiberIso x y).hom ≫ toConeSpace x y = (fiber (coneπ X x) y).ι := by
  -- The two maps forget the same subtype membership proofs.
  ext m s
  rfl

/-- The inverse cone fibre isomorphism commutes with the inclusions. -/
@[reassoc (attr := simp)]
lemma coneFiberIso_inv_ι :
    (coneFiberIso x y).inv ≫ (fiber (coneπ X x) y).ι = toConeSpace x y :=
  fiber.lift_ι _ _ _ _

/-- **The left mapping space `Hom^L_X(x, y)` is the fibre over `y` of the projection
`X_{x/} ⟶ X`** of the coslice under `x`. Through `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`, an `n`-simplex
`Δ[0] ⋆ Δ[n] ⟶ X` of the coslice is an `(n + 1)`-simplex of `X` with initial vertex `x`, and it lies
over `y` exactly when its face opposite to the initial vertex is constant at `y`. -/
noncomputable def cosliceFiberIso :
    (fiber (coslice.π (yonedaEquiv.symm x)) y : SSet.{u}) ≅ (X.leftMappingSpace x y : SSet.{u}) :=
  fiber.mapIso (cosliceIso x) (cosliceIso_hom_coneπ _) y ≪≫ coneFiberIso x y

/-- The simplex of `Hom^L_X(x, y)` attached to a simplex `Δ[0] ⋆ Δ[n] ⟶ X` of the fibre of
`X_{x/} ⟶ X` is its composite with `Δ[n + 1] ≅ Δ[0] ⋆ Δ[n]`. -/
@[simp]
theorem cosliceFiberIso_hom_app_coe {n : ℕ}
    (s : (fiber (coslice.π (yonedaEquiv.symm x)) y : SSet.{u}) _⦋n⦌) :
    dsimp% ((cosliceFiberIso x y).hom.app _ s).val =
      (yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s.val).val) : X _⦋n + 1⦌) :=
by
  have h : (cosliceFiberIso x y).hom ≫ toConeSpace x y =
      (fiber (coslice.π (yonedaEquiv.symm x)) y).ι ≫ (cosliceIso x).hom := by
    simp only [cosliceFiberIso, Iso.trans_hom, Category.assoc,
      coneFiberIso_hom_toConeSpace, fiber.mapIso_hom, fiber.map_ι]
  exact (congrArg (fun f ↦ (f.app _ s).val) h).trans (cosliceIso_hom_app_val x s.val)

/-- The simplex `Δ[0] ⋆ Δ[n] ⟶ X` of the fibre of `X_{x/} ⟶ X` attached to a simplex of
`Hom^L_X(x, y)` is its composite with `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
@[simp]
theorem cosliceFiberIso_inv_app_coe {n : ℕ} (t : (X.leftMappingSpace x y : SSet.{u}) _⦋n⦌) :
    dsimp% (coslice.objEquiv ((cosliceFiberIso x y).inv.app _ t).val).val =
      (join.coneIso n).hom ≫ yonedaEquiv.symm (t.val : X _⦋n + 1⦌) :=
by
  have h : (cosliceFiberIso x y).inv ≫ (fiber (coslice.π (yonedaEquiv.symm x)) y).ι =
      toConeSpace x y ≫ (cosliceIso x).inv := by
    simp only [cosliceFiberIso, Iso.trans_inv, Category.assoc,
      fiber.mapIso_inv, fiber.map_ι, coneFiberIso_inv_ι_assoc]
  exact (congrArg (fun f ↦ (coslice.objEquiv (f.app _ t)).val) h).trans
    (cosliceIso_inv_app_val x ((toConeSpace x y).app _ t))

end cosliceFiber

end leftMappingSpace

end SSet
