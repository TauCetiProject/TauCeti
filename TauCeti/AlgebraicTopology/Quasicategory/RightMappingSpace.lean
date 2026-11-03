/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
public import TauCeti.AlgebraicTopology.SimplexCategory.JoinVertex
public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import TauCeti.AlgebraicTopology.SimplicialSet.Vertex

/-!
# Right mapping spaces of simplicial sets

For vertices `x` and `y` of a simplicial set `X`, the right mapping space `Hom^R_X(x, y)` is the
simplicial set whose `n`-simplices are the `(n + 1)`-simplices of `X` with last vertex `y` whose
face spanned by the first `n + 1` vertices is the constant simplex at `x`. Its vertices are the
edges from `x` to `y`. It is the fibre over `x` of the projection `X_{/y} ⟶ X` from the slice over
`y`, and it models the space of maps from `x` to `y` when `X` is a quasicategory.

We realise it as a subcomplex of `SimplexCategory.joinVertex.op ⋙ X`, the simplicial set whose
`n`-simplices are the `(n + 1)`-simplices of `X`, with simplicial operators acting on the first
`n + 1` vertices and fixing the last one. Here `SimplexCategory.joinVertex` is the join
`- ⋆ ⦋0⦌` with a final vertex, the restriction to `SimplexCategory` of the join of
`AugmentedSimplexCategory` (see `TauCeti.AlgebraicTopology.SimplexCategory.JoinVertex`).

If `X` is a quasicategory, every horn `Λ[n, i]` with `0 < i` in `Hom^R_X(x, y)` has a filler: in
`X` it is an inner horn `Λ[n + 1, i]` whose last face is the constant simplex at `x`. Thus
`Hom^R_X(x, y)` is again a quasicategory, in which all horns except possibly the ones `Λ[n, 0]`
can be filled. (That the remaining horns can also be filled, making `Hom^R_X(x, y)` a Kan complex,
is Joyal's theorem on special outer horns, which this file does not prove.)

If `X` is strict Segal, for instance the nerve of a category, then every simplex of
`Hom^R_X(x, y)` is totally degenerate: its spine consists of degenerate edges at `x` followed by
a single edge to `y`. Hence `Hom^R_X(x, y)` is the discrete simplicial set on the edges from `x`
to `y`.

A map of simplicial sets `f : X ⟶ Y` induces maps `Hom^R_X(x, y) ⟶ Hom^R_Y(f x, f y)`, which are
the maps on mapping spaces whose invertibility up to weak equivalence makes `f` fully faithful.
The projections of a product identify the right mapping spaces of `X ⊗ Y` with the products of
those of `X` and `Y`.

## Main definitions

* `SSet.rightMappingSpace X x y`: the right mapping space `Hom^R_X(x, y)`.
* `SSet.rightMappingSpace.obj₀Equiv`: its vertices are the edges from `x` to `y`.
* `SSet.rightMappingSpace.constEdgeIso`: for a strict Segal simplicial set, `Hom^R_X(x, y)` is
  the discrete simplicial set on the edges from `x` to `y`.
* `SSet.rightMappingSpace.map x y f`: the map `Hom^R_X(x, y) ⟶ Hom^R_Y(f x, f y)` induced by
  `f : X ⟶ Y`.
* `SSet.rightMappingSpace.prodIso`: the isomorphism
  `Hom^R_{X ⊗ Y}((x₀, y₀), (x₁, y₁)) ≅ Hom^R_X(x₀, x₁) ⊗ Hom^R_Y(y₀, y₁)`.

## Main results

* `SSet.mem_rightMappingSpace_iff`: the description of the simplices of `Hom^R_X(x, y)`, and
  `SSet.rightMappingSpace.coe_δ`, `SSet.rightMappingSpace.coe_σ`: their faces and degeneracies
  are those in `X` avoiding, respectively fixing, the last vertex.
* `SSet.rightMappingSpace.hornFilling`: if `X` is a quasicategory, the horns `Λ[n, i]` with
  `i ≠ 0` in `Hom^R_X(x, y)` have fillers.
* `SSet.rightMappingSpace.quasicategory`: the right mapping spaces of a quasicategory are
  quasicategories.
* `SSet.rightMappingSpace.isIso_map_iff_bijective`: for strict Segal simplicial sets, `f` induces
  an isomorphism of right mapping spaces exactly when it is bijective on edges.
* `SSet.rightMappingSpace.isIso_map_ι`: a subcomplex containing all simplices of a right mapping
  space has the same right mapping space.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 (the right mapping space `Hom^R_S(x, y)`) and
  Proposition 1.2.2.3.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

open SimplexCategory

variable (X : SSet.{u})

/-- Pulling back a totally degenerate simplex along a simplicial operator gives the totally
degenerate simplex at the same vertex. -/
@[simp]
theorem map_map_const_zero {m m' : SimplexCategory} (f : m' ⟶ m) (x : X _⦋0⦌) :
    X.map f.op (X.map (SimplexCategory.const m ⦋0⦌ 0).op x) =
      X.map (SimplexCategory.const m' ⦋0⦌ 0).op x := by
  rw [← Functor.map_comp_apply, ← op_comp, Subsingleton.elim (f ≫ _)]

/-- The right mapping space `Hom^R_X(x, y)` between vertices `x` and `y` of a simplicial set `X`.
It is the subcomplex of `joinVertex.op ⋙ X` whose `n`-simplices are the `(n + 1)`-simplices of
`X` with last vertex `y` whose face opposite to the last vertex is the constant simplex at `x`.
Equivalently, it is the fibre over `x` of the projection to `X` of the slice `X_{/y}`. -/
def rightMappingSpace (x y : X _⦋0⦌) : Subcomplex (joinVertex.op ⋙ X) where
  obj m := {σ | X.map (joinVertexInl m.unop).op σ =
      X.map (SimplexCategory.const m.unop ⦋0⦌ 0).op x ∧ X.map (joinVertexInr m.unop).op σ = y}
  map {m m'} f σ hσ := by
    -- `f` acts on `joinVertex.op ⋙ X` as `joinVertex.map f.unop` acts on `X`.
    refine ⟨?_, ?_⟩
    · have h := congrArg (fun g ↦ X.map g.op σ) (joinVertexInl_comp_joinVertex_map f.unop)
      simp only [op_comp, Functor.map_comp_apply, hσ.1, map_map_const_zero] at h
      exact h
    · have h := congrArg (fun g ↦ X.map g.op σ) (joinVertexInr_comp_joinVertex_map f.unop)
      simp only [op_comp, Functor.map_comp_apply, hσ.2] at h
      exact h

variable {X} {x y : X _⦋0⦌}

/-- An `(n + 1)`-simplex of `X` is an `n`-simplex of `Hom^R_X(x, y)` exactly when its face
opposite to the last vertex is the constant simplex at `x` and its last vertex is `y`. -/
theorem mem_rightMappingSpace_iff {n : ℕ} (σ : X _⦋n + 1⦌) :
    σ ∈ (X.rightMappingSpace x y).obj (op ⦋n⦌) ↔
      X.δ (Fin.last (n + 1)) σ = X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x ∧
        X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last _)).op σ = y := by
  simp only [rightMappingSpace, unop_op, joinVertexInl_mk, joinVertexInr_mk, SimplicialObject.δ]
  -- `σ` is an element of `(joinVertex.op ⋙ X) _⦋n⦌` only through the definitional equality of
  -- this type with `X _⦋n + 1⦌`, so `Set.mem_ofPred_eq` cannot be rewritten across the membership
  -- (its `Membership` instance does not typecheck at `X _⦋n + 1⦌`); membership in the unfolded
  -- set-builder set is the defining predicate, closed by `Iff.rfl`.
  exact Iff.rfl

namespace rightMappingSpace

/-- The vertices of the right mapping space `Hom^R_X(x, y)` are the edges from `x` to `y`. -/
def obj₀Equiv : (X.rightMappingSpace x y : SSet.{u}) _⦋0⦌ ≃ Edge x y where
  toFun σ := Edge.mk (σ.1 : X _⦋1⦌)
    (by simpa [const_eq_id] using ((mem_rightMappingSpace_iff (n := 0) _).1 σ.2).1)
    (by
      simpa [SimplicialObject.δ, SimplexCategory.δ_zero_eq_const] using
        ((mem_rightMappingSpace_iff (n := 0) _).1 σ.2).2)
  invFun e := ⟨e.edge, (mem_rightMappingSpace_iff (n := 0) _).2
    ⟨by simp [const_eq_id],
      by simpa [SimplicialObject.δ, SimplexCategory.δ_zero_eq_const] using e.tgt_eq⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The edge attached to a vertex of `Hom^R_X(x, y)` is that vertex, as a `1`-simplex of `X`. -/
theorem obj₀Equiv_apply_edge (σ : (X.rightMappingSpace x y : SSet.{u}) _⦋0⦌) :
    (obj₀Equiv σ).edge = σ.1 :=
  (rfl)

/-- The vertex of `Hom^R_X(x, y)` attached to an edge is that edge, as a `1`-simplex of `X`. -/
theorem obj₀Equiv_symm_apply_coe (e : Edge x y) :
    (obj₀Equiv.symm e).1 = e.edge :=
  (rfl)

/-- The `j`-th face of an `(n + 1)`-simplex of `Hom^R_X(x, y)` is the `j`-th face of the
corresponding `(n + 2)`-simplex of `X`. -/
theorem coe_δ {n : ℕ} (j : Fin (n + 2)) (s : (X.rightMappingSpace x y : SSet.{u}) _⦋n + 1⦌) :
    (SimplicialObject.δ (X.rightMappingSpace x y : SSet.{u}) j s).1 =
      X.δ j.castSucc (s.1 : X _⦋n + 2⦌) :=
  (ConcreteCategory.congr_hom (X.joinVertex_op_comp_δ j) s.1 :)

/-- The `j`-th degeneracy of an `n`-simplex of `Hom^R_X(x, y)` is the `j`-th degeneracy of the
corresponding `(n + 1)`-simplex of `X`. -/
theorem coe_σ {n : ℕ} (j : Fin (n + 1)) (s : (X.rightMappingSpace x y : SSet.{u}) _⦋n⦌) :
    (SimplicialObject.σ (X.rightMappingSpace x y : SSet.{u}) j s).1 =
      X.σ j.castSucc (s.1 : X _⦋n + 1⦌) :=
  (ConcreteCategory.congr_hom (X.joinVertex_op_comp_σ j) s.1 :)

/-- The first `n + 1` vertices of an `n`-simplex of `Hom^R_X(x, y)`, an `(n + 1)`-simplex of `X`,
are `x`. -/
theorem map_const_castSucc {n : ℕ} (s : (X.rightMappingSpace x y : SSet.{u}) _⦋n⦌)
    (j : Fin (n + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ j.castSucc).op (s.1 : X _⦋n + 1⦌) = x :=
  map_const_castSucc_of_δ_last ((mem_rightMappingSpace_iff _).1 s.2).1 j

/-- The last vertex of an `n`-simplex of `Hom^R_X(x, y)`, an `(n + 1)`-simplex of `X`, is `y`. -/
theorem map_const_last {n : ℕ} (s : (X.rightMappingSpace x y : SSet.{u}) _⦋n⦌) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last _)).op (s.1 : X _⦋n + 1⦌) = y :=
  ((mem_rightMappingSpace_iff _).1 s.2).2

/-! ### Horn filling -/

variable {n : ℕ} {i : Fin (n + 2)}

/-- The `j`-th face of a horn in `Hom^R_X(x, y)`, as a simplex of `joinVertex.op ⋙ X`. -/
private def hornFace
    (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u}))
    (j : Fin (n + 2)) (hj : j ≠ i) : (joinVertex.op ⋙ X) _⦋n⦌ :=
  (σ₀.app _ (horn.face i j hj)).1

private theorem hornFace_mem
    (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u}))
    (j : Fin (n + 2)) (hj : j ≠ i) :
    hornFace σ₀ j hj ∈ (X.rightMappingSpace x y).obj (op ⦋n⦌) :=
  (σ₀.app _ (horn.face i j hj)).2

/-- The faces of a horn in `Hom^R_X(x, y)` satisfy the compatibility of faces of a horn. -/
private theorem hornFace_δ {m : ℕ} {i : Fin (m + 3)}
    (σ₀ : (Λ[m + 2, i] : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u}))
    (j k : Fin (m + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k) :
    SimplicialObject.δ (joinVertex.op ⋙ X) (k.pred (Fin.ne_zero_of_lt hjk))
        (hornFace σ₀ j hj) =
      SimplicialObject.δ (joinVertex.op ⋙ X) (j.castPred (Fin.ne_last_of_lt hjk))
        (hornFace σ₀ k hk) := by
  have h := congrArg yonedaEquiv
    ((horn.IsCompatible.of_hom (σ₀ ≫ Subcomplex.ι _)).δ_pred_comp j k hj hk hjk)
  -- Evaluate each side at the faces of `Δ[m + 1]`, then restrict `σ₀` along `horn.ι` by evaluating
  -- it at the corresponding face of the horn.
  rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp, yonedaEquiv_comp,
    yonedaEquiv_comp, horn.yonedaEquiv_ι, horn.yonedaEquiv_ι] at h
  exact h

/-- The faces of the horn in `X` attached to a horn in `Hom^R_X(x, y)`: the faces of the given
horn, and the constant simplex at `x` as the face opposite to the last vertex. -/
private def liftFace
    (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u}))
    (k : Fin (n + 3)) (hk : k ≠ i.castSucc) : X _⦋n + 1⦌ :=
  if h : k = Fin.last _ then X.map (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0).op x
  else hornFace σ₀ (k.castPred h) (fun h' ↦ hk (by rw [← h', Fin.castSucc_castPred]))

private theorem liftFace_last
    (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u}))
    (hk : Fin.last (n + 2) ≠ i.castSucc) :
    liftFace σ₀ (Fin.last _) hk = X.map (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0).op x := by
  simp [liftFace]

private theorem liftFace_castSucc
    (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u}))
    (j : Fin (n + 2)) (hj : j ≠ i) (hk : j.castSucc ≠ i.castSucc) :
    liftFace σ₀ j.castSucc hk = hornFace σ₀ j hj := by
  simp only [liftFace, Fin.castSucc_ne_last, ↓reduceDIte]
  rfl

/-- The faces `liftFace σ₀` glue to an inner horn `Λ[n + 2, i.castSucc]` in `X`. -/
private theorem isCompatible_liftFace
    (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u})) :
    horn.IsCompatible (i := i.castSucc) (fun k hk ↦ yonedaEquiv.symm (liftFace σ₀ k hk)) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
  congr 1
  obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
  have hj' : j ≠ i := fun h ↦ hj (h ▸ rfl)
  rw [liftFace_castSucc σ₀ j hj']
  cases k using Fin.lastCases with
  | last =>
    -- The face of `σ₀` opposite to its last vertex is constant at `x`, as is any face of the
    -- constant simplex.
    rw [liftFace_last, Fin.pred_last,
      ((mem_rightMappingSpace_iff _).1 (hornFace_mem σ₀ j hj')).1, SimplicialObject.δ,
      map_map_const_zero]
  | cast k =>
    have hk' : k ≠ i := fun h ↦ hk (h ▸ rfl)
    rw [liftFace_castSucc σ₀ k hk']
    obtain _ | m := n
    · exfalso
      rw [Fin.castSucc_lt_castSucc_iff] at hjk
      omega
    · have h := (ConcreteCategory.congr_hom (X.joinVertex_op_comp_δ _) _).symm.trans
        ((hornFace_δ σ₀ j k hj' hk' (Fin.castSucc_lt_castSucc_iff.1 hjk)).trans
          (ConcreteCategory.congr_hom (X.joinVertex_op_comp_δ _) _))
      -- The indices agree definitionally: `(k.pred _).castSucc = k.castSucc.pred _` and
      -- `(j.castSucc.castPred _).castSucc = j.castSucc`.
      exact h

/-- If `X` is a quasicategory, every horn `Λ[n + 1, i]` with `i ≠ 0` in the right mapping space
`Hom^R_X(x, y)` can be filled. -/
theorem hornFilling [X.Quasicategory] (hi : i ≠ 0)
    (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u})) :
    ∃ σ : Δ[n + 1] ⟶ (X.rightMappingSpace x y : SSet.{u}), σ₀ = Λ[n + 1, i].ι ≫ σ := by
  -- Fill the inner horn of `X` whose faces are those of `σ₀` and the constant simplex at `x`.
  obtain ⟨τ, hτ⟩ := Quasicategory.hornFilling
    (Fin.castSucc_pos_iff.2 (Fin.pos_iff_ne_zero.2 hi)) (Fin.castSucc_lt_last i)
    (isCompatible_liftFace σ₀).desc
  set t : X _⦋n + 2⦌ := yonedaEquiv τ with ht
  have hface (k : Fin (n + 3)) (hk : k ≠ i.castSucc) :
      X.δ k t = liftFace σ₀ k hk := by
    simpa [ht, stdSimplex.yonedaEquiv_δ_comp] using
      (congrArg yonedaEquiv (horn.ι _ k hk ≫= hτ)).symm
  -- The filler is a simplex of the right mapping space.
  have hmem : t ∈ (X.rightMappingSpace x y).obj (op ⦋n + 1⦌) := by
    refine (mem_rightMappingSpace_iff _).2 ⟨?_, ?_⟩
    · rw [hface _ (Fin.castSucc_lt_last i).ne', liftFace_last]
    · -- The last vertex of the filler is the last vertex of its face opposite to `0`.
      have h0 : Fin.castSucc (0 : Fin (n + 2)) ≠ i.castSucc :=
        fun h ↦ hi (Fin.castSucc_injective _ h).symm
      have h := ((mem_rightMappingSpace_iff _).1 (hornFace_mem σ₀ 0 hi.symm)).2
      rw [← liftFace_castSucc σ₀ 0 hi.symm h0, ← hface _ h0, SimplicialObject.δ,
        ← Functor.map_comp_apply, ← op_comp] at h
      rw [← joinVertexInr_mk] at h ⊢
      exact (congrArg (fun g ↦ X.map g.op t) (joinVertexInr_comp_δ_castSucc 0)).symm.trans h
  let s : (X.rightMappingSpace x y : SSet.{u}) _⦋n + 1⦌ := ⟨t, hmem⟩
  refine ⟨yonedaEquiv.symm s, horn.hom_ext _ _ fun j hj ↦ Subtype.ext ?_⟩
  have hR : (Λ[n + 1, i].ι ≫ yonedaEquiv.symm s).app _ (horn.face i j hj) =
      SimplicialObject.δ (X.rightMappingSpace x y : SSet.{u}) j s := by
    -- Evaluating at the `j`-th face is restricting along `horn.ι`, i.e. along `stdSimplex.δ j`.
    rw [← horn.yonedaEquiv_ι, ← yonedaEquiv_comp, horn.ι_ι_assoc, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply]
  rw [hR, coe_δ, hface _ fun h ↦ hj (Fin.castSucc_injective _ h), liftFace_castSucc σ₀ j hj]
  rfl

/-- The right mapping spaces of a quasicategory are quasicategories. -/
instance quasicategory [X.Quasicategory] :
    (X.rightMappingSpace x y : SSet.{u}).Quasicategory where
  hornFilling' _ _ σ₀ h0 _ := hornFilling h0.ne' σ₀

/-! ### Strict Segal simplicial sets -/

section IsStrictSegal

/-- In the right mapping space of a strict Segal simplicial set, every simplex is the totally
degenerate simplex at its last vertex. -/
private theorem eq_map_const_of_isStrictSegal [X.IsStrictSegal] {n : ℕ}
    (s : (X.rightMappingSpace x y : SSet.{u}) _⦋n⦌) :
    s = (X.rightMappingSpace x y : SSet.{u}).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      ((X.rightMappingSpace x y : SSet.{u}).map
        (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op s) := by
  refine Subtype.ext ((map_eq_of_isStrictSegal (joinVertex.map
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)))
    mkOfSucc_last_comp_joinVertex_map mkOfSucc_castSucc_comp_joinVertex_map (s.1 : X _⦋n + 1⦌)
    ((mem_rightMappingSpace_iff _).1 s.2).1).symm.trans ?_)
  -- The simplicial operators of `Hom^R_X(x, y)` act on `X` through `joinVertex`.
  rw [Functor.map_comp]
  exact Functor.map_comp_apply X (joinVertex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))).op
    (joinVertex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op _

/-- The right mapping spaces of a strict Segal simplicial set, such as the nerve of a category,
are discrete: sending an edge from `x` to `y` to the totally degenerate simplices at the
corresponding vertex is an isomorphism from the discrete simplicial set on these edges. -/
instance isIso_constHomEquiv_symm [X.IsStrictSegal] :
    IsIso ((constHomEquiv (X.Edge x y)).symm (obj₀Equiv (x := x) (y := y)).symm) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  -- The comparison sends an edge to the totally degenerate simplex at the corresponding vertex.
  have happ (e : X.Edge x y) :
      ((constHomEquiv (X.Edge x y)).symm (obj₀Equiv (x := x) (y := y)).symm).app (op ⦋n⦌) e =
        (X.rightMappingSpace x y : SSet.{u}).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
          (obj₀Equiv.symm e) := by
    rw [← constHomEquiv_symm_app_zero (X.Edge x y) obj₀Equiv.symm e]
    exact (NatTrans.naturality_apply ((constHomEquiv (X.Edge x y)).symm obj₀Equiv.symm)
      (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (e : ((Functor.const SimplexCategoryᵒᵖ).obj (X.Edge x y)).obj (op ⦋0⦌)))
  refine ⟨fun e e' h ↦ ?_, fun s ↦ ⟨obj₀Equiv ((X.rightMappingSpace x y : SSet.{u}).map
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op s), ?_⟩⟩
  · -- The last vertex of the totally degenerate simplex at a vertex is that vertex.
    have h' := congrArg ((X.rightMappingSpace x y : SSet.{u}).map
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op) ((happ e).symm.trans (h.trans (happ e')))
    simp only [← Functor.map_comp_apply, ← op_comp, Subsingleton.elim
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n) ≫ SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) (𝟙 _),
      op_id] at h'
    exact obj₀Equiv.symm.injective (by simpa using h')
  · rw [happ, Equiv.symm_apply_apply]
    exact (eq_map_const_of_isStrictSegal s).symm

variable (x y) in
/-- The right mapping space `Hom^R_X(x, y)` of a strict Segal simplicial set, such as the nerve of
a category, is the discrete simplicial set on the edges from `x` to `y`. -/
noncomputable def constEdgeIso [X.IsStrictSegal] :
    (Functor.const SimplexCategoryᵒᵖ).obj (X.Edge x y) ≅ (X.rightMappingSpace x y : SSet.{u}) :=
  asIso ((constHomEquiv (X.Edge x y)).symm obj₀Equiv.symm)

/-- On vertices, the discreteness isomorphism sends an edge to the corresponding vertex of
`Hom^R_X(x, y)`. -/
@[simp]
theorem constEdgeIso_hom_app_zero [X.IsStrictSegal] (e : X.Edge x y) :
    dsimp% (constEdgeIso x y).hom.app (op ⦋0⦌) e = obj₀Equiv.symm e :=
  constHomEquiv_symm_app_zero (X.Edge x y) obj₀Equiv.symm e

/-- On vertices, the inverse of the discreteness isomorphism sends a vertex of `Hom^R_X(x, y)` to
the corresponding edge. -/
@[simp]
theorem constEdgeIso_inv_app_zero [X.IsStrictSegal]
    (s : (X.rightMappingSpace x y : SSet.{u}) _⦋0⦌) :
    dsimp% (constEdgeIso x y).inv.app (op ⦋0⦌) s = obj₀Equiv s := by
  apply obj₀Equiv.symm.injective
  rw [Equiv.symm_apply_apply, ← constEdgeIso_hom_app_zero]
  simp

end IsStrictSegal

/-! ### Functoriality -/

section map

variable {Y Z : SSet.{u}}

/-- A map of simplicial sets `f : X ⟶ Y` sends the simplices of `Hom^R_X(x, y)` to simplices of
`Hom^R_Y(f x, f y)`. -/
private theorem range_le_rightMappingSpace (f : X ⟶ Y) (x y : X _⦋0⦌) :
    Subcomplex.range ((X.rightMappingSpace x y).ι ≫ Functor.whiskerLeft joinVertex.op f) ≤
      Y.rightMappingSpace (f.app _ x) (f.app _ y) := by
  rintro m _ ⟨s, rfl⟩
  -- The faces of `f σ` are the images under `f` of the faces of `σ`, by naturality of `f`.
  exact ⟨(NatTrans.naturality_apply f _ s.1).symm.trans
      ((congrArg (f.app _) s.2.1).trans (NatTrans.naturality_apply f _ x)),
    (NatTrans.naturality_apply f _ s.1).symm.trans (congrArg (f.app _) s.2.2)⟩

variable (x y) in
/-- The map `Hom^R_X(x, y) ⟶ Hom^R_Y(f x, f y)` induced by a map of simplicial sets
`f : X ⟶ Y`: it sends an `n`-simplex of `Hom^R_X(x, y)`, an `(n + 1)`-simplex of `X`, to its image
under `f`. -/
def map (f : X ⟶ Y) :
    (X.rightMappingSpace x y : SSet.{u}) ⟶
      (Y.rightMappingSpace (f.app _ x) (f.app _ y) : SSet.{u}) :=
  Subcomplex.lift _ (range_le_rightMappingSpace f x y)

variable (x y) in
/-- The map induced on right mapping spaces is the restriction of the map induced by `f` on
`joinVertex.op ⋙ X`. -/
@[reassoc (attr := simp)]
theorem map_ι (f : X ⟶ Y) :
    map x y f ≫ (Y.rightMappingSpace (f.app _ x) (f.app _ y)).ι =
      (X.rightMappingSpace x y).ι ≫ Functor.whiskerLeft joinVertex.op f :=
  (rfl)

/-- The map induced on right mapping spaces sends an `(n + 1)`-simplex of `X` to its image under
`f`. -/
@[simp]
theorem map_app_coe (f : X ⟶ Y) {n : ℕ} (s : (X.rightMappingSpace x y : SSet.{u}) _⦋n⦌) :
    dsimp% ((map x y f).app _ s).1 = f.app _ (s.1 : X _⦋n + 1⦌) :=
  (rfl)

variable (x y) in
/-- The identity induces the identity of right mapping spaces. -/
@[simp]
theorem map_id : map x y (𝟙 X) = 𝟙 _ :=
  (rfl)

variable (x y) in
/-- The maps induced on right mapping spaces are compatible with composition. -/
@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    map x y (f ≫ g) = map x y f ≫ map (f.app _ x) (f.app _ y) g :=
  (rfl)

/-- On vertices, the map induced on right mapping spaces is the map of edges induced by `f`. -/
@[simp]
theorem obj₀Equiv_map_app (f : X ⟶ Y) (s : (X.rightMappingSpace x y : SSet.{u}) _⦋0⦌) :
    dsimp% obj₀Equiv ((map x y f).app _ s) = (obj₀Equiv s).map f :=
  Edge.ext (rfl)

/-- Under the discreteness isomorphisms `constEdgeIso` of strict Segal simplicial sets, the map
induced by `f` on right mapping spaces is the map of discrete simplicial sets induced by the map of
edges. -/
@[reassoc]
theorem constEdgeIso_hom_comp_map [X.IsStrictSegal] [Y.IsStrictSegal] (f : X ⟶ Y) :
    (constEdgeIso x y).hom ≫ map x y f =
      (Functor.const SimplexCategoryᵒᵖ).map (↾fun e ↦ e.map f) ≫
        (constEdgeIso (f.app _ x) (f.app _ y)).hom := by
  refine (constHomEquiv _).injective (funext fun e ↦ obj₀Equiv.injective ?_)
  -- Both sides are computed on vertices by `constEdgeIso_hom_app_zero`.
  simp

/-- For strict Segal simplicial sets, such as nerves of categories, the map induced by `f` on right
mapping spaces is an isomorphism exactly when `f` induces a bijection on edges from `x` to `y`. -/
theorem isIso_map_iff_bijective [X.IsStrictSegal] [Y.IsStrictSegal] (f : X ⟶ Y) :
    IsIso (map x y f) ↔ Function.Bijective fun e : X.Edge x y ↦ e.map f := by
  rw [← isIso_comp_left_iff (constEdgeIso x y).hom, constEdgeIso_hom_comp_map,
    isIso_comp_right_iff]
  -- A map of discrete simplicial sets is an isomorphism exactly when its map of vertices is.
  refine ⟨fun _ ↦ (isIso_iff_bijective (↾fun e : X.Edge x y ↦ e.map f)).1
    (inferInstanceAs (IsIso (((Functor.const _).map _).app (op ⦋0⦌)))), fun h ↦ ?_⟩
  have := (isIso_iff_bijective (↾fun e : X.Edge x y ↦ e.map f)).2 h
  infer_instance

/-- A monomorphism induces monomorphisms of right mapping spaces. -/
instance mono_map (f : X ⟶ Y) [Mono f] : Mono (map x y f) := by
  have : Mono (Functor.whiskerLeft joinVertex.op f) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    exact (NatTrans.mono_iff_mono_app f).1 inferInstance _
  exact mono_of_mono_fac (map_ι x y f)

/-- The map induced on right mapping spaces by an isomorphism is an isomorphism. -/
instance isIso_map (f : X ⟶ Y) [IsIso f] : IsIso (map x y f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).1 inferInstance, fun s ↦ ?_⟩
  -- The preimage of `s` is its image under the inverse of `f`, which lies in `Hom^R_X(x, y)`
  -- because the inverse of `f` sends `f x` and `f y` back to `x` and `y`.
  have hs : (inv f).app _ (s.1 : Y _⦋n + 1⦌) ∈ (X.rightMappingSpace ((inv f).app _ (f.app _ x))
      ((inv f).app _ (f.app _ y))).obj (op ⦋n⦌) :=
    ((map (f.app _ x) (f.app _ y) (inv f)).app _ s).2
  have hx (z : X _⦋0⦌) : (inv f).app _ (f.app _ z) = z := by simp
  rw [hx, hx] at hs
  exact ⟨⟨_, hs⟩, Subtype.ext ((map_app_coe f _).trans (by simp))⟩

/-- If a subcomplex `A` of `X` contains every simplex of `Hom^R_X(x, y)`, for vertices `x` and `y`
of `A`, then the inclusion of `A` induces an isomorphism `Hom^R_A(x, y) ≅ Hom^R_X(x, y)`. -/
theorem isIso_map_ι {A : X.Subcomplex} (x y : (A : SSet.{u}) _⦋0⦌)
    (h : ∀ (n : ℕ) (s : (X.rightMappingSpace x.1 y.1 : SSet.{u}) _⦋n⦌),
      (s.1 : X _⦋n + 1⦌) ∈ A.obj (op ⦋n + 1⦌)) :
    IsIso (map x y A.ι) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).1 inferInstance, fun s ↦ ?_⟩
  -- The simplex `s` of `Hom^R_X(x, y)` lies in `A`, and its faces in `A` are those in `X`.
  obtain ⟨h₁, h₂⟩ := (mem_rightMappingSpace_iff _).1 s.2
  refine ⟨⟨⟨s.1, h n s⟩, (mem_rightMappingSpace_iff _).2 ⟨Subtype.ext h₁, Subtype.ext h₂⟩⟩, ?_⟩
  exact Subtype.ext (map_app_coe A.ι _)

end map

/-! ### Products -/

section prod

open MonoidalCategory CartesianMonoidalCategory

variable {Y : SSet.{u}} {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}

/-- A simplex of `joinVertex.op ⋙ (X ⊗ Y)` lies in `Hom^R_{X ⊗ Y}((x₀, y₀), (x₁, y₁))` exactly
when its two components lie in `Hom^R_X(x₀, x₁)` and `Hom^R_Y(y₀, y₁)`. -/
theorem mem_tensor_iff {m : SimplexCategoryᵒᵖ} (σ : (joinVertex.op ⋙ (X ⊗ Y)).obj m) :
    σ ∈ ((X ⊗ Y).rightMappingSpace (x₀, y₀) (x₁, y₁)).obj m ↔
      σ.1 ∈ (X.rightMappingSpace x₀ x₁).obj m ∧ σ.2 ∈ (Y.rightMappingSpace y₀ y₁).obj m :=
  -- The simplicial operators of `X ⊗ Y` act componentwise.
  (and_congr Prod.ext_iff Prod.ext_iff).trans and_and_and_comm

variable (x₀ x₁ y₀ y₁) in
/-- **Right mapping spaces of products are products**: the maps induced by the two projections
identify `Hom^R_{X ⊗ Y}((x₀, y₀), (x₁, y₁))` with `Hom^R_X(x₀, x₁) ⊗ Hom^R_Y(y₀, y₁)`. -/
noncomputable def prodIso :
    ((X ⊗ Y).rightMappingSpace (x₀, y₀) (x₁, y₁) : SSet.{u}) ≅
      (X.rightMappingSpace x₀ x₁ : SSet.{u}) ⊗ (Y.rightMappingSpace y₀ y₁ : SSet.{u}) where
  hom := lift (map (x₀, y₀) (x₁, y₁) (fst X Y)) (map (x₀, y₀) (x₁, y₁) (snd X Y))
  inv := Subcomplex.lift ((X.rightMappingSpace x₀ x₁).ι ⊗ₘ (Y.rightMappingSpace y₀ y₁).ι) (by
    rintro m _ ⟨s, rfl⟩
    exact (mem_tensor_iff _).2 ⟨s.1.2, s.2.2⟩)
  hom_inv_id := by
    ext m s
    rfl
  inv_hom_id := by
    ext m s <;> rfl

variable (x₀ x₁ y₀ y₁) in
/-- The first component of `prodIso` is the map induced by the first projection. -/
@[reassoc (attr := simp)]
theorem prodIso_hom_fst :
    (prodIso x₀ x₁ y₀ y₁).hom ≫ fst _ _ = map (x₀, y₀) (x₁, y₁) (fst X Y) :=
  lift_fst _ _

variable (x₀ x₁ y₀ y₁) in
/-- The second component of `prodIso` is the map induced by the second projection. -/
@[reassoc (attr := simp)]
theorem prodIso_hom_snd :
    (prodIso x₀ x₁ y₀ y₁).hom ≫ snd _ _ = map (x₀, y₀) (x₁, y₁) (snd X Y) :=
  lift_snd _ _

variable (x₀ x₁ y₀ y₁) in
/-- The inverse of `prodIso` pairs a simplex of `Hom^R_X(x₀, x₁)` with a simplex of
`Hom^R_Y(y₀, y₁)`. -/
@[reassoc (attr := simp)]
theorem prodIso_inv_ι :
    (prodIso x₀ x₁ y₀ y₁).inv ≫ ((X ⊗ Y).rightMappingSpace (x₀, y₀) (x₁, y₁)).ι =
      (X.rightMappingSpace x₀ x₁).ι ⊗ₘ (Y.rightMappingSpace y₀ y₁).ι :=
  (rfl)

end prod

end rightMappingSpace

end SSet
