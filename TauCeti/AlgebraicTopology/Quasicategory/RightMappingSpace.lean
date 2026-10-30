/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

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
`AugmentedSimplexCategory`.

If `X` is a quasicategory, every horn `Λ[n, i]` with `0 < i` in `Hom^R_X(x, y)` has a filler: in
`X` it is an inner horn `Λ[n + 1, i]` whose last face is the constant simplex at `x`. Thus
`Hom^R_X(x, y)` is again a quasicategory, in which all horns except possibly the ones `Λ[n, 0]`
can be filled. (That the remaining horns can also be filled, making `Hom^R_X(x, y)` a Kan complex,
is Joyal's theorem on special outer horns, which this file does not prove.)

## Main definitions

* `SimplexCategory.joinVertex`: the endofunctor `⦋n⦌ ↦ ⦋n⦌ ⋆ ⦋0⦌ = ⦋n + 1⦌` of `SimplexCategory`.
* `SSet.rightMappingSpace X x y`: the right mapping space `Hom^R_X(x, y)`.
* `SSet.rightMappingSpace.obj₀Equiv`: its vertices are the edges from `x` to `y`.

## Main results

* `SSet.mem_rightMappingSpace_iff`: the description of the simplices of `Hom^R_X(x, y)`, and
  `SSet.rightMappingSpace.coe_δ`: their faces are faces in `X` avoiding the last vertex.
* `SSet.rightMappingSpace.hornFilling`: if `X` is a quasicategory, the horns `Λ[n, i]` with
  `i ≠ 0` in `Hom^R_X(x, y)` have fillers.
* `SSet.rightMappingSpace.quasicategory`: the right mapping spaces of a quasicategory are
  quasicategories.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 (the right mapping space `Hom^R_S(x, y)`) and
  Proposition 1.2.2.3.
-/

public section

open CategoryTheory Opposite Simplicial AugmentedSimplexCategory

universe u

namespace SimplexCategory

/-- A morphism out of `⦋m.len + 1⦌` is determined by its values on the first `m.len + 1`
vertices and on the last vertex. -/
private theorem hom_ext_castSucc_last {m n : SimplexCategory} {f g : ⦋m.len + 1⦌ ⟶ n}
    (h : ∀ i : Fin (m.len + 1), f.toOrderHom i.castSucc = g.toOrderHom i.castSucc)
    (h' : f.toOrderHom (Fin.last _) = g.toOrderHom (Fin.last _)) : f = g := by
  ext i : 3
  cases i using Fin.lastCases
  exacts [h', h _]

/-- The extension of `f` to the joins with a final vertex sends `i` to `f i`. -/
private theorem tensorHomOf_castSucc {m n : SimplexCategory} (f : m ⟶ n) (i : Fin (m.len + 1)) :
    (tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom i.castSucc = (f.toOrderHom i).castSucc := by
  ext
  simp [tensorHomOf, Fin.addCases, Fin.is_le]

/-- The extension of `f` to the joins with a final vertex fixes the final vertex. -/
private theorem tensorHomOf_last {m n : SimplexCategory} (f : m ⟶ n) :
    (tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom (Fin.last (m.len + 1)) = Fin.last (n.len + 1) := by
  ext
  simp [tensorHomOf, Fin.addCases]

/-- The join `m ⋆ ⦋0⦌` with a final vertex, as an endofunctor of `SimplexCategory`: the
restriction of the join `- ⊗ ⦋0⦌` of `AugmentedSimplexCategory`. It sends `⦋n⦌` to `⦋n + 1⦌` and
extends a monotone map by sending the final vertex to the final vertex. -/
-- The body is exposed so that `joinVertex.obj ⦋n⦌` is definitionally `⦋n + 1⦌` downstream: the
-- simplices of `joinVertex.op ⋙ X` are then literally simplices of `X`. The functor laws are
-- those of the join, which hold here by definitional unfolding of `tensorHom` on `.of` objects.
@[expose]
def joinVertex : SimplexCategory ⥤ SimplexCategory where
  obj m := ⦋m.len + 1⦌
  map f := tensorHomOf f (𝟙 ⦋0⦌)
  map_id m := tensor_id (WithInitial.of m) (WithInitial.of ⦋0⦌)
  map_comp {a b c} f g := (tensorHom_comp_tensorHom (x₁ := WithInitial.of a)
    (y₁ := WithInitial.of b) (z₁ := WithInitial.of c) (x₂ := WithInitial.of ⦋0⦌)
    (y₂ := WithInitial.of ⦋0⦌) (z₂ := WithInitial.of ⦋0⦌) f (𝟙 _) g (𝟙 _)).symm

@[simp]
theorem joinVertex_obj (m : SimplexCategory) : joinVertex.obj m = ⦋m.len + 1⦌ :=
  (rfl)

@[simp]
theorem joinVertex_map_castSucc {m n : SimplexCategory} (f : m ⟶ n) (i : Fin (m.len + 1)) :
    (joinVertex.map f).toOrderHom i.castSucc = (f.toOrderHom i).castSucc :=
  tensorHomOf_castSucc f i

@[simp]
theorem joinVertex_map_last {m n : SimplexCategory} (f : m ⟶ n) :
    (joinVertex.map f).toOrderHom (Fin.last (m.len + 1)) = Fin.last (n.len + 1) :=
  tensorHomOf_last f

/-- The join with a final vertex sends the `i`-th coface map to the `i`-th coface map. -/
theorem joinVertex_map_δ {n : ℕ} (i : Fin (n + 2)) :
    joinVertex.map (δ i) = δ i.castSucc :=
  hom_ext_castSucc_last (m := ⦋n⦌)
    (fun j ↦ (joinVertex_map_castSucc (δ i) j).trans Fin.castSucc_succAbove_castSucc.symm)
    ((joinVertex_map_last (δ i)).trans
      (Fin.succAbove_ne_last_last (Fin.castSucc_lt_last i).ne).symm)

/-- The inclusion of `m` into `m ⋆ ⦋0⦌` as the face opposite to the final vertex. -/
def joinVertexInl (m : SimplexCategory) : m ⟶ joinVertex.obj m :=
  δ (Fin.last (m.len + 1))

/-- The final vertex of `m ⋆ ⦋0⦌`. -/
def joinVertexInr (m : SimplexCategory) : ⦋0⦌ ⟶ joinVertex.obj m :=
  const ⦋0⦌ ⦋m.len + 1⦌ (Fin.last _)

/-- On `⦋n⦌`, the inclusion into the join with a final vertex is the last coface map. -/
theorem joinVertexInl_mk (n : ℕ) : joinVertexInl ⦋n⦌ = δ (Fin.last (n + 1)) :=
  (rfl)

/-- On `⦋n⦌`, the final vertex of the join is the vertex `n + 1` of `⦋n + 1⦌`. -/
theorem joinVertexInr_mk (n : ℕ) : joinVertexInr ⦋n⦌ = const ⦋0⦌ ⦋n + 1⦌ (Fin.last _) :=
  (rfl)

/-- The inclusion `m ⟶ m ⋆ ⦋0⦌` is natural in `m`. -/
@[reassoc]
theorem joinVertexInl_comp_joinVertex_map {m n : SimplexCategory} (f : m ⟶ n) :
    joinVertexInl m ≫ joinVertex.map f = f ≫ joinVertexInl n := by
  ext i : 3
  exact (congrArg (joinVertex.map f).toOrderHom (Fin.succAbove_last_apply i)).trans
    ((joinVertex_map_castSucc f i).trans (Fin.succAbove_last_apply _).symm)

/-- The join with a final vertex preserves the final vertex. -/
@[reassoc (attr := simp)]
theorem joinVertexInr_comp_joinVertex_map {m n : SimplexCategory} (f : m ⟶ n) :
    joinVertexInr m ≫ joinVertex.map f = joinVertexInr n :=
  Hom.ext_zero_left _ _ (joinVertex_map_last f)

end SimplexCategory

namespace SSet

open SimplexCategory

variable (X : SSet.{u})

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
    · change X.map (joinVertexInl m'.unop).op (X.map (joinVertex.map f.unop).op σ) = _
      rw [← Functor.map_comp_apply, ← op_comp, joinVertexInl_comp_joinVertex_map, op_comp,
        Functor.map_comp_apply, hσ.1, ← Functor.map_comp_apply, ← op_comp,
        Subsingleton.elim (f.unop ≫ SimplexCategory.const m.unop ⦋0⦌ 0)]
    · change X.map (joinVertexInr m'.unop).op (X.map (joinVertex.map f.unop).op σ) = _
      rw [← Functor.map_comp_apply, ← op_comp, joinVertexInr_comp_joinVertex_map, hσ.2]

variable {X} {x y : X _⦋0⦌}

/-- An `(n + 1)`-simplex of `X` is an `n`-simplex of `Hom^R_X(x, y)` exactly when its face
opposite to the last vertex is the constant simplex at `x` and its last vertex is `y`. -/
theorem mem_rightMappingSpace_iff {n : ℕ} (σ : X _⦋n + 1⦌) :
    σ ∈ (X.rightMappingSpace x y).obj (op ⦋n⦌) ↔
      X.δ (Fin.last (n + 1)) σ = X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x ∧
        X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last _)).op σ = y :=
  Iff.rfl

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

/-- The faces of `joinVertex.op ⋙ X` are faces of `X` avoiding the last vertex. -/
private theorem δ_joinVertex {m : ℕ} (a : Fin (m + 2)) (s : X _⦋m + 1 + 1⦌) :
    SimplicialObject.δ (joinVertex.op ⋙ X) a s = X.δ a.castSucc s :=
  congrArg (fun g ↦ X.map (Quiver.Hom.op g) s) (joinVertex_map_δ a)

/-- The `j`-th face of an `(n + 1)`-simplex of `Hom^R_X(x, y)` is the `j`-th face of the
corresponding `(n + 2)`-simplex of `X`. -/
theorem coe_δ {n : ℕ} (j : Fin (n + 2)) (s : (X.rightMappingSpace x y : SSet.{u}) _⦋n + 1⦌) :
    (SimplicialObject.δ (X.rightMappingSpace x y : SSet.{u}) j s).1 =
      X.δ j.castSucc (s.1 : X _⦋n + 2⦌) :=
  δ_joinVertex j s.1

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
  have hg (l : Fin (m + 3)) (hl : l ≠ i) :
      horn.ι i l hl ≫ σ₀ ≫ Subcomplex.ι _ = yonedaEquiv.symm (hornFace σ₀ l hl) := by
    rw [Equiv.eq_symm_apply, yonedaEquiv_comp, horn.yonedaEquiv_ι]
    rfl
  have h := (horn.IsCompatible.of_hom (σ₀ ≫ Subcomplex.ι _)).δ_pred_comp j k hj hk hjk
  rw [hg, hg, stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm] at h
  exact yonedaEquiv.symm.injective h

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
      ← Functor.map_comp_apply, ← op_comp,
      Subsingleton.elim (δ _ ≫ SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0)]
  | cast k =>
    have hk' : k ≠ i := fun h ↦ hk (h ▸ rfl)
    rw [liftFace_castSucc σ₀ k hk']
    obtain _ | m := n
    · exfalso
      rw [Fin.castSucc_lt_castSucc_iff] at hjk
      omega
    · have h := (δ_joinVertex _ _).symm.trans
        ((hornFace_δ σ₀ j k hj' hk' (Fin.castSucc_lt_castSucc_iff.1 hjk)).trans
          (δ_joinVertex _ _))
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
    rw [ht, SimplicialObject.δ, yonedaEquiv_naturality,
      show stdSimplex.map (δ k) = horn.ι _ k hk ≫ Λ[n + 2, i.castSucc].ι from
        (horn.ι_ι _ k hk).symm,
      Category.assoc, ← hτ, horn.IsCompatible.ι_desc, Equiv.apply_symm_apply]
  -- The filler is a simplex of the right mapping space.
  have hmem : t ∈ (X.rightMappingSpace x y).obj (op ⦋n + 1⦌) := by
    refine (mem_rightMappingSpace_iff _).2 ⟨?_, ?_⟩
    · rw [hface _ (Fin.castSucc_lt_last i).ne', liftFace_last]
    · -- The last vertex of the filler is the last vertex of its face opposite to `0`.
      have h0 : Fin.castSucc (0 : Fin (n + 2)) ≠ i.castSucc :=
        fun h ↦ hi (Fin.castSucc_injective _ h).symm
      have h := ((mem_rightMappingSpace_iff _).1 (hornFace_mem σ₀ 0 hi.symm)).2
      rw [← liftFace_castSucc σ₀ 0 hi.symm h0, ← hface _ h0, SimplicialObject.δ,
        ← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp] at h
      simpa [δ] using h
  let s : (X.rightMappingSpace x y : SSet.{u}) _⦋n + 1⦌ := ⟨t, hmem⟩
  refine ⟨yonedaEquiv.symm s, horn.hom_ext _ _ fun j hj ↦ Subtype.ext ?_⟩
  have hR : (Λ[n + 1, i].ι ≫ yonedaEquiv.symm s).app _ (horn.face i j hj) =
      SimplicialObject.δ (X.rightMappingSpace x y : SSet.{u}) j s := by
    rw [← horn.yonedaEquiv_ι, ← yonedaEquiv_comp, ← Category.assoc, horn.ι_ι,
      stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]
  rw [hR, coe_δ, hface _ fun h ↦ hj (Fin.castSucc_injective _ h), liftFace_castSucc σ₀ j hj]
  rfl

/-- The right mapping spaces of a quasicategory are quasicategories. -/
instance quasicategory [X.Quasicategory] :
    (X.rightMappingSpace x y : SSet.{u}).Quasicategory where
  hornFilling' _ _ σ₀ h0 _ := hornFilling h0.ne' σ₀

end rightMappingSpace

end SSet
