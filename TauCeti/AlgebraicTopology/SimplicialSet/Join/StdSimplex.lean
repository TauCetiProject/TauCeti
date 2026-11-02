/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Joins of standard simplices

The join `Δ[n] ⋆ Δ[m]` is the standard simplex `Δ[n + m + 1]`, with `Δ[n]` and `Δ[m]` as the
faces spanned by the first `n + 1` and the last `m + 1` vertices. Under this isomorphism the joins
of horns and boundaries are horns: for `n ≠ 0`, the subcomplex
`(Λ[n, i] ⋆ Δ[m]) ∪ (Δ[n] ⋆ ∂Δ[m])` of `Δ[n] ⋆ Δ[m]` is the horn `Λ[n + m + 1, i]`, and for
`m ≠ 0`, `(∂Δ[n] ⋆ Δ[m]) ∪ (Δ[n] ⋆ Λ[m, j])` is the horn `Λ[n + m + 1, n + 1 + j]`. Hence the
pushout-join of a horn inclusion `Λ[n, i] ⟶ Δ[n]` with `0 < i` and a boundary inclusion
`∂Δ[m] ⟶ Δ[m]` is an inner anodyne extension, and so is the pushout-join of `∂Δ[n] ⟶ Δ[n]` and
`Λ[m, j] ⟶ Δ[m]` with `j < m`. These are the generating cases of the lifting
properties showing that slices and coslices of quasicategories are quasicategories, whose
projections are right and left fibrations.

## Main definitions

* `SSet.join.stdSimplexIso n m`: the isomorphism `Δ[n] ⋆ Δ[m] ≅ Δ[n + m + 1]`.

## Main results

* `SSet.join.yonedaEquiv_inl_comp_stdSimplexIso_hom`,
  `SSet.join.yonedaEquiv_inr_comp_stdSimplexIso_hom`: under `SSet.join.stdSimplexIso`, the vertex
  `j` of `Δ[n]` is the vertex `j` of `Δ[n + m + 1]` and the vertex `j` of `Δ[m]` is the vertex
  `n + 1 + j`.
* `SSet.join.preimage_unionJoin_horn_boundary`: `(Λ[n, i] ⋆ Δ[m]) ∪ (Δ[n] ⋆ ∂Δ[m])` corresponds to
  `Λ[n + m + 1, i]`, for `n ≠ 0`.
* `SSet.join.preimage_unionJoin_boundary_horn`: `(∂Δ[n] ⋆ Δ[m]) ∪ (Δ[n] ⋆ Λ[m, j])` corresponds to
  `Λ[n + m + 1, n + 1 + j]`, for `m ≠ 0`.
* `SSet.join.innerAnodyneExtensions_unionJoin_horn_boundary`,
  `SSet.join.innerAnodyneExtensions_unionJoin_boundary_horn`: the corresponding pushout-joins are
  inner anodyne extensions.

## Implementation notes

The isomorphism sends a simplex of `Δ[n] ⋆ Δ[m]`, described by its join data, to the simplex of
`Δ[n + m + 1]` whose vertices are the images of its vertices in `Δ[n]`, and in `Δ[m]` shifted by
`n + 1`; its inverse is the map given by the universal property of the join from the join data on
`Δ[n + m + 1]` that splits its vertices after `n`. To identify the pushout-join with the horn, note
that a simplex `x` of `Δ[n + m + 1]` that misses a vertex misses it in all faces of its parts in
`Δ[n]` and `Δ[m]`; conversely, if `x` misses no vertex other than the horn vertex, a face of its
part in `Δ[n]` and a face of its part in `Δ[m]` are constructed, as sections of `x`, that meet all
the corresponding vertices.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.8 and Lemma 2.1.2.3.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

namespace join

variable {n m d : ℕ}

/-- The map `⦋n + m + 1⦌ ⟶ ⦋1⦌` sending the first `n + 1` vertices to `0` and the others to `1`. -/
private def splitHom (n m : ℕ) : ⦋n + m + 1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom ⟨fun j ↦ if (j : ℕ) ≤ n then 0 else 1, fun a b hab ↦ by
    simp only [Fin.le_def] at hab
    dsimp only
    split_ifs <;> first | exact le_rfl | exact Fin.zero_le _ | omega⟩

/-- The map `⦋n + m + 1⦌ ⟶ ⦋n⦌` collapsing the last `m + 1` vertices onto `n`. -/
private def leftHom (n m : ℕ) : ⦋n + m + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom ⟨fun j ↦ ⟨min j n, by omega⟩, fun a b hab ↦ by
    simp only [Fin.le_def] at hab ⊢
    omega⟩

/-- The map `⦋n + m + 1⦌ ⟶ ⦋m⦌` collapsing the first `n + 1` vertices onto `0`. -/
private def rightHom (n m : ℕ) : ⦋n + m + 1⦌ ⟶ ⦋m⦌ :=
  SimplexCategory.mkHom ⟨fun j ↦ ⟨j - (n + 1), by omega⟩, fun a b hab ↦ by
    simp only [Fin.le_def] at hab ⊢
    omega⟩

private lemma map_splitHom_app_apply (x : Δ[n + m + 1] _⦋d⦌) (j : Fin (d + 1)) :
    (stdSimplex.map (splitHom n m)).app _ x j = if (x j : ℕ) ≤ n then 0 else 1 :=
  (rfl)

/-- The join data on `Δ[n + m + 1]` splitting it into its first `n + 1` and its last `m + 1`
vertices. -/
private def splitData (n m : ℕ) : JoinData Δ[n + m + 1] Δ[n] Δ[m] where
  p := stdSimplex.map (splitHom n m)
  left := (joinFiber _ 0).ι ≫ stdSimplex.map (leftHom n m)
  right := (joinFiber _ 1).ι ≫ stdSimplex.map (rightHom n m)

section vertex

variable (e : JoinData Δ[d] Δ[n] Δ[m])

/-- The vertex of `Δ[n]` to which `e` sends a vertex `j` of `Δ[d]` over `0`. -/
private def leftVertex (j : Fin (d + 1)) (hj : yonedaEquiv e.p j = 0) : Fin (n + 1) :=
  e.left.app _ ⟨stdSimplex.obj₀Equiv.symm j, (obj₀Equiv_symm_mem_joinFiber_iff _ _ _).2 hj⟩ 0

/-- The vertex of `Δ[m]` to which `e` sends a vertex `j` of `Δ[d]` not over `0`. -/
private def rightVertex (j : Fin (d + 1)) (hj : ¬ yonedaEquiv e.p j = 0) : Fin (m + 1) :=
  e.right.app _ ⟨stdSimplex.obj₀Equiv.symm j,
    (obj₀Equiv_symm_mem_joinFiber_iff _ _ _).2 (Fin.eq_one_of_ne_zero _ hj)⟩ 0

/-- The vertices of the simplex of `Δ[n + m + 1]` attached to join data `e` on `Δ[d]`: a vertex over
`0` goes to its image in `Δ[n]`, and a vertex over `1` goes to `n + 1` plus its image in `Δ[m]`. -/
private def vertex (j : Fin (d + 1)) : Fin (n + m + 2) :=
  if hj : yonedaEquiv e.p j = 0 then Fin.castLE (by omega) (leftVertex e j hj)
  else Fin.cast (by omega) (Fin.natAdd (n + 1) (rightVertex e j hj))

private lemma vertex_of_eq_zero {j : Fin (d + 1)} (hj : yonedaEquiv e.p j = 0) :
    (vertex e j : ℕ) = leftVertex e j hj := by
  rw [vertex, dite_eq_left hj, Fin.val_castLE]

private lemma vertex_of_ne_zero {j : Fin (d + 1)} (hj : ¬ yonedaEquiv e.p j = 0) :
    (vertex e j : ℕ) = n + 1 + rightVertex e j hj := by
  rw [vertex, dite_eq_right hj, Fin.val_cast, Fin.val_natAdd]

/-- The vertex of the image of a simplex `y` over `0` under the map to `Δ[n]` is the image of the
vertex of `y`. -/
private lemma left_app_apply {a : ℕ} (y : Δ[d] _⦋a⦌) (hy : y ∈ (joinFiber e.p 0).obj _)
    (t : Fin (a + 1)) (ht : yonedaEquiv e.p (y t) = 0) :
    e.left.app _ ⟨y, hy⟩ t = leftVertex e (y t) ht :=
  stdSimplex.subcomplex_hom_app_apply _ _ _ _ _

private lemma right_app_apply {a : ℕ} (y : Δ[d] _⦋a⦌) (hy : y ∈ (joinFiber e.p 1).obj _)
    (t : Fin (a + 1)) (ht : ¬ yonedaEquiv e.p (y t) = 0) :
    e.right.app _ ⟨y, hy⟩ t = rightVertex e (y t) ht :=
  stdSimplex.subcomplex_hom_app_apply _ _ _ _ _

private lemma monotone_vertex : Monotone (vertex e) := by
  intro j k hjk
  have hp : yonedaEquiv e.p j ≤ yonedaEquiv e.p k := stdSimplex.monotone_apply _ hjk
  rw [Fin.le_def]
  by_cases hj : yonedaEquiv e.p j = 0 <;> by_cases hk : yonedaEquiv e.p k = 0
  · rw [vertex_of_eq_zero e hj, vertex_of_eq_zero e hk, leftVertex, leftVertex]
    exact joinFiber_hom_vertex_le e.left hjk hj hk
  · rw [vertex_of_eq_zero e hj, vertex_of_ne_zero e hk]
    omega
  · rw [hk, Fin.eq_one_of_ne_zero _ hj] at hp
    exact absurd hp (by decide)
  · rw [vertex_of_ne_zero e hj, vertex_of_ne_zero e hk, rightVertex, rightVertex]
    have := joinFiber_hom_vertex_le e.right hjk (Fin.eq_one_of_ne_zero _ hj)
      (Fin.eq_one_of_ne_zero _ hk)
    rw [Fin.le_def] at this
    omega

private lemma vertex_precomp {d' : ℕ} (g : Δ[d'] ⟶ Δ[d]) (j : Fin (d' + 1)) :
    vertex (e.precomp g) j = vertex e (yonedaEquiv g j) := by
  have hp := e.yonedaEquiv_precomp_p_apply g j
  have hv := stdSimplex.hom_app_obj₀Equiv_symm g j
  apply Fin.ext
  by_cases hj : yonedaEquiv e.p (yonedaEquiv g j) = 0
  · rw [vertex_of_eq_zero _ (hp.trans hj), vertex_of_eq_zero _ hj, leftVertex, leftVertex,
      JoinData.precomp_left_app]
    simp only [hv]
  · rw [vertex_of_ne_zero _ (hp ▸ hj), vertex_of_ne_zero _ hj, rightVertex, rightVertex,
      JoinData.precomp_right_app]
    simp only [hv]

end vertex

/-- The simplex of `Δ[n + m + 1]` with vertices `vertex e`, for the join data `e` of a simplex `s`
of `Δ[n] ⋆ Δ[m]`. -/
private def toStdSimplexObj (s : (join Δ[n] Δ[m]) _⦋d⦌) : Δ[n + m + 1] _⦋d⦌ :=
  stdSimplex.objMk ⟨vertex (objEquiv s), monotone_vertex _⟩

private lemma toStdSimplexObj_apply (s : (join Δ[n] Δ[m]) _⦋d⦌) (j : Fin (d + 1)) :
    toStdSimplexObj s j = vertex (objEquiv s) j :=
  (rfl)

variable (n m) in
/-- The map `Δ[n] ⋆ Δ[m] ⟶ Δ[n + m + 1]` sending a simplex with join data `e` to the simplex with
vertices `vertex e`. -/
private def toStdSimplex : join Δ[n] Δ[m] ⟶ Δ[n + m + 1] where
  app d := ↾fun s ↦ toStdSimplexObj (d := d.unop.len) s
  naturality d d' f := by
    ext s
    induction d using Opposite.rec with | op d
    induction d' using Opposite.rec with | op d'
    induction d using SimplexCategory.rec with | _ d
    induction d' using SimplexCategory.rec with | _ d'
    refine stdSimplex.ext _ _ fun j ↦ ?_
    simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply]
    rw [toStdSimplexObj_apply, objEquiv_map, vertex_precomp, stdSimplex.obj_map_apply,
      toStdSimplexObj_apply, yonedaEquiv_map, stdSimplex.objEquiv_symm_apply]

private lemma toStdSimplex_app_apply (s : (join Δ[n] Δ[m]) _⦋d⦌) (j : Fin (d + 1)) :
    (toStdSimplex n m).app _ s j = vertex (objEquiv s) j :=
  (rfl)

private lemma yonedaEquiv_splitData_p (k : Fin (n + m + 2)) :
    yonedaEquiv (splitData n m).p k = if (k : ℕ) ≤ n then 0 else 1 := by
  rw [splitData, stdSimplex.yonedaEquiv_eq_app_id, map_splitHom_app_apply,
    stdSimplex.yonedaEquiv_id_apply]

private lemma splitData_left_app_apply {a : ℕ} (y : (joinFiber (splitData n m).p 0).obj (op ⦋a⦌))
    (t : Fin (a + 1)) : ((splitData n m).left.app _ y t : ℕ) = min (y.1 t : ℕ) n :=
  (rfl)

private lemma splitData_right_app_apply {a : ℕ} (y : (joinFiber (splitData n m).p 1).obj (op ⦋a⦌))
    (t : Fin (a + 1)) : ((splitData n m).right.app _ y t : ℕ) = y.1 t - (n + 1) :=
  (rfl)

private lemma vertex_splitData (k : Fin (n + m + 2)) : vertex (splitData n m) k = k := by
  have hp := yonedaEquiv_splitData_p (n := n) (m := m) k
  apply Fin.ext
  by_cases hk : (k : ℕ) ≤ n
  · rw [ite_eq_left hk] at hp
    rw [vertex_of_eq_zero _ hp, leftVertex, splitData_left_app_apply]
    simp only [stdSimplex.obj₀Equiv_symm_apply, stdSimplex.const_apply]
    omega
  · rw [ite_eq_right hk] at hp
    rw [vertex_of_ne_zero _ (by rw [hp]; decide), rightVertex, splitData_right_app_apply]
    simp only [stdSimplex.obj₀Equiv_symm_apply, stdSimplex.const_apply]
    omega

private lemma vertex_splitData_precomp (x : Δ[n + m + 1] _⦋d⦌) (j : Fin (d + 1)) :
    vertex ((splitData n m).precomp (yonedaEquiv.symm x)) j = x j := by
  rw [vertex_precomp, Equiv.apply_symm_apply, vertex_splitData]

private lemma toStdSimplex_comp_homEquiv_symm :
    toStdSimplex n m ≫ homEquiv.symm (splitData n m) = 𝟙 _ := by
  ext ⟨d⟩ s
  induction d using SimplexCategory.rec with | _ d
  apply objEquiv.injective
  simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, ConcreteCategory.comp_apply,
    homEquiv_symm_app, Equiv.apply_symm_apply, NatTrans.id_app, ConcreteCategory.id_apply]
  set x := (toStdSimplex n m).app _ s
  have hx (k : Fin (d + 1)) : x k = vertex (objEquiv s) k := toStdSimplex_app_apply s k
  refine JoinData.ext ?_ ?_ ?_
  · refine yonedaEquiv.injective (stdSimplex.ext _ _ fun j ↦ ?_)
    rw [JoinData.precomp_p, yonedaEquiv_comp, Equiv.apply_symm_apply, splitData,
      map_splitHom_app_apply, hx]
    by_cases hj : yonedaEquiv (objEquiv s).p j = 0
    · rw [vertex_of_eq_zero _ hj, ite_eq_left (Nat.lt_succ_iff.1 (Fin.isLt _)), hj]
    · rw [vertex_of_ne_zero _ hj, ite_eq_right (by omega), Fin.eq_one_of_ne_zero _ hj]
  · intro k y hy hy'
    induction k using Opposite.rec with | op k
    induction k using SimplexCategory.rec with | _ k
    refine stdSimplex.ext _ _ fun t ↦ Fin.ext ?_
    have ht := yonedaEquiv_apply_of_mem_joinFiber hy' t
    rw [JoinData.precomp_left_app, splitData_left_app_apply, stdSimplex.hom_app_apply,
      Equiv.apply_symm_apply, hx, vertex_of_eq_zero _ ht, left_app_apply _ _ _ _ ht]
    omega
  · intro k y hy hy'
    induction k using Opposite.rec with | op k
    induction k using SimplexCategory.rec with | _ k
    refine stdSimplex.ext _ _ fun t ↦ Fin.ext ?_
    have ht : ¬ yonedaEquiv (objEquiv s).p (y t) = 0 := by
      rw [yonedaEquiv_apply_of_mem_joinFiber hy' t]
      decide
    rw [JoinData.precomp_right_app, splitData_right_app_apply, stdSimplex.hom_app_apply,
      Equiv.apply_symm_apply, hx, vertex_of_ne_zero _ ht, right_app_apply _ _ _ _ ht]
    omega

private lemma homEquiv_symm_comp_toStdSimplex :
    homEquiv.symm (splitData n m) ≫ toStdSimplex n m = 𝟙 _ := by
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d
  refine stdSimplex.ext _ _ fun j ↦ ?_
  simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, ConcreteCategory.comp_apply,
    NatTrans.id_app, ConcreteCategory.id_apply]
  rw [toStdSimplex_app_apply, homEquiv_symm_app, Equiv.apply_symm_apply,
    vertex_splitData_precomp]

variable (n m) in
/-- **The join of standard simplices**: `Δ[n] ⋆ Δ[m]` is isomorphic to `Δ[n + m + 1]`, with `Δ[n]`
and `Δ[m]` as the faces spanned by the first `n + 1` and the last `m + 1` vertices. -/
noncomputable def stdSimplexIso : join Δ[n] Δ[m] ≅ Δ[n + m + 1] where
  hom := toStdSimplex n m
  inv := homEquiv.symm (splitData n m)
  hom_inv_id := toStdSimplex_comp_homEquiv_symm
  inv_hom_id := homEquiv_symm_comp_toStdSimplex

private lemma objEquiv_stdSimplexIso_inv_app (x : Δ[n + m + 1] _⦋d⦌) :
    objEquiv ((stdSimplexIso n m).inv.app _ x) = (splitData n m).precomp (yonedaEquiv.symm x) := by
  rw [stdSimplexIso, homEquiv_symm_app, Equiv.apply_symm_apply]

private lemma stdSimplexIso_hom_app_apply (s : (join Δ[n] Δ[m]) _⦋d⦌) (j : Fin (d + 1)) :
    (stdSimplexIso n m).hom.app _ s j = vertex (objEquiv s) j :=
  (rfl)

/-- The vertex `j` of `Δ[n + m + 1]` lies over the vertex `0` of `Δ[1]` in `Δ[n] ⋆ Δ[m]` exactly
when `j ≤ n`. -/
@[simp]
lemma yonedaEquiv_stdSimplexIso_inv_comp_π (j : Fin (n + m + 2)) :
    yonedaEquiv ((stdSimplexIso n m).inv ≫ π Δ[n] Δ[m]) j = if (j : ℕ) ≤ n then 0 else 1 := by
  rw [yonedaEquiv_comp, π_app, stdSimplex.yonedaEquiv_eq_app_id (stdSimplexIso n m).inv,
    objEquiv_stdSimplexIso_inv_app, JoinData.yonedaEquiv_precomp_p_apply, Equiv.apply_symm_apply,
    yonedaEquiv_splitData_p, stdSimplex.yonedaEquiv_id_apply]

/-- Under `Δ[n] ⋆ Δ[m] ≅ Δ[n + m + 1]`, `Δ[n]` is the face on the first `n + 1` vertices. -/
@[simp]
lemma yonedaEquiv_inl_comp_stdSimplexIso_hom (j : Fin (n + 1)) :
    yonedaEquiv (inl Δ[n] Δ[m] ≫ (stdSimplexIso n m).hom) j = Fin.castLE (by omega) j := by
  have he : objEquiv (yonedaEquiv (inl Δ[n] Δ[m])) = (univ Δ[n] Δ[m]).precomp (inl Δ[n] Δ[m]) := by
    rw [← univ_precomp_yonedaEquiv_symm, Equiv.symm_apply_apply]
  have hp : yonedaEquiv (objEquiv (yonedaEquiv (inl Δ[n] Δ[m]))).p j = 0 := by
    rw [he, JoinData.precomp_p, univ_p, inl_π, stdSimplex.yonedaEquiv_eq_app_id,
      stdSimplex.const_app_apply]
  apply Fin.ext
  rw [yonedaEquiv_comp, stdSimplexIso_hom_app_apply, vertex_of_eq_zero _ hp, Fin.val_castLE,
    leftVertex, JoinData.congr_left_app he _ _ (by rwa [← he, obj₀Equiv_symm_mem_joinFiber_iff]),
    JoinData.precomp_left_app]
  exact congrArg (fun v : Δ[n] _⦋0⦌ ↦ (v 0 : ℕ)) (univ_left_app_inl_app _ _)

/-- Under `Δ[n] ⋆ Δ[m] ≅ Δ[n + m + 1]`, `Δ[m]` is the face on the last `m + 1` vertices. -/
@[simp]
lemma yonedaEquiv_inr_comp_stdSimplexIso_hom (j : Fin (m + 1)) :
    yonedaEquiv (inr Δ[n] Δ[m] ≫ (stdSimplexIso n m).hom) j =
      Fin.cast (by omega) (Fin.natAdd (n + 1) j) := by
  have he : objEquiv (yonedaEquiv (inr Δ[n] Δ[m])) = (univ Δ[n] Δ[m]).precomp (inr Δ[n] Δ[m]) := by
    rw [← univ_precomp_yonedaEquiv_symm, Equiv.symm_apply_apply]
  have hp : ¬ yonedaEquiv (objEquiv (yonedaEquiv (inr Δ[n] Δ[m]))).p j = 0 := by
    rw [he, JoinData.precomp_p, univ_p, inr_π, stdSimplex.yonedaEquiv_eq_app_id,
      stdSimplex.const_app_apply]
    decide
  apply Fin.ext
  rw [yonedaEquiv_comp, stdSimplexIso_hom_app_apply, vertex_of_ne_zero _ hp, Fin.val_cast,
    Fin.val_natAdd, rightVertex, JoinData.congr_right_app he _ _
      (by rw [← he, obj₀Equiv_symm_mem_joinFiber_iff]; exact Fin.eq_one_of_ne_zero _ hp),
    JoinData.precomp_right_app]
  exact congrArg (fun v : Δ[m] _⦋0⦌ ↦ n + 1 + (v 0 : ℕ)) (univ_right_app_inr_app _ _)

section horn

/-! ### Pushout-joins of horns and boundaries -/

variable (x : Δ[n + m + 1] _⦋d⦌)

private lemma yonedaEquiv_splitData_precomp_p (t : Fin (d + 1)) :
    yonedaEquiv ((splitData n m).precomp (yonedaEquiv.symm x)).p t =
      if (x t : ℕ) ≤ n then 0 else 1 := by
  rw [JoinData.yonedaEquiv_precomp_p_apply, Equiv.apply_symm_apply, yonedaEquiv_splitData_p]

private lemma le_of_mem_joinFiber_zero {a : ℕ} {y : Δ[d] _⦋a⦌}
    (hy : y ∈ (joinFiber ((splitData n m).precomp (yonedaEquiv.symm x)).p 0).obj _)
    (t : Fin (a + 1)) : (x (y t) : ℕ) ≤ n := by
  have h := yonedaEquiv_apply_of_mem_joinFiber hy t
  rw [yonedaEquiv_splitData_precomp_p] at h
  by_contra h'
  rw [ite_eq_right h'] at h
  exact absurd h (by decide)

private lemma lt_of_mem_joinFiber_one {a : ℕ} {y : Δ[d] _⦋a⦌}
    (hy : y ∈ (joinFiber ((splitData n m).precomp (yonedaEquiv.symm x)).p 1).obj _)
    (t : Fin (a + 1)) : n < x (y t) := by
  have h := yonedaEquiv_apply_of_mem_joinFiber hy t
  rw [yonedaEquiv_splitData_precomp_p] at h
  by_contra h'
  rw [ite_eq_left (by omega)] at h
  exact absurd h (by decide)

private lemma splitData_precomp_left_app_apply {a : ℕ} (y : Δ[d] _⦋a⦌)
    (hy : y ∈ (joinFiber ((splitData n m).precomp (yonedaEquiv.symm x)).p 0).obj _)
    (t : Fin (a + 1)) :
    (((splitData n m).precomp (yonedaEquiv.symm x)).left.app _ ⟨y, hy⟩ t : ℕ) = x (y t) := by
  rw [JoinData.precomp_left_app, splitData_left_app_apply]
  simp only [stdSimplex.hom_app_apply, Equiv.apply_symm_apply]
  have := le_of_mem_joinFiber_zero x hy t
  omega

private lemma splitData_precomp_right_app_apply {a : ℕ} (y : Δ[d] _⦋a⦌)
    (hy : y ∈ (joinFiber ((splitData n m).precomp (yonedaEquiv.symm x)).p 1).obj _)
    (t : Fin (a + 1)) :
    (((splitData n m).precomp (yonedaEquiv.symm x)).right.app _ ⟨y, hy⟩ t : ℕ) =
      x (y t) - (n + 1) := by
  rw [JoinData.precomp_right_app, splitData_right_app_apply]
  simp only [stdSimplex.hom_app_apply, Equiv.apply_symm_apply]

/-- A section over the first `n + 1` vertices of a simplex `x` of `Δ[n + m + 1]`: the vertex `j`
goes to the last vertex of `x` with image at most `max j (x 0)`. -/
private def lowerSection : Fin (n + 1) →o Fin (d + 1) where
  toFun j := (Finset.univ.filter fun t ↦ (x t : ℕ) ≤ max (j : ℕ) (x 0 : ℕ)).max' ⟨0, by simp⟩
  monotone' j j' h := Finset.max'_subset _ fun t ht ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at ht h ⊢
    omega

private lemma apply_lowerSection_le (j : Fin (n + 1)) :
    (x (lowerSection x j) : ℕ) ≤ max (j : ℕ) (x 0 : ℕ) := by
  have h := Finset.max'_mem
    (Finset.univ.filter fun t ↦ (x t : ℕ) ≤ max (j : ℕ) (x 0 : ℕ)) ⟨0, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

/-- The section `lowerSection x` hits every vertex `j ≤ n` that `x` hits. -/
private lemma apply_lowerSection_eq {j : Fin (n + 1)} {t : Fin (d + 1)} (ht : (x t : ℕ) = j) :
    (x (lowerSection x j) : ℕ) = j := by
  have h₀ : x 0 ≤ x t := stdSimplex.monotone_apply x (Fin.zero_le t)
  have h₁ := apply_lowerSection_le x j
  have h₂ : x t ≤ x (lowerSection x j) := stdSimplex.monotone_apply x
    (Finset.le_max' _ _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega))
  rw [Fin.le_def] at h₀ h₂
  omega

private lemma lowerSection_mem (h₀ : (x 0 : ℕ) ≤ n) :
    stdSimplex.objMk (n := ⦋d⦌) (m := op ⦋n⦌) (lowerSection x) ∈
      (joinFiber ((splitData n m).precomp (yonedaEquiv.symm x)).p 0).obj _ := by
  refine (mem_joinFiber_iff _ _ _).2 fun t ↦ ?_
  rw [stdSimplex.hom_app_apply, yonedaEquiv_splitData_precomp_p, stdSimplex.objMk_apply]
  have := apply_lowerSection_le x t
  exact ite_eq_left (by omega)

/-- A section over the last `m + 1` vertices of a simplex `x` of `Δ[n + m + 1]`: the vertex `j`
goes to the first vertex of `x` with image at least `min (n + 1 + j) (x (Fin.last d))`. -/
private def upperSection : Fin (m + 1) →o Fin (d + 1) where
  toFun j := (Finset.univ.filter fun t ↦ min (n + 1 + j) (x (Fin.last d) : ℕ) ≤ x t).min'
    ⟨Fin.last d, by simp⟩
  monotone' j j' h := Finset.min'_subset _ fun t ht ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at ht h ⊢
    omega

private lemma le_apply_upperSection (j : Fin (m + 1)) :
    min (n + 1 + j) (x (Fin.last d) : ℕ) ≤ x (upperSection x j) := by
  have h := Finset.min'_mem
    (Finset.univ.filter fun t ↦ min (n + 1 + j) (x (Fin.last d) : ℕ) ≤ x t) ⟨Fin.last d, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

/-- The section `upperSection x` hits every vertex `n + 1 + j` that `x` hits. -/
private lemma apply_upperSection_eq {j : Fin (m + 1)} {t : Fin (d + 1)}
    (ht : (x t : ℕ) = n + 1 + j) : (x (upperSection x j) : ℕ) = n + 1 + j := by
  have h₀ : x t ≤ x (Fin.last d) := stdSimplex.monotone_apply x (Fin.le_last t)
  have h₁ := le_apply_upperSection x j
  have h₂ : x (upperSection x j) ≤ x t := stdSimplex.monotone_apply x
    (Finset.min'_le _ _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega))
  rw [Fin.le_def] at h₀ h₂
  omega

private lemma upperSection_mem (hlast : n < (x (Fin.last d) : ℕ)) :
    stdSimplex.objMk (n := ⦋d⦌) (m := op ⦋m⦌) (upperSection x) ∈
      (joinFiber ((splitData n m).precomp (yonedaEquiv.symm x)).p 1).obj _ := by
  refine (mem_joinFiber_iff _ _ _).2 fun t ↦ ?_
  rw [stdSimplex.hom_app_apply, yonedaEquiv_splitData_precomp_p, stdSimplex.objMk_apply]
  have := le_apply_upperSection x t
  exact ite_eq_right (by omega)

variable {x}

/-- If a simplex `x` of `Δ[n + m + 1]` misses a vertex `j ≤ n`, so does every face of its part in
`Δ[n]`. -/
private lemma notMem_range_left {j : Fin (n + m + 2)} (hjn : (j : ℕ) ≤ n) (hjx : j ∉ Set.range x)
    {a : ℕ} (y : Δ[d] _⦋a⦌)
    (hy : y ∈ (joinFiber ((splitData n m).precomp (yonedaEquiv.symm x)).p 0).obj _) :
    ⟨j, by omega⟩ ∉ Set.range (((splitData n m).precomp (yonedaEquiv.symm x)).left.app _ ⟨y, hy⟩) :=
  fun ⟨t, ht⟩ ↦ hjx ⟨y t, Fin.ext (by rw [← splitData_precomp_left_app_apply x y hy t, ht])⟩

/-- If a simplex `x` of `Δ[n + m + 1]` misses a vertex `j > n`, so does every face of its part in
`Δ[m]`, at `j - (n + 1)`. -/
private lemma notMem_range_right {j : Fin (n + m + 2)} (hjn : n < j) (hjx : j ∉ Set.range x)
    {a : ℕ} (y : Δ[d] _⦋a⦌)
    (hy : y ∈ (joinFiber ((splitData n m).precomp (yonedaEquiv.symm x)).p 1).obj _) :
    ⟨j - (n + 1), by omega⟩ ∉
      Set.range (((splitData n m).precomp (yonedaEquiv.symm x)).right.app _ ⟨y, hy⟩) := by
  rintro ⟨t, ht⟩
  have h := splitData_precomp_right_app_apply x y hy t
  have := lt_of_mem_joinFiber_one x hy t
  rw [ht] at h
  exact hjx ⟨y t, Fin.ext (by simp only at h; omega)⟩

/-- If a simplex `x` of `Δ[n + m + 1]` with first vertex at most `n` hits a vertex `j ≤ n`, the part
in `Δ[n]` of a face of `x` hits `j`. -/
private lemma mem_range_left (h₀ : (x 0 : ℕ) ≤ n) {j : Fin (n + 1)} {t : Fin (d + 1)}
    (ht : (x t : ℕ) = j) :
    j ∈ Set.range (((splitData n m).precomp (yonedaEquiv.symm x)).left.app _
      ⟨_, lowerSection_mem x h₀⟩) :=
  ⟨j, Fin.ext (by rw [splitData_precomp_left_app_apply, stdSimplex.objMk_apply,
    apply_lowerSection_eq x ht])⟩

/-- If a simplex `x` of `Δ[n + m + 1]` with last vertex above `n` hits a vertex `n + 1 + j`, the
part in `Δ[m]` of a face of `x` hits `j`. -/
private lemma mem_range_right (hlast : n < (x (Fin.last d) : ℕ)) {j : Fin (m + 1)}
    {t : Fin (d + 1)} (ht : (x t : ℕ) = n + 1 + j) :
    j ∈ Set.range (((splitData n m).precomp (yonedaEquiv.symm x)).right.app _
      ⟨_, upperSection_mem x hlast⟩) :=
  ⟨j, Fin.ext (by rw [splitData_precomp_right_app_apply, stdSimplex.objMk_apply,
    apply_upperSection_eq x ht]; omega)⟩

/-- If a simplex `x` of `Δ[n + m + 1]` hits a vertex `j ≤ n`, its first vertex is at most `n`. -/
private lemma apply_zero_le {j : Fin (n + m + 2)} (hjn : (j : ℕ) ≤ n) (hjx : j ∈ Set.range x) :
    (x 0 : ℕ) ≤ n := by
  obtain ⟨t, rfl⟩ := hjx
  have h : x 0 ≤ x t := stdSimplex.monotone_apply x (Fin.zero_le t)
  exact (Fin.le_def.1 h).trans hjn

/-- If a simplex `x` of `Δ[n + m + 1]` hits a vertex `j > n`, its last vertex is above `n`. -/
private lemma lt_apply_last {j : Fin (n + m + 2)} (hjn : n < (j : ℕ)) (hjx : j ∈ Set.range x) :
    n < (x (Fin.last d) : ℕ) := by
  obtain ⟨t, rfl⟩ := hjx
  have h : x t ≤ x (Fin.last d) := stdSimplex.monotone_apply x (Fin.le_last t)
  exact hjn.trans_le (Fin.le_def.1 h)

variable (x) in
/-- A simplex `x` of `Δ[n + m + 1]` lies in the horn `Λ[n + m + 1, i]`, for `i ≤ n` and `n ≠ 0`,
exactly when its image in `Δ[n] ⋆ Δ[m]` has its part in `Δ[n]` in `Λ[n, i]` or its part in `Δ[m]`
in `∂Δ[m]`. -/
private lemma mem_horn_castLE_iff (hn : n ≠ 0) (i : Fin (n + 1)) :
    x ∈ Λ[n + m + 1, Fin.castLE (by omega) i].obj _ ↔
      (stdSimplexIso n m).inv.app _ x ∈ (Subcomplex.unionJoin Λ[n, i] ∂Δ[m]).obj _ := by
  rw [Subcomplex.mem_unionJoin_iff, objEquiv_stdSimplexIso_inv_app, mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨j, hji, hjx⟩
    by_cases hjn : (j : ℕ) ≤ n
    · refine Or.inl fun k y hy ↦ ?_
      induction k using Opposite.rec with | op k
      induction k using SimplexCategory.rec with | _ a
      exact (mem_horn_iff_notMem_range _ _).2 ⟨_, fun h ↦ hji (Fin.ext (by
        rw [Fin.val_castLE, ← h])), notMem_range_left hjn hjx y hy⟩
    · refine Or.inr fun k y hy ↦ ?_
      induction k using Opposite.rec with | op k
      induction k using SimplexCategory.rec with | _ a
      exact (mem_boundary_iff_notMem_range _).2 ⟨_, notMem_range_right (by omega) hjx y hy⟩
  · intro h
    by_contra hx
    have hx' (j : Fin (n + m + 2)) (hj : (j : ℕ) ≠ i) : j ∈ Set.range x := by
      by_contra hjx
      exact hx ⟨j, fun h ↦ hj (by rw [h, Fin.val_castLE]), hjx⟩
    rcases h with h | h
    · -- The first vertex of `x` is at most `n`, since `x` hits a vertex `0` or `1` other than `i`.
      obtain ⟨a, han, hai⟩ : ∃ a : ℕ, a ≤ n ∧ a ≠ i :=
        ⟨if (i : ℕ) = 0 then 1 else 0, by split_ifs <;> omega, by split_ifs <;> omega⟩
      have h₀ := apply_zero_le (j := ⟨a, by omega⟩) han (hx' _ hai)
      obtain ⟨j, hji, hj⟩ := (mem_horn_iff_notMem_range _ _).1 (h _ _ (lowerSection_mem x h₀))
      obtain ⟨t, ht⟩ := hx' (Fin.castLE (by omega) j) (by simpa [Fin.ext_iff] using hji)
      exact hj (mem_range_left h₀ (by rw [ht, Fin.val_castLE]))
    · have hlast := lt_apply_last (j := Fin.last _) (by simp) (hx' _ (by simp; omega))
      obtain ⟨j, hj⟩ := (mem_boundary_iff_notMem_range _).1 (h _ _ (upperSection_mem x hlast))
      obtain ⟨t, ht⟩ := hx' ⟨n + 1 + j, by omega⟩ (by simp only; omega)
      exact hj (mem_range_right hlast (by rw [ht]))

variable (x) in
/-- A simplex `x` of `Δ[n + m + 1]` lies in the horn `Λ[n + m + 1, n + 1 + j]`, for `j ≤ m` and
`m ≠ 0`, exactly when its image in `Δ[n] ⋆ Δ[m]` has its part in `Δ[n]` in `∂Δ[n]` or its part in
`Δ[m]` in `Λ[m, j]`. -/
private lemma mem_horn_natAdd_iff (hm : m ≠ 0) (j : Fin (m + 1)) :
    x ∈ Λ[n + m + 1, Fin.cast (by omega) (Fin.natAdd (n + 1) j)].obj _ ↔
      (stdSimplexIso n m).inv.app _ x ∈ (Subcomplex.unionJoin ∂Δ[n] Λ[m, j]).obj _ := by
  rw [Subcomplex.mem_unionJoin_iff, objEquiv_stdSimplexIso_inv_app, mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨l, hlj, hlx⟩
    by_cases hln : (l : ℕ) ≤ n
    · refine Or.inl fun k y hy ↦ ?_
      induction k using Opposite.rec with | op k
      induction k using SimplexCategory.rec with | _ a
      exact (mem_boundary_iff_notMem_range _).2 ⟨_, notMem_range_left hln hlx y hy⟩
    · refine Or.inr fun k y hy ↦ ?_
      induction k using Opposite.rec with | op k
      induction k using SimplexCategory.rec with | _ a
      exact (mem_horn_iff_notMem_range _ _).2 ⟨_, fun h ↦ hlj (Fin.ext (by
        rw [Fin.val_cast, Fin.val_natAdd, ← h]; simp only; omega)),
        notMem_range_right (by omega) hlx y hy⟩
  · intro h
    by_contra hx
    have hx' (l : Fin (n + m + 2)) (hl : (l : ℕ) ≠ n + 1 + j) : l ∈ Set.range x := by
      by_contra hlx
      exact hx ⟨l, fun h ↦ hl (by rw [h, Fin.val_cast, Fin.val_natAdd]), hlx⟩
    rcases h with h | h
    · have h₀ := apply_zero_le (j := 0) (by simp) (hx' 0 (by simp; omega))
      obtain ⟨l, hl⟩ := (mem_boundary_iff_notMem_range _).1 (h _ _ (lowerSection_mem x h₀))
      obtain ⟨t, ht⟩ := hx' (Fin.castLE (by omega) l) (by simp only [Fin.val_castLE]; omega)
      exact hl (mem_range_left h₀ (by rw [ht, Fin.val_castLE]))
    · -- The last vertex of `x` is above `n`, since `x` hits a vertex `n + 1` or `n + 2` other than
      -- `n + 1 + j`.
      obtain ⟨a, ham, haj⟩ : ∃ a : ℕ, a ≤ m ∧ a ≠ j :=
        ⟨if (j : ℕ) = 0 then 1 else 0, by split_ifs <;> omega, by split_ifs <;> omega⟩
      have hlast := lt_apply_last (j := ⟨n + 1 + a, by omega⟩) (by simp only; omega)
        (hx' _ (by simp only; omega))
      obtain ⟨l, hlj, hl⟩ := (mem_horn_iff_notMem_range _ _).1 (h _ _ (upperSection_mem x hlast))
      obtain ⟨t, ht⟩ := hx' ⟨n + 1 + l, by omega⟩ (by simpa [Fin.ext_iff] using hlj)
      exact hl (mem_range_right hlast (by rw [ht]))

end horn

variable (m) in
/-- **The pushout-join of a horn and a boundary is a horn.** Under `Δ[n] ⋆ Δ[m] ≅ Δ[n + m + 1]`, the
subcomplex `(Λ[n, i] ⋆ Δ[m]) ∪ (Δ[n] ⋆ ∂Δ[m])` of `Δ[n] ⋆ Δ[m]` corresponds to the horn
`Λ[n + m + 1, i]`, for `n ≠ 0` and every `i ≤ n`. -/
theorem preimage_unionJoin_horn_boundary (hn : n ≠ 0) (i : Fin (n + 1)) :
    (Subcomplex.unionJoin Λ[n, i] ∂Δ[m]).preimage (stdSimplexIso n m).inv =
      Λ[n + m + 1, Fin.castLE (by omega) i] := by
  ext ⟨k⟩ x
  induction k using SimplexCategory.rec with | _ d
  rw [Subcomplex.preimage_obj, Set.mem_preimage, mem_horn_castLE_iff x hn i]

variable (n) in
/-- **The pushout-join of a boundary and a horn is a horn.** Under `Δ[n] ⋆ Δ[m] ≅ Δ[n + m + 1]`, the
subcomplex `(∂Δ[n] ⋆ Δ[m]) ∪ (Δ[n] ⋆ Λ[m, j])` of `Δ[n] ⋆ Δ[m]` corresponds to the horn
`Λ[n + m + 1, n + 1 + j]`, for `m ≠ 0` and every `j ≤ m`. -/
theorem preimage_unionJoin_boundary_horn (hm : m ≠ 0) (j : Fin (m + 1)) :
    (Subcomplex.unionJoin ∂Δ[n] Λ[m, j]).preimage (stdSimplexIso n m).inv =
      Λ[n + m + 1, Fin.cast (by omega) (Fin.natAdd (n + 1) j)] := by
  ext ⟨k⟩ x
  induction k using SimplexCategory.rec with | _ d
  rw [Subcomplex.preimage_obj, Set.mem_preimage, mem_horn_natAdd_iff x hm j]

variable (m) in
/-- **The pushout-join of a horn `Λ[n, i]` with `0 < i` and a boundary is inner anodyne**: the
inclusion of `(Λ[n, i] ⋆ Δ[m]) ∪ (Δ[n] ⋆ ∂Δ[m])` into `Δ[n] ⋆ Δ[m]` is isomorphic to the inner horn
inclusion `Λ[n + m + 1, i] ⟶ Δ[n + m + 1]`. -/
theorem innerAnodyneExtensions_unionJoin_horn_boundary {i : Fin (n + 1)} (hi : 0 < i) :
    innerAnodyneExtensions (Subcomplex.unionJoin Λ[n, i] ∂Δ[m]).ι := by
  have hi' : 0 < (i : ℕ) := Fin.lt_def.1 hi
  refine (Subcomplex.morphismProperty_ι_iff_of_preimage_eq _ (stdSimplexIso n m)
    (preimage_unionJoin_horn_boundary m (by omega) i)).2 ?_
  exact innerAnodyneExtensions.horn_ι (Fin.lt_def.2 (by rw [Fin.val_castLE]; exact hi'))
    (Fin.lt_def.2 (by rw [Fin.val_castLE, Fin.val_last]; omega))

variable (n) in
/-- **The pushout-join of a boundary and a horn `Λ[m, j]` with `j < m` is inner anodyne**: the
inclusion of `(∂Δ[n] ⋆ Δ[m]) ∪ (Δ[n] ⋆ Λ[m, j])` into `Δ[n] ⋆ Δ[m]` is isomorphic to the inner horn
inclusion `Λ[n + m + 1, n + 1 + j] ⟶ Δ[n + m + 1]`. -/
theorem innerAnodyneExtensions_unionJoin_boundary_horn {j : Fin (m + 1)} (hj : j < Fin.last m) :
    innerAnodyneExtensions (Subcomplex.unionJoin ∂Δ[n] Λ[m, j]).ι := by
  have hj' : (j : ℕ) < m := by rwa [Fin.lt_def, Fin.val_last] at hj
  refine (Subcomplex.morphismProperty_ι_iff_of_preimage_eq _ (stdSimplexIso n m)
    (preimage_unionJoin_boundary_horn n (by omega) j)).2 ?_
  exact innerAnodyneExtensions.horn_ι
    (Fin.lt_def.2 (by rw [Fin.val_cast, Fin.val_natAdd, Fin.val_zero]; omega))
    (Fin.lt_def.2 (by rw [Fin.val_cast, Fin.val_natAdd, Fin.val_last]; omega))

end join

end SSet
