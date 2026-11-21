/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The square as a cone and as a cocone

The square `Δ[1] ⊗ Δ[1]` is the cone `Δ[0] ⋆ Λ[2, 2]` on the cospan `Λ[2, 2]`, with cone point the
initial vertex `(0, 0)`, and it is the cocone `Λ[2, 0] ⋆ Δ[0]` on the span `Λ[2, 0]`, with cone
point the final vertex `(1, 1)`. These identifications are how a square in a quasicategory is read
as a cone over a cospan, to ask whether it is a pullback square, and as a cocone under a span, to
ask whether it is a pushout square.

All three simplicial sets embed into `Δ[3]` as the union of the faces opposite to the vertices
`1` and `2`: the square through `(a, b) ↦ a + 2 b`, the cone through `Δ[0] ⋆ Δ[2] ≅ Δ[3]` and
the cocone through `Δ[2] ⋆ Δ[0] ≅ Δ[3]`.

## Main definitions

* `SSet.square.coneIso`: the isomorphism `Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]`.
* `SSet.square.coconeIso`: the isomorphism `Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]`.

## Main results

* `SSet.square.inl_comp_coneIso_hom`, `SSet.square.ι_zero_comp_inr_comp_coneIso_hom`,
  `SSet.square.ι_one_comp_inr_comp_coneIso_hom`: the cone point is the vertex `(0, 0)`, and the
  edges of the cospan from `1` and from `0` to `2` are the edges of the square from `(0, 1)` and
  from `(1, 0)` to `(1, 1)`.
* `SSet.square.inr_comp_coconeIso_hom`, `SSet.square.ι_two_comp_inl_comp_coconeIso_hom`,
  `SSet.square.ι_one_comp_inl_comp_coconeIso_hom`: the cone point is the vertex `(1, 1)`, and the
  edges of the span from `0` to `1` and to `2` are the edges of the square from `(0, 0)` to
  `(1, 0)` and to `(0, 1)`.

## Implementation notes

The three embeddings into `Δ[3]` are monomorphisms with the same image, which gives the
isomorphisms (`SSet.Subcomplex.isoOfRangeEq`). The image of the cone contains the two faces
because the cone on a face of `Λ[2, 2]` is a face of `Δ[3]`; it contains nothing else because a
simplex of the cone meeting both `1` and `2` would contain an edge of `Λ[2, 2]` from `0` to `1`,
and dually for the cocone.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.8 and §4.4.2.
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SSet

namespace square

/-! ### The square inside `Δ[3]` -/

/-- The vertex `(a, b)` of the square is the vertex `a + 2 b` of `Δ[3]`. -/
private def vertexMap : Fin 2 × Fin 2 →o Fin 4 where
  toFun x := ⟨x.1 + 2 * x.2, by omega⟩
  monotone' x y h := by
    simp only [Prod.le_def, Fin.le_def] at h
    simp only [Fin.le_def]
    omega

private lemma val_vertexMap (x : Fin 2 × Fin 2) : (vertexMap x : ℕ) = x.1 + 2 * x.2 :=
  (rfl)

private lemma vertexMap_injective : Function.Injective vertexMap := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' := congrArg Fin.val h
  rw [val_vertexMap, val_vertexMap] at h'
  ext <;> simp only at h' ⊢ <;> omega

/-- The embedding of the square into `Δ[3]`, sending `(a, b)` to `a + 2 b`. -/
private noncomputable def toStdSimplex : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[3] :=
  (prodStdSimplex.isoNerve 1 1).hom ≫
    nerveMap (Monotone.functor
      (f := fun x : ULift.{u} (Fin 2 × Fin 2) ↦ ULift.up (vertexMap x.down))
      fun _ _ h ↦ vertexMap.monotone h) ≫ (stdSimplex.isoNerve 3).inv

-- Each of the three maps composing `toStdSimplex` acts on a simplex by composing its vertex map
-- with a monotone map: the nerve isomorphisms are identities on vertex maps and `nerveMap` composes
-- with `vertexMap`. The vertex formula therefore holds by definitional unfolding, which is the
-- intended route; the same holds for `yonedaEquiv_lift_comp_toStdSimplex_apply` below.
private lemma toStdSimplex_app_apply {n : ℕ} (x : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) :
    toStdSimplex.app _ x i = vertexMap (prodStdSimplex.objEquiv x i) :=
  (rfl)

private instance : Mono (toStdSimplex.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨n⟩
  induction n using SimplexCategory.rec with | _ n
  rw [mono_iff_injective]
  intro x y h
  apply prodStdSimplex.objEquiv.injective
  refine OrderHom.ext _ _ (funext fun i ↦ vertexMap_injective ?_)
  have h' := congrArg (fun z : (Δ[3] : SSet.{u}) _⦋n⦌ ↦ z i) h
  simpa only [toStdSimplex_app_apply] using h'

/-- The union of the faces of `Δ[3]` opposite to the vertices `1` and `2`. -/
private def image : (Δ[3] : SSet.{u}).Subcomplex :=
  stdSimplex.face {1}ᶜ ⊔ stdSimplex.face {2}ᶜ

private lemma mem_image_iff {n : ℕ} (x : (Δ[3] : SSet.{u}) _⦋n⦌) :
    x ∈ image.obj _ ↔ (∀ i, x i ≠ 1) ∨ ∀ i, x i ≠ 2 := by
  simp [image]

/-- A map to `Δ[3]` taking no edge to the edge from `1` to `2` has its range in the union of the
faces opposite to `1` and to `2`: a simplex meeting both `1` and `2` would contain that edge. -/
private lemma range_le_image {Y : SSet.{u}} (f : Y ⟶ Δ[3])
    (hf : ∀ s : Y _⦋1⦌, f.app _ s ≠ stdSimplex.edge 3 1 2 (by decide)) :
    Subcomplex.range f ≤ image := by
  rintro ⟨n⟩ x ⟨s, rfl⟩
  induction n using SimplexCategory.rec with | _ n
  rw [mem_image_iff]
  by_contra! h
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
  have hij : i ≤ j := by
    by_contra! hji
    have := stdSimplex.monotone_apply (f.app _ s) hji.le
    dsimp only at this
    rw [hi, hj] at this
    exact absurd this (by decide)
  exact hf (Y.map (SimplexCategory.mkOfLe i j hij).op s)
    (stdSimplex.ext _ _ fun t ↦ by
      rw [NatTrans.naturality_apply]
      fin_cases t
      · exact hi
      · exact hj)

private lemma range_toStdSimplex : Subcomplex.range toStdSimplex.{u} = image := by
  ext ⟨n⟩ x
  induction n using SimplexCategory.rec with | _ n
  constructor
  · rintro ⟨y, rfl⟩
    rw [mem_image_iff]
    by_contra! h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    rw [toStdSimplex_app_apply] at hi hj
    have hmono := (prodStdSimplex.objEquiv y).monotone
    rcases le_total i j with hij | hij <;>
    · have := hmono hij
      simp only [Fin.ext_iff, val_vertexMap, Prod.le_def, Fin.le_def] at hi hj this
      omega
  · intro hx
    rw [mem_image_iff] at hx
    -- The vertex `k` of `Δ[3]` is the vertex `(k mod 2, k / 2)` of the square.
    let f : Fin (n + 1) →o Fin 2 × Fin 2 :=
      { toFun i := (⟨x i % 2, by omega⟩, ⟨x i / 2, by omega⟩)
        monotone' i j hij := by
          have h := stdSimplex.monotone_apply x hij
          simp only [Prod.mk_le_mk, Fin.le_def] at h ⊢
          rcases hx with hx | hx
          · have hi : (x i : ℕ) ≠ 1 := fun h ↦ hx i (Fin.ext h)
            have hj : (x j : ℕ) ≠ 1 := fun h ↦ hx j (Fin.ext h)
            omega
          · have hj : (x j : ℕ) ≠ 2 := fun h ↦ hx j (Fin.ext h)
            omega }
    refine ⟨(prodStdSimplex.objEquiv.symm f : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋n⦌),
      stdSimplex.ext _ _ fun i ↦ ?_⟩
    refine (toStdSimplex_app_apply _ i).trans (Fin.ext ?_)
    rw [val_vertexMap]
    exact Nat.mod_add_div _ _

/-! ### The cone `Δ[0] ⋆ Λ[2, 2]` inside `Δ[3]` -/

/-- The embedding of the cone `Δ[0] ⋆ Λ[2, 2]` into `Δ[0] ⋆ Δ[2] ≅ Δ[3]`. -/
private noncomputable def coneMap : join Δ[0] (Λ[2, 2] : SSet.{u}) ⟶ Δ[3] :=
  join.map (𝟙 _) Λ[2, 2].ι ≫ (join.stdSimplexIso 0 2).hom

private instance : Mono (coneMap.{u}) := by
  unfold coneMap
  infer_instance

/-- A simplex of the cone all of whose vertices go to vertices other than `0` of `Δ[3]` lies in
the cospan `Λ[2, 2]`. -/
private lemma mem_joinFiber_one_of_coneMap {n : ℕ} (s : (join Δ[0] (Λ[2, 2] : SSet.{u})) _⦋n⦌)
    (h : ∀ t, coneMap.app _ s t ≠ 0) : s ∈ (joinFiber (join.univ _ _).p 1).obj _ := by
  rw [mem_joinFiber_iff, join.univ_p]
  intro t
  have hπ : join.π Δ[0] (Λ[2, 2] : SSet.{u}) =
      coneMap ≫ (join.stdSimplexIso 0 2).inv ≫ join.π _ _ := by
    simp [coneMap, join.map_π]
  have key : (join.π _ _).app _ s =
      ((join.stdSimplexIso 0 2).inv ≫ join.π _ _).app _ (coneMap.app _ s) := by
    rw [hπ, NatTrans.comp_app_apply]
  rw [key, stdSimplex.hom_app_apply]
  have ht := h t
  -- `Δ[3]` is `Δ[0 + 2 + 1]` only up to definitional unfolding, so the vertex formula for the
  -- inverse of `stdSimplexIso` is applied by `Eq.trans` rather than by rewriting.
  exact (join.yonedaEquiv_stdSimplexIso_inv_comp_π (n := 0) (m := 2) _).trans
    (ite_eq_right (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero] at ht; omega))

private lemma coneMap_inr_app_apply {n : ℕ} (s : (Λ[2, 2] : SSet.{u}) _⦋n⦌) (t : Fin (n + 1)) :
    (coneMap.app _ ((join.inr _ _).app _ s) t : ℕ) = 1 + s.val t := by
  have h : join.inr Δ[0] (Λ[2, 2] : SSet.{u}) ≫ coneMap =
      Λ[2, 2].ι ≫ join.inr _ _ ≫ (join.stdSimplexIso 0 2).hom := by
    simp [coneMap]
  have key : coneMap.app _ ((join.inr _ _).app _ s) =
      (join.inr Δ[0] Δ[2] ≫ (join.stdSimplexIso 0 2).hom).app _ s.val := by
    rw [← NatTrans.comp_app_apply, h, NatTrans.comp_app_apply, Subfunctor.ι_app,
      TypeCat.ofHom_apply]
  rw [key, stdSimplex.hom_app_apply]
  -- As above, the vertex formula for `stdSimplexIso` is applied by `Eq.trans`.
  exact (congrArg Fin.val (join.yonedaEquiv_inr_comp_stdSimplexIso_hom (n := 0) (m := 2) _)).trans
    (by simp)

/-- No simplex of the cone `Δ[0] ⋆ Λ[2, 2]` goes to the edge of `Δ[3]` from `1` to `2`. -/
private lemma coneMap_app_ne {s : (join Δ[0] (Λ[2, 2] : SSet.{u})) _⦋1⦌}
    (hs : coneMap.app _ s = stdSimplex.edge 3 1 2 (by decide)) : False := by
  have hs' : s ∈ (joinFiber (join.univ _ _).p 1).obj _ :=
    mem_joinFiber_one_of_coneMap s fun t ↦ by fin_cases t <;> simp [hs]
  rw [← join.inr_app_univ_right_app s hs'] at hs
  set s' := (join.univ _ _).right.app _ ⟨s, hs'⟩
  have h0 := coneMap_inr_app_apply s' 0
  have h1 := coneMap_inr_app_apply s' 1
  rw [hs] at h0 h1
  obtain ⟨j, hj, hjs⟩ := (mem_horn_iff_notMem_range _ _).1 s'.property
  apply hjs
  fin_cases j
  · exact ⟨0, Fin.ext (by simp at h0 ⊢; omega)⟩
  · exact ⟨1, Fin.ext (by simp at h1 ⊢; omega)⟩
  · exact absurd rfl hj

private lemma range_coneMap_le : Subcomplex.range coneMap.{u} ≤ image :=
  range_le_image _ fun _ ↦ coneMap_app_ne

/-- The cone on the face of `Λ[2, 2]` opposite to the vertex `j` is the face of `Δ[3]` opposite to
the vertex `j + 1`. -/
private lemma coneIso_inv_comp_map_ι_comp_coneMap (j : Fin 3) (hj : j ≠ 2) :
    (join.coneIso 1).inv ≫ join.map (𝟙 _) (horn.ι 2 j hj) ≫ coneMap.{u} =
      stdSimplex.map (SimplexCategory.δ j.succ) := by
  have h := join.map_comp_coneIso_hom.{u} (SimplexCategory.δ j)
  rw [join.coneIso_hom_eq 2, eqToHom_refl, Category.comp_id] at h
  rw [Iso.inv_comp_eq, coneMap, ← join.map_comp_assoc, Category.comp_id, horn.ι_ι,
    ← SimplexCategory.vertexJoin_map_δ]
  exact h

private lemma image_le_range_coneMap : image ≤ Subcomplex.range coneMap.{u} := by
  have h (j : Fin 3) (hj : j ≠ 2) :
      stdSimplex.face {j.succ}ᶜ ≤ Subcomplex.range coneMap.{u} := by
    rw [← stdSimplex.ofSimplex_yonedaEquiv_δ, Subcomplex.ofSimplex_le_iff]
    exact ⟨yonedaEquiv ((join.coneIso 1).inv ≫ join.map (𝟙 _) (horn.ι 2 j hj)), by
      rw [← yonedaEquiv_comp, Category.assoc, coneIso_inv_comp_map_ι_comp_coneMap,
        CosimplicialObject.δ]⟩
  exact sup_le (h 0 (by decide)) (h 1 (by decide))

/-! ### The cocone `Λ[2, 0] ⋆ Δ[0]` inside `Δ[3]` -/

/-- The embedding of the cocone `Λ[2, 0] ⋆ Δ[0]` into `Δ[2] ⋆ Δ[0] ≅ Δ[3]`. -/
private noncomputable def coconeMap : join (Λ[2, 0] : SSet.{u}) Δ[0] ⟶ Δ[3] :=
  join.map Λ[2, 0].ι (𝟙 _) ≫ (join.stdSimplexIso 2 0).hom

private instance : Mono (coconeMap.{u}) := by
  unfold coconeMap
  infer_instance

/-- A simplex of the cocone all of whose vertices go to vertices other than `3` of `Δ[3]` lies in
the span `Λ[2, 0]`. -/
private lemma mem_joinFiber_zero_of_coconeMap {n : ℕ}
    (s : (join (Λ[2, 0] : SSet.{u}) Δ[0]) _⦋n⦌) (h : ∀ t, coconeMap.app _ s t ≠ 3) :
    s ∈ (joinFiber (join.univ _ _).p 0).obj _ := by
  rw [mem_joinFiber_iff, join.univ_p]
  intro t
  have hπ : join.π (Λ[2, 0] : SSet.{u}) Δ[0] =
      coconeMap ≫ (join.stdSimplexIso 2 0).inv ≫ join.π _ _ := by
    simp [coconeMap, join.map_π]
  have key : (join.π _ _).app _ s =
      ((join.stdSimplexIso 2 0).inv ≫ join.π _ _).app _ (coconeMap.app _ s) := by
    rw [hπ, NatTrans.comp_app_apply]
  rw [key, stdSimplex.hom_app_apply]
  have ht := h t
  -- `Δ[3]` is `Δ[2 + 0 + 1]` only up to definitional unfolding, so the vertex formula for the
  -- inverse of `stdSimplexIso` is applied by `Eq.trans` rather than by rewriting.
  exact (join.yonedaEquiv_stdSimplexIso_inv_comp_π (n := 2) (m := 0) _).trans
    (ite_eq_left_iff.2 fun h' ↦ absurd (by
      have := (coconeMap.app _ s t).isLt
      rw [Fin.ext_iff]
      simp only [Fin.coe_ofNat_eq_mod]
      omega) ht)

private lemma coconeMap_inl_app_apply {n : ℕ} (s : (Λ[2, 0] : SSet.{u}) _⦋n⦌) (t : Fin (n + 1)) :
    (coconeMap.app _ ((join.inl _ _).app _ s) t : ℕ) = s.val t := by
  have h : join.inl (Λ[2, 0] : SSet.{u}) Δ[0] ≫ coconeMap =
      Λ[2, 0].ι ≫ join.inl _ _ ≫ (join.stdSimplexIso 2 0).hom := by
    simp [coconeMap]
  have key : coconeMap.app _ ((join.inl _ _).app _ s) =
      (join.inl Δ[2] Δ[0] ≫ (join.stdSimplexIso 2 0).hom).app _ s.val := by
    rw [← NatTrans.comp_app_apply, h, NatTrans.comp_app_apply, Subfunctor.ι_app,
      TypeCat.ofHom_apply]
  rw [key, stdSimplex.hom_app_apply]
  -- As above, the vertex formula for `stdSimplexIso` is applied by `Eq.trans`.
  exact (congrArg Fin.val (join.yonedaEquiv_inl_comp_stdSimplexIso_hom (n := 2) (m := 0) _)).trans
    (by simp)

/-- No simplex of the cocone `Λ[2, 0] ⋆ Δ[0]` goes to the edge of `Δ[3]` from `1` to `2`. -/
private lemma coconeMap_app_ne {s : (join (Λ[2, 0] : SSet.{u}) Δ[0]) _⦋1⦌}
    (hs : coconeMap.app _ s = stdSimplex.edge 3 1 2 (by decide)) : False := by
  have hs' : s ∈ (joinFiber (join.univ _ _).p 0).obj _ :=
    mem_joinFiber_zero_of_coconeMap s fun t ↦ by fin_cases t <;> simp [hs]
  rw [← join.inl_app_univ_left_app s hs'] at hs
  set s' := (join.univ _ _).left.app _ ⟨s, hs'⟩
  have h0 := coconeMap_inl_app_apply s' 0
  have h1 := coconeMap_inl_app_apply s' 1
  rw [hs] at h0 h1
  obtain ⟨j, hj, hjs⟩ := (mem_horn_iff_notMem_range _ _).1 s'.property
  apply hjs
  fin_cases j
  · exact absurd rfl hj
  · exact ⟨0, Fin.ext (by simp at h0 ⊢; omega)⟩
  · exact ⟨1, Fin.ext (by simp at h1 ⊢; omega)⟩

private lemma range_coconeMap_le : Subcomplex.range coconeMap.{u} ≤ image :=
  range_le_image _ fun _ ↦ coconeMap_app_ne

/-- The cocone on the face of `Λ[2, 0]` opposite to the vertex `j` is the face of `Δ[3]` opposite
to the vertex `j`. -/
private lemma map_ι_comp_coconeMap (j : Fin 3) (hj : j ≠ 0) :
    join.map (horn.ι 0 j hj) (𝟙 _) ≫ coconeMap.{u} =
      (join.stdSimplexIso 1 0).hom ≫ stdSimplex.map (SimplexCategory.δ j.castSucc) := by
  rw [coconeMap, ← join.map_comp_assoc, Category.comp_id, horn.ι_ι]
  refine join.hom_ext_stdSimplex ?_ ?_
  · rw [join.inl_map_assoc]
    apply yonedaEquiv.injective
    refine stdSimplex.ext _ _ fun t ↦ ?_
    -- The vertex formulas for `stdSimplexIso` are applied by `Eq.trans`, since `Δ[3]` is
    -- `Δ[2 + 0 + 1]` only up to definitional unfolding.
    refine (stdSimplex.yonedaEquiv_comp_apply _ _ t).trans (Eq.trans ?_
      (stdSimplex.yonedaEquiv_comp_apply (join.inl Δ[1] Δ[0] ≫ (join.stdSimplexIso 1 0).hom)
        (stdSimplex.map (SimplexCategory.δ j.castSucc)) t).symm)
    rw [join.yonedaEquiv_inl_comp_stdSimplexIso_hom (n := 2) (m := 0),
      join.yonedaEquiv_inl_comp_stdSimplexIso_hom (n := 1) (m := 0),
      stdSimplex.yonedaEquiv_map_apply]
    fin_cases j <;> fin_cases t <;> rfl
  · rw [join.inr_map_assoc, Category.id_comp]
    apply yonedaEquiv.injective
    refine stdSimplex.ext _ _ fun t ↦ ?_
    refine Eq.trans ?_ (stdSimplex.yonedaEquiv_comp_apply
      (join.inr Δ[1] Δ[0] ≫ (join.stdSimplexIso 1 0).hom)
        (stdSimplex.map (SimplexCategory.δ j.castSucc)) t).symm
    rw [join.yonedaEquiv_inr_comp_stdSimplexIso_hom (n := 2) (m := 0),
      join.yonedaEquiv_inr_comp_stdSimplexIso_hom (n := 1) (m := 0),
      stdSimplex.yonedaEquiv_map_apply]
    fin_cases j <;> fin_cases t <;> rfl

private lemma image_le_range_coconeMap : image ≤ Subcomplex.range coconeMap.{u} := by
  have h (j : Fin 3) (hj : j ≠ 0) :
      stdSimplex.face {j.castSucc}ᶜ ≤ Subcomplex.range coconeMap.{u} := by
    rw [← stdSimplex.ofSimplex_yonedaEquiv_δ, Subcomplex.ofSimplex_le_iff]
    exact ⟨yonedaEquiv ((join.stdSimplexIso 1 0).inv ≫ join.map (horn.ι 0 j hj) (𝟙 _)), by
      rw [← yonedaEquiv_comp, Category.assoc, map_ι_comp_coconeMap, Iso.inv_hom_id_assoc,
        CosimplicialObject.δ]⟩
  exact sup_le (h 1 (by decide)) (h 2 (by decide))

/-! ### The isomorphisms -/

/-- **The square is a cone on a cospan**: `Δ[1] ⊗ Δ[1]` is the cone `Δ[0] ⋆ Λ[2, 2]`, with cone
point the vertex `(0, 0)` (`SSet.square.inl_comp_coneIso_hom`) and with the cospan
`(1, 0) ⟶ (1, 1) ⟵ (0, 1)` as its base (`SSet.square.ι_one_comp_inr_comp_coneIso_hom`,
`SSet.square.ι_zero_comp_inr_comp_coneIso_hom`). -/
noncomputable def coneIso : join Δ[0] (Λ[2, 2] : SSet.{u}) ≅ Δ[1] ⊗ Δ[1] :=
  Subcomplex.isoOfRangeEq coneMap toStdSimplex
    ((le_antisymm range_coneMap_le image_le_range_coneMap).trans range_toStdSimplex.symm)

/-- **The square is a cocone on a span**: `Δ[1] ⊗ Δ[1]` is the cocone `Λ[2, 0] ⋆ Δ[0]`, with cone
point the vertex `(1, 1)` (`SSet.square.inr_comp_coconeIso_hom`) and with the span
`(1, 0) ⟵ (0, 0) ⟶ (0, 1)` as its base (`SSet.square.ι_two_comp_inl_comp_coconeIso_hom`,
`SSet.square.ι_one_comp_inl_comp_coconeIso_hom`). -/
noncomputable def coconeIso : join (Λ[2, 0] : SSet.{u}) Δ[0] ≅ Δ[1] ⊗ Δ[1] :=
  Subcomplex.isoOfRangeEq coconeMap toStdSimplex
    ((le_antisymm range_coconeMap_le image_le_range_coconeMap).trans range_toStdSimplex.symm)

private lemma coneIso_hom_comp_toStdSimplex : coneIso.{u}.hom ≫ toStdSimplex = coneMap :=
  Subcomplex.isoOfRangeEq_hom_comp _ _ _

private lemma coconeIso_hom_comp_toStdSimplex : coconeIso.{u}.hom ≫ toStdSimplex = coconeMap :=
  Subcomplex.isoOfRangeEq_hom_comp _ _ _

private lemma yonedaEquiv_lift_comp_toStdSimplex_apply {n : ℕ} (f g : Δ[n] ⟶ (Δ[1] : SSet.{u}))
    (t : Fin (n + 1)) :
    yonedaEquiv (CartesianMonoidalCategory.lift f g ≫ toStdSimplex) t =
      vertexMap (yonedaEquiv f t, yonedaEquiv g t) :=
  (rfl)

private lemma inl_comp_coneMap :
    join.inl _ _ ≫ coneMap.{u} = stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ 0) := by
  rw [coneMap, join.inl_map_assoc, Category.id_comp, join.inl_comp_stdSimplexIso_hom]

private lemma inr_comp_coneMap : join.inr _ _ ≫ coneMap.{u} = Λ[2, 2].ι ≫ stdSimplex.δ 0 := by
  rw [coneMap, join.inr_map_assoc, ← join.inr_comp_coneIso_hom, join.coneIso_hom_eq,
    eqToHom_refl, Category.comp_id]

private lemma inl_comp_coconeMap : join.inl _ _ ≫ coconeMap.{u} =
    Λ[2, 0].ι ≫ join.inl _ _ ≫ (join.stdSimplexIso 2 0).hom := by
  rw [coconeMap, join.inl_map_assoc]

private lemma inr_comp_coconeMap : join.inr _ _ ≫ coconeMap.{u} =
    join.inr _ _ ≫ (join.stdSimplexIso 2 0).hom := by
  rw [coconeMap, join.inr_map_assoc, Category.id_comp]

/-- The cone point of `Δ[0] ⋆ Λ[2, 2]` is the vertex `(0, 0)` of the square. -/
@[reassoc (attr := simp)]
lemma inl_comp_coneIso_hom : join.inl _ _ ≫ coneIso.{u}.hom =
    CartesianMonoidalCategory.lift (stdSimplex.δ 1) (stdSimplex.δ 1) := by
  rw [← cancel_mono toStdSimplex, Category.assoc, coneIso_hom_comp_toStdSimplex, inl_comp_coneMap]
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun t ↦ ?_
  rw [yonedaEquiv_lift_comp_toStdSimplex_apply, stdSimplex.yonedaEquiv_map_apply]
  fin_cases t
  rfl

/-- The edge of the cospan `Λ[2, 2]` from `1` to `2` is the edge of the square from `(0, 1)` to
`(1, 1)`. -/
@[reassoc (attr := simp)]
lemma ι_zero_comp_inr_comp_coneIso_hom :
    horn.ι 2 0 (by decide) ≫ join.inr _ _ ≫ coneIso.{u}.hom =
      CartesianMonoidalCategory.lift (𝟙 Δ[1]) (const (stdSimplex.const 1 1 _)) := by
  rw [← cancel_mono toStdSimplex, Category.assoc, Category.assoc, coneIso_hom_comp_toStdSimplex,
    inr_comp_coneMap, horn.ι_ι_assoc]
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun t ↦ ?_
  rw [yonedaEquiv_lift_comp_toStdSimplex_apply, stdSimplex.yonedaEquiv_comp_apply]
  fin_cases t <;> rfl

/-- The edge of the cospan `Λ[2, 2]` from `0` to `2` is the edge of the square from `(1, 0)` to
`(1, 1)`. -/
@[reassoc (attr := simp)]
lemma ι_one_comp_inr_comp_coneIso_hom :
    horn.ι 2 1 (by decide) ≫ join.inr _ _ ≫ coneIso.{u}.hom =
      CartesianMonoidalCategory.lift (const (stdSimplex.const 1 1 _)) (𝟙 Δ[1]) := by
  rw [← cancel_mono toStdSimplex, Category.assoc, Category.assoc, coneIso_hom_comp_toStdSimplex,
    inr_comp_coneMap, horn.ι_ι_assoc]
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun t ↦ ?_
  rw [yonedaEquiv_lift_comp_toStdSimplex_apply, stdSimplex.yonedaEquiv_comp_apply]
  fin_cases t <;> rfl

/-- The cone point of `Λ[2, 0] ⋆ Δ[0]` is the vertex `(1, 1)` of the square. -/
@[reassoc (attr := simp)]
lemma inr_comp_coconeIso_hom : join.inr _ _ ≫ coconeIso.{u}.hom =
    CartesianMonoidalCategory.lift (stdSimplex.δ 0) (stdSimplex.δ 0) := by
  rw [← cancel_mono toStdSimplex, Category.assoc, coconeIso_hom_comp_toStdSimplex,
    inr_comp_coconeMap]
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun t ↦ ?_
  rw [yonedaEquiv_lift_comp_toStdSimplex_apply]
  -- `Δ[3]` is `Δ[2 + 0 + 1]` only up to definitional unfolding, so the vertex formula for
  -- `stdSimplexIso` is applied by `Eq.trans`.
  refine (join.yonedaEquiv_inr_comp_stdSimplexIso_hom (n := 2) (m := 0) t).trans ?_
  fin_cases t
  rfl

/-- The edge of the span `Λ[2, 0]` from `0` to `1` is the edge of the square from `(0, 0)` to
`(1, 0)`. -/
@[reassoc (attr := simp)]
lemma ι_two_comp_inl_comp_coconeIso_hom :
    horn.ι 0 2 (by decide) ≫ join.inl _ _ ≫ coconeIso.{u}.hom =
      CartesianMonoidalCategory.lift (𝟙 Δ[1]) (const (stdSimplex.const 1 0 _)) := by
  rw [← cancel_mono toStdSimplex, Category.assoc, Category.assoc, coconeIso_hom_comp_toStdSimplex,
    inl_comp_coconeMap, horn.ι_ι_assoc]
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun t ↦ ?_
  rw [yonedaEquiv_lift_comp_toStdSimplex_apply, stdSimplex.yonedaEquiv_comp_apply]
  -- As above, the vertex formula for `stdSimplexIso` is applied by `Eq.trans`.
  refine (join.yonedaEquiv_inl_comp_stdSimplexIso_hom (n := 2) (m := 0) _).trans ?_
  fin_cases t <;> rfl

/-- The edge of the span `Λ[2, 0]` from `0` to `2` is the edge of the square from `(0, 0)` to
`(0, 1)`. -/
@[reassoc (attr := simp)]
lemma ι_one_comp_inl_comp_coconeIso_hom :
    horn.ι 0 1 (by decide) ≫ join.inl _ _ ≫ coconeIso.{u}.hom =
      CartesianMonoidalCategory.lift (const (stdSimplex.const 1 0 _)) (𝟙 Δ[1]) := by
  rw [← cancel_mono toStdSimplex, Category.assoc, Category.assoc, coconeIso_hom_comp_toStdSimplex,
    inl_comp_coconeMap, horn.ι_ι_assoc]
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun t ↦ ?_
  rw [yonedaEquiv_lift_comp_toStdSimplex_apply, stdSimplex.yonedaEquiv_comp_apply]
  refine (join.yonedaEquiv_inl_comp_stdSimplexIso_hom (n := 2) (m := 0) _).trans ?_
  fin_cases t <;> rfl

end square

end SSet
