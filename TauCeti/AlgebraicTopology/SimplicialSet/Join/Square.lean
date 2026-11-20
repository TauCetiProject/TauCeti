/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplex.Basic

/-!
# The square as a cone and as a cocone

The square `Δ[1] ⊗ Δ[1]` has four vertices `(a, b)` and two nondegenerate `2`-simplices
`(0, 0) ⟶ (1, 0) ⟶ (1, 1)` and `(0, 0) ⟶ (0, 1) ⟶ (1, 1)`. It is the cone, with cone point
`(0, 0)`, on its cospan `(1, 0) ⟶ (1, 1) ⟵ (0, 1)`, which is the horn `Λ[2, 2]`, and the cocone,
with cone point `(1, 1)`, under its span `(1, 0) ⟵ (0, 0) ⟶ (0, 1)`, which is the horn `Λ[2, 0]`:

* `SSet.join.coneHornIso : Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]` sends the cone point to `(0, 0)` and the
  vertices `0`, `1`, `2` of the horn to `(1, 0)`, `(0, 1)`, `(1, 1)`;
* `SSet.join.hornConeIso : Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]` sends the vertices `0`, `1`, `2` of the
  horn to `(0, 0)`, `(1, 0)`, `(0, 1)` and the cone point to `(1, 1)`.

These isomorphisms are fixed by their values on vertices
(`SSet.join.objEquiv_coneHornIso_hom_app_inl`, `SSet.join.objEquiv_coneHornIso_hom_app_inr`,
`SSet.join.objEquiv_hornConeIso_hom_app_inl`, `SSet.join.objEquiv_hornConeIso_hom_app_inr`),
since maps to `Δ[1] ⊗ Δ[1]` are determined by their values on vertices
(`SSet.prodStdSimplex.hom_ext`). They agree on the labelling of the square, and they present a
square `Δ[1] ⊗ Δ[1] ⟶ C` as a cone over a cospan and as a cocone under a span: this is how pullback
and pushout squares in a quasicategory are defined.

## Implementation notes

Both joins and the square are identified with the same subcomplex of `Δ[3]`: the simplices that
miss the vertex `1` or the vertex `2`, that is, the union of the faces opposite to `1` and `2`. The
square embeds in `Δ[3]` by sending `(a, b)` to `a + 2 b`; the joins embed in `Δ[0] ⋆ Δ[2] ≅ Δ[3]`
and in `Δ[2] ⋆ Δ[0] ≅ Δ[3]` (`SSet.join.coneIso`, `SSet.join.stdSimplexIso`). The two faces lie in
the image of each join, being joins of faces of `Δ[2]` lying in the horn. Conversely, a simplex of
`Δ[3]` hitting both `1` and `2` has the edge from `1` to `2` as a face, and no edge of either join
is sent to this edge: it would be an edge of the horn from `0` to `1` (respectively from `1` to
`2`), or an edge from (respectively to) the cone point.

## References

* J. Lurie, *Higher Topos Theory*, §4.4.2, where pullback and pushout squares are the limit cones
  `Δ[0] ⋆ Λ[2, 2] ⟶ C` and the colimit cocones `Λ[2, 0] ⋆ Δ[0] ⟶ C`.
-/

public section

open CategoryTheory MonoidalCategory Opposite Simplicial

universe u

namespace SSet

namespace prodStdSimplex

/-- The vertex `(a, b)` of the square `Δ[1] ⊗ Δ[1]` as the vertex `a + 2 b` of `Δ[3]`. -/
private def squareVertex (v : Fin 2 × Fin 2) : Fin 4 :=
  ⟨v.1 + 2 * v.2, by omega⟩

private lemma monotone_squareVertex : Monotone squareVertex := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨ha, hb⟩
  simp only [squareVertex, Fin.le_def] at ha hb ⊢
  omega

/-- The embedding of the square `Δ[1] ⊗ Δ[1]` in `Δ[3]` sending the vertex `(a, b)` to `a + 2 b`.
-/
private def toStdSimplexThree : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[3] :=
  (isoNerve 1 1).hom ≫
    nerveMap (ULift.orderIso.symm.monotone.comp
      (monotone_squareVertex.comp ULift.orderIso.monotone)).functor ≫
    (stdSimplex.isoNerve 3).inv

private lemma toStdSimplexThree_app_apply {d : ℕ} (x : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋d⦌)
    (i : Fin (d + 1)) : toStdSimplexThree.app _ x i = squareVertex (objEquiv x i) :=
  rfl

private lemma squareVertex_injective : Function.Injective squareVertex := by
  decide

private instance mono_toStdSimplexThree : Mono toStdSimplexThree.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨n⟩
  induction n using SimplexCategory.rec with | _ d
  rw [mono_iff_injective]
  intro x y h
  refine objEquiv.injective (OrderHom.ext _ _ (funext fun i ↦ squareVertex_injective ?_))
  rw [← toStdSimplexThree_app_apply, ← toStdSimplexThree_app_apply]
  exact congrArg (fun s : Δ[3] _⦋d⦌ ↦ s i) h

private lemma inv_toRange_toStdSimplexThree_comp :
    inv (Subcomplex.toRange toStdSimplexThree.{u}) ≫ toStdSimplexThree =
      (Subcomplex.range toStdSimplexThree).ι := by
  rw [IsIso.inv_comp_eq, Subcomplex.toRange_ι]

/-- The vertex of the square `Δ[1] ⊗ Δ[1]` with image `j` in `Δ[3]`. -/
private def squareCorner (j : Fin 4) : Fin 2 × Fin 2 :=
  (⟨j % 2, by omega⟩, ⟨j / 2, by omega⟩)

/-- The square `Δ[1] ⊗ Δ[1]` is the subcomplex of `Δ[3]` of the simplices missing the vertex `1`
or the vertex `2`. -/
private lemma range_toStdSimplexThree :
    Subcomplex.range toStdSimplexThree.{u} =
      stdSimplex.face {1}ᶜ ⊔ stdSimplex.face {2}ᶜ := by
  ext ⟨k⟩ x
  induction k using SimplexCategory.rec with | _ d
  simp only [Subfunctor.range_obj, Set.mem_range, Subfunctor.max_obj, Set.mem_union,
    stdSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    by_contra h
    simp only [not_or, not_forall, not_not] at h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    rw [toStdSimplexThree_app_apply] at hi hj
    have key : ∀ a b : Fin 2 × Fin 2, squareVertex a = 1 → squareVertex b = 2 →
        ¬ a ≤ b ∧ ¬ b ≤ a := by
      decide
    rcases le_total i j with hij | hij
    · exact (key _ _ hi hj).1 ((objEquiv y).monotone hij)
    · exact (key _ _ hi hj).2 ((objEquiv y).monotone hij)
  · intro h
    refine ⟨objEquiv.symm ⟨fun i ↦ squareCorner (x i), fun i j hij ↦ ?_⟩,
      stdSimplex.ext _ _ fun i ↦ ?_⟩
    · have key : ∀ a b : Fin 4, a ≤ b → (a ≠ 1 ∧ b ≠ 1 ∨ a ≠ 2 ∧ b ≠ 2) →
          squareCorner a ≤ squareCorner b := by
        decide
      exact key _ _ (stdSimplex.monotone_apply x hij)
        (h.imp (fun h ↦ ⟨h i, h j⟩) fun h ↦ ⟨h i, h j⟩)
    · -- The image of the vertex `squareCorner (x i)` is `x i`, by `toStdSimplexThree_app_apply`.
      exact (by decide : ∀ a : Fin 4, squareVertex (squareCorner a) = a) (x i)

end prodStdSimplex

namespace join

/-! ### The cone `Δ[0] ⋆ Λ[2, 2]` -/

/-- The embedding `Δ[0] ⋆ Λ[2, 2] ⟶ Δ[0] ⋆ Δ[2] ≅ Δ[3]`. -/
private noncomputable abbrev coneHornToStdSimplex : join Δ[0] (Λ[2, 2] : SSet.{u}) ⟶ Δ[3] :=
  map (𝟙 Δ[0]) Λ[2, 2].ι ≫ (coneIso 2).hom

/-- The faces of `Δ[3]` opposite to the vertices `1` and `2` lie in `Δ[0] ⋆ Λ[2, 2]`: they are the
cones on the faces of `Δ[2]` opposite to the vertices `0` and `1`. -/
private lemma face_le_range_coneHornToStdSimplex (j : Fin 3) (hj : j ≠ 2) :
    stdSimplex.face {j.succ}ᶜ ≤ Subcomplex.range coneHornToStdSimplex.{u} := by
  have hle : Subcomplex.range (stdSimplex.δ j) ≤ Λ[2, 2] := by
    rw [stdSimplex.range_δ]
    exact face_le_horn _ _ hj
  have h : stdSimplex.δ j.succ = (coneIso 1).inv ≫ map (𝟙 Δ[0]) (Subcomplex.lift _ hle) ≫
      coneHornToStdSimplex.{u} := by
    rw [coneHornToStdSimplex, ← map_comp_assoc, Category.id_comp, Subcomplex.lift_ι,
      Iso.eq_inv_comp]
    have := map_comp_coneIso_hom.{u} (SimplexCategory.δ j)
    rw [SimplexCategory.vertexJoin_map_δ] at this
    exact this.symm
  rw [← stdSimplex.range_δ, h, ← Category.assoc]
  exact Subfunctor.range_comp_le _ _

private lemma inl_comp_coneHornToStdSimplex :
    inl _ _ ≫ coneHornToStdSimplex.{u} = stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ 0) := by
  simp [coneHornToStdSimplex]

private lemma inr_comp_coneHornToStdSimplex :
    inr _ _ ≫ coneHornToStdSimplex.{u} = Λ[2, 2].ι ≫ stdSimplex.δ 0 := by
  simp [coneHornToStdSimplex]

/-- The cone point of `Δ[0] ⋆ Λ[2, 2]` is sent to the vertex `0` of `Δ[3]`. -/
private lemma coneHornToStdSimplex_app_inl_app {d : ℕ} (v : Δ[0] _⦋d⦌) (i : Fin (d + 1)) :
    coneHornToStdSimplex.{u}.app _ ((inl _ _).app _ v) i = 0 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, inl_comp_coneHornToStdSimplex,
    stdSimplex.hom_app_apply, stdSimplex.yonedaEquiv_map_apply]
  rfl

/-- The vertex `i` of `Λ[2, 2]` is sent to the vertex `i + 1` of `Δ[3]`. -/
private lemma coneHornToStdSimplex_app_inr_app {d : ℕ} (v : (Λ[2, 2] : SSet.{u}) _⦋d⦌)
    (i : Fin (d + 1)) : coneHornToStdSimplex.app _ ((inr _ _).app _ v) i = (v.val i).succ := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, inr_comp_coneHornToStdSimplex,
    NatTrans.comp_app, ConcreteCategory.comp_apply, stdSimplex.hom_app_apply,
    CosimplicialObject.δ, stdSimplex.yonedaEquiv_map_apply]
  exact congrFun Fin.succAbove_zero _

/-- No edge of `Δ[0] ⋆ Λ[2, 2]` goes from the vertex `1` to the vertex `2` of `Δ[3]`: an edge
starting at the cone point starts at `0`, and the other edges are edges of `Λ[2, 2]`, which does not
contain the edge from `0` to `1`. -/
private lemma not_coneHornToStdSimplex_edge (t : (join Δ[0] (Λ[2, 2] : SSet.{u})) _⦋1⦌) :
    ¬ (coneHornToStdSimplex.app _ t 0 = 1 ∧ coneHornToStdSimplex.app _ t 1 = 2) := by
  rintro ⟨h₀, h₁⟩
  by_cases hp : (π _ _).app _ t 0 = 0
  · -- The source of `t` is the cone point, sent to the vertex `0`.
    set v := (join Δ[0] (Λ[2, 2] : SSet.{u})).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op t
    have hv : v ∈ (joinFiber (univ _ _).p 0).obj _ := by
      rw [mem_joinFiber_iff, univ_p]
      intro i
      rw [NatTrans.naturality_apply, stdSimplex.obj_map_apply]
      exact hp
    have hv' : coneHornToStdSimplex.app _ v 0 = 1 := by
      rw [NatTrans.naturality_apply, stdSimplex.obj_map_apply]
      exact h₀
    rw [← inl_app_univ_left_app v hv, coneHornToStdSimplex_app_inl_app] at hv'
    exact absurd hv' (by decide)
  · -- Otherwise `t` lies over the vertex `1`, so it is an edge of `Λ[2, 2]`.
    have hp₁ : (π _ _).app _ t 0 = 1 := Fin.eq_one_of_ne_zero _ hp
    have ht : t ∈ (joinFiber (univ _ _).p 1).obj _ := by
      rw [mem_joinFiber_iff, univ_p]
      intro i
      refine le_antisymm (Fin.le_last _) ?_
      rw [← hp₁]
      exact stdSimplex.monotone_apply _ (Fin.zero_le i)
    rw [← inr_app_univ_right_app t ht, coneHornToStdSimplex_app_inr_app] at h₀ h₁
    have hy := ((univ _ _).right.app _ ⟨t, ht⟩).property
    obtain ⟨k, hk, hky⟩ := (mem_horn_iff_notMem_range _ _).1 hy
    fin_cases k
    · exact hky ⟨0, Fin.succ_injective _ h₀⟩
    · exact hky ⟨1, Fin.succ_injective _ h₁⟩
    · exact hk rfl

private lemma range_coneHornToStdSimplex :
    Subcomplex.range coneHornToStdSimplex.{u} = stdSimplex.face {1}ᶜ ⊔ stdSimplex.face {2}ᶜ :=
  le_antisymm (stdSimplex.range_le_face_singleton_compl_sup_face_singleton_compl _
      (by decide) not_coneHornToStdSimplex_edge)
    (sup_le (face_le_range_coneHornToStdSimplex 0 (by decide))
      (face_le_range_coneHornToStdSimplex 1 (by decide)))

/-! ### The cocone `Λ[2, 0] ⋆ Δ[0]` -/

/-- The embedding `Λ[2, 0] ⋆ Δ[0] ⟶ Δ[2] ⋆ Δ[0] ≅ Δ[3]`. -/
private noncomputable abbrev hornConeToStdSimplex : join (Λ[2, 0] : SSet.{u}) Δ[0] ⟶ Δ[3] :=
  map Λ[2, 0].ι (𝟙 Δ[0]) ≫ (stdSimplexIso 2 0).hom

/-- The vertex `i` of `Λ[2, 0]` is sent to the vertex `i` of `Δ[3]`. -/
private lemma hornConeToStdSimplex_app_inl_app {d : ℕ} (v : (Λ[2, 0] : SSet.{u}) _⦋d⦌)
    (i : Fin (d + 1)) :
    hornConeToStdSimplex.app _ ((inl _ _).app _ v) i = Fin.castLE (by omega) (v.val i) := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, inl_map_assoc, NatTrans.comp_app,
    ConcreteCategory.comp_apply, stdSimplex.hom_app_apply,
    yonedaEquiv_inl_comp_stdSimplexIso_hom (n := 2) (m := 0)]
  rfl

/-- The cone point of `Λ[2, 0] ⋆ Δ[0]` is sent to the vertex `3` of `Δ[3]`. -/
private lemma hornConeToStdSimplex_app_inr_app {d : ℕ} (v : Δ[0] _⦋d⦌) (i : Fin (d + 1)) :
    hornConeToStdSimplex.{u}.app _ ((inr _ _).app _ v) i = 3 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, inr_map_assoc, Category.id_comp,
    stdSimplex.hom_app_apply, yonedaEquiv_inr_comp_stdSimplexIso_hom (n := 2) (m := 0)]
  simp [Fin.ext_iff]

/-- The faces of `Δ[3]` opposite to the vertices `1` and `2` lie in `Λ[2, 0] ⋆ Δ[0]`: they are the
cocones on the faces of `Δ[2]` opposite to the vertices `1` and `2`. -/
private lemma face_le_range_hornConeToStdSimplex (j : Fin 3) (hj : j ≠ 0) :
    stdSimplex.face {j.castSucc}ᶜ ≤ Subcomplex.range hornConeToStdSimplex.{u} := by
  have hle : Subcomplex.range (stdSimplex.δ j) ≤ Λ[2, 0] := by
    rw [stdSimplex.range_δ]
    exact face_le_horn _ _ hj
  have h : stdSimplex.δ j.castSucc = (stdSimplexIso 1 0).inv ≫
      map (Subcomplex.lift _ hle) (𝟙 Δ[0]) ≫ hornConeToStdSimplex.{u} := by
    rw [hornConeToStdSimplex, ← map_comp_assoc, Category.id_comp, Subcomplex.lift_ι,
      Iso.eq_inv_comp]
    exact (map_δ_comp_stdSimplexIso_hom j).symm
  rw [← stdSimplex.range_δ, h, ← Category.assoc]
  exact Subfunctor.range_comp_le _ _

/-- No edge of `Λ[2, 0] ⋆ Δ[0]` goes from the vertex `1` to the vertex `2` of `Δ[3]`: an edge
ending at the cone point ends at `3`, and the other edges are edges of `Λ[2, 0]`, which does not
contain the edge from `1` to `2`. -/
private lemma not_hornConeToStdSimplex_edge (t : (join (Λ[2, 0] : SSet.{u}) Δ[0]) _⦋1⦌) :
    ¬ (hornConeToStdSimplex.app _ t 0 = 1 ∧ hornConeToStdSimplex.app _ t 1 = 2) := by
  rintro ⟨h₀, h₁⟩
  by_cases hp : (π _ _).app _ t 1 = 1
  · -- The target of `t` is the cone point, sent to the vertex `3`.
    set v := (join (Λ[2, 0] : SSet.{u}) Δ[0]).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op t
    have hv : v ∈ (joinFiber (univ _ _).p 1).obj _ := by
      rw [mem_joinFiber_iff, univ_p]
      intro i
      rw [NatTrans.naturality_apply, stdSimplex.obj_map_apply]
      exact hp
    have hv' : hornConeToStdSimplex.app _ v 0 = 2 := by
      rw [NatTrans.naturality_apply, stdSimplex.obj_map_apply]
      exact h₁
    rw [← inr_app_univ_right_app v hv, hornConeToStdSimplex_app_inr_app] at hv'
    exact absurd hv' (by decide)
  · -- Otherwise `t` lies over the vertex `0`, so it is an edge of `Λ[2, 0]`.
    have hp₀ : (π _ _).app _ t 1 = 0 := by
      by_contra h
      exact hp (Fin.eq_one_of_ne_zero _ h)
    have ht : t ∈ (joinFiber (univ _ _).p 0).obj _ := by
      rw [mem_joinFiber_iff, univ_p]
      intro i
      refine le_antisymm ?_ (Fin.zero_le _)
      rw [← hp₀]
      exact stdSimplex.monotone_apply _ (Fin.le_last i)
    rw [← inl_app_univ_left_app t ht, hornConeToStdSimplex_app_inl_app] at h₀ h₁
    have hy := ((univ _ _).left.app _ ⟨t, ht⟩).property
    obtain ⟨k, hk, hky⟩ := (mem_horn_iff_notMem_range _ _).1 hy
    fin_cases k
    · exact hk rfl
    · exact hky ⟨0, Fin.castLE_injective _ h₀⟩
    · exact hky ⟨1, Fin.castLE_injective _ h₁⟩

private lemma range_hornConeToStdSimplex :
    Subcomplex.range hornConeToStdSimplex.{u} = stdSimplex.face {1}ᶜ ⊔ stdSimplex.face {2}ᶜ :=
  le_antisymm (stdSimplex.range_le_face_singleton_compl_sup_face_singleton_compl _
      (by decide) not_hornConeToStdSimplex_edge)
    (sup_le (face_le_range_hornConeToStdSimplex 1 (by decide))
      (face_le_range_hornConeToStdSimplex 2 (by decide)))

/-! ### The isomorphisms -/

/-- **The square as a cone over a cospan.** The join `Δ[0] ⋆ Λ[2, 2]` of a point and the horn
`Λ[2, 2]` (the cospan `0 ⟶ 2 ⟵ 1`) is the square `Δ[1] ⊗ Δ[1]`: the cone point is the vertex
`(0, 0)`, and the vertices `0`, `1` and `2` of the horn are the vertices `(1, 0)`, `(0, 1)` and
`(1, 1)` (`SSet.join.objEquiv_coneHornIso_hom_app_inl`,
`SSet.join.objEquiv_coneHornIso_hom_app_inr`). -/
noncomputable def coneHornIso : join Δ[0] (Λ[2, 2] : SSet.{u}) ≅ Δ[1] ⊗ Δ[1] :=
  asIso (Subcomplex.toRange coneHornToStdSimplex) ≪≫
    Subcomplex.eqToIso
      (range_coneHornToStdSimplex.trans prodStdSimplex.range_toStdSimplexThree.symm) ≪≫
    (asIso (Subcomplex.toRange prodStdSimplex.toStdSimplexThree)).symm

private lemma coneHornIso_hom_comp_toStdSimplexThree :
    coneHornIso.{u}.hom ≫ prodStdSimplex.toStdSimplexThree = coneHornToStdSimplex := by
  simp [coneHornIso, prodStdSimplex.inv_toRange_toStdSimplexThree_comp]

/-- The vertex `i` of the image of `x` under `Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]`, seen in `Δ[3]`, is the
vertex `i` of the image of `x` in `Δ[3]`. -/
private lemma squareVertex_objEquiv_coneHornIso_hom_app {d : ℕ}
    (x : (join Δ[0] (Λ[2, 2] : SSet.{u})) _⦋d⦌) (i : Fin (d + 1)) :
    prodStdSimplex.squareVertex (prodStdSimplex.objEquiv (coneHornIso.hom.app _ x) i) =
      coneHornToStdSimplex.app _ x i := by
  rw [← prodStdSimplex.toStdSimplexThree_app_apply, ← ConcreteCategory.comp_apply,
    ← NatTrans.comp_app, coneHornIso_hom_comp_toStdSimplexThree]

/-- **The square as a cocone under a span.** The join `Λ[2, 0] ⋆ Δ[0]` of the horn `Λ[2, 0]` (the
span `1 ⟵ 0 ⟶ 2`) and a point is the square `Δ[1] ⊗ Δ[1]`: the vertices `0`, `1` and `2` of the
horn are the vertices `(0, 0)`, `(1, 0)` and `(0, 1)`, and the cone point is the vertex `(1, 1)`
(`SSet.join.objEquiv_hornConeIso_hom_app_inl`, `SSet.join.objEquiv_hornConeIso_hom_app_inr`). -/
noncomputable def hornConeIso : join (Λ[2, 0] : SSet.{u}) Δ[0] ≅ Δ[1] ⊗ Δ[1] :=
  asIso (Subcomplex.toRange hornConeToStdSimplex) ≪≫
    Subcomplex.eqToIso
      (range_hornConeToStdSimplex.trans prodStdSimplex.range_toStdSimplexThree.symm) ≪≫
    (asIso (Subcomplex.toRange prodStdSimplex.toStdSimplexThree)).symm

private lemma hornConeIso_hom_comp_toStdSimplexThree :
    hornConeIso.{u}.hom ≫ prodStdSimplex.toStdSimplexThree = hornConeToStdSimplex := by
  simp [hornConeIso, prodStdSimplex.inv_toRange_toStdSimplexThree_comp]

/-- The vertex `i` of the image of `x` under `Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]`, seen in `Δ[3]`, is the
vertex `i` of the image of `x` in `Δ[3]`. -/
private lemma squareVertex_objEquiv_hornConeIso_hom_app {d : ℕ}
    (x : (join (Λ[2, 0] : SSet.{u}) Δ[0]) _⦋d⦌) (i : Fin (d + 1)) :
    prodStdSimplex.squareVertex (prodStdSimplex.objEquiv (hornConeIso.hom.app _ x) i) =
      hornConeToStdSimplex.app _ x i := by
  rw [← prodStdSimplex.toStdSimplexThree_app_apply, ← ConcreteCategory.comp_apply,
    ← NatTrans.comp_app, hornConeIso_hom_comp_toStdSimplexThree]

/-- Under `Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]`, the cone point is the vertex `(0, 0)`. -/
@[simp]
lemma objEquiv_coneHornIso_hom_app_inl (v : Δ[0] _⦋0⦌) :
    dsimp% prodStdSimplex.objEquiv (coneHornIso.{u}.hom.app _ ((inl _ _).app _ v)) 0 =
      (0, 0) := by
  refine prodStdSimplex.squareVertex_injective
    ((squareVertex_objEquiv_coneHornIso_hom_app _ 0).trans ?_)
  rw [coneHornToStdSimplex_app_inl_app]
  rfl

/-- Under `Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]`, the vertices `0`, `1` and `2` of the horn are the
vertices `(1, 0)`, `(0, 1)` and `(1, 1)`. -/
@[simp]
lemma objEquiv_coneHornIso_hom_app_inr (v : (Λ[2, 2] : SSet.{u}) _⦋0⦌) :
    dsimp% prodStdSimplex.objEquiv (coneHornIso.{u}.hom.app _ ((inr _ _).app _ v)) 0 =
      ![(1, 0), (0, 1), (1, 1)] (v.val 0) := by
  refine prodStdSimplex.squareVertex_injective
    ((squareVertex_objEquiv_coneHornIso_hom_app _ 0).trans ?_)
  rw [coneHornToStdSimplex_app_inr_app]
  exact ((by decide : ∀ a : Fin 3, prodStdSimplex.squareVertex (![(1, 0), (0, 1), (1, 1)] a) =
    a.succ) _).symm

/-- Under `Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]`, the vertices `0`, `1` and `2` of the horn are the
vertices `(0, 0)`, `(1, 0)` and `(0, 1)`. -/
@[simp]
lemma objEquiv_hornConeIso_hom_app_inl (v : (Λ[2, 0] : SSet.{u}) _⦋0⦌) :
    dsimp% prodStdSimplex.objEquiv (hornConeIso.{u}.hom.app _ ((inl _ _).app _ v)) 0 =
      ![(0, 0), (1, 0), (0, 1)] (v.val 0) := by
  refine prodStdSimplex.squareVertex_injective
    ((squareVertex_objEquiv_hornConeIso_hom_app _ 0).trans ?_)
  rw [hornConeToStdSimplex_app_inl_app]
  exact ((by decide : ∀ a : Fin 3, prodStdSimplex.squareVertex (![(0, 0), (1, 0), (0, 1)] a) =
    Fin.castLE (by omega) a) _).symm

/-- Under `Λ[2, 0] ⋆ Δ[0] ≅ Δ[1] ⊗ Δ[1]`, the cone point is the vertex `(1, 1)`. -/
@[simp]
lemma objEquiv_hornConeIso_hom_app_inr (v : Δ[0] _⦋0⦌) :
    dsimp% prodStdSimplex.objEquiv (hornConeIso.{u}.hom.app _ ((inr _ _).app _ v)) 0 =
      (1, 1) := by
  refine prodStdSimplex.squareVertex_injective
    ((squareVertex_objEquiv_hornConeIso_hom_app _ 0).trans ?_)
  rw [hornConeToStdSimplex_app_inr_app]
  rfl

end join

end SSet
