/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex
public import TauCeti.CategoryTheory.ComposableArrows.Under

/-!
# Coslices of ordinary nerves

The simplicial coslice of the nerve of a category under an object x is the nerve of
its ordinary under category, through `CategoryTheory.nerve.cosliceIso`. The comparison preserves
the projection to the original
nerve. It identifies the join description of a coslice simplex with a string of arrows
under x, retaining the structure arrows and all simplicial operators.

This is the ordinary-category model of the coslices used in comma-category criteria
for finality of maps of simplicial sets.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.9 and Theorem 4.1.3.1.
-/

public section

open CategoryTheory Limits Opposite Simplicial
open SSet

universe v u

namespace CategoryTheory.nerve

variable {C : Type u} [Category.{v} C] (x : C)

/-- Reindexing a string of arrows under x along `f` reindexes its string of arrows starting at x
along the extension `SimplexCategory.vertexJoin.map f` of `f` fixing the initial vertex. -/
lemma underEquiv_symm_map_coe {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (s : ComposableArrows (Under x) n) :
    ((ComposableArrows.underEquiv x m).symm ((nerve (Under x)).map f.op s)).1 =
      (nerve C).map (SimplexCategory.vertexJoin.map f).op
        ((ComposableArrows.underEquiv x n).symm s).1 := by
  symm
  -- Both strings drop their first arrow to the reindexing along f of the string s. The nerve acts
  -- by reindexing strings, and dropping the first arrow is reindexing along δ 0, so the steps
  -- between these reindexings hold by unfolding `nerve`.
  have h₁ : ((nerve C).map (SimplexCategory.vertexJoin.map f).op
      ((ComposableArrows.underEquiv x n).symm s).1).δ₀ =
      (nerve C).map (SimplexCategory.δ 0 ≫ SimplexCategory.vertexJoin.map f).op
        ((ComposableArrows.underEquiv x n).symm s).1 := rfl
  have h₂ : (nerve C).map (f ≫ SimplexCategory.δ 0).op
      ((ComposableArrows.underEquiv x n).symm s).1 = (nerve C).map f.op (s ⋙ Under.forget x) := rfl
  have h₃ : (nerve C).map f.op (s ⋙ Under.forget x) =
      ((nerve (Under x)).map f.op s ⋙ Under.forget x) := rfl
  refine ComposableArrows.ext_succ_of_totalArrow (h₁.trans ((congrArg (fun g : ⦋m⦌ ⟶ ⦋n + 1⦌ ↦
      (nerve C).map g.op ((ComposableArrows.underEquiv x n).symm s).1)
      (SimplexCategory.δ_zero_comp_vertexJoin_map f)).trans (h₂.trans (h₃.trans
        (ComposableArrows.precomp_δ₀ _ _).symm)))) ?_
  -- The first arrow of the reindexed string runs from the vertex 0 to the vertex f 0 + 1.
  have key (i j : Fin (n + 2)) (hij : i ≤ j) (hi : i = 0) (hj : j = (f.toOrderHom 0).succ) :
      ((ComposableArrows.underEquiv x n).symm s).1.totalArrow i j hij =
        ((ComposableArrows.underEquiv x n).symm s).1.totalArrow 0 (f.toOrderHom 0).succ
          (Fin.zero_le _) := by
    subst hi hj
    rfl
  refine (ComposableArrows.totalArrow_whiskerLeft _ _ _ _ _).trans
    ((key _ _ _ (SimplexCategory.vertexJoin_map_zero f)
      (SimplexCategory.vertexJoin_map_succ f 0)).trans
        ((ComposableArrows.totalArrow_precomp_zero_succ _ _ _).trans ?_))
  -- The first structure arrow followed by the arrow to f 0 is the structure arrow of f 0.
  exact (congrArg (fun a ↦ (⟨x, _, a⟩ : Quiver.Total C))
    (Under.w (s.map (homOfLE (Fin.zero_le (f.toOrderHom 0)))))).trans
      (ComposableArrows.totalArrow_def ((ComposableArrows.underEquiv x m).symm
        ((nerve (Under x)).map f.op s)).1 0 1 (Fin.zero_le _)).symm

/-- The cone `Δ[0] ⋆ Δ[n] ⟶ nerve C` on a string of arrows under x: the string of n + 1 arrows
prepending the structure arrow of its first object, read through `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
private noncomputable def cone (n : ℕ) (s : ComposableArrows (Under x) n) :
    join Δ[0] Δ[n] ⟶ nerve C :=
  (join.coneIso.{max u v} n).hom ≫
    SSet.yonedaEquiv.symm ((ComposableArrows.underEquiv x n).symm s).1

-- The vertex `nerveEquiv.symm x : ComposableArrows C 0` is a 0-simplex of `nerve C` only after
-- unfolding `nerve`, so `rw` rejects goals mentioning the coslice under it as ill-typed at
-- reducible transparency. The proofs below therefore compose their equations by `Eq.trans` and
-- `congrArg`.

private lemma cone_inl (n : ℕ) (s : ComposableArrows (Under x) n) :
    join.inl Δ[0] Δ[n] ≫ cone x n s = const (nerveEquiv.symm x) := by
  rw [cone, join.inl_comp_coneIso_hom_assoc]
  -- The vertex 0 of the prepended string is x.
  exact (SSet.yonedaEquiv_symm_naturality_left _ _).trans
    ((congrArg _ (ComposableArrows.ext₀ rfl)).trans (yonedaEquiv_symm_zero _))

private lemma cone_inr (n : ℕ) (s : ComposableArrows (Under x) n) :
    join.inr Δ[0] Δ[n] ≫ cone x n s =
      (SSet.yonedaEquiv (X := nerve C)).symm (s ⋙ Under.forget x) := by
  rw [cone, join.inr_comp_coneIso_hom_assoc]
  exact (stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans
    (congrArg _ (nerve.δ₀_eq.trans (ComposableArrows.precomp_δ₀ _ _)))

private lemma cone_naturality {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (s : ComposableArrows (Under x) n) :
    join.map (𝟙 _) (stdSimplex.map f) ≫ cone x n s =
      cone x m ((nerve (Under x)).map f.op s) := by
  unfold cone
  rw [join.map_comp_coneIso_hom_assoc]
  exact congrArg ((join.coneIso m).hom ≫ ·) ((SSet.yonedaEquiv_symm_naturality_left _ _).trans
    (congrArg _ (underEquiv_symm_map_coe x f s).symm))

/-- The string of n + 1 arrows starting at x read off from a cone `Δ[0] ⋆ Δ[n] ⟶ nerve C`
with cone point x, through `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
private noncomputable def coneSimplex {n : ℕ}
    (τ : {τ : join Δ[0] Δ[n] ⟶ nerve C // join.inl _ _ ≫ τ = const (nerveEquiv.symm x)}) :
    {t : ComposableArrows C (n + 1) // t.obj 0 = x} :=
  ⟨SSet.yonedaEquiv ((join.coneIso n).inv ≫ τ.1),
    -- The vertex 0 of the simplex is the cone point of τ.
    (congrArg nerveEquiv (((SSet.yonedaEquiv_naturality _ _).trans (congrArg SSet.yonedaEquiv
      ((join.const_zero_comp_coneIso_inv_assoc τ.1).trans τ.2))).trans
        (SSet.yonedaEquiv_const _))).trans (Equiv.apply_symm_apply _ _)⟩

private lemma cone_coneSimplex {n : ℕ}
    (τ : {τ : join Δ[0] Δ[n] ⟶ nerve C // join.inl _ _ ≫ τ = const (nerveEquiv.symm x)}) :
    cone x n (ComposableArrows.underEquiv x n (coneSimplex x τ)) = τ.1 :=
  (congrArg (fun t : {t : ComposableArrows C (n + 1) // t.obj 0 = x} ↦
    (join.coneIso n).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm t.1)
    (Equiv.symm_apply_apply (ComposableArrows.underEquiv x n) (coneSimplex x τ))).trans
      ((congrArg _ (SSet.yonedaEquiv.symm_apply_apply _)).trans (Iso.hom_inv_id_assoc _ _))

private lemma coneSimplex_cone {n : ℕ} (s : ComposableArrows (Under x) n) :
    coneSimplex x ⟨cone x n s, cone_inl x n s⟩ = (ComposableArrows.underEquiv x n).symm s :=
  Subtype.ext ((congrArg SSet.yonedaEquiv (Iso.inv_hom_id_assoc _ _)).trans
    (Equiv.apply_symm_apply _ _))

/-- The comparison map, sending a string of arrows under x to its cone. -/
private noncomputable def toCoslice :
    nerve (Under x) ⟶ coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C) where
  app n := ↾fun s ↦ coslice.objEquiv.symm ⟨cone x n.unop.len s, cone_inl x _ s⟩
  naturality n m f := by
    ext s
    refine coslice.objEquiv.injective (Subtype.ext ?_)
    exact ((congrArg Subtype.val (Equiv.apply_symm_apply _ _)).trans
      (cone_naturality x f.unop s).symm).trans
        ((congrArg (join.map (𝟙 _) (stdSimplex.map f.unop) ≫ ·)
          (congrArg Subtype.val (Equiv.apply_symm_apply _ _))).symm.trans
            (coslice.objEquiv_map_coe _ _).symm)

/-- Evaluating the comparison map gives the cone on a string of arrows under x. -/
private lemma objEquiv_toCoslice_app (n : SimplexCategoryᵒᵖ) (s : (nerve (Under x)).obj n) :
    coslice.objEquiv ((toCoslice x).app n s) = ⟨cone x n.unop.len s, cone_inl x _ s⟩ :=
  Equiv.apply_symm_apply _ _

private instance isIso_toCoslice : IsIso (toCoslice x) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun τ ↦ ComposableArrows.underEquiv x _ (coneSimplex x (coslice.objEquiv τ)), fun s ↦ ?_,
      fun τ ↦ ?_⟩
  · exact (congrArg (fun τ ↦ ComposableArrows.underEquiv x _ (coneSimplex x τ))
      (objEquiv_toCoslice_app x n s)).trans
        ((congrArg _ (coneSimplex_cone x s)).trans (Equiv.apply_symm_apply _ _))
  · exact coslice.objEquiv.injective (Subtype.ext ((congrArg Subtype.val
      (objEquiv_toCoslice_app x n _)).trans (cone_coneSimplex x (coslice.objEquiv τ))))

/-- The nerve of the under category of x is the coslice of the nerve under x. -/
noncomputable def cosliceIso :
    nerve (Under x) ≅ coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C) :=
  asIso (toCoslice x)

/-- The coslice simplex of a string of n arrows under x is the string of n + 1 arrows prepending
its first structure arrow, read through `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
lemma objEquiv_cosliceIso_hom_app_coe {n : ℕ} (s : ComposableArrows (Under x) n) :
    (coslice.objEquiv ((cosliceIso x).hom.app (op ⦋n⦌) s)).1 =
      (join.coneIso n).hom ≫
        SSet.yonedaEquiv.symm ((ComposableArrows.underEquiv x n).symm s).1 :=
  congrArg Subtype.val (objEquiv_toCoslice_app x (op ⦋n⦌) s)

/-- The string of n + 1 arrows starting at x underlying the inverse image of a coslice simplex
`τ : Δ[0] ⋆ Δ[n] ⟶ nerve C` is τ read through `Δ[n + 1] ≅ Δ[0] ⋆ Δ[n]`. -/
lemma underEquiv_symm_cosliceIso_inv_app_coe {n : ℕ}
    (τ : (coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C)).obj (op ⦋n⦌)) :
    ((ComposableArrows.underEquiv x n).symm ((cosliceIso x).inv.app (op ⦋n⦌) τ)).1 =
      SSet.yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv τ).1) :=
  (SSet.yonedaEquiv.apply_symm_apply _).symm.trans (congrArg SSet.yonedaEquiv
    ((Iso.inv_hom_id_assoc _ _).symm.trans (congrArg _
      ((objEquiv_cosliceIso_hom_app_coe x _).symm.trans (congrArg (fun σ ↦ (coslice.objEquiv σ).1)
        (Iso.inv_hom_id_apply ((cosliceIso x).app (op ⦋n⦌)) τ))))))

/-- The projection `SSet.coslice.π` of a coslice simplex is the string obtained by forgetting its
structure arrows. -/
@[simp]
lemma π_app_cosliceIso_hom_app (n : SimplexCategoryᵒᵖ) (s : (nerve (Under x)).obj n) :
    SSet.yonedaEquiv (join.inr Δ[0] (stdSimplex.obj n.unop) ≫
      (coslice.objEquiv ((cosliceIso x).hom.app n s)).1) = s ⋙ Under.forget x :=
  (congrArg (fun τ ↦ SSet.yonedaEquiv (join.inr _ _ ≫ τ.1)) (objEquiv_toCoslice_app x n s)).trans
    ((congrArg SSet.yonedaEquiv (cone_inr x _ s)).trans (Equiv.apply_symm_apply _ _))

/-- The vertex given by an arrow x → y retains that arrow in the coslice. -/
@[simp]
lemma cosliceIso_hom_app_vertex {y : C} (f : x ⟶ y) :
    (coslice.objEquiv ((cosliceIso x).hom.app (op ⦋0⦌)
      (nerveEquiv.symm (Under.mk f)))).1 =
        (join.coneIso 0).hom ≫ SSet.yonedaEquiv.symm (ComposableArrows.mk₁ f) :=
  (objEquiv_cosliceIso_hom_app_coe x _).trans (congrArg _ (congrArg _
    -- The structure arrow of the vertex is f, between identities of its endpoints.
    (ComposableArrows.ext₁ rfl rfl ((Category.id_comp _).trans (Category.comp_id f)).symm)))

end CategoryTheory.nerve
