/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.CategoryTheory.ComposableArrows.Under

/-!
# Coslices of ordinary nerves

The simplicial coslice of the nerve of a category under an object x is the nerve of
its ordinary under category, through `CategoryTheory.nerve.cosliceIso`. Projection compatibility
is given simplexwise by `CategoryTheory.nerve.yonedaEquiv_inr_comp_objEquiv_cosliceIso_hom_app_coe`:
restricting the comparison along `join.inr` sends a string `s` to `s ⋙ Under.forget x`
(`CategoryTheory.nerve.cosliceIso_inv_app_comp_forget` is the inverse form). When the objects of
the category live in a universe containing its morphisms, so that `Under x` and the category have
the same object universe as `CategoryTheory.nerveMap` requires, the comparison takes the coslice
projection to `nerveMap (Under.forget x)` (`CategoryTheory.nerve.cosliceIso_hom_comp_π`).
The comparison identifies the join description of a coslice simplex with a string of arrows
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
  -- Both strings drop their first arrow to the reindexing along f of the string s: dropping the
  -- first arrow is the face `δ 0`, and the nerve reindexes strings by whiskering.
  have h₁ : ((nerve C).map (SimplexCategory.vertexJoin.map f).op
      ((ComposableArrows.underEquiv x n).symm s).1).δ₀ =
      (nerve C).map (SimplexCategory.δ 0 ≫ SimplexCategory.vertexJoin.map f).op
        ((ComposableArrows.underEquiv x n).symm s).1 :=
    nerve.δ₀_eq.symm.trans (Functor.map_comp_apply _ _ _ _).symm
  have h₂ : (nerve C).map (f ≫ SimplexCategory.δ 0).op
      ((ComposableArrows.underEquiv x n).symm s).1 = (nerve C).map f.op (s ⋙ Under.forget x) :=
    (Functor.map_comp_apply _ _ _ _).trans
      (congrArg _ (nerve.δ₀_eq.trans (ComposableArrows.precomp_δ₀ _ _)))
  have h₃ : (nerve C).map f.op (s ⋙ Under.forget x) =
      ((nerve (Under x)).map f.op s ⋙ Under.forget x) := by
    rw [nerve_map, nerve_map]
    exact Functor.assoc _ s (Under.forget x)
  refine ComposableArrows.ext_succ_of_totalArrow (h₁.trans ((congrArg (fun g : ⦋m⦌ ⟶ ⦋n + 1⦌ ↦
      (nerve C).map g.op ((ComposableArrows.underEquiv x n).symm s).1)
      (SimplexCategory.δ_zero_comp_vertexJoin_map f)).trans (h₂.trans (h₃.trans
        (ComposableArrows.precomp_δ₀ _ _).symm)))) ?_
  -- The first arrow of the reindexed string runs from the vertex 0 to the vertex f 0 + 1.
  -- Rewriting the indices along `vertexJoin_map_zero` and `vertexJoin_map_succ` changes the
  -- dependent proof of `0 ≤ f 0 + 1`, so `key` transports along them by `subst`.
  have key (i j : Fin (n + 2)) (hij : i ≤ j) (hi : i = 0) (hj : j = (f.toOrderHom 0).succ) :
      ((ComposableArrows.underEquiv x n).symm s).1.totalArrow i j hij =
        ((ComposableArrows.underEquiv x n).symm s).1.totalArrow 0 (f.toOrderHom 0).succ
          (Fin.zero_le _) := by
    subst hi hj
    rfl
  refine (nerve.totalArrow_map _ _ _ _ _).trans
    ((key _ _ _ (SimplexCategory.vertexJoin_map_zero f)
      (SimplexCategory.vertexJoin_map_succ f 0)).trans
        ((ComposableArrows.totalArrow_underEquiv_symm_apply_coe_zero_succ x s _).trans ?_))
  -- Both first arrows are the structure arrow of the vertex f 0 of s.
  exact (congrArg (fun a : Under x ↦ (⟨x, a.right, a.hom⟩ : Quiver.Total C))
    (nerve.map_obj f s 0)).symm.trans
      (ComposableArrows.totalArrow_underEquiv_symm_apply_coe_zero_succ x _ 0).symm

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
    ((congrArg _ ((nerve.map_const _ 0).trans (congrArg nerveEquiv.symm
      ((ComposableArrows.underEquiv x n).symm s).2))).trans (yonedaEquiv_symm_zero _))

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
    nerveEquiv.symm.injective ((nerve.map_const _ 0).symm.trans
      (((SSet.yonedaEquiv_naturality _ _).trans (congrArg SSet.yonedaEquiv
        ((join.const_zero_comp_coneIso_inv_assoc τ.1).trans τ.2))).trans
          (SSet.yonedaEquiv_const _)))⟩

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

/-- Strings of arrows under x correspond to cones with cone point x, by taking a string to its
cone and a cone to the string under x of its simplex. -/
private noncomputable def coneEquiv (n : SimplexCategoryᵒᵖ) :
    (nerve (Under x)).obj n ≃ (coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C)).obj n where
  toFun s := coslice.objEquiv.symm ⟨cone x n.unop.len s, cone_inl x _ s⟩
  invFun τ := ComposableArrows.underEquiv x _ (coneSimplex x (coslice.objEquiv τ))
  left_inv s := (congrArg (fun τ ↦ ComposableArrows.underEquiv x _ (coneSimplex x τ))
    (coslice.objEquiv.apply_symm_apply _)).trans
      ((congrArg _ (coneSimplex_cone x s)).trans (Equiv.apply_symm_apply _ _))
  right_inv τ := coslice.objEquiv.symm_apply_eq.mpr
    (Subtype.ext (cone_coneSimplex x (coslice.objEquiv τ)))

/-- The nerve of the under category of x is the coslice of the nerve under x. -/
noncomputable def cosliceIso :
    nerve (Under x) ≅ coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C) :=
  NatIso.ofComponents (fun n ↦ (coneEquiv x n).toIso) fun f ↦ by
    ext s
    refine coslice.objEquiv.injective (Subtype.ext ?_)
    exact ((congrArg Subtype.val (Equiv.apply_symm_apply _ _)).trans
      (cone_naturality x f.unop s).symm).trans
        ((congrArg (join.map (𝟙 _) (stdSimplex.map f.unop) ≫ ·)
          (congrArg Subtype.val (Equiv.apply_symm_apply _ _))).symm.trans
            (coslice.objEquiv_map_coe _ _).symm)

/-- The coslice simplex of a string of n arrows under x is the string of n + 1 arrows prepending
its first structure arrow, read through `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
lemma objEquiv_cosliceIso_hom_app_coe {n : ℕ} (s : ComposableArrows (Under x) n) :
    (coslice.objEquiv ((cosliceIso x).hom.app (op ⦋n⦌) s)).1 =
      (join.coneIso n).hom ≫
        SSet.yonedaEquiv.symm ((ComposableArrows.underEquiv x n).symm s).1 :=
  congrArg Subtype.val (coslice.objEquiv.apply_symm_apply _)

/-- The string of n + 1 arrows starting at x underlying the inverse image of a coslice simplex
`τ : Δ[0] ⋆ Δ[n] ⟶ nerve C` is τ read through `Δ[n + 1] ≅ Δ[0] ⋆ Δ[n]`. -/
lemma underEquiv_symm_cosliceIso_inv_app_coe {n : ℕ}
    (τ : (coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C)).obj (op ⦋n⦌)) :
    ((ComposableArrows.underEquiv x n).symm ((cosliceIso x).inv.app (op ⦋n⦌) τ)).1 =
      SSet.yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv τ).1) :=
  congrArg Subtype.val ((ComposableArrows.underEquiv x n).symm_apply_apply _)

/-- Restricting `(cosliceIso x).hom.app n s` to the base simplex along `join.inr` forgets the
structure arrows of `s`. This is the `SSet.coslice.π_app` normal form of its projection. -/
@[simp]
lemma yonedaEquiv_inr_comp_objEquiv_cosliceIso_hom_app_coe (n : SimplexCategoryᵒᵖ)
    (s : (nerve (Under x)).obj n) :
    SSet.yonedaEquiv (join.inr Δ[0] (stdSimplex.obj n.unop) ≫
      (coslice.objEquiv ((cosliceIso x).hom.app n s)).1) = s ⋙ Under.forget x :=
  (congrArg (fun τ ↦ SSet.yonedaEquiv (join.inr _ _ ≫ τ.1))
    (coslice.objEquiv.apply_symm_apply ⟨cone x n.unop.len s, cone_inl x _ s⟩)).trans
    ((congrArg SSet.yonedaEquiv (cone_inr x _ s)).trans (Equiv.apply_symm_apply _ _))

/-- Restricting the comparison along `join.inr` forgets the structure arrows of `s`. This is the
`SSet.coslice.comp_π` normal form of the projection of `(cosliceIso x).hom`. -/
@[simp]
lemma homEquiv_cosliceIso_hom_coe_app_inr_app (n : SimplexCategoryᵒᵖ)
    (s : (nerve (Under x)).obj n) :
    (coslice.homEquiv (cosliceIso x).hom).1.app n ((join.inr Δ[0] (nerve (Under x))).app n s) =
      s ⋙ Under.forget x :=
  (congrArg (fun φ ↦ φ.app n s) (coslice.comp_π (cosliceIso x).hom)).symm.trans
    ((coslice.π_app _).trans (yonedaEquiv_inr_comp_objEquiv_cosliceIso_hom_app_coe x n s))

/-- Forgetting the structure arrows of the inverse image of a coslice simplex `τ` restricts `τ` to
the base simplex along `join.inr`, the `SSet.coslice.π_app` normal form of the projection of `τ`. -/
@[simp]
lemma cosliceIso_inv_app_comp_forget (n : SimplexCategoryᵒᵖ)
    (τ : (coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C)).obj n) :
    (cosliceIso x).inv.app n τ ⋙ Under.forget x =
      SSet.yonedaEquiv (join.inr Δ[0] (stdSimplex.obj n.unop) ≫ (coslice.objEquiv τ).1) := by
  have e : (cosliceIso x).hom.app n ((cosliceIso x).inv.app n τ) = τ :=
    by simp
  exact (yonedaEquiv_inr_comp_objEquiv_cosliceIso_hom_app_coe x n _).symm.trans
    (congrArg (fun σ : (coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C)).obj n ↦
      SSet.yonedaEquiv (join.inr Δ[0] (stdSimplex.obj n.unop) ≫ (coslice.objEquiv σ).1)) e)

/-- The vertex given by an object `a : Under x` retains its structure arrow in the coslice. -/
lemma objEquiv_cosliceIso_hom_app_nerveEquiv_symm_coe (a : Under x) :
    (coslice.objEquiv ((cosliceIso x).hom.app (op ⦋0⦌)
      (nerveEquiv.symm a))).1 =
        (join.coneIso 0).hom ≫ SSet.yonedaEquiv.symm (ComposableArrows.mk₁ a.hom) :=
  -- `nerveEquiv.symm a` is `ComposableArrows.mk₀ a` by definition of `nerveEquiv`.
  (objEquiv_cosliceIso_hom_app_coe x _).trans
    (congrArg _ (congrArg _ (ComposableArrows.underEquiv_symm_mk₀_coe x a)))

end CategoryTheory.nerve

namespace CategoryTheory.nerve

/-! When the objects of `C` live in a universe containing its morphisms, `Under x` and `C` have the
same object universe, as required to write the induced map of nerves as
`CategoryTheory.nerveMap (Under.forget x)`. -/

variable {C : Type (max u v)} [Category.{v} C] (x : C)

/-- The comparison commutes with the projections to `nerve C`: the projection of the coslice
corresponds to the nerve of the forgetful functor `Under x ⥤ C`. -/
lemma cosliceIso_hom_comp_π :
    (cosliceIso x).hom ≫ coslice.π (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C) =
      nerveMap (Under.forget x) := by
  ext n s
  exact (coslice.π_app _).trans (yonedaEquiv_inr_comp_objEquiv_cosliceIso_hom_app_coe x n s)

/-- The inverse comparison turns the nerve of the forgetful functor `Under x ⥤ C` into the
projection of the coslice. -/
-- Not `@[simp]`: the simpNF linter finds that its left side does not match itself at reducible
-- transparency, so it would never fire.
@[reassoc]
lemma cosliceIso_inv_comp_nerveMap_forget :
    (cosliceIso x).inv ≫ nerveMap (Under.forget x) =
      coslice.π (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C) := by
  rw [Iso.inv_comp_eq, cosliceIso_hom_comp_π]

end CategoryTheory.nerve
