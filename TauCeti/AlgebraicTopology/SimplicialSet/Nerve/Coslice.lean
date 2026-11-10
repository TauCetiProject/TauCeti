/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplexCategory.JoinVertex
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

private noncomputable def coneIso (n : ℕ) : join Δ[0] Δ[n] ≅ (Δ[n + 1] : SSet.{u}) :=
  (join.stdSimplexIso 0 n).trans
    (stdSimplex.mapIso (eqToIso (by simp : ⦋0 + n + 1⦌ = ⦋n + 1⦌)))

private lemma coneIso_inl (n : ℕ) :
    join.inl Δ[0] Δ[n] ≫ (coneIso.{u} n).hom =
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) := by
  simp only [coneIso, Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc,
    join.inl_comp_stdSimplexIso_hom, ← Functor.map_comp]
  congr 1
  ext i : 3
  simp [SimplexCategory.eqToHom_toOrderHom]

private lemma coneIso_inr (n : ℕ) :
    join.inr Δ[0] Δ[n] ≫ (coneIso.{u} n).hom = stdSimplex.map (SimplexCategory.δ 0) := by
  apply (SSet.yonedaEquiv (X := (Δ[n + 1] : SSet.{u}))).injective
  ext i : 1
  dsimp only [coneIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, SSet.yonedaEquiv_comp, stdSimplex.hom_app_apply,
    join.yonedaEquiv_inr_comp_stdSimplexIso_hom, SSet.yonedaEquiv_map,
    SSet.yonedaEquiv_map]
  rw [stdSimplex.objEquiv_symm_apply, stdSimplex.objEquiv_symm_apply, eqToIso.hom,
    SimplexCategory.eqToHom_toOrderHom]
  apply Fin.ext
  simp [SimplexCategory.δ]

private def prepend {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) : ⦋m + 1⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.rev.map (SimplexCategory.joinVertex.map (SimplexCategory.rev.map f))

private lemma prepend_zero {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    (prepend f).toOrderHom 0 = 0 := by
  unfold prepend
  erw [SimplexCategory.rev_map_apply]
  rw [Fin.rev_zero]
  erw [SimplexCategory.joinVertex_map_last]
  simp

private lemma prepend_succ {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (prepend f).toOrderHom i.succ = (f.toOrderHom i).succ := by
  unfold prepend
  erw [SimplexCategory.rev_map_apply]
  rw [Fin.rev_succ]
  erw [SimplexCategory.joinVertex_map_castSucc, SimplexCategory.rev_map_apply]
  simp [Fin.rev_castSucc]

private lemma prepend_eq {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    prepend f =
      SimplexCategory.mkHom
        { toFun := Fin.cases 0 (fun i ↦ (f.toOrderHom i).succ)
          monotone' := by
            intro i j hij
            cases i using Fin.cases with
            | zero => exact Fin.zero_le _
            | succ i =>
              cases j using Fin.cases with
              | zero => exact by simp at hij
              | succ j => exact Fin.succ_le_succ_iff.mpr (f.toOrderHom.monotone
                  (Fin.succ_le_succ_iff.mp hij)) } := by
  ext i : 3
  cases i using Fin.cases with
  | zero => exact prepend_zero f
  | succ i => exact prepend_succ f i

private lemma coneIso_naturality {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    join.map (𝟙 _) (stdSimplex.map f) ≫ (coneIso.{u} n).hom =
      (coneIso m).hom ≫ stdSimplex.map (prepend f) := by
  apply (cancel_epi (coneIso m).inv).mp
  apply SSet.yonedaEquiv.injective
  rw [Iso.inv_hom_id_assoc, SSet.yonedaEquiv_map]
  ext i : 1
  rw [stdSimplex.objEquiv_symm_apply, prepend_eq]
  cases i using Fin.cases with
  | zero =>
      have h : stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ 0) ≫
          (coneIso.{u} m).inv = join.inl _ _ := by
        rw [← coneIso_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have h' : stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ 0) ≫
          ((coneIso.{u} m).inv ≫ join.map (𝟙 _) (stdSimplex.map f) ≫ (coneIso n).hom) =
          stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) := by
        rw [← Category.assoc, ← Category.assoc, h, Category.assoc,
          join.inl_map_assoc, Category.id_comp,
          coneIso_inl]
      have h'' := congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] ↦ SSet.yonedaEquiv k 0) h'
      rw [SSet.yonedaEquiv_comp, stdSimplex.hom_app_apply, SSet.yonedaEquiv_map,
        stdSimplex.objEquiv_symm_apply, SSet.yonedaEquiv_map,
        stdSimplex.objEquiv_symm_apply] at h''
      exact h''
  | succ i =>
      have h : stdSimplex.map (SimplexCategory.δ (0 : Fin (m + 2))) ≫
          (coneIso.{u} m).inv = join.inr _ _ := by
        rw [← coneIso_inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have h' : stdSimplex.map (SimplexCategory.δ (0 : Fin (m + 2))) ≫
          ((coneIso.{u} m).inv ≫ join.map (𝟙 _) (stdSimplex.map f) ≫ (coneIso n).hom) =
          stdSimplex.map f ≫ stdSimplex.map (SimplexCategory.δ 0) := by
        rw [← Category.assoc, ← Category.assoc, h, Category.assoc, join.inr_map_assoc, coneIso_inr]
      have h'' := congrArg (fun k : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1] ↦ SSet.yonedaEquiv k i) h'
      rw [SSet.yonedaEquiv_comp, stdSimplex.hom_app_apply, SSet.yonedaEquiv_map,
        stdSimplex.objEquiv_symm_apply,
        SSet.yonedaEquiv_comp (stdSimplex.map f) (stdSimplex.map (SimplexCategory.δ 0)),
        stdSimplex.hom_app_apply,
        SSet.yonedaEquiv_map, stdSimplex.objEquiv_symm_apply, SSet.yonedaEquiv_map,
        stdSimplex.objEquiv_symm_apply] at h''
      simp only [SimplexCategory.δ] at h''
      exact h''

variable {C : Type u} [Category.{v} C] (x : C)

private noncomputable def cone (n : ℕ) (s : ComposableArrows (Under x) n) :
    join Δ[0] Δ[n] ⟶ nerve C :=
  (coneIso.{max u v} n).hom ≫ SSet.yonedaEquiv.symm
    (ComposableArrows.precomp (s ⋙ Under.forget x) (s.obj 0).hom)

private lemma cone_inl (n : ℕ) (s : ComposableArrows (Under x) n) :
    join.inl Δ[0] Δ[n] ≫ cone x n s = const (nerveEquiv.symm x) := by
  rw [cone, ← Category.assoc, coneIso_inl]
  apply SSet.yonedaEquiv.injective
  simp only [← SSet.yonedaEquiv_naturality]
  rfl

private lemma cone_inr (n : ℕ) (s : ComposableArrows (Under x) n) :
    join.inr Δ[0] Δ[n] ≫ cone x n s =
      (SSet.yonedaEquiv (X := nerve C)).symm (s ⋙ Under.forget x) := by
  rw [cone, ← Category.assoc, coneIso_inr]
  apply SSet.yonedaEquiv.injective
  simp only [← SSet.yonedaEquiv_naturality]
  exact ComposableArrows.precomp_δ₀ _ _

private lemma cone_naturality {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (s : ComposableArrows (Under x) n) :
    join.map (𝟙 _) (stdSimplex.map f) ≫ cone x n s =
      cone x m ((nerve (Under x)).map f.op s) := by
  unfold cone
  rw [← Category.assoc, coneIso_naturality, Category.assoc]
  erw [SSet.yonedaEquiv_symm_naturality_left]
  rw [prepend_eq]
  congr 1
  congr 1
  apply ComposableArrows.ext_succ_of_totalArrow
  · refine Functor.ext (fun i ↦ rfl) ?_
    intro i j g
    -- Both reindexings act on the old vertices through f; the new vertex is fixed.
    change (s.map ((SimplexCategory.toCat.map f).toFunctor.map g)).right =
      eqToHom rfl ≫ (s.map ((SimplexCategory.toCat.map f).toFunctor.map g)).right ≫ eqToHom rfl
    simp
  · erw [ComposableArrows.totalArrow_whiskerLeft]
    -- The nerve map reindexes the extended string along prepend f.
    change (ComposableArrows.precomp (s ⋙ Under.forget x) (s.obj 0).hom).totalArrow
      0 (f.toOrderHom 0).succ (Fin.zero_le _) = _
    erw [ComposableArrows.totalArrow_precomp_zero_succ, ComposableArrows.totalArrow_def]
    -- The first arrow of the target string is its prepended arrow.
    change (⟨x, (s.obj (f.toOrderHom 0)).right,
      (s.obj 0).hom ≫ (s.map (homOfLE (Fin.zero_le (f.toOrderHom 0)))).right⟩ :
      Quiver.Total C) = ⟨x, (s.obj (f.toOrderHom 0)).right, (s.obj (f.toOrderHom 0)).hom⟩
    exact congrArg (fun a ↦ (⟨x, (s.obj (f.toOrderHom 0)).right, a⟩ : Quiver.Total C))
      (Under.w (s.map (homOfLE (Fin.zero_le (f.toOrderHom 0)))))

private noncomputable def coneSimplex {n : ℕ}
    (τ : {τ : join Δ[0] Δ[n] ⟶ nerve C // join.inl _ _ ≫ τ = const (nerveEquiv.symm x)}) :
    {t : ComposableArrows C (n + 1) // t.obj 0 = x} := by
  let t : ComposableArrows C (n + 1) := SSet.yonedaEquiv ((coneIso n).inv ≫ τ.1)
  have ht : t.obj 0 = x := by
    have h : stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
        ((coneIso n).inv ≫ τ.1) = const (nerveEquiv.symm x) := by
      rw [← coneIso_inl, Category.assoc, Iso.hom_inv_id_assoc, τ.2]
    have h' := congrArg (fun k : (Δ[0] : SSet.{max u v}) ⟶ nerve C ↦
      nerveEquiv (SSet.yonedaEquiv k)) h
    erw [← SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_const,
      Equiv.apply_symm_apply] at h'
    exact h'
  exact ⟨t, ht⟩

private noncomputable def uncone {n : ℕ}
    (τ : {τ : join Δ[0] Δ[n] ⟶ nerve C // join.inl _ _ ≫ τ = const (nerveEquiv.symm x)}) :
    ComposableArrows (Under x) n := ComposableArrows.underEquiv x n (coneSimplex x τ)

private lemma cone_uncone {n : ℕ}
    (τ : {τ : join Δ[0] Δ[n] ⟶ nerve C // join.inl _ _ ≫ τ = const (nerveEquiv.symm x)}) :
    cone x n (uncone x τ) = τ.1 := by
  dsimp only [cone, uncone, ComposableArrows.underEquiv, Equiv.coe_fn_mk]
  rw [ComposableArrows.precomp_toUnder]
  -- The value of coneSimplex is the simplex obtained through the join isomorphism.
  change (coneIso n).hom ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv ((coneIso n).inv ≫ τ.1)) = τ.1
  rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

private lemma coneSimplex_cone {n : ℕ} (s : ComposableArrows (Under x) n) :
    coneSimplex x ⟨cone x n s, cone_inl x n s⟩ =
      ⟨ComposableArrows.precomp (s ⋙ Under.forget x) (s.obj 0).hom, rfl⟩ := by
  apply Subtype.ext
  -- Expose just the simplex; its first-vertex proof is irrelevant.
  change SSet.yonedaEquiv ((coneIso n).inv ≫ cone x n s) = _
  erw [cone, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

private lemma uncone_cone {n : ℕ} (s : ComposableArrows (Under x) n) :
    uncone x ⟨cone x n s, cone_inl x n s⟩ = s := by
  rw [uncone, coneSimplex_cone]
  exact (ComposableArrows.underEquiv x n).apply_symm_apply s

private noncomputable def toCosliceApp (n : SimplexCategoryᵒᵖ) :
    (nerve (Under x)).obj n → (coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C)).obj n :=
  fun s ↦ coslice.objEquiv.symm ⟨cone x n.unop.len s, cone_inl x _ s⟩

private lemma toCosliceApp_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (s : (nerve (Under x)).obj n) :
    toCosliceApp x m ((nerve (Under x)).map f s) =
      (coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C)).map f (toCosliceApp x n s) := by
  induction n using Opposite.rec with | op n
  induction m using Opposite.rec with | op m
  induction n using SimplexCategory.rec with | _ n
  induction m using SimplexCategory.rec with | _ m
  apply (coslice.objEquiv (p := (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C))
    (n := op ⦋m⦌)).injective
  apply Subtype.ext
  dsimp only [toCosliceApp]
  erw [coslice.objEquiv_map_coe, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (cone_naturality x f.unop s).symm

private noncomputable def toCoslice :
    nerve (Under x) ⟶ coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C) where
  app n := ↾toCosliceApp x n
  naturality _ _ f := ConcreteCategory.hom_ext _ _ (toCosliceApp_naturality x f)

private instance isIso_toCoslice : IsIso (toCoslice x) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨fun τ ↦ uncone x (coslice.objEquiv τ), ?_, ?_⟩
  · intro s
    -- Evaluation of the bundled map is its defining inverse of objEquiv.
    change uncone x (coslice.objEquiv (coslice.objEquiv.symm
      ⟨cone x n.unop.len s, cone_inl x _ s⟩)) = s
    rw [Equiv.apply_symm_apply]
    exact uncone_cone x s
  · intro τ
    apply coslice.objEquiv.injective
    apply Subtype.ext
    -- Evaluate toCoslice on the recovered under-category simplex.
    change (coslice.objEquiv (coslice.objEquiv.symm
      ⟨cone x n.unop.len (uncone x (coslice.objEquiv τ)), cone_inl x _ _⟩)).1 = _
    rw [Equiv.apply_symm_apply]
    exact cone_uncone x (coslice.objEquiv τ)

/-- The nerve of the under category of x is the coslice of the nerve under x. -/
noncomputable def cosliceIso :
    nerve (Under x) ≅ coslice (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve C) :=
  asIso (toCoslice x)

/-- The base of a coslice simplex is the string obtained by forgetting its structure arrows. -/
@[simp]
lemma cosliceIso_hom_base (n : SimplexCategoryᵒᵖ) (s : (nerve (Under x)).obj n) :
    SSet.yonedaEquiv (join.inr Δ[0] (stdSimplex.obj n.unop) ≫
      (coslice.objEquiv ((cosliceIso x).hom.app n s)).1) = s ⋙ Under.forget x := by
  -- The component of the comparison is the cone on the under-category string.
  change SSet.yonedaEquiv (join.inr _ _ ≫ (coslice.objEquiv (coslice.objEquiv.symm
    ⟨cone x n.unop.len s, cone_inl x _ s⟩)).1) = s ⋙ Under.forget x
  erw [Equiv.apply_symm_apply, cone_inr, Equiv.apply_symm_apply]

/-- The vertex given by an arrow x → y retains that arrow in the coslice. -/
@[simp]
lemma cosliceIso_hom_app_vertex {y : C} (f : x ⟶ y) :
    (coslice.objEquiv ((cosliceIso x).hom.app (op ⦋0⦌)
      (nerveEquiv.symm (Under.mk f)))).1 =
        (join.stdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (ComposableArrows.mk₁ f) := by
  -- Evaluate the defining cone at a zero-length under-category string.
  change (coslice.objEquiv (coslice.objEquiv.symm
    ⟨cone x 0 (nerveEquiv.symm (Under.mk f)), cone_inl x _ _⟩)).1 = _
  rw [Equiv.apply_symm_apply]
  simp only [cone, coneIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso_refl,
    Iso.refl_hom, Functor.map_id, Category.comp_id]
  congr 1
  congr 1
  refine ComposableArrows.ext₁
    (F := ComposableArrows.precomp (nerveEquiv.symm (Under.mk f) ⋙ Under.forget x)
      ((nerveEquiv.symm (Under.mk f)).obj 0).hom)
    (G := ComposableArrows.mk₁ f) rfl rfl ?_
  -- At a vertex, the extended string is exactly the one-arrow string of f.
  change f = 𝟙 _ ≫ f ≫ 𝟙 _
  simp

end CategoryTheory.nerve
