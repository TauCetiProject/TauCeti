/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.IsoCat
public import TauCeti.AlgebraicTopology.SimplexCategory.Augmented
public import TauCeti.AlgebraicTopology.SimplexCategory.EndpointPreserving
public import TauCeti.AlgebraicTopology.SimplicialObject.II
import TauCeti.Order.Hom.Adjoint

/-!
# The duality between finite ordinals and their chains of cuts

A finite ordinal with `n` elements has `n + 1` cuts, forming the ordinal `⦋n⦌` with distinct
least and greatest elements (the empty and the full initial segment, which coincide when
`n = 0`). A monotone map `α : Fin n →o Fin m` acts contravariantly on cuts, sending the cut
`j : Fin (m + 1)` to the number of `i` with `α i < j`, and this cut map preserves both endpoints.
This gives an isomorphism of categories between the opposite `Δ₊ᵒᵖ` of the augmented simplex
category, with the ordinal with `n` elements going to `⦋n⦌`, and the category
`TauCeti.SimplexCategory.EndpointPreserving` (`Δ_∂`) of endpoint-preserving monotone maps.

On nonempty ordinals the cut map is Mathlib's `SimplexCategory.II.map'`, the action of the
Gabriel–Zisman functor `SimplexCategory.II : SimplexCategory ⥤ SimplexCategoryᵒᵖ` on morphisms.
Its characteristic property is the Galois condition `i < cut α j ↔ α i < j`
(`SimplexCategory.II.castSucc_lt_map'_iff`, `TauCeti.SimplexCategory.castSucc_lt_cutOrderHom_iff`).
For an endpoint-preserving `β : Fin (n + 1) →o Fin (m + 1)` the map `Fin m →o Fin n` sending `i` to
the greatest `j` with `β j ≤ i` satisfies the same condition, so it is the inverse of the cut map
(`TauCeti.SimplexCategory.uncutOrderHom`).

## Main definitions and results

* `TauCeti.SimplexCategory.cutOrderHom`, `TauCeti.SimplexCategory.uncutOrderHom`: the cut map
  of a monotone map of finite ordinals and its inverse, with the Galois conditions
  characterizing them, their functoriality, and `cutOrderHom_uncutOrderHom`,
  `uncutOrderHom_cutOrderHom`.
* `TauCeti.SimplexCategory.II.toEndpointPreserving`: the functor `SimplexCategory.II`, with
  opposites arranged as `Δᵒᵖ ⥤ Δ`, factored through `Δ_∂`.
* `TauCeti.AugmentedSimplexCategory.cut : Δ₊ᵒᵖ ⥤ Δ_∂`, which extends `II.toEndpointPreserving`
  to the empty ordinal by sending it to `⦋0⦌` (`inclusion_op_comp_cut`), its explicit inverse
  `TauCeti.AugmentedSimplexCategory.uncut`, the two identities `cut_comp_uncut` and
  `uncut_comp_cut`, and the resulting isomorphism of categories
  `TauCeti.AugmentedSimplexCategory.cutIsoCat`.

## References

* P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*, chapter III, §1.1.
* E. Riehl, D. Verity, *Homotopy coherent adjunctions and the formal theory of monads*,
  Advances in Mathematics 286 (2016), §3.3.
-/

public section

open CategoryTheory Opposite Simplicial

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-! ### Cut maps of finite ordinals -/

/-- The cut map of a monotone map `α : Fin n →o Fin m` of finite ordinals: it sends the cut
`j : Fin (m + 1)` of `Fin m` to the cut of `Fin n` whose lower part is the set of `i` with
`α i < j`, that is, to the number of these `i`. On nonempty ordinals it is `II.map'`. -/
def cutOrderHom : {n m : ℕ} → (Fin n →o Fin m) → (Fin (m + 1) →o Fin (n + 1))
  | 0, _, _ => OrderHom.const _ 0
  | _ + 1, 0, α => (α 0).elim0
  | _ + 1, _ + 1, α => ⟨II.map' α, II.monotone_map' α⟩

lemma cutOrderHom_succ_succ {n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1)) :
    ⇑(cutOrderHom α) = II.map' α := by
  simp [cutOrderHom]

variable {n m p : ℕ}

/-- The Galois condition characterizing `cutOrderHom α`: the elements below `cutOrderHom α j`
are the `i` with `α i < j`. -/
@[simp]
lemma castSucc_lt_cutOrderHom_iff (α : Fin n →o Fin m) (i : Fin n) (j : Fin (m + 1)) :
    i.castSucc < cutOrderHom α j ↔ (α i).castSucc < j :=
  match n, m, α with
  | 0, _, _ => i.elim0
  | _ + 1, 0, α => (α i).elim0
  | _ + 1, _ + 1, α => II.castSucc_lt_map'_iff α j i

/-- `cutOrderHom α j` is the unique `x` satisfying the Galois condition. -/
lemma eq_cutOrderHom_apply_iff (α : Fin n →o Fin m) (j : Fin (m + 1)) (x : Fin (n + 1)) :
    x = cutOrderHom α j ↔ ∀ i : Fin n, i.castSucc < x ↔ (α i).castSucc < j := by
  refine ⟨fun h i ↦ h ▸ castSucc_lt_cutOrderHom_iff α i j, fun h ↦ ?_⟩
  have key {x y : Fin (n + 1)} (hxy : ∀ i : Fin n, i.castSucc < x → i.castSucc < y) : x ≤ y :=
    le_of_forall_lt fun c hc ↦ by
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (hc.trans_le (Fin.le_last _)).ne
      exact hxy i hc
  exact le_antisymm (key fun i hi ↦ (castSucc_lt_cutOrderHom_iff α i j).2 ((h i).1 hi))
    (key fun i hi ↦ (h i).2 ((castSucc_lt_cutOrderHom_iff α i j).1 hi))

@[simp]
lemma cutOrderHom_zero (α : Fin n →o Fin m) : cutOrderHom α 0 = 0 :=
  ((eq_cutOrderHom_apply_iff α 0 0).2 fun i ↦ by simp).symm

@[simp]
lemma cutOrderHom_last (α : Fin n →o Fin m) : cutOrderHom α (Fin.last m) = Fin.last n :=
  ((eq_cutOrderHom_apply_iff α _ _).2 fun i ↦ by simp [Fin.castSucc_lt_last]).symm

@[simp]
lemma cutOrderHom_id : cutOrderHom (OrderHom.id : Fin n →o Fin n) = OrderHom.id := by
  ext j : 2
  exact ((eq_cutOrderHom_apply_iff _ j j).2 fun i ↦ Iff.rfl).symm

@[simp]
lemma cutOrderHom_comp (f : Fin n →o Fin m) (g : Fin m →o Fin p) :
    cutOrderHom (g.comp f) = (cutOrderHom f).comp (cutOrderHom g) := by
  ext j : 2
  refine ((eq_cutOrderHom_apply_iff _ j _).2 fun i ↦ ?_).symm
  simp

/-! ### The inverse of the cut map -/

/-- The greatest `j` with `β j ≤ i.castSucc` is not the greatest vertex, since `β` preserves
it. -/
private lemma rightAdjoint_castSucc_ne_last (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) (i : Fin m) :
    β.rightAdjoint h₀ i.castSucc ≠ Fin.last n := fun he ↦
  (Fin.castSucc_lt_last i).not_ge <| h ▸ (OrderHom.le_rightAdjoint_iff β h₀).mp he.ge

/-- For a monotone map `β : Fin (n + 1) →o Fin (m + 1)` preserving both endpoints, the monotone
map `Fin m →o Fin n` sending `i` to the greatest `j` with `β j ≤ i`. It is the inverse of
`cutOrderHom` (`cutOrderHom_uncutOrderHom`, `uncutOrderHom_cutOrderHom`). -/
def uncutOrderHom (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) : Fin m →o Fin n where
  toFun i := (β.rightAdjoint h₀ i.castSucc).castPred (rightAdjoint_castSucc_ne_last β h₀ h i)
  monotone' _ _ hii' := Fin.castPred_le_castPred_iff.mpr
    ((β.rightAdjoint h₀).monotone (Fin.castSucc_le_castSucc_iff.mpr hii'))

/-- Embedding `uncutOrderHom β h₀ h i` via `Fin.castSucc` recovers
`β.rightAdjoint h₀ i.castSucc`. -/
private lemma castSucc_uncutOrderHom (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) (i : Fin m) :
    (uncutOrderHom β h₀ h i).castSucc = β.rightAdjoint h₀ i.castSucc :=
  Fin.castSucc_castPred _ (rightAdjoint_castSucc_ne_last β h₀ h i)

/-- The Galois condition characterizing `uncutOrderHom β h₀ h`: it lies below `j` exactly when
`i < β j`. -/
@[simp]
lemma castSucc_uncutOrderHom_lt_iff (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) (i : Fin m) (j : Fin (n + 1)) :
    (uncutOrderHom β h₀ h i).castSucc < j ↔ i.castSucc < β j := by
  rw [castSucc_uncutOrderHom, ← not_le, OrderHom.le_rightAdjoint_iff, not_le]

/-- `uncutOrderHom β h₀ h i` is the unique `a` satisfying the Galois condition. -/
lemma eq_uncutOrderHom_apply_iff (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) (i : Fin m) (a : Fin n) :
    a = uncutOrderHom β h₀ h i ↔ ∀ j : Fin (n + 1), a.castSucc < j ↔ i.castSucc < β j := by
  refine ⟨fun ha j ↦ ha ▸ castSucc_uncutOrderHom_lt_iff β h₀ h i j, fun H ↦ ?_⟩
  have key {a b : Fin n} (hab : ∀ j : Fin (n + 1), a.castSucc < j → b.castSucc < j) : b ≤ a :=
    Fin.castSucc_lt_succ_iff.1 (hab a.succ Fin.castSucc_lt_succ)
  exact le_antisymm
    (key fun j hj ↦ (H j).2 ((castSucc_uncutOrderHom_lt_iff β h₀ h i j).1 hj))
    (key fun j hj ↦ (castSucc_uncutOrderHom_lt_iff β h₀ h i j).2 ((H j).1 hj))

@[simp]
lemma uncutOrderHom_id (h₀ : (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) 0 = 0)
    (h : (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) (Fin.last n) = Fin.last n) :
    uncutOrderHom OrderHom.id h₀ h = OrderHom.id := by
  ext i : 2
  exact Fin.castSucc_inj.mp (by simp [castSucc_uncutOrderHom, OrderHom.rightAdjoint_id])

lemma uncutOrderHom_comp (β : Fin (n + 1) →o Fin (m + 1)) (γ : Fin (m + 1) →o Fin (p + 1))
    (hβ₀ : β 0 = 0) (hβ : β (Fin.last n) = Fin.last m) (hγ₀ : γ 0 = 0)
    (hγ : γ (Fin.last m) = Fin.last p) (h₀ : (γ.comp β) 0 = 0)
    (h : (γ.comp β) (Fin.last n) = Fin.last p) :
    uncutOrderHom (γ.comp β) h₀ h = (uncutOrderHom β hβ₀ hβ).comp (uncutOrderHom γ hγ₀ hγ) := by
  ext i : 2
  exact Fin.castSucc_inj.mp
    (by simp [castSucc_uncutOrderHom, OrderHom.rightAdjoint_comp hβ₀ hγ₀ h₀])

@[simp]
lemma cutOrderHom_uncutOrderHom (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) : cutOrderHom (uncutOrderHom β h₀ h) = β := by
  ext j : 2
  refine ((eq_cutOrderHom_apply_iff _ j _).2 fun i ↦ ?_).symm
  rw [castSucc_uncutOrderHom_lt_iff]

@[simp]
lemma uncutOrderHom_cutOrderHom (α : Fin n →o Fin m) (h₀ : cutOrderHom α 0 = 0)
    (h : cutOrderHom α (Fin.last m) = Fin.last n) :
    uncutOrderHom (cutOrderHom α) h₀ h = α := by
  ext i : 2
  refine ((eq_uncutOrderHom_apply_iff _ h₀ h i _).2 fun j ↦ ?_).symm
  rw [castSucc_lt_cutOrderHom_iff]

/-! ### Factoring `II` through endpoint-preserving maps -/

/-- The Gabriel–Zisman functor `SimplexCategory.II`, with opposites arranged as `Δᵒᵖ ⥤ Δ`, as a
functor to the endpoint-preserving maps `Δ_∂`: it sends `⦋n⦌` to `⦋n + 1⦌`, its chain of cuts. -/
@[expose, simps obj]
def II.toEndpointPreserving : SimplexCategoryᵒᵖ ⥤ EndpointPreserving where
  obj X := EndpointPreserving.mk (X.unop.len + 1)
  map f := EndpointPreserving.homMk (II.map f.unop).unop (II.map'_zero _) (II.map'_last _)
  -- After `simp only`, each `rfl` unfolds `II.obj ⦋n⦌` to the object `⦋n + 1⦌` of `mk (n + 1)`
  -- and the identity and composition of `WideSubcategory` to those of `SimplexCategory`.
  map_id X := WideSubcategory.hom_ext _ (by simp only [unop_id, II.map_id]; rfl)
  map_comp f g := WideSubcategory.hom_ext _ (by simp only [unop_comp, II.map_comp]; rfl)

@[simp]
lemma II.toEndpointPreserving_map_hom {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y) :
    (II.toEndpointPreserving.map f).hom = (II.map f.unop).unop := rfl

/-- `II.toEndpointPreserving` sends the face `δ i` to the degeneracy `σ i`. -/
@[simp]
lemma II.toEndpointPreserving_map_δ_op {n : ℕ} (i : Fin (n + 2)) :
    II.toEndpointPreserving.map (SimplexCategory.δ i).op = EndpointPreserving.σ i :=
  WideSubcategory.hom_ext _ (by
    rw [II.toEndpointPreserving_map_hom, EndpointPreserving.σ_hom]
    exact congrArg Quiver.Hom.unop (II_δ i))

/-- `II.toEndpointPreserving` sends the degeneracy `σ i` to the inner face
`δ i.succ.castSucc`. -/
@[simp]
lemma II.toEndpointPreserving_map_σ_op {n : ℕ} (i : Fin (n + 1)) :
    II.toEndpointPreserving.map (SimplexCategory.σ i).op = EndpointPreserving.δ i :=
  WideSubcategory.hom_ext _ (by
    rw [II.toEndpointPreserving_map_hom, EndpointPreserving.δ_hom]
    exact congrArg Quiver.Hom.unop (II_σ i))

/-- `II.toEndpointPreserving` factors `SimplexCategory.II`, as a functor `Δᵒᵖ ⥤ Δ`, through the
inclusion `Δ_∂ ⥤ Δ`. -/
lemma II.toEndpointPreserving_comp_inclusion :
    II.toEndpointPreserving ⋙ wideSubcategoryInclusion _ = Functor.leftOp II :=
  rfl

end TauCeti.SimplexCategory

namespace TauCeti.AugmentedSimplexCategory

open _root_.SimplexCategory _root_.AugmentedSimplexCategory TauCeti.SimplexCategory

/-! ### The cut duality -/

/-- The functor `Δ₊ᵒᵖ ⥤ Δ_∂` sending the ordinal with `n` elements to `⦋n⦌`, its chain of cuts,
and a monotone map to its cut map `TauCeti.SimplexCategory.cutOrderHom`. -/
@[expose, simps obj]
def cut : AugmentedSimplexCategoryᵒᵖ ⥤ EndpointPreserving where
  obj X := EndpointPreserving.mk X.unop.card
  map f := EndpointPreserving.homMk (mkHom (cutOrderHom (toOrderHom f.unop))) (cutOrderHom_zero _)
    (cutOrderHom_last _)
  map_id X := EndpointPreserving.hom_ext' (by simp)
  map_comp f g := EndpointPreserving.hom_ext' (by simp)

@[simp]
lemma cut_map_hom_toOrderHom {X Y : AugmentedSimplexCategoryᵒᵖ} (f : X ⟶ Y) :
    (cut.map f).hom.toOrderHom = cutOrderHom (toOrderHom f.unop) := rfl

/-- On nonempty ordinals, `cut` is the Gabriel–Zisman functor `II`. -/
lemma inclusion_op_comp_cut : inclusion.op ⋙ cut = II.toEndpointPreserving :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq (EndpointPreserving.hom_ext' <|
    (congrArg cutOrderHom (toOrderHom_inclusion_map f.unop)).trans
      (OrderHom.ext _ _ (cutOrderHom_succ_succ _)))

/-- The inverse `Δ_∂ ⥤ Δ₊ᵒᵖ` of the cut functor: it sends `⦋n⦌` to the ordinal with `n` elements
and an endpoint-preserving map to `TauCeti.SimplexCategory.uncutOrderHom`. -/
@[expose, simps obj]
def uncut :
    EndpointPreserving ⥤ AugmentedSimplexCategoryᵒᵖ where
  obj X := op (ofCard X.obj.len)
  map f := (homOfOrderHom (uncutOrderHom f.hom.toOrderHom
    (EndpointPreserving.hom_toOrderHom_zero f) (EndpointPreserving.hom_toOrderHom_last f))).op
  map_id X := Quiver.Hom.unop_inj (by simp)
  map_comp f g := Quiver.Hom.unop_inj (by simp [uncutOrderHom_comp])

@[simp]
lemma uncut_map_unop {X Y : EndpointPreserving} (f : X ⟶ Y) :
    (uncut.map f).unop = homOfOrderHom (uncutOrderHom f.hom.toOrderHom
      (EndpointPreserving.hom_toOrderHom_zero f) (EndpointPreserving.hom_toOrderHom_last f)) :=
  rfl

/-- `uncut` is a left inverse of `cut`: one half of the isomorphism of categories
`Δ₊ᵒᵖ ≅ Δ_∂`. -/
theorem cut_comp_uncut : cut ⋙ uncut = 𝟭 _ := by
  refine CategoryTheory.Functor.hext (fun X ↦ congrArg op (ofCard_card X.unop)) fun X Y f ↦ ?_
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  -- After the case split both sides have definitionally equal types, so `≍` becomes `=`.
  cases X <;> cases Y
  · refine heq_of_eq (Quiver.Hom.unop_inj (hom_ext ?_))
    exact (toOrderHom_homOfOrderHom _).trans
      (uncutOrderHom_cutOrderHom _ (cutOrderHom_zero _) (cutOrderHom_last _))
  · exact heq_of_eq (Quiver.Hom.unop_inj (WithInitial.starInitial.hom_ext _ _))
  · exact (f.unop : PEmpty).elim
  · exact heq_of_eq (Quiver.Hom.unop_inj (WithInitial.starInitial.hom_ext _ _))

/-- `uncut` is a right inverse of `cut`: the other half of the isomorphism of categories
`Δ₊ᵒᵖ ≅ Δ_∂`. -/
theorem uncut_comp_cut : uncut ⋙ cut = 𝟭 _ := by
  refine CategoryTheory.Functor.hext (fun X ↦ ?_) fun X Y f ↦ ?_
  · obtain ⟨⟨n⟩⟩ := X
    exact congrArg EndpointPreserving.mk (card_ofCard n)
  · obtain ⟨⟨n⟩⟩ := X
    obtain ⟨⟨m⟩⟩ := Y
    cases n <;> cases m <;> refine heq_of_eq (EndpointPreserving.hom_ext' ?_)
    · ext i : 2
      exact Subsingleton.elim (α := Fin 1) _ _
    · have h := EndpointPreserving.hom_toOrderHom_last f
      rw [Fin.last_zero, EndpointPreserving.hom_toOrderHom_zero] at h
      simp [Fin.ext_iff] at h
    · ext i : 2
      exact Subsingleton.elim (α := Fin 1) _ _
    · exact (congrArg cutOrderHom (toOrderHom_homOfOrderHom _)).trans
        (cutOrderHom_uncutOrderHom _ (EndpointPreserving.hom_toOrderHom_zero f)
          (EndpointPreserving.hom_toOrderHom_last f))

/-- The isomorphism of categories `Δ₊ᵒᵖ ≅ Δ_∂` given by the cut functor and its inverse. The
underlying equivalence is `cutIsoCat.toEquivalence`. -/
@[expose, simps functor inverse]
def cutIsoCat : IsoCat AugmentedSimplexCategoryᵒᵖ EndpointPreserving where
  functor := cut
  inverse := uncut
  unit_eq := cut_comp_uncut.symm
  counit_eq := uncut_comp_cut

end TauCeti.AugmentedSimplexCategory
