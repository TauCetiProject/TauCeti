/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.II
public import TauCeti.AlgebraicTopology.SimplexCategory.EndpointPreserving

/-!
# The duality between finite ordinals and their chains of cuts

A finite ordinal with `n` elements has `n + 1` cuts, forming the ordinal `⦋n⦌` with distinct
least and greatest elements (the empty and the full initial segment, which coincide when
`n = 0`). A monotone map `α : Fin n →o Fin m` acts contravariantly on cuts, sending the cut
`j : Fin (m + 1)` to the number of `i` with `α i < j`, and this cut map preserves both endpoints.
This gives an isomorphism of categories between the opposite `Δ₊ᵒᵖ` of the augmented simplex
category, with the ordinal with `n` elements going to `⦋n⦌`, and the category
`SimplexCategory.EndpointPreserving` (`Δ_∂`) of endpoint-preserving monotone maps.

On nonempty ordinals the cut map is Mathlib's `SimplexCategory.II.map'`, the action of the
Gabriel–Zisman functor `SimplexCategory.II : SimplexCategory ⥤ SimplexCategoryᵒᵖ` on morphisms.
Its characteristic property is the Galois condition `i < cut α j ↔ α i < j`
(`SimplexCategory.II.castSucc_lt_map'_iff`, `SimplexCategory.castSucc_lt_cutOrderHom_iff`). For
an endpoint-preserving `β : Fin (n + 1) →o Fin (m + 1)` the map `Fin m →o Fin n` sending `i` to
the greatest `j` with `β j ≤ i` satisfies the same condition, so it is the inverse of the cut map
(`SimplexCategory.uncutOrderHom`).

## Main definitions and results

* `SimplexCategory.cutOrderHom`, `SimplexCategory.uncutOrderHom`: the cut map of a monotone map
  of finite ordinals and its inverse, with the Galois conditions characterizing them, their
  functoriality, and `cutOrderHom_uncutOrderHom`, `uncutOrderHom_cutOrderHom`.
* `SimplexCategory.II.toEndpointPreserving`: the functor `SimplexCategory.II`, with opposites
  arranged as `Δᵒᵖ ⥤ Δ`, factored through `Δ_∂`.
* `AugmentedSimplexCategory.card`, `AugmentedSimplexCategory.toOrderHom`: the number of elements
  of an augmented simplex object and the monotone map underlying a morphism, and
  `AugmentedSimplexCategory.ofCard`, `AugmentedSimplexCategory.homOfOrderHom` in the other
  direction.
* `AugmentedSimplexCategory.cut : Δ₊ᵒᵖ ⥤ Δ_∂`, which extends `II.toEndpointPreserving` to the
  empty ordinal by sending it to `⦋0⦌` (`AugmentedSimplexCategory.inclusion_op_comp_cut`), its
  explicit inverse `AugmentedSimplexCategory.uncut`, the two identities
  `AugmentedSimplexCategory.cut_comp_uncut` and `AugmentedSimplexCategory.uncut_comp_cut`, and
  the resulting equivalence `AugmentedSimplexCategory.cutEquivalence`.

## References

* P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*, chapter III, §1.1.
* E. Riehl, D. Verity, *Homotopy coherent adjunctions and the formal theory of monads*,
  Advances in Mathematics 286 (2016), §3.3.
-/

public section

open CategoryTheory Opposite Simplicial

namespace SimplexCategory

namespace II

/-- The Galois condition characterizing `II.map' f`: the elements below `II.map' f x` are the
`i` with `f i < x`. -/
@[simp]
lemma castSucc_lt_map'_iff {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2))
    (i : Fin (n + 1)) : i.castSucc < map' f x ↔ (f i).castSucc < x := by
  constructor
  · intro h
    by_contra! hx
    exact h.not_ge (Finset.min'_le _ _ ((castSucc_mem_finset_iff f x i).2 hx))
  · intro h
    by_contra! hle
    obtain ⟨y, hy⟩ := Fin.eq_castSucc_of_ne_last (hle.trans_lt (Fin.castSucc_lt_last i)).ne
    rw [← hy, Fin.castSucc_le_castSucc_iff] at hle
    exact h.not_ge (((map'_eq_castSucc_iff f x y).1 hy.symm).1.trans
      (Fin.castSucc_le_castSucc_iff.2 (f.monotone hle)))

end II

/-! ### Cut maps of finite ordinals -/

/-- The cut map of a monotone map `α : Fin n →o Fin m` of finite ordinals: it sends the cut
`j : Fin (m + 1)` of `Fin m` to the cut of `Fin n` below the elements `i` with `α i < j`, that
is, to the number of these `i`. On nonempty ordinals it is `II.map'`. -/
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

lemma cutOrderHom_comp (f : Fin n →o Fin m) (g : Fin m →o Fin p) :
    cutOrderHom (g.comp f) = (cutOrderHom f).comp (cutOrderHom g) := by
  ext j : 2
  refine ((eq_cutOrderHom_apply_iff _ j _).2 fun i ↦ ?_).symm
  simp

/-! ### The inverse of the cut map -/

/-- For a monotone map `β : Fin (n + 1) →o Fin (m + 1)` preserving both endpoints, the monotone
map `Fin m →o Fin n` sending `i` to the greatest `j` with `β j ≤ i`. It is the inverse of
`cutOrderHom` (`cutOrderHom_uncutOrderHom`, `uncutOrderHom_cutOrderHom`). -/
def uncutOrderHom (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) : Fin m →o Fin n where
  toFun i := ((Finset.univ.filter fun j ↦ β j ≤ i.castSucc).max'
      (Finset.filter_nonempty_iff.2 ⟨0, Finset.mem_univ _, by simp [h₀]⟩)).castPred
    fun he ↦ by
      have hmem := Finset.max'_mem (Finset.univ.filter fun j ↦ β j ≤ i.castSucc)
        (Finset.filter_nonempty_iff.2 ⟨0, Finset.mem_univ _, by simp [h₀]⟩)
      rw [he] at hmem
      simp [h] at hmem
  monotone' i i' hii' := by
    rw [Fin.castPred_le_castPred_iff]
    exact Finset.max'_subset _ fun j ↦ by
      simpa using fun hj ↦ hj.trans (Fin.castSucc_le_castSucc_iff.2 hii')

/-- The Galois condition characterizing `uncutOrderHom β h₀ h`: it lies below `j` exactly when
`i < β j`. -/
@[simp]
lemma uncutOrderHom_castSucc_lt_iff (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) (i : Fin m) (j : Fin (n + 1)) :
    (uncutOrderHom β h₀ h i).castSucc < j ↔ i.castSucc < β j := by
  have hi : (uncutOrderHom β h₀ h i).castSucc =
      (Finset.univ.filter fun j ↦ β j ≤ i.castSucc).max'
      (Finset.filter_nonempty_iff.2 ⟨0, Finset.mem_univ _, by simp [h₀]⟩) :=
    rfl
  rw [hi, Finset.max'_lt_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun H ↦ ?_, fun H s hs ↦ ?_⟩
  · by_contra! hj
    exact (H j hj).false
  · by_contra! hjs
    exact (H.trans_le (β.monotone hjs)).not_ge hs

/-- `uncutOrderHom β h₀ h i` is the unique `a` satisfying the Galois condition. -/
lemma eq_uncutOrderHom_apply_iff (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) (i : Fin m) (a : Fin n) :
    a = uncutOrderHom β h₀ h i ↔ ∀ j : Fin (n + 1), a.castSucc < j ↔ i.castSucc < β j := by
  refine ⟨fun ha j ↦ ha ▸ uncutOrderHom_castSucc_lt_iff β h₀ h i j, fun H ↦ ?_⟩
  have key {a b : Fin n} (hab : ∀ j : Fin (n + 1), a.castSucc < j → b.castSucc < j) : b ≤ a :=
    Fin.castSucc_lt_succ_iff.1 (hab a.succ Fin.castSucc_lt_succ)
  exact le_antisymm
    (key fun j hj ↦ (H j).2 ((uncutOrderHom_castSucc_lt_iff β h₀ h i j).1 hj))
    (key fun j hj ↦ (uncutOrderHom_castSucc_lt_iff β h₀ h i j).2 ((H j).1 hj))

@[simp]
lemma uncutOrderHom_id (h₀ : (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) 0 = 0)
    (h : (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) (Fin.last n) = Fin.last n) :
    uncutOrderHom OrderHom.id h₀ h = OrderHom.id := by
  ext i : 2
  exact ((eq_uncutOrderHom_apply_iff _ h₀ h i i).2 fun j ↦ Iff.rfl).symm

lemma uncutOrderHom_comp (β : Fin (n + 1) →o Fin (m + 1)) (γ : Fin (m + 1) →o Fin (p + 1))
    (hβ₀ : β 0 = 0) (hβ : β (Fin.last n) = Fin.last m) (hγ₀ : γ 0 = 0)
    (hγ : γ (Fin.last m) = Fin.last p) (h₀ : (γ.comp β) 0 = 0)
    (h : (γ.comp β) (Fin.last n) = Fin.last p) :
    uncutOrderHom (γ.comp β) h₀ h = (uncutOrderHom β hβ₀ hβ).comp (uncutOrderHom γ hγ₀ hγ) := by
  ext i : 2
  refine ((eq_uncutOrderHom_apply_iff _ h₀ h i _).2 fun j ↦ ?_).symm
  simp

@[simp]
lemma cutOrderHom_uncutOrderHom (β : Fin (n + 1) →o Fin (m + 1)) (h₀ : β 0 = 0)
    (h : β (Fin.last n) = Fin.last m) : cutOrderHom (uncutOrderHom β h₀ h) = β := by
  ext j : 2
  refine ((eq_cutOrderHom_apply_iff _ j _).2 fun i ↦ ?_).symm
  rw [uncutOrderHom_castSucc_lt_iff]

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

lemma II.toEndpointPreserving_comp_inclusion :
    II.toEndpointPreserving ⋙ wideSubcategoryInclusion _ = Functor.leftOp II :=
  rfl

end SimplexCategory

namespace AugmentedSimplexCategory

open SimplexCategory

/-! ### Finite ordinals in the augmented simplex category -/

/-- The number of elements of an object of the augmented simplex category: `0` for the empty
ordinal and `n + 1` for `⦋n⦌`. -/
@[expose]
def card : AugmentedSimplexCategory → ℕ
  | .star => 0
  | .of x => x.len + 1

@[simp]
lemma card_star : card .star = 0 := rfl

@[simp]
lemma card_of (x : SimplexCategory) : card (.of x) = x.len + 1 := rfl

/-- The monotone map of finite ordinals underlying a morphism of the augmented simplex
category. -/
@[expose]
def toOrderHom : {X Y : AugmentedSimplexCategory} → (X ⟶ Y) → (Fin X.card →o Fin Y.card)
  | .of _, .of _, f => (WithInitial.down f).toOrderHom
  | .star, _, _ => ⟨fun a ↦ a.elim0, fun a ↦ a.elim0⟩
  | .of _, .star, f => (f : PEmpty).elim

@[simp]
lemma toOrderHom_of {x y : SimplexCategory} (f : WithInitial.of x ⟶ WithInitial.of y) :
    toOrderHom f = (WithInitial.down f).toOrderHom := rfl

@[simp]
lemma toOrderHom_id (X : AugmentedSimplexCategory) : toOrderHom (𝟙 X) = OrderHom.id := by
  cases X with
  | of x => exact id_toOrderHom x
  | star => ext a; exact a.elim0

@[simp]
lemma toOrderHom_comp {X Y Z : AugmentedSimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toOrderHom (f ≫ g) = (toOrderHom g).comp (toOrderHom f) :=
  match X, Y, Z, f, g with
  | .of _, .of _, .of _, _, _ => rfl
  | .star, _, _, _, _ => by ext a; exact a.elim0
  | .of _, .star, _, f, _ => (f : PEmpty).elim
  | .of _, .of _, .star, _, g => (g : PEmpty).elim

lemma hom_ext {X Y : AugmentedSimplexCategory} {f g : X ⟶ Y}
    (h : toOrderHom f = toOrderHom g) : f = g :=
  match X, Y, f, g with
  | .of _, .of _, _, _ => Hom.ext _ _ h
  | .star, _, _, _ => (WithInitial.starInitial.hom_ext _ _)
  | .of _, .star, f, _ => (f : PEmpty).elim

/-- The object of the augmented simplex category with `n` elements: the empty ordinal for
`n = 0` and `⦋n - 1⦌` otherwise. -/
@[expose]
def ofCard : ℕ → AugmentedSimplexCategory
  | 0 => .star
  | n + 1 => .of ⦋n⦌

@[simp]
lemma ofCard_zero : ofCard 0 = .star := rfl

@[simp]
lemma ofCard_succ (n : ℕ) : ofCard (n + 1) = .of ⦋n⦌ := rfl

lemma card_ofCard (n : ℕ) : card (ofCard n) = n := by
  cases n <;> rfl

lemma ofCard_card (X : AugmentedSimplexCategory) : ofCard (card X) = X := by
  cases X <;> rfl

/-- The morphism of the augmented simplex category given by a monotone map of finite
ordinals. -/
@[expose]
def homOfOrderHom : {n m : ℕ} → (Fin n →o Fin m) → (ofCard n ⟶ ofCard m)
  | 0, _, _ => WithInitial.starInitial.to _
  | _ + 1, 0, f => (f 0).elim0
  | _ + 1, _ + 1, f => (mkHom f : ⦋_⦌ ⟶ ⦋_⦌)

@[simp]
lemma down_homOfOrderHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) :
    WithInitial.down (homOfOrderHom f) = mkHom f := rfl

@[simp]
lemma homOfOrderHom_id (n : ℕ) : homOfOrderHom (OrderHom.id : Fin n →o Fin n) = 𝟙 _ := by
  cases n with
  | zero => exact WithInitial.starInitial.hom_ext _ _
  | succ n => rfl

@[simp]
lemma homOfOrderHom_comp {n m p : ℕ} (f : Fin n →o Fin m) (g : Fin m →o Fin p) :
    homOfOrderHom (g.comp f) = homOfOrderHom f ≫ homOfOrderHom g :=
  match n, m, p, f, g with
  | 0, _, _, _, _ => WithInitial.starInitial.hom_ext _ _
  | _ + 1, 0, _, f, _ => (f 0).elim0
  | _ + 1, _ + 1, 0, _, g => (g 0).elim0
  | _ + 1, _ + 1, _ + 1, _, _ => rfl

/-! ### The cut duality -/

/-- The functor `Δ₊ᵒᵖ ⥤ Δ_∂` sending the ordinal with `n` elements to `⦋n⦌`, its chain of cuts,
and a monotone map to its cut map `SimplexCategory.cutOrderHom`. -/
@[expose, simps obj]
def cut : AugmentedSimplexCategoryᵒᵖ ⥤ EndpointPreserving where
  obj X := EndpointPreserving.mk X.unop.card
  map f := EndpointPreserving.homMk (mkHom (cutOrderHom (toOrderHom f.unop))) (cutOrderHom_zero _)
    (cutOrderHom_last _)
  map_id X := EndpointPreserving.hom_ext' (by simp)
  map_comp f g := EndpointPreserving.hom_ext' (by simp [cutOrderHom_comp])

@[simp]
lemma cut_map_hom_toOrderHom {X Y : AugmentedSimplexCategoryᵒᵖ} (f : X ⟶ Y) :
    (cut.map f).hom.toOrderHom = cutOrderHom (toOrderHom f.unop) := rfl

/-- On nonempty ordinals, `cut` is the Gabriel–Zisman functor `II`. -/
lemma inclusion_op_comp_cut : inclusion.op ⋙ cut = II.toEndpointPreserving :=
  -- `cutOrderHom` is defined to be `II.map'` on nonempty ordinals.
  (rfl)

/-- The inverse `Δ_∂ ⥤ Δ₊ᵒᵖ` of the cut functor: it sends `⦋n⦌` to the ordinal with `n` elements
and an endpoint-preserving map to `SimplexCategory.uncutOrderHom`. -/
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

theorem cut_comp_uncut : cut ⋙ uncut = 𝟭 _ := by
  refine CategoryTheory.Functor.hext (fun X ↦ congrArg op (ofCard_card X.unop)) fun X Y f ↦ ?_
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  -- After the case split both sides have definitionally equal types, so `≍` becomes `=`.
  cases X <;> cases Y
  · refine heq_of_eq (Quiver.Hom.unop_inj (hom_ext ?_))
    exact uncutOrderHom_cutOrderHom _ (cutOrderHom_zero _) (cutOrderHom_last _)
  · exact heq_of_eq (Quiver.Hom.unop_inj (WithInitial.starInitial.hom_ext _ _))
  · exact (f.unop : PEmpty).elim
  · exact heq_of_eq (Quiver.Hom.unop_inj (WithInitial.starInitial.hom_ext _ _))

theorem uncut_comp_cut : uncut ⋙ cut = 𝟭 _ := by
  refine CategoryTheory.Functor.hext (fun X ↦ ?_) fun X Y f ↦ ?_
  · obtain ⟨⟨n⟩⟩ := X
    cases n <;> rfl
  · obtain ⟨⟨n⟩⟩ := X
    obtain ⟨⟨m⟩⟩ := Y
    cases n <;> cases m <;> refine heq_of_eq (EndpointPreserving.hom_ext' ?_)
    · ext i : 2
      exact Subsingleton.elim (α := Fin 1) _ _
    · have h := (EndpointPreserving.hom_toOrderHom_zero f).symm.trans
        (EndpointPreserving.hom_toOrderHom_last f)
      simp [Fin.ext_iff] at h
    · ext i : 2
      exact Subsingleton.elim (α := Fin 1) _ _
    · -- On nonempty ordinals `toOrderHom (homOfOrderHom g)` is `g` by definition.
      exact cutOrderHom_uncutOrderHom _ (EndpointPreserving.hom_toOrderHom_zero f)
        (EndpointPreserving.hom_toOrderHom_last f)

/-- The isomorphism of categories `Δ₊ᵒᵖ ≌ Δ_∂` given by the cut functor and its inverse, with
identity unit and counit up to `eqToIso`. -/
def cutEquivalence : AugmentedSimplexCategoryᵒᵖ ≌ EndpointPreserving where
  functor := cut
  inverse := uncut
  unitIso := eqToIso cut_comp_uncut.symm
  counitIso := eqToIso uncut_comp_cut
  functor_unitIso_comp X := by
    simp [eqToHom_map]

@[simp]
lemma cutEquivalence_functor : cutEquivalence.functor = cut := (rfl)

@[simp]
lemma cutEquivalence_inverse : cutEquivalence.inverse = uncut := (rfl)

end AugmentedSimplexCategory
