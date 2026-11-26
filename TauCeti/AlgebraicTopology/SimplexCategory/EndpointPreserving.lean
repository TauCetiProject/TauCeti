/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Endpoint-preserving maps in the simplex category

This file defines three wide subcategories of `SimplexCategory`, all with the objects `⦋n⦌`:

* `TauCeti.SimplexCategory.BotPreserving` (often written `Δ_⊥`): the monotone maps sending the
  least vertex `0` to the least vertex;
* `TauCeti.SimplexCategory.TopPreserving` (often written `Δ_⊤`): the monotone maps sending the
  greatest vertex `Fin.last` to the greatest vertex;
* `TauCeti.SimplexCategory.EndpointPreserving` (often written `Δ_∂`): the monotone maps
  preserving both endpoints. It contains `⦋0⦌`, whose two endpoints coincide, and `⦋0⦌` is
  terminal in it.

They are the wide subcategories `WideSubcategory P` for the multiplicative morphism properties
`TauCeti.SimplexCategory.preservesBot`, `TauCeti.SimplexCategory.preservesTop` and
`TauCeti.SimplexCategory.preservesEndpoints`, so the identities, composition and the faithful
inclusion into `SimplexCategory` come from Mathlib's wide-subcategory API. Every degeneracy `σ i`
preserves both endpoints, while the face `δ i` preserves the least vertex exactly when `i ≠ 0`
and the greatest one exactly when `i ≠ Fin.last _`; the corresponding restricted faces and
degeneracies are `BotPreserving.δ`, `TopPreserving.δ`, `EndpointPreserving.δ` and the three `σ`.

These categories describe the hom-categories of the free adjunction: the hom-categories between
its two distinct objects are `Δ_⊤` and `Δ_⊥`, and `Δ_∂` is the opposite of the augmented simplex
category under the duality of finite ordinals sending an ordinal to its chain of cuts.

## References

* S. Schanuel, R. Street, *The free adjunction*, Cahiers de Topologie et Géométrie
  Différentielle Catégoriques 27 (1986), 81–83.
* E. Riehl, D. Verity, *Homotopy coherent adjunctions and the formal theory of monads*,
  Advances in Mathematics 286 (2016), §3.3.
-/

public section

open CategoryTheory Simplicial

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-- The morphisms of `SimplexCategory` sending the least vertex to the least vertex. -/
def preservesBot : MorphismProperty SimplexCategory :=
  fun _ _ f ↦ f.toOrderHom 0 = 0

/-- The morphisms of `SimplexCategory` sending the greatest vertex to the greatest vertex. -/
def preservesTop : MorphismProperty SimplexCategory :=
  fun x y f ↦ f.toOrderHom (Fin.last x.len) = Fin.last y.len

/-- The morphisms of `SimplexCategory` preserving both the least and the greatest vertex. -/
def preservesEndpoints : MorphismProperty SimplexCategory :=
  preservesBot ⊓ preservesTop

variable {x y : SimplexCategory}

lemma preservesBot_iff (f : x ⟶ y) : preservesBot f ↔ f.toOrderHom 0 = 0 := Iff.rfl

lemma preservesTop_iff (f : x ⟶ y) :
    preservesTop f ↔ f.toOrderHom (Fin.last x.len) = Fin.last y.len := Iff.rfl

lemma preservesEndpoints_iff (f : x ⟶ y) :
    preservesEndpoints f ↔ preservesBot f ∧ preservesTop f := Iff.rfl

instance : preservesBot.IsMultiplicative where
  id_mem _ := rfl
  comp_mem f g hf hg := by
    rw [preservesBot_iff] at hf hg ⊢
    simp [hf, hg]

instance : preservesTop.IsMultiplicative where
  id_mem _ := rfl
  comp_mem f g hf hg := by
    rw [preservesTop_iff] at hf hg ⊢
    simp [hf, hg]

instance : preservesEndpoints.IsMultiplicative :=
  inferInstanceAs (preservesBot ⊓ preservesTop).IsMultiplicative

/-! ### Faces and degeneracies -/

lemma toOrderHom_δ_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (δ i).toOrderHom j = i.succAbove j := rfl

lemma toOrderHom_σ_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (σ i).toOrderHom j = i.predAbove j := rfl

lemma preservesBot_σ {n : ℕ} (i : Fin (n + 1)) : preservesBot (σ i) := by
  simp [preservesBot_iff, toOrderHom_σ_apply]

lemma preservesTop_σ {n : ℕ} (i : Fin (n + 1)) : preservesTop (σ i) := by
  simp [preservesTop_iff, toOrderHom_σ_apply]

lemma preservesEndpoints_σ {n : ℕ} (i : Fin (n + 1)) : preservesEndpoints (σ i) :=
  ⟨preservesBot_σ i, preservesTop_σ i⟩

lemma preservesBot_δ_iff {n : ℕ} (i : Fin (n + 2)) : preservesBot (δ i) ↔ i ≠ 0 := by
  rw [preservesBot_iff, toOrderHom_δ_apply]
  constructor
  · rintro h rfl
    simp at h
  · intro h
    exact Fin.succAbove_ne_zero_zero h

lemma preservesTop_δ_iff {n : ℕ} (i : Fin (n + 2)) :
    preservesTop (δ i) ↔ i ≠ Fin.last _ := by
  rw [preservesTop_iff]
  simp only [toOrderHom_δ_apply, len_mk]
  constructor
  · rintro h rfl
    simp at h
  · intro h
    exact Fin.succAbove_ne_last_last h

lemma preservesEndpoints_δ_iff {n : ℕ} (i : Fin (n + 2)) :
    preservesEndpoints (δ i) ↔ i ≠ 0 ∧ i ≠ Fin.last _ := by
  rw [preservesEndpoints_iff, preservesBot_δ_iff, preservesTop_δ_iff]

/-! ### The three wide subcategories -/

/-- The wide subcategory `Δ_⊥` of `SimplexCategory` whose morphisms preserve the least vertex. -/
abbrev BotPreserving := WideSubcategory preservesBot

/-- The wide subcategory `Δ_⊤` of `SimplexCategory` whose morphisms preserve the greatest
vertex. -/
abbrev TopPreserving := WideSubcategory preservesTop

/-- The wide subcategory `Δ_∂` of `SimplexCategory` whose morphisms preserve both the least and
the greatest vertex. -/
abbrev EndpointPreserving := WideSubcategory preservesEndpoints

namespace BotPreserving

/-- The object `⦋n⦌` of `Δ_⊥`. -/
abbrev mk (n : ℕ) : BotPreserving := ⟨⦋n⦌⟩

/-- The morphism of `Δ_⊥` given by a monotone map preserving `0`. -/
abbrev homMk {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (h : f.toOrderHom 0 = 0) : mk n ⟶ mk m :=
  ⟨f, (preservesBot_iff f).2 h⟩

variable {X Y : BotPreserving}

@[simp]
lemma hom_toOrderHom_zero (f : X ⟶ Y) : f.hom.toOrderHom 0 = 0 := f.property

lemma hom_ext' {f g : X ⟶ Y} (h : f.hom.toOrderHom = g.hom.toOrderHom) : f = g :=
  WideSubcategory.hom_ext _ (Hom.ext _ _ h)

/-- The face `δ i.succ : ⦋n⦌ ⟶ ⦋n + 1⦌`, which omits a vertex other than `0`, as a morphism of
`Δ_⊥`. -/
def δ {n : ℕ} (i : Fin (n + 1)) : mk n ⟶ mk (n + 1) :=
  ⟨SimplexCategory.δ i.succ, (preservesBot_δ_iff _).2 i.succ_ne_zero⟩

@[simp]
lemma δ_hom {n : ℕ} (i : Fin (n + 1)) : (δ i).hom = SimplexCategory.δ i.succ := (rfl)

/-- The degeneracy `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` as a morphism of `Δ_⊥`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : mk (n + 1) ⟶ mk n :=
  ⟨SimplexCategory.σ i, preservesBot_σ i⟩

@[simp]
lemma σ_hom {n : ℕ} (i : Fin (n + 1)) : (σ i).hom = SimplexCategory.σ i := (rfl)

end BotPreserving

namespace TopPreserving

/-- The object `⦋n⦌` of `Δ_⊤`. -/
abbrev mk (n : ℕ) : TopPreserving := ⟨⦋n⦌⟩

/-- The morphism of `Δ_⊤` given by a monotone map preserving the greatest vertex. -/
abbrev homMk {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (h : f.toOrderHom (Fin.last n) = Fin.last m) :
    mk n ⟶ mk m := ⟨f, (preservesTop_iff f).2 h⟩

variable {X Y : TopPreserving}

@[simp]
lemma hom_toOrderHom_last (f : X ⟶ Y) :
    f.hom.toOrderHom (Fin.last X.obj.len) = Fin.last Y.obj.len := f.property

lemma hom_ext' {f g : X ⟶ Y} (h : f.hom.toOrderHom = g.hom.toOrderHom) : f = g :=
  WideSubcategory.hom_ext _ (Hom.ext _ _ h)

/-- The face `δ i.castSucc : ⦋n⦌ ⟶ ⦋n + 1⦌`, which omits a vertex other than the greatest one,
as a morphism of `Δ_⊤`. -/
def δ {n : ℕ} (i : Fin (n + 1)) : mk n ⟶ mk (n + 1) :=
  ⟨SimplexCategory.δ i.castSucc, (preservesTop_δ_iff _).2 i.castSucc_ne_last⟩

@[simp]
lemma δ_hom {n : ℕ} (i : Fin (n + 1)) : (δ i).hom = SimplexCategory.δ i.castSucc := (rfl)

/-- The degeneracy `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` as a morphism of `Δ_⊤`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : mk (n + 1) ⟶ mk n :=
  ⟨SimplexCategory.σ i, preservesTop_σ i⟩

@[simp]
lemma σ_hom {n : ℕ} (i : Fin (n + 1)) : (σ i).hom = SimplexCategory.σ i := (rfl)

end TopPreserving

namespace EndpointPreserving

/-- The object `⦋n⦌` of `Δ_∂`. -/
abbrev mk (n : ℕ) : EndpointPreserving := ⟨⦋n⦌⟩

/-- The morphism of `Δ_∂` given by a monotone map preserving both endpoints. -/
abbrev homMk {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (h₀ : f.toOrderHom 0 = 0)
    (h : f.toOrderHom (Fin.last n) = Fin.last m) : mk n ⟶ mk m :=
  ⟨f, (preservesEndpoints_iff f).2 ⟨(preservesBot_iff f).2 h₀, (preservesTop_iff f).2 h⟩⟩

variable {X Y : EndpointPreserving}

@[simp]
lemma hom_toOrderHom_zero (f : X ⟶ Y) : f.hom.toOrderHom 0 = 0 :=
  ((preservesEndpoints_iff _).1 f.property).1

@[simp]
lemma hom_toOrderHom_last (f : X ⟶ Y) :
    f.hom.toOrderHom (Fin.last X.obj.len) = Fin.last Y.obj.len :=
  ((preservesEndpoints_iff _).1 f.property).2

lemma hom_ext' {f g : X ⟶ Y} (h : f.hom.toOrderHom = g.hom.toOrderHom) : f = g :=
  WideSubcategory.hom_ext _ (Hom.ext _ _ h)

/-- The inner face `δ i.succ.castSucc : ⦋n + 1⦌ ⟶ ⦋n + 2⦌`, which omits a vertex other than the
two endpoints, as a morphism of `Δ_∂`. -/
def δ {n : ℕ} (i : Fin (n + 1)) : mk (n + 1) ⟶ mk (n + 2) :=
  ⟨SimplexCategory.δ i.succ.castSucc,
    (preservesEndpoints_δ_iff _).2
      ⟨Fin.castSucc_ne_zero_iff.2 i.succ_ne_zero, Fin.castSucc_ne_last _⟩⟩

@[simp]
lemma δ_hom {n : ℕ} (i : Fin (n + 1)) : (δ i).hom = SimplexCategory.δ i.succ.castSucc := (rfl)

/-- The degeneracy `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` as a morphism of `Δ_∂`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : mk (n + 1) ⟶ mk n :=
  ⟨SimplexCategory.σ i, preservesEndpoints_σ i⟩

@[simp]
lemma σ_hom {n : ℕ} (i : Fin (n + 1)) : (σ i).hom = SimplexCategory.σ i := (rfl)

/-- The unique morphism of `Δ_∂` to `⦋0⦌`, the constant map. -/
def toZero (X : EndpointPreserving) : X ⟶ mk 0 :=
  ⟨const _ _ 0, (preservesEndpoints_iff _).2 ⟨rfl, Subsingleton.elim (α := Fin 1) _ _⟩⟩

instance (X : EndpointPreserving) : Subsingleton (X ⟶ mk 0) where
  allEq _ _ := WideSubcategory.hom_ext _ (Subsingleton.elim _ _)

instance (X : EndpointPreserving) : Unique (X ⟶ mk 0) where
  default := toZero X
  uniq _ := Subsingleton.elim _ _

/-- `⦋0⦌` is a terminal object of `Δ_∂`. -/
def isTerminalZero : Limits.IsTerminal (mk 0) :=
  Limits.IsTerminal.ofUnique _

end EndpointPreserving

end TauCeti.SimplexCategory
