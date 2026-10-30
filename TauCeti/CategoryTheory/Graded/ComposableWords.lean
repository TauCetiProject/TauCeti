/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Stream.Defs
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.CategoryTheory.Graded.InducedQuiver
public import TauCeti.LinearAlgebra.Graded.Insertion
public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Composable words in the bar construction of a graded linear quiver

The reduced bar construction of the total module of morphisms of a graded linear quiver `C` is
spanned by words `z₀ ⋯ zₙ₋₁` of morphisms `zᵢ : aᵢ ⟶ bᵢ`.  Such a word is **composable** from `X`
to `Y` when the source of each morphism is the target of the next one, `aₙ₋₁ = X` and `b₀ = Y`;
this is the input order of the operations of an `A∞` category.  This file introduces the span
`TauCeti.GradedLinearQuiver.composableWords R X Y` of the composable words from `X` to `Y` and the
span `TauCeti.GradedLinearQuiver.nonComposableWords R C` of the words which are not composable.
Together they span the whole bar construction.

The Taylor maps of `A∞` categories and of `A∞` functors send composable words to morphisms between
the images of their endpoints, and other words to zero.  This is the word-level form
`TauCeti.GradedLinearQuiver.IsWordPathCompatible` of path compatibility of their components
(`TauCeti.GradedLinearQuiver.isWordPathCompatible_iff`).  Path compatibility propagates through
the two constructions out of which bar differentials and bar maps are built: the graded Taylor
expansion of a path-compatible endomorphism preserves both spans, and the coalgebra morphism with
path-compatible Taylor components along an injective map of objects sends each span to the
corresponding span.  Moreover, a relation between two Taylor maps which only holds on composable
words is inherited by their graded Taylor expansions and by the coalgebra morphisms they generate.
These statements are what is needed to compare `A∞` structures on categories induced along a
non-injective map of objects, where strings which are not composable can become composable after
applying the map.

## Main definitions

* `TauCeti.GradedLinearQuiver.composableWords`: the span of the composable words from `X` to `Y`.
* `TauCeti.GradedLinearQuiver.nonComposableWords`: the span of the words which are not composable.
* `TauCeti.GradedLinearQuiver.IsWordPathCompatible`: a map from words to morphisms sending
  composable words to morphisms between the images of their endpoints and other words to zero.

## Main results

* `TauCeti.GradedLinearQuiver.iSup_composableWords_sup_nonComposableWords`: composable and
  non-composable words span the bar construction, so linear maps agreeing on both are equal
  (`TauCeti.GradedLinearQuiver.linearMap_ext_composableWords`).
* `TauCeti.GradedLinearQuiver.isWordPathCompatible_iff`: word-level path compatibility is path
  compatibility of the restrictions to words of each positive length.
* `TauCeti.GradedLinearQuiver.IsWordPathCompatible.coalgHom_mem_composableWords` and
  `TauCeti.GradedLinearQuiver.IsWordPathCompatible.coalgHom_mem_nonComposableWords`: the coalgebra
  morphism with path-compatible Taylor components preserves composability.
* `TauCeti.GradedLinearQuiver.IsWordPathCompatible.gradedCoderiv_mem_composableWords` and
  `TauCeti.GradedLinearQuiver.IsWordPathCompatible.gradedCoderiv_mem_nonComposableWords`: so does
  the graded Taylor expansion of a path-compatible map.
* `TauCeti.GradedLinearQuiver.map_coalgHom_of_mem_composableWords` and
  `TauCeti.GradedLinearQuiver.map_gradedCoderiv_of_mem_composableWords`: relations between Taylor
  maps on composable words extend to their coalgebra morphisms and graded Taylor expansions.
* `TauCeti.GradedLinearQuiver.IsWordPathCompatible.eq_of_totalHomMap_eq`: path-compatible maps
  into a quiver induced along a map of objects are determined by their images on composable words.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), for the bar construction of an `A∞` category over its set of objects.
-/

public section

namespace TauCeti.GradedLinearQuiver

open ReducedTensorWords

universe u u' u'' v v' v'' w

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-! ### Composable and non-composable words -/

variable (R) in
/-- The span of the **composable words from `X` to `Y`**: the words `z₀ ⋯ zₙ₋₁` of morphisms
`zᵢ : aᵢ ⟶ bᵢ`, with `n` positive, in which the source of each morphism is the target of the next
one, the source of the last is `X` and the target of the first is `Y`. -/
noncomputable def composableWords (X Y : C) : Submodule R (ReducedTensorWords R (TotalHom R C)) :=
  Submodule.span R {w | ∃ (n : ℕ) (hn : 0 < n) (a b : ℕ → C) (z : ℕ → TotalHom R C),
    (∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) ∧
      IsComposableString a b n ∧ a (n - 1) = X ∧ b 0 = Y ∧
        w = of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i)}

variable (R C) in
/-- The span of the **non-composable words**: the words `z₀ ⋯ zₙ₋₁` of morphisms `zᵢ : aᵢ ⟶ bᵢ`,
with `n` positive, in which the source of some morphism is not the target of the next one. -/
noncomputable def nonComposableWords : Submodule R (ReducedTensorWords R (TotalHom R C)) :=
  Submodule.span R {w | ∃ (n : ℕ) (hn : 0 < n) (a b : ℕ → C) (z : ℕ → TotalHom R C),
    (∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) ∧
      ¬ IsComposableString a b n ∧
        w = of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i)}

/-- A word of morphisms along a composable string is a composable word from the source of its last
morphism to the target of its first. -/
theorem of_tprod_mem_composableWords {n : ℕ} (hn : 0 < n) {a b : ℕ → C}
    {z : ℕ → TotalHom R C} (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : IsComposableString a b n) :
    of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i) ∈
      composableWords R (a (n - 1)) (b 0) :=
  Submodule.subset_span ⟨n, hn, a, b, z, hz, hab, rfl, rfl, rfl⟩

/-- A word of morphisms along a string which is not composable is a non-composable word. -/
theorem of_tprod_mem_nonComposableWords {n : ℕ} (hn : 0 < n) {a b : ℕ → C}
    {z : ℕ → TotalHom R C} (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : ¬ IsComposableString a b n) :
    of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i) ∈ nonComposableWords R C :=
  Submodule.subset_span ⟨n, hn, a, b, z, hz, hab, rfl⟩

/-- **Induction on composable words**: a property of words closed under sums and scalar multiples
and holding on the words along composable strings from `X` to `Y` holds on all composable words
from `X` to `Y`. -/
@[elab_as_elim]
theorem composableWords_induction {X Y : C} {P : ReducedTensorWords R (TotalHom R C) → Prop}
    (word : ∀ (n : ℕ) (hn : 0 < n) (a b : ℕ → C) (z : ℕ → TotalHom R C),
      (∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) →
        IsComposableString a b n → a (n - 1) = X → b 0 = Y →
          P (of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i)))
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y)) (smul : ∀ (r : R) x, P x → P (r • x))
    {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ composableWords R X Y) : P w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, ha, hb, rfl⟩ := hw
    exact word n hn a b z hz hab ha hb
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul r x _ hx => exact smul r x hx

/-- **Induction on non-composable words**: a property of words closed under sums and scalar
multiples and holding on the words along strings which are not composable holds on all
non-composable words. -/
@[elab_as_elim]
theorem nonComposableWords_induction {P : ReducedTensorWords R (TotalHom R C) → Prop}
    (word : ∀ (n : ℕ) (hn : 0 < n) (a b : ℕ → C) (z : ℕ → TotalHom R C),
      (∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) →
        ¬ IsComposableString a b n →
          P (of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ z i)))
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y)) (smul : ∀ (r : R) x, P x → P (r • x))
    {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ nonComposableWords R C) : P w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl⟩ := hw
    exact word n hn a b z hz hab
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul r x _ hx => exact smul r x hx

/-- A word of morphisms, each in a single hom module, is composable or non-composable. -/
private theorem of_tprod_homInclusion_mem_sup {n : ℕ} (hn : 0 < n) (p : Fin n → C × C)
    (x : ∀ i, homModule (R := R) (p i).1 (p i).2) :
    of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i ↦ homInclusion (p i).1 (p i).2 (x i)) ∈
      (⨆ X : C, ⨆ Y : C, composableWords R X Y) ⊔ nonComposableWords R C := by
  -- Read the string as a natural-indexed string, clamping the indices to the string itself.
  let j : ℕ → Fin n := fun i ↦ ⟨min i (n - 1), by omega⟩
  have hj (i : Fin n) : j i = i := Fin.ext (min_eq_left (by have := i.isLt; omega))
  let a : ℕ → C := fun i ↦ (p (j i)).1
  let b : ℕ → C := fun i ↦ (p (j i)).2
  let z : ℕ → TotalHom R C := fun i ↦ homInclusion (a i) (b i) (x (j i))
  have hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)) :=
    fun i _ ↦ LinearMap.mem_range_self _ _
  have hxz : (fun i : Fin n ↦ homInclusion (p i).1 (p i).2 (x i)) = fun i : Fin n ↦ z i :=
    funext fun i ↦
      (congrArg (fun k : Fin n ↦ homInclusion (R := R) (p k).1 (p k).2 (x k)) (hj i)).symm
  rw [hxz]
  by_cases hab : IsComposableString a b n
  · exact Submodule.mem_sup_left <| Submodule.mem_iSup_of_mem (a (n - 1)) <|
      Submodule.mem_iSup_of_mem (b 0) (of_tprod_mem_composableWords hn hz hab)
  · exact Submodule.mem_sup_right (of_tprod_mem_nonComposableWords hn hz hab)

/-- A pure word of morphisms is a sum of composable and non-composable words. -/
private theorem of_tprod_mem_sup {n : ℕ} (hn : 0 < n) (y : Fin n → TotalHom R C) :
    of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R y) ∈
      (⨆ X : C, ⨆ Y : C, composableWords R X Y) ⊔ nonComposableWords R C := by
  classical
  have e : y = fun i ↦ ∑ q ∈ (y i).support, homInclusion q.1 q.2 (homProjection q.1 q.2 (y i)) :=
    funext fun i ↦ by
      simp only [homProjection_apply, homInclusion_eq_lof, DirectSum.lof_eq_of,
        DirectSum.sum_support_of]
  rw [e, MultilinearMap.map_sum_finset, map_sum]
  exact Submodule.sum_mem _ fun p _ ↦ of_tprod_homInclusion_mem_sup hn p _

/-- **Composable and non-composable words span the bar construction.** -/
theorem iSup_composableWords_sup_nonComposableWords :
    (⨆ X : C, ⨆ Y : C, composableWords R X Y) ⊔ nonComposableWords R C = ⊤ := by
  rw [eq_top_iff, ← iSup_range_of R (TotalHom R C)]
  refine iSup_le fun n ↦ ?_
  rintro _ ⟨y, rfl⟩
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x => rw [map_smul]; exact Submodule.smul_mem _ r (of_tprod_mem_sup n.2 x)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- Two linear maps out of the bar construction which agree on composable and on non-composable
words are equal. -/
theorem linearMap_ext_composableWords {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : ReducedTensorWords R (TotalHom R C) →ₗ[R] M}
    (hc : ∀ X Y : C, ∀ w ∈ composableWords R X Y, f w = g w)
    (hn : ∀ w ∈ nonComposableWords R C, f w = g w) : f = g := by
  refine LinearMap.ext fun w ↦ ?_
  have hle : (⨆ X : C, ⨆ Y : C, composableWords R X Y) ⊔ nonComposableWords R C ≤
      LinearMap.eqLocus f g :=
    sup_le (iSup_le fun X ↦ iSup_le fun Y w hw ↦ hc X Y w hw) fun w hw ↦ hn w hw
  rw [iSup_composableWords_sup_nonComposableWords] at hle
  exact hle Submodule.mem_top

/-! ### Building composable words -/

/-- A single morphism `X ⟶ Y` is a composable word from `X` to `Y`. -/
theorem ofLetter_mem_composableWords {X Y : C} {u : TotalHom R C}
    (hu : u ∈ LinearMap.range (homInclusion (R := R) X Y)) :
    ofLetter R _ u ∈ composableWords R X Y := by
  rw [ofLetter_eq_of_tprod]
  exact of_tprod_mem_composableWords (n := 1) (a := fun _ ↦ X) (b := fun _ ↦ Y)
    (z := fun _ ↦ u) Nat.one_pos (fun _ _ ↦ hu) ⟨fun i hi ↦ absurd hi (by omega)⟩

/-- A composable block of a word of morphisms is a composable word from the source of its last
morphism to the target of its first. -/
theorem subword_mem_composableWords {n : ℕ} {a b : ℕ → C} {z : ℕ → TotalHom R C}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) {p s : ℕ}
    (hab : IsComposableString (fun j ↦ a (p + j)) (fun j ↦ b (p + j)) s) (hs : 0 < s)
    (hps : p + s ≤ n) :
    subword R (fun i : Fin n ↦ z i) p s ∈ composableWords R (a (p + s - 1)) (b p) := by
  rw [subword_eq_of_tprod R _ hs hps]
  have h := of_tprod_mem_composableWords hs (a := fun j ↦ a (p + j)) (b := fun j ↦ b (p + j))
    (z := fun j ↦ z (p + j)) (fun i hi ↦ hz (p + i) (by omega)) hab
  rwa [show p + (s - 1) = p + s - 1 by omega, add_zero] at h

/-- A block of a word of morphisms which is not composable is a non-composable word. -/
theorem subword_mem_nonComposableWords {n : ℕ} {a b : ℕ → C} {z : ℕ → TotalHom R C}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) {p s : ℕ}
    (hab : ¬ IsComposableString (fun j ↦ a (p + j)) (fun j ↦ b (p + j)) s) (hps : p + s ≤ n) :
    subword R (fun i : Fin n ↦ z i) p s ∈ nonComposableWords R C := by
  have hs : 0 < s := Nat.pos_of_ne_zero fun h ↦ hab ⟨fun i hi ↦ absurd hi (by omega)⟩
  rw [subword_eq_of_tprod R _ hs hps]
  exact of_tprod_mem_nonComposableWords hs (a := fun j ↦ a (p + j)) (b := fun j ↦ b (p + j))
    (z := fun j ↦ z (p + j)) (fun i hi ↦ hz (p + i) (by omega)) hab

/-- Every block of a word along a composable string is a composable word between some objects. -/
theorem exists_subword_mem_composableWords {n : ℕ} {a b : ℕ → C} {z : ℕ → TotalHom R C}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : IsComposableString a b n) (p s : ℕ) :
    ∃ X Y : C, subword R (fun i : Fin n ↦ z i) p s ∈ composableWords R X Y := by
  by_cases h : 0 < s ∧ p + s ≤ n
  · exact ⟨_, _, subword_mem_composableWords hz (hab.block h.2) h.1 h.2⟩
  · have h0 : subword R (fun i : Fin n ↦ z i) p s = 0 := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · exact subword_length_zero R _ p
      · exact subword_eq_zero_of_lt_add R _ (by omega)
    exact ⟨a 0, b 0, h0 ▸ zero_mem _⟩

/-- Replacing a block of a string of morphisms `aᵢ ⟶ bᵢ` by a morphism from the source of the last
morphism of the block to the target of its first gives a string of morphisms between the replaced
objects. -/
theorem replaceBlock_mem_range_homInclusion {n p d : ℕ} {a b : ℕ → C} {y : ℕ → TotalHom R C}
    (hy : ∀ i < n, y i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) {e : TotalHom R C}
    (he : e ∈ LinearMap.range (homInclusion (R := R) (a (p + d - 1)) (b p))) (hpd : p + d ≤ n) :
    ∀ i < p + 1 + (n - p - d), replaceBlock y p d e i ∈ LinearMap.range
      (homInclusion (R := R) (replaceBlock a p d (a (p + d - 1)) i)
        (replaceBlock b p d (b p) i)) := by
  intro i hi
  rcases lt_trichotomy i p with h | rfl | h
  · rw [replaceBlock_of_lt _ _ _ _ h, replaceBlock_of_lt _ _ _ _ h, replaceBlock_of_lt _ _ _ _ h]
    exact hy i (by omega)
  · rwa [replaceBlock_self, replaceBlock_self, replaceBlock_self]
  · rw [replaceBlock_of_gt _ _ _ _ h, replaceBlock_of_gt _ _ _ _ h, replaceBlock_of_gt _ _ _ _ h]
    exact hy (i + d - 1) (by omega)

/-- The morphisms of a string with a morphism prepended lie in the expected hom modules. -/
private theorem cons_mem {n : ℕ} {a b : ℕ → C} {z : ℕ → TotalHom R C}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) {Y Z : C}
    {u : TotalHom R C} (hu : u ∈ LinearMap.range (homInclusion (R := R) Y Z)) :
    ∀ i < n + 1, Stream'.cons u z i ∈
      LinearMap.range (homInclusion (R := R) (Stream'.cons Y a i) (Stream'.cons Z b i)) := by
  rintro (_ | i) hi
  · exact hu
  · exact hz i (by omega)

/-- If a string is not composable, neither is the string with a morphism prepended. -/
private theorem not_isComposableString_cons {n : ℕ} {a b : ℕ → C}
    (hab : ¬ IsComposableString a b n) (Y Z : C) :
    ¬ IsComposableString (Stream'.cons Y a) (Stream'.cons Z b) (n + 1) := fun h ↦
  hab ⟨fun i hi ↦ h.eq (i + 1) (by omega)⟩

/-- Prepending a morphism `Y ⟶ Z` to a composable word from `X` to `Y` gives a composable word from
`X` to `Z`. -/
theorem prepend_mem_composableWords {X Y Z : C} {u : TotalHom R C}
    (hu : u ∈ LinearMap.range (homInclusion (R := R) Y Z)) {w : ReducedTensorWords R (TotalHom R C)}
    (hw : w ∈ composableWords R X Y) : prepend R _ u w ∈ composableWords R X Z := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl, rfl, rfl⟩ := hw
    rw [prepend_of_tprod_cons]
    have h := of_tprod_mem_composableWords (n := n + 1) (by omega) (cons_mem hz hu)
      (a := Stream'.cons (b 0) a) (b := Stream'.cons Z b) ⟨fun i hi ↦ by
        rcases i with _ | i
        · rfl
        · exact hab.eq i (by omega)⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    exact h
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-- Prepending a morphism to a non-composable word gives a non-composable word. -/
theorem prepend_mem_nonComposableWords {Y Z : C} {u : TotalHom R C}
    (hu : u ∈ LinearMap.range (homInclusion (R := R) Y Z)) {w : ReducedTensorWords R (TotalHom R C)}
    (hw : w ∈ nonComposableWords R C) : prepend R _ u w ∈ nonComposableWords R C := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl⟩ := hw
    rw [prepend_of_tprod_cons]
    exact of_tprod_mem_nonComposableWords _ (cons_mem hz hu)
      (not_isComposableString_cons hab Y Z)
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-- Prepending a morphism `Y ⟶ Z` to a composable word from `X` to `Y'`, where `Y' ≠ Y`, gives a
non-composable word. -/
theorem prepend_mem_nonComposableWords_of_ne {X Y Y' Z : C} {u : TotalHom R C}
    (hu : u ∈ LinearMap.range (homInclusion (R := R) Y Z)) {w : ReducedTensorWords R (TotalHom R C)}
    (hw : w ∈ composableWords R X Y') (hne : Y' ≠ Y) :
    prepend R _ u w ∈ nonComposableWords R C := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl, rfl, rfl⟩ := hw
    rw [prepend_of_tprod_cons]
    exact of_tprod_mem_nonComposableWords _ (cons_mem hz hu)
      fun h ↦ hne (h.eq 0 (by omega))
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-- A linear map of total modules sending morphisms `X ⟶ Y` to morphisms `φ X ⟶ φ Y`, applied to
every letter, sends composable words from `X` to `Y` to composable words from `φ X` to `φ Y`. -/
theorem map_mem_composableWords {D : Type u'} [GradedLinearQuiver.{u', v', w} R D] {φ : C → D}
    {Θ : TotalHom R C →ₗ[R] TotalHom R D}
    (hΘ : ∀ (X Y : C) (f : homModule (R := R) X Y),
      Θ (homInclusion X Y f) ∈ LinearMap.range (homInclusion (R := R) (φ X) (φ Y)))
    {X Y : C} {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ composableWords R X Y) :
    ReducedTensorWords.map (R := R) Θ w ∈ composableWords R (φ X) (φ Y) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl, rfl, rfl⟩ := hw
    rw [map_of_tprod]
    refine of_tprod_mem_composableWords (R := R) (C := D) hn (a := fun i ↦ φ (a i))
      (b := fun i ↦ φ (b i)) (z := fun i ↦ Θ (z i)) (fun i hi ↦ ?_)
      ⟨fun i hi ↦ congrArg φ (hab.eq i hi)⟩
    obtain ⟨f, hf⟩ := hz i hi
    exact hf ▸ hΘ _ _ f
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-- A linear map of total modules sending morphisms `X ⟶ Y` to morphisms `φ X ⟶ φ Y`, along an
injective map of objects `φ` and applied to every letter, sends non-composable words to
non-composable words. -/
theorem map_mem_nonComposableWords {D : Type u'} [GradedLinearQuiver.{u', v', w} R D] {φ : C → D}
    {Θ : TotalHom R C →ₗ[R] TotalHom R D}
    (hΘ : ∀ (X Y : C) (f : homModule (R := R) X Y),
      Θ (homInclusion X Y f) ∈ LinearMap.range (homInclusion (R := R) (φ X) (φ Y)))
    (hφ : Function.Injective φ) {w : ReducedTensorWords R (TotalHom R C)}
    (hw : w ∈ nonComposableWords R C) :
    ReducedTensorWords.map (R := R) Θ w ∈ nonComposableWords R D := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl⟩ := hw
    rw [map_of_tprod]
    refine of_tprod_mem_nonComposableWords (R := R) (C := D) hn (a := fun i ↦ φ (a i))
      (b := fun i ↦ φ (b i)) (z := fun i ↦ Θ (z i)) (fun i hi ↦ ?_)
      fun h ↦ hab ⟨fun i hi ↦ hφ (h.eq i hi)⟩
    obtain ⟨f, hf⟩ := hz i hi
    exact hf ▸ hΘ _ _ f
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-! ### Word-level path compatibility -/

/-- A linear map `t` from the bar construction of `C` to the total module of morphisms of `D` is
**path-compatible on words** along a map of objects `φ : C → D` when it sends composable words from
`X` to `Y` to morphisms `φ X ⟶ φ Y` and non-composable words to zero.  The Taylor maps of `A∞`
categories (along the identity) and of `A∞` functors (along their object maps) are of this kind;
see `TauCeti.GradedLinearQuiver.isWordPathCompatible_iff` for the comparison with path
compatibility of their components. -/
structure IsWordPathCompatible {D : Type u'} [GradedLinearQuiver.{u', v', w} R D] (φ : C → D)
    (t : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R D) : Prop where
  /-- A composable word from `X` to `Y` is sent to a morphism `φ X ⟶ φ Y`. -/
  mem_range_of_mem_composableWords {X Y : C} {w : ReducedTensorWords R (TotalHom R C)} :
    w ∈ composableWords R X Y → t w ∈ LinearMap.range (homInclusion (R := R) (φ X) (φ Y))
  /-- A non-composable word is sent to zero. -/
  eq_zero_of_mem_nonComposableWords {w : ReducedTensorWords R (TotalHom R C)} :
    w ∈ nonComposableWords R C → t w = 0

/-- **Word-level path compatibility is path compatibility on words of each length.** A linear map
from the bar construction is path-compatible on words exactly when its restriction to words of
every positive length `n`, as a multilinear map of `n` morphisms, is path-compatible. -/
theorem isWordPathCompatible_iff {D : Type u'} [GradedLinearQuiver.{u', v', w} R D] {φ : C → D}
    {t : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R D} :
    IsWordPathCompatible φ t ↔ ∀ (n : ℕ) (hn : 0 < n),
      IsPathCompatible φ ((t ∘ₗ of R _ ⟨n, hn⟩).compMultilinearMap
        (PiTensorProduct.tprod R (s := fun _ : Fin n ↦ TotalHom R C))) := by
  constructor
  · intro ht n hn
    -- Clamp natural indices to the string, to read strings of `Fin n` as natural-indexed strings.
    let j : ℕ → Fin n := fun i ↦ ⟨min i (n - 1), by omega⟩
    have hj (i : Fin n) : j i = i := Fin.ext (min_eq_left (by have := i.isLt; omega))
    constructor
    · intro X x
      let a : ℕ → C := fun i ↦ X (j i).rev.castSucc
      let b : ℕ → C := fun i ↦ X (j i).rev.succ
      have hw := of_tprod_mem_composableWords hn (a := a) (b := b)
        (z := fun i ↦ homInclusion (a i) (b i) (x (j i))) (fun i _ ↦ LinearMap.mem_range_self _ _)
        ⟨fun i hi ↦ congrArg X (Fin.ext (by simp [j, Fin.val_rev]; omega))⟩
      have ha : a (n - 1) = X 0 := congrArg X (Fin.ext (by simp [j, Fin.val_rev]; omega))
      have hb : b 0 = X (Fin.last n) := congrArg X (Fin.ext (by simp [j, Fin.val_rev]; omega))
      have h := ht.mem_range_of_mem_composableWords hw
      rw [ha, hb] at h
      have hx : (fun i : Fin n ↦ homInclusion (a i) (b i) (x (j i))) =
          fun i ↦ homInclusion _ _ (x i) := funext fun i ↦
        congrArg (fun k : Fin n ↦ homInclusion (R := R) (X k.rev.castSucc) (X k.rev.succ) (x k))
          (hj i)
      simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hx] using h
    · intro s t' x i i' hii' hne
      let a : ℕ → C := fun k ↦ s (j k)
      let b : ℕ → C := fun k ↦ t' (j k)
      have hw := of_tprod_mem_nonComposableWords hn (a := a) (b := b)
        (z := fun k ↦ homInclusion (a k) (b k) (x (j k))) (fun k _ ↦ LinearMap.mem_range_self _ _)
        fun hc ↦ hne <| by
          have e := hc.eq i (by omega)
          simp only [a, b] at e
          rwa [show j (i + 1) = i' from Fin.ext (by simp [j, hii']; omega), hj] at e
      have hx : (fun k : Fin n ↦ homInclusion (a k) (b k) (x (j k))) =
          fun k ↦ homInclusion _ _ (x k) := funext fun k ↦
        congrArg (fun k' : Fin n ↦ homInclusion (R := R) (s k') (t' k') (x k')) (hj k)
      simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hx] using
        ht.eq_zero_of_mem_nonComposableWords hw
  · intro h
    constructor
    · intro X Y w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨n, hn, a, b, z, hz, hab, rfl, rfl, rfl⟩ := hw
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
        choose g hg using fun i : Fin (m + 1) ↦ hz i i.isLt
        have e := (h (m + 1) hn).mem_range_homInclusion_of_chain (fun i ↦ a i) (fun i ↦ b i) g
          (fun k ↦ by simpa using hab.eq k (by have := k.isLt; omega)) (a := a m) (b := b 0)
          (by simp) (by simp)
        simpa [hg] using e
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | smul r x _ hx => simpa using Submodule.smul_mem _ r hx
    · intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨n, hn, a, b, z, hz, hab, rfl⟩ := hw
        choose g hg using fun i : Fin n ↦ hz i i.isLt
        obtain ⟨i, hi, hne⟩ : ∃ i, ∃ _ : i + 1 < n, b (i + 1) ≠ a i := by
          by_contra! hc
          exact hab ⟨hc⟩
        have e := (h n hn).eq_zero_of_ne (fun k ↦ a k) (fun k ↦ b k) g ⟨i, by omega⟩ ⟨i + 1, hi⟩
          rfl hne
        simpa [hg] using e
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul r x _ hx => simp [hx]

/-- Precomposing a path-compatible map with a letterwise map of total modules along an injective
map of objects gives a path-compatible map. -/
theorem IsWordPathCompatible.comp_map {D : Type u'} [GradedLinearQuiver.{u', v', w} R D]
    {E : Type u''} [GradedLinearQuiver.{u'', v'', w} R E] {φ : C → D} {ψ : D → E}
    {t : ReducedTensorWords R (TotalHom R D) →ₗ[R] TotalHom R E} (ht : IsWordPathCompatible ψ t)
    {Θ : TotalHom R C →ₗ[R] TotalHom R D}
    (hΘ : ∀ (X Y : C) (f : homModule (R := R) X Y),
      Θ (homInclusion X Y f) ∈ LinearMap.range (homInclusion (R := R) (φ X) (φ Y)))
    (hφ : Function.Injective φ) :
    IsWordPathCompatible (ψ ∘ φ) (t ∘ₗ ReducedTensorWords.map (R := R) Θ) where
  mem_range_of_mem_composableWords hw :=
    ht.mem_range_of_mem_composableWords (map_mem_composableWords hΘ hw)
  eq_zero_of_mem_nonComposableWords hw :=
    ht.eq_zero_of_mem_nonComposableWords (map_mem_nonComposableWords hΘ hφ hw)

/-- **Path-compatible maps into an induced quiver are determined by their images.** Two maps from
words to the morphisms of the quiver induced along `G`, path-compatible along the same map of
objects, are equal as soon as their images under the map of total modules agree on composable
words: on a composable word both values lie in a single hom module, on which the map of total
modules is injective. -/
theorem IsWordPathCompatible.eq_of_totalHomMap_eq {D : Type u'}
    [GradedLinearQuiver.{u', v', w} R D] {B : Type u''} {G : B → D}
    {κ : C → InducedQuiver D G}
    {t₁ t₂ : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R (InducedQuiver D G)}
    (h₁ : IsWordPathCompatible κ t₁) (h₂ : IsWordPathCompatible κ t₂)
    (h : ∀ X Y : C, ∀ w ∈ composableWords R X Y,
      InducedQuiver.totalHomMap R G (t₁ w) = InducedQuiver.totalHomMap R G (t₂ w)) :
    t₁ = t₂ := by
  refine linearMap_ext_composableWords (fun X Y w hw ↦ ?_) (fun w hw ↦ ?_)
  · obtain ⟨f₁, hf₁⟩ := h₁.mem_range_of_mem_composableWords hw
    obtain ⟨f₂, hf₂⟩ := h₂.mem_range_of_mem_composableWords hw
    have e := h X Y w hw
    rw [← hf₁, ← hf₂, InducedQuiver.totalHomMap_homInclusion,
      InducedQuiver.totalHomMap_homInclusion] at e
    rw [← hf₁, ← hf₂, homInclusion_injective _ _ e]
  · rw [h₁.eq_zero_of_mem_nonComposableWords hw, h₂.eq_zero_of_mem_nonComposableWords hw]

/-- The letter of a word is path-compatible on words: a single morphism `X ⟶ Y` is a composable
word from `X` to `Y`, and every non-composable word has length at least two. -/
theorem isWordPathCompatible_letter : IsWordPathCompatible id (letter R (TotalHom R C)) where
  mem_range_of_mem_composableWords {X Y} {w} hw := by
    refine composableWords_induction (fun n hn a b z hz hab ha hb ↦ ?_) (by simp)
      (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
      (fun r x hx ↦ by rw [map_smul]; exact Submodule.smul_mem _ r hx) hw
    rw [letter_of_tprod R _ hn z]
    split_ifs with h
    · subst h ha hb
      exact hz 0 Nat.one_pos
    · exact zero_mem _
  eq_zero_of_mem_nonComposableWords {w} hw := by
    refine nonComposableWords_induction (fun n hn a b z hz hab ↦ ?_) (by simp)
      (fun x y hx hy ↦ by rw [map_add, hx, hy, add_zero])
      (fun r x hx ↦ by rw [map_smul, hx, smul_zero]) hw
    have hn1 : n ≠ 1 := by
      rintro rfl
      exact hab ⟨fun i hi ↦ absurd hi (by omega)⟩
    rw [letter_of_tprod R _ hn z, ite_eq_right hn1]

/-! ### The coalgebra morphism of path-compatible Taylor components -/

section CoalgHom

variable {D : Type u'} [GradedLinearQuiver.{u', v', w} R D] {φ : C → D}
  {t : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R D}

/-- On the blocks of a word along a composable string, the coalgebra morphism with path-compatible
Taylor components produces composable words between the images of the endpoints of the block. -/
private theorem IsWordPathCompatible.coalgHom_subword_mem (ht : IsWordPathCompatible φ t)
    {n : ℕ} {a b : ℕ → C} {z : ℕ → TotalHom R C}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : IsComposableString a b n) (s : ℕ) :
    ∀ p, 0 < s → p + s ≤ n → coalgHom R t (subword R (fun i : Fin n ↦ z i) p s) ∈
      composableWords R (φ (a (p + s - 1))) (φ (b p)) := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro p hs hps
    rw [coalgHom_subword]
    refine add_mem (ofLetter_mem_composableWords (ht.mem_range_of_mem_composableWords
      (subword_mem_composableWords hz (hab.block hps) hs hps))) (Submodule.sum_mem _ fun d hd ↦ ?_)
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd₀
    · simp
    · have hjoin : b (p + d) = a (p + d - 1) := by
        simpa [show p + d - 1 + 1 = p + d by omega] using hab.eq (p + d - 1) (by omega)
      have hrest := ih (s - d) (by omega) (p + d) (by omega) (by omega)
      rw [show p + d + (s - d) - 1 = p + s - 1 by omega, hjoin] at hrest
      exact prepend_mem_composableWords (ht.mem_range_of_mem_composableWords
        (subword_mem_composableWords hz (hab.block (by omega)) hd₀ (by omega))) hrest

/-- **The coalgebra morphism with path-compatible Taylor components preserves composable words.**
It sends composable words from `X` to `Y` to composable words from `φ X` to `φ Y`. -/
theorem IsWordPathCompatible.coalgHom_mem_composableWords (ht : IsWordPathCompatible φ t)
    {X Y : C} {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ composableWords R X Y) :
    coalgHom R t w ∈ composableWords R (φ X) (φ Y) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl, rfl, rfl⟩ := hw
    rw [of_tprod_eq_subword R hn]
    simpa using ht.coalgHom_subword_mem hz hab n 0 hn (by omega)
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-- If a block of a string is not composable but is the concatenation of two composable blocks,
then the two blocks do not meet. -/
private theorem ne_of_not_isComposableString_block {a b : ℕ → C} {p s d : ℕ} (hds : d < s)
    (h : ¬ IsComposableString (fun j ↦ a (p + j)) (fun j ↦ b (p + j)) s)
    (h₁ : IsComposableString (fun j ↦ a (p + j)) (fun j ↦ b (p + j)) d)
    (h₂ : IsComposableString (fun j ↦ a (p + d + j)) (fun j ↦ b (p + d + j)) (s - d)) :
    b (p + d) ≠ a (p + d - 1) := fun e ↦ h ⟨fun i hi ↦ by
  rcases lt_trichotomy (i + 1) d with hlt | heq | hgt
  · exact h₁.eq i hlt
  · simpa [show p + (i + 1) = p + d by omega, show p + i = p + d - 1 by omega] using e
  · simpa [show p + (i + 1) = p + d + (i - d + 1) by omega, show p + i = p + d + (i - d) by omega]
      using h₂.eq (i - d) (by omega)⟩

/-- On the blocks of a word along a string which are not composable, the coalgebra morphism with
path-compatible Taylor components along an injective map of objects produces non-composable
words. -/
private theorem IsWordPathCompatible.coalgHom_subword_mem_nonComposableWords
    (ht : IsWordPathCompatible φ t) (hφ : Function.Injective φ) {n : ℕ} {a b : ℕ → C}
    {z : ℕ → TotalHom R C}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) (s : ℕ) :
    ∀ p, p + s ≤ n → ¬ IsComposableString (fun j ↦ a (p + j)) (fun j ↦ b (p + j)) s →
      coalgHom R t (subword R (fun i : Fin n ↦ z i) p s) ∈ nonComposableWords R D := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro p hps hns
    have hs : 0 < s := Nat.pos_of_ne_zero fun h ↦ hns ⟨fun i hi ↦ absurd hi (by omega)⟩
    -- A block of the string is the word along the shifted string.
    have hshift (q r : ℕ) (hqr : q + r ≤ n) :
        subword R (fun i : Fin n ↦ z i) q r = subword R (fun i : Fin r ↦ z (q + i)) 0 r :=
      subword_congr R _ _ hqr (by omega) fun j _ ↦ by simp
    have hzq (q r : ℕ) (hqr : q + r ≤ n) :
        ∀ i < r, z (q + i) ∈ LinearMap.range (homInclusion (R := R) (a (q + i)) (b (q + i))) :=
      fun i hi ↦ hz _ (by omega)
    rw [coalgHom_subword]
    have hletter : t (subword R (fun i : Fin n ↦ z i) p s) = 0 := by
      rw [hshift p s hps, ← of_tprod_eq_subword R hs]
      exact ht.eq_zero_of_mem_nonComposableWords
        (of_tprod_mem_nonComposableWords hs (hzq p s hps) hns)
    rw [hletter, map_zero, zero_add]
    refine Submodule.sum_mem _ fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd₀
    · simp
    rw [hshift p d (by omega), ← of_tprod_eq_subword R hd₀]
    by_cases h₁ : IsComposableString (fun j ↦ a (p + j)) (fun j ↦ b (p + j)) d
    · have hu := ht.mem_range_of_mem_composableWords
        (of_tprod_mem_composableWords hd₀ (hzq p d (by omega)) h₁)
      by_cases h₂ : IsComposableString (fun j ↦ a (p + d + j)) (fun j ↦ b (p + d + j)) (s - d)
      · -- Both blocks are composable, so they do not meet: the image of the first block does not
        -- compose with the image of the second.
        have hrest := ht.coalgHom_mem_composableWords
          (of_tprod_mem_composableWords (by omega : 0 < s - d) (hzq (p + d) (s - d) (by omega)) h₂)
        rw [of_tprod_eq_subword, ← hshift (p + d) (s - d) (by omega)] at hrest
        refine prepend_mem_nonComposableWords_of_ne hu hrest fun e ↦
          ne_of_not_isComposableString_block hd hns h₁ h₂ (hφ ?_)
        simpa [show p + (d - 1) = p + d - 1 by omega] using e
      · exact prepend_mem_nonComposableWords hu (ih (s - d) (by omega) (p + d) (by omega) h₂)
    · rw [ht.eq_zero_of_mem_nonComposableWords
        (of_tprod_mem_nonComposableWords hd₀ (hzq p d (by omega)) h₁)]
      simp

/-- **The coalgebra morphism with path-compatible Taylor components preserves non-composable
words**, along an injective map of objects. -/
theorem IsWordPathCompatible.coalgHom_mem_nonComposableWords (ht : IsWordPathCompatible φ t)
    (hφ : Function.Injective φ) {w : ReducedTensorWords R (TotalHom R C)}
    (hw : w ∈ nonComposableWords R C) : coalgHom R t w ∈ nonComposableWords R D := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl⟩ := hw
    rw [of_tprod_eq_subword R hn]
    exact ht.coalgHom_subword_mem_nonComposableWords hφ hz n 0 (by omega) (by simpa using hab)
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-- Composing a path-compatible map with the coalgebra morphism of path-compatible Taylor
components along an injective map of objects gives a path-compatible map. -/
theorem IsWordPathCompatible.comp_coalgHom {E : Type u''} [GradedLinearQuiver.{u'', v'', w} R E]
    {ψ : D → E} {s : ReducedTensorWords R (TotalHom R D) →ₗ[R] TotalHom R E}
    (hs : IsWordPathCompatible ψ s) (ht : IsWordPathCompatible φ t) (hφ : Function.Injective φ) :
    IsWordPathCompatible (ψ ∘ φ) (s ∘ₗ coalgHom R t) where
  mem_range_of_mem_composableWords hw :=
    hs.mem_range_of_mem_composableWords (ht.coalgHom_mem_composableWords hw)
  eq_zero_of_mem_nonComposableWords hw :=
    hs.eq_zero_of_mem_nonComposableWords (ht.coalgHom_mem_nonComposableWords hφ hw)

/-- **Relations on composable words extend to coalgebra morphisms.** If the Taylor maps `t` and
`t₁` are related through letterwise maps `Θ` and `Θ'` on composable words, then so are the
coalgebra morphisms they generate. -/
theorem map_coalgHom_of_mem_composableWords {M₁ N N₁ : Type*} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid N] [Module R N] [AddCommMonoid N₁] [Module R N₁] {Θ : TotalHom R C →ₗ[R] M₁}
    {Θ' : N →ₗ[R] N₁} {t : ReducedTensorWords R (TotalHom R C) →ₗ[R] N}
    {t₁ : ReducedTensorWords R M₁ →ₗ[R] N₁}
    (h : ∀ X Y : C, ∀ w ∈ composableWords R X Y,
      Θ' (t w) = t₁ (ReducedTensorWords.map (R := R) Θ w))
    {X Y : C} {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ composableWords R X Y) :
    ReducedTensorWords.map (R := R) Θ' (coalgHom R t w) =
      coalgHom R t₁ (ReducedTensorWords.map (R := R) Θ w) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl, rfl, rfl⟩ := hw
    rw [of_tprod_eq_subword R hn, map_subword]
    -- Induct on the length of a block.
    suffices key : ∀ s p, ReducedTensorWords.map (R := R) Θ'
        (coalgHom R t (subword R (fun i : Fin n ↦ z i) p s)) =
          coalgHom R t₁ (subword R (fun i : Fin n ↦ Θ (z i)) p s) from key n 0
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro p
      have hblock (d : ℕ) : Θ' (t (subword R (fun i : Fin n ↦ z i) p d)) =
          t₁ (subword R (fun i : Fin n ↦ Θ (z i)) p d) := by
        obtain ⟨X, Y, hXY⟩ := exists_subword_mem_composableWords hz hab p d
        rw [h X Y _ hXY, map_subword]
      rw [coalgHom_subword, coalgHom_subword, map_add, map_ofLetter, hblock, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun d hd ↦ ?_)
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | hd₀
      · simp
      rw [map_prepend, hblock, ih (s - d) (by omega)]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

end CoalgHom

/-! ### Graded Taylor expansions of path-compatible maps -/

section GradedCoderiv

/-- The Koszul twist of a shift of the total grading preserves each hom module. -/
theorem koszulTwist_shift_mem_range (c q : ℤ) {X Y : C} {u : TotalHom R C}
    (hu : u ∈ LinearMap.range (homInclusion (R := R) X Y)) :
    ((totalGrading R C).shift c).koszulTwist q u ∈
      LinearMap.range (homInclusion (R := R) X Y) := by
  rw [InternalGrading.koszulTwist_shift, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (koszulTwist_mem_range_homInclusion q hu)

/-- The natural-indexed string with its first `p` morphisms Koszul-twisted. -/
private noncomputable def twistNat (G : InternalGrading R (TotalHom R C)) (q : ℤ)
    (z : ℕ → TotalHom R C) (p : ℕ) : ℕ → TotalHom R C :=
  fun i ↦ if i < p then G.koszulTwist q (z i) else z i

private theorem twistedTuple_eq_twistNat (G : InternalGrading R (TotalHom R C)) (q : ℤ) {n : ℕ}
    (z : ℕ → TotalHom R C) (p : ℕ) :
    G.twistedTuple q (fun i : Fin n ↦ z i) 0 p = fun i : Fin n ↦ twistNat G q z p i := by
  funext i
  simp [twistNat, InternalGrading.twistedTuple_apply]

private theorem twistNat_mem (c q : ℤ) {n : ℕ} {a b : ℕ → C} {z : ℕ → TotalHom R C}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) (p : ℕ) :
    ∀ i < n, twistNat ((totalGrading R C).shift c) q z p i ∈
      LinearMap.range (homInclusion (R := R) (a i) (b i)) := fun i hi ↦ by
  unfold twistNat
  split_ifs
  · exact koszulTwist_shift_mem_range c q (hz i hi)
  · exact hz i hi

variable {t : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R C}

/-- **The graded Taylor expansion of a path-compatible map preserves composable words**: for a
shift of the total grading, it sends composable words from `X` to `Y` to composable words from `X`
to `Y`. -/
theorem IsWordPathCompatible.gradedCoderiv_mem_composableWords (ht : IsWordPathCompatible id t)
    (c q : ℤ) {X Y : C} {w : ReducedTensorWords R (TotalHom R C)}
    (hw : w ∈ composableWords R X Y) :
    gradedCoderiv ((totalGrading R C).shift c) t q w ∈ composableWords R X Y := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl, rfl, rfl⟩ := hw
    rw [gradedCoderiv_of_tprod]
    refine Submodule.sum_mem _ fun p _ ↦ Submodule.sum_mem _ fun d _ ↦ ?_
    by_cases hfit : 0 < d ∧ p + d ≤ n
    · obtain ⟨hd, hpd⟩ := hfit
      have he := ht.mem_range_of_mem_composableWords
        (subword_mem_composableWords hz (hab.block hpd) hd hpd)
      rw [twistedTuple_eq_twistNat, splice_eq_of_tprod_replaceBlock R _ hd hpd]
      have h := of_tprod_mem_composableWords (by omega)
        (replaceBlock_mem_range_homInclusion (twistNat_mem c q hz p) he hpd)
        (hab.replaceBlock hd hpd)
      rwa [replaceBlock_last a hd hpd, replaceBlock_zero] at h
    · rw [splice_eq_zero_of_not_fits R _ _ hfit]
      exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-- **The graded Taylor expansion of a path-compatible map preserves non-composable words**, for a
shift of the total grading. -/
theorem IsWordPathCompatible.gradedCoderiv_mem_nonComposableWords (ht : IsWordPathCompatible id t)
    (c q : ℤ) {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ nonComposableWords R C) :
    gradedCoderiv ((totalGrading R C).shift c) t q w ∈ nonComposableWords R C := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl⟩ := hw
    rw [gradedCoderiv_of_tprod]
    refine Submodule.sum_mem _ fun p _ ↦ Submodule.sum_mem _ fun d _ ↦ ?_
    by_cases hfit : 0 < d ∧ p + d ≤ n
    · obtain ⟨hd, hpd⟩ := hfit
      by_cases hblock : IsComposableString (fun j ↦ a (p + j)) (fun j ↦ b (p + j)) d
      · -- The collapsed block is composable, so the string with the block replaced is not.
        have he := ht.mem_range_of_mem_composableWords
          (subword_mem_composableWords hz hblock hd hpd)
        rw [twistedTuple_eq_twistNat, splice_eq_of_tprod_replaceBlock R _ hd hpd]
        exact of_tprod_mem_nonComposableWords _
          (replaceBlock_mem_range_homInclusion (twistNat_mem c q hz p) he hpd)
          ((not_isComposableString_block_or_replaceBlock hab hpd).resolve_left (not_not.2 hblock))
      · rw [ht.eq_zero_of_mem_nonComposableWords (subword_mem_nonComposableWords hz hblock hpd),
          splice_zero]
        exact zero_mem _
    · rw [splice_eq_zero_of_not_fits R _ _ hfit]
      exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-- Composing a path-compatible map with the graded Taylor expansion of a path-compatible map gives
a path-compatible map. -/
theorem IsWordPathCompatible.comp_gradedCoderiv {D : Type u'} [GradedLinearQuiver.{u', v', w} R D]
    {φ : C → D} {s : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R D}
    (hs : IsWordPathCompatible φ s) (ht : IsWordPathCompatible id t) (c q : ℤ) :
    IsWordPathCompatible φ (s ∘ₗ gradedCoderiv ((totalGrading R C).shift c) t q) where
  mem_range_of_mem_composableWords hw :=
    hs.mem_range_of_mem_composableWords (ht.gradedCoderiv_mem_composableWords c q hw)
  eq_zero_of_mem_nonComposableWords hw :=
    hs.eq_zero_of_mem_nonComposableWords (ht.gradedCoderiv_mem_nonComposableWords c q hw)

/-- **Relations on composable words extend to graded Taylor expansions.** If a degree-preserving
letterwise map `Θ` relates the Taylor maps `t` and `t₁` on composable words, it relates their graded
Taylor expansions on composable words. -/
theorem map_gradedCoderiv_of_mem_composableWords {M₁ : Type*} [AddCommMonoid M₁] [Module R M₁]
    {G : InternalGrading R (TotalHom R C)} {G₁ : InternalGrading R M₁}
    {Θ : TotalHom R C →ₗ[R] M₁} (hΘ : LinearMap.IsHomogeneous Θ G.piece G₁.piece 0)
    {t₁ : ReducedTensorWords R M₁ →ₗ[R] M₁}
    (h : ∀ X Y : C, ∀ w ∈ composableWords R X Y,
      Θ (t w) = t₁ (ReducedTensorWords.map (R := R) Θ w))
    (q : ℤ) {X Y : C} {w : ReducedTensorWords R (TotalHom R C)} (hw : w ∈ composableWords R X Y) :
    ReducedTensorWords.map (R := R) Θ (gradedCoderiv G t q w) =
      gradedCoderiv G₁ t₁ q (ReducedTensorWords.map (R := R) Θ w) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, a, b, z, hz, hab, rfl, rfl, rfl⟩ := hw
    rw [map_of_tprod, gradedCoderiv_of_tprod, gradedCoderiv_of_tprod, map_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    obtain ⟨X, Y, hXY⟩ := exists_subword_mem_composableWords hz hab p d
    rw [map_splice, h X Y _ hXY, map_subword, hΘ.twistedTuple_map]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

end GradedCoderiv

end TauCeti.GradedLinearQuiver
