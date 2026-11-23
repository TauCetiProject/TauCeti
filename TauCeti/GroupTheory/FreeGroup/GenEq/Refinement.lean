/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Parametric
import Mathlib.Data.Fin.VecNotation

/-!
# Refining a generalised equation: splitting items and adding bases

Let `Ω` be a generalised equation over `F = F(A)` with `ρ` items. This file defines two operations
on `Ω`, cutting its items into pieces and adding new bases, and relates the points, solutions and
section partitions of the result to those of `Ω`, under the conditions stated below.

* *Splitting items* (`TauCeti.GenEq.splitItems`). An order embedding
  `bd : {0, …, ρ} ↪ {0, …, n}` of boundaries cuts the item `h_k` of `Ω` into the items
  `h'_{bd k}, …, h'_{bd (k+1) - 1}` of an equation with `n` items, the end-points of the bases and
  the boundary connections being moved along `bd`; a constant base goes to the last piece of its
  item, and the items before `bd 0` and from `bd ρ` on are free. When no constant item is cut, the
  equations of the result are those of `Ω` with every item replaced by the word of its pieces
  (`TauCeti.GenEq.equations_splitItems`), so the points of its system are the tuples whose
  products over the pieces are points of `Ω*` (`TauCeti.GenEq.mem_V_splitItems_iff`). When `bd`
  fixes the end boundaries, a solution of `Ω` whose words are cut into nonempty pieces is a
  solution of the result (`TauCeti.GenEq.Solution.splitItems`). For one cut this is the
  introduction of a boundary by the elementary transformation ET5 of Makanin's process
  (Kharlampovich–Myasnikov, §5.1, second kind), without the boundary connection that ET5 adds
  through the new boundary.
* *Adding bases* (`TauCeti.GenEq.addBases`). New dual pairs of variable bases, indexed by a finite
  type with an involution, are added to those of `Ω`. The points of the result are the points of
  `Ω*` satisfying the new basic equations (`TauCeti.GenEq.mem_V_addBases_iff`), and a solution of
  `Ω` satisfying them letter by letter is a solution of the result
  (`TauCeti.GenEq.Solution.addBases`). The bases, constant bases and boundary connections of `Ω`
  are kept; `TauCeti.GenEq.ofBases` is the generalised equation given by such bases alone.

Section partitions are transported: a partition of the closed sections of `Ω` gives the pieces of
an item the kind of the item when `bd` fixes the end boundaries
(`TauCeti.GenEq.SectionPartition.splitItems`), and survives the addition of bases all of whose
items have one kind (`TauCeti.GenEq.SectionPartition.addBases`).

In the second minimal replacement of Kharlampovich and Myasnikov ([IFT], Lemma 29) the content of
the periodic sections is transferred to the parametric part by new bases; the equations of the
transfer are obtained from `Ω` by these two operations, the items of the periodic sections and of
the parameters being cut and the pieces identified by new bases.

## Main definitions

* `TauCeti.GenEq.splitItems`, `TauCeti.GenEq.Solution.splitItems`: splitting items along an order
  embedding of boundaries, and the solution with cut words.
* `TauCeti.GenEq.lastPiece`: the last piece of an item.
* `TauCeti.GenEq.splitItemsWord`: a word in the items of `Ω` with every item replaced by the word
  of its pieces.
* `TauCeti.GenEq.addBases`, `TauCeti.GenEq.Solution.addBases`: adding variable bases, and a
  solution satisfying the new basic equations.
* `TauCeti.GenEq.SectionPartition.splitItems`, `TauCeti.GenEq.SectionPartition.addBases`: section
  partitions under these operations.

## Main results

* `TauCeti.GenEq.equations_splitItems`, `TauCeti.GenEq.mem_equations_addBases_iff`: the equations
  of the results, with the equation-by-equation forms `TauCeti.GenEq.basicEquation_splitItems`,
  `TauCeti.GenEq.coeffEquation_splitItems`, `TauCeti.GenEq.boundaryEquation_splitItems` and
  `TauCeti.GenEq.basicEquation_addBases_castAdd`, `TauCeti.GenEq.basicEquation_addBases_natAdd`,
  `TauCeti.GenEq.coeffEquation_addBases`, `TauCeti.GenEq.boundaryEquation_addBases`.
* `TauCeti.GenEq.mem_V_splitItems_iff`, `TauCeti.GenEq.mem_V_addBases_iff`: the points of the
  systems of the results.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.1 (ET5) and §5.4.3 (Lemma 29).
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom
open FreeGroup (substituteVars)

variable {A : Type*}

/-! ### Splitting items -/

section SplitItems

variable (Ω : GenEq A) (n : ℕ) (bd : Fin (Ω.numItems + 1) ↪o Fin (n + 1))

/-- The last piece of an item after splitting along `bd`: the item preceding the boundary
`bd (k + 1)`. -/
def lastPiece : Fin Ω.numItems ↪ Fin n where
  toFun k := (bd k.succ).pred ((Fin.zero_le _).trans_lt (bd.strictMono k.castSucc_lt_succ)).ne'
  inj' k k' h := by
    simpa using bd.injective (Fin.pred_inj.1 h)

/-- The last piece of `h_k` ends at the boundary `bd (k + 1)`. -/
@[simp]
theorem succ_lastPiece (k : Fin Ω.numItems) : (lastPiece Ω n bd k).succ = bd k.succ :=
  Fin.succ_pred _ ((Fin.zero_le _).trans_lt (bd.strictMono k.castSucc_lt_succ)).ne'

/-- Split the items of `Ω` along an order embedding `bd` of boundaries: the result has `n` items,
the item `h_k` of `Ω` being replaced by the items between the boundaries `bd k` and `bd (k + 1)`;
the end-points of the bases and the boundary connections are moved along `bd`, signs and duality
are kept, and a constant base on `h_k` is put on its last piece. The items before `bd 0` and from
`bd ρ` on lie in no base. -/
abbrev splitItems : GenEq A where
  numItems := n
  numBases := Ω.numBases
  left μ := bd (Ω.left μ)
  right μ := bd (Ω.right μ)
  left_lt_right μ := bd.strictMono (Ω.left_lt_right μ)
  sign := Ω.sign
  dual := Ω.dual
  dual_involutive := Ω.dual_involutive
  constBases := Ω.constBases.map ((lastPiece Ω n bd).prodMap (Function.Embedding.refl _))
  connections := Ω.connections.map
    (bd.toEmbedding.prodMap ((Function.Embedding.refl _).prodMap bd.toEmbedding))
  bounds_of_mem_connections := by
    simp only [Finset.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections c hc
    exact ⟨bd.strictMono h₁, bd.strictMono h₂, bd.strictMono h₃, bd.strictMono h₄⟩
  dual_mem_connections := by
    simp only [Finset.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨_, Ω.dual_mem_connections c hc, rfl⟩

variable {Ω n bd}

/-- The constant bases of the split equation are those of `Ω`, on the last piece of their item. -/
theorem mem_constBases_splitItems {b : Fin n × (A × Bool)} :
    b ∈ (Ω.splitItems n bd).constBases ↔
      ∃ b' ∈ Ω.constBases, (lastPiece Ω n bd b'.1, b'.2) = b :=
  Finset.mem_map

variable (Ω n bd) in
/-- The word in the items of the split equation obtained from a word in the items of `Ω` and the
letters of `A` by replacing every item `h_k` by the word `h'[bd k, bd (k + 1)]` of its pieces, and
an inverse item by the formal inverse of that word, without free reduction; the letters of `A` are
kept. -/
def splitItemsWord (w : List ((Fin Ω.numItems ⊕ A) × Bool)) : List ((Fin n ⊕ A) × Bool) :=
  w.flatMap (FreeGroup.substituteLetter (Sum.elim
    (fun k ↦ (Ω.splitItems n bd).segment (bd k.castSucc) (bd k.succ) true)
    fun a ↦ [(Sum.inr a, true)]))

@[simp]
theorem splitItemsWord_nil : splitItemsWord Ω n bd [] = [] :=
  List.flatMap_nil

/-- The word of pieces of a concatenation is the concatenation of the words of pieces. -/
@[simp]
theorem splitItemsWord_append (w w' : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    splitItemsWord Ω n bd (w ++ w') = splitItemsWord Ω n bd w ++ splitItemsWord Ω n bd w' :=
  List.flatMap_append

/-- The item `h_k ^ ±1` becomes the word `h'[bd k, bd (k + 1)] ^ ±1` of its pieces. -/
@[simp]
theorem splitItemsWord_singleton_inl (k : Fin Ω.numItems) (s : Bool) :
    splitItemsWord Ω n bd [(Sum.inl k, s)] =
      (Ω.splitItems n bd).segment (bd k.castSucc) (bd k.succ) s := by
  cases s <;> simp [splitItemsWord, segment_false]

/-- A letter of `A^{±1}` is kept. -/
@[simp]
theorem splitItemsWord_singleton_inr (a : A) (s : Bool) :
    splitItemsWord Ω n bd [(Sum.inr a, s)] = [(Sum.inr a, s)] := by
  cases s <;> simp [splitItemsWord, FreeGroup.invRev]

/- The word `h[i, j]` of `Ω` becomes, piece by piece, the word between the boundaries `bd i` and
`bd j` of the split equation. -/
private theorem segment_splitItems_true {i j : Fin (Ω.numItems + 1)} (hij : i ≤ j) :
    (Ω.splitItems n bd).segment (bd i) (bd j) true =
      splitItemsWord Ω n bd (Ω.segment i j true) := by
  induction j using Fin.induction with
  | zero =>
    obtain rfl := le_antisymm hij (Fin.zero_le _)
    simp [segment_eq_nil_of_le]
  | succ x ih =>
    rcases hij.lt_or_eq with h | rfl
    · have hx : i ≤ x.castSucc := Fin.le_castSucc_iff.2 h
      rw [← (Ω.splitItems n bd).segment_append (bd.monotone hx)
          (bd.strictMono x.castSucc_lt_succ).le, ih hx,
        ← Ω.segment_append hx x.castSucc_lt_succ.le, splitItemsWord_append,
        ← splitItemsWord_singleton_inl]
      simp
    · simp [segment_eq_nil_of_le]

/-- The word `h[i, j] ^ ±1` of `Ω` becomes, piece by piece, the word `h'[bd i, bd j] ^ ±1` of the
split equation. -/
theorem segment_splitItems (i j : Fin (Ω.numItems + 1)) (s : Bool) :
    (Ω.splitItems n bd).segment (bd i) (bd j) s = splitItemsWord Ω n bd (Ω.segment i j s) := by
  have htrue : (Ω.splitItems n bd).segment (bd i) (bd j) true =
      splitItemsWord Ω n bd (Ω.segment i j true) := by
    rcases le_or_gt i j with hij | hji
    · exact segment_splitItems_true hij
    · rw [Ω.segment_eq_nil_of_le (Fin.le_def.1 hji.le),
        (Ω.splitItems n bd).segment_eq_nil_of_le (Fin.le_def.1 (bd.strictMono hji).le)]
      rfl
  cases s
  · rw [segment_false, segment_false, htrue]
    exact (FreeGroup.flatMap_substituteLetter_invRev _ _).symm
  · exact htrue

/-- The basic equation of a base of the split equation is that of `Ω` with every item replaced by
the word of its pieces. -/
theorem basicEquation_splitItems (μ : Fin Ω.numBases) :
    (Ω.splitItems n bd).basicEquation μ =
      Prod.map (splitItemsWord Ω n bd) (splitItemsWord Ω n bd) (Ω.basicEquation μ) :=
  Prod.ext (by simpa using segment_splitItems _ _ _) (by simpa using segment_splitItems _ _ _)

/-- If the item `h_k` of a constant base `(k, a)` is not cut, the coefficient equation of the
constant base on its last piece is that of `Ω` with `h_k` replaced by its piece. -/
theorem coeffEquation_splitItems {b : Fin Ω.numItems × (A × Bool)}
    (hb : (bd b.1.succ : ℕ) = bd b.1.castSucc + 1) :
    (Ω.splitItems n bd).coeffEquation (lastPiece Ω n bd b.1, b.2) =
      Prod.map (splitItemsWord Ω n bd) (splitItemsWord Ω n bd) (Ω.coeffEquation b) := by
  have h : (lastPiece Ω n bd b.1 : ℕ) = bd b.1.castSucc := by
    have := congrArg Fin.val (succ_lastPiece Ω n bd b.1)
    simp only [Fin.val_succ] at this
    lia
  obtain ⟨k, a, t⟩ := b
  refine Prod.ext ?_ (by simp)
  simp only [coeffEquation_fst, Prod.map_fst, splitItemsWord_singleton_inl]
  rw [← (Ω.splitItems n bd).segment_succ (lastPiece Ω n bd k) true, h, ← hb]

/-- The boundary equation of a boundary connection `(bd p, μ, bd q)` of the split equation is that
of `(p, μ, q)` in `Ω` with every item replaced by the word of its pieces. -/
theorem boundaryEquation_splitItems (p : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases)
    (q : Fin (Ω.numItems + 1)) :
    (Ω.splitItems n bd).boundaryEquation (bd p, μ, bd q) =
      Prod.map (splitItemsWord Ω n bd) (splitItemsWord Ω n bd) (Ω.boundaryEquation (p, μ, q)) := by
  refine Prod.ext (by simpa using segment_splitItems _ _ _) ?_
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [Prod.map_snd, Ω.boundaryEquation_snd_of_sign_eq (c := (p, μ, q)) hs,
      (Ω.splitItems n bd).boundaryEquation_snd_of_sign_eq (c := (_, μ, _)) hs]
    exact segment_splitItems _ _ _
  · rw [Prod.map_snd, Ω.boundaryEquation_snd_of_sign_ne (c := (p, μ, q)) hs,
      (Ω.splitItems n bd).boundaryEquation_snd_of_sign_ne (c := (_, μ, _)) hs]
    exact segment_splitItems _ _ _

/-- If no constant item is cut, the equations of the split equation are those of `Ω` with every
item replaced by the word of its pieces. -/
theorem equations_splitItems
    (hconst : ∀ b ∈ Ω.constBases, (bd b.1.succ : ℕ) = bd b.1.castSucc + 1) :
    (Ω.splitItems n bd).equations =
      Prod.map (splitItemsWord Ω n bd) (splitItemsWord Ω n bd) '' Ω.equations := by
  refine Set.Subset.antisymm ((forall_mem_equations _).2 ⟨fun μ ↦ ⟨_,
    Ω.basicEquation_mem_equations μ, (basicEquation_splitItems (bd := bd) μ).symm⟩, fun b hb ↦ ?_,
    fun c hc ↦ ?_⟩) (Set.image_subset_iff.2 ((forall_mem_equations _).2 ⟨fun μ ↦ ?_,
      fun b hb ↦ ?_, fun ⟨p, μ, q⟩ hc ↦ ?_⟩))
  · obtain ⟨b, hb', rfl⟩ := mem_constBases_splitItems.1 hb
    exact ⟨_, Ω.coeffEquation_mem_equations hb', (coeffEquation_splitItems (hconst b hb')).symm⟩
  · obtain ⟨⟨p, μ, q⟩, hc', rfl⟩ := Finset.mem_map.1 hc
    exact ⟨_, Ω.boundaryEquation_mem_equations hc', (boundaryEquation_splitItems p μ q).symm⟩
  · rw [Set.mem_preimage, ← basicEquation_splitItems (bd := bd)]
    exact (Ω.splitItems n bd).basicEquation_mem_equations μ
  · rw [Set.mem_preimage, ← coeffEquation_splitItems (hconst b hb)]
    exact (Ω.splitItems n bd).coeffEquation_mem_equations (mem_constBases_splitItems.2 ⟨b, hb, rfl⟩)
  · rw [Set.mem_preimage, ← boundaryEquation_splitItems (bd := bd)]
    exact (Ω.splitItems n bd).boundaryEquation_mem_equations (Finset.mem_map_of_mem _ hc)

/-- Evaluating a word with every item replaced by the word of its pieces is evaluating the word at
the products over the pieces. -/
theorem lift_mk_splitItemsWord {H : Type*} [Group H] (ι : FreeGroup A →* H) (v : Fin n → H)
    (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk (splitItemsWord Ω n bd w)) =
      FreeGroup.lift (Sum.elim (fun k ↦ FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of))
        (FreeGroup.mk ((Ω.splitItems n bd).segment (bd k.castSucc) (bd k.succ) true)))
          (ι ∘ FreeGroup.of)) (FreeGroup.mk w) := by
  rw [splitItemsWord, FreeGroup.mk_flatMap_substituteLetter, ← MonoidHom.comp_apply]
  congr 1
  refine FreeGroup.ext_hom _ _ fun x ↦ ?_
  rcases x with k | a <;> simp [FreeGroup.lift_mk]

/-- If no constant item is cut, a tuple is a point of the system of the split equation exactly when
the tuple of its products over the pieces of the items of `Ω` is a point of `Ω*`, in every group
over `F(A)`. -/
theorem mem_V_splitItems_iff (hconst : ∀ b ∈ Ω.constBases, (bd b.1.succ : ℕ) = bd b.1.castSucc + 1)
    {H : Type*} [Group H] (ι : FreeGroup A →* H) {v : Fin n → H} :
    v ∈ V ι (Ω.splitItems n bd).toSystem ↔
      (fun k ↦ FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of))
        (FreeGroup.mk ((Ω.splitItems n bd).segment (bd k.castSucc) (bd k.succ) true))) ∈
          V ι Ω.toSystem := by
  rw [mem_V_toSystem_iff, mem_V_toSystem_iff, equations_splitItems hconst, Set.forall_mem_image]
  refine forall₂_congr fun e _ ↦ ?_
  rw [Prod.map_fst, Prod.map_snd, lift_mk_splitItemsWord, lift_mk_splitItemsWord]

/-- Substituting words for the items of the split equation into a word with every item replaced by
the word of its pieces is substituting into the word itself, with the concatenated words of the
pieces for the items. -/
theorem substituteVars_splitItemsWord (W : Fin n → List (A × Bool))
    (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    substituteVars W (splitItemsWord Ω n bd w) = substituteVars (fun k ↦
      substituteVars W ((Ω.splitItems n bd).segment (bd k.castSucc) (bd k.succ) true)) w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [← List.singleton_append, splitItemsWord_append, FreeGroup.substituteVars_append,
      FreeGroup.substituteVars_append, ih]
    obtain ⟨k | a, _ | _⟩ := x <;> simp [segment_false, FreeGroup.substituteVars_invRev]

/- A solution of `Ω` cut into nonempty pieces does not cut a constant item: its word has one
letter. -/
private theorem succ_eq_of_mem_constBases (U : Ω.Solution) {W : Fin n → List (A × Bool)}
    (hne : ∀ k, W k ≠ [])
    (hW : ∀ k, substituteVars W ((Ω.splitItems n bd).segment (bd k.castSucc) (bd k.succ) true) =
      U.word k) {b : Fin Ω.numItems × (A × Bool)} (hb : b ∈ Ω.constBases) :
    (bd b.1.succ : ℕ) = bd b.1.castSucc + 1 := by
  have e := U.subst_eq _ (Ω.coeffEquation_mem_equations hb)
  simp only [coeffEquation_fst, coeffEquation_snd, FreeGroup.substituteVars_singleton_inl,
    FreeGroup.substituteVars_singleton_inr] at e
  have h := FreeGroup.length_le_length_substituteVars (w := (Ω.splitItems n bd).segment
    (bd b.1.castSucc) (bd b.1.succ) true) fun k _ _ ↦ hne k
  rw [hW, e, length_segment, min_eq_left (bd b.1.succ).is_le] at h
  have := bd.strictMono b.1.castSucc_lt_succ
  simp only [List.length_singleton, Fin.lt_def] at h this
  lia

/- A property of the two sides of every equation of `Ω` under a solution is the property of the two
sides of every equation of the split equation under the pieces of the words of the solution. -/
private theorem forall_mem_equations_splitItems (U : Ω.Solution) {W : Fin n → List (A × Bool)}
    (hne : ∀ k, W k ≠ [])
    (hW : ∀ k, substituteVars W ((Ω.splitItems n bd).segment (bd k.castSucc) (bd k.succ) true) =
      U.word k) (P : List (A × Bool) → List (A × Bool) → Prop)
    (h : ∀ e ∈ Ω.equations, P (substituteVars U.word e.1) (substituteVars U.word e.2)) :
    ∀ e ∈ (Ω.splitItems n bd).equations, P (substituteVars W e.1) (substituteVars W e.2) := by
  rw [equations_splitItems fun b hb ↦ succ_eq_of_mem_constBases U hne hW hb, Set.forall_mem_image]
  intro e he
  rw [Prod.map_fst, Prod.map_snd, substituteVars_splitItemsWord, substituteVars_splitItemsWord,
    funext hW]
  exact h e he

/- For a splitting fixing the end boundaries, every item of the split equation is a piece of a
unique item of `Ω`. -/
private theorem existsUnique_splitItems_parent (h₀ : bd 0 = 0)
    (hlast : bd (Fin.last Ω.numItems) = Fin.last n) (k' : Fin n) :
    ∃! k : Fin Ω.numItems, bd k.castSucc ≤ k'.castSucc ∧ k'.succ ≤ bd k.succ := by
  -- The first boundary of `Ω` after the piece `k'` ends its parent.
  have hS : ({j | k'.castSucc < bd j} : Finset (Fin (Ω.numItems + 1))).Nonempty :=
    ⟨Fin.last _, by simp [hlast, Fin.castSucc_lt_last]⟩
  set j := Finset.min' _ hS
  have hj : k'.castSucc < bd j := (Finset.mem_filter.1 (Finset.min'_mem _ hS)).2
  obtain ⟨k, hk⟩ := Fin.exists_succ_eq.2 (fun h : j = 0 ↦ by simp [h, h₀] at hj)
  have hk₁ : bd k.castSucc ≤ k'.castSucc := not_lt.1 fun h ↦
    (Finset.min'_le _ k.castSucc (by simp [h])).not_gt (hk ▸ k.castSucc_lt_succ)
  have hk₂ := Fin.castSucc_lt_iff_succ_le.1 (hk ▸ hj)
  refine ⟨k, ⟨hk₁, hk₂⟩, fun k₁ ⟨h₁, h₂⟩ ↦ le_antisymm (not_lt.1 fun h ↦ ?_)
    (not_lt.1 fun h ↦ ?_)⟩ <;>
  -- Two parents would be nested, `bd (k₁ + 1) ≤ bd k` or `bd (k + 1) ≤ bd k₁`.
  · have := bd.monotone (Fin.succ_le_castSucc_iff.2 h)
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at this h₁ h₂ hk₁ hk₂
    lia

/-- A solution of `Ω` whose words are cut into nonempty pieces, for a splitting along `bd` which
fixes the end boundaries: the words of the pieces form a solution of the split equation. (A
constant item, whose word has one letter, is then not cut.) -/
def Solution.splitItems (h₀ : bd 0 = 0) (hlast : bd (Fin.last Ω.numItems) = Fin.last n)
    (U : Ω.Solution) (W : Fin n → List (A × Bool)) (hne : ∀ k, W k ≠ [])
    (hW : ∀ k, substituteVars W ((Ω.splitItems n bd).segment (bd k.castSucc) (bd k.succ) true) =
      U.word k) :
    (Ω.splitItems n bd).Solution where
  word := W
  isReduced_word k' := by
    -- Every piece is a factor of the word of its parent item.
    obtain ⟨k, ⟨h₁, h₂⟩, -⟩ := existsUnique_splitItems_parent h₀ hlast k'
    have h := hW k ▸ U.isReduced_word k
    have h₁' : (bd k.castSucc : ℕ) ≤ k' := by simpa [Fin.le_def] using h₁
    have h₂' : (k' : ℕ) + 1 ≤ bd k.succ := by simpa [Fin.le_def] using h₂
    rw [← (Ω.splitItems n bd).segment_append h₁' (by lia),
      ← (Ω.splitItems n bd).segment_append (Nat.le_succ _) h₂',
      segment_succ] at h
    simp only [FreeGroup.substituteVars_append, FreeGroup.substituteVars_singleton_inl] at h
    exact h.infix ⟨_, _, List.append_assoc _ _ _⟩
  word_ne_nil := hne
  isReduced_subst := forall_mem_equations_splitItems U hne hW
    (fun u w ↦ FreeGroup.IsReduced u ∧ FreeGroup.IsReduced w) U.isReduced_subst
  subst_eq := forall_mem_equations_splitItems U hne hW (· = ·) U.subst_eq

/-- The words of the cut solution are the pieces. -/
@[simp]
theorem Solution.splitItems_word (h₀ : bd 0 = 0) (hlast : bd (Fin.last Ω.numItems) = Fin.last n)
    (U : Ω.Solution) (W : Fin n → List (A × Bool)) (hne : ∀ k, W k ≠ [])
    (hW : ∀ k, substituteVars W ((Ω.splitItems n bd).segment (bd k.castSucc) (bd k.succ) true) =
      U.word k) :
    (Solution.splitItems h₀ hlast U W hne hW).word = W :=
  (rfl)

/- The item of `Ω` of which an item of the split equation is a piece. -/
private noncomputable def splitItemsParent (h₀ : bd 0 = 0)
    (hlast : bd (Fin.last Ω.numItems) = Fin.last n) (k' : Fin n) : Fin Ω.numItems :=
  (existsUnique_splitItems_parent h₀ hlast k').exists.choose

private theorem splitItemsParent_spec (h₀ : bd 0 = 0)
    (hlast : bd (Fin.last Ω.numItems) = Fin.last n) (k' : Fin n) :
    bd (splitItemsParent h₀ hlast k').castSucc ≤ k'.castSucc ∧
      k'.succ ≤ bd (splitItemsParent h₀ hlast k').succ :=
  (existsUnique_splitItems_parent h₀ hlast k').exists.choose_spec

private theorem splitItemsParent_eq (h₀ : bd 0 = 0) (hlast : bd (Fin.last Ω.numItems) = Fin.last n)
    {k : Fin Ω.numItems} {k' : Fin n} (h₁ : bd k.castSucc ≤ k'.castSucc)
    (h₂ : k'.succ ≤ bd k.succ) : splitItemsParent h₀ hlast k' = k :=
  (existsUnique_splitItems_parent h₀ hlast k').unique (splitItemsParent_spec h₀ hlast k') ⟨h₁, h₂⟩

/- The parents of two consecutive items of the split equation separated by an open boundary have
the same kind: either they are equal, or the boundary is `bd` of an open boundary of `Ω`. -/
private theorem itemKind_eq_of_isOpenBoundary_splitItems (h₀ : bd 0 = 0)
    (hlast : bd (Fin.last Ω.numItems) = Fin.last n) (P : Ω.SectionPartition) (k k' : Fin n)
    (hk' : (k' : ℕ) = k + 1) (ho : (Ω.splitItems n bd).IsOpenBoundary k.succ) :
    P.itemKind (splitItemsParent h₀ hlast k') = P.itemKind (splitItemsParent h₀ hlast k) := by
  obtain ⟨hp₁, hp₂⟩ := splitItemsParent_spec h₀ hlast k
  set p := splitItemsParent h₀ hlast k
  have hp₁' : (bd p.castSucc : ℕ) ≤ k := by simpa [Fin.le_def] using hp₁
  rcases (Fin.le_def.1 hp₂).lt_or_eq with hlt | heq
  · -- The piece `k'` still lies in the parent of `k`.
    simp only [Fin.val_succ] at hlt
    rw [splitItemsParent_eq h₀ hlast (k' := k') (k := p)
      (Fin.le_def.2 (by simp only [Fin.val_castSucc]; lia))
      (Fin.le_def.2 (by simp only [Fin.val_succ]; lia))]
  · -- The boundary between the pieces is `bd (p + 1)`, open in `Ω`; the piece `k'` lies in the
    -- next item `q = p + 1`.
    obtain ⟨μ, hμ⟩ := (Ω.splitItems n bd).isOpenBoundary_iff.1 ho
    have hb : k.succ = bd p.succ := Fin.ext heq
    rw [crosses_iff, hb, bd.lt_iff_lt, bd.lt_iff_lt] at hμ
    obtain ⟨q, hq⟩ := Fin.exists_castSucc_eq.2 (hμ.2.trans_le (Fin.le_last _)).ne
    have hq' := congrArg Fin.val hq
    have hbq := bd.strictMono q.castSucc_lt_succ
    rw [hq] at hbq
    simp only [Fin.val_castSucc, Fin.val_succ] at hq' heq
    simp only [Fin.lt_def] at hbq
    rw [splitItemsParent_eq h₀ hlast (k' := k') (k := q)
      (Fin.le_def.2 (by rw [hq]; simp only [Fin.val_castSucc]; lia))
      (Fin.le_def.2 (by simp only [Fin.val_succ]; lia))]
    exact P.itemKind_eq_of_isOpenBoundary p q hq'
      (Ω.isOpenBoundary_iff.2 ⟨μ, Ω.crosses_iff.2 (hq ▸ hμ)⟩)

/-- For a splitting fixing the end boundaries, a section partition of `Ω` gives every piece of an
item the kind of that item. -/
noncomputable def SectionPartition.splitItems (h₀ : bd 0 = 0)
    (hlast : bd (Fin.last Ω.numItems) = Fin.last n) (P : Ω.SectionPartition) :
    (Ω.splitItems n bd).SectionPartition where
  itemKind k' := P.itemKind (splitItemsParent h₀ hlast k')
  itemKind_eq_of_isOpenBoundary k k' hk' ho :=
    itemKind_eq_of_isOpenBoundary_splitItems h₀ hlast P k k' hk' ho

/-- The pieces of an item have the kind of the item. -/
theorem SectionPartition.itemKind_splitItems (h₀ : bd 0 = 0)
    (hlast : bd (Fin.last Ω.numItems) = Fin.last n) (P : Ω.SectionPartition) {k : Fin Ω.numItems}
    {k' : Fin n} (h₁ : bd k.castSucc ≤ k'.castSucc) (h₂ : k'.succ ≤ bd k.succ) :
    (P.splitItems h₀ hlast).itemKind k' = P.itemKind k :=
  congrArg P.itemKind (splitItemsParent_eq h₀ hlast h₁ h₂)

end SplitItems

/-! ### Adding bases -/

section AddBases

variable (Ω : GenEq A) {β : Type*} [Finite β] (left right : β → Fin (Ω.numItems + 1))
  (left_lt_right : ∀ b, left b < right b) (sign : β → Bool) (dual : β → β)
  (dual_involutive : Function.Involutive dual)

/-- Add to `Ω` the variable bases indexed by a finite type `β`: the base `b` spans the items between
the boundaries `left b < right b`, has sign `sign b` and dual `dual b`, for an involution `dual` of
`β`. The items, the constant bases and the boundary connections are those of `Ω`. The new bases
are numbered after those of `Ω`, by an arbitrary enumeration of `β`. -/
noncomputable abbrev addBases : GenEq A :=
  letI := Fintype.ofFinite β
  { numItems := Ω.numItems
    numBases := Ω.numBases + Fintype.card β
    left := Fin.append Ω.left (left ∘ (Fintype.equivFin β).symm)
    right := Fin.append Ω.right (right ∘ (Fintype.equivFin β).symm)
    left_lt_right := Fin.addCases (fun μ ↦ by simpa using Ω.left_lt_right μ)
      (fun b ↦ by simpa using left_lt_right _)
    sign := Fin.append Ω.sign (sign ∘ (Fintype.equivFin β).symm)
    dual := Fin.append (Fin.castAdd _ ∘ Ω.dual)
      (Fin.natAdd _ ∘ Fintype.equivFin β ∘ dual ∘ (Fintype.equivFin β).symm)
    dual_involutive := Fin.addCases (fun μ ↦ by simp [Ω.dual_involutive μ])
      (fun b ↦ by simp [dual_involutive _])
    constBases := Ω.constBases
    connections := Ω.connections.image fun c ↦ (c.1, Fin.castAdd _ c.2.1, c.2.2)
    bounds_of_mem_connections := by
      simp only [Finset.mem_image]
      rintro _ ⟨c, hc, rfl⟩
      simpa using Ω.bounds_of_mem_connections c hc
    dual_mem_connections := by
      simp only [Finset.mem_image]
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨_, Ω.dual_mem_connections c hc, by simp⟩ }

variable {Ω left right left_lt_right sign dual dual_involutive}

/-- The words `h[i, j] ^ ±1` of `Ω` with added bases are those of `Ω`. -/
@[simp]
theorem segment_addBases (i j : ℕ) (s : Bool) :
    (Ω.addBases left right left_lt_right sign dual dual_involutive).segment i j s =
      Ω.segment i j s := by
  cases s <;> simp only [segment_false, segment_true]

/-- The basic equation of an old base of `Ω` with added bases is its basic equation in `Ω`. -/
@[simp]
theorem basicEquation_addBases_castAdd (μ : Fin Ω.numBases) :
    letI := Fintype.ofFinite β
    (Ω.addBases left right left_lt_right sign dual dual_involutive).basicEquation
      (Fin.castAdd _ μ) = Ω.basicEquation μ :=
  Prod.ext (by simp) (by simp)

/-- The basic equation of a new base `b` is
`h[left b, right b] ^ sign b = h[left (dual b), right (dual b)] ^ sign (dual b)`. -/
@[simp]
theorem basicEquation_addBases_natAdd (b : β) :
    letI := Fintype.ofFinite β
    (Ω.addBases left right left_lt_right sign dual dual_involutive).basicEquation
      (Fin.natAdd _ (Fintype.equivFin β b)) =
        (Ω.segment (left b) (right b) (sign b),
          Ω.segment (left (dual b)) (right (dual b)) (sign (dual b))) :=
  Prod.ext (by simp) (by simp)

/-- The coefficient equations of `Ω` with added bases are those of `Ω`. -/
@[simp]
theorem coeffEquation_addBases (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.addBases left right left_lt_right sign dual dual_involutive).coeffEquation b =
      Ω.coeffEquation b :=
  Prod.ext (by simp) (by simp)

/-- The boundary equation of a boundary connection `(p, μ, q)` of `Ω` is the same in `Ω` with added
bases. -/
@[simp]
theorem boundaryEquation_addBases (p : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases)
    (q : Fin (Ω.numItems + 1)) :
    letI := Fintype.ofFinite β
    (Ω.addBases left right left_lt_right sign dual dual_involutive).boundaryEquation
      (p, Fin.castAdd _ μ, q) = Ω.boundaryEquation (p, μ, q) := by
  let := Fintype.ofFinite β
  refine Prod.ext (by simp) ?_
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [Ω.boundaryEquation_snd_of_sign_eq (c := (p, μ, q)) hs,
      boundaryEquation_snd_of_sign_eq _ (by simpa using hs)]
    simp
  · rw [Ω.boundaryEquation_snd_of_sign_ne (c := (p, μ, q)) hs,
      boundaryEquation_snd_of_sign_ne _ (by simpa using hs)]
    simp

/-- The equations of `Ω` with added bases are those of `Ω` and the basic equations of the new
bases. -/
theorem mem_equations_addBases_iff
    {e : List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool)} :
    e ∈ (Ω.addBases left right left_lt_right sign dual dual_involutive).equations ↔
      e ∈ Ω.equations ∨ ∃ b, (Ω.segment (left b) (right b) (sign b),
        Ω.segment (left (dual b)) (right (dual b)) (sign (dual b))) = e := by
  let := Fintype.ofFinite β
  rw [mem_equations_iff, mem_equations_iff]
  constructor
  · rintro (⟨μ, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩)
    · induction μ using Fin.addCases with
      | left μ => exact Or.inl (Or.inl ⟨μ, (basicEquation_addBases_castAdd ..).symm⟩)
      | right i =>
        obtain ⟨b, rfl⟩ := (Fintype.equivFin β).surjective i
        exact Or.inr ⟨b, (basicEquation_addBases_natAdd ..).symm⟩
    · exact Or.inl (Or.inr (Or.inl ⟨b, hb, (coeffEquation_addBases ..).symm⟩))
    · obtain ⟨⟨p, μ, q⟩, hc', rfl⟩ := Finset.mem_image.1 hc
      exact Or.inl (Or.inr (Or.inr ⟨_, hc', (boundaryEquation_addBases ..).symm⟩))
  · rintro ((⟨μ, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨⟨p, μ, q⟩, hc, rfl⟩) | ⟨b, rfl⟩)
    · exact Or.inl ⟨_, basicEquation_addBases_castAdd ..⟩
    · exact Or.inr (Or.inl ⟨b, hb, coeffEquation_addBases ..⟩)
    · exact Or.inr (Or.inr ⟨_, Finset.mem_image_of_mem _ hc, boundaryEquation_addBases ..⟩)
    · exact Or.inl ⟨_, basicEquation_addBases_natAdd ..⟩

/-- A tuple is a point of the system of `Ω` with added bases exactly when it is a point of `Ω*`
satisfying the basic equations of the new bases, in every group over `F(A)`. -/
theorem mem_V_addBases_iff {H : Type*} [Group H] (ι : FreeGroup A →* H) {v : Fin Ω.numItems → H} :
    v ∈ V ι (Ω.addBases left right left_lt_right sign dual dual_involutive).toSystem ↔
      v ∈ V ι Ω.toSystem ∧ ∀ b, FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of))
          (FreeGroup.mk (Ω.segment (left b) (right b) (sign b))) =
        FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of))
          (FreeGroup.mk (Ω.segment (left (dual b)) (right (dual b)) (sign (dual b)))) := by
  rw [mem_V_toSystem_iff, mem_V_toSystem_iff]
  refine ⟨fun h ↦ ⟨fun e he ↦ h e (mem_equations_addBases_iff.2 (Or.inl he)),
    fun b ↦ h _ (mem_equations_addBases_iff.2 (Or.inr ⟨b, rfl⟩))⟩, fun ⟨h₁, h₂⟩ e he ↦ ?_⟩
  obtain he | ⟨b, rfl⟩ := mem_equations_addBases_iff.1 he
  exacts [h₁ e he, h₂ b]

variable (left_lt_right dual_involutive)

/-- A solution of `Ω` under which both sides of every new basic equation are reduced as written and
agree letter by letter is a solution of `Ω` with the added bases. -/
def Solution.addBases (U : Ω.Solution)
    (hred : ∀ b,
      FreeGroup.IsReduced (substituteVars U.word (Ω.segment (left b) (right b) (sign b))))
    (heq : ∀ b, substituteVars U.word (Ω.segment (left b) (right b) (sign b)) =
      substituteVars U.word (Ω.segment (left (dual b)) (right (dual b)) (sign (dual b)))) :
    (Ω.addBases left right left_lt_right sign dual dual_involutive).Solution where
  word := U.word
  isReduced_word := U.isReduced_word
  word_ne_nil := U.word_ne_nil
  isReduced_subst e he := by
    obtain he | ⟨b, rfl⟩ := mem_equations_addBases_iff.1 he
    exacts [U.isReduced_subst e he, ⟨hred b, hred (dual b)⟩]
  subst_eq e he := by
    obtain he | ⟨b, rfl⟩ := mem_equations_addBases_iff.1 he
    exacts [U.subst_eq e he, heq b]

/-- A solution keeps its words when bases are added. -/
@[simp]
theorem Solution.addBases_word (U : Ω.Solution)
    (hred : ∀ b,
      FreeGroup.IsReduced (substituteVars U.word (Ω.segment (left b) (right b) (sign b))))
    (heq : ∀ b, substituteVars U.word (Ω.segment (left b) (right b) (sign b)) =
      substituteVars U.word (Ω.segment (left (dual b)) (right (dual b)) (sign (dual b)))) :
    (Solution.addBases left_lt_right dual_involutive U hred heq).word = U.word :=
  (rfl)

/- A boundary open after adding bases separates two items of one new base, or is open in `Ω`. -/
private theorem itemKind_eq_of_isOpenBoundary_addBases (P : Ω.SectionPartition)
    (h : ∀ b, ∀ k ∈ Ω.sectionItems (left b) (right b), ∀ k' ∈ Ω.sectionItems (left b) (right b),
      P.itemKind k = P.itemKind k') (k k' : Fin Ω.numItems) (hk' : (k' : ℕ) = k + 1)
    (ho : (Ω.addBases left right left_lt_right sign dual dual_involutive).IsOpenBoundary k.succ) :
    P.itemKind k' = P.itemKind k := by
  let := Fintype.ofFinite β
  obtain ⟨μ, hμ⟩ := (isOpenBoundary_iff _).1 ho
  rw [crosses_iff] at hμ
  induction μ using Fin.addCases with
  | left μ =>
    simp only [Fin.append_left] at hμ
    exact P.itemKind_eq_of_isOpenBoundary k k' hk'
      (Ω.isOpenBoundary_iff.2 ⟨μ, Ω.crosses_iff.2 hμ⟩)
  | right i =>
    simp only [Fin.append_right, Function.comp_apply, Fin.lt_def, Fin.val_succ] at hμ
    exact h ((Fintype.equivFin β).symm i) k' (by simp only [mem_sectionItems]; lia) k
      (by simp only [mem_sectionItems]; lia)

/-- A section partition of `Ω` is a section partition of `Ω` with added bases when all items of each
new base have one kind. -/
def SectionPartition.addBases (P : Ω.SectionPartition)
    (h : ∀ b, ∀ k ∈ Ω.sectionItems (left b) (right b), ∀ k' ∈ Ω.sectionItems (left b) (right b),
      P.itemKind k = P.itemKind k') :
    (Ω.addBases left right left_lt_right sign dual dual_involutive).SectionPartition where
  itemKind := P.itemKind
  itemKind_eq_of_isOpenBoundary :=
    itemKind_eq_of_isOpenBoundary_addBases left_lt_right dual_involutive P h

/-- A section partition keeps the kinds of the items when bases are added. -/
@[simp]
theorem SectionPartition.itemKind_addBases (P : Ω.SectionPartition)
    (h : ∀ b, ∀ k ∈ Ω.sectionItems (left b) (right b), ∀ k' ∈ Ω.sectionItems (left b) (right b),
      P.itemKind k = P.itemKind k') :
    (P.addBases left_lt_right (sign := sign) dual_involutive h).itemKind = P.itemKind :=
  (rfl)

end AddBases

/-! ### Example -/

/- The generalised equation `y = x` over `F(a, b)`, with `a = 0` and `b = 1`: the items `h₀ = y` and
`h₁ = x` and the dual pair of bases `[0, 1]`, `[1, 2]`. -/
private abbrev equalExample : GenEq (Fin 2) where
  numItems := 2
  numBases := 2
  left := ![0, 1]
  right := ![1, 2]
  left_lt_right := by decide
  sign := fun _ ↦ true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc ↦ absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc ↦ absurd hc (Finset.notMem_empty _)

/- The solution `y = x = ab` of `y = x`. -/
private def equalSolution : equalExample.Solution :=
  have h₀ : equalExample.segment 0 1 true = [(Sum.inl 0, true)] := equalExample.segment_succ 0 true
  have h₁ : equalExample.segment 1 2 true = [(Sum.inl 1, true)] := equalExample.segment_succ 1 true
  { word _ := [(0, true), (1, true)]
    isReduced_word _ := by simp
    word_ne_nil _ := by simp
    isReduced_subst := (forall_mem_equations _).2
      ⟨Fin.forall_fin_two.2 ⟨by simp [h₀, h₁], by simp [h₀, h₁]⟩, by simp, by simp⟩
    subst_eq := (forall_mem_equations _).2
      ⟨Fin.forall_fin_two.2 ⟨by simp [h₀, h₁], by simp [h₀, h₁]⟩, by simp, by simp⟩ }

/-- In `y = x`, cutting the item `x` in two and the solution `y = x = ab` as `ab | a | b` gives a
solution of `h'₀ = h'₁ h'₂`. It stays a solution when the dual pair of bases `[1, 3]`, `[0, 1]` is
added, identifying the pieces `a | b` with the item of `y`. -/
example : ∃ U : ((equalExample.splitItems 3 (Fin.succAboveOrderEmb 2)).addBases
    (fun s : Bool ↦ if s then 1 else 0) (fun s ↦ if s then 3 else 1) (by decide) (fun _ ↦ true)
    (fun s ↦ !s) Bool.not_not).Solution,
      U.word = ![[(0, true), (1, true)], [(0, true)], [(1, true)]] := by
  have h₀ : (equalExample.splitItems 3 (Fin.succAboveOrderEmb 2)).segment 0 1 true =
      [(Sum.inl 0, true)] := segment_succ _ 0 true
  have h₁ : (equalExample.splitItems 3 (Fin.succAboveOrderEmb 2)).segment 1 3 true =
      [(Sum.inl 1, true), (Sum.inl 2, true)] :=
    (segment_append _ (Nat.le_succ 1) (Nat.le_succ 2)).symm.trans
      (congrArg₂ (· ++ ·) (segment_succ _ 1 true) (segment_succ _ 2 true))
  have h₂ : substituteVars (![[(0, true), (1, true)], [(0, true)], [(1, true)]] :
      Fin 3 → List (Fin 2 × Bool)) [(Sum.inl 1, true), (Sum.inl 2, true)] =
        [(0, true), (1, true)] := rfl
  refine ⟨(equalSolution.splitItems (by decide) (by decide)
    ![[(0, true), (1, true)], [(0, true)], [(1, true)]] (by decide) (Fin.forall_fin_two.2
      ⟨(congrArg (substituteVars _) h₀).trans rfl, (congrArg (substituteVars _) h₁).trans h₂⟩)
    ).addBases _ _ (Bool.forall_bool.2 ⟨?_, ?_⟩) (Bool.forall_bool.2 ⟨?_, ?_⟩), rfl⟩ <;>
    simp [h₀, h₁, h₂]

/-- In `y = x` with `x` cut in two, a section partition gives both pieces the kind of `x`, and it
remains a section partition when the dual pair of bases `[1, 3]`, `[0, 1]` is added. -/
example (P : equalExample.SectionPartition) :
    ∃ P' : ((equalExample.splitItems 3 (Fin.succAboveOrderEmb 2)).addBases
      (fun s : Bool ↦ if s then 1 else 0) (fun s ↦ if s then 3 else 1) (by decide) (fun _ ↦ true)
      (fun s ↦ !s) Bool.not_not).SectionPartition,
        P'.itemKind 1 = P.itemKind 1 ∧ P'.itemKind 2 = P.itemKind 1 := by
  set Q := P.splitItems (n := 3) (bd := Fin.succAboveOrderEmb 2) (by decide) (by decide)
  -- The items `1` and `2` of the split equation are the pieces of `x`.
  have hQ (k : Fin 3) (h₁ : 1 ≤ (k : ℕ)) : Q.itemKind k = P.itemKind 1 :=
    SectionPartition.itemKind_splitItems _ _ P (k := 1) (Fin.le_def.2 h₁) k.isLt
  refine ⟨Q.addBases _ _ (Bool.forall_bool.2 ⟨fun k hk k' hk' ↦ ?_, fun k hk k' hk' ↦ ?_⟩),
    hQ 1 le_rfl, hQ 2 (by decide)⟩
  · rw [mem_sectionItems] at hk hk'
    have h : (k : ℕ) < 1 := hk.2
    have h' : (k' : ℕ) < 1 := hk'.2
    exact congrArg Q.itemKind (Fin.ext (by lia))
  · rw [mem_sectionItems] at hk hk'
    rw [hQ k hk.1, hQ k' hk'.1]

end GenEq

end TauCeti
