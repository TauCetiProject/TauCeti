/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.CutEquation
public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.FinCases

/-!
# The cut equation of a generalised equation

To a generalised equation `Ω` Kharlampovich and Myasnikov attach a cut equation `Π_Ω` (Lemma 34):
its parameters are the closed sections of `Ω`, its pieces are the items of `Ω` together with one
base of each pair of dual variable bases, and its intervals are the partitions of the closed
sections into items, variable bases and constant bases. The interval of a partition is labelled
by its section and cut into the letters of the partition: an item `hₖ`, the representative of
the pair `{μ, Δ(μ)}` with exponent `ε(μ)`, or the letter of a constant base.

A solution `U` of `Ω` gives a solution of `Π_Ω` with respect to the values of the sections
(`TauCeti.GenEq.Solution.isSolution_cutEquation`): the items keep their words and the
representative `μ` gets the common value `U[μ] ^ ε(μ)` of the two sides of its basic equation.
Conversely, when `Ω` has no boundary connections, the items of a solution of `Π_Ω` form a solution
of `Ω` (`TauCeti.GenEq.exists_solution_of_isSolution_cutEquation`), and the items of a group
solution form a group solution of `Ω`
(`TauCeti.GenEq.mem_V_toSystem_of_isGroupSolution_cutEquation`): two partitions of a section that
differ in one place have the same value, which gives the basic and the coefficient equations.
The boundary equations are not seen by `Π_Ω`, so the hypothesis on boundary connections cannot be
dropped from these two statements
(`TauCeti.GenEq.exists_isSolution_cutEquation_not_mem_V_toSystem`).

The intervals may be restricted to the partitions of a set `T` of closed sections; the converse
statements then need the sections outside `T` to consist of free items. This is the form used for
the finite covering of the solutions of a system by cut equations, where a section of free items
need not carry a parameter.

Partitions are read as ordered sequences: a partition of `[i, j]` lists its elements from left to
right (`TauCeti.GenEq.IsTiling`), so that the label of its interval, evaluated at the pieces of a
solution, is the word of the section letter by letter.

This differs from the source in three places. The source assigns the word `U[μ]` to the
representative, which is not a solution when `ε(μ) = -1`. It states (4) without hypotheses, which
can fail for this construction in the presence of boundary connections. And it does not list
constant bases among the elements of a partition, without which (4) loses the coefficient
equations.

## Main definitions

* `TauCeti.GenEq.CutPiece`: the items and the representatives of the pairs of dual bases.
* `TauCeti.GenEq.IsTiling`: a list of items and bases covering a section without overlaps.
* `TauCeti.GenEq.cutEquation`: the cut equation `Π_Ω` on a set of closed sections.
* `TauCeti.GenEq.sectionValue`: the value of the word of a closed section at a point.
* `TauCeti.GenEq.Solution.cutPieces`: the pieces of a solution.

## Main results

* `TauCeti.GenEq.Solution.isSolution_cutEquation`: Lemma 34 (3).
* `TauCeti.GenEq.exists_solution_of_isSolution_cutEquation`: Lemma 34 (4).
* `TauCeti.GenEq.mem_V_toSystem_of_isGroupSolution_cutEquation`: Lemma 34 (4) for group
  solutions.
* `TauCeti.GenEq.exists_isSolution_cutEquation_not_mem_V_toSystem`: there is a generalised
  equation with boundary connections for which the converse fails for `Π_Ω` (on all closed
  sections), for solutions and group solutions.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.7, Lemma 34.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open FreeGroup (IsReduced substituteVars)

variable {A : Type*} (Ω : GenEq A)

/-! ### Pieces, partitions and the cut equation -/

/-- The representatives of the pairs of dual variable bases: the base of smaller index. -/
abbrev BaseRep : Type := {μ : Fin Ω.numBases // μ ≤ Ω.dual μ}

/-- The representative of the pair `{μ, Δ(μ)}`. -/
def baseRep (μ : Fin Ω.numBases) : Ω.BaseRep :=
  if h : μ ≤ Ω.dual μ then ⟨μ, h⟩ else
    ⟨Ω.dual μ, by rw [Ω.dual_involutive μ]; exact (not_le.1 h).le⟩

/-- A base no larger than its dual is the representative of its pair. -/
theorem baseRep_of_le {μ : Fin Ω.numBases} (h : μ ≤ Ω.dual μ) : Ω.baseRep μ = ⟨μ, h⟩ := by
  simp [baseRep, h]

/-- A representative is the representative of its own pair. -/
@[simp]
theorem baseRep_coe (r : Ω.BaseRep) : Ω.baseRep r = r :=
  Ω.baseRep_of_le r.property

/-- The representative of the pair `{μ, Δ(μ)}` is the smaller of the two bases. -/
theorem coe_baseRep (μ : Fin Ω.numBases) : (Ω.baseRep μ : Fin Ω.numBases) = min μ (Ω.dual μ) := by
  unfold baseRep
  rw [min_def]
  split_ifs <;> rfl

/-- Dual bases have the same representative. -/
@[simp]
theorem baseRep_dual (μ : Fin Ω.numBases) : Ω.baseRep (Ω.dual μ) = Ω.baseRep μ :=
  Subtype.ext <| by rw [coe_baseRep, coe_baseRep, Ω.dual_involutive μ, min_comm]

/-- The pieces of the cut equation of `Ω`: the items and the representatives of the pairs of
dual variable bases. -/
abbrev CutPiece : Type := Fin Ω.numItems ⊕ Ω.BaseRep

/-- The elements of a partition of a section: items, variable bases and constant bases. -/
abbrev PartElem : Type _ := Fin Ω.numItems ⊕ Fin Ω.numBases ⊕ Ω.constBases

/-- The left end point of an item, a variable base or a constant base. -/
@[simp]
def startPt : Ω.PartElem → ℕ
  | .inl k => k
  | .inr (.inl μ) => Ω.left μ
  | .inr (.inr b) => b.val.1

/-- The right end point of an item, a variable base or a constant base. -/
@[simp]
def endPt : Ω.PartElem → ℕ
  | .inl k => k + 1
  | .inr (.inl μ) => Ω.right μ
  | .inr (.inr b) => b.val.1 + 1

/-- Every item, variable base and constant base spans at least one item. -/
theorem startPt_lt_endPt : ∀ e : Ω.PartElem, Ω.startPt e < Ω.endPt e
  | .inl _ => Nat.lt_succ_self _
  | .inr (.inl μ) => Ω.left_lt_right μ
  | .inr (.inr _) => Nat.lt_succ_self _

/-- Every item, variable base and constant base ends at or before the last boundary. -/
theorem endPt_le_numItems : ∀ e : Ω.PartElem, Ω.endPt e ≤ Ω.numItems
  | .inl k => k.isLt
  | .inr (.inl μ) => Nat.lt_succ_iff.1 (Ω.right μ).isLt
  | .inr (.inr b) => b.val.1.isLt

/-- The letter of a partition element in the label of its interval: the item `hₖ`; the
representative of the pair of a variable base `μ`, with exponent `ε(μ)`; or the letter of a
constant base. -/
@[simp]
def partLetter : Ω.PartElem → (Ω.CutPiece ⊕ A) × Bool
  | .inl k => (.inl (.inl k), true)
  | .inr (.inl μ) => (.inl (.inr (Ω.baseRep μ)), Ω.sign μ)
  | .inr (.inr b) => (.inr b.val.2.1, b.val.2.2)

/-- `Ω.IsTiling i j l`: the elements of `l` cover the section `[i, j]` without overlaps, in order:
the first starts at `i`, each one starts where the previous one ends, and the last ends at `j`. -/
def IsTiling : ℕ → ℕ → List Ω.PartElem → Prop
  | i, j, [] => i = j
  | i, j, e :: l => Ω.startPt e = i ∧ IsTiling (Ω.endPt e) j l

variable {Ω}

@[simp]
theorem isTiling_nil {i j : ℕ} : Ω.IsTiling i j [] ↔ i = j :=
  Iff.rfl

@[simp]
theorem isTiling_cons {i j : ℕ} {e : Ω.PartElem} {l : List Ω.PartElem} :
    Ω.IsTiling i j (e :: l) ↔ Ω.startPt e = i ∧ Ω.IsTiling (Ω.endPt e) j l :=
  Iff.rfl

/-- A tiling of `[i, j]` has at most `j - i` elements. -/
theorem IsTiling.add_length_le {i j : ℕ} {l : List Ω.PartElem} (h : Ω.IsTiling i j l) :
    i + l.length ≤ j := by
  induction l generalizing i with
  | nil => exact (Nat.add_zero i).trans_le (isTiling_nil.1 h).le
  | cons e l ih =>
    obtain ⟨rfl, hl⟩ := isTiling_cons.1 h
    have := Ω.startPt_lt_endPt e
    have := ih hl
    simp only [List.length_cons]
    omega

/-- A section with a tiling is nonempty or a single boundary: `i ≤ j`. -/
theorem IsTiling.le {i j : ℕ} {l : List Ω.PartElem} (h : Ω.IsTiling i j l) : i ≤ j :=
  (Nat.le_add_right _ _).trans h.add_length_le

/-- Tilings of adjacent sections `[i, j]` and `[j, k]` concatenate to a tiling of `[i, k]`. -/
theorem IsTiling.append {i j k : ℕ} {l₁ l₂ : List Ω.PartElem} (h₁ : Ω.IsTiling i j l₁)
    (h₂ : Ω.IsTiling j k l₂) : Ω.IsTiling i k (l₁ ++ l₂) := by
  induction l₁ generalizing i with
  | nil => exact (isTiling_nil.1 h₁) ▸ h₂
  | cons e l ih => exact ⟨(isTiling_cons.1 h₁).1, ih (isTiling_cons.1 h₁).2⟩

/-- A tiling starting at a boundary ends at a boundary. -/
theorem IsTiling.le_numItems {i j : ℕ} {l : List Ω.PartElem} (h : Ω.IsTiling i j l)
    (hi : i ≤ Ω.numItems) : j ≤ Ω.numItems := by
  induction l generalizing i with
  | nil => exact isTiling_nil.1 h ▸ hi
  | cons e l ih => exact ih (isTiling_cons.1 h).2 (Ω.endPt_le_numItems e)

variable (Ω)

/-- The items `hᵢ, …, h_{j-1}`, as partition elements. -/
def itemTiling (i j : ℕ) : List Ω.PartElem :=
  (((List.finRange Ω.numItems).take j).drop i).map .inl

/-- The items `hᵢ, …, h_{j-1}` tile `[i, j]`. -/
theorem isTiling_itemTiling {i j : ℕ} (hij : i ≤ j) (hj : j ≤ Ω.numItems) :
    Ω.IsTiling i j (Ω.itemTiling i j) := by
  induction h : j - i generalizing i with
  | zero =>
    obtain rfl : i = j := by omega
    simp [itemTiling]
  | succ n ih =>
    have hi : i < (List.take j (List.finRange Ω.numItems)).length := by
      simp only [List.length_take, List.length_finRange]
      omega
    have hget : ((List.take j (List.finRange Ω.numItems))[i] : ℕ) = i := by simp
    rw [itemTiling, List.drop_eq_getElem_cons hi, List.map_cons, isTiling_cons]
    refine ⟨by simp only [startPt, hget], ?_⟩
    simp only [endPt, hget]
    exact ih (by omega) (by omega)

/-- The intervals of the cut equation of `Ω` on a set `T` of closed sections: the partitions of
the sections of `T`. -/
abbrev CutInterval (T : Set Ω.closedSections) : Type _ :=
  Σ s : T, {l : List Ω.PartElem // Ω.IsTiling s.val.val.1 s.val.val.2 l}

/-- A cut equation of a generalised equation has finitely many intervals: a tiling of a section
has at most as many elements as the section has items. -/
instance (T : Set Ω.closedSections) : Finite (Ω.CutInterval T) :=
  have (s : T) : Finite {l : List Ω.PartElem // Ω.IsTiling s.val.val.1 s.val.val.2 l} :=
    Set.Finite.to_subtype (s := {l | Ω.IsTiling s.val.val.1 s.val.val.2 l}) <|
      (List.finite_length_le Ω.PartElem s.val.val.2).subset fun _ hl =>
        le_trans (Nat.le_add_left _ _) (IsTiling.add_length_le hl)
  inferInstance

/-- The cut equation `Π_Ω` of a generalised equation on a set `T` of closed sections
(Kharlampovich–Myasnikov, Lemma 34): the parameters are the closed sections, the pieces are the
items and the representatives of the pairs of dual bases, and each partition of a section of `T`
is an interval, labelled by its section and cut into the letters of the partition. -/
def cutEquation (T : Set Ω.closedSections) :
    CutEquation A (Ω.CutInterval T) Ω.closedSections Ω.CutPiece where
  paramLabel σ := inr (FreeGroup.of σ.1.val)
  pieceLabel σ := σ.2.val.map Ω.partLetter

@[simp]
theorem cutEquation_paramLabel (T : Set Ω.closedSections) (σ : Ω.CutInterval T) :
    (Ω.cutEquation T).paramLabel σ = inr (FreeGroup.of σ.1.val) := (rfl)

@[simp]
theorem cutEquation_pieceLabel (T : Set Ω.closedSections) (σ : Ω.CutInterval T) :
    (Ω.cutEquation T).pieceLabel σ = σ.2.val.map Ω.partLetter := (rfl)

/-- The value at a point `h` of the word `h[i, j]` of a closed section `[i, j]`. -/
def sectionValue (h : Fin Ω.numItems → FreeGroup A) (s : Ω.closedSections) : FreeGroup A :=
  EqIneqSystem.eval h FreeGroup.of (FreeGroup.mk (Ω.segment s.val.1 s.val.2 true))

theorem sectionValue_def (h : Fin Ω.numItems → FreeGroup A) (s : Ω.closedSections) :
    Ω.sectionValue h s =
      EqIneqSystem.eval h FreeGroup.of (FreeGroup.mk (Ω.segment s.val.1 s.val.2 true)) :=
  (rfl)

/-! ### Labels of tilings -/

/-- The label of the items `hᵢ, …, h_{j-1}` is the word `h[i, j]`, an item `hₖ` read as a piece. -/
theorem map_partLetter_itemTiling (i j : ℕ) :
    (Ω.itemTiling i j).map Ω.partLetter =
      (Ω.segment i j true).map (Prod.map (Sum.map .inl id) id) := by
  simp [itemTiling, segment_true, Function.comp_def]

/-- Substituted into the label of the items `hᵢ, …, h_{j-1}`, the pieces give the substituted
word `h[i, j]`. -/
private theorem substituteVars_map_partLetter_itemTiling (α : Ω.CutPiece → List (A × Bool))
    (i j : ℕ) : substituteVars α ((Ω.itemTiling i j).map Ω.partLetter) =
      substituteVars (fun k => α (.inl k)) (Ω.segment i j true) := by
  rw [map_partLetter_itemTiling, FreeGroup.substituteVars_map]
  rfl

/-- Evaluated at values of the pieces, the label of the items `hᵢ, …, h_{j-1}` is the value of
`h[i, j]`. -/
private theorem lift_mk_map_partLetter_itemTiling (α : Ω.CutPiece → FreeGroup A) (i j : ℕ) :
    FreeGroup.lift (Sum.elim α FreeGroup.of) (FreeGroup.mk ((Ω.itemTiling i j).map Ω.partLetter)) =
      FreeGroup.lift (Sum.elim (fun k => α (.inl k)) FreeGroup.of)
        (FreeGroup.mk (Ω.segment i j true)) := by
  rw [map_partLetter_itemTiling, FreeGroup.lift_mk, FreeGroup.lift_mk, List.map_map]
  congr 2
  funext x
  rcases x with ⟨x | a, b⟩ <;> rfl

variable {Ω} in
/-- If each partition element, substituted, is the word of the items it spans, then so is every
tiling of a section. -/
private theorem substituteVars_map_partLetter_of_isTiling {α : Ω.CutPiece → List (A × Bool)}
    (hα : ∀ e, substituteVars α [Ω.partLetter e] =
      substituteVars (fun k => α (.inl k)) (Ω.segment (Ω.startPt e) (Ω.endPt e) true))
    {i j : ℕ} {l : List Ω.PartElem} (hl : Ω.IsTiling i j l) :
    substituteVars α (l.map Ω.partLetter) =
      substituteVars (fun k => α (.inl k)) (Ω.segment i j true) := by
  induction l generalizing i with
  | nil => simp [isTiling_nil.1 hl, Ω.segment_eq_nil_of_le le_rfl]
  | cons e l ih =>
    obtain ⟨rfl, hl'⟩ := isTiling_cons.1 hl
    rw [List.map_cons, FreeGroup.substituteVars_cons, ih hl', hα,
      ← FreeGroup.substituteVars_append,
      Ω.segment_append (Ω.startPt_lt_endPt e).le hl'.le]

/-! ### Solutions of `Ω` give solutions of `Π_Ω` -/

namespace Solution

variable {Ω} (U : Ω.Solution)

/-- The pieces of a solution `U` of `Ω`: an item gets its word, and the representative `μ` of a
pair of dual bases gets the word `U[μ] ^ ε(μ)` of the sides of their basic equation. -/
def cutPieces : Ω.CutPiece → List (A × Bool)
  | .inl k => U.word k
  | .inr μ => substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) (Ω.sign μ))

@[simp]
theorem cutPieces_inl (k : Fin Ω.numItems) : U.cutPieces (.inl k) = U.word k := (rfl)

@[simp]
theorem cutPieces_inr (μ : Ω.BaseRep) :
    U.cutPieces (.inr μ) = substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) (Ω.sign μ)) :=
  (rfl)

/-- The representative of the pair of a base `μ` gets the word `U[μ] ^ ε(μ)`. -/
theorem cutPieces_baseRep (μ : Fin Ω.numBases) :
    U.cutPieces (.inr (Ω.baseRep μ)) =
      substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) (Ω.sign μ)) := by
  rcases le_total μ (Ω.dual μ) with h | h
  · rw [Ω.baseRep_of_le h, cutPieces_inr]
  · have := U.subst_eq _ (Ω.basicEquation_mem_equations μ)
    rw [basicEquation_fst, basicEquation_snd] at this
    rw [← baseRep_dual, Ω.baseRep_of_le (by rwa [Ω.dual_involutive]), cutPieces_inr, this]

/-- The value of a section at the point of a solution is the word of the section. -/
theorem sectionValue_point (s : Ω.closedSections) :
    Ω.sectionValue U.point s =
      FreeGroup.mk (substituteVars U.word (Ω.segment s.val.1 s.val.2 true)) :=
  U.eval_point_mk _

/-- In a solution, a partition element, substituted, is the word of the items it spans. -/
private theorem substituteVars_cutPieces_partLetter (e : Ω.PartElem) :
    substituteVars U.cutPieces [Ω.partLetter e] =
      substituteVars U.word (Ω.segment (Ω.startPt e) (Ω.endPt e) true) := by
  rcases e with k | μ | ⟨b, hb⟩
  · simp
  · simp only [partLetter, startPt, endPt]
    cases hs : Ω.sign μ
    · rw [FreeGroup.substituteVars_singleton_inl_false, cutPieces_baseRep, hs, segment_false,
        FreeGroup.substituteVars_invRev, FreeGroup.invRev_invRev]
    · rw [FreeGroup.substituteVars_singleton_inl, cutPieces_baseRep, hs]
  · have := U.subst_eq _ (Ω.coeffEquation_mem_equations hb)
    simp only [coeffEquation_fst, coeffEquation_snd, FreeGroup.substituteVars_singleton_inl,
      FreeGroup.substituteVars_singleton_inr] at this
    simp [this]

/-- In a solution, the label of a tiling of `[i, j]` (for instance the label of an interval of
`Π_Ω`), substituted, is the word `U[i, j]`, letter by letter. -/
theorem substituteVars_cutPieces_map_partLetter {i j : ℕ} {l : List Ω.PartElem}
    (hl : Ω.IsTiling i j l) :
    substituteVars U.cutPieces (l.map Ω.partLetter) =
      substituteVars U.word (Ω.segment i j true) :=
  substituteVars_map_partLetter_of_isTiling U.substituteVars_cutPieces_partLetter hl

/-- **Kharlampovich–Myasnikov, Lemma 34 (3).** The pieces of a solution `U` of `Ω` are a solution
of the cut equation `Π_Ω`, on any set of closed sections, with respect to the values of the
sections at `U`. -/
theorem isSolution_cutEquation (T : Set Ω.closedSections) :
    (Ω.cutEquation T).IsSolution (Ω.sectionValue U.point) U.cutPieces where
  ne_nil
    | .inl k => U.word_ne_nil k
    | .inr μ => U.substituteVars_word_ne_nil <| List.ne_nil_of_length_pos <| by
        have := Ω.left_lt_right μ
        have := (Ω.right μ).is_le
        simp only [length_segment]
        omega
  isReduced
    | .inl k => U.isReduced_word k
    | .inr μ => by simpa using (U.isReduced_subst _ (Ω.basicEquation_mem_equations μ)).1
  isReduced_substituteVars σ := by
    rw [cutEquation_pieceLabel, U.substituteVars_cutPieces_map_partLetter σ.2.property]
    exact U.isReduced_substituteVars_segment_of_forall_isOpenBoundary
      (Ω.mem_closedSections.1 σ.1.val.property).isOpenBoundary
  isGroupSolution := CutEquation.isGroupSolution_mk_iff.2 fun σ => by
    rw [cutEquation_pieceLabel, U.substituteVars_cutPieces_map_partLetter σ.2.property,
      cutEquation_paramLabel, eval_inr_of, sectionValue_point]

end Solution

/-! ### Solutions of `Π_Ω` give solutions of `Ω` -/

variable {Ω} {T : Set Ω.closedSections}

/-- If the closed sections outside `T` consist of free items, the closed section of a variable
base belongs to `T`. -/
private theorem closedSectionOfBase_mem
    (hT : ∀ s ∉ T, ∀ k ∈ Ω.sectionItems s.val.1 s.val.2, Ω.IsFreeItem k) (μ : Fin Ω.numBases) :
    (⟨_, Ω.closedSectionOfBase_mem_closedSections μ⟩ : Ω.closedSections) ∈ T := by
  by_contra hs
  exact (Ω.isFreeItem_iff.1 (hT _ hs _ (Ω.baseItems_subset_sectionItems_closedSectionOfBase μ
    (Ω.left_mem_baseItems μ)))).1 μ (Ω.left_mem_baseItems μ)

/-- If the closed sections outside `T` consist of free items, the closed section of an item with a
constant base belongs to `T`. -/
private theorem closedSectionOfItem_mem
    (hT : ∀ s ∉ T, ∀ k ∈ Ω.sectionItems s.val.1 s.val.2, Ω.IsFreeItem k)
    {b : Fin Ω.numItems × (A × Bool)} (hb : b ∈ Ω.constBases) :
    (⟨_, Ω.closedSectionOfItem_mem_closedSections b.1⟩ : Ω.closedSections) ∈ T := by
  by_contra hs
  exact (Ω.isFreeItem_iff.1 (hT _ hs _ (Ω.mem_sectionItems_closedSectionOfItem b.1))).2
    (Ω.isConstantItem_iff.2 ⟨b, hb, rfl⟩)

/-- Two partitions of a section of `T` which differ in one element, the element `e` against the
items it spans, have the same value at a group solution of `Π_Ω`. -/
private theorem lift_mk_partLetter {β : Ω.closedSections → FreeGroup A}
    {α : Ω.CutPiece → FreeGroup A} (h : (Ω.cutEquation T).IsGroupSolution β α)
    {s : Ω.closedSections} (hs : s ∈ T) {e : Ω.PartElem} (h₁ : (s.val.1 : ℕ) ≤ Ω.startPt e)
    (h₂ : Ω.endPt e ≤ s.val.2) :
    FreeGroup.lift (Sum.elim α FreeGroup.of) (FreeGroup.mk [Ω.partLetter e]) =
      FreeGroup.lift (Sum.elim (fun k => α (.inl k)) FreeGroup.of)
        (FreeGroup.mk (Ω.segment (Ω.startPt e) (Ω.endPt e) true)) := by
  have hj : (s.val.2 : ℕ) ≤ Ω.numItems := Nat.lt_succ_iff.1 s.val.2.isLt
  have he := Ω.startPt_lt_endPt e
  have h₃ := CutEquation.isGroupSolution_iff_lift.1 h ⟨⟨s, hs⟩, ⟨_,
    ((Ω.isTiling_itemTiling h₁ (by omega)).append
      (isTiling_cons.2 ⟨rfl, isTiling_nil.2 rfl⟩)).append
      (Ω.isTiling_itemTiling h₂ hj)⟩⟩
  have h₄ := CutEquation.isGroupSolution_iff_lift.1 h ⟨⟨s, hs⟩, ⟨_,
    Ω.isTiling_itemTiling (h₁.trans (he.le.trans h₂)) hj⟩⟩
  simp only [cutEquation_pieceLabel, cutEquation_paramLabel, List.map_append, ← FreeGroup.mul_mk,
    map_mul, lift_mk_map_partLetter_itemTiling] at h₃ h₄
  rw [← Ω.segment_append h₁ (he.le.trans h₂), ← Ω.segment_append he.le h₂,
    ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul, ← h₃, mul_assoc] at h₄
  exact (mul_right_cancel (mul_left_cancel h₄)).symm

/-- At a group solution of `Π_Ω` on `T`, a variable base `μ` whose closed section belongs to `T`
has the value of the representative of its pair. -/
private theorem lift_mk_segment_eq {β : Ω.closedSections → FreeGroup A}
    {α : Ω.CutPiece → FreeGroup A} (h : (Ω.cutEquation T).IsGroupSolution β α)
    (hT : ∀ s ∉ T, ∀ k ∈ Ω.sectionItems s.val.1 s.val.2, Ω.IsFreeItem k) (μ : Fin Ω.numBases) :
    FreeGroup.lift (Sum.elim (fun k => α (.inl k)) FreeGroup.of)
      (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) (Ω.sign μ))) = α (.inr (Ω.baseRep μ)) := by
  have := lift_mk_partLetter h (closedSectionOfBase_mem hT μ) (e := .inr (.inl μ))
    (Ω.closedSectionOfBase_fst_le μ) (Ω.right_le_closedSectionOfBase_snd μ)
  rw [Ω.lift_mk_segment]
  simp only [startPt, endPt] at this
  rw [← this]
  cases hs : Ω.sign μ <;> simp [FreeGroup.lift_mk, hs]

/-- Lemma 34 (4) for group solutions: if `Ω` has no boundary connections and every closed section
outside `T` consists of free items, the items of a group solution of `Π_Ω` on `T` are a group
solution of `Ω`. -/
theorem mem_V_toSystem_of_isGroupSolution_cutEquation (hc : Ω.connections = ∅)
    (hT : ∀ s ∉ T, ∀ k ∈ Ω.sectionItems s.val.1 s.val.2, Ω.IsFreeItem k)
    {β : Ω.closedSections → FreeGroup A} {α : Ω.CutPiece → FreeGroup A}
    (h : (Ω.cutEquation T).IsGroupSolution β α) :
    (fun k => α (.inl k)) ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem := by
  simp only [Ω.mem_V_toSystem_iff, MonoidHom.coe_id, Function.id_comp]
  refine Ω.forall_mem_equations.2 ⟨fun μ => ?_, fun b hb => ?_, fun c hc' => ?_⟩
  · rw [basicEquation_fst, basicEquation_snd, lift_mk_segment_eq h hT,
      lift_mk_segment_eq h hT, baseRep_dual]
  · -- The constant base on `hₖ` against the item `hₖ` in the closed section of `hₖ`.
    have := lift_mk_partLetter h (closedSectionOfItem_mem hT hb) (e := .inr (.inr ⟨b, hb⟩))
      (Ω.closedSectionOfItem_fst_le b.1) (Ω.succ_le_closedSectionOfItem_snd b.1)
    have hseg := Ω.segment_succ b.1 true
    simp only [startPt, endPt] at this
    rw [hseg] at this
    simpa [FreeGroup.lift_mk] using this.symm
  · simp [hc] at hc'

/-- At a solution of `Π_Ω` on `T`, the word `h[α(μ), β(μ)]` of a variable base whose closed section
belongs to `T` is reduced as written: it lies in the partition of that section into items. -/
private theorem isReduced_substituteVars_segment_of_isSolution {β : Ω.closedSections → FreeGroup A}
    {α : Ω.CutPiece → List (A × Bool)} (h : (Ω.cutEquation T).IsSolution β α)
    (hT : ∀ s ∉ T, ∀ k ∈ Ω.sectionItems s.val.1 s.val.2, Ω.IsFreeItem k) (μ : Fin Ω.numBases) :
    IsReduced (substituteVars (fun k => α (.inl k)) (Ω.segment (Ω.left μ) (Ω.right μ) true)) := by
  have h₁ := Ω.closedSectionOfBase_fst_le μ
  have h₂ := Ω.right_le_closedSectionOfBase_snd μ
  have h' := h.isReduced_substituteVars ⟨⟨_, closedSectionOfBase_mem hT μ⟩, ⟨_,
    Ω.isTiling_itemTiling (h₁.trans ((Ω.left_lt_right μ).le.trans h₂))
      (Nat.lt_succ_iff.1 (Ω.closedSectionOfBase μ).2.isLt)⟩⟩
  rw [cutEquation_pieceLabel, substituteVars_map_partLetter_itemTiling] at h'
  exact Ω.isReduced_substituteVars_segment_of_le_of_le h' h₁ h₂

/-- **Kharlampovich–Myasnikov, Lemma 34 (4).** If `Ω` has no boundary connections and every
closed section outside `T` consists of free items, the items of a solution of `Π_Ω` on `T` form a
solution of `Ω`. -/
theorem exists_solution_of_isSolution_cutEquation (hc : Ω.connections = ∅)
    (hT : ∀ s ∉ T, ∀ k ∈ Ω.sectionItems s.val.1 s.val.2, Ω.IsFreeItem k)
    {β : Ω.closedSections → FreeGroup A} {α : Ω.CutPiece → List (A × Bool)}
    (h : (Ω.cutEquation T).IsSolution β α) :
    ∃ U : Ω.Solution, U.word = fun k => α (.inl k) := by
  refine ⟨Solution.ofMemV (fun k => α (.inl k)) (fun k => h.isReduced _) (fun k => h.ne_nil _)
    (Ω.forall_mem_equations.2 ⟨fun μ => ?_, fun b _ => ?_, fun c hc' => ?_⟩)
    (mem_V_toSystem_of_isGroupSolution_cutEquation hc hT h.isGroupSolution),
    Solution.ofMemV_word ..⟩
  · rw [basicEquation_fst, basicEquation_snd]
    exact ⟨(Ω.isReduced_substituteVars_segment_iff _ _ _ _).2
      (isReduced_substituteVars_segment_of_isSolution h hT μ),
      (Ω.isReduced_substituteVars_segment_iff _ _ _ _).2
      (isReduced_substituteVars_segment_of_isSolution h hT (Ω.dual μ))⟩
  · simp [h.isReduced]
  · simp [hc] at hc'

/-! ### Boundary connections -/

/-- Over `F(a)`: four items, the dual bases `μ = [0, 2]` and `Δ(μ) = [2, 4]` with positive signs,
and the boundary connection `(1, μ, 3)` with its dual. -/
private def boundaryExample : GenEq Unit where
  numItems := 4
  numBases := 2
  left := ![0, 2]
  right := ![2, 4]
  left_lt_right := by decide
  sign _ := true
  dual := Fin.rev
  dual_involutive := Fin.rev_rev
  constBases := ∅
  connections := {(1, 0, 3), (3, 1, 1)}
  bounds_of_mem_connections := by decide
  dual_mem_connections := by decide

/-- The pieces `(a, a², a², a)` of the items and `a³` of the representative of `{μ, Δ(μ)}`. -/
private def boundaryExamplePieces : boundaryExample.CutPiece → List (Unit × Bool)
  | .inl k => List.replicate (![0, 1, 1, 0] k + 1) ((), true)
  | .inr _ => List.replicate 3 ((), true)

/-- The pieces of the example are positive powers of `a`. -/
private theorem mem_boundaryExamplePieces {m : boundaryExample.CutPiece} {x : Unit × Bool}
    (hx : x ∈ boundaryExamplePieces m) : x = ((), true) := by
  rcases m with k | r <;> exact List.eq_of_mem_replicate hx

/-- Each partition element of the example, substituted, is the word of the items it spans. -/
private theorem substituteVars_boundaryExamplePieces_partLetter (e : boundaryExample.PartElem) :
    substituteVars boundaryExamplePieces [boundaryExample.partLetter e] =
      substituteVars (fun k => boundaryExamplePieces (.inl k))
        (boundaryExample.segment (boundaryExample.startPt e) (boundaryExample.endPt e) true) := by
  rcases e with k | μ | ⟨b, hb⟩
  · simp
  · fin_cases μ <;> (rw [segment_true]; decide)
  · exact (Finset.notMem_empty b hb).elim

/-- Property (4) of Lemma 34 can fail for the cut equation `Π_Ω` constructed here (the construction
of the source's proof) when `Ω` has boundary connections, since `Π_Ω` does not see the boundary
equations. For example, over `F(a)`, take four items, the dual bases `μ = [0, 2]` and
`Δ(μ) = [2, 4]` with positive signs, and the boundary connection `(1, μ, 3)` with its dual. The
items `(a, a², a², a)` and the piece `a³` of `μ` are a solution of `Π_Ω`, but the items are not
even a group solution of `Ω`, since the boundary equation `h₀ = h₂` fails. In particular they are
the words of no solution of `Ω` (`TauCeti.GenEq.Solution.point_mem_V`). -/
theorem exists_isSolution_cutEquation_not_mem_V_toSystem :
    ∃ (Ω : GenEq Unit) (β : Ω.closedSections → FreeGroup Unit)
      (α : Ω.CutPiece → List (Unit × Bool)), (Ω.cutEquation Set.univ).IsSolution β α ∧
        (fun k => FreeGroup.mk (α (.inl k))) ∉ V (MonoidHom.id (FreeGroup Unit)) Ω.toSystem := by
  have hα := substituteVars_boundaryExamplePieces_partLetter
  -- Every word made of pieces is a power of `a`, hence reduced.
  have hpos (l : List (Unit × Bool)) (hl : ∀ x ∈ l, x = ((), true)) : IsReduced l :=
    List.eq_replicate_of_mem hl ▸ FreeGroup.isReduced_replicate _ _
  refine ⟨boundaryExample,
    boundaryExample.sectionValue fun k => FreeGroup.mk (boundaryExamplePieces (.inl k)),
    boundaryExamplePieces,
    ⟨fun m => ?_, fun m => hpos _ fun _ => mem_boundaryExamplePieces, fun σ => ?_,
      CutEquation.isGroupSolution_mk_iff.2 fun σ => ?_⟩, fun hV => ?_⟩
  · rcases m with k | _ <;> exact List.cons_ne_nil _ _
  · rw [cutEquation_pieceLabel, substituteVars_map_partLetter_of_isTiling hα σ.2.property,
      segment_true, FreeGroup.substituteVars_map_inl]
    refine hpos _ fun x hx => ?_
    obtain ⟨k, -, hx⟩ := List.mem_flatMap.1 hx
    exact mem_boundaryExamplePieces hx
  · rw [cutEquation_pieceLabel, substituteVars_map_partLetter_of_isTiling hα σ.2.property,
      cutEquation_paramLabel, eval_inr_of, sectionValue_def, EqIneqSystem.eval_eq_lift,
      FreeGroup.mk_substituteVars]
  · -- The boundary equation `h₀ = h₂` of the connection `(1, μ, 3)` reads `a = a²`.
    have := boundaryExample.mem_V_toSystem_iff.1 hV _
      (boundaryExample.boundaryEquation_mem_equations (c := ((1 : Fin 5), (0 : Fin 2), (3 : Fin 5)))
        (by decide))
    rw [boundaryExample.boundaryEquation_snd_of_sign_eq rfl, boundaryEquation_fst,
      MonoidHom.coe_id, Function.id_comp, ← FreeGroup.mk_substituteVars,
      ← FreeGroup.mk_substituteVars, segment_true, segment_true] at this
    revert this
    decide

/-! ### The cut equation of one item -/

/-- The generalised equation with one item and no bases. -/
private def oneItem : GenEq A where
  numItems := 1
  numBases := 0
  left := Fin.elim0
  right := Fin.elim0
  left_lt_right μ := μ.elim0
  sign := Fin.elim0
  dual := Fin.elim0
  dual_involutive μ := μ.elim0
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := by simp
  dual_mem_connections := by simp

/-- The generalised equation with one item and no bases has the cut equation `m = x`: its only
closed section is `[0, 1]`, which has the single partition `(h₀)`. -/
example (σ : (oneItem (A := A)).CutInterval Set.univ) :
    (oneItem.cutEquation Set.univ).pieceLabel σ = [(.inl (.inl ⟨0, Nat.one_pos⟩), true)] := by
  rcases σ with ⟨⟨⟨⟨i, j⟩, hs⟩, -⟩, l, hl⟩
  have hij := (oneItem.mem_closedSections.1 hs).lt
  have hn : (oneItem (A := A)).numItems = 1 := rfl
  dsimp only at hl hij
  rcases l with _ | ⟨e, _ | ⟨e', l⟩⟩
  · exact absurd (Fin.ext (isTiling_nil.1 hl)) hij.ne
  · rcases e with k | μ | ⟨b, hb⟩
    · obtain rfl : k = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.1 k.isLt)
      rfl
    · exact μ.elim0
    · exact (Finset.notMem_empty b hb).elim
  · have := hl.add_length_le
    have := j.isLt
    simp only [List.length_cons] at *
    omega

end GenEq

end TauCeti
