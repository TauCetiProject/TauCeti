/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Elementary.Lonely.Basic
-- The examples reuse the private test equations `equalItems` and `tiedExample`.
import all TauCeti.GroupTheory.FreeGroup.GenEq.Elementary.Lonely.Basic
import all TauCeti.GroupTheory.FreeGroup.GenEq.Tied

/-!
# Removal of a lonely base: solutions

Let `μ` be a lonely base of a generalised equation `Ω` and let `Ω′ = Ω.removeLonely μ h` be the
generalised equation obtained from `Ω` by the elementary transformation ET4
(Kharlampovich–Myasnikov, §5.1), which removes `μ` and `Δ(μ)` together with the section `σ(μ)`.
The *matched word* of an item `hₖ` of `μ` is `h[b(k), b(k + 1)]` when `ε(μ) = ε(Δμ)` and the
formal inverse `h[b(k + 1), b(k)]⁻¹` otherwise, where `b(i)` is the boundary of `Δ(μ)` tied to `i`
(`TauCeti.GenEq.tiedSegment`). The substitution `π` sends an item of `μ` to its matched word and
induces, when `Ω` is formally consistent, an `F(A)`-isomorphism `F_{R(Ω)} → F_{R(Ω′)}`
(`TauCeti.GenEq.removeLonelyHom`). This file transfers solutions along ET4 in both directions.

* A solution `U` of `Ω` restricts to a solution of `Ω′` (`TauCeti.GenEq.Solution.removeLonely`):
  the words of the items outside `μ` are kept. If `Ω` is formally consistent, the homomorphism
  `F_{R(Ω′)} → F(A)` of the restriction precomposed with `π` is the homomorphism of `U`
  (`TauCeti.GenEq.toHom_comp_removeLonelyHom`): the triangle in the source's definition of an
  elementary transformation commutes.
* Conversely, if `Ω` is formally consistent, the solutions of `Ω` are exactly the solutions of
  `Ω′` for which the word of the former place of `Δ(μ)` is reduced as written
  (`TauCeti.GenEq.Solution.IsReducedOnDual`, `TauCeti.GenEq.solutionEquivRemoveLonely`,
  `TauCeti.GenEq.Solution.mem_range_removeLonely_iff`). An item of `μ` then carries its matched
  word evaluated at the solution of `Ω′`, and the homomorphism of the solution of `Ω` is that of
  the solution of `Ω′` precomposed with `π`.

The source states only the forward transfer. The backward equivalence follows the treatment of
ET3 in `TauCeti.GenEq.solutionEquivRemovePair`: the remark after ET3 in §5.1 asserts that ET1–ET3
preserve the solutions themselves, which fails for ET3 unless a word is reduced as written, and
the same reducedness condition appears here. What is new for ET4 is the lifting along `π`, which
gives the items of `μ` their matched words. The condition on `Δ(μ)` is needed: after `π`, the
words of the items of `μ` may cancel with each other, and the second example at the end of the
file is a solution of `Ω′` which is not the restriction of a solution of `Ω`. The first example
treats the equation `h₀ = h₁`: removing its lonely base keeps the remaining item unconstrained,
and every solution of the result comes from a solution of `h₀ = h₁`.

Under a solution, the boundaries tied to the two end-points of an item with a one-letter word,
for instance a constant item, are adjacent
(`TauCeti.GenEq.Solution.adjacent_of_length_word_eq_one_of_isTiedTo`). So the last condition of
`TauCeti.GenEq.IsLonely`, which the source does not state, holds as soon as `Ω` has a solution
(`TauCeti.GenEq.Solution.isLonely`).

## Main definitions

* `TauCeti.GenEq.Solution.removeLonely`: the restriction of a solution of `Ω` to `Ω′`.
* `TauCeti.GenEq.Solution.IsReducedOnDual`: a solution of `Ω′` makes the word of the former place
  of `Δ(μ)` reduced as written.
* `TauCeti.GenEq.solutionEquivRemoveLonely`: for a formally consistent `Ω`, the solutions of `Ω`
  as the solutions of `Ω′` that make the word of the former place of `Δ(μ)` reduced as written.

## Main results

* `TauCeti.GenEq.toHom_comp_removeLonelyHom`,
  `TauCeti.GenEq.solutionEquivRemoveLonely_symm_apply_toHom`: the solutions of `Ω` and `Ω′`
  corresponding to each other are related by `π` at the level of coordinate groups.
* `TauCeti.GenEq.Solution.mem_range_removeLonely_iff`: the restrictions of the solutions of a
  formally consistent `Ω` are the solutions of `Ω′` that are reduced on the former place of
  `Δ(μ)`.
* `TauCeti.GenEq.Solution.isLonely`: if `Ω` has a solution, the source's conditions for ET4
  together with `Δ(μ) ≠ μ` imply that `μ` is lonely.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1, the definition of elementary transformations, the remark after ET3, and ET4.
* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005),
  §5.1, ET4.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom
open FreeGroup (substituteVars substituteVars_append)

variable {A : Type*} {Ω : GenEq A}

variable {μ : Fin Ω.numBases}

/-! ### Loneliness under a solution -/

/-- If `Ω` has a solution, a base which is not its own dual, meets no other variable base and has
all its inner boundaries tied is lonely: a constant item of it carries a word of one letter, so it
is matched with a single item of the dual base. -/
theorem Solution.isLonely (U : Ω.Solution) (hd : Ω.dual μ ≠ μ)
    (hdisj : ∀ ν, ν ≠ μ → Disjoint (Ω.baseItems ν) (Ω.baseItems μ))
    (ht : ∀ p, Ω.Crosses p μ → ∃ q, (p, μ, q) ∈ Ω.connections) : Ω.IsLonely μ where
  dual_ne := hd
  disjoint := hdisj
  tied := ht
  adjacent_of_mem_constBases _ hb _ _ _ hq hq' := U.adjacent_of_mem_constBases hb hq hq'

variable (h : Ω.IsLonely μ) (hΩ : Ω.IsFormallyConsistent)

/-! ### The forward transfer -/

/-- After substituting the words of a solution of `Ω`, both sides of every equation of `Ω` with the
constant bases of `μ` moved are reduced as written: they are equations of `Ω`, or coefficient
equations. -/
private theorem isReduced_subst_moveConstBases (U : Ω.Solution) :
    ∀ e ∈ (Ω.moveConstBases μ).equations,
      FreeGroup.IsReduced (substituteVars U.word e.1) ∧
        FreeGroup.IsReduced (substituteVars U.word e.2) := by
  intro e he
  rcases Ω.equations_moveConstBases_subset_union μ he with he | ⟨b, -, rfl⟩
  · exact U.isReduced_subst e he
  · exact Ω.isReduced_substituteVars_coeffEquation U.isReduced_word b

namespace Solution

/-- A solution of `Ω` restricts to a solution of `Ω′ = Ω.removeLonely μ h`, the generalised
equation obtained by removing a lonely base `μ` (ET4): it remains a solution when the constant
bases of `μ` are moved and when `μ` and `Δ(μ)` are removed, and the items of `μ` are then
deleted. The words of the items outside `μ` are kept. -/
noncomputable def removeLonely (U : Ω.Solution) : (Ω.removeLonely μ h).Solution :=
  ((ofMemV (Ω := Ω.moveConstBases μ) U.word U.isReduced_word U.word_ne_nil
    (isReduced_subst_moveConstBases U)
    (funext U.point_apply ▸ mem_V_moveConstBases h U.isFormallyConsistent U.point_mem_V)).removePair
      μ).deleteItems h.disjoint_baseItems_removePair

/-- The restricted solution keeps the words of the items outside `μ`. -/
@[simp]
theorem removeLonely_word (U : Ω.Solution) (k : Fin (Ω.baseItems μ)ᶜ.card) :
    (U.removeLonely h).word k = U.word ((Ω.baseItems μ)ᶜ.orderEmbOfFin rfl k) := by
  simp [removeLonely]

/-- The point of the restricted solution is the restriction of the point to the items outside
`μ`. -/
@[simp]
theorem removeLonely_point (U : Ω.Solution) :
    (U.removeLonely h).point = U.point ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl := by
  ext k
  simp

end Solution

/-- `π` maps the point of the restriction of a solution `U` of `Ω` to the point of `U`. -/
private theorem wordMap_point_removeLonely (U : Ω.Solution) :
    wordMap (MonoidHom.id (FreeGroup A)) (Ω.removeLonelyWord μ h) (U.removeLonely h).point =
      U.point := by
  rw [Solution.removeLonely_point,
    wordMap_removeLonelyWord_comp h U.isFormallyConsistent U.point_mem_V]

/-- **ET4 transfers solutions.** The homomorphism `F_{R(Ω′)} → F(A)` of the restriction of a
solution `U` of `Ω` to `Ω′ = Ω.removeLonely μ h`, precomposed with the isomorphism
`π : F_{R(Ω)} → F_{R(Ω′)}`, is the homomorphism of `U`. -/
theorem toHom_comp_removeLonelyHom (U : Ω.Solution) :
    (U.removeLonely h).toHom.comp (removeLonelyHom h hΩ) = U.toHom := by
  ext k
  have := congrFun (wordMap_point_removeLonely h U) k
  rw [wordMap_apply] at this
  rw [GHom.coe_comp, Function.comp_apply, removeLonelyHom_inr_of, Solution.toHom_mk,
    Solution.toHom_inr_of, this, Solution.point_apply]

/-! ### Solutions reduced on the former place of `Δ(μ)` -/

/-- A solution `U` of `Ω′ = Ω.removeLonely μ h` is *reduced on the dual* when it makes the word of
the segment of `Ω′` which replaces `Δ(μ)` reduced as written. For a formally consistent `Ω` these
are exactly the restrictions of the solutions of `Ω`
(`TauCeti.GenEq.Solution.mem_range_removeLonely_iff`). -/
def Solution.IsReducedOnDual (U : (Ω.removeLonely μ h).Solution) : Prop :=
  FreeGroup.IsReduced (substituteVars U.word ((Ω.removeLonely μ h).segment
    ((Ω.baseItems μ).collapse (Ω.left (Ω.dual μ)))
    ((Ω.baseItems μ).collapse (Ω.right (Ω.dual μ))) true))

/-- Being reduced on the dual, unfolded. -/
theorem Solution.isReducedOnDual_iff (U : (Ω.removeLonely μ h).Solution) :
    U.IsReducedOnDual h ↔ FreeGroup.IsReduced (substituteVars U.word ((Ω.removeLonely μ h).segment
      ((Ω.baseItems μ).collapse (Ω.left (Ω.dual μ)))
      ((Ω.baseItems μ).collapse (Ω.right (Ω.dual μ))) true)) :=
  Iff.rfl

/-- The restriction of a solution of `Ω` is reduced on the former place of `Δ(μ)`: there it carries
the word of `Δ(μ)`. -/
theorem Solution.isReducedOnDual_removeLonely (U : Ω.Solution) :
    (U.removeLonely h).IsReducedOnDual h := by
  have hw : (U.removeLonely h).word = U.word ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl :=
    funext (removeLonely_word h U)
  rw [isReducedOnDual_iff, hw, ← substituteVars_restoreWord,
    restoreWord_segment_removeLonely h le_rfl le_rfl]
  exact U.isReduced_substituteVars_segment _

/-! ### Telescoping along `μ` -/

include h hΩ in
/-- If the word of every item of `μ` is its matched word, then for every boundary `p` of `μ` the
word of `h[α(μ), p]` is the word of `h[α(Δμ), b(p)]` when `ε(μ) = ε(Δμ)`, and the formal inverse of
the word of `h[b(p), β(Δμ)]` otherwise. -/
private theorem substituteVars_segment_left_eq {W : Fin Ω.numItems → List (A × Bool)}
    (hW : ∀ k ∈ Ω.baseItems μ, W k = substituteVars W (Ω.tiedSegment μ k))
    (p : Fin (Ω.numItems + 1)) (h₁ : Ω.left μ ≤ p) (h₂ : p ≤ Ω.right μ) :
    substituteVars W (Ω.segment (Ω.left μ) p true) =
      if Ω.sign μ = Ω.sign (Ω.dual μ) then
        substituteVars W (Ω.segment (Ω.left (Ω.dual μ)) (Ω.tiedBoundary μ p) true)
      else FreeGroup.invRev
        (substituteVars W (Ω.segment (Ω.tiedBoundary μ p) (Ω.right (Ω.dual μ)) true)) := by
  refine base_induction ?_ (fun k hk ih ↦ ?_) p h₁ h₂
  · rw [tiedBoundary_left]
    split_ifs <;> simp [Ω.segment_eq_nil_of_le le_rfl]
  have hc := h.isTiedTo_tiedBoundary (left_le_castSucc_of_mem_baseItems hk)
    (k.castSucc_lt_succ.le.trans (succ_le_right_of_mem_baseItems hk))
  rw [Fin.val_castSucc] at ih
  rw [Fin.val_succ, ← Ω.segment_append (j := k) (k := (k : ℕ) + 1)
    (left_le_castSucc_of_mem_baseItems hk) (Nat.le_succ _), substituteVars_append, ih,
    Ω.segment_succ k true, FreeGroup.substituteVars_singleton_inl, hW k hk]
  split_ifs with hσ
  · rw [tiedSegment_of_sign_eq h hΩ hk hσ, ← substituteVars_append,
      Ω.segment_append hc.left_dual_le (tiedBoundary_castSucc_lt_succ_of_sign_eq h hΩ hk hσ).le]
  · rw [tiedSegment_of_sign_ne h hΩ hk hσ, segment_false, FreeGroup.substituteVars_invRev,
      ← FreeGroup.invRev_append, ← substituteVars_append,
      Ω.segment_append (tiedBoundary_succ_lt_castSucc_of_sign_ne h hΩ hk hσ).le hc.le_right_dual]

include h hΩ in
/-- If the word of every item of `μ` is its matched word and the word of `Δ(μ)` is reduced as
written, then every factor of the words of `μ` and `Δ(μ)` is reduced as written. -/
private theorem isReduced_substituteVars_segment_of_mem_pair {W : Fin Ω.numItems → List (A × Bool)}
    (hW : ∀ k ∈ Ω.baseItems μ, W k = substituteVars W (Ω.tiedSegment μ k))
    (hred : FreeGroup.IsReduced
      (substituteVars W (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)))
    {ν : Fin Ω.numBases} (hν : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))) {i j : ℕ}
    (hi : (Ω.left ν : ℕ) ≤ i) (hj : j ≤ Ω.right ν) :
    FreeGroup.IsReduced (substituteVars W (Ω.segment i j true)) := by
  rcases Finset.mem_insert.1 hν with rfl | hν
  · -- The word of `μ` is the word of `Δ(μ)` or its formal inverse.
    have hμ := substituteVars_segment_left_eq h hΩ hW _ (Ω.left_lt_right ν).le le_rfl
    rw [tiedBoundary_right] at hμ
    refine Ω.isReduced_substituteVars_segment_of_le_of_le ?_ hi hj
    split_ifs at hμ <;> rw [hμ]
    exacts [hred, hred.invRev]
  · rw [Finset.mem_singleton.1 hν] at hi hj
    exact Ω.isReduced_substituteVars_segment_of_le_of_le hred hi hj

include hΩ in
/-- Reduced words for the items of `Ω` that restrict to a solution of `Ω′`, give each item of `μ`
its matched word, and make the word of `Δ(μ)` reduced as written, make both sides of every equation
of `Ω` reduced as written. -/
private theorem isReduced_subst_lift {W : Fin Ω.numItems → List (A × Bool)}
    (hW : ∀ k ∈ Ω.baseItems μ, W k = substituteVars W (Ω.tiedSegment μ k))
    (hred : FreeGroup.IsReduced
      (substituteVars W (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)))
    (hW' : ∀ k, FreeGroup.IsReduced (W k)) (hrest : ∀ e ∈ (Ω.removeLonely μ h).equations,
      FreeGroup.IsReduced (substituteVars (W ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl) e.1) ∧
        FreeGroup.IsReduced (substituteVars (W ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl) e.2)) :
    ∀ e ∈ Ω.equations,
      FreeGroup.IsReduced (substituteVars W e.1) ∧ FreeGroup.IsReduced (substituteVars W e.2) := by
  have hseg := fun {ν} (hν : ν ∈ _) {i j} ↦
    isReduced_substituteVars_segment_of_mem_pair h hΩ hW hred (ν := ν) hν (i := i) (j := j)
  intro e he
  rcases Ω.equations_subset_union_moveConstBases μ he with he | ⟨b, -, rfl⟩
  swap
  · exact Ω.isReduced_substituteVars_coeffEquation hW' b
  rcases equations_subset_union_removeBases _ he with he | ⟨ν, hν, rfl⟩ | ⟨c, ⟨hc, hν⟩, rfl⟩
  · rcases equations_subset_union_deleteItems h.disjoint_baseItems_removePair he with
      ⟨e', he', rfl⟩ | ⟨b, -, rfl⟩
    · simpa only [restoreEquation_fst, restoreEquation_snd, substituteVars_restoreWord] using
        hrest e' he'
    · exact ((Ω.moveConstBases μ).removePair μ).isReduced_substituteVars_coeffEquation hW' b
  · rw [basicEquation_moveConstBases, basicEquation_fst, basicEquation_snd]
    exact ⟨(isReduced_substituteVars_segment_iff ..).2 (hseg hν le_rfl le_rfl),
      (isReduced_substituteVars_segment_iff ..).2 (hseg (Ω.dual_mem_pair μ ν hν) le_rfl le_rfl)⟩
  · rw [boundaryEquation_moveConstBases]
    obtain ⟨-, hp₂, hq₁, hq₂⟩ := Ω.bounds_of_mem_connections c hc
    have hν' := Ω.dual_mem_pair μ _ hν
    refine ⟨by rw [boundaryEquation_fst]; exact hseg hν le_rfl hp₂.le, ?_⟩
    by_cases hs : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1)
    · rw [Ω.boundaryEquation_snd_of_sign_eq hs]
      exact hseg hν' le_rfl hq₂.le
    · rw [Ω.boundaryEquation_snd_of_sign_ne hs, isReduced_substituteVars_segment_iff]
      exact hseg hν' hq₁.le le_rfl

/-! ### The backward transfer -/

/-- The words of the items of `Ω` obtained from a solution `U` of `Ω′` through `π`: an item of `μ`
receives its matched word evaluated at `U`, another item its word in `U`. -/
private noncomputable def liftWord (U : (Ω.removeLonely μ h).Solution) (k : Fin Ω.numItems) :
    List (A × Bool) :=
  substituteVars U.word (Ω.removeLonelyList μ h k)

section Backward

variable (U : (Ω.removeLonely μ h).Solution)

/-- The lifted word of an item outside `μ` is its word in `U`. -/
private theorem liftWord_orderEmbOfFin (j : Fin (Ω.baseItems μ)ᶜ.card) :
    liftWord h U ((Ω.baseItems μ)ᶜ.orderEmbOfFin rfl j) = U.word j := by
  rw [liftWord, removeLonelyList_of_notMem, FreeGroup.substituteVars_singleton_inl]

/-- The lifted words restrict to the words of `U`. -/
private theorem liftWord_comp : liftWord h U ∘ (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl = U.word :=
  funext (liftWord_orderEmbOfFin h U)

/-- Substituting the words of `U` into a word of `Ω′` is substituting the lifted words into that
word read in the items of `Ω`. -/
private theorem substituteVars_eq_substituteVars_restoreWord
    (w : List ((Fin (Ω.removeLonely μ h).numItems ⊕ A) × Bool)) :
    substituteVars U.word w = substituteVars (liftWord h U) (restoreWord (Ω.baseItems μ) w) := by
  rw [substituteVars_restoreWord, liftWord_comp]

/-- The lifted word of an item of `μ` is its matched word evaluated at the lifted words. -/
private theorem liftWord_of_mem {k : Fin Ω.numItems} (hk : k ∈ Ω.baseItems μ) :
    liftWord h U k = substituteVars (liftWord h U) (Ω.tiedSegment μ k) := by
  rw [liftWord, substituteVars_eq_substituteVars_restoreWord,
    restoreWord_removeLonelyList_of_mem h hk]

variable {U} in
/-- If `U` is reduced on the former place of `Δ(μ)`, the lifted words make the word of `Δ(μ)`
reduced as written. -/
private theorem isReduced_substituteVars_liftWord_dual_segment (hU : U.IsReducedOnDual h) :
    FreeGroup.IsReduced (substituteVars (liftWord h U)
      (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)) := by
  rwa [Solution.isReducedOnDual_iff, substituteVars_eq_substituteVars_restoreWord,
    restoreWord_segment_removeLonely h le_rfl le_rfl] at hU

variable {U} in
/-- The lifted words are reduced: the word of an item of `μ` is a factor of the word of `Δ(μ)` or
the formal inverse of one. -/
private theorem isReduced_liftWord (hU : U.IsReducedOnDual h) (k : Fin Ω.numItems) :
    FreeGroup.IsReduced (liftWord h U k) := by
  by_cases hk : k ∈ Ω.baseItems μ
  · rw [liftWord_of_mem h U hk]
    exact isReduced_substituteVars_tiedSegment h
      (isReduced_substituteVars_liftWord_dual_segment h hU) hk
  · obtain ⟨j, rfl⟩ : ∃ j, (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl j = k :=
      ⟨_, Finset.orderEmbOfFin_collapse hk⟩
    rw [liftWord_orderEmbOfFin]
    exact U.isReduced_word j

include hΩ in
/-- The lifted words are nonempty: the matched word of an item of `μ` is nonempty. -/
private theorem liftWord_ne_nil (k : Fin Ω.numItems) : liftWord h U k ≠ [] := by
  by_cases hk : k ∈ Ω.baseItems μ
  · refine U.substituteVars_word_ne_nil fun hnil ↦ tiedSegment_ne_nil h hΩ hk ?_
    rw [← restoreWord_removeLonelyList_of_mem h hk, hnil, restoreWord_nil]
  · obtain ⟨j, rfl⟩ : ∃ j, (Ω.baseItems μ)ᶜ.orderEmbOfFin rfl j = k :=
      ⟨_, Finset.orderEmbOfFin_collapse hk⟩
    rw [liftWord_orderEmbOfFin]
    exact U.word_ne_nil j

/-- `π` evaluated at the point of `U` is the tuple of the lifted words. -/
private theorem wordMap_removeLonelyWord_point (k : Fin Ω.numItems) :
    wordMap (MonoidHom.id (FreeGroup A)) (Ω.removeLonelyWord μ h) U.point k =
      FreeGroup.mk (liftWord h U k) := by
  rw [wordMap_removeLonelyWord_apply, MonoidHom.coe_id, Function.id_comp,
    ← EqIneqSystem.eval_eq_lift, Solution.eval_point_mk, liftWord]

include hΩ in
/-- The lifted words form the point `π(U)` of `Ω*`. -/
private theorem mem_V_liftWord :
    (fun k ↦ FreeGroup.mk (liftWord h U k)) ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem := by
  rw [← funext (wordMap_removeLonelyWord_point h U)]
  exact mapsTo_wordMap_removeLonely h hΩ _ U.point_mem_V

end Backward

include hΩ in
/-- **ET4 on solutions.** If `Ω` is formally consistent, its solutions are the solutions of
`Ω′ = Ω.removeLonely μ h` that are reduced on the former place of `Δ(μ)`. A solution of `Ω` is sent
to its restriction; conversely, an item of `μ` receives its matched word evaluated at the solution
of `Ω′`. -/
noncomputable def solutionEquivRemoveLonely :
    Ω.Solution ≃ {U : (Ω.removeLonely μ h).Solution // U.IsReducedOnDual h} where
  toFun U := ⟨U.removeLonely h, U.isReducedOnDual_removeLonely h⟩
  invFun U := Solution.ofMemV (liftWord h U.val) (isReduced_liftWord h U.property)
    (liftWord_ne_nil h hΩ U.val)
    (isReduced_subst_lift h hΩ (fun _ ↦ liftWord_of_mem h U.val)
      (isReduced_substituteVars_liftWord_dual_segment h U.property)
      (isReduced_liftWord h U.property) (by rw [liftWord_comp]; exact U.val.isReduced_subst))
    (mem_V_liftWord h hΩ U.val)
  left_inv U := Solution.point_injective <| funext fun k ↦ by
    rw [Solution.point_apply, Solution.ofMemV_word, ← wordMap_removeLonelyWord_point,
      wordMap_point_removeLonely]
  right_inv U := Subtype.ext <| Solution.ext <| funext fun j ↦ by
    rw [Solution.removeLonely_word, Solution.ofMemV_word, liftWord_orderEmbOfFin]

/-- ET4 sends a solution of `Ω` to its restriction. -/
@[simp]
theorem solutionEquivRemoveLonely_apply_coe (U : Ω.Solution) :
    (solutionEquivRemoveLonely h hΩ U).val = U.removeLonely h :=
  (rfl)

section Symm

variable (U : {U : (Ω.removeLonely μ h).Solution // U.IsReducedOnDual h})

/-- The inverse of ET4 on solutions gives an item of `Ω` the word of its image under `π`: its
matched word evaluated at `U` for an item of `μ`, its own word otherwise. -/
@[simp]
theorem solutionEquivRemoveLonely_symm_apply_word (k : Fin Ω.numItems) :
    ((solutionEquivRemoveLonely h hΩ).symm U).word k =
      substituteVars U.val.word (Ω.removeLonelyList μ h k) :=
  congrFun (Solution.ofMemV_word ..) k

/-- The inverse of ET4 on solutions sends the point of a solution `U` of `Ω′` to its image under
`π`. -/
@[simp]
theorem solutionEquivRemoveLonely_symm_apply_point :
    ((solutionEquivRemoveLonely h hΩ).symm U).point =
      wordMap (MonoidHom.id (FreeGroup A)) (Ω.removeLonelyWord μ h) U.val.point :=
  funext fun k ↦ by
    rw [Solution.point_apply, solutionEquivRemoveLonely_symm_apply_word,
      wordMap_removeLonelyWord_point, liftWord]

/-- **ET4 on solutions, backward.** The solution of `Ω` corresponding to a solution `U` of `Ω′`
that is reduced on the former place of `Δ(μ)` has as homomorphism the homomorphism
`U.toHom : F_{R(Ω′)} → F(A)` precomposed with `π : F_{R(Ω)} → F_{R(Ω′)}`. -/
theorem solutionEquivRemoveLonely_symm_apply_toHom :
    ((solutionEquivRemoveLonely h hΩ).symm U).toHom = U.val.toHom.comp (removeLonelyHom h hΩ) := by
  conv_rhs => rw [← (solutionEquivRemoveLonely h hΩ).apply_symm_apply U]
  exact (toHom_comp_removeLonelyHom h hΩ _).symm

end Symm

include hΩ in
/-- If `Ω` is formally consistent, the restrictions of the solutions of `Ω` to
`Ω′ = Ω.removeLonely μ h` are exactly the solutions of `Ω′` that are reduced on the former place
of `Δ(μ)`. -/
theorem Solution.mem_range_removeLonely_iff (U : (Ω.removeLonely μ h).Solution) :
    U ∈ Set.range (Solution.removeLonely h) ↔ U.IsReducedOnDual h := by
  refine ⟨?_, fun hU ↦ ⟨(solutionEquivRemoveLonely h hΩ).symm ⟨U, hU⟩, ?_⟩⟩
  · rintro ⟨U, rfl⟩
    exact U.isReducedOnDual_removeLonely h
  · rw [← solutionEquivRemoveLonely_apply_coe h hΩ, Equiv.apply_symm_apply]

/-! ### Examples -/

/-- Removing the lonely base of `h₀ = h₁` loses no solution: the remaining item is unconstrained,
and every solution of the result comes from a solution of `h₀ = h₁`. -/
example (U' : (equalItems.removeLonely 0 isLonely_equalItems).Solution) :
    ∃ U : equalItems.Solution, U.removeLonely isLonely_equalItems = U' := by
  have hΩ : equalItems.IsFormallyConsistent :=
    isFormallyConsistent_of_sign_eq (fun _ ↦ rfl) rfl rfl
  have h₁ : (equalItems.baseItems 0).collapse (equalItems.left (equalItems.dual 0)) = 0 := by
    rw [baseItems_equalItems, Finset.collapse_def]
    decide
  have h₂ : (equalItems.baseItems 0).collapse (equalItems.right (equalItems.dual 0)) = 0 + 1 := by
    rw [baseItems_equalItems, Finset.collapse_def]
    decide
  have hn : 0 < (equalItems.removeLonely 0 isLonely_equalItems).numItems := by
    rw [numItems_removeLonely_equalItems]
    exact one_pos
  -- The former place of `Δ(μ)` is the remaining item, whose word is reduced.
  refine (Solution.mem_range_removeLonely_iff isLonely_equalItems hΩ U').2 ?_
  rw [Solution.isReducedOnDual_iff, h₁, h₂,
    (equalItems.removeLonely 0 isLonely_equalItems).segment_succ ⟨0, hn⟩,
    FreeGroup.substituteVars_singleton_inl]
  exact U'.isReduced_word _

/-- The base `μ = [0, 2]` of `h₀h₁ = h₂h₃`, `h₀ = h₂` is lonely. -/
private theorem isLonely_tiedExample : (tiedExample true).IsLonely 0 where
  dual_ne := by decide
  disjoint ν hν := Finset.disjoint_left.2 fun k hk hk' ↦ by
    rw [mem_baseItems] at hk hk'
    revert ν k
    decide
  tied p hp := by
    obtain rfl : p = 1 := by
      have := (tiedExample true).crosses_iff.1 hp
      revert p
      decide
    exact ⟨3, by decide⟩
  adjacent_of_mem_constBases b hb := absurd hb (Finset.notMem_empty b)

/-- Removing a lonely base loses the condition that the word of its dual be reduced as written:
removing `μ` from `h₀h₁ = h₂h₃`, `h₀ = h₂` leaves two unconstrained items, and their words `a`,
`a⁻¹` form a solution of the result which is not the restriction of a solution, as `aa⁻¹` is not
reduced. -/
example : ∃ U' : ((tiedExample true).removeLonely 0 isLonely_tiedExample).Solution,
    ∀ U : (tiedExample true).Solution, U.removeLonely isLonely_tiedExample ≠ U' := by
  have hS : (tiedExample true).baseItems 0 = {0, 1} := by
    ext k
    rw [mem_baseItems]
    revert k
    decide
  have hn : 1 < ((tiedExample true).removeLonely 0 isLonely_tiedExample).numItems := by
    simp [hS, Finset.card_compl]
  have hc : ((tiedExample true).removeLonely 0 isLonely_tiedExample).constBases = ∅ :=
    Finset.eq_empty_of_forall_notMem fun b hb ↦ by
      rw [mem_constBases_deleteItems] at hb
      simp at hb
  let U' := Solution.ofNumBasesEqZero (by decide) hc
    (fun j ↦ if (j : ℕ) = 0 then [(0, true)] else [(0, false)])
    (fun j ↦ by split_ifs <;> exact .singleton) (fun j ↦ by split_ifs <;> simp)
  refine ⟨U', fun U hU ↦ ?_⟩
  have h₁ : ((tiedExample true).baseItems 0).collapse
      ((tiedExample true).left ((tiedExample true).dual 0)) = 0 := by
    rw [hS, Finset.collapse_def]
    decide
  have h₂ : ((tiedExample true).baseItems 0).collapse
      ((tiedExample true).right ((tiedExample true).dual 0)) = 0 + 1 + 1 := by
    rw [hS, Finset.collapse_def]
    decide
  -- The restriction of `U` makes the word `h₂h₃` of the former place of `Δ(μ)` reduced.
  have := U.isReducedOnDual_removeLonely isLonely_tiedExample
  rw [Solution.isReducedOnDual_iff, hU, h₁, h₂,
    ← ((tiedExample true).removeLonely 0 isLonely_tiedExample).segment_append (j := 0 + 1)
      (Nat.zero_le _) (Nat.le_succ _),
    ((tiedExample true).removeLonely 0 isLonely_tiedExample).segment_succ ⟨0, one_pos.trans hn⟩,
    ((tiedExample true).removeLonely 0 isLonely_tiedExample).segment_succ ⟨0 + 1, hn⟩,
    substituteVars_append, FreeGroup.substituteVars_singleton_inl,
    FreeGroup.substituteVars_singleton_inl] at this
  simp [U'] at this

end GenEq

end TauCeti
