/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Order.SuccPred.Int
public import TauCeti.GroupTheory.InfWord.Mul
public import TauCeti.Order.SuccPred.Prod
import TauCeti.Order.SuccPred.Iterate

/-!
# Failure of Stallings' pregroup axiom (P5) on reduced infinite words

Over a discretely ordered non-Archimedean abelian group `Λ`, where there exists `t : Λ` exceeding
every finite multiple `n • Order.succ 0` of the least positive element (such as `t = toLex (1, 0)`
in `ℤ ×ₗ ℤ`), Stallings' fifth pregroup axiom (P5) fails on the set `R(Λ, X)` of all reduced
`Λ`-words (`TauCeti.InfWord.not_pregroup_P5`): there exist reduced words `u, v, w, z` such that
`u ∗ v`, `v ∗ w`, and `w ∗ z` are all defined, while neither `(u ∗ v) ∗ w` nor `v ∗ (w ∗ z)` is
defined. Thus axioms (P1)–(P4) alone do not justify a universal-group normal form without proving
(P5) on a chosen subset.

We prove the general statement for an arbitrary discretely ordered non-Archimedean abelian group `Λ`
and nonempty alphabet `X` (using a single letter `a : X`), and instantiate it concretely on
`Λ = ℤ ×ₗ ℤ` and `X = Fin 2` (`TauCeti.InfWord.not_pregroup_P5_intLex`).

## Main results

* `TauCeti.InfWord.not_pregroup_P5`: failure of Stallings' pregroup axiom (P5) on `R(Λ, X)`.
* `TauCeti.InfWord.not_pregroup_P5_intLex`: concrete counterexample on `R(ℤ ×ₗ ℤ, Fin 2)`.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §2.2 and §3.1–§3.2.
-/

public section

namespace TauCeti

namespace InfWord

section General

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ]

private noncomputable def finPrefixWord (t : Λ) (x y : X × Bool) : InfWord Λ X :=
  open Classical in
  ofFun t fun β => if β ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) then x else y

omit [IsOrderedAddMonoid Λ] in
private theorem letter_finPrefixWord_of_pos_of_le {t β : Λ} (x y : X × Bool)
    (h0 : 0 < β) (hβ : β ≤ t) :
    (finPrefixWord t x y).letter β =
      open Classical in
      some (if β ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) then x else y) := by
  classical
  exact letter_ofFun_of_pos_of_le _ h0 hβ

private theorem isReduced_finPrefixWord (t : Λ) (x y : X × Bool) :
    (finPrefixWord t x y).IsReduced := by
  classical
  refine isReduced_ofFun_iff.2 fun β h0 _ => ?_
  have hmem : (Order.succ β ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ)) ↔
      (β ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨n, hn⟩
      dsimp only at hn
      cases n with
      | zero =>
        rw [zero_nsmul, Order.succ_eq_add_succ_zero] at hn
        exact ((add_pos_of_pos_of_nonneg h0 (Order.le_succ 0)).ne hn).elim
      | succ k =>
        rw [Order.succ_eq_add_succ_zero β, succ_nsmul, add_left_inj] at hn
        exact ⟨k, hn⟩
    · rintro ⟨n, hn⟩
      dsimp only at hn
      exact ⟨n + 1, by dsimp only; rw [succ_nsmul, hn, ← Order.succ_eq_add_succ_zero]⟩
  simp only [hmem]
  split_ifs
  · rcases x with ⟨a, s⟩; cases s <;> simp [Prod.map]
  · rcases y with ⟨b, s⟩; cases s <;> simp [Prod.map]

private theorem not_exists_isMul_inv_ofFun_const_finPrefixWord {t : Λ}
    (ht : ∀ n : ℕ, n • Order.succ 0 < t) {x y : X × Bool} (hxy : x ≠ y) :
    ¬∃ w, IsMul (ofFun t fun _ => x)⁻¹ (finPrefixWord t x y) w := by
  classical
  rw [exists_isMul_inv_left_iff (isReduced_ofFun_const t x) (isReduced_finPrefixWord t x y)]
  rintro ⟨δ, ⟨hδ0, hδ1, -, htake⟩, hmax⟩
  have ht0 : 0 < t := by simpa using ht 0
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_self_of_lt ht0
  have hle_δ : ∀ n : ℕ, n • Order.succ 0 ≤ δ := fun n => by
    have hn0 : 0 ≤ n • Order.succ (0 : Λ) := by
      rw [← Order.succ_iterate_zero]
      exact Order.le_succ_iterate n 0
    refine hmax ⟨hn0, ?_, ?_, take_eq_take_iff_forall_letter_eq.2 fun γ hγ => ?_⟩
    · rw [length_ofFun, max_eq_left ht0.le]; exact (ht n).le
    · rw [finPrefixWord, length_ofFun, max_eq_left ht0.le]; exact (ht n).le
    · by_cases hγ0 : 0 < γ
      · have hγm : γ ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) := by
          by_contra hne
          rw [Set.mem_range, not_exists] at hne
          have hle := Order.succ_iterate_le_of_forall_ne (a := (0 : Λ)) (b := γ) hγ0.le
            (n := n + 1) fun k _ hk => hne k (by simpa using hk)
          rw [Order.succ_iterate_zero, succ_nsmul, ← Order.succ_eq_add_succ_zero] at hle
          exact (Order.lt_succ_self_of_lt (ht n)).not_ge (hle.trans hγ)
        have hγt : γ ≤ t := hγ.trans (ht n).le
        rw [letter_ofFun_of_pos_of_le (fun _ => x) hγ0 hγt,
          letter_finPrefixWord_of_pos_of_le x y hγ0 hγt]
        simp [hγm]
      · rw [letter_eq_none_of_not_pos hγ0, letter_eq_none_of_not_pos hγ0]
  have hδpos : 0 < δ := h01.trans_le (by simpa [one_nsmul] using hle_δ 1)
  have hδnot : δ ∉ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) := by
    rintro ⟨k, rfl⟩
    have hlt : k • Order.succ (0 : Λ) < (k + 1) • Order.succ 0 := by
      rw [succ_nsmul]
      exact lt_add_of_pos_right _ h01
    exact hlt.not_ge (hle_δ (k + 1))
  have hδt : δ ≤ t := by rwa [length_ofFun, max_eq_left ht0.le] at hδ1
  have hletter := take_eq_take_iff_forall_letter_eq.1 htake δ le_rfl
  rw [letter_ofFun_of_pos_of_le (fun _ => x) hδpos hδt,
    letter_finPrefixWord_of_pos_of_le x y hδpos hδt] at hletter
  simp only [hδnot, ↓reduceIte, Option.some.injEq] at hletter
  exact hxy hletter

/-- Stallings' fifth pregroup axiom (P5) fails on the set of all reduced `Λ`-words whenever `Λ` is
non-Archimedean and `X` is nonempty: there exist reduced words `u, v, w, z` such that `u ∗ v`,
`v ∗ w`, and `w ∗ z` are all defined, while neither `(u ∗ v) ∗ w` nor `v ∗ (w ∗ z)` is defined. -/
theorem not_pregroup_P5 {t : Λ} (ht : ∀ n : ℕ, n • Order.succ 0 < t) (a : X) :
    ∃ u v w z : InfWord Λ X,
      u.IsReduced ∧ v.IsReduced ∧ w.IsReduced ∧ z.IsReduced ∧
      (u.mul v).Dom ∧ (v.mul w).Dom ∧ (w.mul z).Dom ∧
      ¬((u.mul v).bind (·.mul w)).Dom ∧ ¬((w.mul z).bind (v.mul ·)).Dom := by
  classical
  have ht0 : 0 < t := by simpa using ht 0
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_self_of_lt ht0
  have h1t : Order.succ 0 ≤ t := Order.succ_le_of_lt ht0
  set p : InfWord Λ X := ofFun t fun _ => (a, true)
  set q : InfWord Λ X := finPrefixWord t (a, true) (a, false)
  set q' : InfWord Λ X := finPrefixWord t (a, false) (a, true)
  have hp : p.IsReduced := isReduced_ofFun_const t _
  have hq : q.IsReduced := isReduced_finPrefixWord t _ _
  have hq' : q'.IsReduced := isReduced_finPrefixWord t _ _
  have hmem1 : Order.succ (0 : Λ) ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) := ⟨1, one_nsmul _⟩
  have hu : (q⁻¹ ++ p⁻¹).IsReduced := by
    refine isReduced_append_iff.2 ⟨hq.inv, hp.inv, fun _ _ => ?_⟩
    rw [letter_inv_succ_zero, length_inv, letter_inv_length, length_ofFun, max_eq_left ht0.le,
      letter_ofFun_of_pos_of_le (fun _ => (a, true)) ht0 le_rfl,
      letter_finPrefixWord_of_pos_of_le (a, true) (a, false) h01 h1t]
    simp [hmem1, Prod.map]
  have hz : (p⁻¹ ++ q').IsReduced := by
    refine isReduced_append_iff.2 ⟨hp.inv, hq', fun _ _ => ?_⟩
    rw [length_inv, letter_inv_length, letter_ofFun_of_pos_of_le (fun _ => (a, true)) h01 h1t,
      letter_finPrefixWord_of_pos_of_le (a, false) (a, true) h01 h1t]
    simp [hmem1, Prod.map]
  have huv : IsMul (q⁻¹ ++ p⁻¹) p q⁻¹ := by
    simpa using (isMul_append_inv_append_iff hu (by simpa using hp)).2 (isMul_empty_right hq.inv)
  have hvw : IsMul p p (p ++ p) := by
    refine isMul_append ?_
    rw [ofFun_const_append_ofFun_const _ ht0.le ht0.le]
    exact isReduced_ofFun_const (t + t) (a, true)
  have hwz : IsMul p (p⁻¹ ++ q') q' := by
    simpa using (isMul_append_inv_append_iff' (by simpa using hp) hz).2 (isMul_empty_left hq')
  refine ⟨q⁻¹ ++ p⁻¹, p, p, p⁻¹ ++ q', hu, hp, hp, hz, mul_dom_iff.2 ⟨_, huv⟩,
    mul_dom_iff.2 ⟨_, hvw⟩, mul_dom_iff.2 ⟨_, hwz⟩, ?_, ?_⟩
  · simp only [mul_eq_some_iff.2 huv, Part.bind_dom, Part.get_some, mul_dom_iff]
    rintro ⟨-, r, hr⟩
    exact not_exists_isMul_inv_ofFun_const_finPrefixWord ht
      (x := (a, true)) (y := (a, false)) (by simp) ⟨r⁻¹, by simpa using hr.inv⟩
  · simp only [mul_eq_some_iff.2 hwz, Part.bind_dom, Part.get_some, mul_dom_iff]
    rintro ⟨-, r, hr⟩
    have hpinv : p = (ofFun t fun _ => (a, false))⁻¹ := by
      rw [inv_ofFun]
      exact ofFun_congr fun _ _ _ => by simp [Prod.map]
    rw [hpinv] at hr
    exact not_exists_isMul_inv_ofFun_const_finPrefixWord ht (by simp) ⟨r, hr⟩

end General

/-- Concrete check of Stallings' pregroup axiom (P5) failing on `R(ℤ ×ₗ ℤ, Fin 2)`. -/
theorem not_pregroup_P5_intLex :
    ∃ u v w z : InfWord (ℤ ×ₗ ℤ) (Fin 2),
      u.IsReduced ∧ v.IsReduced ∧ w.IsReduced ∧ z.IsReduced ∧
      (u.mul v).Dom ∧ (v.mul w).Dom ∧ (w.mul z).Dom ∧
      ¬((u.mul v).bind (·.mul w)).Dom ∧ ¬((w.mul z).bind (v.mul ·)).Dom := by
  refine not_pregroup_P5 (t := toLex ((1 : ℤ), (0 : ℤ)))
    (fun n => Prod.Lex.lt_iff.2 (.inl ?_)) (0 : Fin 2)
  change (ofLex (n • Order.succ (0 : ℤ ×ₗ ℤ))).1 < 1
  have hfst : (ofLex (n • Order.succ (0 : ℤ ×ₗ ℤ))).1 = 0 := by
    induction n with
    | zero => simp
    | succ k ih => rw [succ_nsmul, ofLex_add, Prod.fst_add, ih, Prod.Lex.ofLex_succ]; simp
  rw [hfst]
  exact zero_lt_one

end InfWord

end TauCeti
