/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Order.SuccPred.Int
public import TauCeti.GroupTheory.InfWord.FreeGroup
public import TauCeti.Order.SuccPred.Prod

/-!
# Non-Archimedean checks and counterexamples for infinite words

Over a discretely ordered non-Archimedean abelian group `Λ`, where there exists `t : Λ` exceeding
every finite multiple `n • Order.succ 0` of the least positive element (such as `t = toLex (1, 0)`
in `ℤ ×ₗ ℤ`), the partial multiplication `∗` on reduced `Λ`-words behaves strictly differently from
the Archimedean case `Λ = ℤ`:

* Constant words multiply cleanly: `a^t ∗ a = a^{t+1}` (`TauCeti.InfWord.at_mul_a`) and
  `|a^t ∗ b| = t + 1` (`TauCeti.InfWord.at_mul_b`, `TauCeti.InfWord.length_at_mul_b`).
* `∗` is genuinely partial (`TauCeti.InfWord.undefined_product`): letting `v` be the reduced word
  on `[1, t]` with `a` at the finite positions `1, 2, 3, …` and `b` elsewhere, the common initial
  segments of `a^t` and `v` are `{0, 1, 2, …}`, which has no greatest element, so `(a^t)⁻¹ ∗ v` is
  undefined and `R(Λ, X)` is not a group.
* Stallings' fifth pregroup axiom (P5) fails on `R(Λ, X)` (`TauCeti.InfWord.not_pregroup_P5`), so
  axioms (P1)–(P4) alone do not justify a universal-group normal form without proving (P5) on a
  chosen subset.
* `CDR(Λ, X)` is a strict subset of the reduced words (`TauCeti.InfWord.exists_isReduced_notMem_CDR`
  and `TauCeti.InfWord.archimedeanPrefixWord_notMem_CDR`).

All general statements are proved for an arbitrary discretely ordered abelian group `Λ` with a
non-Archimedean element `t`, and then concretely instantiated on `Λ = ℤ ×ₗ ℤ` and `X = Fin 2`.

## Main definitions

* `TauCeti.InfWord.archimedeanPrefixWord`: the reduced `Λ`-word on `[1, t]` equal to `x` at the
  finite positions `(n + 1) • Order.succ 0` and to `y` elsewhere.

## Main results

* `TauCeti.InfWord.at_mul_a`, `TauCeti.InfWord.at_mul_b`, `TauCeti.InfWord.length_at_mul_b`:
  `a^t ∗ a = a^{t+1}` and `|a^t ∗ b| = t + 1`.
* `TauCeti.InfWord.undefined_product`: `(a^t)⁻¹ ∗ v` is undefined for the non-Archimedean word `v`.
* `TauCeti.InfWord.not_pregroup_P5`: failure of Stallings' pregroup axiom (P5) on `R(Λ, X)`.
* `TauCeti.InfWord.exists_isReduced_notMem_CDR`: existence of reduced words outside `CDR Λ X`.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.1–§3.2.
-/

public section

namespace TauCeti

namespace InfWord

section General

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ]

/-! ### Finite multiples of `Order.succ 0` -/

private theorem exists_eq_succ_nsmul_of_pos_le_nsmul {β : Λ} {n : ℕ} (h0 : 0 < β)
    (hle : β ≤ n • Order.succ 0) : ∃ k : ℕ, β = (k + 1) • Order.succ 0 := by
  induction n with
  | zero =>
    simp only [zero_nsmul] at hle
    exact (h0.not_ge hle).elim
  | succ n ih =>
    rw [succ_nsmul, ← Order.succ_eq_add_succ_zero] at hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact ⟨n, by rw [Order.succ_eq_add_succ_zero, ← succ_nsmul]⟩
    · exact ih (Order.le_of_lt_succ hlt)

private theorem nsmul_succ_zero_lt_of_forall_ne {β : Λ} (h0 : 0 < β)
    (hne : ∀ k : ℕ, β ≠ (k + 1) • Order.succ 0) (n : ℕ) : n • Order.succ 0 < β := by
  by_contra! hle
  obtain ⟨k, rfl⟩ := exists_eq_succ_nsmul_of_pos_le_nsmul h0 hle
  exact hne k rfl

private theorem exists_succ_eq_succ_nsmul_iff {β : Λ} (h0 : 0 < β) :
    (∃ n : ℕ, Order.succ β = (n + 1) • Order.succ 0) ↔
      ∃ n : ℕ, β = (n + 1) • Order.succ 0 := by
  constructor
  · rintro ⟨n, hn⟩
    rw [Order.succ_eq_add_succ_zero, succ_nsmul, add_left_inj] at hn
    cases n with
    | zero =>
      simp only [zero_nsmul] at hn
      exact (h0.ne' hn).elim
    | succ k => exact ⟨k, hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, by rw [Order.succ_eq_add_succ_zero, ← succ_nsmul]⟩

/-! ### Products of `a^t` with single letters -/

/-- For `0 < t`, `a^t ∗ a = a^{t+1}` as a partial product of `Λ`-words. -/
theorem at_mul_a {t : Λ} (ht : 0 < t) (a : X) :
    (ofFun t fun _ => (a, true)).mul (ofFun (Order.succ 0) fun _ => (a, true)) =
      Part.some (ofFun (Order.succ t) fun _ => (a, true)) := by
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_self_of_lt ht
  have happ : (ofFun t fun _ => (a, true)) ++ (ofFun (Order.succ 0) fun _ => (a, true)) =
      ofFun (Order.succ t) fun _ => (a, true) := by
    rw [ofFun_const_append_ofFun_const _ ht.le h01.le, ← Order.succ_eq_add_succ_zero]
  rw [← happ]
  exact mul_eq_some_append (happ ▸ isReduced_ofFun_const (Order.succ t) (a, true))

/-- For `0 < t`, the concatenation `a^t ++ b` is reduced, so `a^t ∗ b` is defined and equals
`a^t ++ b`. -/
theorem at_mul_b {t : Λ} (ht : 0 < t) (a b : X) :
    (ofFun t fun _ => (a, true)).mul (ofFun (Order.succ 0) fun _ => (b, true)) =
      Part.some ((ofFun t fun _ => (a, true)) ++ (ofFun (Order.succ 0) fun _ => (b, true))) := by
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_self_of_lt ht
  refine mul_eq_some_append (isReduced_append_iff.2 ⟨isReduced_ofFun_const t _,
    isReduced_ofFun_const (Order.succ 0) _, fun _ _ => ?_⟩)
  rw [length_ofFun, max_eq_left ht.le, letter_ofFun_of_pos_of_le (fun _ => (b, true)) h01 le_rfl,
    letter_ofFun_of_pos_of_le (fun _ => (a, true)) ht le_rfl]
  simp [Prod.map]

/-- For `0 < t`, the length of `a^t ++ b` (which equals `a^t ∗ b`) is `Order.succ t`. -/
theorem length_at_mul_b {t : Λ} (ht : 0 < t) (a b : X) :
    ((ofFun t fun _ => (a, true)) ++ (ofFun (Order.succ 0) fun _ => (b, true))).length =
      Order.succ t := by
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_self_of_lt ht
  rw [length_append, length_ofFun, length_ofFun, max_eq_left ht.le, max_eq_left h01.le,
    ← Order.succ_eq_add_succ_zero]

/-- For `0 < t`, if `w` is the product `a^t ∗ b`, then `|w| = Order.succ t`. -/
theorem length_of_isMul_at_b {t : Λ} (ht : 0 < t) {a b : X} {w : InfWord Λ X}
    (hw : IsMul (ofFun t fun _ => (a, true)) (ofFun (Order.succ 0) fun _ => (b, true)) w) :
    w.length = Order.succ t := by
  obtain rfl := hw.unique (mul_eq_some_iff.1 (at_mul_b ht a b))
  exact length_at_mul_b ht a b

/-! ### The non-Archimedean prefix word and undefined products -/

/-- The `Λ`-word of length `t` with letter `x` at the finite positions `(n + 1) • Order.succ 0`
and letter `y` at all other positions of `[1, t]`. -/
noncomputable def archimedeanPrefixWord (t : Λ) (x y : X × Bool) : InfWord Λ X :=
  ofFun t fun β => by
    classical
    exact if ∃ n : ℕ, β = (n + 1) • Order.succ 0 then x else y

/-- `archimedeanPrefixWord t x y` is always reduced, because the finite positions
`(n + 1) • Order.succ 0` are invariant under `Order.succ` on positive elements. -/
theorem isReduced_archimedeanPrefixWord (t : Λ) (x y : X × Bool) :
    (archimedeanPrefixWord t x y).IsReduced := by
  rw [archimedeanPrefixWord, isReduced_ofFun_iff]
  intro β h0 _
  classical
  simp only [exists_succ_eq_succ_nsmul_iff h0]
  split_ifs
  · rcases x with ⟨a, s⟩; cases s <;> simp [Prod.map]
  · rcases y with ⟨b, s⟩; cases s <;> simp [Prod.map]

omit [IsOrderedAddMonoid Λ] in
private theorem letter_archimedeanPrefixWord_of_exists {t β : Λ} {x y : X × Bool}
    (h0 : 0 < β) (hβ : β ≤ t) (h : ∃ n : ℕ, β = (n + 1) • Order.succ 0) :
    (archimedeanPrefixWord t x y).letter β = some x := by
  classical
  rw [archimedeanPrefixWord, letter_ofFun_of_pos_of_le _ h0 hβ]
  simp [h]

omit [IsOrderedAddMonoid Λ] in
private theorem letter_archimedeanPrefixWord_of_not_exists {t β : Λ} {x y : X × Bool}
    (h0 : 0 < β) (hβ : β ≤ t) (h : ¬∃ n : ℕ, β = (n + 1) • Order.succ 0) :
    (archimedeanPrefixWord t x y).letter β = some y := by
  classical
  rw [archimedeanPrefixWord, letter_ofFun_of_pos_of_le _ h0 hβ]
  simp [h]

/-- If `t` exceeds every finite multiple of `Order.succ 0` and `x ≠ y`, then the product
`(x^t)⁻¹ ∗ archimedeanPrefixWord t x y` is undefined. -/
theorem not_exists_isMul_inv_ofFun_const_archimedeanPrefixWord {t : Λ}
    (ht : ∀ n : ℕ, n • Order.succ 0 < t) {x y : X × Bool} (hxy : x ≠ y) :
    ¬∃ w, IsMul (ofFun t fun _ => x)⁻¹ (archimedeanPrefixWord t x y) w := by
  rw [exists_isMul_inv_left_iff (isReduced_ofFun_const t x) (isReduced_archimedeanPrefixWord t x y)]
  rintro ⟨δ, ⟨hδ0, hδ1, -, htake⟩, hmax⟩
  have ht0 : 0 < t := by simpa using ht 0
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_self_of_lt ht0
  have hle_δ : ∀ n : ℕ, n • Order.succ 0 ≤ δ := fun n => by
    refine hmax ⟨nsmul_nonneg h01.le n, ?_, ?_, take_eq_take_iff_forall_letter_eq.2 fun γ hγ => ?_⟩
    · rw [length_ofFun, max_eq_left ht0.le]; exact (ht n).le
    · rw [archimedeanPrefixWord, length_ofFun, max_eq_left ht0.le]; exact (ht n).le
    · by_cases hγ0 : 0 < γ
      · have hγt : γ ≤ t := hγ.trans (ht n).le
        rw [letter_ofFun_of_pos_of_le (fun _ => x) hγ0 hγt,
          letter_archimedeanPrefixWord_of_exists hγ0 hγt
            (exists_eq_succ_nsmul_of_pos_le_nsmul hγ0 hγ)]
      · simp [archimedeanPrefixWord, letter_ofFun, hγ0]
  have hδpos : 0 < δ := h01.trans_le (by simpa using hle_δ 1)
  have hδnot : ¬∃ k : ℕ, δ = (k + 1) • Order.succ 0 := by
    rintro ⟨k, rfl⟩
    have hlt : (k + 1) • Order.succ (0 : Λ) < (k + 2) • Order.succ 0 := by
      rw [show (k + 2) • Order.succ (0 : Λ) = (k + 1) • Order.succ 0 + Order.succ 0 from
        succ_nsmul _ (k + 1)]
      exact lt_add_of_pos_right _ h01
    exact hlt.not_ge (hle_δ (k + 2))
  have hδt : δ ≤ t := by rwa [length_ofFun, max_eq_left ht0.le] at hδ1
  have hletter := take_eq_take_iff_forall_letter_eq.1 htake δ le_rfl
  rw [letter_ofFun_of_pos_of_le (fun _ => x) hδpos hδt,
    letter_archimedeanPrefixWord_of_not_exists hδpos hδt hδnot] at hletter
  exact hxy (Option.some.inj hletter)

/-- Over a non-Archimedean `Λ`, `(a^t)⁻¹ ∗ v` is undefined where `v` has `a` at positions
`1, 2, 3, …` and `b` elsewhere (`a ≠ b`). Hence `∗` is genuinely partial and `R(Λ, X)` is not a
group. -/
theorem undefined_product {t : Λ} (ht : ∀ n : ℕ, n • Order.succ 0 < t) {a b : X} (hab : a ≠ b) :
    (ofFun t fun _ => (a, true))⁻¹.mul (archimedeanPrefixWord t (a, true) (b, true)) =
      Part.none :=
  mul_eq_none_iff.2 fun w hw =>
    not_exists_isMul_inv_ofFun_const_archimedeanPrefixWord ht (by simp [hab]) ⟨w, hw⟩

/-! ### Failure of Stallings' pregroup axiom (P5) on `R(Λ, X)` -/

/-- Stallings' fifth pregroup axiom (P5) fails on the set of all reduced `Λ`-words whenever `Λ` is
non-Archimedean and `X` is nonempty: there exist reduced words `u, v, w, z` such that `u ∗ v`,
`v ∗ w`, and `w ∗ z` are all defined, while neither `(u ∗ v) ∗ w` nor `v ∗ (w ∗ z)` is defined. -/
theorem not_pregroup_P5 {t : Λ} (ht : ∀ n : ℕ, n • Order.succ 0 < t) (a : X) :
    ∃ u v w z : InfWord Λ X,
      u.IsReduced ∧ v.IsReduced ∧ w.IsReduced ∧ z.IsReduced ∧
      (u.mul v).Dom ∧ (v.mul w).Dom ∧ (w.mul z).Dom ∧
      ¬((u.mul v).bind (·.mul w)).Dom ∧ ¬((w.mul z).bind (v.mul ·)).Dom := by
  have ht0 : 0 < t := by simpa using ht 0
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_self_of_lt ht0
  have h1t : Order.succ 0 ≤ t := Order.succ_le_of_lt ht0
  set p : InfWord Λ X := ofFun t fun _ => (a, true)
  set q : InfWord Λ X := archimedeanPrefixWord t (a, true) (a, false)
  set q' : InfWord Λ X := archimedeanPrefixWord t (a, false) (a, true)
  have hp : p.IsReduced := isReduced_ofFun_const t _
  have hq : q.IsReduced := isReduced_archimedeanPrefixWord t _ _
  have hq' : q'.IsReduced := isReduced_archimedeanPrefixWord t _ _
  have hu : (q⁻¹ ++ p⁻¹).IsReduced := by
    refine isReduced_append_iff.2 ⟨hq.inv, hp.inv, fun _ _ => ?_⟩
    rw [letter_inv_succ_zero, length_inv, letter_inv_length, length_ofFun, max_eq_left ht0.le,
      letter_ofFun_of_pos_of_le (fun _ => (a, true)) ht0 le_rfl,
      letter_archimedeanPrefixWord_of_exists h01 h1t ⟨0, by simp⟩]
    simp [Prod.map]
  have hz : (p⁻¹ ++ q').IsReduced := by
    refine isReduced_append_iff.2 ⟨hp.inv, hq', fun _ _ => ?_⟩
    rw [length_inv, letter_inv_length, letter_ofFun_of_pos_of_le (fun _ => (a, true)) h01 h1t,
      letter_archimedeanPrefixWord_of_exists h01 h1t ⟨0, by simp⟩]
    simp [Prod.map]
  have huv : IsMul (q⁻¹ ++ p⁻¹) p q⁻¹ := by
    simpa using (isMul_append_inv_append_iff hu (by simpa using hp)).2 (isMul_empty_right hq.inv)
  have hvw : IsMul p p (p ++ p) := (isCyclicallyReduced_ofFun_const t (a, true)).isMul_self
  have hwz : IsMul p (p⁻¹ ++ q') q' := by
    simpa using (isMul_append_inv_append_iff' (by simpa using hp) hz).2 (isMul_empty_left hq')
  refine ⟨q⁻¹ ++ p⁻¹, p, p, p⁻¹ ++ q', hu, hp, hp, hz, mul_dom_iff.2 ⟨_, huv⟩,
    mul_dom_iff.2 ⟨_, hvw⟩, mul_dom_iff.2 ⟨_, hwz⟩, ?_, ?_⟩
  · simp only [mul_eq_some_iff.2 huv, Part.bind_dom, Part.get_some, mul_dom_iff]
    rintro ⟨-, r, hr⟩
    exact not_exists_isMul_inv_ofFun_const_archimedeanPrefixWord ht
      (x := (a, true)) (y := (a, false)) (by simp) ⟨r⁻¹, by simpa using hr.inv⟩
  · simp only [mul_eq_some_iff.2 hwz, Part.bind_dom, Part.get_some, mul_dom_iff]
    rintro ⟨-, r, hr⟩
    have hpinv : p = (ofFun t fun _ => (a, false))⁻¹ := by
      rw [inv_ofFun]
      simp [p, Prod.map]
    rw [hpinv] at hr
    exact not_exists_isMul_inv_ofFun_const_archimedeanPrefixWord ht (by simp) ⟨r, hr⟩

/-! ### Strict inclusion `CDR(Λ, X) ⊊ R(Λ, X)` -/

private theorem not_cyclic_decomp_of_fin_length {t : Λ} (ht : ∀ n : ℕ, n • Order.succ 0 < t)
    {a : X} {c v : InfWord Λ X} (hv : v.IsCyclicallyReduced)
    (heq : archimedeanPrefixWord t (a, true) (a, false) = c⁻¹ ++ v ++ c)
    {n : ℕ} (hc : c.length = n • Order.succ 0) : False := by
  have ht0 : 0 < t := by simpa using ht 0
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_self_of_lt ht0
  have hlen : t = c.length + (v.length + c.length) := by
    have := congrArg InfWord.length heq
    simpa [archimedeanPrefixWord, length_ofFun, max_eq_left ht0.le] using this
  have h2c : c.length + c.length < t := by
    rw [hc, ← add_nsmul]
    exact ht (n + n)
  have hvpos : 0 < v.length := by grind
  have h1 : v.letter (Order.succ 0) = some (a, true) := by
    have hle : c.length + Order.succ 0 ≤ (c⁻¹ ++ v).length := by
      simp only [length_append, length_inv]
      exact add_le_add_right (Order.succ_le_of_lt hvpos) _
    have hlet : (c⁻¹ ++ v ++ c).letter (c.length + Order.succ 0) = v.letter (Order.succ 0) := by
      rw [letter_append_of_le _ hle, ← length_inv c, letter_append_length_add _ _ h01]
    rw [← hlet, ← heq]
    have hpos : 0 < c.length + Order.succ 0 :=
      add_pos_of_nonneg_of_pos c.length_nonneg h01
    have hsucc : c.length + Order.succ 0 = (n + 1) • Order.succ 0 := by rw [hc, succ_nsmul]
    exact letter_archimedeanPrefixWord_of_exists hpos (hsucc ▸ (ht (n + 1)).le) ⟨n, hsucc⟩
  have h2 : v.letter v.length = some (a, false) := by
    have hlet : (c⁻¹ ++ v ++ c).letter (c.length + v.length) = v.letter v.length := by
      rw [letter_append_of_le _ (by simp), ← length_inv c, letter_append_length_add _ _ hvpos]
    rw [← hlet, ← heq]
    refine letter_archimedeanPrefixWord_of_not_exists
      (add_pos_of_nonneg_of_pos c.length_nonneg hvpos) (by grind [c.length_nonneg]) ?_
    rintro ⟨k, hk⟩
    have hteq : t = (k + 1 + n) • Order.succ 0 := by
      rw [add_nsmul, ← hk, ← hc]
      grind
    exact (ht (k + 1 + n)).ne' hteq
  have hne := (isCyclicallyReduced_iff.1 hv).2 hvpos
  rw [h1, h2] at hne
  exact hne (by simp [Prod.map])

private theorem not_cyclic_decomp_of_inf_length {t : Λ} (ht : ∀ n : ℕ, n • Order.succ 0 < t)
    {a : X} {c v : InfWord Λ X}
    (heq : archimedeanPrefixWord t (a, true) (a, false) = c⁻¹ ++ v ++ c)
    (hc : ∀ n : ℕ, c.length ≠ n • Order.succ 0) : False := by
  have ht0 : 0 < t := by simpa using ht 0
  have h01 : (0 : Λ) < Order.succ 0 := Order.lt_succ_self_of_lt ht0
  have hlen : t = c.length + (v.length + c.length) := by
    have := congrArg InfWord.length heq
    simpa [archimedeanPrefixWord, length_ofFun, max_eq_left ht0.le] using this
  have hcpos : 0 < c.length := lt_of_le_of_ne c.length_nonneg (Ne.symm (by simpa using hc 0))
  have hct : c.length ≤ t := by grind [c.length_nonneg, v.length_nonneg]
  have hleft : (archimedeanPrefixWord t (a, true) (a, false)).letter c.length = some (a, false) :=
    letter_archimedeanPrefixWord_of_not_exists hcpos hct (fun ⟨k, hk⟩ => hc (k + 1) hk)
  have hc1 : c.letter (Order.succ 0) = some (a, false) := by
    have hlet : (c⁻¹ ++ v ++ c).letter ((c⁻¹ ++ v).length + Order.succ 0) =
        c.letter (Order.succ 0) := letter_append_length_add (c⁻¹ ++ v) c h01
    rw [← hlet, ← heq]
    have hpos : 0 < (c⁻¹ ++ v).length + Order.succ 0 :=
      add_pos_of_nonneg_of_pos (c⁻¹ ++ v).length_nonneg h01
    have hle : (c⁻¹ ++ v).length + Order.succ 0 ≤ t := by
      simp only [length_append, length_inv]
      have := Order.succ_le_of_lt hcpos
      grind
    refine letter_archimedeanPrefixWord_of_not_exists hpos hle ?_
    rintro ⟨k, hk⟩
    have hlt := nsmul_succ_zero_lt_of_forall_ne hcpos (fun m => hc (m + 1)) (k + 1)
    simp only [length_append, length_inv] at hk
    grind [v.length_nonneg]
  have hright : (archimedeanPrefixWord t (a, true) (a, false)).letter c.length =
      some (a, true) := by
    rw [heq, letter_append_of_le _ (by simp [v.length_nonneg]),
      letter_append_of_le _ (by simp), letter_inv_length, hc1]
    simp [Prod.map]
  rw [hleft] at hright
  simp at hright

/-- Over a non-Archimedean `Λ`, `archimedeanPrefixWord t (a, true) (a, false)` is reduced yet has
no cyclic decomposition `c⁻¹ ++ v ++ c`. -/
theorem archimedeanPrefixWord_notMem_CDR {t : Λ} (ht : ∀ n : ℕ, n • Order.succ 0 < t) (a : X) :
    archimedeanPrefixWord t (a, true) (a, false) ∉ CDR Λ X := by
  rw [mem_CDR_iff]
  rintro ⟨-, c, v, hv, heq⟩
  by_cases hc : ∃ n : ℕ, c.length = n • Order.succ 0
  · obtain ⟨n, hn⟩ := hc
    exact not_cyclic_decomp_of_fin_length ht hv heq hn
  · push Not at hc
    exact not_cyclic_decomp_of_inf_length ht heq hc

/-- Over a non-Archimedean `Λ` with nonempty alphabet `X`, `CDR Λ X` is a strict subset of the
reduced `Λ`-words. -/
theorem exists_isReduced_notMem_CDR {t : Λ} (ht : ∀ n : ℕ, n • Order.succ 0 < t) (a : X) :
    ∃ w : InfWord Λ X, w.IsReduced ∧ w ∉ CDR Λ X :=
  ⟨archimedeanPrefixWord t (a, true) (a, false),
    isReduced_archimedeanPrefixWord t _ _,
    archimedeanPrefixWord_notMem_CDR ht a⟩

end General

/-! ### Concrete checks over `ℤ ×ₗ ℤ` and `Fin 2` -/

section IntLex

/-- In `ℤ ×ₗ ℤ`, the least positive element is `toLex (0, 1)`. -/
theorem succ_zero_intLex : Order.succ (0 : ℤ ×ₗ ℤ) = toLex (0, 1) := by
  change Order.succ (toLex ((0 : ℤ), (0 : ℤ))) = toLex (0, 1)
  rw [Prod.Lex.succ_toLex, Order.succ_eq_add_one, zero_add]

/-- Every finite multiple of `Order.succ (0 : ℤ ×ₗ ℤ)` is strictly less than `toLex (1, 0)`. -/
theorem nsmul_succ_zero_lt_intLex (n : ℕ) :
    n • Order.succ (0 : ℤ ×ₗ ℤ) < toLex (1, 0) := by
  have h : n • Order.succ (0 : ℤ ×ₗ ℤ) = toLex (0, (n : ℤ)) := by
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [succ_nsmul, ih, succ_zero_intLex]
      change toLex ((0 : ℤ) + 0, (k : ℤ) + 1) = toLex (0, ((k + 1 : ℕ) : ℤ))
      simp
  rw [h, Prod.Lex.lt_iff]
  exact Or.inl zero_lt_one

/-- Concrete check of `a^t ∗ a = a^{t+1}` over `Λ = ℤ ×ₗ ℤ` and `X = Fin 2`. -/
theorem at_mul_a_intLex :
    (ofFun (toLex ((1 : ℤ), (0 : ℤ))) fun _ => ((0 : Fin 2), true)).mul
      (ofFun (Order.succ 0) fun _ => ((0 : Fin 2), true)) =
      Part.some (ofFun (Order.succ (toLex ((1 : ℤ), (0 : ℤ)))) fun _ => ((0 : Fin 2), true)) :=
  at_mul_a (by simpa using nsmul_succ_zero_lt_intLex 0) (0 : Fin 2)

/-- Concrete check of `|a^t ∗ b| = t + 1` over `Λ = ℤ ×ₗ ℤ` and `X = Fin 2`. -/
theorem length_at_mul_b_intLex :
    ((ofFun (toLex ((1 : ℤ), (0 : ℤ))) fun _ => ((0 : Fin 2), true)) ++
      (ofFun (Order.succ 0) fun _ => ((1 : Fin 2), true))).length =
      Order.succ (toLex ((1 : ℤ), (0 : ℤ))) :=
  length_at_mul_b (by simpa using nsmul_succ_zero_lt_intLex 0) (0 : Fin 2) (1 : Fin 2)

/-- Concrete check that `a^t ∗ b` is defined with length `t + 1` over `Λ = ℤ ×ₗ ℤ` and
`X = Fin 2`. -/
theorem at_mul_b_intLex :
    ∃ w, (ofFun (toLex ((1 : ℤ), (0 : ℤ))) fun _ => ((0 : Fin 2), true)).mul
      (ofFun (Order.succ 0) fun _ => ((1 : Fin 2), true)) = Part.some w ∧
      w.length = Order.succ (toLex ((1 : ℤ), (0 : ℤ))) :=
  ⟨_, at_mul_b (by simpa using nsmul_succ_zero_lt_intLex 0) (0 : Fin 2) (1 : Fin 2),
    length_at_mul_b_intLex⟩

/-- Concrete check of an undefined product over `Λ = ℤ ×ₗ ℤ` and `X = Fin 2`. -/
theorem undefined_product_intLex :
    (ofFun (toLex ((1 : ℤ), (0 : ℤ))) fun _ => ((0 : Fin 2), true))⁻¹.mul
      (archimedeanPrefixWord (toLex ((1 : ℤ), (0 : ℤ))) ((0 : Fin 2), true) ((1 : Fin 2), true)) =
      Part.none :=
  undefined_product nsmul_succ_zero_lt_intLex (by decide : (0 : Fin 2) ≠ 1)

/-- Concrete check of Stallings' pregroup axiom (P5) failing on `R(ℤ ×ₗ ℤ, Fin 2)`. -/
theorem not_pregroup_P5_intLex :
    ∃ u v w z : InfWord (ℤ ×ₗ ℤ) (Fin 2),
      u.IsReduced ∧ v.IsReduced ∧ w.IsReduced ∧ z.IsReduced ∧
      (u.mul v).Dom ∧ (v.mul w).Dom ∧ (w.mul z).Dom ∧
      ¬((u.mul v).bind (·.mul w)).Dom ∧ ¬((w.mul z).bind (v.mul ·)).Dom :=
  not_pregroup_P5 nsmul_succ_zero_lt_intLex (0 : Fin 2)

/-- Concrete check that `CDR (ℤ ×ₗ ℤ) (Fin 2)` is a strict subset of the reduced words. -/
theorem exists_isReduced_notMem_CDR_intLex :
    ∃ w : InfWord (ℤ ×ₗ ℤ) (Fin 2), w.IsReduced ∧ w ∉ CDR (ℤ ×ₗ ℤ) (Fin 2) :=
  exists_isReduced_notMem_CDR nsmul_succ_zero_lt_intLex (0 : Fin 2)

end IntLex

end InfWord

end TauCeti
