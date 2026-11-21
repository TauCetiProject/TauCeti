/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Order.SuccPred.Int
public import TauCeti.GroupTheory.InfWord.CDR
public import TauCeti.Order.SuccPred.Prod
import TauCeti.Order.SuccPred.Iterate

/-!
# Non-Archimedean counterexamples for reduced infinite words

Over a discretely ordered non-Archimedean abelian group `Λ`, where there exists `t : Λ` exceeding
every finite multiple `n • Order.succ 0` of the least positive element (such as `t = toLex (1, 0)`
in `ℤ ×ₗ ℤ`), and a nonempty alphabet `X` (for instance `X = Fin 2`), the partial multiplication `∗`
and the subset `CDR(Λ, X)` of cyclically decomposable reduced words exhibit three obstructions that
do not occur in the Archimedean case `Λ = ℤ`:

* **Partiality of `∗`**: for distinct signed letters `x ≠ y` in `X × Bool` (such as `(a, true)` and
  `(b, true)` with `a ≠ b`, or `(a, true)` and `(a, false)` from a single letter `a : X`), the
  common initial segments of `x^t` and the word `nonArchimedeanWord t x y` on `{β | 0 < β ≤ t}`
  that reads `x` at the nonnegative integer multiples `n • Order.succ 0` and `y` elsewhere have
  lengths `{0, 1, 2, …}`, which has no greatest element, so `(x^t)⁻¹ ∗ nonArchimedeanWord t x y` is
  undefined (`TauCeti.InfWord.inv_ofFun_const_mul_nonArchimedeanWord_eq_none`).
* **Strictness of `CDR(Λ, X)`**: the concatenation `nonArchimedeanWord t x y ++ (x^t)⁻¹` is reduced
  (`TauCeti.InfWord.isReduced_nonArchimedeanWord_append_inv`) yet does not belong to `CDR(Λ, X)`
  (`TauCeti.InfWord.nonArchimedeanWord_append_inv_notMem_CDR`).
* **Failure of Stallings' pregroup axiom (P5)**: on the set `R(Λ, X)` of all reduced `Λ`-words
  (`TauCeti.InfWord.not_pregroup_P5`), there exist reduced words `u, v, w, z` such that `u ∗ v`,
  `v ∗ w`, and `w ∗ z` are all defined, while neither `(u ∗ v) ∗ w` nor `v ∗ (w ∗ z)` is defined.
  Thus axioms (P1)–(P4) alone do not justify a universal-group normal form without proving (P5) on
  a chosen subset.

We prove the general statements for an arbitrary discretely ordered non-Archimedean abelian group
`Λ` and nonempty alphabet `X`, and instantiate them concretely on `Λ = ℤ ×ₗ ℤ` (and `X = Fin 2`).

## Main definitions

* `TauCeti.InfWord.nonArchimedeanWord`: the reduced `Λ`-word on `{β | 0 < β ≤ t}` reading `x` at
  the finite multiples `n • Order.succ 0` and `y` elsewhere.

## Main results

* `TauCeti.InfWord.inv_ofFun_const_mul_nonArchimedeanWord_eq_none`,
  `TauCeti.InfWord.inv_ofFun_const_mul_nonArchimedeanWord_toLex_eq_none`: `(x^t)⁻¹ ∗ v` is
  undefined when `t` exceeds all finite multiples of `Order.succ 0` and `x ≠ y`.
* `TauCeti.InfWord.nonArchimedeanWord_append_inv_notMem_CDR`,
  `TauCeti.InfWord.nonArchimedeanWord_append_inv_toLex_notMem_CDR`: `v ++ (x^t)⁻¹` is reduced yet
  lies outside `CDR(Λ, X)`.
* `TauCeti.InfWord.not_pregroup_P5`, `TauCeti.InfWord.not_pregroup_P5_intLex`: failure of
  Stallings' pregroup axiom (P5) on `R(Λ, X)` and concretely on `R(ℤ ×ₗ ℤ, Fin 2)`.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §2.2 and §3.1–§3.2 (Example 3.5).
-/

public section

namespace TauCeti

namespace InfWord

section General

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ]

/-- The `Λ`-word of length `max t 0` that reads the signed letter `x` at the nonnegative integer
multiples `n • Order.succ 0` and `y` at all other positions of `{β | 0 < β ≤ t}`. -/
noncomputable def nonArchimedeanWord (t : Λ) (x y : X × Bool) : InfWord Λ X :=
  open Classical in
  ofFun t fun β => if β ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) then x else y

omit [IsOrderedAddMonoid Λ] in
@[simp, grind =]
theorem length_nonArchimedeanWord (t : Λ) (x y : X × Bool) :
    (nonArchimedeanWord t x y).length = max t 0 := by
  simp [nonArchimedeanWord]

omit [IsOrderedAddMonoid Λ] in
@[grind =]
theorem letter_nonArchimedeanWord (t : Λ) (x y : X × Bool) (β : Λ) :
    (nonArchimedeanWord t x y).letter β =
      open Classical in
      if 0 < β ∧ β ≤ t then
        some (if β ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) then x else y)
      else none := by
  classical
  exact letter_ofFun t _ β

omit [IsOrderedAddMonoid Λ] in
theorem letter_nonArchimedeanWord_of_pos_of_le {t β : Λ} (x y : X × Bool) (h0 : 0 < β)
    (hβ : β ≤ t) :
    (nonArchimedeanWord t x y).letter β =
      open Classical in
      some (if β ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) then x else y) := by
  classical
  exact letter_ofFun_of_pos_of_le _ h0 hβ

/-- The word `nonArchimedeanWord t x y` is reduced. -/
@[simp]
theorem isReduced_nonArchimedeanWord (t : Λ) (x y : X × Bool) :
    (nonArchimedeanWord t x y).IsReduced := by
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

/-- When `t` exceeds every finite multiple `n • Order.succ 0` and `x ≠ y`, the common initial
segment lengths of `x^t` and `nonArchimedeanWord t x y` are the nonnegative integer multiples
`n • Order.succ 0`. -/
theorem commonPrefix_nonArchimedeanWord_eq_range {t : Λ}
    (ht : ∀ n : ℕ, n • Order.succ (0 : Λ) < t) {x y : X × Bool} (hxy : x ≠ y) :
    {β | 0 ≤ β ∧ β ≤ (ofFun t fun _ => x).length ∧
        β ≤ (nonArchimedeanWord t x y).length ∧
        (ofFun t fun _ => x).take β = (nonArchimedeanWord t x y).take β} =
      Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) := by
  classical
  have ht0 : 0 < t := by simpa using ht 0
  ext β
  simp only [length_ofFun, length_nonArchimedeanWord, max_eq_left ht0.le, Set.mem_ofPred,
    Set.mem_range]
  refine ⟨fun ⟨h0, hβt, _, htake⟩ => ?_, ?_⟩
  · rcases h0.eq_or_lt with rfl | hβ0
    · exact ⟨0, zero_nsmul _⟩
    have hlet := take_eq_take_iff_forall_letter_eq.1 htake β le_rfl
    rw [letter_ofFun_of_pos_of_le _ hβ0 hβt, letter_nonArchimedeanWord_of_pos_of_le x y hβ0 hβt,
      Option.some.injEq] at hlet
    split_ifs at hlet with hmem
    · exact hmem
    · exact absurd hlet hxy
  · rintro ⟨n, rfl⟩
    have hnt : n • Order.succ (0 : Λ) ≤ t := (ht n).le
    have h01 : 0 ≤ Order.succ (0 : Λ) := Order.le_succ 0
    refine ⟨nsmul_nonneg h01 n, hnt, hnt, take_eq_take_iff_forall_letter_eq.2 fun γ hγ => ?_⟩
    by_cases hγ0 : 0 < γ
    · have hγm : γ ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) := by
        by_contra hne
        rw [Set.mem_range, not_exists] at hne
        have hle := Order.succ_iterate_le_of_forall_ne (a := (0 : Λ)) (b := γ) hγ0.le
          (n := n + 1) fun k _ hk => hne k (by simpa using hk)
        rw [Order.succ_iterate_zero, succ_nsmul, ← Order.succ_eq_add_succ_zero] at hle
        exact (Order.lt_succ_self_of_lt (ht n)).not_ge (hle.trans hγ)
      rw [letter_ofFun_of_pos_of_le _ hγ0 (hγ.trans hnt),
        letter_nonArchimedeanWord_of_pos_of_le x y hγ0 (hγ.trans hnt)]
      simp [hγm]
    · rw [letter_eq_none_of_not_pos hγ0, letter_eq_none_of_not_pos hγ0]

/-- When `t` exceeds every finite multiple `n • Order.succ 0` and `x ≠ y`, the partial product
`(x^t)⁻¹ ∗ nonArchimedeanWord t x y` is undefined. -/
theorem inv_ofFun_const_mul_nonArchimedeanWord_eq_none {t : Λ}
    (ht : ∀ n : ℕ, n • Order.succ (0 : Λ) < t) {x y : X × Bool} (hxy : x ≠ y) :
    (ofFun t fun _ => x)⁻¹.mul (nonArchimedeanWord t x y) = Part.none := by
  rw [mul_eq_none_iff, ← not_exists,
    exists_isMul_inv_left_iff (isReduced_ofFun_const t x) (isReduced_nonArchimedeanWord t x y),
    commonPrefix_nonArchimedeanWord_eq_range ht hxy]
  rintro ⟨δ, ⟨n, rfl⟩, hmax⟩
  have h01 : 0 < Order.succ (0 : Λ) := Order.lt_succ_self_of_lt (by simpa using ht 0)
  have hle : (n + 1) • Order.succ (0 : Λ) ≤ n • Order.succ 0 := hmax ⟨n + 1, rfl⟩
  rw [succ_nsmul] at hle
  grind

/-- When `t` exceeds every finite multiple `n • Order.succ 0` and `x ≠ y`, the concatenation
`nonArchimedeanWord t x y ++ (x^t)⁻¹` is reduced. -/
theorem isReduced_nonArchimedeanWord_append_inv {t : Λ}
    (ht : ∀ n : ℕ, n • Order.succ (0 : Λ) < t) {x y : X × Bool} (hxy : x ≠ y) :
    (nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹).IsReduced := by
  classical
  have ht0 : 0 < t := by simpa using ht 0
  refine isReduced_append_iff.2 ⟨isReduced_nonArchimedeanWord t x y,
    (isReduced_ofFun_const t x).inv, fun _ _ => ?_⟩
  have hnotmem : t ∉ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) := by
    rintro ⟨n, hn⟩; exact (ht n).ne hn
  rw [letter_inv_succ_zero, length_ofFun, length_nonArchimedeanWord, max_eq_left ht0.le,
    letter_ofFun_of_pos_of_le _ ht0 le_rfl,
    letter_nonArchimedeanWord_of_pos_of_le x y ht0 le_rfl]
  simp only [hnotmem, ↓reduceIte, Option.map_some, ne_eq, Option.some.injEq]
  exact fun h => hxy (by rcases x; rcases y; simpa [Prod.map] using h)

/-- When `t` exceeds every finite multiple `n • Order.succ 0` and `x ≠ y`, the reduced word
`nonArchimedeanWord t x y ++ (x^t)⁻¹` does not belong to `CDR(Λ, X)`. -/
theorem nonArchimedeanWord_append_inv_notMem_CDR {t : Λ}
    (ht : ∀ n : ℕ, n • Order.succ (0 : Λ) < t) {x y : X × Bool} (hxy : x ≠ y) :
    nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹ ∉ CDR Λ X := by
  have ht0 : 0 < t := by simpa using ht 0
  have hred := isReduced_nonArchimedeanWord_append_inv ht hxy
  intro hCDR
  obtain ⟨δ, hδ⟩ := (exists_isMul_iff hred hred).1 (mul_dom_iff.1 (mul_self_dom_of_mem_CDR hCDR))
  have hnone : ¬∃ w, IsMul (ofFun t fun _ => x)⁻¹ (nonArchimedeanWord t x y) w :=
    not_exists.2 (mul_eq_none_iff.1 (inv_ofFun_const_mul_nonArchimedeanWord_eq_none ht hxy))
  rw [exists_isMul_inv_left_iff (isReduced_ofFun_const t x)
    (isReduced_nonArchimedeanWord t x y)] at hnone
  refine hnone ⟨δ, ?_⟩
  convert hδ using 1
  ext β
  simp only [Set.mem_ofPred, inv_append, inv_inv, length_append, length_inv, length_ofFun,
    length_nonArchimedeanWord, max_eq_left ht0.le]
  refine ⟨fun ⟨h0, hβt, _, htake⟩ => ?_, fun ⟨h0, _, _, htake⟩ => ?_⟩
  · have hle2 : β ≤ t + t := hβt.trans (le_add_of_nonneg_right ht0.le)
    refine ⟨h0, hle2, hle2, ?_⟩
    rw [take_append_of_le_length _ (by simp [ht0.le, hβt]),
      take_append_of_le_length _ (by simp [ht0.le, hβt]), htake]
  · by_cases htβ : t ≤ β
    · exfalso
      have huv : (ofFun t fun _ => x).take t = (nonArchimedeanWord t x y).take t := by
        have h := congrArg (take · t) htake
        rwa [take_take, take_take, min_eq_left htβ,
          take_append_of_le_length _ (by simp [ht0.le]),
          take_append_of_le_length _ (by simp [ht0.le])] at h
      have hmem : t ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) := by
        rw [← commonPrefix_nonArchimedeanWord_eq_range ht hxy]
        exact ⟨ht0.le, by simp [ht0.le], by simp [ht0.le], huv⟩
      obtain ⟨n, hn⟩ := hmem
      exact (ht n).ne hn
    · have hle : β ≤ t := le_of_not_ge htβ
      refine ⟨h0, hle, hle, ?_⟩
      rwa [take_append_of_le_length _ (by simp [ht0.le, hle]),
        take_append_of_le_length _ (by simp [ht0.le, hle])] at htake

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
  set q : InfWord Λ X := nonArchimedeanWord t (a, true) (a, false)
  set q' : InfWord Λ X := nonArchimedeanWord t (a, false) (a, true)
  have hp : p.IsReduced := isReduced_ofFun_const t _
  have hq : q.IsReduced := isReduced_nonArchimedeanWord t _ _
  have hq' : q'.IsReduced := isReduced_nonArchimedeanWord t _ _
  have hmem1 : Order.succ (0 : Λ) ∈ Set.range (· • Order.succ (0 : Λ) : ℕ → Λ) := ⟨1, one_nsmul _⟩
  have hu : (q⁻¹ ++ p⁻¹).IsReduced := by
    refine isReduced_append_iff.2 ⟨hq.inv, hp.inv, fun _ _ => ?_⟩
    rw [letter_inv_succ_zero, length_inv, letter_inv_length, length_ofFun, max_eq_left ht0.le,
      letter_ofFun_of_pos_of_le (fun _ => (a, true)) ht0 le_rfl,
      letter_nonArchimedeanWord_of_pos_of_le (a, true) (a, false) h01 h1t]
    simp [hmem1, Prod.map]
  have hz : (p⁻¹ ++ q').IsReduced := by
    refine isReduced_append_iff.2 ⟨hp.inv, hq', fun _ _ => ?_⟩
    rw [length_inv, letter_inv_length, letter_ofFun_of_pos_of_le (fun _ => (a, true)) h01 h1t,
      letter_nonArchimedeanWord_of_pos_of_le (a, false) (a, true) h01 h1t]
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
    exact mul_eq_none_iff.1 (inv_ofFun_const_mul_nonArchimedeanWord_eq_none ht
      (x := (a, true)) (y := (a, false)) (by simp)) r⁻¹ (by simpa using hr.inv)
  · simp only [mul_eq_some_iff.2 hwz, Part.bind_dom, Part.get_some, mul_dom_iff]
    rintro ⟨-, r, hr⟩
    have hpinv : p = (ofFun t fun _ => (a, false))⁻¹ := by
      rw [inv_ofFun]
      exact ofFun_congr fun _ _ _ => by simp [Prod.map]
    rw [hpinv] at hr
    exact mul_eq_none_iff.1 (inv_ofFun_const_mul_nonArchimedeanWord_eq_none ht (by simp)) r hr

end General

/-- In `InfWord (ℤ ×ₗ ℤ) X` with `t = toLex (1, 0)` and distinct signed letters `x ≠ y`, the
partial product `(x^t)⁻¹ ∗ nonArchimedeanWord t x y` is undefined. -/
theorem inv_ofFun_const_mul_nonArchimedeanWord_toLex_eq_none {x y : X × Bool} (hxy : x ≠ y) :
    let t : ℤ ×ₗ ℤ := toLex (1, 0)
    (ofFun t fun _ => x)⁻¹.mul (nonArchimedeanWord t x y) = Part.none :=
  inv_ofFun_const_mul_nonArchimedeanWord_eq_none (fun _ => Prod.Lex.lt_iff.2 (.inl (by simp))) hxy

/-- In `InfWord (ℤ ×ₗ ℤ) X` with `t = toLex (1, 0)` and distinct signed letters `x ≠ y`, the
reduced word `nonArchimedeanWord t x y ++ (x^t)⁻¹` does not belong to `CDR (ℤ ×ₗ ℤ) X`. -/
theorem nonArchimedeanWord_append_inv_toLex_notMem_CDR {x y : X × Bool} (hxy : x ≠ y) :
    let t : ℤ ×ₗ ℤ := toLex (1, 0)
    nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹ ∉ CDR (ℤ ×ₗ ℤ) X :=
  nonArchimedeanWord_append_inv_notMem_CDR (fun _ => Prod.Lex.lt_iff.2 (.inl (by simp))) hxy

/-- Concrete check of Stallings' pregroup axiom (P5) failing on `R(ℤ ×ₗ ℤ, Fin 2)`. -/
theorem not_pregroup_P5_intLex :
    ∃ u v w z : InfWord (ℤ ×ₗ ℤ) (Fin 2),
      u.IsReduced ∧ v.IsReduced ∧ w.IsReduced ∧ z.IsReduced ∧
      (u.mul v).Dom ∧ (v.mul w).Dom ∧ (w.mul z).Dom ∧
      ¬((u.mul v).bind (·.mul w)).Dom ∧ ¬((w.mul z).bind (v.mul ·)).Dom :=
  not_pregroup_P5 (t := toLex ((1 : ℤ), (0 : ℤ)))
    (fun _ => Prod.Lex.lt_iff.2 (.inl (by simp))) (0 : Fin 2)

end InfWord

end TauCeti
