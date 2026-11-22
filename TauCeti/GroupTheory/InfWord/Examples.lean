/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.InfWord.CDR
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Order.SuccPred.Int
import TauCeti.Order.SuccPred.Iterate
import TauCeti.Order.SuccPred.Prod

/-!
# Non-Archimedean counterexamples for reduced infinite words

Over a discretely ordered non-Archimedean abelian group `Λ`, where there exists `t : Λ` exceeding
every finite multiple `n • Order.succ 0` of the least positive element (such as `t = toLex (1, 0)`
in `ℤ ×ₗ ℤ`, equivalently `¬ Archimedean Λ` by
`TauCeti.Order.not_archimedean_iff_exists_nsmul_succ_zero_lt`), and a nonempty alphabet `X` (for
instance `X = Fin 2`), the partial multiplication `∗` and the subset `CDR(Λ, X)` of cyclically
decomposable reduced words exhibit three obstructions that do not occur in the Archimedean case
`Λ = ℤ`:

* **Partiality of `∗`**: for distinct signed letters `x ≠ y` in `X × Bool` (such as `(a, true)` and
  `(b, true)` with `a ≠ b`, or `(a, true)` and `(a, false)` from a single letter `a : X`), the
  common initial segments of `x^t` and the word `nonArchimedeanWord t x y` on `{β | 0 < β ≤ t}`
  that reads `x` at the iterated successors `Order.succ^[n] 0` (the nonnegative multiples
  `n • Order.succ 0`) and `y` elsewhere have lengths `{0, 1, 2, …}`, which has no greatest
  element, so `(x^t)⁻¹ ∗ nonArchimedeanWord t x y` is undefined
  (`TauCeti.InfWord.inv_ofFun_const_mul_nonArchimedeanWord_eq_none`).
* **Strictness of `CDR(Λ, X)`**: the concatenation `nonArchimedeanWord t x y ++ (x^t)⁻¹` is reduced
  (`TauCeti.InfWord.isReduced_nonArchimedeanWord_append_inv`) yet does not belong to `CDR(Λ, X)`
  (`TauCeti.InfWord.nonArchimedeanWord_append_inv_notMem_CDR`, packaged for a single letter in
  `TauCeti.InfWord.exists_isReduced_notMem_CDR`).
* **Failure of Stallings' pregroup axiom (P5)**: on the set `R(Λ, X)` of all reduced `Λ`-words
  (`TauCeti.InfWord.exists_pregroup_P5_counterexample`), there exist reduced words `u, v, w, z` such
  that `u ∗ v`, `v ∗ w`, and `w ∗ z` are all defined, while neither `(u ∗ v) ∗ w` nor `v ∗ (w ∗ z)`
  is defined. Thus axioms (P1)–(P4) alone do not justify a universal-group normal form without
  proving (P5) on a chosen subset.

We define `nonArchimedeanWord` and characterize its common-prefix lengths with `x^t` in an
arbitrary linear order with `0` and `Order.succ`, prove the general counterexamples for any
discretely ordered non-Archimedean abelian group `Λ` and nonempty alphabet `X`, and check them
concretely on `Λ = ℤ ×ₗ ℤ` (and `X = Fin 2`).

## Main definitions

* `TauCeti.InfWord.nonArchimedeanWord`: the reduced `Λ`-word on `{β | 0 < β ≤ t}` reading `x` at
  the iterated successors `Order.succ^[n] 0` and `y` elsewhere.

## Main results

* `TauCeti.InfWord.common_prefix_lengths_nonArchimedeanWord_eq_range`: the set of common initial
  segment lengths of `x^t` and `nonArchimedeanWord t x y` is the iterated successor range of `0`.
* `TauCeti.InfWord.inv_ofFun_const_mul_nonArchimedeanWord_eq_none`: `(x^t)⁻¹ ∗ v` is undefined when
  `t` exceeds all finite multiples of `Order.succ 0` and `x ≠ y`.
* `TauCeti.InfWord.nonArchimedeanWord_append_inv_notMem_CDR`,
  `TauCeti.InfWord.exists_isReduced_notMem_CDR`: `v ++ (x^t)⁻¹` is reduced yet lies outside
  `CDR(Λ, X)`.
* `TauCeti.InfWord.exists_pregroup_P5_counterexample`: failure of Stallings' pregroup axiom (P5) on
  `R(Λ, X)`.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §2.2 and §3.1–§3.2 (Example 3.5).
-/

public section

namespace TauCeti

namespace InfWord

section Order

variable {Λ X : Type*} [Zero Λ] [LinearOrder Λ] [SuccOrder Λ]

/-- The `Λ`-word of length `max t 0` that reads the signed letter `x` at the iterated successors
`Order.succ^[n] 0` and `y` at all other positions of `{β | 0 < β ≤ t}`. -/
noncomputable def nonArchimedeanWord (t : Λ) (x y : X × Bool) : InfWord Λ X :=
  open Classical in
  ofFun t fun β => if β ∈ Set.range (fun n : ℕ => (Order.succ^[n]) (0 : Λ)) then x else y

@[simp, grind =]
theorem length_nonArchimedeanWord (t : Λ) (x y : X × Bool) :
    (nonArchimedeanWord t x y).length = max t 0 := by
  simp [nonArchimedeanWord]

@[grind =]
theorem letter_nonArchimedeanWord (t : Λ) (x y : X × Bool) (β : Λ) :
    (nonArchimedeanWord t x y).letter β =
      open Classical in
      if 0 < β ∧ β ≤ t then
        some (if β ∈ Set.range (fun n : ℕ => (Order.succ^[n]) (0 : Λ)) then x else y)
      else none := by
  classical
  exact letter_ofFun t _ β

theorem letter_nonArchimedeanWord_of_pos_of_le {t β : Λ} (x y : X × Bool) (h0 : 0 < β)
    (hβ : β ≤ t) :
    (nonArchimedeanWord t x y).letter β =
      open Classical in
      some (if β ∈ Set.range (fun n : ℕ => (Order.succ^[n]) (0 : Λ)) then x else y) := by
  classical
  exact letter_ofFun_of_pos_of_le _ h0 hβ

/-- The word `nonArchimedeanWord t x y` is reduced. -/
@[simp]
theorem isReduced_nonArchimedeanWord (t : Λ) (x y : X × Bool) :
    (nonArchimedeanWord t x y).IsReduced := by
  classical
  refine isReduced_ofFun_iff.2 fun β h0 _ => ?_
  simp only [Order.succ_mem_range_succ_iterate_iff h0.le]
  split_ifs
  · rcases x with ⟨a, s⟩; cases s <;> simp [Prod.map]
  · rcases y with ⟨b, s⟩; cases s <;> simp [Prod.map]

/-- When `t` exceeds every iterated successor `Order.succ^[n] 0` and `x ≠ y`, the common initial
segment lengths of `x^t` and `nonArchimedeanWord t x y` are the iterated successors
`Order.succ^[n] 0`. -/
theorem common_prefix_lengths_nonArchimedeanWord_eq_range {t : Λ}
    (ht : ∀ n : ℕ, (Order.succ^[n]) (0 : Λ) < t) {x y : X × Bool} (hxy : x ≠ y) :
    {β | 0 ≤ β ∧ β ≤ (ofFun t fun _ => x).length ∧
        β ≤ (nonArchimedeanWord t x y).length ∧
        (ofFun t fun _ => x).take β = (nonArchimedeanWord t x y).take β} =
      Set.range (fun n : ℕ => (Order.succ^[n]) (0 : Λ)) := by
  classical
  have ht0 : 0 < t := by simpa using ht 0
  ext β
  simp only [length_ofFun, length_nonArchimedeanWord, max_eq_left ht0.le, Set.mem_ofPred,
    Set.mem_range]
  refine ⟨fun ⟨h0, hβt, _, htake⟩ => ?_, ?_⟩
  · rcases h0.eq_or_lt with rfl | hβ0
    · exact ⟨0, rfl⟩
    have hlet := take_eq_take_iff_forall_letter_eq.1 htake β le_rfl
    rw [letter_ofFun_of_pos_of_le _ hβ0 hβt, letter_nonArchimedeanWord_of_pos_of_le x y hβ0 hβt,
      Option.some.injEq] at hlet
    split_ifs at hlet with hmem
    · exact hmem
    · exact absurd hlet hxy
  · rintro ⟨n, rfl⟩
    have hnt : (Order.succ^[n]) (0 : Λ) ≤ t := (ht n).le
    refine ⟨Order.le_succ_iterate n 0, hnt, hnt,
      take_eq_take_iff_forall_letter_eq.2 fun γ hγ => ?_⟩
    by_cases hγ0 : 0 < γ
    · have hγm : γ ∈ Set.range (fun n : ℕ => (Order.succ^[n]) (0 : Λ)) :=
        Order.mem_range_succ_iterate_of_le hγ0.le hγ
      rw [letter_ofFun_of_pos_of_le _ hγ0 (hγ.trans hnt),
        letter_nonArchimedeanWord_of_pos_of_le x y hγ0 (hγ.trans hnt)]
      simp [hγm]
    · rw [letter_eq_none_of_not_pos hγ0, letter_eq_none_of_not_pos hγ0]

end Order

section General

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ]

/-- When `t` exceeds every finite multiple `n • Order.succ 0` and `x ≠ y`, the partial product
`(x^t)⁻¹ ∗ nonArchimedeanWord t x y` is undefined. -/
theorem inv_ofFun_const_mul_nonArchimedeanWord_eq_none {t : Λ}
    (ht : ∀ n : ℕ, n • Order.succ (0 : Λ) < t) {x y : X × Bool} (hxy : x ≠ y) :
    (ofFun t fun _ => x)⁻¹.mul (nonArchimedeanWord t x y) = Part.none := by
  have ht' : ∀ n : ℕ, (Order.succ^[n]) (0 : Λ) < t := by simpa [Order.succ_iterate_zero] using ht
  rw [mul_eq_none_iff, ← not_exists,
    exists_isMul_inv_left_iff (isReduced_ofFun_const t x) (isReduced_nonArchimedeanWord t x y),
    common_prefix_lengths_nonArchimedeanWord_eq_range ht' hxy]
  rintro ⟨δ, ⟨n, rfl⟩, hmax⟩
  have hlt : (Order.succ^[n]) (0 : Λ) < (Order.succ^[n + 1]) (0 : Λ) := by
    rw [Function.iterate_succ_apply']
    exact Order.lt_succ_self_of_lt (ht' n)
  exact hlt.not_ge (hmax ⟨n + 1, rfl⟩)

/-- When `t` exceeds every finite multiple `n • Order.succ 0` and `x ≠ y`, the concatenation
`nonArchimedeanWord t x y ++ (x^t)⁻¹` is reduced. -/
theorem isReduced_nonArchimedeanWord_append_inv {t : Λ}
    (ht : ∀ n : ℕ, n • Order.succ (0 : Λ) < t) {x y : X × Bool} (hxy : x ≠ y) :
    (nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹).IsReduced := by
  classical
  have ht0 : 0 < t := by simpa using ht 0
  have hnotmem : t ∉ Set.range (fun n : ℕ => (Order.succ^[n]) (0 : Λ)) := by
    rintro ⟨n, hn⟩
    exact (ht n).ne (by simpa [Order.succ_iterate_zero] using hn)
  refine isReduced_append_inv_iff.2 ⟨isReduced_nonArchimedeanWord t x y,
    isReduced_ofFun_const t x, fun _ _ => ?_⟩
  rw [length_ofFun, length_nonArchimedeanWord, max_eq_left ht0.le,
    letter_ofFun_of_pos_of_le _ ht0 le_rfl,
    letter_nonArchimedeanWord_of_pos_of_le x y ht0 le_rfl]
  simp only [hnotmem, ↓reduceIte, ne_eq, Option.some.injEq]
  exact hxy

omit [SuccOrder Λ] in
private theorem common_prefix_lengths_append_eq {u v r s : InfWord Λ X}
    (hlen : u.length = v.length) (hne : u ≠ v) :
    {β | 0 ≤ β ∧ β ≤ (u ++ r).length ∧ β ≤ (v ++ s).length ∧
        (u ++ r).take β = (v ++ s).take β} =
      {β | 0 ≤ β ∧ β ≤ u.length ∧ β ≤ v.length ∧ u.take β = v.take β} := by
  ext β
  simp only [Set.mem_ofPred, length_append]
  refine ⟨fun ⟨h0, _, _, htake⟩ => ?_, fun ⟨h0, hβu, hβv, htake⟩ => ?_⟩
  · have hle : β ≤ u.length := by
      by_contra! hlt
      apply hne
      have h := congrArg (take · u.length) htake
      rwa [take_take, take_take, min_eq_left hlt.le, take_append_length, hlen,
        take_append_length] at h
    refine ⟨h0, hle, hlen ▸ hle, ?_⟩
    rwa [take_append_of_le_length _ hle, take_append_of_le_length _ (hlen ▸ hle)] at htake
  · refine ⟨h0, hβu.trans (le_add_of_nonneg_right r.length_nonneg),
      hβv.trans (le_add_of_nonneg_right s.length_nonneg), ?_⟩
    rw [take_append_of_le_length _ hβu, take_append_of_le_length _ hβv, htake]

/-- When `t` exceeds every finite multiple `n • Order.succ 0` and `x ≠ y`, the reduced word
`nonArchimedeanWord t x y ++ (x^t)⁻¹` does not belong to `CDR(Λ, X)`. -/
theorem nonArchimedeanWord_append_inv_notMem_CDR {t : Λ}
    (ht : ∀ n : ℕ, n • Order.succ (0 : Λ) < t) {x y : X × Bool} (hxy : x ≠ y) :
    nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹ ∉ CDR Λ X := by
  classical
  have ht0 : 0 < t := by simpa using ht 0
  have hred := isReduced_nonArchimedeanWord_append_inv ht hxy
  have hnotmem : t ∉ Set.range (fun n : ℕ => (Order.succ^[n]) (0 : Λ)) := by
    rintro ⟨n, hn⟩
    exact (ht n).ne (by simpa [Order.succ_iterate_zero] using hn)
  have hne : (ofFun t fun _ => x) ≠ nonArchimedeanWord t x y := by
    intro h
    have hl := congrArg (letter · t) h
    rw [letter_ofFun_of_pos_of_le _ ht0 le_rfl,
      letter_nonArchimedeanWord_of_pos_of_le x y ht0 le_rfl] at hl
    simp only [hnotmem, ↓reduceIte, Option.some.injEq] at hl
    exact hxy hl
  intro hCDR
  obtain ⟨δ, hδ⟩ := (exists_isMul_iff hred hred).1 (mul_dom_iff.1 (mul_self_dom_of_mem_CDR hCDR))
  have hset :
      {β | 0 ≤ β ∧ β ≤ (nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹).length ∧
        β ≤ (nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹).length ∧
        (nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹)⁻¹.take β =
          (nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹).take β} =
      {β | 0 ≤ β ∧ β ≤ (ofFun t fun _ => x).length ∧ β ≤ (nonArchimedeanWord t x y).length ∧
        (ofFun t fun _ => x).take β = (nonArchimedeanWord t x y).take β} := by
    rw [← common_prefix_lengths_append_eq (by simp) hne
      (r := (nonArchimedeanWord t x y)⁻¹) (s := (ofFun t fun _ => x)⁻¹)]
    ext β
    simp [inv_append]
  rw [hset] at hδ
  obtain ⟨w, hw⟩ := (exists_isMul_inv_left_iff (isReduced_ofFun_const t x)
    (isReduced_nonArchimedeanWord t x y)).2 ⟨δ, hδ⟩
  exact mul_eq_none_iff.1 (inv_ofFun_const_mul_nonArchimedeanWord_eq_none ht hxy) w hw

/-- Whenever `Λ` has an element exceeding all finite multiples of `Order.succ 0` and `X` has
at least one letter, `CDR(Λ, X)` is a strict subset of the reduced `Λ`-words. -/
theorem exists_isReduced_notMem_CDR {t : Λ} (ht : ∀ n : ℕ, n • Order.succ (0 : Λ) < t)
    (a : X) : ∃ w : InfWord Λ X, w.IsReduced ∧ w ∉ CDR Λ X :=
  ⟨_, isReduced_nonArchimedeanWord_append_inv ht (x := (a, true)) (y := (a, false)) (by simp),
    nonArchimedeanWord_append_inv_notMem_CDR ht (x := (a, true)) (y := (a, false)) (by simp)⟩

/-- Stallings' fifth pregroup axiom (P5) fails on the set of all reduced `Λ`-words whenever `Λ` is
non-Archimedean and `X` is nonempty: there exist reduced words `u, v, w, z` such that `u ∗ v`,
`v ∗ w`, and `w ∗ z` are all defined, while neither `(u ∗ v) ∗ w` nor `v ∗ (w ∗ z)` is defined. -/
theorem exists_pregroup_P5_counterexample {t : Λ} (ht : ∀ n : ℕ, n • Order.succ 0 < t) (a : X) :
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
  have hmem1 : Order.succ (0 : Λ) ∈ Set.range (fun n : ℕ => (Order.succ^[n]) (0 : Λ)) := ⟨1, rfl⟩
  have hu : (q⁻¹ ++ p⁻¹).IsReduced := by
    rw [← inv_append, isReduced_inv]
    refine isReduced_append_iff.2 ⟨hp, hq, fun _ _ => ?_⟩
    rw [length_ofFun, max_eq_left ht0.le, letter_ofFun_of_pos_of_le _ ht0 le_rfl,
      letter_nonArchimedeanWord_of_pos_of_le (a, true) (a, false) h01 h1t]
    simp only [hmem1, ↓reduceIte, Option.map_some, Prod.map, id_eq, Bool.not_true, ne_eq,
      Option.some.injEq, Prod.mk.injEq, true_and]
    decide
  have hz : (p⁻¹ ++ q').IsReduced := by
    refine isReduced_inv_append_iff.2 ⟨hp, hq', fun _ _ => ?_⟩
    rw [letter_ofFun_of_pos_of_le _ h01 h1t,
      letter_nonArchimedeanWord_of_pos_of_le (a, false) (a, true) h01 h1t]
    simp only [hmem1, ↓reduceIte, ne_eq, Option.some.injEq, Prod.mk.injEq, true_and]
    decide
  have huv : (q⁻¹ ++ p⁻¹).mul p = Part.some q⁻¹ := by
    simpa [mul_empty hq.inv] using append_inv_mul_append_cancel (r := empty Λ X) hu
      (by simpa using hp)
  have hvw : p.mul p = Part.some (ofFun (t + t) fun _ => (a, true)) :=
    ofFun_const_mul_ofFun_const _ ht0.le ht0.le
  have hwz : p.mul (p⁻¹ ++ q') = Part.some q' := by
    simpa [empty_mul hq'] using append_mul_inv_append_cancel (p := empty Λ X)
      (by simpa using hp) hz
  refine ⟨q⁻¹ ++ p⁻¹, p, p, p⁻¹ ++ q', hu, hp, hp, hz, by simp [huv], by simp [hvw], by simp [hwz],
    ?_, ?_⟩
  · rw [huv, Part.bind_some, ← Part.eq_none_iff']
    have hnone : p⁻¹.mul q = Part.none :=
      inv_ofFun_const_mul_nonArchimedeanWord_eq_none ht (x := (a, true)) (y := (a, false)) (by simp)
    rw [← inv_inv p, ← InfWord.mul_inv_rev p⁻¹ q, hnone]
    simp [Part.inv_def]
  · rw [hwz, Part.bind_some, ← Part.eq_none_iff']
    have hpinv : p = (ofFun t fun _ => (a, false))⁻¹ := by
      rw [inv_ofFun]
      exact ofFun_congr fun _ _ _ => by simp [Prod.map]
    rw [hpinv]
    exact inv_ofFun_const_mul_nonArchimedeanWord_eq_none ht (by simp)

end General

private theorem nsmul_succ_zero_lt_toLex_one_zero (n : ℕ) :
    n • Order.succ (0 : ℤ ×ₗ ℤ) < toLex (1, 0) :=
  Prod.Lex.lt_iff.2 (.inl (by simp))

-- Concrete check of partiality of `∗` in `InfWord (ℤ ×ₗ ℤ) X` with `t = toLex (1, 0)`.
example {X : Type*} {x y : X × Bool} (hxy : x ≠ y) :
    let t : ℤ ×ₗ ℤ := toLex (1, 0)
    (ofFun t fun _ => x)⁻¹.mul (nonArchimedeanWord t x y) = Part.none :=
  inv_ofFun_const_mul_nonArchimedeanWord_eq_none nsmul_succ_zero_lt_toLex_one_zero hxy

-- Concrete check of strictness of `CDR (ℤ ×ₗ ℤ) X` with `t = toLex (1, 0)`.
example {X : Type*} {x y : X × Bool} (hxy : x ≠ y) :
    let t : ℤ ×ₗ ℤ := toLex (1, 0)
    nonArchimedeanWord t x y ++ (ofFun t fun _ => x)⁻¹ ∉ CDR (ℤ ×ₗ ℤ) X :=
  nonArchimedeanWord_append_inv_notMem_CDR nsmul_succ_zero_lt_toLex_one_zero hxy

-- Concrete check of Stallings' pregroup axiom (P5) failing on `R(ℤ ×ₗ ℤ, Fin 2)`.
example :
    ∃ u v w z : InfWord (ℤ ×ₗ ℤ) (Fin 2),
      u.IsReduced ∧ v.IsReduced ∧ w.IsReduced ∧ z.IsReduced ∧
      (u.mul v).Dom ∧ (v.mul w).Dom ∧ (w.mul z).Dom ∧
      ¬((u.mul v).bind (·.mul w)).Dom ∧ ¬((w.mul z).bind (v.mul ·)).Dom :=
  exists_pregroup_P5_counterexample nsmul_succ_zero_lt_toLex_one_zero (0 : Fin 2)

end InfWord

end TauCeti
