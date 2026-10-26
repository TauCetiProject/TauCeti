/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Karp
public import TauCeti.ModelTheory.Order
public import TauCeti.Order.SuccPred.Iterate
public import TauCeti.Order.SuccPred.Sum
public import Mathlib.ModelTheory.Order
public import Mathlib.Order.SuccPred.Int
public import Mathlib.Order.Interval.Set.OrderIso
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max

/-!
# Back-and-forth for discrete linear orders without endpoints

A discrete linear order without endpoints is a linear order in which every element has an
immediate successor and an immediate predecessor and there is no least or greatest element; in
Mathlib terms, a linear order with `SuccOrder`, `PredOrder`, `NoMaxOrder` and `NoMinOrder`. The
integers `ℤ` are the basic example, and so is `ℤ ⊕ₗ ℤ`, two copies of `ℤ` one after the other.

Any two nonempty discrete linear orders without endpoints are back-and-forth equivalent at every
finite level, hence elementarily equivalent. The proof is the classical Ehrenfeucht–Fraïssé
argument: at level `k` it suffices that the entries of two tuples compare in the same way after
shifting each of them by at most `4 ^ k` successor steps. A new element within `4 ^ (k - 1)` steps
of an old entry is answered at the same offset from the matching entry, and an element far from
every old entry is answered by an element far from every matching entry, in the same gap.

These orders are not all isomorphic, even among countable ones: `ℤ` and `ℤ ⊕ₗ ℤ` are countable,
elementarily equivalent and not isomorphic, since every bounded interval of `ℤ` is finite while
the interval between the two copies of `0` in `ℤ ⊕ₗ ℤ` is infinite. By Karp's theorem for
countable structures they are therefore not even `L_{ω₁ω}`-equivalent: elementary equivalence is
strictly weaker than infinitary equivalence.

## Main results

* `TauCeti.sameAtomicType_order_iff`: in the language of orders, two tuples have the same atomic
  type exactly when they have the same equalities and order relations between their entries.
* `TauCeti.bfEquiv_omega0_of_succOrder_of_predOrder`: nonempty discrete linear orders without
  endpoints are back-and-forth equivalent at level `ω`.
* `TauCeti.elementarilyEquivalent_of_succOrder_of_predOrder`: nonempty discrete linear orders
  without endpoints are elementarily equivalent.
* `TauCeti.isEmpty_equiv_int_sumLex_int`, `TauCeti.elementarilyEquivalent_int_sumLex_int` and
  `TauCeti.not_infEquivAt_nat_int_sumLex_int`: `ℤ` and `ℤ ⊕ₗ ℤ` are elementarily equivalent but
  neither isomorphic nor `L_{ω₁ω}`-equivalent.

## References

* Andrzej Ehrenfeucht, *An application of games to the completeness problem for formalized
  theories*, Fundamenta Mathematicae 49, 1961.
* Wilfrid Hodges, *Model Theory*, Cambridge University Press, 1993, Section 3.3.
* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
-/

public section

universe w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language Order

section Atomic

variable {M : Type w} {N : Type w'} [LE M] [LE N]
variable [Language.order.Structure M] [Language.order.OrderedStructure M]
variable [Language.order.Structure N] [Language.order.OrderedStructure N]

/-- In the language of orders, two tuples have the same atomic type exactly when they have the
same equalities and the same order relations between their entries. -/
theorem sameAtomicType_order_iff {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType (L := Language.order) a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i j, a i ≤ a j ↔ b i ≤ b j := by
  rw [sameAtomicType_iff]
  refine and_congr_right fun _ => ⟨fun h i j => ?_, fun h k r f => ?_⟩
  · simpa [relMap_leSymb] using h leSymb ![i, j]
  · obtain ⟨⟩ := r
    rw [order.relation_eq_leSymb .le, relMap_leSymb, relMap_leSymb]
    exact h (f 0) (f 1)

end Atomic

section Discrete

variable {M : Type w} {N : Type w'} [LinearOrder M] [SuccOrder M] [LinearOrder N] [SuccOrder N]
variable {K K' n : ℕ} {a : Fin n → M} {b : Fin n → N}

/-- The entries of two tuples compare in the same way after shifting each of them by at most `K`
successor steps. -/
private def ShiftAgree (K : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ i j (d e : ℕ), d ≤ K → e ≤ K →
    (succ^[d] (a i) ≤ succ^[e] (a j) ↔ succ^[d] (b i) ≤ succ^[e] (b j))

private theorem ShiftAgree.mono (h : ShiftAgree K a b) (hK : K' ≤ K) : ShiftAgree K' a b :=
  fun i j d e hd he => h i j d e (hd.trans hK) (he.trans hK)

private theorem ShiftAgree.symm (h : ShiftAgree K a b) : ShiftAgree K b a :=
  fun i j d e hd he => (h i j d e hd he).symm

/-- Unshifted entries compare in the same way. -/
private theorem ShiftAgree.le_iff (h : ShiftAgree K a b) (i j : Fin n) :
    a i ≤ a j ↔ b i ≤ b j := by
  simpa using h i j 0 0 K.zero_le K.zero_le

/-- If `succ^[c] x = u`, comparisons of shifts of `x` are comparisons of shifts of `u`. -/
private theorem succ_iterate_le_iff_of_succ_iterate_eq {P : Type*} [LinearOrder P] [SuccOrder P]
    [NoMaxOrder P] {x u y : P} {c : ℕ} (hx : succ^[c] x = u) (d e : ℕ) :
    (succ^[d] x ≤ succ^[e] y ↔ succ^[d] u ≤ succ^[e + c] y) ∧
      (succ^[e] y ≤ succ^[d] x ↔ succ^[e + c] y ≤ succ^[d] u) := by
  subst hx
  rw [← Function.iterate_add_apply]
  exact ⟨(succ_iterate_add_le_succ_iterate_add_iff d e c).symm,
    (succ_iterate_add_le_succ_iterate_add_iff e d c).symm⟩

variable [NoMaxOrder M] [NoMaxOrder N]

/-- To extend agreeing tuples by `m` and `m'`, it suffices to compare the shifts of the new
entries with the shifts of the old ones. -/
private theorem ShiftAgree.snoc (h : ShiftAgree K a b) (hK : K' ≤ K) {m : M} {m' : N}
    (hm : ∀ j (d e : ℕ), d ≤ K' → e ≤ K' →
      (succ^[d] m ≤ succ^[e] (a j) ↔ succ^[d] m' ≤ succ^[e] (b j)) ∧
        (succ^[e] (a j) ≤ succ^[d] m ↔ succ^[e] (b j) ≤ succ^[d] m')) :
    ShiftAgree K' (Fin.snoc a m) (Fin.snoc b m') := by
  intro i j d e hd he
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
  · rw [(succ_strictMono.strictMono_iterate_of_lt_map (lt_succ _)).le_iff_le,
      (succ_strictMono.strictMono_iterate_of_lt_map (lt_succ _)).le_iff_le]
  · exact (hm _ d e hd he).1
  · exact (hm _ e d he hd).2
  · exact h _ _ d e (hd.trans hK) (he.trans hK)

variable [PredOrder N] [NoMinOrder N]

/-- **The forth step.** If the entries of two tuples agree on shifts by at most `2 * K' + 2`
steps, every new element of `M` has an answer in `N` keeping agreement on shifts by at most
`K'` steps. -/
private theorem ShiftAgree.exists_snoc [Nonempty N] (h : ShiftAgree K a b)
    (hK : 2 * K' + 2 ≤ K) (m : M) : ∃ m' : N, ShiftAgree K' (Fin.snoc a m) (Fin.snoc b m') := by
  classical
  -- If `m` lies at most `K'` steps above an entry, answer at the same offset.
  by_cases hA : ∃ i, ∃ c ≤ K', succ^[c] (a i) = m
  · obtain ⟨i, c, hc, rfl⟩ := hA
    refine ⟨succ^[c] (b i), h.snoc (by omega) fun j d e hd he => ?_⟩
    simp only [← Function.iterate_add_apply]
    exact ⟨h i j _ _ (by omega) (by omega), h j i _ _ (by omega) (by omega)⟩
  -- If `m` lies at most `K'` steps below an entry, answer at the same offset.
  by_cases hB : ∃ i, ∃ c ≤ K', succ^[c] m = a i
  · obtain ⟨i, c, hc, hmi⟩ := hB
    have hm'i : succ^[c] (pred^[c] (b i)) = b i :=
      Function.LeftInverse.iterate (g := succ) (f := pred) succ_pred c (b i)
    refine ⟨pred^[c] (b i), h.snoc (by omega) fun j d e hd he => ?_⟩
    rw [(succ_iterate_le_iff_of_succ_iterate_eq hmi d e).1,
      (succ_iterate_le_iff_of_succ_iterate_eq hmi d e).2,
      (succ_iterate_le_iff_of_succ_iterate_eq hm'i d e).1,
      (succ_iterate_le_iff_of_succ_iterate_eq hm'i d e).2]
    exact ⟨h i j _ _ (by omega) (by omega), h j i _ _ (by omega) (by omega)⟩
  -- Otherwise every entry lies more than `K'` steps below or above `m`.
  push Not at hA hB
  have hbelow (j) (hj : a j < m) : succ^[K' + 1] (a j) ≤ m :=
    succ_iterate_le_of_forall_ne hj.le fun c hc => hA j c (by omega)
  have habove (j) (hj : m < a j) : succ^[K' + 1] m ≤ a j :=
    succ_iterate_le_of_forall_ne hj.le fun c hc => hB j c (by omega)
  -- It suffices to find `m'` in the same position relative to the entries of `b`, again more
  -- than `K'` steps away from each of them.
  suffices ∃ m' : N, ∀ j, (a j < m → succ^[K' + 1] (b j) ≤ m') ∧
      (m < a j → succ^[K' + 1] m' ≤ b j) by
    obtain ⟨m', hm'⟩ := this
    refine ⟨m', h.snoc (by omega) fun j d e hd he => ?_⟩
    rcases (hA j 0 K'.zero_le).lt_or_gt with hj | hj
    · have ha := succ_iterate_lt_succ_iterate_of_succ_iterate_le (hbelow j hj)
        (by omega : e < K' + 1) d
      have hb := succ_iterate_lt_succ_iterate_of_succ_iterate_le ((hm' j).1 hj)
        (by omega : e < K' + 1) d
      exact ⟨iff_of_false ha.not_ge hb.not_ge, iff_of_true ha.le hb.le⟩
    · have ha := succ_iterate_lt_succ_iterate_of_succ_iterate_le (habove j hj)
        (by omega : d < K' + 1) e
      have hb := succ_iterate_lt_succ_iterate_of_succ_iterate_le ((hm' j).2 hj)
        (by omega : d < K' + 1) e
      exact ⟨iff_of_true ha.le hb.le, iff_of_false ha.not_ge hb.not_ge⟩
  by_cases hL : ∃ i, a i < m
  · -- Go `K' + 1` steps above the entry of `b` matching the greatest entry of `a` below `m`.
    obtain ⟨i₀, hi₀, hmax⟩ := (Finset.univ.filter fun i => a i < m).exists_max_image a
      (by simpa [Finset.Nonempty] using hL)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀ hmax
    refine ⟨succ^[K' + 1] (b i₀), fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
    · exact (succ_strictMono.iterate _).monotone ((h.le_iff j i₀).1 (hmax j hj))
    · -- The entry `a j` lies at least `2 * K' + 2` steps above `a i₀`.
      have ha : succ^[K' + 1 + (K' + 1)] (a i₀) ≤ succ^[0] (a j) := by
        rw [Function.iterate_add_apply, Function.iterate_zero_apply]
        exact ((succ_strictMono.iterate _).monotone (hbelow i₀ hi₀)).trans (habove j hj)
      simpa only [Function.iterate_add_apply, Function.iterate_zero_apply] using
        (h i₀ j _ 0 (by omega) K.zero_le).1 ha
  · push Not at hL
    by_cases hU : ∃ i, m < a i
    · -- Go `K' + 1` steps below the entry of `b` matching the least entry of `a` above `m`.
      obtain ⟨j₀, hj₀, hmin⟩ := (Finset.univ.filter fun i => m < a i).exists_min_image a
        (by simpa [Finset.Nonempty] using hU)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀ hmin
      refine ⟨pred^[K' + 1] (b j₀), fun j => ⟨fun hj => absurd hj (hL j).not_gt, fun hj => ?_⟩⟩
      rw [Function.LeftInverse.iterate (g := succ) (f := pred) succ_pred]
      exact (h.le_iff j₀ j).1 (hmin j hj)
    · -- The tuples are empty.
      push Not at hU
      exact ⟨Classical.arbitrary N, fun j =>
        ⟨fun hj => absurd hj (hL j).not_gt, fun hj => absurd hj (hU j).not_gt⟩⟩

variable [PredOrder M] [NoMinOrder M]
variable [Language.order.Structure M] [Language.order.OrderedStructure M]
variable [Language.order.Structure N] [Language.order.OrderedStructure N]

/-- Tuples whose entries agree on shifts by at most `4 ^ k` steps are back-and-forth equivalent at
level `k`. -/
private theorem ShiftAgree.bfEquiv [Nonempty M] [Nonempty N] (k : ℕ) {n : ℕ} {a : Fin n → M}
    {b : Fin n → N} (h : ShiftAgree (4 ^ k) a b) :
    BFEquiv (L := Language.order) (k : Ordinal.{o}) n a b := by
  induction k generalizing n with
  | zero =>
    rw [Nat.cast_zero, BFEquiv.zero, sameAtomicType_order_iff]
    refine ⟨fun i j => ?_, h.le_iff⟩
    rw [le_antisymm_iff, le_antisymm_iff, h.le_iff i j, h.le_iff j i]
  | succ k ih =>
    have hK : 2 * 4 ^ k + 2 ≤ 4 ^ (k + 1) := by
      have := Nat.one_le_pow k 4 (by norm_num)
      rw [pow_succ]
      omega
    rw [Nat.cast_succ, BFEquiv.add_one]
    refine ⟨ih (h.mono (by omega)), fun x => ?_, fun y => ?_⟩
    · obtain ⟨y, hy⟩ := h.exists_snoc hK x
      exact ⟨y, ih hy⟩
    · obtain ⟨x, hx⟩ := h.symm.exists_snoc hK y
      exact ⟨x, ih hx.symm⟩

variable (M N) [Nonempty M] [Nonempty N]

/-- **Discrete linear orders without endpoints are back-and-forth equivalent at level `ω`.** In
any two nonempty linear orders with successors and predecessors and without endpoints, the empty
tuples are back-and-forth equivalent at every finite level. -/
theorem bfEquiv_omega0_of_succOrder_of_predOrder :
    BFEquiv (L := Language.order) (Ordinal.omega0 : Ordinal.{o}) 0 (Fin.elim0 : Fin 0 → M)
      (Fin.elim0 : Fin 0 → N) := by
  refine (BFEquiv.limit Ordinal.isSuccLimit_omega0 _ _).mpr fun β hβ => ?_
  obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hβ
  exact ShiftAgree.bfEquiv k fun i => i.elim0

/-- **Discrete linear orders without endpoints are elementarily equivalent.** Any two nonempty
linear orders with successors and predecessors and without endpoints satisfy the same first-order
sentences in the language of orders. -/
theorem elementarilyEquivalent_of_succOrder_of_predOrder : M ≅[Language.order] N :=
  (bfEquiv_omega0_of_succOrder_of_predOrder.{w, w', 0} M N).elementarilyEquivalent

end Discrete

section Int

open Sum

attribute [local instance] orderStructure

/-- `ℤ` and `ℤ ⊕ₗ ℤ` are not isomorphic as orders: the interval between the two copies of `0` in
`ℤ ⊕ₗ ℤ` is infinite, while every bounded interval of `ℤ` is finite. -/
theorem isEmpty_equiv_int_sumLex_int : IsEmpty (ℤ ≃[Language.order] (ℤ ⊕ₗ ℤ)) := by
  refine ⟨fun e => ?_⟩
  let := StrongHomClass.toOrderIsoClass Language.order ℤ (ℤ ⊕ₗ ℤ) (ℤ ≃[Language.order] (ℤ ⊕ₗ ℤ))
  let f := OrderIso.ofClass e
  have hfin : (Set.Icc (toLex (inl 0)) (toLex (inr 0)) : Set (ℤ ⊕ₗ ℤ)).Finite := by
    simpa only [f.image_Icc, OrderIso.apply_symm_apply] using
      (Set.finite_Icc (f.symm (toLex (inl 0))) (f.symm (toLex (inr 0)))).image f
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => toLex (inl (k : ℤ) : ℤ ⊕ ℤ))
    (fun k l hkl => ?_) (fun k => ?_) hfin
  · simpa using hkl
  · exact ⟨Lex.inl_le_inl_iff.mpr (Int.natCast_nonneg k), Lex.inl_le_inr _ _⟩

/-- `ℤ` and `ℤ ⊕ₗ ℤ` satisfy the same first-order sentences in the language of orders. -/
theorem elementarilyEquivalent_int_sumLex_int : ℤ ≅[Language.order] (ℤ ⊕ₗ ℤ) :=
  have : Nonempty (ℤ ⊕ₗ ℤ) := ⟨toLex (inl 0)⟩
  elementarilyEquivalent_of_succOrder_of_predOrder ℤ (ℤ ⊕ₗ ℤ)

/-- **Elementary equivalence is strictly weaker than infinitary equivalence.** The countable
orders `ℤ` and `ℤ ⊕ₗ ℤ` are elementarily equivalent (`elementarilyEquivalent_int_sumLex_int`),
but some `L_{ω₁ω}` sentence distinguishes them. A fortiori they are not `L_{∞ω}`-equivalent, since
`TauCeti.InfEquivW.infEquivAt` turns `L_{∞ω}`-equivalence into agreement at `ℕ`. -/
theorem not_infEquivAt_nat_int_sumLex_int : ¬ InfEquivAt (L := Language.order) ℕ ℤ (ℤ ⊕ₗ ℤ) := by
  have : Countable (ℤ ⊕ₗ ℤ) := inferInstanceAs (Countable (ℤ ⊕ ℤ))
  rw [countable_infEquivAt_nat_iff_iso]
  exact not_nonempty_iff.mpr isEmpty_equiv_int_sumLex_int

end Int

end TauCeti
