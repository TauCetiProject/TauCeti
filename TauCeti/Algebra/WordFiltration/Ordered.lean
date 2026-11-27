/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.Generators
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Integral straightening of weighted words

A word in weighted ring elements has weight the sum of its letters' weights, including
weight zero for the empty word. If exchanging an inverted pair changes its product by an
integral combination of words of strictly smaller weight, sorting a word preserves its
product modulo lower weight. Consequently nondecreasing words span every bounded word span.

The argument uses stable insertion sort: letters with equal keys are never exchanged.
Thus no commutation assumption on letters with equal keys is required. For a finite family
`g i n`, with `g i 0 = 1`, a bounded integral single-index multiplication law compresses
consecutive equal indices. The resulting increasing products, indexed by exponent vectors,
span the same bounded filtration and, without a bound, the generated subring. The latter
identification reuses `TauCeti.GradedAlgebra.iSup_wordSpan` for the exact-weight word spans.
-/

public section

namespace TauCeti

variable {A α : Type*} [Ring A] (e : α → A) (wt : α → ℕ)

/-- The integral span of words of weight at most `d`. -/
def weightedWordSpan (d : ℕ) : Submodule ℤ A :=
  Submodule.span ℤ {x | ∃ l : List α, (l.map wt).sum ≤ d ∧ (l.map e).prod = x}

/-- The integral span of words of weight strictly below `d`; it is zero for `d = 0`. -/
def weightedWordSpanLT (d : ℕ) : Submodule ℤ A :=
  Submodule.span ℤ {x | ∃ l : List α, (l.map wt).sum < d ∧ (l.map e).prod = x}

/-- The defining bounded-word span formula. -/
theorem weightedWordSpan_def (d : ℕ) :
    weightedWordSpan e wt d =
      Submodule.span ℤ {x | ∃ l : List α, (l.map wt).sum ≤ d ∧ (l.map e).prod = x} :=
  (rfl)

/-- The defining strict-word span formula. -/
theorem weightedWordSpanLT_def (d : ℕ) :
    weightedWordSpanLT e wt d =
      Submodule.span ℤ {x | ∃ l : List α, (l.map wt).sum < d ∧ (l.map e).prod = x} :=
  (rfl)

/-- A word belongs to its bounded word span. -/
theorem prod_mem_weightedWordSpan (l : List α) {d : ℕ} (h : (l.map wt).sum ≤ d) :
    (l.map e).prod ∈ weightedWordSpan e wt d :=
  Submodule.subset_span ⟨l, h, rfl⟩

/-- A word of strictly smaller weight belongs to the strict word span. -/
theorem prod_mem_weightedWordSpanLT (l : List α) {d : ℕ} (h : (l.map wt).sum < d) :
    (l.map e).prod ∈ weightedWordSpanLT e wt d :=
  Submodule.subset_span ⟨l, h, rfl⟩

/-- To contain a bounded word span it suffices, and is necessary, to contain its words. -/
theorem weightedWordSpan_le_iff {d : ℕ} {p : Submodule ℤ A} :
    weightedWordSpan e wt d ≤ p ↔
      ∀ l : List α, (l.map wt).sum ≤ d → (l.map e).prod ∈ p := by
  rw [weightedWordSpan, Submodule.span_le]
  exact ⟨fun h l hl => h ⟨l, hl, rfl⟩, by rintro h _ ⟨l, hl, rfl⟩; exact h l hl⟩

/-- To contain a strict word span it suffices, and is necessary, to contain its words. -/
theorem weightedWordSpanLT_le_iff {d : ℕ} {p : Submodule ℤ A} :
    weightedWordSpanLT e wt d ≤ p ↔
      ∀ l : List α, (l.map wt).sum < d → (l.map e).prod ∈ p := by
  rw [weightedWordSpanLT, Submodule.span_le]
  exact ⟨fun h l hl => h ⟨l, hl, rfl⟩, by rintro h _ ⟨l, hl, rfl⟩; exact h l hl⟩

/-- No word has weight strictly below zero. -/
@[simp]
theorem weightedWordSpanLT_zero : weightedWordSpanLT e wt 0 = ⊥ := by
  simp [weightedWordSpanLT]

/-- The bounded word spans increase with the bound. -/
theorem weightedWordSpan_mono : Monotone (weightedWordSpan e wt) := by
  intro i j hij
  exact (weightedWordSpan_le_iff e wt).2 fun l hl =>
    prod_mem_weightedWordSpan e wt l (hl.trans hij)

/-- Multiplication adds the bounds on word weights. -/
theorem mul_mem_weightedWordSpan {i j : ℕ} {x y : A}
    (hx : x ∈ weightedWordSpan e wt i) (hy : y ∈ weightedWordSpan e wt j) :
    x * y ∈ weightedWordSpan e wt (i + j) := by
  have h : weightedWordSpan e wt i * weightedWordSpan e wt j ≤
      weightedWordSpan e wt (i + j) := by
    rw [weightedWordSpan, weightedWordSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
    simpa only [SetLike.mem_coe, List.map_append, List.prod_append] using
      prod_mem_weightedWordSpan e wt (l ++ t) (by
        simp only [List.map_append, List.sum_append]
        omega)
  exact h (Submodule.mul_mem_mul hx hy)

/-- A strict weight bound remains strict after multiplication on the right. -/
theorem mul_mem_weightedWordSpanLT_left {i j : ℕ} {x y : A}
    (hx : x ∈ weightedWordSpanLT e wt i) (hy : y ∈ weightedWordSpan e wt j) :
    x * y ∈ weightedWordSpanLT e wt (i + j) := by
  have h : weightedWordSpanLT e wt i * weightedWordSpan e wt j ≤
      weightedWordSpanLT e wt (i + j) := by
    rw [weightedWordSpanLT, weightedWordSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
    simpa only [SetLike.mem_coe, List.map_append, List.prod_append] using
      prod_mem_weightedWordSpanLT e wt (l ++ t) (by
        simp only [List.map_append, List.sum_append]
        omega)
  exact h (Submodule.mul_mem_mul hx hy)

/-- A strict weight bound remains strict after multiplication on the left. -/
theorem mul_mem_weightedWordSpanLT_right {i j : ℕ} {x y : A}
    (hx : x ∈ weightedWordSpan e wt i) (hy : y ∈ weightedWordSpanLT e wt j) :
    x * y ∈ weightedWordSpanLT e wt (i + j) := by
  have h : weightedWordSpan e wt i * weightedWordSpanLT e wt j ≤
      weightedWordSpanLT e wt (i + j) := by
    rw [weightedWordSpan, weightedWordSpanLT, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
    simpa only [SetLike.mem_coe, List.map_append, List.prod_append] using
      prod_mem_weightedWordSpanLT e wt (l ++ t) (by
        simp only [List.map_append, List.sum_append]
        omega)
  exact h (Submodule.mul_mem_mul hx hy)

/-- All bounded word spans together give the integral module of the generated subring. -/
theorem iSup_weightedWordSpan :
    ⨆ d, weightedWordSpan e wt d = (Algebra.adjoin ℤ (Set.range e)).toSubmodule := by
  rw [← GradedAlgebra.iSup_wordSpan e wt]
  apply le_antisymm
  · refine iSup_le fun d => (weightedWordSpan_le_iff e wt).2 fun l _ => ?_
    exact Submodule.mem_iSup_of_mem _ (GradedAlgebra.prod_mem_wordSpan e wt l)
  · refine iSup_le fun d => (GradedAlgebra.wordSpan_le_iff d _).2 fun l hl => ?_
    exact Submodule.mem_iSup_of_mem d (prod_mem_weightedWordSpan e wt l hl.le)

section Sorting

variable {κ : Type*} [LinearOrder κ] (key : α → κ)
variable (hswap : ∀ a b, key b < key a →
  e a * e b - e b * e a ∈ weightedWordSpanLT e wt (wt a + wt b))

include hswap in
private theorem prod_sub_orderedInsert (a : α) (l : List α) :
    e a * (l.map e).prod - ((l.orderedInsert (fun a b => key a ≤ key b) a).map e).prod ∈
      weightedWordSpanLT e wt (wt a + (l.map wt).sum) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases hab : key a ≤ key b
    · simp [List.orderedInsert_cons, hab]
    · rw [List.orderedInsert_cons, ite_eq_right hab]
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      have h₁ := mul_mem_weightedWordSpanLT_left e wt
        (hswap a b (lt_of_not_ge hab)) (prod_mem_weightedWordSpan e wt l le_rfl)
      rw [Nat.add_assoc] at h₁
      have hb : e b ∈ weightedWordSpan e wt (wt b) := by
        simpa using prod_mem_weightedWordSpan e wt [b] le_rfl
      have h₂ := mul_mem_weightedWordSpanLT_right e wt hb ih
      rw [← Nat.add_assoc, Nat.add_comm (wt b) (wt a), Nat.add_assoc] at h₂
      simpa only [sub_mul, mul_sub, mul_assoc, sub_add_sub_cancel] using
        (weightedWordSpanLT e wt (wt a + (wt b + (l.map wt).sum))).add_mem h₁ h₂

include hswap in
/-- Stable sorting changes a word only by an integral combination of lower-weight words. -/
theorem prod_sub_insertionSort_mem_weightedWordSpanLT (l : List α) :
    (l.map e).prod - ((l.insertionSort (fun a b => key a ≤ key b)).map e).prod ∈
      weightedWordSpanLT e wt (l.map wt).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.insertionSort_cons, List.map_cons, List.prod_cons, List.sum_cons]
    have ha : e a ∈ weightedWordSpan e wt (wt a) := by
      simpa using prod_mem_weightedWordSpan e wt [a] le_rfl
    have h₁ := mul_mem_weightedWordSpanLT_right e wt ha ih
    have h₂ := prod_sub_orderedInsert e wt key hswap a
      (l.insertionSort (fun a b => key a ≤ key b))
    rw [((List.perm_insertionSort (fun a b => key a ≤ key b) l).map wt).sum_eq] at h₂
    simpa only [mul_sub, sub_add_sub_cancel] using
      (weightedWordSpanLT e wt _).add_mem h₁ h₂

include hswap in
/-- Under lower-weight exchange relations, nondecreasing words span every bounded word span. -/
theorem weightedWordSpan_eq_span_sorted (d : ℕ) :
    weightedWordSpan e wt d = Submodule.span ℤ
      {x | ∃ l : List α, l.Pairwise (fun a b => key a ≤ key b) ∧
        (l.map wt).sum ≤ d ∧ (l.map e).prod = x} := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    refine le_antisymm ((weightedWordSpan_le_iff e wt).2 fun l hl => ?_)
      (Submodule.span_le.2 ?_)
    · let s := l.insertionSort (fun a b => key a ≤ key b)
      have hw : (s.map wt).sum = (l.map wt).sum :=
        ((List.perm_insertionSort _ l).map wt).sum_eq
      have hs : (s.map e).prod ∈ Submodule.span ℤ
          {x | ∃ t : List α, t.Pairwise (fun a b => key a ≤ key b) ∧
            (t.map wt).sum ≤ d ∧ (t.map e).prod = x} :=
        Submodule.subset_span ⟨s, List.pairwise_insertionSort _ _, hw.trans_le hl, rfl⟩
      have hlow : weightedWordSpanLT e wt (l.map wt).sum ≤ Submodule.span ℤ
          {x | ∃ t : List α, t.Pairwise (fun a b => key a ≤ key b) ∧
            (t.map wt).sum ≤ d ∧ (t.map e).prod = x} := by
        refine (weightedWordSpanLT_le_iff e wt).2 fun t ht => ?_
        have hm := prod_mem_weightedWordSpan e wt t le_rfl
        rw [ih _ (ht.trans_le hl)] at hm
        exact Submodule.span_mono (by
          rintro x ⟨u, hu, hwu, rfl⟩
          exact ⟨u, hu, hwu.trans (ht.le.trans hl), rfl⟩) hm
      exact (Submodule.sub_mem_iff_left _ hs).mp
        (hlow (prod_sub_insertionSort_mem_weightedWordSpanLT e wt key hswap l))
    · rintro x ⟨l, _, hl, rfl⟩
      exact prod_mem_weightedWordSpan e wt l hl

end Sorting

section FiniteFamily

variable {r : ℕ} (g : Fin r → ℕ → A)

/-- Increasing products in the factors `g`, with bounded total exponent. -/
def orderedFactorSpan (d : ℕ) : Submodule ℤ A :=
  Submodule.span ℤ {x | ∃ a : Fin r → ℕ, ∑ i, a i ≤ d ∧
    (List.ofFn fun i => g i (a i)).prod = x}

/-- The defining span formula for increasing products of bounded total exponent. -/
theorem orderedFactorSpan_def (d : ℕ) :
    orderedFactorSpan g d = Submodule.span ℤ {x | ∃ a : Fin r → ℕ, ∑ i, a i ≤ d ∧
      (List.ofFn fun i => g i (a i)).prod = x} :=
  (rfl)

/-- An increasing product belongs to the ordered span with its total exponent bound. -/
theorem prod_mem_orderedFactorSpan (a : Fin r → ℕ) {d : ℕ} (h : ∑ i, a i ≤ d) :
    (List.ofFn fun i => g i (a i)).prod ∈ orderedFactorSpan g d :=
  Submodule.subset_span ⟨a, h, rfl⟩

/-- A submodule contains the bounded ordered span exactly when it contains all its
increasing products with the stated total-exponent bound. -/
theorem orderedFactorSpan_le_iff {d : ℕ} {p : Submodule ℤ A} :
    orderedFactorSpan g d ≤ p ↔ ∀ a : Fin r → ℕ, ∑ i, a i ≤ d →
      (List.ofFn fun i => g i (a i)).prod ∈ p := by
  rw [orderedFactorSpan, Submodule.span_le]
  exact ⟨fun h a ha => h ⟨a, ha, rfl⟩, by rintro h _ ⟨a, ha, rfl⟩; exact h a ha⟩

/-- Increasing the total-exponent bound enlarges the ordered span. -/
theorem orderedFactorSpan_mono : Monotone (orderedFactorSpan g) := by
  intro i j hij
  apply Submodule.span_mono
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, ha.trans hij, rfl⟩

private theorem mul_first_mem_orderedFactorSpan {s : ℕ} (g : Fin (s + 1) → ℕ → A)
    (hsame : ∀ m n, g 0 m * g 0 n ∈
      Submodule.span ℤ {x | ∃ k ≤ m + n, g 0 k = x})
    (m d : ℕ) {x : A} (hx : x ∈ orderedFactorSpan g d) :
    g 0 m * x ∈ orderedFactorSpan g (m + d) := by
  have h : orderedFactorSpan g d ≤
      (orderedFactorSpan g (m + d)).comap (LinearMap.mulLeft ℤ (g 0 m)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have hk : Submodule.span ℤ {x | ∃ k ≤ m + a 0, g 0 k = x} ≤
        (orderedFactorSpan g (m + d)).comap
          (LinearMap.mulRight ℤ (List.ofFn fun i => g i.succ (a i.succ)).prod) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, hk, rfl⟩
      have hdeg : ∑ i, Fin.cons k (fun i => a i.succ) i ≤ m + d := by
        rw [Fin.sum_univ_succ] at ha ⊢
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega
      simpa only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply, List.ofFn_succ,
        Fin.cons_zero, Fin.cons_succ, List.prod_cons] using
        prod_mem_orderedFactorSpan g (Fin.cons k (fun i => a i.succ)) hdeg
    simpa only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, List.ofFn_succ, List.prod_cons, mul_assoc] using hk (hsame m (a 0))
  exact h hx

/-- Compressing a nondecreasing word uses only the single-index product laws and never
increases its weight. No exchange relations between distinct indices are needed here. -/
theorem prod_mem_orderedFactorSpan_of_pairwise
    (hzero : ∀ i, g i 0 = 1)
    (hsame : ∀ i m n, g i m * g i n ∈
      Submodule.span ℤ {x | ∃ k ≤ m + n, g i k = x})
    (l : List (Fin r × ℕ)) (hl : l.Pairwise (fun a b => a.1 ≤ b.1)) :
    (l.map fun p => g p.1 p.2).prod ∈ orderedFactorSpan g (l.map Prod.snd).sum := by
  induction r with
  | zero =>
    have he : l = [] := List.eq_nil_iff_forall_not_mem.2 fun p _ => Fin.elim0 p.1
    subst l
    simpa using prod_mem_orderedFactorSpan g (fun i => Fin.elim0 i) (by simp)
  | succ s ihr =>
    induction l with
    | nil => simpa [hzero] using prod_mem_orderedFactorSpan g 0 (by simp)
    | cons p l ihl =>
      by_cases hp : p.1 = 0
      · simp only [List.map_cons, List.prod_cons, List.sum_cons]
        rw [hp]
        exact mul_first_mem_orderedFactorSpan g (hsame 0) _ _ (ihl hl.tail)
      · have hnz : ∀ q ∈ p :: l, q.1 ≠ 0 := by
          intro q hq hq0
          have hpq : p.1 ≤ q.1 := by
            rcases List.mem_cons.1 hq with rfl | hq
            · exact le_rfl
            · exact (List.pairwise_cons.1 hl).1 q hq
          exact hp (le_antisymm (hq0 ▸ hpq) (Fin.zero_le _))
        let t := (p :: l).pmap (fun q hq => (q.1.pred hq, q.2)) hnz
        have ht : t.map (fun q => (q.1.succ, q.2)) = p :: l := by
          rw [List.map_pmap]
          apply List.pmap_eq_self.2
          intro q _
          simp only [Fin.succ_pred]
        have hsorted : t.Pairwise (fun a b => a.1 ≤ b.1) := by
          rw [← ht, List.pairwise_map] at hl
          simpa only [Fin.succ_le_succ_iff] using hl
        have hm := ihr (fun i n => g i.succ n) (fun i => hzero i.succ)
          (fun i => hsame i.succ) t hsorted
        have h : orderedFactorSpan (fun i n => g i.succ n) (t.map Prod.snd).sum ≤
            orderedFactorSpan g (t.map Prod.snd).sum := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨a, ha, rfl⟩
          simpa only [SetLike.mem_coe, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, hzero,
            one_mul, List.prod_cons] using prod_mem_orderedFactorSpan g (Fin.cons 0 a)
              (by simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_add] using ha)
        simpa only [← ht, List.map_map, Function.comp_def] using h hm

/-- Integral word straightening: bounded words and increasing products of bounded total
exponent have the same integral span. The two hypotheses separate distinct-index exchanges
from compression at a single index. -/
theorem weightedWordSpan_eq_orderedFactorSpan
    (hzero : ∀ i, g i 0 = 1)
    (hswap : ∀ i j, i < j → ∀ m n,
      g j m * g i n - g i n * g j m ∈
        weightedWordSpanLT (fun p : Fin r × ℕ => g p.1 p.2) Prod.snd (m + n))
    (hsame : ∀ i m n, g i m * g i n ∈
      Submodule.span ℤ {x | ∃ k ≤ m + n, g i k = x}) (d : ℕ) :
    weightedWordSpan (fun p : Fin r × ℕ => g p.1 p.2) Prod.snd d =
      orderedFactorSpan g d := by
  rw [weightedWordSpan_eq_span_sorted _ _ Prod.fst
    (fun a b hab => hswap b.1 a.1 hab a.2 b.2)]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨l, hl, hd, rfl⟩
    exact orderedFactorSpan_mono g hd (prod_mem_orderedFactorSpan_of_pairwise g hzero hsame l hl)
  · rintro _ ⟨a, ha, rfl⟩
    refine Submodule.subset_span ⟨List.ofFn (fun i => (i, a i)), ?_, ?_, ?_⟩
    · rw [List.pairwise_ofFn]
      intro i j hij
      exact hij.le
    · simpa only [List.map_ofFn, Function.comp_def, Fin.sum_ofFn] using ha
    · simp only [List.map_ofFn, Function.comp_def]

/-- Forgetting the bound gives precisely the span of all increasing products. -/
theorem iSup_orderedFactorSpan :
    ⨆ d, orderedFactorSpan g d = Submodule.span ℤ
      (Set.range fun a : Fin r → ℕ => (List.ofFn fun i => g i (a i)).prod) := by
  refine le_antisymm (iSup_le fun d => Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨a, _, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self a)
  · rintro _ ⟨a, rfl⟩
    exact Submodule.mem_iSup_of_mem (∑ i, a i) (prod_mem_orderedFactorSpan g a le_rfl)

/-- The unbounded ordered span is the integral module of the subring generated by all factors. -/
theorem span_orderedFactor_eq_subringClosure
    (hzero : ∀ i, g i 0 = 1)
    (hswap : ∀ i j, i < j → ∀ m n,
      g j m * g i n - g i n * g j m ∈
        weightedWordSpanLT (fun p : Fin r × ℕ => g p.1 p.2) Prod.snd (m + n))
    (hsame : ∀ i m n, g i m * g i n ∈
      Submodule.span ℤ {x | ∃ k ≤ m + n, g i k = x}) :
    Submodule.span ℤ (Set.range fun a : Fin r → ℕ => (List.ofFn fun i => g i (a i)).prod) =
      (Subring.closure (Set.range fun p : Fin r × ℕ => g p.1 p.2)).toAddSubgroup.toIntSubmodule :=
    by
  rw [← iSup_orderedFactorSpan]
  simp_rw [← weightedWordSpan_eq_orderedFactorSpan g hzero hswap hsame]
  rw [iSup_weightedWordSpan, Algebra.adjoin_int]
  rfl

/-- With no coordinates, the empty product still contributes the integral scalars. -/
@[simp]
theorem orderedFactorSpan_empty (g : Fin 0 → ℕ → A) (d : ℕ) :
    orderedFactorSpan g d = Submodule.span ℤ {(1 : A)} := by
  unfold orderedFactorSpan
  congr 1
  ext x
  simp

example (g : Fin 0 → ℕ → A) (d : ℕ) :
    weightedWordSpan (fun p : Fin 0 × ℕ => g p.1 p.2) Prod.snd d =
      Submodule.span ℤ {(1 : A)} := by
  rw [weightedWordSpan_eq_orderedFactorSpan g (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i), orderedFactorSpan_empty]

end FiniteFamily

end TauCeti
