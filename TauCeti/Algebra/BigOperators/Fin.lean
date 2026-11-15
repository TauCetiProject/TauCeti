/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import TauCeti.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.OfFn
import TauCeti.Algebra.BigOperators.Finset.PartialSum
import TauCeti.Data.Fin.Basic

/-!
# Sums and products over `Fin n`

Successive differences along a finite sequence sum to the difference of its endpoints,
including the empty edge sequence. Reversing every difference reverses the endpoint difference.
The equivalence omitting the last index also reindexes sums by the preceding indices, and a
filtered product over `Fin (n + 1)` splits off its first index; when two such products agree and
so do their first factors, the products over the remaining indices agree.

Along a divisibility chain `d₀ ∣ d₁ ∣ ⋯`, the product of the first `k` entries divides the
product of the entries at any `k` distinct positions. This is what makes the leading `k × k`
minors of a diagonal matrix with chained entries the smallest ones in divisibility.

A tuple is determined by its leading partial sums `∑_{j < k} a j`, and in a canonically ordered
monoid each of them is at most the total. These are the facts about the dominance order of
exponent vectors (compare leading partial sums) that triangular expansions in Hecke rings use.

A product over the pairs `Fin 2 → α` is the double product over their two entries. A double sum
over pairs of paths `Fin (i + 1) → X` and `Fin (j + 1) → X` meeting at an endpoint is a sum over
the paths of length `i + j` (`Fin.sum_sum_ite_apply_last_eq_apply_zero`). A sum over the pairs
`(a, b)` with `P a` and a fixed second entry `b` is the sum over the `a` with `P a`.

A strictly increasing list `a` on `Fin (n + 1)` in an additive group with a preorder (no
compatibility between the two is needed) telescopes (`StrictMono.eq_add_sum_ite_sub`): `a k` is
`a 0` plus the gaps below `a k`, and a finset sum of values in the list is the cardinality times
`a 0` plus, for each gap, the number of elements above its lower threshold times the gap
(`StrictMono.sum_eq_card_nsmul_add_sum_card_filter_nsmul_sub`).

Mathlib's `finSigmaFinEquiv` places the pair `⟨i, k⟩`, `k < m i`, at `∑_{i' < i} m i' + k`
(`val_finSigmaFinEquiv_eq_sum_filter`), so pairs with an earlier first entry come earlier
(`finSigmaFinEquiv_lt_of_fst_lt`). Read as the positions of `r` consecutive blocks of lengths
`m i`, the cyclic successor `finRotate` moves inside a block to the next position of that block
(`Fin.finRotate_finSigmaFinEquiv_of_lt`), and from the last position of a block to the first
position of the cyclically next block, when that block is nonempty
(`Fin.finRotate_finSigmaFinEquiv_of_eq`). The list of values of a function on `Fin (∑ i, m i)`
is the concatenation of the lists of its values on the blocks (`List.ofFn_sum`), as `List.ofFn_mul`
says for blocks of equal length.
-/

public section

namespace Fin

/-- Successive differences telescope to the endpoint difference. -/
theorem sum_univ_succ_sub_castSucc {G : Type*} [AddCommGroup G] {n : ℕ}
    (f : Fin (n + 1) → G) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (last n) - f 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have hIic : Finset.Iic (last n) = Finset.univ := Finset.Iic_top
    simpa only [hIic, succ_last] using sum_Iic_sub (last n) f

/-- Reversed successive differences telescope to the reversed endpoint difference. -/
theorem sum_univ_castSucc_sub_succ {G : Type*} [AddCommGroup G] {n : ℕ}
    (f : Fin (n + 1) → G) :
    ∑ i : Fin n, (f i.castSucc - f i.succ) = f 0 - f (last n) := by
  simpa only [neg_sub_neg] using sum_univ_succ_sub_castSucc (fun i ↦ -f i)

-- Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Chris Birkbeck), Apache-2.0, at
-- commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
-- `LeanModularForms/HeckeRIngs/GLn/DiagonalCosets.lean`, where it is a step in the uniqueness of
-- the Smith normal form; generalized here from `ℤ` to any commutative monoid.
/-- **The leading entries of a divisibility chain divide any equally many entries.** Along a
chain `d₀ ∣ d₁ ∣ ⋯`, the product of the first `k` entries divides the product of the entries
at any `k` distinct positions. -/
theorem prod_castLE_dvd_prod_of_injective {M : Type*} [CommMonoid M] {n : ℕ} {d : Fin n → M}
    (hd : ∀ ⦃i j : Fin n⦄, i ≤ j → d i ∣ d j) {k : ℕ} (hk : k ≤ n) {f : Fin k → Fin n}
    (hf : Function.Injective f) :
    ∏ j : Fin k, d (castLE hk j) ∣ ∏ j : Fin k, d (f j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- the position `f j₀` of largest index is at least `k`, by injectivity
    obtain ⟨j₀, -, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun j ↦ (f j : ℕ)) Finset.univ_nonempty
    have hge : k ≤ (f j₀ : ℕ) := by
      by_contra hlt
      push Not at hlt
      have := Fintype.card_le_of_injective
        (fun j : Fin (k + 1) ↦ (⟨f j, (hmax j (Finset.mem_univ _)).trans_lt hlt⟩ : Fin k))
        (fun j₁ j₂ heq ↦ hf (Fin.ext (mk.inj heq)))
      simp at this
    rw [prod_univ_castSucc, prod_univ_succAbove _ j₀, mul_comm (d (f j₀))]
    exact mul_dvd_mul (ih (by omega) (hf.comp succAbove_right_injective))
      (hd (le_def.mpr hge))

/-- **A tuple is determined by its leading partial sums.** If the sums of the first `k` entries
of `a` and `b` agree for every `k ≤ n`, then `a = b`: entry `i` is what the sum of the first
`i + 1` entries adds to the sum of the first `i`. -/
theorem eq_of_forall_sum_castLE_eq {M : Type*} [AddCommMonoid M] [IsLeftCancelAdd M] {n : ℕ}
    {a b : Fin n → M}
    (h : ∀ (k : ℕ) (hk : k ≤ n), ∑ j : Fin k, a (castLE hk j) = ∑ j : Fin k, b (castLE hk j)) :
    a = b := by
  funext i
  have h₁ := h (i + 1) i.isLt
  simp only [sum_univ_castSucc, castLE_castSucc] at h₁
  rw [h i i.isLt.le] at h₁
  exact (congrArg a (Fin.ext rfl)).trans ((add_left_cancel h₁).trans (congrArg b (Fin.ext rfl)))

/-- A leading partial sum of a tuple in a canonically ordered monoid is at most its total. -/
theorem sum_castLE_le_sum {M : Type*} [AddCommMonoid M] [Preorder M] [CanonicallyOrderedAdd M]
    {n k : ℕ} (hk : k ≤ n) (f : Fin n → M) :
    ∑ j : Fin k, f (castLE hk j) ≤ ∑ i, f i :=
  calc ∑ j : Fin k, f (castLE hk j) = ∑ i ∈ Finset.univ.map (castLEEmb hk), f i := by simp
    _ ≤ ∑ i, f i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- A product over the indices of `Fin (n + 1)` satisfying a predicate splits off the first
index. -/
@[to_additive /-- A sum over the indices of `Fin (n + 1)` satisfying a predicate splits off the
first index. -/]
theorem prod_filter_univ_succ {M : Type*} [CommMonoid M] {n : ℕ} (P : Fin (n + 1) → Prop)
    [DecidablePred P] (f : Fin (n + 1) → M) :
    ∏ i with P i, f i = (if P 0 then f 0 else 1) * ∏ i : Fin n with P i.succ, f i.succ := by
  rw [Finset.prod_filter, prod_univ_succ, Finset.prod_filter]

/-- If two filtered products over `Fin (n + 1)` agree, and their first factors are nonzero and
equal whenever the first index is selected, then the filtered products over the remaining indices
agree. -/
theorem prod_filter_succ_eq_of_prod_filter_eq {M : Type*} [CommMonoidWithZero M]
    [IsLeftCancelMulZero M] {n : ℕ}
    (P : Fin (n + 1) → Prop) [DecidablePred P] {f g : Fin (n + 1) → M}
    (h : ∏ i with P i, f i = ∏ i with P i, g i) (hf : P 0 → f 0 ≠ 0) (h0 : P 0 → f 0 = g 0) :
    ∏ i : Fin n with P i.succ, f i.succ = ∏ i : Fin n with P i.succ, g i.succ := by
  rw [prod_filter_univ_succ, prod_filter_univ_succ] at h
  by_cases hP : P 0
  · simp only [hP, ↓reduceIte, h0 hP] at h
    exact mul_left_cancel₀ (h0 hP ▸ hf hP) h
  · simpa only [hP, ↓reduceIte, one_mul] using h

/-- **Concatenating paths.** The pairs of paths `x` of length `i` and `y` of length `j` in `X`
with the end point of `x` the starting point of `y` are the paths `w` of length `i + j`, split at
the vertex `wᵢ`. -/
theorem sum_sum_ite_apply_last_eq_apply_zero {X N : Type*} [Fintype X] [DecidableEq X]
    [AddCommMonoid N] {i j n : ℕ} (h : i + j = n)
    (g : (Fin (i + 1) → X) → (Fin (j + 1) → X) → N) :
    ∑ x : Fin (i + 1) → X, ∑ y : Fin (j + 1) → X,
        (if x (last i) = y 0 then g x y else 0) =
      ∑ w : Fin (n + 1) → X,
        g (fun t => w ⟨t, by have := t.isLt; omega⟩)
          (fun t => w ⟨i + t, by have := t.isLt; omega⟩) := by
  rw [← Finset.sum_product', ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun w => ((fun t => w ⟨t, by have := t.isLt; omega⟩),
      fun t => w ⟨i + t, by have := t.isLt; omega⟩))
    (fun p t => if ht : (t : ℕ) ≤ i then p.1 ⟨t, by omega⟩
      else p.2 ⟨t - i, by have := t.isLt; omega⟩)
    (fun w _ => by simp [val_last]) (fun _ _ => Finset.mem_univ _) (fun w _ => ?_)
    (fun p hp => ?_) (fun _ _ => rfl)
  · funext t
    split_ifs with ht
    · rfl
    · dsimp only
      exact congrArg w (Fin.ext (by simp only; omega))
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    refine Prod.ext (funext fun t => ?_) (funext fun t => ?_)
    · simp [show (t : ℕ) ≤ i by have := t.isLt; omega]
    · by_cases ht : (t : ℕ) = 0
      · have h0 : t = 0 := Fin.ext ht
        subst h0
        have hi : (⟨i, by omega⟩ : Fin (i + 1)) = last i := Fin.ext (val_last i).symm
        simpa [hi] using hp
      · simp only [show ¬ (i + t ≤ i) by omega, dite_false]
        exact congrArg p.2 (Fin.ext (by simp))

end Fin

namespace Fintype

/-- A sum over the pairs `(a, b)` with `P a` and second entry `b` is the sum of the values at
`(a, b)` over the `a` with `P a`. -/
theorem sum_filter_and_snd_eq {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [AddCommMonoid M] (h : α × β → M) (P : α → Prop) [DecidablePred P] (b : β) :
    ∑ x ∈ Finset.univ.filter (fun x : α × β ↦ P x.1 ∧ x.2 = b), h x =
      ∑ a ∈ Finset.univ.filter P, h (a, b) := by
  rw [Finset.sum_filter, Finset.sum_filter, sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases hP : P a <;> simp [hP]

/-- **A product over the pairs `Fin 2 → α`** is the double product over their two entries. -/
@[to_additive /-- **A sum over the pairs `Fin 2 → α`** is the double sum over their two
entries. -/]
theorem prod_finTwoArrow {α M : Type*} [Fintype α] [CommMonoid M] (f : (Fin 2 → α) → M) :
    ∏ w, f w = ∏ p, ∏ q, f ![p, q] := by
  rw [← (finTwoArrowEquiv α).symm.prod_comp, prod_prod_type]
  rfl

end Fintype

/-- The position of the pair `⟨i, k⟩` in the lexicographic order is `∑_{i' < i} m i' + k`. -/
theorem val_finSigmaFinEquiv_eq_sum_filter {r : ℕ} {m : Fin r → ℕ}
    (x : (i : Fin r) × Fin (m i)) :
    (finSigmaFinEquiv x : ℕ) = ∑ i ∈ Finset.univ.filter (· < x.1), m i + x.2 := by
  rw [finSigmaFinEquiv_apply]
  congr 1
  refine (Finset.sum_map Finset.univ (Fin.castLEEmb x.1.2.le) m).symm.trans
    (congrArg (fun s : Finset (Fin r) => s.sum m) ?_)
  ext t
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.coe_castLEEmb, Finset.mem_filter]
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun h => ⟨⟨t, h⟩, rfl⟩⟩

/-- A pair with an earlier first entry comes earlier in the lexicographic order. -/
theorem finSigmaFinEquiv_lt_of_fst_lt {r : ℕ} {m : Fin r → ℕ} {x y : (i : Fin r) × Fin (m i)}
    (h : x.1 < y.1) : finSigmaFinEquiv x < finSigmaFinEquiv y := by
  rw [Fin.lt_def, val_finSigmaFinEquiv_eq_sum_filter, val_finSigmaFinEquiv_eq_sum_filter]
  have hsub : insert x.1 (Finset.univ.filter (· < x.1)) ⊆ Finset.univ.filter (· < y.1) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rcases ht with rfl | ht
    · exact h
    · exact ht.trans h
  have := Finset.sum_le_sum_of_subset (f := m) hsub
  rw [Finset.sum_insert (by simp)] at this
  have := x.2.2
  omega

namespace Fin

open TauCeti

variable {r : ℕ} {m : Fin r → ℕ}

/-- The position of `⟨i, j⟩` in the concatenation is the total length of the blocks before `i`,
plus `j`. -/
private theorem coe_finSigmaFinEquiv (i : Fin r) (j : Fin (m i)) :
    (finSigmaFinEquiv ⟨i, j⟩ : ℕ) = prefixSum i m + j := by
  rw [finSigmaFinEquiv_apply, prefixSum_eq_sum_castLE i.2.le]

/-- Inside a block, the cyclic successor of a position is the next position of that block. -/
theorem finRotate_finSigmaFinEquiv_of_lt (i : Fin r) (j : Fin (m i)) (h : (j : ℕ) + 1 < m i) :
    finRotate _ (finSigmaFinEquiv ⟨i, j⟩) = finSigmaFinEquiv ⟨i, ⟨j + 1, h⟩⟩ := by
  apply Fin.ext
  have hlt := (finSigmaFinEquiv ⟨i, ⟨j + 1, h⟩⟩).is_lt
  rw [Fin.coe_finRotate_eq_ite, coe_finSigmaFinEquiv, coe_finSigmaFinEquiv]
  rw [coe_finSigmaFinEquiv] at hlt
  simp only at hlt ⊢
  split_ifs <;> omega

/-- The cyclic successor of the last position of a block is the first position `j'` of the
cyclically next block; the existence of `j'` says that this block is nonempty. -/
theorem finRotate_finSigmaFinEquiv_of_eq (i : Fin r) (j : Fin (m i)) (h : (j : ℕ) + 1 = m i)
    (j' : Fin (m (finRotate r i))) (hj' : (j' : ℕ) = 0) :
    finRotate _ (finSigmaFinEquiv ⟨i, j⟩) = finSigmaFinEquiv ⟨finRotate r i, j'⟩ := by
  apply Fin.ext
  have hlt := (finSigmaFinEquiv ⟨finRotate r i, j'⟩).is_lt
  have hstep : prefixSum (i + 1) m = prefixSum i m + m i := prefixSum_succ i.2 m
  rw [Fin.coe_finRotate_eq_ite, coe_finSigmaFinEquiv, coe_finSigmaFinEquiv]
  rw [coe_finSigmaFinEquiv] at hlt
  rw [Fin.coe_finRotate_eq_ite i] at hlt ⊢
  by_cases hi : (i : ℕ) + 1 = r
  · rw [hi, prefixSum_of_le le_rfl] at hstep
    simp only [hi, ite_true, prefixSum_zero]
    split_ifs <;> omega
  · simp only [hi, ite_false] at hlt ⊢
    split_ifs <;> omega

end Fin

namespace List

/-- The list of values of a function on the concatenation of blocks of lengths `m i` is the
concatenation of the lists of its values on the blocks. -/
theorem ofFn_sum {α : Type*} {r : ℕ} {m : Fin r → ℕ} (f : Fin (∑ i, m i) → α) :
    ofFn f = (ofFn fun i => ofFn fun j => f (finSigmaFinEquiv ⟨i, j⟩)).flatten := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ofFn_congr (Fin.sum_univ_castSucc m), ofFn_add, ofFn_succ', concat_eq_append,
      flatten_append, flatten_singleton, ih]
    congr 3 <;> funext i
    · congr 1
      funext j
      congr 1
      ext
      simp [finSigmaFinEquiv_apply]
    · congr 1
      ext
      simp [finSigmaFinEquiv_apply]
      -- The two sums agree term by term: `Fin.castSucc` and `Fin.castLE` keep the value.
      rfl

end List

namespace TauCeti

/-- Reindex a sum over all indices except the last by the preceding finite ordinal. -/
theorem sum_finSuccAboveEquiv_last {M : Type*} [AddCommMonoid M] (n : ℕ)
    (z : {i : Fin (n + 1) // i ≠ Fin.last n} → M) :
    ∑ i : Fin n, z ⟨i.castSucc, Fin.castSucc_ne_last i⟩ = ∑ j, z j := by
  simpa only [finSuccAboveEquiv_last_apply] using
    Equiv.sum_comp (finSuccAboveEquiv (Fin.last n)) z

end TauCeti

namespace StrictMono

/-- Telescoping a strictly increasing list `a` in an additive group with a preorder expresses
`a k` as `a 0` plus the successive gaps below `a k`. -/
theorem eq_add_sum_ite_sub {R : Type*} [AddCommGroup R] [Preorder R] [DecidableLT R] {n : ℕ}
    {a : Fin (n + 1) → R} (ha : StrictMono a)
    (k : Fin (n + 1)) : a k = a 0 +
      ∑ j : Fin n, if a j.castSucc < a k then a j.succ - a j.castSucc else 0 := by
  simp_rw [ha.lt_iff_lt]
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp
  · simp only [Fin.castSucc_lt_succ_iff]
    rw [← Finset.sum_filter]
    have heq : Finset.univ.filter (fun j : Fin n ↦ j ≤ k) = Finset.Iic k := by
      ext j; simp
    rw [heq, Fin.sum_Iic_sub]
    rw [add_sub_cancel]

/-- When a finite strictly increasing list in an additive group with a preorder contains the
values of `c` on a finset `b`, the sum of `c` over `b` is its cardinality times `a 0` plus, for
each successive gap, the number of elements above its lower threshold times the gap. -/
theorem sum_eq_card_nsmul_add_sum_card_filter_nsmul_sub {R : Type*} [AddCommGroup R] [Preorder R]
    [DecidableLT R]
    {n : ℕ} {a : Fin (n + 1) → R}
    (ha : StrictMono a) {ι : Type*} {c : ι → R}
    (b : Finset ι) (hc : ∀ i ∈ b, c i ∈ Set.range a) :
    (∑ i ∈ b, c i) = b.card • a 0 +
      ∑ j : Fin n, (b.filter fun i ↦ a j.castSucc < c i).card • (a j.succ - a j.castSucc) := by
  classical
  have hci (i : ι) (hi : i ∈ b) : c i = a 0 +
      ∑ j : Fin n, if a j.castSucc < c i then a j.succ - a j.castSucc else 0 := by
    obtain ⟨k, hk⟩ := hc i hi
    simpa only [hk] using ha.eq_add_sum_ite_sub k
  calc
    (∑ i ∈ b, c i) = ∑ i ∈ b, (a 0 +
        ∑ j : Fin n, if a j.castSucc < c i then a j.succ - a j.castSucc else 0) :=
      Finset.sum_congr rfl hci
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      · simp
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← Finset.sum_filter, Finset.sum_const]

end StrictMono
