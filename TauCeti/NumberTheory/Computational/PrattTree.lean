/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.List.Prime
public import Mathlib.Data.Set.List
public import Mathlib.NumberTheory.LucasPrimality
public import TauCeti.Data.Nat.Log

/-!
# Pratt primality certificates

A *Pratt tree* is a finite recursive certificate of primality. It is either the leaf `two`,
presenting the prime `2`, or a node `node n a cs` claiming that `n` is prime with Lucas witness
`a`, whose children `cs` present the prime factors of `n - 1`, repeated with multiplicity.

A tree is `PrattTree.Valid` when every node satisfies `PrattTree.NodeConditions`: `3 ≤ n`,
`0 < a < n`, the child values multiply to `n - 1`, `a ^ (n - 1) ≡ 1 (mod n)` and
`a ^ ((n - 1) / q) ≢ 1 (mod n)` for every child value `q`. All of these are arithmetic
conditions on natural numbers, checked independently of how the tree was found.

The bit size `PrattTree.bitSize` of a tree charges one tag bit per tree, and at each node the
binary lengths of `n`, `a` and the number of children; repeated children are charged repeatedly.

## Main results

* `TauCeti.Computational.PrattTree.Valid.prime_value`: the value of a valid Pratt tree is prime
  (soundness).
* `TauCeti.Computational.PrattTree.exists_valid_value_eq_bitSize_le`: every prime `n` is the
  value of a valid Pratt tree of bit size at most `10 * (Nat.log 2 n) ^ 2`.
* `TauCeti.Computational.PrattTree.exists_valid_value_eq`: every prime is the value of a valid
  Pratt tree (completeness).
* `TauCeti.Computational.PrattTree.prime_iff_exists_valid`: soundness and completeness combined.

Soundness is Lucas's primality test, `lucas_primality`, applied at each node: by induction the
child values are prime, so every prime divisor of their product `n - 1` is one of them.
Completeness follows from `reverse_lucas_primality` by strong induction on `n`. For an odd prime
`n` write `n - 1 = 2 * m`; the children are the leaf and trees for the prime factors of `m`. If
their logarithms add up to `s`, then `s + 1 ≤ Nat.log 2 n`, there are at most `s` such trees, and
by induction they cost at most `10 * s ^ 2` bits together, which leaves room for the header.

## References

* V. R. Pratt, *Every prime has a succinct certificate*, SIAM J. Comput. 4 (1975), 214–220.
* V. Chvátal, *Pratt's primality proofs*, lecture notes, pp. 1–4.
-/

public section

namespace TauCeti.Computational

/-- A Pratt tree: the leaf `two`, presenting `2`, or a node `node n a cs` claiming that `n` is
prime with Lucas witness `a`, whose children `cs` present the prime factors of `n - 1` with
multiplicity. Primality is not part of the data; it is a consequence of `PrattTree.Valid`. -/
inductive PrattTree where
  /-- The leaf, presenting the prime `2`. -/
  | two
  /-- A node with claimed value `n`, Lucas witness `a` and children `cs`. -/
  | node (n a : ℕ) (cs : List PrattTree)

namespace PrattTree

/-- The number presented by a Pratt tree: `2` at the leaf and the stored `n` at a node. -/
def value : PrattTree → ℕ
  | two => 2
  | node n _ _ => n

@[simp] theorem value_two : two.value = 2 := (rfl)

@[simp] theorem value_node (n a : ℕ) (cs : List PrattTree) : (node n a cs).value = n := (rfl)

/-- The bit size of a Pratt tree: one tag bit for the leaf, and at a node `node n a cs` one tag
bit, the binary lengths `Nat.log 2 x + 1` of `n`, `a` and the number of children, and the bit
sizes of all children, repeated children being charged repeatedly. -/
def bitSize : PrattTree → ℕ
  | two => 1
  | node n a cs => 1 + (Nat.log 2 n + 1) + (Nat.log 2 a + 1) + (Nat.log 2 cs.length + 1) +
      (cs.map bitSize).sum

@[simp] theorem bitSize_two : two.bitSize = 1 := by simp [bitSize]

@[simp] theorem bitSize_node (n a : ℕ) (cs : List PrattTree) :
    (node n a cs).bitSize = 1 + (Nat.log 2 n + 1) + (Nat.log 2 a + 1) +
      (Nat.log 2 cs.length + 1) + (cs.map bitSize).sum := by
  simp [bitSize]

/-- Every Pratt tree has positive bit size. -/
theorem bitSize_pos (c : PrattTree) : 0 < c.bitSize := by
  cases c <;> simp

/-- The arithmetic conditions checked at a Pratt node `node n a cs`: the bounds `3 ≤ n` and
`0 < a < n`, the product of the child values is `n - 1`, and the Lucas congruences
`a ^ (n - 1) ≡ 1 [MOD n]` and `a ^ ((n - 1) / q) ≢ 1 [MOD n]` for every child value `q`. -/
structure NodeConditions (n a : ℕ) (cs : List PrattTree) : Prop where
  /-- The claimed value is at least `3`. -/
  three_le : 3 ≤ n
  /-- The witness is positive. -/
  pos : 0 < a
  /-- The witness is less than the claimed value. -/
  lt : a < n
  /-- The child values multiply to `n - 1`. -/
  prod_map_value : (cs.map value).prod = n - 1
  /-- Fermat's congruence for the witness. -/
  pow_modEq : a ^ (n - 1) ≡ 1 [MOD n]
  /-- The witness fails the congruence for `(n - 1) / q` at every child value `q`. -/
  not_pow_div_modEq : ∀ c ∈ cs, ¬a ^ ((n - 1) / c.value) ≡ 1 [MOD n]

/-- Validity of a Pratt tree: the leaf is valid, and a node is valid when its arithmetic
conditions `PrattTree.NodeConditions` hold and all of its children are valid. -/
inductive Valid : PrattTree → Prop
  /-- The leaf is valid. -/
  | two : Valid two
  /-- A node is valid when its conditions hold and all of its children are valid. -/
  | node {n a : ℕ} {cs : List PrattTree} (h : NodeConditions n a cs)
      (hcs : ∀ c ∈ cs, Valid c) : Valid (node n a cs)

attribute [simp] Valid.two

@[simp] theorem valid_node_iff {n a : ℕ} {cs : List PrattTree} :
    (node n a cs).Valid ↔ NodeConditions n a cs ∧ ∀ c ∈ cs, c.Valid :=
  ⟨fun | .node h hcs => ⟨h, hcs⟩, fun ⟨h, hcs⟩ => .node h hcs⟩

/-- **Soundness of Pratt trees**: the value of a valid Pratt tree is prime. -/
theorem Valid.prime_value {c : PrattTree} (hc : c.Valid) : c.value.Prime := by
  induction hc with
  | two => exact Nat.prime_two
  | @node n a cs h _ ih =>
    refine lucas_primality n a (by exact_mod_cast (ZMod.natCast_eq_natCast_iff ..).2 h.pow_modEq)
      fun q hq hqn => ?_
    rw [← h.prod_map_value, (Nat.prime_iff.mp hq).dvd_prod_iff] at hqn
    obtain ⟨_, hmem, hqd⟩ := hqn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
    rw [(Nat.prime_dvd_prime_iff_eq hq (ih c hc)).mp hqd]
    exact_mod_cast mt (ZMod.natCast_eq_natCast_iff ..).1 (h.not_pow_div_modEq c hc)

/-- A node built from a Lucas witness `a` modulo `n ≥ 3` and valid children whose values
multiply to `n - 1` is valid. -/
private theorem valid_node_val {n : ℕ} [NeZero n] (hn : 3 ≤ n) {a : ZMod n}
    (ha : a ^ (n - 1) = 1) (had : ∀ q : ℕ, q.Prime → q ∣ n - 1 → a ^ ((n - 1) / q) ≠ 1)
    {cs : List PrattTree} (hcs : ∀ c ∈ cs, c.Valid) (hprod : (cs.map value).prod = n - 1) :
    (node n a.val cs).Valid := by
  have : Fact (1 < n) := ⟨by omega⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact zero_ne_one ((zero_pow (by omega)).symm.trans ha)
  refine .node ⟨hn, ZMod.val_pos.mpr ha0, ZMod.val_lt a, hprod, ?_, fun c hc => ?_⟩ hcs
  · rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, ZMod.natCast_zmod_val, ha, Nat.cast_one]
  · rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one]
    exact had _ (hcs c hc).prime_value (hprod ▸ List.dvd_prod (List.mem_map_of_mem hc))

/-- The total bit size of a list of Pratt trees, each of bit size at most `10 * Nat.log 2 q ^ 2`
for its value `q`, is at most `10 * s ^ 2`, where `s` is the sum of the logarithms of the
values. -/
private theorem sum_map_bitSize_le {cs : List PrattTree}
    (h : ∀ c ∈ cs, c.bitSize ≤ 10 * Nat.log 2 c.value ^ 2) :
    (cs.map bitSize).sum ≤ 10 * (cs.map fun c => Nat.log 2 c.value).sum ^ 2 := by
  set s := (cs.map fun c => Nat.log 2 c.value).sum
  calc (cs.map bitSize).sum ≤ (cs.map fun c => 10 * s * Nat.log 2 c.value).sum := by
        refine List.sum_le_sum fun c hc => (h c hc).trans ?_
        have : Nat.log 2 c.value ≤ s := List.le_sum_of_mem (List.mem_map_of_mem hc)
        rw [sq, ← mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
    _ = 10 * s ^ 2 := by rw [List.sum_map_mul_left, sq, mul_assoc]

/-- The size estimate behind the quadratic bound: if `n - 1 = 2 * m` with `m ≠ 0`, `a < n`, and
the trees `ds` present the prime factors of `m`, each `d` of bit size at most
`10 * Nat.log 2 d.value ^ 2`, then the node `node n a (two :: ds)` has bit size at most
`10 * Nat.log 2 n ^ 2`. -/
private theorem bitSize_node_two_cons_le {n a m : ℕ} (hm : n - 1 = 2 * m) (hm0 : m ≠ 0)
    (ha : a < n) {ds : List PrattTree} (hmap : ds.map value = m.primeFactorsList)
    (hds : ∀ d ∈ ds, d.bitSize ≤ 10 * Nat.log 2 d.value ^ 2) :
    (node n a (two :: ds)).bitSize ≤ 10 * Nat.log 2 n ^ 2 := by
  -- With `s` the sum of the logarithms of the prime factors of `m`, the children other than the
  -- leaf cost at most `10 * s ^ 2`, there are at most `s` of them, and `s + 1 ≤ Nat.log 2 n`.
  set s := (ds.map fun d => Nat.log 2 d.value).sum
  have hsum : (ds.map bitSize).sum ≤ 10 * s ^ 2 := sum_map_bitSize_le hds
  have hs : s + 1 ≤ Nat.log 2 n := by
    have h1 := Nat.sum_map_log_le_log_prod 2 (l := ds.map value) (by simp [hmap])
    rw [List.map_map, hmap, Nat.prod_primeFactorsList hm0] at h1
    have h2 : Nat.log 2 m + 1 ≤ Nat.log 2 n := by
      rw [← Nat.log_mul_base one_lt_two hm0, mul_comm, ← hm]
      exact Nat.log_mono_right (by omega)
    exact (Nat.add_le_add_right h1 1).trans h2
  have hlen : ds.length ≤ s := by
    have := List.length_le_sum_of_one_le (ds.map fun d => Nat.log 2 d.value) fun _ hq => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      have : d.value ∈ m.primeFactorsList := hmap ▸ List.mem_map_of_mem hd
      exact Nat.log_pos one_lt_two (Nat.prime_of_mem_primeFactorsList this).two_le
    simpa using this
  have hloga : Nat.log 2 a ≤ Nat.log 2 n := Nat.log_mono_right ha.le
  have hlogk : Nat.log 2 (ds.length + 1) < ds.length + 1 := Nat.log_lt_self 2 (by omega)
  simp only [bitSize_node, List.length_cons, List.map_cons, List.sum_cons, bitSize_two]
  nlinarith

/-- **Completeness of Pratt trees with a size bound**: every prime `n` is the value of a valid
Pratt tree of bit size at most `10 * (Nat.log 2 n) ^ 2`. -/
theorem exists_valid_value_eq_bitSize_le {n : ℕ} (hn : n.Prime) :
    ∃ c : PrattTree, c.Valid ∧ c.value = n ∧ c.bitSize ≤ 10 * Nat.log 2 n ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain rfl | hn3 : n = 2 ∨ 3 ≤ n := by have := hn.two_le; omega
  · refine ⟨two, .two, rfl, ?_⟩
    rw [bitSize_two, Nat.log_eq_one_iff.2 (by norm_num)]
    norm_num
  have : NeZero n := ⟨by omega⟩
  -- Write `n - 1 = 2 * m`; the children are the leaf and small trees for the prime factors of `m`.
  obtain ⟨m, hm⟩ : 2 ∣ n - 1 := (hn.even_sub_one (by omega)).two_dvd
  have hm0 : m ≠ 0 := by omega
  obtain ⟨cs, hcs⟩ : m.primeFactorsList ∈ Set.range (List.map fun c :
      {c : PrattTree // c.Valid ∧ c.bitSize ≤ 10 * Nat.log 2 c.value ^ 2} => c.val.value) := by
    rw [Set.range_list_map]
    intro q hq
    obtain ⟨c, hc, rfl, hsize⟩ := ih q (by have := Nat.le_of_mem_primeFactorsList hq; omega)
      (Nat.prime_of_mem_primeFactorsList hq)
    exact ⟨⟨c, hc, hsize⟩, rfl⟩
  have hmap : (cs.map Subtype.val).map value = m.primeFactorsList := by
    simpa [Function.comp_def] using hcs
  obtain ⟨a, ha, had⟩ := reverse_lucas_primality n hn
  refine ⟨node n a.val (two :: cs.map Subtype.val), valid_node_val hn3 ha had ?_ ?_, rfl,
    bitSize_node_two_cons_le hm hm0 (ZMod.val_lt a) hmap ?_⟩
  · simp only [List.mem_cons, List.mem_map, forall_eq_or_imp]
    exact ⟨.two, by rintro _ ⟨d, -, rfl⟩; exact d.property.1⟩
  · rw [List.map_cons, List.prod_cons, hmap, Nat.prod_primeFactorsList hm0, value_two, hm]
  · rintro _ hd
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hd
    exact d.property.2

/-- **Completeness of Pratt trees**: every prime is the value of a valid Pratt tree. -/
theorem exists_valid_value_eq {n : ℕ} (hn : n.Prime) : ∃ c : PrattTree, c.Valid ∧ c.value = n :=
  let ⟨c, hc, hcn, _⟩ := exists_valid_value_eq_bitSize_le hn
  ⟨c, hc, hcn⟩

/-- A natural number is prime exactly when it is the value of a valid Pratt tree. -/
theorem prime_iff_exists_valid {n : ℕ} : n.Prime ↔ ∃ c : PrattTree, c.Valid ∧ c.value = n :=
  ⟨exists_valid_value_eq, fun ⟨_, hc, hcn⟩ => hcn ▸ hc.prime_value⟩

/-! ### Examples -/

/-- The node `(3, 2, [two])` is a valid Pratt tree, of bit size `7`. -/
example : (node 3 2 [two]).Valid ∧ (node 3 2 [two]).bitSize = 7 := by
  refine ⟨.node ⟨le_rfl, two_pos, by norm_num, rfl, by decide, ?_⟩ (by simp), ?_⟩
  · simp only [List.mem_singleton, forall_eq, value_two]
    decide
  have h2 : Nat.log 2 2 = 1 := Nat.log_eq_one_iff.2 (by norm_num)
  have h3 : Nat.log 2 3 = 1 := Nat.log_eq_one_iff.2 (by norm_num)
  simp [h2, h3]

/-- The node `(9, 2, [two, two, two])` is not valid, although its child values multiply to
`8`: indeed `2 ^ 8 ≡ 4 [MOD 9]`. -/
example : ¬(node 9 2 [two, two, two]).Valid := fun h =>
  absurd (valid_node_iff.mp h).1.pow_modEq (by decide)

end PrattTree

end TauCeti.Computational
