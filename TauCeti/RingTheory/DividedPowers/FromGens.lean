/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import TauCeti.Data.Nat.Choose.Vandermonde

/-!
# Divided powers from identities on generators

An *additive divided power structure* on an ideal `I` of a commutative semiring `A` is a family of
operations `dpow : ℕ → A → A`, vanishing outside `I`, that satisfies the additive, homogeneity,
degree-zero, degree-one, and ideal-membership axioms of `DividedPowers I`, without assuming the
multiplication identity (`mul_dpow`) or the iteration identity (`dpow_comp`).

This file proves the generator criterion for divided powers (Stacks Project, Lemma 23.2.4, tag
`07GP`): if `I = Ideal.span S` and an `AdditiveDividedPowers I` satisfies `mul_dpow` and
`dpow_comp` on every generator `s ∈ S`, then both identities hold on all of `I` and the candidate
upgrades to a `DividedPowers I` structure with the exact same operations.

The multiplication identity propagates through sums by Vandermonde's identity
(`Nat.add_choose_eq`). The iteration identity propagates through sums by expanding
`dpow m (dpow n (x + y))` into a universal `ℕ`-linear combination of products
`dpow a x * dpow (m * n - a) y` (`a ≤ m * n`) and evaluating the natural-number coefficients once
in the polynomial ring `MvPolynomial (Fin 2) ℚ`, where `DividedPowers.RatAlgebra.dividedPowers`
already satisfies `dpow_comp` and monomials are linearly independent. No injectivity into a
`ℚ`-algebra, freeness, or nilpotence hypothesis is imposed on `A`.

We also record a witness over `TrivSqZeroExt (ZMod 2) (ZMod 2)` showing that an
`AdditiveDividedPowers` structure need not satisfy `mul_dpow`, so the generator hypotheses cannot
be omitted.

## Main definitions and results

* `TauCeti.AdditiveDividedPowers`: candidate divided power operations on an ideal `I` satisfying
  all axioms of `DividedPowers I` except `mul_dpow` and `dpow_comp`.
* `DividedPowers.toAdditiveDividedPowers`: forgetful map from `DividedPowers I` to
  `TauCeti.AdditiveDividedPowers I`.
* `TauCeti.AdditiveDividedPowers.mul_dpow_add`: stability of `mul_dpow` under addition.
* `TauCeti.AdditiveDividedPowers.mul_dpow_of_span`: propagation of `mul_dpow` from a generating
  set to the whole ideal.
* `TauCeti.AdditiveDividedPowers.dpow_comp_add`: stability of `dpow_comp` under addition.
* `TauCeti.AdditiveDividedPowers.dpow_comp_of_span`: propagation of `dpow_comp` from a generating
  set to the whole ideal.
* `TauCeti.AdditiveDividedPowers.toDividedPowers`: constructs `DividedPowers I` from an
  `AdditiveDividedPowers I` satisfying `mul_dpow` and `dpow_comp` on a generating set of `I`.
* `TauCeti.AdditiveDividedPowers.exists_not_dividedPowers`: existence of an
  `AdditiveDividedPowers` structure that does not underlie any `DividedPowers` structure.

## References

* [Stacks: Divided power algebra, Lemma 07GP](https://stacks.math.columbia.edu/tag/07GP).
* P. Berthelot, *Cohomologie cristalline des schémas de caractéristique $p > 0$*, Lecture Notes in
  Math. 407 (1974), I.1.
* Mathlib's `DividedPowers`, from the divided powers formalization of A. Chambert-Loir and
  M. I. de Frutos-Fernández.
-/

public section

open Finset Nat Ideal

namespace TauCeti

variable {A : Type*} [CommSemiring A] (I : Ideal A)

/-- An *additive divided power structure* on an ideal `I` of a commutative semiring `A`: a family
of maps `dpow : ℕ → A → A`, vanishing outside `I`, satisfying the degree-zero, degree-one,
ideal-membership, addition, and scalar-homogeneity axioms of `DividedPowers I`, without assuming
`mul_dpow` or `dpow_comp`. -/
structure AdditiveDividedPowers where
  /-- The underlying operation `ℕ → A → A`, extended by `0` outside `I`. -/
  dpow : ℕ → A → A
  /-- The operation vanishes outside `I` in every degree. -/
  dpow_null : ∀ {n x}, x ∉ I → dpow n x = 0
  /-- The degree-zero operation is `1` on `I`. -/
  dpow_zero : ∀ {x}, x ∈ I → dpow 0 x = 1
  /-- The degree-one operation is the identity on `I`. -/
  dpow_one : ∀ {x}, x ∈ I → dpow 1 x = x
  /-- Positive-degree operations preserve membership in `I`. -/
  dpow_mem : ∀ {n x}, n ≠ 0 → x ∈ I → dpow n x ∈ I
  /-- The additive (binomial) law on `I`. -/
  dpow_add : ∀ {n x y}, x ∈ I → y ∈ I →
    dpow n (x + y) = ∑ k ∈ antidiagonal n, dpow k.1 x * dpow k.2 y
  /-- Scalar homogeneity of degree `n` on `I`. -/
  dpow_mul : ∀ {n} {a x : A}, x ∈ I → dpow n (a * x) = a ^ n * dpow n x

attribute [simp] AdditiveDividedPowers.dpow_null AdditiveDividedPowers.dpow_zero
  AdditiveDividedPowers.dpow_one

/-- Coercion from an additive divided power structure to its underlying family of maps. -/
instance : CoeFun (AdditiveDividedPowers I) fun _ ↦ ℕ → A → A := ⟨fun hI ↦ hI.dpow⟩

variable {I}

/-- Forget `mul_dpow` and `dpow_comp` to view a `DividedPowers` structure as an
`AdditiveDividedPowers` structure with the exact same operations. -/
def _root_.DividedPowers.toAdditiveDividedPowers (hI : DividedPowers I) :
    AdditiveDividedPowers I where
  dpow := hI.dpow
  dpow_null := hI.dpow_null
  dpow_zero := hI.dpow_zero
  dpow_one := hI.dpow_one
  dpow_mem := hI.dpow_mem
  dpow_add := hI.dpow_add
  dpow_mul := hI.dpow_mul

/-- `toAdditiveDividedPowers` preserves the underlying divided power operations identically. -/
@[simp]
theorem _root_.DividedPowers.toAdditiveDividedPowers_dpow (hI : DividedPowers I) :
    hI.toAdditiveDividedPowers.dpow = hI.dpow := by
  rfl

/-- Two `DividedPowers` structures are equal if and only if their underlying
`AdditiveDividedPowers` structures are equal. -/
@[simp]
theorem _root_.DividedPowers.toAdditiveDividedPowers_inj {hI hI' : DividedPowers I} :
    hI.toAdditiveDividedPowers = hI'.toAdditiveDividedPowers ↔ hI = hI' :=
  ⟨fun h ↦ DividedPowers.ext hI hI' fun n x _ ↦
    congrFun (congrFun (congrArg AdditiveDividedPowers.dpow h) n) x,
   fun h ↦ h ▸ rfl⟩

namespace AdditiveDividedPowers

/-- Two additive divided power structures on `I` are equal if their operations agree on `I`. -/
@[ext]
theorem ext (hI hI' : AdditiveDividedPowers I)
    (h : ∀ (n : ℕ) {x : A}, x ∈ I → hI.dpow n x = hI'.dpow n x) : hI = hI' := by
  obtain ⟨f, hf₀, _, _, _, _, _⟩ := hI
  obtain ⟨g, hg₀, _, _, _, _, _⟩ := hI'
  simp only [mk.injEq]
  funext n x
  by_cases hx : x ∈ I
  · exact h n hx
  · rw [hf₀ hx, hg₀ hx]

/-- The coercion `AdditiveDividedPowers I → (ℕ → A → A)` is injective. -/
theorem coe_injective :
    Function.Injective (fun h : AdditiveDividedPowers I ↦ (h : ℕ → A → A)) := fun _ _ h ↦ by
  ext n x _
  exact congrFun (congrFun h n) x

variable (hI : AdditiveDividedPowers I)

/-- Variant of `dpow_add` indexed by `Finset.range (n + 1)`. -/
theorem dpow_add' {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    hI.dpow n (x + y) = ∑ k ∈ range (n + 1), hI.dpow k x * hI.dpow (n - k) y := by
  rw [hI.dpow_add hx hy, sum_antidiagonal_eq_sum_range_succ_mk]

/-- Scalar homogeneity with the scalar on the right. -/
theorem dpow_mul_right {n : ℕ} {a x : A} (hx : x ∈ I) :
    hI.dpow n (x * a) = hI.dpow n x * a ^ n := by
  rw [mul_comm, hI.dpow_mul hx, mul_comm]

/-- Positive-degree additive divided powers vanish at `0`. -/
@[simp]
theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := by
  rw [← MulZeroClass.mul_zero (0 : A), hI.dpow_mul I.zero_mem, zero_pow hn, zero_mul, zero_mul]

/-- The multinomial expansion of an additive divided power of a finite sum. -/
theorem dpow_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) {n : ℕ} :
    hI.dpow n (∑ i ∈ s, x i) =
      ∑ k ∈ s.sym n, ∏ i ∈ s, hI.dpow (Multiset.count i k) (x i) :=
  DividedPowers.dpow_sum' hI.dpow hI.dpow_zero hI.dpow_add hI.dpow_eval_zero hx

/-! ### Propagation of the multiplication identity -/

/-- The multiplication identity holds automatically at `0`. -/
theorem mul_dpow_zero (m n : ℕ) :
    hI.dpow m 0 * hI.dpow n 0 = ((m + n).choose m : A) * hI.dpow (m + n) 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hI.dpow_zero I.zero_mem]
  · rw [hI.dpow_eval_zero hm, zero_mul, hI.dpow_eval_zero (by omega), mul_zero]

/-- The multiplication identity is preserved under multiplication by any scalar `a : A`. -/
theorem mul_dpow_mul {x : A} (hx : x ∈ I) (a : A) {m n : ℕ}
    (h : hI.dpow m x * hI.dpow n x = ((m + n).choose m : A) * hI.dpow (m + n) x) :
    hI.dpow m (a * x) * hI.dpow n (a * x) =
      ((m + n).choose m : A) * hI.dpow (m + n) (a * x) := by
  rw [hI.dpow_mul hx, hI.dpow_mul hx, hI.dpow_mul hx]
  calc
    a ^ m * hI.dpow m x * (a ^ n * hI.dpow n x)
        = a ^ (m + n) * (hI.dpow m x * hI.dpow n x) := by rw [pow_add]; ring
    _ = a ^ (m + n) * (((m + n).choose m : A) * hI.dpow (m + n) x) := by rw [h]
    _ = ((m + n).choose m : A) * (a ^ (m + n) * hI.dpow (m + n) x) := by ring

/-- The multiplication identity is stable under addition: if `mul_dpow` holds for all degrees at
`x ∈ I` and at `y ∈ I`, then it holds for all degrees at `x + y`. -/
theorem mul_dpow_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmx : ∀ m n, hI.dpow m x * hI.dpow n x = ((m + n).choose m : A) * hI.dpow (m + n) x)
    (hmy : ∀ m n, hI.dpow m y * hI.dpow n y = ((m + n).choose m : A) * hI.dpow (m + n) y)
    (m n : ℕ) :
    hI.dpow m (x + y) * hI.dpow n (x + y) =
      ((m + n).choose m : A) * hI.dpow (m + n) (x + y) := by
  rw [hI.dpow_add hx hy, hI.dpow_add hx hy, hI.dpow_add hx hy, sum_mul_sum, ← sum_product',
    Finset.mul_sum]
  have hterm :
      ∑ pq ∈ antidiagonal m ×ˢ antidiagonal n,
        hI.dpow pq.1.1 x * hI.dpow pq.1.2 y * (hI.dpow pq.2.1 x * hI.dpow pq.2.2 y) =
      ∑ pq ∈ antidiagonal m ×ˢ antidiagonal n,
        (((pq.1.1 + pq.2.1).choose pq.1.1 * (pq.1.2 + pq.2.2).choose pq.1.2 : ℕ) : A) *
          (hI.dpow (pq.1.1 + pq.2.1) x * hI.dpow (pq.1.2 + pq.2.2) y) := by
    refine Finset.sum_congr rfl fun pq _ ↦ ?_
    calc
      hI.dpow pq.1.1 x * hI.dpow pq.1.2 y * (hI.dpow pq.2.1 x * hI.dpow pq.2.2 y)
          = (hI.dpow pq.1.1 x * hI.dpow pq.2.1 x) * (hI.dpow pq.1.2 y * hI.dpow pq.2.2 y) := by
            ring
      _ = (((pq.1.1 + pq.2.1).choose pq.1.1 : A) * hI.dpow (pq.1.1 + pq.2.1) x) *
            (((pq.1.2 + pq.2.2).choose pq.1.2 : A) * hI.dpow (pq.1.2 + pq.2.2) y) := by
            rw [hmx, hmy]
      _ = (((pq.1.1 + pq.2.1).choose pq.1.1 * (pq.1.2 + pq.2.2).choose pq.1.2 : ℕ) : A) *
            (hI.dpow (pq.1.1 + pq.2.1) x * hI.dpow (pq.1.2 + pq.2.2) y) := by
            rw [Nat.cast_mul]; ring
  rw [hterm]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun pq : (ℕ × ℕ) × (ℕ × ℕ) ↦ (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2))
    (t := antidiagonal (m + n))]
  · refine Finset.sum_congr rfl fun r hr ↦ ?_
    have hr_sum : r.1 + r.2 = m + n := mem_antidiagonal.mp hr
    have hinner :
        ∑ pq ∈ (antidiagonal m ×ˢ antidiagonal n).filter
            (fun pq ↦ (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) = r),
          (((pq.1.1 + pq.2.1).choose pq.1.1 * (pq.1.2 + pq.2.2).choose pq.1.2 : ℕ) : A) *
            (hI.dpow (pq.1.1 + pq.2.1) x * hI.dpow (pq.1.2 + pq.2.2) y) =
        ((∑ pq ∈ (antidiagonal m ×ˢ antidiagonal n).filter
            (fun pq ↦ (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) = r),
          r.1.choose pq.1.1 * r.2.choose pq.1.2 : ℕ) : A) *
          (hI.dpow r.1 x * hI.dpow r.2 y) := by
      rw [Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun pq hpq ↦ ?_
      have heq := (mem_filter.mp hpq).2
      have h1 : pq.1.1 + pq.2.1 = r.1 := congrArg Prod.fst heq
      have h2 : pq.1.2 + pq.2.2 = r.2 := congrArg Prod.snd heq
      rw [h1, h2]
    rw [hinner, sum_filter_antidiagonal_choose m n r.1 r.2 hr_sum]
  · intro pq hpq
    simp only [mem_product, mem_antidiagonal] at hpq ⊢
    omega

/-- If `mul_dpow` holds on a generating set `S` of `I`, then it holds on all of `I`. -/
theorem mul_dpow_of_span {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, hI.dpow m s * hI.dpow n s = ((m + n).choose m : A) * hI.dpow (m + n) s)
    {m n : ℕ} {x : A} (hx : x ∈ I) :
    hI.dpow m x * hI.dpow n x = ((m + n).choose m : A) * hI.dpow (m + n) x := by
  suffices ∀ z ∈ Ideal.span S, ∀ k l,
      hI.dpow k z * hI.dpow l z = ((k + l).choose k : A) * hI.dpow (k + l) z from
    this x (hS ▸ hx) m n
  intro z hz
  induction hz using Submodule.span_induction with
  | mem s hs => exact hmul s hs
  | zero => exact hI.mul_dpow_zero
  | add x y hxS hyS ihx ihy =>
    exact hI.mul_dpow_add (hS ▸ hxS) (hS ▸ hyS) ihx ihy
  | smul a x hxS ihx =>
    exact fun k l ↦ hI.mul_dpow_mul (hS ▸ hxS) a (ihx k l)

/-- A product of additive divided powers at an element `x ∈ I` satisfying `mul_dpow` reduces to a
multinomial coefficient times a single divided power. -/
theorem prod_dpow {ι : Type*} {s : Finset ι} {n : ι → ℕ} {x : A} (hx : x ∈ I)
    (hmul : ∀ m k, hI.dpow m x * hI.dpow k x = ((m + k).choose m : A) * hI.dpow (m + k) x) :
    ∏ i ∈ s, hI.dpow (n i) x = (Nat.multinomial s n : A) * hI.dpow (∑ i ∈ s, n i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [hI.dpow_zero hx]
  | insert a s ha ih =>
    rw [prod_insert ha, ih, ← mul_assoc, mul_comm (hI.dpow (n a) x), mul_assoc, hmul,
      ← sum_insert ha, ← mul_assoc]
    congr 1
    rw [Nat.multinomial_insert ha, mul_comm, Nat.cast_mul, sum_insert ha]

/-! ### Propagation of the iteration identity -/

/-- The iteration identity holds automatically at `0`. -/
theorem dpow_comp_zero (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    hI.dpow m (hI.dpow n 0) = (Nat.uniformBell m n : A) * hI.dpow (m * n) 0 := by
  rw [hI.dpow_eval_zero hn]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hI.dpow_zero I.zero_mem, Nat.uniformBell_zero_left]
  · rw [hI.dpow_eval_zero hm, hI.dpow_eval_zero (mul_ne_zero hm hn), mul_zero]

/-- The iteration identity is preserved under multiplication by any scalar `a : A`. -/
theorem dpow_comp_mul {x : A} (hx : x ∈ I) (a : A) {m n : ℕ} (hn : n ≠ 0)
    (h : hI.dpow m (hI.dpow n x) = (Nat.uniformBell m n : A) * hI.dpow (m * n) x) :
    hI.dpow m (hI.dpow n (a * x)) = (Nat.uniformBell m n : A) * hI.dpow (m * n) (a * x) := by
  rw [hI.dpow_mul hx, hI.dpow_mul (hI.dpow_mem hn hx), h, hI.dpow_mul hx, ← pow_mul, mul_comm n m]
  ring

private def iterTermCoeff (n c i : ℕ) : ℕ :=
  if i = 0 then Nat.uniformBell c n
  else Nat.uniformBell c i * Nat.multinomial (range c) (fun _ ↦ n - i)

private def iterWeightX {m : ℕ} (n : ℕ) (k : Sym ℕ m) : ℕ :=
  ∑ i ∈ range (n + 1), Multiset.count i (k : Multiset ℕ) * i

private def iterWeightY {m : ℕ} (n : ℕ) (k : Sym ℕ m) : ℕ :=
  ∑ i ∈ range (n + 1), Multiset.count i (k : Multiset ℕ) * (n - i)

private def iterSymCoeff {m : ℕ} (n : ℕ) (k : Sym ℕ m) : ℕ :=
  (∏ i ∈ range (n + 1), iterTermCoeff n (Multiset.count i (k : Multiset ℕ)) i) *
    Nat.multinomial (range (n + 1)) (fun i ↦ Multiset.count i (k : Multiset ℕ) * i) *
    Nat.multinomial (range (n + 1)) (fun i ↦ Multiset.count i (k : Multiset ℕ) * (n - i))

private def iterTotalCoeff (m n a : ℕ) : ℕ :=
  ∑ k ∈ ((range (n + 1)).sym m).filter (fun k ↦ iterWeightX n k = a), iterSymCoeff n k

private lemma iterWeightX_add_iterWeightY {m n : ℕ} {k : Sym ℕ m}
    (hk : k ∈ (range (n + 1)).sym m) :
    iterWeightX n k + iterWeightY n k = m * n := by
  rw [iterWeightX, iterWeightY, ← Finset.sum_add_distrib]
  have hterm :
      ∑ i ∈ range (n + 1),
        (Multiset.count i (k : Multiset ℕ) * i + Multiset.count i (k : Multiset ℕ) * (n - i)) =
      ∑ i ∈ range (n + 1), Multiset.count i (k : Multiset ℕ) * n := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [← mul_add, Nat.add_sub_of_le hin]
  rw [hterm, ← Finset.sum_mul, Multiset.sum_count_eq_card]
  · rw [Sym.card_coe]
  · intro a ha
    exact Finset.mem_sym_iff.mp hk a ha

private lemma dpow_mul_term {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmy : ∀ m n, hI.dpow m y * hI.dpow n y = ((m + n).choose m : A) * hI.dpow (m + n) y)
    (hcx : ∀ m n, n ≠ 0 → hI.dpow m (hI.dpow n x) = (Nat.uniformBell m n : A) * hI.dpow (m * n) x)
    (hcy : ∀ m n, n ≠ 0 → hI.dpow m (hI.dpow n y) = (Nat.uniformBell m n : A) * hI.dpow (m * n) y)
    {n : ℕ} (hn : n ≠ 0) (c i : ℕ) :
    hI.dpow c (hI.dpow i x * hI.dpow (n - i) y) =
      (iterTermCoeff n c i : A) * (hI.dpow (c * i) x * hI.dpow (c * (n - i)) y) := by
  by_cases hi : i = 0
  · subst hi
    simp only [iterTermCoeff, ↓reduceIte, Nat.sub_zero, mul_zero, hI.dpow_zero hx, one_mul]
    exact hcy c n hn
  · simp only [iterTermCoeff, hi, ↓reduceIte, Nat.cast_mul]
    rw [hI.dpow_mul_right (hI.dpow_mem hi hx), hcx c i hi]
    have hpow :
        hI.dpow (n - i) y ^ c =
          (Nat.multinomial (range c) (fun _ ↦ n - i) : A) * hI.dpow (c * (n - i)) y := by
      have h := hI.prod_dpow (s := range c) (n := fun _ ↦ n - i) hy hmy
      simpa only [Finset.prod_const, Finset.card_range, Finset.sum_const, smul_eq_mul] using h
    rw [hpow]
    ring

private lemma dpow_comp_add_universal {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmx : ∀ m n, hI.dpow m x * hI.dpow n x = ((m + n).choose m : A) * hI.dpow (m + n) x)
    (hmy : ∀ m n, hI.dpow m y * hI.dpow n y = ((m + n).choose m : A) * hI.dpow (m + n) y)
    (hcx : ∀ m n, n ≠ 0 → hI.dpow m (hI.dpow n x) = (Nat.uniformBell m n : A) * hI.dpow (m * n) x)
    (hcy : ∀ m n, n ≠ 0 → hI.dpow m (hI.dpow n y) = (Nat.uniformBell m n : A) * hI.dpow (m * n) y)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    hI.dpow m (hI.dpow n (x + y)) =
      ∑ a ∈ range (m * n + 1),
        (iterTotalCoeff m n a : A) * (hI.dpow a x * hI.dpow (m * n - a) y) := by
  have hmem : ∀ i ∈ range (n + 1), hI.dpow i x * hI.dpow (n - i) y ∈ I := by
    intro i _
    by_cases hi : i = 0
    · subst hi
      rw [hI.dpow_zero hx, one_mul, Nat.sub_zero]
      exact hI.dpow_mem hn hy
    · exact I.mul_mem_right _ (hI.dpow_mem hi hx)
  rw [hI.dpow_add' hx hy, hI.dpow_sum hmem]
  have hprod :
      ∑ k ∈ (range (n + 1)).sym m,
        ∏ i ∈ range (n + 1), hI.dpow (Multiset.count i k) (hI.dpow i x * hI.dpow (n - i) y) =
      ∑ k ∈ (range (n + 1)).sym m,
        (iterSymCoeff n k : A) * (hI.dpow (iterWeightX n k) x * hI.dpow (iterWeightY n k) y) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hstep :
        ∏ i ∈ range (n + 1), hI.dpow (Multiset.count i k) (hI.dpow i x * hI.dpow (n - i) y) =
        (∏ i ∈ range (n + 1), (iterTermCoeff n (Multiset.count i k) i : A)) *
          ((∏ i ∈ range (n + 1), hI.dpow (Multiset.count i k * i) x) *
            ∏ i ∈ range (n + 1), hI.dpow (Multiset.count i k * (n - i)) y) := by
      simp_rw [hI.dpow_mul_term hx hy hmy hcx hcy hn, Finset.prod_mul_distrib]
    rw [hstep, hI.prod_dpow hx hmx, hI.prod_dpow hy hmy, iterSymCoeff, iterWeightX, iterWeightY]
    simp only [Nat.cast_mul, Nat.cast_prod]
    ring
  rw [hprod]
  rw [← Finset.sum_fiberwise_of_maps_to (g := iterWeightX n) (t := range (m * n + 1))]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [iterTotalCoeff, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rcases mem_filter.mp hk with ⟨hk_sym, hkx⟩
    have hky : iterWeightY n k = m * n - a := by
      have hsum := iterWeightX_add_iterWeightY hk_sym
      omega
    rw [hkx, hky]
  · intro k hk
    have hsum := iterWeightX_add_iterWeightY hk
    exact mem_range.mpr (by omega)

private lemma iterTotalCoeff_eq_uniformBell (m : ℕ) {n : ℕ} (hn : n ≠ 0) {a : ℕ} (ha : a ≤ m * n) :
    iterTotalCoeff m n a = Nat.uniformBell m n := by
  classical
  let γ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
    DividedPowers.RatAlgebra.dividedPowers ⊤
  let X0 : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 0
  let X1 : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 1
  have huniv :=
    γ.toAdditiveDividedPowers.dpow_comp_add_universal (x := X0) (y := X1)
      Submodule.mem_top Submodule.mem_top
      (fun p q ↦ γ.mul_dpow Submodule.mem_top)
      (fun p q ↦ γ.mul_dpow Submodule.mem_top)
      (fun p q hq ↦ γ.dpow_comp hq Submodule.mem_top)
      (fun p q hq ↦ γ.dpow_comp hq Submodule.mem_top) m hn
  have hcomp :
      γ.dpow m (γ.dpow n (X0 + X1)) =
        ∑ p ∈ range (m * n + 1),
          (Nat.uniformBell m n : MvPolynomial (Fin 2) ℚ) *
            (γ.dpow p X0 * γ.dpow (m * n - p) X1) := by
    rw [γ.dpow_comp hn Submodule.mem_top, γ.dpow_add' Submodule.mem_top Submodule.mem_top,
      Finset.mul_sum]
  have heq :
      ∑ p ∈ range (m * n + 1),
        (iterTotalCoeff m n p : MvPolynomial (Fin 2) ℚ) *
          (γ.dpow p X0 * γ.dpow (m * n - p) X1) =
      ∑ p ∈ range (m * n + 1),
        (Nat.uniformBell m n : MvPolynomial (Fin 2) ℚ) *
          (γ.dpow p X0 * γ.dpow (m * n - p) X1) :=
    huniv.symm.trans hcomp
  let d : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 (m * n - a)
  have hcoeff_prod : ∀ p q : ℕ,
      (γ.dpow p X0 * γ.dpow q X1).coeff d =
        if p = a ∧ q = m * n - a then (p ! : ℚ)⁻¹ * (q ! : ℚ)⁻¹ else 0 := by
    intro p q
    have hX0 : γ.dpow p X0 = ((p ! : ℚ)⁻¹ : ℚ) • X0 ^ p := by
      simpa [Ring.inverse_eq_inv'] using
        DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) γ
          (n := p) (x := X0) Submodule.mem_top
    have hX1 : γ.dpow q X1 = ((q ! : ℚ)⁻¹ : ℚ) • X1 ^ q := by
      simpa [Ring.inverse_eq_inv'] using
        DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) γ
          (n := q) (x := X1) Submodule.mem_top
    rw [hX0, hX1, smul_mul_smul_comm, MvPolynomial.coeff_smul, smul_eq_mul]
    have hmon : X0 ^ p * X1 ^ q =
        MvPolynomial.monomial (Finsupp.single 0 p + Finsupp.single 1 q) (1 : ℚ) := by
      simp only [X0, X1, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
        one_mul]
    rw [hmon, MvPolynomial.coeff_monomial]
    have hiff : Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q = d ↔
        p = a ∧ q = m * n - a := by
      constructor
      · intro h
        exact ⟨by simpa [d] using congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) h,
          by simpa [d] using congrArg (fun f : Fin 2 →₀ ℕ ↦ f 1) h⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    rw [if_congr hiff rfl rfl]
    split_ifs <;> simp
  have hcoeff_sum : ∀ f : ℕ → ℕ,
      (∑ p ∈ range (m * n + 1),
        (f p : MvPolynomial (Fin 2) ℚ) * (γ.dpow p X0 * γ.dpow (m * n - p) X1)).coeff d =
      (f a : ℚ) * ((a ! : ℚ)⁻¹ * ((m * n - a)! : ℚ)⁻¹) := by
    intro f
    rw [MvPolynomial.coeff_sum, Finset.sum_eq_single a]
    · have hnat : (f a : MvPolynomial (Fin 2) ℚ) = MvPolynomial.C (f a : ℚ) := by simp
      rw [hnat, MvPolynomial.coeff_C_mul, hcoeff_prod]
      simp
    · intro p _ hpa
      have hnat : (f p : MvPolynomial (Fin 2) ℚ) = MvPolynomial.C (f p : ℚ) := by simp
      rw [hnat, MvPolynomial.coeff_C_mul, hcoeff_prod]
      simp [hpa]
    · intro ha'
      exact absurd (mem_range.mpr (Nat.lt_succ_of_le ha)) ha'
  have hval := congrArg (fun p : MvPolynomial (Fin 2) ℚ ↦ p.coeff d) heq
  rw [hcoeff_sum (iterTotalCoeff m n), hcoeff_sum (fun _ ↦ Nat.uniformBell m n)] at hval
  have hne : (a ! : ℚ)⁻¹ * ((m * n - a)! : ℚ)⁻¹ ≠ 0 :=
    mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
  exact Nat.cast_injective (R := ℚ) (mul_right_cancel₀ hne hval)

/-- The iteration identity is stable under addition: if `mul_dpow` and `dpow_comp` hold at `x ∈ I`
and at `y ∈ I`, then `dpow_comp` holds at `x + y`. -/
theorem dpow_comp_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmx : ∀ m n, hI.dpow m x * hI.dpow n x = ((m + n).choose m : A) * hI.dpow (m + n) x)
    (hmy : ∀ m n, hI.dpow m y * hI.dpow n y = ((m + n).choose m : A) * hI.dpow (m + n) y)
    (hcx : ∀ m n, n ≠ 0 → hI.dpow m (hI.dpow n x) = (Nat.uniformBell m n : A) * hI.dpow (m * n) x)
    (hcy : ∀ m n, n ≠ 0 → hI.dpow m (hI.dpow n y) = (Nat.uniformBell m n : A) * hI.dpow (m * n) y)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    hI.dpow m (hI.dpow n (x + y)) = (Nat.uniformBell m n : A) * hI.dpow (m * n) (x + y) := by
  rw [hI.dpow_comp_add_universal hx hy hmx hmy hcx hcy m hn]
  have hcongr :
      ∑ a ∈ range (m * n + 1),
        (iterTotalCoeff m n a : A) * (hI.dpow a x * hI.dpow (m * n - a) y) =
      ∑ a ∈ range (m * n + 1),
        (Nat.uniformBell m n : A) * (hI.dpow a x * hI.dpow (m * n - a) y) := by
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [iterTotalCoeff_eq_uniformBell m hn (Nat.lt_succ_iff.mp (mem_range.mp ha))]
  rw [hcongr, ← Finset.mul_sum, ← hI.dpow_add' hx hy]

/-- If `mul_dpow` holds on `I` and `dpow_comp` holds on a generating set `S` of `I`, then
`dpow_comp` holds on all of `I`. -/
theorem dpow_comp_of_span {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ x ∈ I, ∀ m n, hI.dpow m x * hI.dpow n x = ((m + n).choose m : A) * hI.dpow (m + n) x)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
      hI.dpow m (hI.dpow n s) = (Nat.uniformBell m n : A) * hI.dpow (m * n) s)
    {m n : ℕ} (hn : n ≠ 0) {x : A} (hx : x ∈ I) :
    hI.dpow m (hI.dpow n x) = (Nat.uniformBell m n : A) * hI.dpow (m * n) x := by
  suffices ∀ z ∈ Ideal.span S, ∀ k l, l ≠ 0 →
      hI.dpow k (hI.dpow l z) = (Nat.uniformBell k l : A) * hI.dpow (k * l) z from
    this x (hS ▸ hx) m n hn
  intro z hz
  induction hz using Submodule.span_induction with
  | mem s hs => exact hcomp s hs
  | zero => exact fun k l hl ↦ hI.dpow_comp_zero k hl
  | add x y hxS hyS ihx ihy =>
    exact fun k l hl ↦ hI.dpow_comp_add (hS ▸ hxS) (hS ▸ hyS)
      (hmul x (hS ▸ hxS)) (hmul y (hS ▸ hyS)) ihx ihy k hl
  | smul a x hxS ihx =>
    exact fun k l hl ↦ hI.dpow_comp_mul (hS ▸ hxS) a hl (ihx k l hl)

/-! ### Construction of `DividedPowers` from generators -/

/-- Stacks Project, Lemma 23.2.4 (tag `07GP`): an additive divided power structure on an ideal
`I = Ideal.span S` that satisfies `mul_dpow` and `dpow_comp` on every generator `s ∈ S` upgrades to
a `DividedPowers I` structure with the exact same operations. -/
def toDividedPowers {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, hI.dpow m s * hI.dpow n s = ((m + n).choose m : A) * hI.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
      hI.dpow m (hI.dpow n s) = (Nat.uniformBell m n : A) * hI.dpow (m * n) s) :
    DividedPowers I where
  dpow := hI.dpow
  dpow_null := hI.dpow_null
  dpow_zero := hI.dpow_zero
  dpow_one := hI.dpow_one
  dpow_mem := hI.dpow_mem
  dpow_add := hI.dpow_add
  dpow_mul := hI.dpow_mul
  mul_dpow hx := hI.mul_dpow_of_span hS hmul hx
  dpow_comp hn hx :=
    hI.dpow_comp_of_span hS (fun _ hx _ _ ↦ hI.mul_dpow_of_span hS hmul hx) hcomp hn hx

/-- `toDividedPowers` preserves the underlying divided power operations identically. -/
@[simp]
theorem toDividedPowers_dpow {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, hI.dpow m s * hI.dpow n s = ((m + n).choose m : A) * hI.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
      hI.dpow m (hI.dpow n s) = (Nat.uniformBell m n : A) * hI.dpow (m * n) s) :
    (hI.toDividedPowers hS hmul hcomp).dpow = hI.dpow := by
  rfl

/-- Applying `toAdditiveDividedPowers` after `toDividedPowers` recovers the original candidate. -/
@[simp]
theorem toDividedPowers_toAdditiveDividedPowers {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, hI.dpow m s * hI.dpow n s = ((m + n).choose m : A) * hI.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
      hI.dpow m (hI.dpow n s) = (Nat.uniformBell m n : A) * hI.dpow (m * n) s) :
    (hI.toDividedPowers hS hmul hcomp).toAdditiveDividedPowers = hI := by
  ext n x _
  rfl

/-- Any `DividedPowers I` whose operations agree with `hI` on `I` equals `hI.toDividedPowers`. -/
theorem toDividedPowers_unique {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, hI.dpow m s * hI.dpow n s = ((m + n).choose m : A) * hI.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
      hI.dpow m (hI.dpow n s) = (Nat.uniformBell m n : A) * hI.dpow (m * n) s)
    {hI' : DividedPowers I} (h : ∀ n, ∀ x ∈ I, hI'.dpow n x = hI.dpow n x) :
    hI' = hI.toDividedPowers hS hmul hcomp :=
  DividedPowers.ext hI' _ fun n _ hx ↦ h n _ hx

/-- `toDividedPowers` does not depend on the choice of generating set `S` or identity proofs. -/
theorem toDividedPowers_eq_of_span {S₁ S₂ : Set A}
    (hS₁ : I = Ideal.span S₁) (hS₂ : I = Ideal.span S₂)
    (hmul₁ : ∀ s ∈ S₁, ∀ m n,
      hI.dpow m s * hI.dpow n s = ((m + n).choose m : A) * hI.dpow (m + n) s)
    (hcomp₁ : ∀ s ∈ S₁, ∀ m n, n ≠ 0 →
      hI.dpow m (hI.dpow n s) = (Nat.uniformBell m n : A) * hI.dpow (m * n) s)
    (hmul₂ : ∀ s ∈ S₂, ∀ m n,
      hI.dpow m s * hI.dpow n s = ((m + n).choose m : A) * hI.dpow (m + n) s)
    (hcomp₂ : ∀ s ∈ S₂, ∀ m n, n ≠ 0 →
      hI.dpow m (hI.dpow n s) = (Nat.uniformBell m n : A) * hI.dpow (m * n) s) :
    hI.toDividedPowers hS₁ hmul₁ hcomp₁ = hI.toDividedPowers hS₂ hmul₂ hcomp₂ :=
  DividedPowers.ext _ _ fun _ _ _ ↦ rfl

/-- Applying `toDividedPowers` to the additive candidate of an existing `DividedPowers I`
recovers that structure. -/
@[simp]
theorem _root_.DividedPowers.toAdditiveDividedPowers_toDividedPowers (hI : DividedPowers I)
    {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n,
      hI.toAdditiveDividedPowers.dpow m s * hI.toAdditiveDividedPowers.dpow n s =
        ((m + n).choose m : A) * hI.toAdditiveDividedPowers.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
      hI.toAdditiveDividedPowers.dpow m (hI.toAdditiveDividedPowers.dpow n s) =
        (Nat.uniformBell m n : A) * hI.toAdditiveDividedPowers.dpow (m * n) s) :
    hI.toAdditiveDividedPowers.toDividedPowers hS hmul hcomp = hI :=
  DividedPowers.ext _ _ fun _ _ _ ↦ rfl

/-! ### Strictness of `AdditiveDividedPowers` -/

/-- Not every `AdditiveDividedPowers` structure underlies a `DividedPowers` structure: on the
dual numbers `𝔽₂[ε]/(ε²)` with `I = (ε)`, the family `δ₀ = 1`, `δ₁ = δ₃ = id`, and `δₙ = 0` for
`n = 2` and `n ≥ 4` satisfies all additive divided power axioms, yet fails `mul_dpow` at
`m = 1, n = 2` because `δ₁(ε) * δ₂(ε) = 0 ≠ ε = 3 * δ₃(ε)`. -/
theorem exists_not_dividedPowers :
    ∃ hI : AdditiveDividedPowers (Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)}),
      hI.dpow 1 (TrivSqZeroExt.inr 1) * hI.dpow 2 (TrivSqZeroExt.inr 1) ≠
        (((1 + 2).choose 1 : ℕ) : TrivSqZeroExt (ZMod 2) (ZMod 2)) *
          hI.dpow (1 + 2) (TrivSqZeroExt.inr 1) ∧
      ∀ h : DividedPowers (Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)}), h.dpow ≠ hI.dpow := by
  classical
  let I : Ideal (TrivSqZeroExt (ZMod 2) (ZMod 2)) := Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)}
  have hmem_iff : ∀ x : TrivSqZeroExt (ZMod 2) (ZMod 2), x ∈ I ↔ x.fst = 0 := by
    intro x
    constructor
    · intro hx
      rw [Ideal.mem_span_singleton] at hx
      rcases hx with ⟨a, rfl⟩
      simp
    · intro hx
      rw [Ideal.mem_span_singleton]
      refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
      ext
      · simp [hx]
      · simp
  have hmul_zero : ∀ {x y : TrivSqZeroExt (ZMod 2) (ZMod 2)}, x ∈ I → y ∈ I → x * y = 0 := by
    intro x y hx hy
    have hx0 := (hmem_iff x).mp hx
    have hy0 := (hmem_iff y).mp hy
    ext <;> simp [hx0, hy0]
  let f : ℕ → TrivSqZeroExt (ZMod 2) (ZMod 2) → TrivSqZeroExt (ZMod 2) (ZMod 2) := fun n x ↦
    if x ∈ I then
      match n with
      | 0 => 1
      | 1 => x
      | 3 => x
      | _ => 0
    else 0
  have hf_mem : ∀ {n : ℕ} {x : TrivSqZeroExt (ZMod 2) (ZMod 2)}, n ≠ 0 → x ∈ I → f n x ∈ I := by
    intro n x hn hx
    match n with
    | 0 => exact absurd rfl hn
    | 1 | 2 | 3 | _ + 4 => simp [f, hx]
  let hI : AdditiveDividedPowers I := {
    dpow := f
    dpow_null := fun hx ↦ by simp [f, hx]
    dpow_zero := fun hx ↦ by simp [f, hx]
    dpow_one := fun hx ↦ by simp [f, hx]
    dpow_mem := hf_mem
    dpow_add := fun {n x y} hx hy ↦ by
      have hxy : x + y ∈ I := I.add_mem hx hy
      match n with
      | 0 => simp [f, hx, hy, hxy]
      | 1 =>
        rw [Finset.Nat.sum_antidiagonal_succ]
        simp [f, hx, hy, hxy, add_comm]
      | k + 2 =>
        rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
        have hmid : ∑ p ∈ antidiagonal k, f (p.1 + 1) x * f (p.2 + 1) y = 0 :=
          Finset.sum_eq_zero fun p _ ↦
            hmul_zero (hf_mem p.1.succ_ne_zero hx) (hf_mem p.2.succ_ne_zero hy)
        rw [hmid, add_zero]
        match k with
        | 0 | 1 => simp [f, hx, hy, hxy, add_comm]
        | _ + 2 => simp [f, hx, hy, hxy]
    dpow_mul := fun {n a x} hx ↦ by
      have hax : a * x ∈ I := I.mul_mem_left a hx
      match n with
      | 0 | 1 | 2 | _ + 4 => simp [f, hx, hax]
      | 3 =>
        simp only [f, hx, hax, ↓reduceIte]
        have hx0 := (hmem_iff x).mp hx
        have hcube : a.fst * a.fst * a.fst = a.fst := by
          have : ∀ u : ZMod 2, u * u * u = u := by decide
          exact this a.fst
        ext
        · simp [hx0]
        · simp [hx0, pow_succ, hcube]
  }
  have hε : TrivSqZeroExt.inr (1 : ZMod 2) ∈ I := Ideal.subset_span rfl
  have hlhs : hI.dpow 1 (TrivSqZeroExt.inr 1) * hI.dpow 2 (TrivSqZeroExt.inr 1) = 0 := by
    simp [hI, f, hε]
  have hrhs : (((1 + 2).choose 1 : ℕ) : TrivSqZeroExt (ZMod 2) (ZMod 2)) *
      hI.dpow (1 + 2) (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1 := by
    simp only [hI, f, hε, ↓reduceIte]
    have h3 : (((1 + 2).choose 1 : ℕ) : TrivSqZeroExt (ZMod 2) (ZMod 2)) = 1 := by
      ext <;> decide
    rw [h3, one_mul]
  have hne : hI.dpow 1 (TrivSqZeroExt.inr 1) * hI.dpow 2 (TrivSqZeroExt.inr 1) ≠
      (((1 + 2).choose 1 : ℕ) : TrivSqZeroExt (ZMod 2) (ZMod 2)) *
        hI.dpow (1 + 2) (TrivSqZeroExt.inr 1) := by
    rw [hlhs, hrhs]
    exact fun h01 ↦ zero_ne_one (congrArg TrivSqZeroExt.snd h01)
  refine ⟨hI, hne, fun h hh ↦ hne ?_⟩
  have hmul := h.mul_dpow (m := 1) (n := 2) hε
  rwa [hh] at hmul

end AdditiveDividedPowers

end TauCeti
