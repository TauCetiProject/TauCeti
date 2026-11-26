/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Ungraded
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.OneStrand
import Mathlib.Data.Fin.Tuple.Take
import TauCeti.Data.Fin.Tuple.Basic
import Mathlib.Tactic.LinearCombination

/-!
# One-generator type `A` modules over the one-strand algebra

Let `M` be a matching on a finite linearly ordered set `α`, and `A` the summand
`TauCeti.StrandsAlgebra.matchedSummand R M 1` of the matched algebra with one strand, over a ring
`R` of characteristic two. Fix three points `k < i < j` such that `i` is the only point strictly
between `k` and `j`, and `k` and `j` are matched. The three chords `ρ_ij`, `ρ_kj` and `ρ_ki` then
satisfy `ρ_ki ρ_ij = ρ_kj`, and `ρ_kj` is not the product of two other chords.

This file constructs the `A∞` right module structure on `R` with one generator `x`
(`TauCeti.StrandsAlgebra.threePointTypeA`) whose only nonzero operations are

* `m₂(x, I(i)) = x`, for the idempotent `I(i)` of the pair of `i`, and
* `m_{n+3}(x, ρ_ij, ρ_kj, …, ρ_kj, ρ_ki) = x`, with `n` copies of `ρ_kj`, for every `n ≥ 0`,

extended multilinearly through the coordinates of the algebra inputs in the basis of idempotents
and chords. In general `m_{n+1}(x, a₁, …, aₙ)` is `x` times the product of the coordinates of
`ρ_ij` in `a₁`, of `ρ_kj` in `a₂, …, aₙ₋₁` and of `ρ_ki` in `aₙ`, for `n ≥ 2`
(`TauCeti.StrandsAlgebra.threePointTypeA_act_add_two_apply`). The module is strictly unital for the
idempotents (`TauCeti.StrandsAlgebra.isStrictlyUnital_threePointTypeA`). Its operation `m₁`
vanishes, while `m₂` and every `m_{n+3}` are nonzero
(`TauCeti.StrandsAlgebra.threePointTypeA_act_one_oneStrandIdem`,
`TauCeti.StrandsAlgebra.threePointTypeA_act_cons_snoc`), so it is not a differential module.

For the genus-one pointed matched circle, whose points `0, 1, 2, 3` are matched as `{0, 2}` and
`{1, 3}`, the triples `(1, 2, 3)` and `(0, 1, 2)` give the operations
`m_{n+3}(x, ρ₃, ρ₂₃, …, ρ₂₃, ρ₂) = x` and `m_{n+3}(x, ρ₂, ρ₁₂, …, ρ₁₂, ρ₁) = x` over the torus
algebra, the shape of the type `A` modules of solid tori in bordered Floer homology; see
`TauCeti.LowDimTopology.Bordered.Torus.TypeA`.

**The `A∞` relations.** Write `e`, `f`, `p`, `q` and `r` for the coordinates of `I(i)`, of
`I(k) = I(j)`, of `ρ_ij`, of `ρ_kj` and of `ρ_ki`. Since nothing lies strictly between `i` and `j`
or between `k` and `i`, and only `i` lies strictly between `k` and `j`, the product formula for
chord coordinates (`TauCeti.StrandsAlgebra.oneStrandChordCoord_mul`) gives

`e(ab) = e(a) e(b)`, `p(ab) = e(a) p(b) + p(a) f(b)`, `r(ab) = f(a) r(b) + r(a) e(b)` and
`q(ab) = f(a) q(b) + r(a) p(b) + q(a) f(b)`.

The algebra has zero differential, so the relation of length `n` reads
`∑ m(m(x, a₁, …, aₛ), aₛ₊₁, …, aₙ) + ∑ m(x, a₁, …, aₗ aₗ₊₁, …, aₙ) = 0`. Splitting off the first
input, each product term `p(aₗ aₗ₊₁)`, `q(aₗ aₗ₊₁)` or `r(aₗ aₗ₊₁)` produces one term `r p`, which
cancels the composite term breaking the word between `aₗ` and `aₗ₊₁`, and terms with an idempotent
coordinate, which cancel in pairs between adjacent positions, over a ring of characteristic two.
The proof runs by induction on the word, read as a list.

## Main definitions

* `TauCeti.StrandsAlgebra.threePointTypeA`: the one-generator type `A` module of three points.

## Main results

* `TauCeti.StrandsAlgebra.threePointTypeA_act_one_apply`,
  `TauCeti.StrandsAlgebra.threePointTypeA_act_add_two_apply`: its operations.
* `TauCeti.StrandsAlgebra.threePointTypeA_act_cons_snoc`:
  `m_{n+3}(x, ρ_ij, ρ_kj, …, ρ_kj, ρ_ki) = x`.
* `TauCeti.StrandsAlgebra.isStrictlyUnital_threePointTypeA`: it is strictly unital.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.1 (`A∞` modules over `𝔽₂`) and Chapter 11 (the type `A` modules of solid tori).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

/-! ### Weights of words

The operations of the module weigh a word `a₁ ⋯ aₙ` of algebra inputs by `e(a₁)` when `n = 1` and
by `p(a₁) q(a₂) ⋯ q(aₙ₋₁) r(aₙ)` when `n ≥ 2`. The `A∞` relations are identities between these
weights, proved here for lists over any multiplication with coordinates satisfying the four
product formulas. -/

section Word

variable {A S : Type*} [Mul A] [CommRing S]

/-- Multiply the entries `l` and `l + 1` of a list. -/
private def contractAt : ℕ → List A → List A
  | 0, x :: y :: L => (x * y) :: L
  | l + 1, x :: L => x :: contractAt l L
  | _, L => L

private theorem contractAt_cons_ne_nil (l : ℕ) (x : A) (L : List A) :
    contractAt l (x :: L) ≠ [] := by
  cases l <;> cases L <;> simp [contractAt]

variable (e p q r : A → S)

/-- The weight `q(a₁) ⋯ q(aₙ₋₁) r(aₙ)` of a nonempty word. -/
private def tailWeight : List A → S
  | [] => 0
  | [z] => r z
  | y :: z :: L => q y * tailWeight (z :: L)

/-- The weight `e(a₁)` of a word of length one, and `p(a₁) q(a₂) ⋯ q(aₙ₋₁) r(aₙ)` of a word of
length `n ≥ 2`. -/
private def wordWeight : List A → S
  | [] => 0
  | [x] => e x
  | x :: y :: L => p x * tailWeight q r (y :: L)

omit [Mul A] in
private theorem tailWeight_cons_of_ne_nil (y : A) {L : List A} (hL : L ≠ []) :
    tailWeight q r (y :: L) = q y * tailWeight q r L := by
  cases L with
  | nil => exact absurd rfl hL
  | cons z L => rfl

omit [Mul A] in
private theorem wordWeight_cons_of_ne_nil (x : A) {L : List A} (hL : L ≠ []) :
    wordWeight e p q r (x :: L) = p x * tailWeight q r L := by
  cases L with
  | nil => exact absurd rfl hL
  | cons z L => rfl

omit [Mul A] in
/-- The product of `q` over all but the last letter and `r` at the last letter of a word is its
tail weight. -/
private theorem prod_ite_eq_tailWeight (m : ℕ) (g : Fin (m + 1) → A) :
    ∏ l : Fin (m + 1), (if (l : ℕ) = m then r (g l) else q (g l)) =
      tailWeight q r (List.ofFn g) := by
  induction m with
  | zero => simp [tailWeight]
  | succ m ih =>
    rw [Fin.prod_univ_succ, List.ofFn_succ, tailWeight_cons_of_ne_nil q r _ (by simp), ← ih]
    simp

variable {e p q r} (f : A → S) [CharP S 2]
  (he : ∀ x y, e (x * y) = e x * e y) (hp : ∀ x y, p (x * y) = e x * p y + p x * f y)
  (hq : ∀ x y, q (x * y) = f x * q y + r x * p y + q x * f y)
  (hr : ∀ x y, r (x * y) = f x * r y + r x * e y)

include hq hr in
/-- The relation for the tail weights of a word `y z L` of length at least two. -/
private theorem tailWeight_relation (y z : A) (L : List A) :
    f y * tailWeight q r (z :: L) +
        ∑ s ∈ range (L.length + 2), wordWeight e p q r ((y :: z :: L).drop (s + 1)) *
          tailWeight q r ((y :: z :: L).take (s + 1)) +
      ∑ l ∈ range (L.length + 1), tailWeight q r (contractAt l (y :: z :: L)) = 0 := by
  have h2 : (2 : S) = 0 := CharTwo.two_eq_zero
  induction L generalizing y z with
  | nil =>
    simp only [List.length_nil, zero_add, sum_range_succ, range_zero, sum_empty]
    simp only [tailWeight, wordWeight, contractAt, List.drop, List.take, hr]
    linear_combination (f y * r z + r y * e z) * h2
  | cons w L ih =>
    -- Split off the first letter `y` from the splittings and from the contractions.
    have hA : ∑ s ∈ range ((w :: L).length + 2),
        wordWeight e p q r ((y :: z :: w :: L).drop (s + 1)) *
          tailWeight q r ((y :: z :: w :: L).take (s + 1)) =
        p z * tailWeight q r (w :: L) * r y +
          q y * ∑ s ∈ range (L.length + 2), wordWeight e p q r ((z :: w :: L).drop (s + 1)) *
            tailWeight q r ((z :: w :: L).take (s + 1)) := by
      rw [List.length_cons, show L.length + 1 + 2 = L.length + 2 + 1 by omega, sum_range_succ',
        add_comm, mul_sum]
      congr 1
      · refine sum_congr rfl fun s _ ↦ ?_
        rw [List.drop_succ_cons, List.take_succ_cons, List.take_succ_cons, tailWeight]
        ring
    have hB : ∑ l ∈ range ((w :: L).length + 1), tailWeight q r (contractAt l (y :: z :: w :: L)) =
        q (y * z) * tailWeight q r (w :: L) +
          q y * ∑ l ∈ range (L.length + 1), tailWeight q r (contractAt l (z :: w :: L)) := by
      rw [List.length_cons, sum_range_succ', add_comm, mul_sum]
      congr 1
      exact sum_congr rfl fun l _ ↦ tailWeight_cons_of_ne_nil q r y (contractAt_cons_ne_nil l z _)
    rw [hA, hB, hq, tailWeight.eq_3]
    linear_combination q y * ih z w + (f y * q z + r y * p z) * tailWeight q r (w :: L) * h2

include he hp hq hr in
/-- **The `A∞` relation for word weights**: for every word `L`, the sum over the splittings of `L`
into two words of the products of their weights, plus the weights of the words obtained by
multiplying two adjacent letters, vanishes. -/
private theorem wordWeight_relation (L : List A) :
    ∑ s ∈ range (L.length + 1), wordWeight e p q r (L.drop s) * wordWeight e p q r (L.take s) +
      ∑ l ∈ range (L.length - 1), wordWeight e p q r (contractAt l L) = 0 := by
  have h2 : (2 : S) = 0 := CharTwo.two_eq_zero
  match L with
  | [] => simp [wordWeight]
  | [x] => simp [sum_range_succ, wordWeight]
  | x :: y :: L =>
    -- Split off the first letter `x` from the splittings and from the contractions.
    have hA : ∑ s ∈ range ((x :: y :: L).length + 1),
        wordWeight e p q r ((x :: y :: L).drop s) * wordWeight e p q r ((x :: y :: L).take s) =
        wordWeight e p q r (y :: L) * e x +
          p x * ∑ s ∈ range (L.length + 1), wordWeight e p q r ((y :: L).drop (s + 1)) *
            tailWeight q r ((y :: L).take (s + 1)) := by
      rw [sum_range_succ', List.length_cons, sum_range_succ', mul_sum]
      simp only [List.drop_succ_cons, List.take_succ_cons, List.drop_zero, List.take_zero,
        wordWeight, mul_zero, add_zero]
      rw [add_comm]
      congr 1
      exact sum_congr rfl fun s _ ↦ by ring
    have hB : ∑ l ∈ range ((x :: y :: L).length - 1),
        wordWeight e p q r (contractAt l (x :: y :: L)) =
        wordWeight e p q r ((x * y) :: L) +
          p x * ∑ l ∈ range L.length, tailWeight q r (contractAt l (y :: L)) := by
      rw [List.length_cons, List.length_cons, Nat.add_sub_cancel, sum_range_succ', add_comm,
        mul_sum]
      congr 1
      exact sum_congr rfl fun l _ ↦
        wordWeight_cons_of_ne_nil e p q r x (contractAt_cons_ne_nil l y _)
    rw [hA, hB]
    match L with
    | [] =>
      simp only [wordWeight, tailWeight, he, List.length_nil, zero_add, range_one,
        List.drop_succ_cons, List.drop_nil, List.take_succ_cons, List.take_nil, zero_mul,
        sum_const_zero, mul_zero, add_zero, range_zero, sum_empty]
      linear_combination e x * e y * h2
    | z :: L =>
      have hrel := tailWeight_relation f hq hr y z L
      rw [show (z :: L).length + 1 = L.length + 2 by simp,
        show (z :: L).length = L.length + 1 by simp]
      rw [wordWeight.eq_3, wordWeight.eq_3, hp]
      linear_combination p x * hrel + e x * p y * tailWeight q r (z :: L) * h2

end Word

/-! ### Words of inputs as lists -/

section OfFn

variable {A : Type*} [Mul A]

private theorem ofFn_contractNth {n : ℕ} (a : Fin (n + 1) → A) (l : Fin n) :
    List.ofFn (Fin.contractNth l.castSucc (· * ·) a) = contractAt l (List.ofFn a) := by
  induction n with
  | zero => exact l.elim0
  | succ n ih =>
    cases l using Fin.cases with
    | zero =>
      rw [List.ofFn_succ, List.ofFn_succ (f := a), List.ofFn_succ (f := fun i ↦ a i.succ)]
      simp [Fin.contractNth, contractAt]
    | succ l =>
      rw [List.ofFn_succ, List.ofFn_succ (f := a)]
      simp only [Fin.val_succ, contractAt]
      rw [← ih]
      congr 2
      rw [← Fin.succ_castSucc]
      exact Fin.tail_contractNth_succ _ l.castSucc a

end OfFn

/-! ### The module -/

section Module

variable {R α β : Type*} [CommRing R] [LinearOrder α] [Fintype α] [DecidableEq β] (M : α → β)
  {k i j : α} (hki : k < i) (hij : i < j)

variable (R) in
/-- The coordinate read by the operation `m_{n+1}` at its input `l`: the coordinate of the
idempotent of `i` for `n = 1`, and for `n ≥ 2` that of `ρ_ij` at the first input, of `ρ_ki` at the
last and of `ρ_kj` in between. -/
private def threePointCoord (n : ℕ) (l : Fin n) : Module.Dual R (matchedSummand R M 1) :=
  if n = 1 then oneStrandIdemCoord R M ⟨M i, i, rfl⟩
  else if (l : ℕ) = 0 then oneStrandChordCoord R M hij
  else if (l : ℕ) + 1 = n then oneStrandChordCoord R M hki
  else oneStrandChordCoord R M (hki.trans hij)

variable (R) in
/-- The operations of the one-generator module of the three points `k < i < j`. -/
private def threePointAct :
    (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ matchedSummand R M 1) (R →ₗ[R] R)
  | 0 => 0
  | n + 1 => ((MultilinearMap.mkPiAlgebra R (Fin (n + 1)) R).compLinearMap
      (threePointCoord R M hki hij (n + 1))).smulRight LinearMap.id

private theorem threePointAct_succ_apply (n : ℕ) (a : Fin (n + 1) → matchedSummand R M 1)
    (x : R) :
    threePointAct R M hki hij (n + 1) a x =
      (∏ l, threePointCoord R M hki hij (n + 1) l (a l)) * x := by
  simp [threePointAct]

/-- The operations weigh their inputs by the word weights. -/
private theorem threePointAct_apply (n : ℕ) (a : Fin n → matchedSummand R M 1) (x : R) :
    threePointAct R M hki hij n a x =
      wordWeight (oneStrandIdemCoord R M ⟨M i, i, rfl⟩) (oneStrandChordCoord R M hij)
        (oneStrandChordCoord R M (hki.trans hij)) (oneStrandChordCoord R M hki)
        (List.ofFn a) * x := by
  match n with
  | 0 => simp [threePointAct, wordWeight]
  | 1 => simp [threePointAct_succ_apply, threePointCoord, wordWeight]
  | n + 2 =>
    rw [threePointAct_succ_apply, Fin.prod_univ_succ, List.ofFn_succ,
      wordWeight_cons_of_ne_nil _ _ _ _ _ (by simp), ← prod_ite_eq_tailWeight]
    congr 2
    exact Fintype.prod_congr _ _ fun l ↦ by
      simp only [threePointCoord, Fin.val_succ]
      split_ifs <;> first | contradiction | omega | rfl

variable {M hki hij} (hM : M k = M j) (hbetween : ∀ m, k < m → m < j → m = i)
include hM hbetween

include hki in
/-- The coordinate of `ρ_ij` of a product. -/
private theorem chordCoord_ij_mul (x y : matchedSummand R M 1) :
    oneStrandChordCoord R M hij (x * y) =
      oneStrandIdemCoord R M ⟨M i, i, rfl⟩ x * oneStrandChordCoord R M hij y +
        oneStrandChordCoord R M hij x * oneStrandIdemCoord R M ⟨M k, k, rfl⟩ y := by
  -- No point lies strictly between `i` and `j`.
  rw [oneStrandChordCoord_mul,
    Fintype.sum_eq_zero _ fun (m : {m // i < m ∧ m < j}) ↦ absurd m.property.1 (by
      rw [hbetween m (hki.trans m.property.1) m.property.2]
      exact lt_irrefl i),
    add_zero, show (⟨M j, j, rfl⟩ : Set.range M) = ⟨M k, k, rfl⟩ from Subtype.ext hM.symm]

/-- The coordinate of `ρ_kj` of a product. -/
private theorem chordCoord_kj_mul (x y : matchedSummand R M 1) :
    oneStrandChordCoord R M (hki.trans hij) (x * y) =
      oneStrandIdemCoord R M ⟨M k, k, rfl⟩ x * oneStrandChordCoord R M (hki.trans hij) y +
        oneStrandChordCoord R M hki x * oneStrandChordCoord R M hij y +
        oneStrandChordCoord R M (hki.trans hij) x * oneStrandIdemCoord R M ⟨M k, k, rfl⟩ y := by
  -- The only point strictly between `k` and `j` is `i`.
  rw [oneStrandChordCoord_mul,
    Fintype.sum_eq_single ⟨i, hki, hij⟩ fun (m : {m // k < m ∧ m < j}) hm ↦
      absurd (Subtype.ext (hbetween m m.property.1 m.property.2)) hm,
    show (⟨M j, j, rfl⟩ : Set.range M) = ⟨M k, k, rfl⟩ from Subtype.ext hM.symm]
  ring

omit hM in
include hij in
/-- The coordinate of `ρ_ki` of a product. -/
private theorem chordCoord_ki_mul (x y : matchedSummand R M 1) :
    oneStrandChordCoord R M hki (x * y) =
      oneStrandIdemCoord R M ⟨M k, k, rfl⟩ x * oneStrandChordCoord R M hki y +
        oneStrandChordCoord R M hki x * oneStrandIdemCoord R M ⟨M i, i, rfl⟩ y := by
  -- No point lies strictly between `k` and `i`.
  rw [oneStrandChordCoord_mul,
    Fintype.sum_eq_zero _ fun (m : {m // k < m ∧ m < i}) ↦ absurd m.property.2 (by
      rw [hbetween m m.property.1 (m.property.2.trans hij)]
      exact lt_irrefl i),
    add_zero]

/-- **The `A∞` relations** of the operations of the module of three points. -/
private theorem threePointAct_stasheff [CharP R 2] (N : ℕ) (a : Fin N → matchedSummand R M 1)
    (x : R) :
    ungradedStasheffComp (threePointAct R M hki hij) N a x +
        ungradedStasheffDiff (threePointAct R M hki hij) (matchedSummandDifferential R M 1) N a x +
      ungradedStasheffMul (threePointAct R M hki hij) N a x = 0 := by
  have hdiff : ungradedStasheffDiff (threePointAct R M hki hij)
      (matchedSummandDifferential R M 1) N a x = 0 := by
    rw [ungradedStasheffDiff_apply]
    refine sum_eq_zero fun l _ ↦ ?_
    rw [(threePointAct R M hki hij N).map_coord_zero l (by simp), LinearMap.zero_apply]
  have hcomp : ungradedStasheffComp (threePointAct R M hki hij) N a x =
      (∑ s ∈ range (N + 1), wordWeight (oneStrandIdemCoord R M ⟨M i, i, rfl⟩)
          (oneStrandChordCoord R M hij) (oneStrandChordCoord R M (hki.trans hij))
          (oneStrandChordCoord R M hki) ((List.ofFn a).drop s) *
        wordWeight (oneStrandIdemCoord R M ⟨M i, i, rfl⟩)
          (oneStrandChordCoord R M hij) (oneStrandChordCoord R M (hki.trans hij))
          (oneStrandChordCoord R M hki) ((List.ofFn a).take s)) * x := by
    rw [ungradedStasheffComp_def, sum_mul, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun s _ ↦ ?_
    -- The inner inputs `fun l ↦ a ⟨l, _⟩` are `Fin.take s _ a` by the definition of `Fin.take`.
    rw [threePointAct_apply, threePointAct_apply, Fin.ofFn_drop_eq_drop_ofFn,
      show List.ofFn (fun l : Fin s ↦ a ⟨l, by omega⟩) = (List.ofFn a).take s from
        Fin.ofFn_take_eq_take_ofFn (Nat.lt_succ_iff.1 s.isLt) a, mul_assoc]
  have hmul : ungradedStasheffMul (threePointAct R M hki hij) N a x =
      (∑ l ∈ range (N - 1), wordWeight
        (oneStrandIdemCoord R M ⟨M i, i, rfl⟩) (oneStrandChordCoord R M hij)
        (oneStrandChordCoord R M (hki.trans hij)) (oneStrandChordCoord R M hki)
        (contractAt l (List.ofFn a))) * x := by
    match N, a with
    | 0, a => simp
    | n + 1, a =>
      rw [ungradedStasheffMul_succ_apply, Nat.add_sub_cancel, sum_mul,
        ← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun l _ ↦ ?_
      rw [threePointAct_apply, ofFn_contractNth]
  have h := wordWeight_relation (oneStrandIdemCoord R M ⟨M k, k, rfl⟩)
    (oneStrandIdemCoord_mul M _) (chordCoord_ij_mul (hki := hki) (hij := hij) hM hbetween)
    (chordCoord_kj_mul (hki := hki) (hij := hij) hM hbetween)
    (chordCoord_ki_mul (hki := hki) (hij := hij) hbetween) (List.ofFn a)
  rw [List.length_ofFn] at h
  rw [hdiff, add_zero, hcomp, hmul, ← add_mul, h, zero_mul]

variable (R M hki hij) in
/-- **The one-generator type `A` module of three points** `k < i < j`, where `i` is the only point
strictly between `k` and `j` and `k` and `j` are matched, over a ring of characteristic two. It is
the `A∞` right module `R` over the matched summand with one strand whose operation `m₂(x, a)` is
`x` times the coordinate of the idempotent `I(i)` in `a`, and whose operation `m_{n+1}`, `n ≥ 2`,
multiplies `x` by the coordinates of `ρ_ij` in the first input, of `ρ_ki` in the last and of `ρ_kj`
in the others. So `m₂(x, I(i)) = x` and `m_{n+3}(x, ρ_ij, ρ_kj, …, ρ_kj, ρ_ki) = x`. -/
def threePointTypeA [CharP R 2] :
    UngradedAInfinityRightModule (matchedSummandDifferential R M 1) R where
  act := threePointAct R M hki hij
  stasheff := threePointAct_stasheff hM hbetween

variable [CharP R 2]

/-- The operations of the module of three points are `threePointAct`. -/
private theorem threePointTypeA_act :
    (threePointTypeA R M hki hij hM hbetween).act = threePointAct R M hki hij :=
  rfl

/-- The operation `m₁` of the module of three points vanishes. -/
@[simp]
theorem threePointTypeA_act_zero : (threePointTypeA R M hki hij hM hbetween).act 0 = 0 := by
  rw [threePointTypeA_act, threePointAct]

/-- **The operation `m₂`** of the module of three points multiplies by the coordinate of the
idempotent `I(i)`. -/
theorem threePointTypeA_act_one_apply (a : Fin 1 → matchedSummand R M 1) (x : R) :
    (threePointTypeA R M hki hij hM hbetween).act 1 a x =
      oneStrandIdemCoord R M ⟨M i, i, rfl⟩ (a 0) * x := by
  simp [threePointTypeA, threePointAct_succ_apply, threePointCoord]

/-- The idempotent `I(i)` acts by the identity through `m₂`, and the other idempotents by zero. -/
@[simp]
theorem threePointTypeA_act_one_oneStrandIdem (p : Set.range M) (x : R) :
    (threePointTypeA R M hki hij hM hbetween).act 1 (fun _ ↦ oneStrandIdem R M p) x =
      if p = ⟨M i, i, rfl⟩ then x else 0 := by
  rw [threePointTypeA_act_one_apply, oneStrandIdemCoord_oneStrandIdem]
  split_ifs <;> simp

/-- **The higher operations** of the module of three points: `m_{n+3}(x, a₀, …, aₙ₊₁)` is `x`
times the coordinates of `ρ_ij` in `a₀`, of `ρ_kj` in `a₁, …, aₙ` and of `ρ_ki` in `aₙ₊₁`. -/
theorem threePointTypeA_act_add_two_apply (n : ℕ) (a : Fin (n + 2) → matchedSummand R M 1)
    (x : R) :
    (threePointTypeA R M hki hij hM hbetween).act (n + 2) a x =
      oneStrandChordCoord R M hij (a 0) *
        (∏ l : Fin n, oneStrandChordCoord R M (hki.trans hij) (a l.succ.castSucc)) *
        oneStrandChordCoord R M hki (a (Fin.last (n + 1))) * x := by
  rw [threePointTypeA_act]
  have h0 : threePointCoord R M hki hij (n + 2) 0 = oneStrandChordCoord R M hij := by
    simp [threePointCoord]
  have hlast : threePointCoord R M hki hij (n + 2) (Fin.last n).succ =
      oneStrandChordCoord R M hki := by
    simp [threePointCoord]
  have hmid : ∏ l : Fin n, threePointCoord R M hki hij (n + 2) l.castSucc.succ
      (a l.castSucc.succ) =
        ∏ l : Fin n, oneStrandChordCoord R M (hki.trans hij) (a l.succ.castSucc) :=
    Fintype.prod_congr _ _ fun l ↦ by
      have := l.isLt
      simp only [threePointCoord, Fin.val_succ, Fin.val_castSucc, Fin.succ_castSucc]
      split_ifs <;> first | contradiction | omega | rfl
  rw [threePointAct_succ_apply, Fin.prod_univ_succ, Fin.prod_univ_castSucc, h0, hlast, hmid,
    Fin.succ_last]
  ring

/-- **The defining operations** of the module of three points:
`m_{n+3}(x, ρ_ij, ρ_kj, …, ρ_kj, ρ_ki) = x`, with `n` copies of `ρ_kj`. In particular every
operation `m_{n+3}` is nonzero, so this is not a differential module. -/
theorem threePointTypeA_act_cons_snoc (n : ℕ) (x : R) :
    (threePointTypeA R M hki hij hM hbetween).act (n + 2)
        (Fin.cons (oneStrandChord R M hij)
          (Fin.snoc (fun _ : Fin n ↦ oneStrandChord R M (hki.trans hij))
            (oneStrandChord R M hki))) x = x := by
  rw [threePointTypeA_act_add_two_apply]
  simp [← Fin.succ_last]

/-- **The module of three points is strictly unital**: its operations `m_{n+1}`, `n ≥ 2`, vanish
as soon as one input is an idempotent `I({p})`, whose chord coordinates vanish. -/
theorem isStrictlyUnital_threePointTypeA :
    (threePointTypeA R M hki hij hM hbetween).IsStrictlyUnital (oneStrandIdem R M) := by
  refine (UngradedAInfinityRightModule.isStrictlyUnital_iff _).2 fun n hn a l p hl ↦ ?_
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  refine LinearMap.ext fun x ↦ ?_
  rw [threePointTypeA_act, LinearMap.zero_apply]
  rw [threePointAct_succ_apply, Finset.prod_eq_zero (Finset.mem_univ l), zero_mul]
  rw [hl, threePointCoord]
  split_ifs <;> first | omega | simp

end Module


end StrandsAlgebra

end TauCeti
