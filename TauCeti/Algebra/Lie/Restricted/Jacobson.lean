/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Free
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Notation
import TauCeti.Algebra.Lie.AdjointAction.Frobenius

/-!
# Jacobson's Lie polynomial and Jacobson's formula

In an associative `R`-algebra `A` of prime characteristic `p`, the Frobenius map `a ↦ a ^ p` is
not additive in general: `(a + b) ^ p - a ^ p - b ^ p` is a universal Lie polynomial in `a` and
`b`, introduced by Jacobson (1937) to axiomatize restricted Lie algebras.

For any commutative ring `R` and natural number `p`, we define the universal Lie polynomial
`TauCeti.jacobsonLie R p : FreeLieAlgebra R (Fin 2)` explicitly as a sum over words
`z : Fin (p - 1) → Fin 2` of length `p - 1`:

`Λ_p(x, y) = ∑ z, ((((#{j | z j = 0} + 1 : ℕ) : ZMod p)⁻¹).val) • [z₀, [z₁, … [z_{p-2}, x] …]]`,

where `x = FreeLieAlgebra.of R 0` and `y = FreeLieAlgebra.of R 1`. This concrete formula makes
`jacobsonLie R p` well-defined over every commutative ring `R`, without requiring `p` to be
invertible or zero in `R`. For `p = 2` it is `[y, x]`; for `p = 3` it is
`[y, [y, x]] + 2 • [x, [y, x]]`.

## Main definitions

* `TauCeti.jacobsonLie`: Jacobson's Lie polynomial `Λ_p(x, y)` in `FreeLieAlgebra R (Fin 2)`.

## Main results

* `TauCeti.jacobsonLie_def`: defining sum expansion of `jacobsonLie R p`.
* `TauCeti.lift_jacobsonLie_eq_sum`: evaluation of `jacobsonLie R p` under `FreeLieAlgebra.lift`.
* `TauCeti.map_lift_jacobsonLie`: naturality of `Λ_p` under Lie algebra morphisms.
* `TauCeti.lift_jacobsonLie_change_ring`: independence of the evaluation
  `FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p)` from the scalar ring `R`.
* `TauCeti.jacobsonLie_one`, `TauCeti.jacobsonLie_two`, `TauCeti.jacobsonLie_three`: explicit
  closed forms for `p = 1, 2, 3`.
* `TauCeti.lift_jacobsonLie_eq_zero_of_lie_eq_zero`: `Λ_p(x, y) = 0` when `⁅x, y⁆ = 0` (`p ≠ 0`).
* `TauCeti.lift_jacobsonLie_smul_smul`: `p`-homogeneity `Λ_p(c • x, c • y) = c ^ p • Λ_p(x, y)`
  (`p ≠ 0`).
* `TauCeti.sum_nsmul_foldr_eq_lift_jacobsonLie`: when `p • v = 0` for all `v : L` (`p ≠ 0`),
  `Λ_p(x, y)` does not depend on the choice of natural-number representatives for `i⁻¹ mod p`.
* `TauCeti.lift_jacobsonLie_eq_ad_pow_of_lie_ad_pow_eq_zero`: rank-one collapse
  `Λ_p(x, y) = (ad y) ^ (p - 1) x` when `⁅x, (ad y) ^ k x⁆ = 0` for all `k` (`1 < p`).
* `TauCeti.add_pow_eq_jacobson`: Jacobson's formula `(a + b) ^ p = a ^ p + b ^ p + Λ_p(a, b)` in
  any associative algebra of prime characteristic `p`.

## References

* N. Jacobson, *Abstract Derivation and Lie Algebras*, Trans. Amer. Math. Soc. **42** (1937),
  206–224.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V, §7.
* N. M. Katz, *Nilpotent connections and the monodromy theorem: Applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), (5.2.4)–(5.2.5).
-/

public section

namespace TauCeti

open Finset

section Definition

variable (R : Type*) [CommRing R] (p : ℕ)

/-- Jacobson's Lie polynomial `Λ_p(x, y)` in `FreeLieAlgebra R (Fin 2)`, with generators
`x = FreeLieAlgebra.of R 0` and `y = FreeLieAlgebra.of R 1`. For each word
`z : Fin (p - 1) → Fin 2`, the iterated bracket `[z₀, [z₁, … [z_{p - 2}, x] …]]` carries the
natural-number representative of `(i : ZMod p)⁻¹`, where `i - 1` is the number of occurrences of `0`
in `z`. -/
noncomputable def jacobsonLie : FreeLieAlgebra R (Fin 2) :=
  ∑ z : Fin (p - 1) → Fin 2,
    (((((Finset.univ.filter fun j => z j = 0).card + 1 : ℕ) : ZMod p)⁻¹).val) •
      (List.ofFn z).foldr (fun i v => ⁅FreeLieAlgebra.of R i, v⁆) (FreeLieAlgebra.of R 0)

/-- The defining sum expansion of `jacobsonLie R p`. -/
theorem jacobsonLie_def :
    jacobsonLie R p =
      ∑ z : Fin (p - 1) → Fin 2,
        (((((Finset.univ.filter fun j => z j = 0).card + 1 : ℕ) : ZMod p)⁻¹).val) •
          (List.ofFn z).foldr (fun i v => ⁅FreeLieAlgebra.of R i, v⁆) (FreeLieAlgebra.of R 0) :=
  (rfl)

end Definition

section FoldrHelpers

private theorem map_foldr_lie {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') {α : Type*} (g : α → L)
    (l : List α) (v : L) :
    f (l.foldr (fun i w => ⁅g i, w⁆) v) = l.foldr (fun i w => ⁅f (g i), w⁆) (f v) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem foldr_lie_zero {L : Type*} [LieRing L] {α : Type*} (g : α → L) (l : List α) :
    l.foldr (fun i w => ⁅g i, w⁆) (0 : L) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem foldr_lie_smul {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {α : Type*} (c : R) (g : α → L) (l : List α) (v : L) :
    l.foldr (fun i w => ⁅c • g i, w⁆) (c • v) =
      c ^ (l.length + 1) • l.foldr (fun i w => ⁅g i, w⁆) v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ih, lie_smul, smul_lie, smul_smul, List.length_cons, List.foldr_cons,
      ← pow_succ]

private theorem foldr_lie_eq_zero_of_last {L : Type*} [LieRing L] {α : Type*} (g : α → L)
    (l : List α) (x : L) (h : ∀ a ∈ l, ⁅g a, x⁆ = 0) (hl : l ≠ []) :
    l.foldr (fun i w => ⁅g i, w⁆) x = 0 := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil => simp [h a (List.mem_cons_self ..)]
    | cons b l' =>
      have ih' := ih (fun c hc => h c (List.mem_cons_of_mem a hc)) (List.cons_ne_nil b l')
      simp [ih']

end FoldrHelpers

section BasicProperties

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- Evaluating `jacobsonLie R p` via `FreeLieAlgebra.lift R ![x, y]` produces the sum of iterated
brackets in `x` and `y` weighted by natural-number representatives of inverses modulo `p`. -/
theorem lift_jacobsonLie_eq_sum (p : ℕ) (x y : L) :
    FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) =
      ∑ z : Fin (p - 1) → Fin 2,
        (((((Finset.univ.filter fun j => z j = 0).card + 1 : ℕ) : ZMod p)⁻¹).val) •
          (List.ofFn z).foldr (fun i v => ⁅![x, y] i, v⁆) x := by
  rw [jacobsonLie_def, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_nsmul, map_foldr_lie]
  simp [FreeLieAlgebra.lift_of_apply]

/-- Naturality of Jacobson's Lie polynomial under Lie algebra morphisms. -/
@[simp]
theorem map_lift_jacobsonLie (p : ℕ) (f : L →ₗ⁅R⁆ L') (x y : L) :
    f (FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p)) =
      FreeLieAlgebra.lift R ![f x, f y] (jacobsonLie R p) := by
  rw [lift_jacobsonLie_eq_sum, lift_jacobsonLie_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_nsmul, map_foldr_lie]
  congr 1
  refine congrArg (fun g => (List.ofFn z).foldr g (f x)) ?_
  funext i v
  fin_cases i <;> simp

/-- Because `jacobsonLie` uses natural-number scalar multiples, its evaluation in a `LieRing` is
independent of the ground commutative ring. -/
theorem lift_jacobsonLie_change_ring {S : Type*} [CommRing S] [LieAlgebra S L]
    (p : ℕ) (x y : L) :
    FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) =
      FreeLieAlgebra.lift S ![x, y] (jacobsonLie S p) := by
  rw [lift_jacobsonLie_eq_sum, lift_jacobsonLie_eq_sum]

/-- At `p = 1`, `jacobsonLie R 1 = 0`. -/
@[simp]
theorem jacobsonLie_one (R : Type*) [CommRing R] : jacobsonLie R 1 = 0 := by
  rw [jacobsonLie_def]
  refine Finset.sum_eq_zero fun z _ => ?_
  have hval : (((((Finset.univ.filter fun j => z j = 0).card + 1 : ℕ) : ZMod 1)⁻¹).val) = 0 :=
    ZMod.val_eq_zero _ |>.mpr (Subsingleton.elim _ _)
  rw [hval, zero_nsmul]

/-- Evaluating `jacobsonLie R 1` gives `0`. -/
theorem lift_jacobsonLie_one (x y : L) :
    FreeLieAlgebra.lift R ![x, y] (jacobsonLie R 1) = 0 := by
  rw [jacobsonLie_one, map_zero]

/-- At `p = 2`, `jacobsonLie R 2 = ⁅y, x⁆`. -/
@[simp]
theorem jacobsonLie_two (R : Type*) [CommRing R] :
    jacobsonLie R 2 = ⁅FreeLieAlgebra.of R (1 : Fin 2), FreeLieAlgebra.of R (0 : Fin 2)⁆ := by
  rw [jacobsonLie_def]
  let e : (Fin 1 → Fin 2) ≃ Fin 2 := Equiv.funUnique (Fin 1) (Fin 2)
  rw [Fintype.sum_equiv e _ (fun i : Fin 2 =>
    (((((Finset.univ.filter fun j : Fin 1 => (fun _ => i) j = 0).card + 1 : ℕ) : ZMod 2)⁻¹).val) •
      ⁅FreeLieAlgebra.of R i, FreeLieAlgebra.of R (0 : Fin 2)⁆) (fun z => by
        have hz : z = fun _ => z 0 := funext fun j => by rw [Fin.eq_zero j]
        have he : e z = z 0 := rfl
        rw [he]
        conv_lhs => rw [hz]
        simp [List.ofFn_succ])]
  rw [Fin.sum_univ_two]
  have h0 : ⁅FreeLieAlgebra.of R (0 : Fin 2), FreeLieAlgebra.of R (0 : Fin 2)⁆ = 0 :=
    lie_self _
  have hcard : (Finset.univ.filter fun _ : Fin 1 => (1 : Fin 2) = 0).card = 0 := by simp
  have h1 : (((0 + 1 : ℕ) : ZMod 2)⁻¹).val = 1 := by
    simp [ZMod.val_one'' (by decide : (2 : ℕ) ≠ 1)]
  rw [h0, smul_zero, zero_add, hcard, h1, one_nsmul]

/-- Evaluating `jacobsonLie R 2` gives `⁅y, x⁆`. -/
theorem lift_jacobsonLie_two (x y : L) :
    FreeLieAlgebra.lift R ![x, y] (jacobsonLie R 2) = ⁅y, x⁆ := by
  simp [jacobsonLie_two]

/-- At `p = 3`, `jacobsonLie R 3 = ⁅y, ⁅y, x⁆⁆ + 2 • ⁅x, ⁅y, x⁆⁆`. -/
theorem jacobsonLie_three (R : Type*) [CommRing R] :
    jacobsonLie R 3 =
      ⁅FreeLieAlgebra.of R (1 : Fin 2),
        ⁅FreeLieAlgebra.of R (1 : Fin 2), FreeLieAlgebra.of R (0 : Fin 2)⁆⁆ +
      2 • ⁅FreeLieAlgebra.of R (0 : Fin 2),
        ⁅FreeLieAlgebra.of R (1 : Fin 2), FreeLieAlgebra.of R (0 : Fin 2)⁆⁆ := by
  rw [jacobsonLie_def]
  rw [Fintype.sum_equiv (finTwoArrowEquiv (Fin 2)) _ (fun p : Fin 2 × Fin 2 =>
    (((((Finset.univ.filter fun j : Fin 2 => ![p.1, p.2] j = 0).card + 1 : ℕ) : ZMod 3)⁻¹).val) •
      ⁅FreeLieAlgebra.of R p.1,
        ⁅FreeLieAlgebra.of R p.2, FreeLieAlgebra.of R (0 : Fin 2)⁆⁆) (fun z => by
        have hz : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
        simp [finTwoArrowEquiv_apply, hz, List.ofFn_succ])]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  dsimp only
  have hself : ⁅FreeLieAlgebra.of R (0 : Fin 2), FreeLieAlgebra.of R (0 : Fin 2)⁆ = 0 := lie_self _
  have hcard01 : (Finset.univ.filter fun j : Fin 2 => ![(0 : Fin 2), 1] j = 0).card = 1 := by
    rw [Fin.card_filter_univ_succ]; simp
  have hcard11 : (Finset.univ.filter fun j : Fin 2 => ![(1 : Fin 2), 1] j = 0).card = 0 := by
    rw [Fin.card_filter_univ_succ]; simp
  have hinv2 : (2 : ZMod 3)⁻¹ = 2 := by
    have h := ZMod.coe_mul_inv_eq_one 2 (by decide : Nat.Coprime 2 3)
    have h22 : (2 : ZMod 3) * 2 = 1 := by decide
    calc (2 : ZMod 3)⁻¹ = 1 * (2 : ZMod 3)⁻¹ := (one_mul _).symm
      _ = 2 * (2 * (2 : ZMod 3)⁻¹) := by rw [← mul_assoc, h22]
      _ = 2 * 1 := by rw [Nat.cast_ofNat] at h; rw [h]
      _ = 2 := mul_one _
  have hv2 : (((1 + 1 : ℕ) : ZMod 3)⁻¹).val = 2 := by
    rw [Nat.cast_add, Nat.cast_one, one_add_one_eq_two, hinv2]
    rfl
  have hv1 : (((0 + 1 : ℕ) : ZMod 3)⁻¹).val = 1 := by
    simp [ZMod.val_one'' (by decide : (3 : ℕ) ≠ 1)]
  rw [hself, lie_zero, smul_zero, zero_add, lie_zero, smul_zero, zero_add,
    hcard01, hcard11, hv2, hv1, one_nsmul, add_comm]

/-- Evaluating `jacobsonLie R 3` gives `⁅y, ⁅y, x⁆⁆ + 2 • ⁅x, ⁅y, x⁆⁆`. -/
theorem lift_jacobsonLie_three (x y : L) :
    FreeLieAlgebra.lift R ![x, y] (jacobsonLie R 3) = ⁅y, ⁅y, x⁆⁆ + 2 • ⁅x, ⁅y, x⁆⁆ := by
  simp [jacobsonLie_three]

/-- `Λ_p(0, y) = 0` for every `p : ℕ` (including `p = 0`), since `0` sits at the innermost
slot of every iterated bracket. -/
@[simp]
theorem lift_jacobsonLie_zero_left (p : ℕ) (y : L) :
    FreeLieAlgebra.lift R ![0, y] (jacobsonLie R p) = 0 := by
  rw [lift_jacobsonLie_eq_sum]
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [foldr_lie_zero, smul_zero]

/-- If `x` and `y` commute in `L` and `p ≠ 0`, then `Λ_p(x, y) = 0`. -/
theorem lift_jacobsonLie_eq_zero_of_lie_eq_zero {p : ℕ} (hp : p ≠ 0) {x y : L} (h : ⁅x, y⁆ = 0) :
    FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) = 0 := by
  rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hp) with rfl | hp1
  · exact lift_jacobsonLie_one x y
  · rw [lift_jacobsonLie_eq_sum]
    refine Finset.sum_eq_zero fun z _ => ?_
    have hlen : List.ofFn z ≠ [] := by
      intro hnil
      have := congrArg List.length hnil
      simp at this
      omega
    have hyx : ⁅y, x⁆ = 0 := by rw [← lie_skew, h, neg_zero]
    have hkill : ∀ a ∈ List.ofFn z, ⁅![x, y] a, x⁆ = 0 := by
      intro a _
      fin_cases a
      · exact lie_self x
      · exact hyx
    rw [foldr_lie_eq_zero_of_last _ _ _ hkill hlen, smul_zero]

/-- `Λ_p(x, 0) = 0` for every `p ≠ 0`. -/
@[simp]
theorem lift_jacobsonLie_zero_right {p : ℕ} (hp : p ≠ 0) (x : L) :
    FreeLieAlgebra.lift R ![x, 0] (jacobsonLie R p) = 0 :=
  lift_jacobsonLie_eq_zero_of_lie_eq_zero hp (lie_zero x)

/-- `Λ_p(x, x) = 0` for every `p ≠ 0`. -/
@[simp]
theorem lift_jacobsonLie_self {p : ℕ} (hp : p ≠ 0) (x : L) :
    FreeLieAlgebra.lift R ![x, x] (jacobsonLie R p) = 0 :=
  lift_jacobsonLie_eq_zero_of_lie_eq_zero hp (lie_self x)

/-- Homogeneity of Jacobson's Lie polynomial:
`Λ_p(c • x, c • y) = c ^ p • Λ_p(x, y)` for `p ≠ 0`. -/
theorem lift_jacobsonLie_smul_smul {p : ℕ} (hp : p ≠ 0) (c : R) (x y : L) :
    FreeLieAlgebra.lift R ![c • x, c • y] (jacobsonLie R p) =
      c ^ p • FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) := by
  rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hp) with rfl | hp1
  · simp
  · rw [lift_jacobsonLie_eq_sum, lift_jacobsonLie_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hg : ![c • x, c • y] = fun i => c • ![x, y] i := by
      funext i; fin_cases i <;> rfl
    rw [hg, foldr_lie_smul, List.length_ofFn, Nat.sub_add_cancel (by omega : 1 ≤ p), smul_comm]

/-- When `p • v = 0` for every `v : L` (`p ≠ 0`), replacing the natural-number representatives of
`(i : ZMod p)⁻¹` (`1 ≤ i < p`) in the definition of `jacobsonLie` does not change its value. -/
theorem sum_nsmul_foldr_eq_lift_jacobsonLie {p : ℕ} (hp : p ≠ 0) (hchar : ∀ v : L, p • v = 0)
    (c : ℕ → ℕ)
    (hc : ∀ i, 1 ≤ i → i < p → (c i : ZMod p) = ((i : ZMod p)⁻¹))
    (x y : L) :
    ∑ z : Fin (p - 1) → Fin 2,
      c ((Finset.univ.filter fun j => z j = 0).card + 1) •
        (List.ofFn z).foldr (fun i v => ⁅![x, y] i, v⁆) x =
      FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) := by
  have : NeZero p := ⟨hp⟩
  have nsmul_congr : ∀ {a b : ℕ} (v : L), (a : ZMod p) = (b : ZMod p) → a • v = b • v := by
    intro a b v hab
    have hmod : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    have hred : ∀ n : ℕ, n • v = (n % p) • v := fun n => by
      conv_lhs => rw [← Nat.div_add_mod n p]
      rw [add_nsmul, mul_comm, mul_nsmul, hchar, zero_add]
    rw [hred a, hred b, hmod]
  rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hp) with rfl | hp1
  · have hzero : ∀ v : L, v = 0 := fun v => by simpa using hchar v
    rw [hzero (∑ z : Fin 0 → Fin 2, _), hzero (FreeLieAlgebra.lift R ![x, y] (jacobsonLie R 1))]
  · rw [lift_jacobsonLie_eq_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    set k := (Finset.univ.filter fun j => z j = 0).card
    have hkle : k ≤ p - 1 := by
      simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin (p - 1))) (fun j => z j = 0))
    rcases Nat.eq_or_lt_of_le hkle with hkeq | hklt
    · have hall : ∀ j : Fin (p - 1), z j = 0 := by
        intro j
        have hmem : j ∈ Finset.univ.filter (fun j => z j = 0) := by
          have : Finset.univ.filter (fun j => z j = 0) = Finset.univ :=
            Finset.eq_univ_of_card _ (by simpa [k] using hkeq)
          rw [this]
          exact Finset.mem_univ j
        exact (Finset.mem_filter.mp hmem).2
      have hlen : List.ofFn z ≠ [] := by
        intro hnil
        have := congrArg List.length hnil
        simp at this
        omega
      have hkill : ∀ a ∈ List.ofFn z, ⁅![x, y] a, x⁆ = 0 := by
        intro a ha
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
        simp [hall j]
      rw [foldr_lie_eq_zero_of_last _ _ _ hkill hlen, smul_zero, smul_zero]
    · apply nsmul_congr
      rw [hc (k + 1) (Nat.succ_pos k) (by omega), ZMod.natCast_zmod_val]

private theorem foldr_const_one (y x : L) (n : ℕ) :
    (List.replicate n (1 : Fin 2)).foldr (fun i v => ⁅![x, y] i, v⁆) x =
      (LieAlgebra.ad R L y ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ']
    simp [mul_apply_eq_comp]

private theorem foldr_eq_zero_of_mem_zero {x y : L}
    (h : ∀ k, ⁅x, (LieAlgebra.ad R L y ^ k) x⁆ = 0) (l : List (Fin 2)) (hl : (0 : Fin 2) ∈ l) :
    l.foldr (fun i v => ⁅![x, y] i, v⁆) x = 0 := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    by_cases h0 : (0 : Fin 2) ∈ l
    · rw [List.foldr_cons, ih h0, lie_zero]
    · have ha : a = 0 := by
        rcases List.mem_cons.mp hl with rfl | hmem
        · rfl
        · exact (h0 hmem).elim
      have hall1 : ∀ b ∈ l, b = 1 := fun b hb => by
        fin_cases b
        · exact (h0 hb).elim
        · rfl
      have hrep : l = List.replicate l.length (1 : Fin 2) :=
        List.eq_replicate_iff.mpr ⟨rfl, hall1⟩
      rw [List.foldr_cons, ha, hrep, foldr_const_one (R := R)]
      simpa using h l.length

/-- **Rank-one collapse of Jacobson's Lie polynomial.** If `1 < p` and `x` commutes with
`(ad R L y ^ k) x` for every `k : ℕ`, then only the word of all `y`'s survives in `Λ_p(x, y)`,
yielding `FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) = (LieAlgebra.ad R L y ^ (p - 1)) x`. -/
theorem lift_jacobsonLie_eq_ad_pow_of_lie_ad_pow_eq_zero {p : ℕ} (hp : 1 < p) {x y : L}
    (h : ∀ k, ⁅x, (LieAlgebra.ad R L y ^ k) x⁆ = 0) :
    FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) = (LieAlgebra.ad R L y ^ (p - 1)) x := by
  rw [lift_jacobsonLie_eq_sum]
  rw [Finset.sum_eq_single (fun _ : Fin (p - 1) => (1 : Fin 2))]
  · have hfilter : (Finset.univ.filter fun _ : Fin (p - 1) => (1 : Fin 2) = 0).card = 0 := by
      simp
    have hinv1 : (1 : ZMod p)⁻¹ = 1 := by simp
    have hval : ((1 : ZMod p)⁻¹).val = 1 := by
      rw [hinv1, ZMod.val_one'' (by omega : p ≠ 1)]
    have hofFn : List.ofFn (fun _ : Fin (p - 1) => (1 : Fin 2)) =
        List.replicate (p - 1) (1 : Fin 2) := by
      simp [List.ofFn_const]
    rw [hfilter, Nat.zero_add, Nat.cast_one, hval, one_nsmul, hofFn, foldr_const_one (R := R)]
  · intro z _ hne
    have hex : ∃ j : Fin (p - 1), z j = 0 := by
      by_contra hno
      push Not at hno
      apply hne
      funext j
      have hj : z j ≠ 0 := hno j
      match hzj : z j with
      | ⟨0, _⟩ => exact (hj hzj).elim
      | ⟨1, _⟩ => rfl
    obtain ⟨j, hj⟩ := hex
    have hmem : (0 : Fin 2) ∈ List.ofFn z := List.mem_ofFn.mpr ⟨j, hj⟩
    rw [foldr_eq_zero_of_mem_zero (R := R) h _ hmem, smul_zero]
  · intro hnotmem
    exact (hnotmem (Finset.mem_univ _)).elim

end BasicProperties

section Associative

open Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem lie_C_mul_X_mul_X_pow {A : Type*} [Ring A] (a v : A) (k : ℕ) :
    ⁅C a * X, C v * X ^ k⁆ = C ⁅a, v⁆ * X ^ (k + 1) := by
  rw [Ring.lie_def, Ring.lie_def]
  have h1 : (C a * X) * (C v * X ^ k) = C (a * v) * X ^ (k + 1) := by
    calc (C a * X) * (C v * X ^ k)
        = C a * (X * C v) * X ^ k := by simp only [mul_assoc]
      _ = C a * (C v * X) * X ^ k := by rw [Polynomial.X_mul_C]
      _ = C (a * v) * (X * X ^ k) := by rw [← mul_assoc, ← C_mul, mul_assoc]
      _ = C (a * v) * X ^ (k + 1) := by rw [pow_succ']
  have h2 : (C v * X ^ k) * (C a * X) = C (v * a) * X ^ (k + 1) := by
    calc (C v * X ^ k) * (C a * X)
        = C v * (X ^ k * C a) * X := by simp only [mul_assoc]
      _ = C v * (C a * X ^ k) * X := by
          rw [((Polynomial.commute_X (C a)).pow_left k).eq]
      _ = C (v * a) * (X ^ k * X) := by rw [← mul_assoc, ← C_mul, mul_assoc]
      _ = C (v * a) * X ^ (k + 1) := by rw [pow_succ]
  rw [h1, h2, ← sub_mul, ← C_sub]

private theorem lie_C_mul_X_pow {A : Type*} [Ring A] (b v : A) (k : ℕ) :
    ⁅C b, C v * X ^ k⁆ = C ⁅b, v⁆ * X ^ k := by
  rw [Ring.lie_def, Ring.lie_def]
  have h1 : C b * (C v * X ^ k) = C (b * v) * X ^ k := by rw [← mul_assoc, ← C_mul]
  have h2 : (C v * X ^ k) * C b = C (v * b) * X ^ k := by
    calc (C v * X ^ k) * C b
        = C v * (X ^ k * C b) := by rw [mul_assoc]
      _ = C v * (C b * X ^ k) := by rw [((Polynomial.commute_X (C b)).pow_left k).eq]
      _ = C (v * b) * X ^ k := by rw [← mul_assoc, ← C_mul]
  rw [h1, h2, ← sub_mul, ← C_sub]

private theorem ad_pow_linear_eq_sum {A : Type*} [Ring A] (a b : A) (n : ℕ) :
    (LieAlgebra.ad ℤ A[X] (C a * X + C b) ^ n) (C a) =
      ∑ z : Fin n → Fin 2,
        C ((List.ofFn z).foldr (fun i v => ⁅![a, b] i, v⁆) a) *
          X ^ (Finset.univ.filter fun j => z j = 0).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, LieAlgebra.ad_apply, lie_sum]
    have hlhs : ∑ z : Fin n → Fin 2,
        ⁅C a * X + C b, C ((List.ofFn z).foldr (fun i v => ⁅![a, b] i, v⁆) a) *
          X ^ (Finset.univ.filter fun j => z j = 0).card⁆ =
        ∑ p : Fin 2 × (Fin n → Fin 2),
          C ((List.ofFn (Fin.cons (α := fun _ => Fin 2) p.1 p.2)).foldr
            (fun i v => ⁅![a, b] i, v⁆) a) *
            X ^ (Finset.univ.filter fun j =>
              Fin.cons (α := fun _ => Fin 2) p.1 p.2 j = 0).card := by
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [add_lie, lie_C_mul_X_mul_X_pow, lie_C_mul_X_pow, Fin.sum_univ_two]
      have hcard0 : (Finset.univ.filter fun j : Fin (n + 1) =>
          Fin.cons (α := fun _ => Fin 2) (0 : Fin 2) z j = 0).card =
          (Finset.univ.filter fun j : Fin n => z j = 0).card + 1 := by
        rw [Fin.card_filter_univ_succ]; simp
      have hcard1 : (Finset.univ.filter fun j : Fin (n + 1) =>
          Fin.cons (α := fun _ => Fin 2) (1 : Fin 2) z j = 0).card =
          (Finset.univ.filter fun j : Fin n => z j = 0).card := by
        rw [Fin.card_filter_univ_succ]; simp
      simp [List.ofFn_succ, hcard0, hcard1]
    rw [hlhs]
    exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)) _ _ (fun _ => rfl)

private theorem derivative_linear_pow_prime {A : Type*} [Ring A] (p : ℕ) [Fact p.Prime]
    [CharP A p] (a b : A) :
    derivative ((C a * X + C b) ^ p) =
      ∑ z : Fin (p - 1) → Fin 2,
        C ((List.ofFn z).foldr (fun i v => ⁅![a, b] i, v⁆) a) *
          X ^ (Finset.univ.filter fun j => z j = 0).card := by
  have : CharP A[X] p := charP_of_injective_ringHom Polynomial.C_injective p
  have hx : derivative (C a * X + C b) = C a := by
    simp [derivative_add, derivative_mul, derivative_C, derivative_X]
  have hpow : ∀ n : ℕ, derivative ((C a * X + C b) ^ n) =
      ∑ m ∈ Finset.range n, (C a * X + C b) ^ m * C a * (C a * X + C b) ^ (n - 1 - m) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, derivative_mul, ih, hx, Finset.sum_mul, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun m hm => ?_
        have hmn : m < n := Finset.mem_range.mp hm
        rw [mul_assoc, ← pow_succ]
        have hexp : n - 1 - m + 1 = n + 1 - 1 - m := by omega
        rw [hexp]
      · simp
  rw [hpow p,
    ← TauCeti.LieAlgebra.ad_pow_prime_sub_one_apply (R := ℤ) p (C a * X + C b) (C a),
    ad_pow_linear_eq_sum]

private theorem coeff_linear_pow_succ_eq_sum {A : Type*} [Ring A] (p : ℕ) [Fact p.Prime]
    [CharP A p] (a b : A) {k : ℕ} (hk : k < p - 1) :
    ((C a * X + C b) ^ p).coeff (k + 1) =
      ∑ z ∈ (Finset.univ : Finset (Fin (p - 1) → Fin 2)).filter
        (fun z => (Finset.univ.filter fun j => z j = 0).card = k),
        ((((k + 1 : ℕ) : ZMod p)⁻¹).val) •
          (List.ofFn z).foldr (fun i v => ⁅![a, b] i, v⁆) a := by
  have hp : p.Prime := Fact.out
  have hderiv := derivative_linear_pow_prime p a b
  have hcop : Nat.Coprime (k + 1) p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) (by omega))).symm
  set u : ℕ := (((k + 1 : ℕ) : ZMod p)⁻¹).val
  have humod : u * (k + 1) ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa [u, Nat.cast_mul, Nat.cast_one] using ZMod.val_inv_mul hcop
  have hmul_one : ∀ c : A, u • ((k + 1) • c) = c := fun c => by
    rw [← mul_nsmul', nsmul_eq_mul]
    have hcast : ((u * (k + 1) : ℕ) : A) = 1 := by
      simpa using CharP.natCast_eq_natCast' A p humod
    rw [hcast, one_mul]
  have hck : (derivative ((C a * X + C b) ^ p)).coeff k =
      (k + 1) • ((C a * X + C b) ^ p).coeff (k + 1) := by
    rw [coeff_derivative, nsmul_eq_mul, (Nat.cast_commute (k + 1) _).eq, Nat.cast_add_one]
  have hrhs : (derivative ((C a * X + C b) ^ p)).coeff k =
      ∑ z ∈ (Finset.univ : Finset (Fin (p - 1) → Fin 2)).filter
        (fun z => (Finset.univ.filter fun j => z j = 0).card = k),
        (List.ofFn z).foldr (fun i v => ⁅![a, b] i, v⁆) a := by
    rw [hderiv, finsetSum_coeff, Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [coeff_C_mul_X_pow]
    simp [eq_comm]
  calc ((C a * X + C b) ^ p).coeff (k + 1)
      = u • ((k + 1) • ((C a * X + C b) ^ p).coeff (k + 1)) := (hmul_one _).symm
    _ = u • (derivative ((C a * X + C b) ^ p)).coeff k := by rw [hck]
    _ = u • ∑ z ∈ (Finset.univ : Finset (Fin (p - 1) → Fin 2)).filter
          (fun z => (Finset.univ.filter fun j => z j = 0).card = k),
          (List.ofFn z).foldr (fun i v => ⁅![a, b] i, v⁆) a := by rw [hrhs]
    _ = _ := Finset.smul_sum

private theorem sum_coeff_linear_pow_succ {A : Type*} [Ring A] (p : ℕ) [Fact p.Prime]
    [CharP A p] (a b : A) :
    ∑ k ∈ Finset.range (p - 1), ((C a * X + C b) ^ p).coeff (k + 1) =
      FreeLieAlgebra.lift ℤ ![a, b] (jacobsonLie ℤ p) := by
  have hp : p.Prime := Fact.out
  rw [lift_jacobsonLie_eq_sum]
  have hmaps : ∀ z ∈ (Finset.univ : Finset (Fin (p - 1) → Fin 2)),
      (Finset.univ.filter fun j => z j = 0).card ∈ Finset.range p := fun z _ => by
    have hle : (Finset.univ.filter fun j => z j = 0).card ≤ p - 1 := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (p - 1))) (fun j => z j = 0)
    exact Finset.mem_range.mpr (Nat.lt_of_le_of_lt hle (Nat.sub_lt hp.pos Nat.one_pos))
  have hfib := Finset.sum_fiberwise_of_maps_to (t := Finset.range p) hmaps
    (fun z => (((((Finset.univ.filter fun j => z j = 0).card + 1 : ℕ) : ZMod p)⁻¹).val) •
      (List.ofFn z).foldr (fun i v => ⁅![a, b] i, v⁆) a)
  rw [← hfib, ← Nat.sub_add_cancel hp.pos, Finset.sum_range_succ, Nat.sub_add_cancel hp.pos]
  have hlast : ∑ z ∈ (Finset.univ : Finset (Fin (p - 1) → Fin 2)).filter
      (fun z => (Finset.univ.filter fun j => z j = 0).card = p - 1),
      (((((Finset.univ.filter fun j => z j = 0).card + 1 : ℕ) : ZMod p)⁻¹).val) •
        (List.ofFn z).foldr (fun i v => ⁅![a, b] i, v⁆) a = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    have hcard : (Finset.univ.filter fun j => z j = 0).card = p - 1 :=
      (Finset.mem_filter.mp hz).2
    have hval : (((((p - 1) + 1 : ℕ) : ZMod p)⁻¹).val) = 0 := by
      rw [Nat.sub_add_cancel hp.pos, ZMod.natCast_self, ZMod.inv_zero, ZMod.val_zero]
    rw [hcard, hval, zero_nsmul]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [coeff_linear_pow_succ_eq_sum p a b (Finset.mem_range.mp hk)]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [(Finset.mem_filter.mp hz).2]

/-- **Jacobson's formula** (Jacobson 1937; Katz 1970, (5.2.4)–(5.2.5)): in an associative
`R`-algebra `A` of prime characteristic `p`,
`(a + b) ^ p = a ^ p + b ^ p + FreeLieAlgebra.lift R ![a, b] (jacobsonLie R p)`. -/
theorem add_pow_eq_jacobson (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]
    {A : Type*} [Ring A] [Algebra R A] [CharP A p] (a b : A) :
    (a + b) ^ p = a ^ p + b ^ p + FreeLieAlgebra.lift R ![a, b] (jacobsonLie R p) := by
  have hp : p.Prime := Fact.out
  let q : A[X] := (C a * X + C b) ^ p
  let ev1 : A[X] →+* A := eval₂RingHom' (RingHom.id A) (1 : A) (fun _ => Commute.one_right _)
  have hev_lhs : ev1 q = (a + b) ^ p := by
    simp [ev1, q, map_pow, eval₂_C]
  have hdeg1 : (C a * X + C b).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simpa using natDegree_C_mul_X_pow_le a 1) (by simp)
  have hdeg : q.natDegree < p + 1 :=
    Nat.lt_succ_of_le ((natDegree_pow_le_of_le p hdeg1).trans_eq (mul_one p))
  have hcoeff0 : q.coeff 0 = b ^ p := by
    change constantCoeff q = b ^ p
    rw [map_pow, constantCoeff_apply]
    simp
  have hcoeffp : q.coeff p = a ^ p := by
    simpa [q, mul_one] using coeff_pow_of_natDegree_le (m := p) hdeg1
  have hev_rhs : ev1 q = ∑ m ∈ Finset.range (p + 1), q.coeff m := by
    simpa [ev1] using Polynomial.eval₂_eq_sum_range' (f := RingHom.id A) (x := (1 : A)) hdeg
  have hsplit : ∑ m ∈ Finset.range (p + 1), q.coeff m =
      q.coeff 0 + (∑ k ∈ Finset.range (p - 1), q.coeff (k + 1)) + q.coeff p := by
    rw [Finset.sum_range_succ, ← Nat.sub_add_cancel hp.pos, Finset.sum_range_succ',
      Nat.sub_add_cancel hp.pos, add_comm (∑ k ∈ Finset.range (p - 1), q.coeff (k + 1))]
  rw [← hev_lhs, hev_rhs, hsplit, hcoeff0, hcoeffp, sum_coeff_linear_pow_succ,
    lift_jacobsonLie_change_ring (R := ℤ) (S := R)]
  abel

end Associative

end TauCeti

section Examples

attribute [local instance 100] LieRing.ofAssociativeRing

-- Witness: for `2 × 2` matrices over `ZMod p` with `p` an odd prime, `E₁₂` and `E₂₁` satisfy
-- `E₁₂ ^ p = 0`, `E₂₁ ^ p = 0`, and `(E₁₂ + E₂₁) ^ p = E₁₂ + E₂₁ ≠ 0`, so
-- `Λ_p(E₁₂, E₂₁) = E₁₂ + E₂₁ ≠ 0`.
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    let e₁₂ : Matrix (Fin 2) (Fin 2) (ZMod p) := !![0, 1; 0, 0]
    let e₂₁ : Matrix (Fin 2) (Fin 2) (ZMod p) := !![0, 0; 1, 0]
    FreeLieAlgebra.lift (ZMod p) ![e₁₂, e₂₁] (TauCeti.jacobsonLie (ZMod p) p) = e₁₂ + e₂₁ ∧
      FreeLieAlgebra.lift (ZMod p) ![e₁₂, e₂₁] (TauCeti.jacobsonLie (ZMod p) p) ≠ 0 := by
  intro e₁₂ e₂₁
  have hprime : p.Prime := Fact.out
  have hodd : Odd p := hprime.odd_of_ne_two hp
  have he12_sq : e₁₂ ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [e₁₂, pow_two, Matrix.mul_apply]
  have he21_sq : e₂₁ ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [e₂₁, pow_two, Matrix.mul_apply]
  have he12_pow : e₁₂ ^ p = 0 :=
    calc e₁₂ ^ p = e₁₂ ^ (2 + (p - 2)) := congrArg (e₁₂ ^ ·) (Nat.add_sub_of_le hprime.two_le).symm
      _ = e₁₂ ^ 2 * e₁₂ ^ (p - 2) := pow_add _ _ _
      _ = 0 := by rw [he12_sq, zero_mul]
  have he21_pow : e₂₁ ^ p = 0 :=
    calc e₂₁ ^ p = e₂₁ ^ (2 + (p - 2)) := congrArg (e₂₁ ^ ·) (Nat.add_sub_of_le hprime.two_le).symm
      _ = e₂₁ ^ 2 * e₂₁ ^ (p - 2) := pow_add _ _ _
      _ = 0 := by rw [he21_sq, zero_mul]
  have hsum_sq : (e₁₂ + e₂₁) ^ 2 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [e₁₂, e₂₁, pow_two, Matrix.mul_apply]
  obtain ⟨k, hk⟩ := hodd
  have hsum_pow : (e₁₂ + e₂₁) ^ p = e₁₂ + e₂₁ :=
    calc (e₁₂ + e₂₁) ^ p = (e₁₂ + e₂₁) ^ (2 * k + 1) := congrArg ((e₁₂ + e₂₁) ^ ·) hk
      _ = ((e₁₂ + e₂₁) ^ 2) ^ k * (e₁₂ + e₂₁) := by rw [pow_succ, pow_mul]
      _ = e₁₂ + e₂₁ := by rw [hsum_sq, one_pow, one_mul]
  have hjac := TauCeti.add_pow_eq_jacobson (ZMod p) p e₁₂ e₂₁
  rw [hsum_pow, he12_pow, he21_pow, zero_add, zero_add] at hjac
  refine ⟨hjac.symm, fun h0 => ?_⟩
  have hne : (e₁₂ + e₂₁) 0 1 = (0 : ZMod p) := by
    have := congrArg (fun M => M 0 1) (hjac.trans h0)
    simpa using this
  simp [e₁₂, e₂₁] at hne

-- Witness at `p = 3`: `⁅e₁₂, ⁅e₂₁, e₁₂⁆⁆ = 2 • e₁₂ ≠ 0`, distinguishing the coefficient `2`
-- from `1` in `Λ_3(x, y) = ⁅y, ⁅y, x⁆⁆ + 2 • ⁅x, ⁅y, x⁆⁆`.
example :
    let e₁₂ : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![0, 1; 0, 0]
    let e₂₁ : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![0, 0; 1, 0]
    ⁅e₁₂, ⁅e₂₁, e₁₂⁆⁆ = 2 • e₁₂ ∧ ⁅e₁₂, ⁅e₂₁, e₁₂⁆⁆ ≠ 0 := by
  intro e₁₂ e₂₁
  have h : ⁅e₁₂, ⁅e₂₁, e₁₂⁆⁆ = 2 • e₁₂ := by
    rw [Ring.lie_def, Ring.lie_def]
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  refine ⟨h, fun h0 => ?_⟩
  have h20 : (2 : ZMod 3) = 0 := by
    have := congrArg (fun M => M 0 1) (h.symm.trans h0)
    simpa [e₁₂] using this
  exact absurd h20 (by decide)

end Examples
