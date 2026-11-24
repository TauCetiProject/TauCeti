/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.FieldTheory.RatFunc.NumDenom

/-!
# Cyclotomic data

A hypergeometric motive over `ℚ` belongs to a family indexed by a *cyclotomic datum* `(A, B)`:
two multisets of positive integers with no index in common and with equal totient sums
`d = ∑_{a ∈ A} φ(a) = ∑_{b ∈ B} φ(b)`, the degree of the family. This is the family index of the
LMFDB, which writes the datum as the label `A…_B…`. The datum records the local monodromy of the
hypergeometric equation at `∞` and at `0` through the products of cyclotomic polynomials
`Φ_A = ∏_{a ∈ A} Φ_a` and `Φ_B = ∏_{b ∈ B} Φ_b`, which are the characteristic polynomials of
the Levelt matrices, and through the defining rational function `Q = Φ_A / Φ_B`.

This file sets up the carrier and the facts about `Φ_A`, `Φ_B` and `Q` that the later theory
(the Levelt matrices, the gamma vector, reciprocity and the finite hypergeometric sums) reads:

* `Φ_A` and `Φ_B` are monic of degree `d` over every nontrivial commutative ring, and are
  compatible with every change of coefficients;
* they are coprime over every `ℚ`-algebra because `A` and `B` are disjoint; coprimality
  fails over `ℤ` (for `A = {4}`, `B = {2, 1}` the difference `Φ_A - Φ_B` is `2`);
* their constant coefficients are `(-1) ^ m_A` and `(-1) ^ m_B`, with `m_A`, `m_B` the
  multiplicities of `1` in `A` and `B`, at most one of which is positive;
* over a field of characteristic zero, `Φ_A` and `Φ_B` are the normalized numerator and
  denominator of `Q`, and the swap `(A, B) ↦ (B, A)` inverts `Q`.

## Main declarations

* `TauCeti.Hypergeometric.CyclotomicData`: a cyclotomic datum, with its `degree` and the
  `swap`.
* `TauCeti.Hypergeometric.CyclotomicData.phiA`, `phiB`: the cyclotomic products, with
  `monic_phiA`, `natDegree_phiA`, `map_phiA` and `isCoprime_phiA_phiB`.
* `TauCeti.Hypergeometric.CyclotomicData.multOneA`, `multOneB`: the multiplicities of `1`, with
  `coeff_zero_phiA` and `multOneA_mul_multOneB_eq_zero`.
* `TauCeti.Hypergeometric.CyclotomicData.ratFunc`: the defining rational function, with
  `num_ratFunc`, `denom_ratFunc` and `ratFunc_swap`.

## References

* F. Beukers, H. Cohen and A. Mellit, *Finite hypergeometric functions*, Pure Appl. Math. Q. 11
  (2015), §1.
* D. P. Roberts and F. Rodriguez-Villegas, *Hypergeometric motives*, Notices Amer. Math. Soc. 69
  (2022), §2.
-/

public section

open Polynomial

namespace TauCeti.Hypergeometric

/-- A cyclotomic datum `(A, B)`: two multisets of positive integers with no common element and
with equal totient sums. It indexes the hypergeometric family whose local monodromy at `∞` and
at `0` has characteristic polynomials `∏_{a ∈ A} Φ_a` and `∏_{b ∈ B} Φ_b`. -/
@[ext]
structure CyclotomicData where
  /-- The top indices, giving the local monodromy at `∞`. -/
  A : Multiset ℕ
  /-- The bottom indices, giving the local monodromy at `0`. -/
  B : Multiset ℕ
  pos : ∀ n ∈ A + B, 0 < n
  disjoint : Disjoint A B
  totient_sum_eq : (A.map Nat.totient).sum = (B.map Nat.totient).sum

namespace CyclotomicData

/-- The empty datum `(∅, ∅)`, of degree `0`. -/
instance : Inhabited CyclotomicData :=
  ⟨{ A := 0, B := 0, pos := by simp, disjoint := disjoint_bot_left, totient_sum_eq := rfl }⟩

@[simp]
theorem default_A : (default : CyclotomicData).A = 0 := (rfl)

@[simp]
theorem default_B : (default : CyclotomicData).B = 0 := (rfl)

variable (D : CyclotomicData)

theorem pos_of_mem_A {a : ℕ} (ha : a ∈ D.A) : 0 < a :=
  D.pos a (Multiset.mem_add.2 (Or.inl ha))

theorem pos_of_mem_B {b : ℕ} (hb : b ∈ D.B) : 0 < b :=
  D.pos b (Multiset.mem_add.2 (Or.inr hb))

theorem notMem_B_of_mem_A {a : ℕ} (ha : a ∈ D.A) : a ∉ D.B :=
  Multiset.disjoint_left.1 D.disjoint ha

theorem notMem_A_of_mem_B {b : ℕ} (hb : b ∈ D.B) : b ∉ D.A :=
  Multiset.disjoint_right.1 D.disjoint hb

/-! ### Degree and swap -/

/-- The degree `d = ∑_{a ∈ A} φ(a)` of a cyclotomic datum, which is also `∑_{b ∈ B} φ(b)`. -/
def degree : ℕ := (D.A.map Nat.totient).sum

@[simp]
theorem sum_map_totient_A : (D.A.map Nat.totient).sum = D.degree := (rfl)

@[simp]
theorem sum_map_totient_B : (D.B.map Nat.totient).sum = D.degree := D.totient_sum_eq.symm

/-- Only the empty datum has degree `0`, since every index is positive. -/
theorem degree_eq_zero_iff : D.degree = 0 ↔ D.A = 0 ∧ D.B = 0 := by
  have key {S : Multiset ℕ} (hS : ∀ n ∈ S, 0 < n) : (S.map Nat.totient).sum = 0 ↔ S = 0 := by
    refine ⟨fun h ↦ Multiset.eq_zero_of_forall_notMem fun n hn ↦ ?_, fun h ↦ by simp [h]⟩
    have := Multiset.sum_eq_zero_iff.1 h _ (Multiset.mem_map_of_mem _ hn)
    exact (Nat.totient_pos.2 (hS n hn)).ne' this
  rw [← key fun _ ↦ D.pos_of_mem_A, ← key fun _ ↦ D.pos_of_mem_B, sum_map_totient_A,
    sum_map_totient_B, and_self]

/-- The empty datum has degree `0`. -/
@[simp]
theorem degree_default : (default : CyclotomicData).degree = 0 := (rfl)

/-- The swap `(A, B) ↦ (B, A)`. -/
def swap : CyclotomicData where
  A := D.B
  B := D.A
  pos n hn := D.pos n (by rwa [add_comm])
  disjoint := D.disjoint.symm
  totient_sum_eq := D.totient_sum_eq.symm

@[simp]
theorem swap_A : D.swap.A = D.B := (rfl)

@[simp]
theorem swap_B : D.swap.B = D.A := (rfl)

@[simp]
theorem swap_swap : D.swap.swap = D := (rfl)

theorem swap_involutive : Function.Involutive swap := swap_swap

@[simp]
theorem degree_swap : D.swap.degree = D.degree := D.sum_map_totient_B

/-! ### The multiplicities of `1` -/

/-- The multiplicity `m_A` of `1` in `A`, i.e. the number of factors `Φ_1 = X - 1` in the
product `Φ_A`. -/
def multOneA : ℕ := D.A.count 1

/-- The multiplicity `m_B` of `1` in `B`, i.e. the number of factors `Φ_1 = X - 1` in the
product `Φ_B`. -/
def multOneB : ℕ := D.B.count 1

@[simp]
theorem count_one_A : D.A.count 1 = D.multOneA := (rfl)

@[simp]
theorem count_one_B : D.B.count 1 = D.multOneB := (rfl)

@[simp]
theorem multOneA_swap : D.swap.multOneA = D.multOneB := (rfl)

@[simp]
theorem multOneB_swap : D.swap.multOneB = D.multOneA := (rfl)

@[simp]
theorem multOneA_default : (default : CyclotomicData).multOneA = 0 := (rfl)

@[simp]
theorem multOneB_default : (default : CyclotomicData).multOneB = 0 := (rfl)

@[simp]
theorem multOneA_eq_zero_iff : D.multOneA = 0 ↔ 1 ∉ D.A :=
  Multiset.count_eq_zero

@[simp]
theorem multOneB_eq_zero_iff : D.multOneB = 0 ↔ 1 ∉ D.B :=
  Multiset.count_eq_zero

/-- The index `1` lies in at most one of `A` and `B`, so `m_A` and `m_B` are not both
positive. -/
theorem multOneA_mul_multOneB_eq_zero : D.multOneA * D.multOneB = 0 := by
  by_cases h : 1 ∈ D.A
  · rw [D.multOneB_eq_zero_iff.2 (D.notMem_B_of_mem_A h), mul_zero]
  · rw [D.multOneA_eq_zero_iff.2 h, zero_mul]

/-! ### The cyclotomic products -/

variable (R : Type*) [CommRing R]

/-- The product `Φ_A = ∏_{a ∈ A} Φ_a` of cyclotomic polynomials over `R`, the characteristic
polynomial of the local monodromy at `∞`. -/
noncomputable def phiA : R[X] := (D.A.map fun a ↦ cyclotomic a R).prod

/-- The product `Φ_B = ∏_{b ∈ B} Φ_b` of cyclotomic polynomials over `R`, the characteristic
polynomial of the local monodromy at `0`. -/
noncomputable def phiB : R[X] := (D.B.map fun b ↦ cyclotomic b R).prod

theorem phiA_def : D.phiA R = (D.A.map fun a ↦ cyclotomic a R).prod := (rfl)

theorem phiB_def : D.phiB R = (D.B.map fun b ↦ cyclotomic b R).prod := (rfl)

@[simp]
theorem phiA_swap : D.swap.phiA R = D.phiB R := (rfl)

@[simp]
theorem phiB_swap : D.swap.phiB R = D.phiA R := (rfl)

/-- The empty datum has `Φ_A = 1`. -/
@[simp]
theorem phiA_default : (default : CyclotomicData).phiA R = 1 := (rfl)

/-- The empty datum has `Φ_B = 1`. -/
@[simp]
theorem phiB_default : (default : CyclotomicData).phiB R = 1 := (rfl)

theorem monic_phiA : (D.phiA R).Monic :=
  monic_multiset_prod_of_monic _ _ fun a _ ↦ cyclotomic.monic a R

theorem monic_phiB : (D.phiB R).Monic :=
  D.swap.monic_phiA R

@[simp]
theorem natDegree_phiA [Nontrivial R] : (D.phiA R).natDegree = D.degree := by
  rw [phiA_def, natDegree_multiset_prod_of_monic _ (by simpa using fun a _ ↦ cyclotomic.monic a R),
    Multiset.map_map]
  simp [natDegree_cyclotomic]

@[simp]
theorem natDegree_phiB [Nontrivial R] : (D.phiB R).natDegree = D.degree := by
  rw [← phiA_swap, natDegree_phiA, degree_swap]

theorem phiA_ne_zero [Nontrivial R] : D.phiA R ≠ 0 :=
  (D.monic_phiA R).ne_zero

theorem phiB_ne_zero [Nontrivial R] : D.phiB R ≠ 0 :=
  (D.monic_phiB R).ne_zero

/-- The cyclotomic products are compatible with every change of coefficients. -/
@[simp]
theorem map_phiA {S : Type*} [CommRing S] (f : R →+* S) : (D.phiA R).map f = D.phiA S := by
  simp [phiA_def, Polynomial.map_multiset_prod, Multiset.map_map, map_cyclotomic]

@[simp]
theorem map_phiB {S : Type*} [CommRing S] (f : R →+* S) : (D.phiB R).map f = D.phiB S :=
  D.swap.map_phiA R f

/-- The constant coefficient of `Φ_A` is `(-1) ^ m_A`: `Φ_1(0) = -1`, while `Φ_n(0) = 1` for
`n ≠ 1`. -/
@[simp]
theorem coeff_zero_phiA : (D.phiA R).coeff 0 = (-1) ^ D.multOneA := by
  rw [phiA_def, coeff_zero_multiset_prod, Multiset.map_map, ← count_one_A]
  induction D.A using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, Function.comp_apply]
    obtain rfl | rfl | ha := lt_trichotomy a 1 |>.imp_left Nat.lt_one_iff.1
    · simp
    · simp [pow_succ']
    · rw [cyclotomic_coeff_zero R ha, one_mul, Multiset.count_cons_of_ne ha.ne]

@[simp]
theorem coeff_zero_phiB : (D.phiB R).coeff 0 = (-1) ^ D.multOneB :=
  D.swap.coeff_zero_phiA R

/-- Over every `ℚ`-algebra the cyclotomic products `Φ_A` and `Φ_B` are coprime: distinct
cyclotomic polynomials are coprime over `ℚ`, and `A`, `B` have no common index. Over `ℤ` this
fails in general. -/
theorem isCoprime_phiA_phiB [Algebra ℚ R] : IsCoprime (D.phiA R) (D.phiB R) := by
  classical
  rw [← D.map_phiA ℚ (algebraMap ℚ R), ← D.map_phiB ℚ (algebraMap ℚ R)]
  refine IsCoprime.map ?_ (mapRingHom (algebraMap ℚ R))
  rw [phiA_def, phiB_def, Finset.prod_multiset_map_count, Finset.prod_multiset_map_count]
  refine IsCoprime.prod_left fun a ha ↦ IsCoprime.prod_right fun b hb ↦ IsCoprime.pow ?_
  rw [Multiset.mem_toFinset] at ha hb
  exact cyclotomic.isCoprime_rat fun hab ↦ D.notMem_B_of_mem_A ha (hab ▸ hb)

/-! ### The defining rational function -/

variable (K : Type*) [Field K]

/-- The defining rational function `Q = Φ_A / Φ_B` of a cyclotomic datum, over a field `K`. -/
noncomputable def ratFunc : RatFunc K :=
  algebraMap K[X] (RatFunc K) (D.phiA K) / algebraMap K[X] (RatFunc K) (D.phiB K)

theorem ratFunc_def :
    D.ratFunc K = algebraMap K[X] (RatFunc K) (D.phiA K) / algebraMap K[X] (RatFunc K) (D.phiB K) :=
  (rfl)

/-- The swap inverts the defining rational function. -/
@[simp]
theorem ratFunc_swap : D.swap.ratFunc K = (D.ratFunc K)⁻¹ := by
  rw [ratFunc_def, ratFunc_def, inv_div, phiA_swap, phiB_swap]

/-- In characteristic zero, `Φ_A` is the normalized numerator of `Q = Φ_A / Φ_B`. -/
@[simp]
theorem num_ratFunc [CharZero K] : (D.ratFunc K).num = D.phiA K :=
  ((RatFunc.num_eq_and_denom_eq_iff_eq_div (D.isCoprime_phiA_phiB K) (D.monic_phiB K)).2
    (D.ratFunc_def K)).1

/-- In characteristic zero, `Φ_B` is the monic denominator of `Q = Φ_A / Φ_B`. -/
@[simp]
theorem denom_ratFunc [CharZero K] : (D.ratFunc K).denom = D.phiB K :=
  ((RatFunc.num_eq_and_denom_eq_iff_eq_div (D.isCoprime_phiA_phiB K) (D.monic_phiB K)).2
    (D.ratFunc_def K)).2

end CyclotomicData

end TauCeti.Hypergeometric
