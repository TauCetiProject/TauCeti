/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Data.Matrix.Mul
import TauCeti.Data.Int.LinearDiophantine
import TauCeti.Algebra.Order.BigOperators.Sum.NatSub
import TauCeti.Computability.Primrec.Bitwise
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-!
# Small solutions of linear Diophantine systems over the natural numbers

Below every solution `x` in natural numbers of a system `A *ᵥ x = b` of linear equations with
integer coefficients lies a solution whose entries are bounded by a primitive-recursive function
of a common bound `M` for the number of unknowns, the absolute values of the coefficients and
the absolute values of the right-hand sides. The number of equations does not matter: the rows
of a matrix with at most `M` columns and entries in `[-M, M]` take at most `(2 * M + 1) ^ M`
values. Only the primitive recursiveness of the bounds is asserted, not a particular formula.

The bound for a homogeneous system is proved by induction on the number of distinct equations,
starting from the bound `TauCeti.exists_le_sum_mul_eq_zero` for one equation: every solution of
one equation is a combination, with coefficients in `ℕ`, of its nonzero solutions of total size
at most `2 * M + 1`, and the remaining equations become a system with one equation fewer in the
multiplicities. An inhomogeneous system is made homogeneous by one further unknown.

## Main results

* `TauCeti.exists_primrec_bound_le_mulVec_eq_zero`: a nonzero solution of a homogeneous system
  lies above a nonzero solution of primitive-recursively bounded total size.
* `TauCeti.exists_primrec_bound_le_mulVec_eq`: a solution of `A *ᵥ x = b` lies above a solution
  with primitive-recursively bounded entries.

## References

* J. von zur Gathen, M. Sieveking, *A bound on solutions of linear integer equalities and
  inequalities*, Proc. Amer. Math. Soc. 72 (1978), 155–158, for the classical, much sharper bound
  on the size of some solution of a solvable system.
* V. Diekert, A. Jez, W. Plandowski, *Finding all solutions of equations in free groups and
  monoids with involution*, arXiv:1405.5133, §1.4 and §3.2, where small solutions of linear
  Diophantine systems over the natural numbers are used.
-/

public section

universe u v

namespace TauCeti

open Finset Matrix

variable {ι : Type*} [Fintype ι]

/- After one equation is eliminated, the number of unknowns and the coefficients of the system
in the multiplicities are at most `sizeBound M`. -/
private def sizeBound (M : ℕ) : ℕ :=
  (2 * M + 2) ^ M + M * (2 * M + 1)

/- One step of the bound: `(M, P) ↦ (sizeBound M, P * (2 * M + 1))`. -/
private def boundStep (p : ℕ × ℕ) : ℕ × ℕ :=
  (sizeBound p.1, p.2 * (2 * p.1 + 1))

/- The bound for homogeneous systems, with at most `(2 * M + 1) ^ M` distinct equations. -/
private def homogeneousBound (M : ℕ) : ℕ :=
  (boundStep^[(2 * M + 1) ^ M] (M, 1)).2

private lemma primrec_homogeneousBound : Primrec homogeneousBound := by
  have h1 : Primrec fun M : ℕ => 2 * M + 1 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) .id) (.const 1)
  have hsize : Primrec sizeBound := Primrec.nat_add.comp (Primrec.nat_pow.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) .id) (.const 2)) .id)
    (Primrec.nat_mul.comp .id h1)
  have hstep : Primrec boundStep :=
    Primrec.pair (hsize.comp .fst) (Primrec.nat_mul.comp .snd (h1.comp .fst))
  exact Primrec.snd.comp <| Primrec.nat_iterate (Primrec.nat_pow.comp h1 .id)
    (Primrec.pair .id (.const 1)) (hstep.comp .snd).to₂

/- Every solution of one homogeneous equation is a combination, with coefficients in `ℕ`, of
the nonzero solutions of total size at most `2 * H + 1`. -/
private lemma exists_sum_mul_eq {a : ι → ℤ} {H : ℕ} (ha : ∀ j, |a j| ≤ H) (S : Finset (ι → ℕ))
    (hS : ∀ y : ι → ℕ, y ≠ 0 → ∑ j, a j * y j = 0 → ∑ j, y j ≤ 2 * H + 1 → y ∈ S) (x : ι → ℕ)
    (hx : ∑ j, a j * x j = 0) :
    ∃ c : S → ℕ, ∀ j, ∑ s, c s * (s : ι → ℕ) j = x j := by
  classical
  induction h : ∑ j, x j using Nat.strong_induction_on generalizing x with
  | _ N ih =>
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  obtain ⟨y, hy0, hyx, hy, hyH⟩ := exists_le_sum_mul_eq_zero a H ha x hx hx0
  obtain ⟨c, hc⟩ := ih _ (h ▸ sum_tsub_lt_sum hyx hy0) (x - y)
    (by simp [Nat.cast_sub (hyx _), mul_sub, hx, hy]) rfl
  refine ⟨fun s => c s + if s = ⟨y, hS y hy0 hy hyH⟩ then 1 else 0, fun j => ?_⟩
  simpa only [add_mul, sum_add_distrib, hc, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq',
    Pi.sub_apply] using Nat.sub_add_cancel (hyx j)

/- A set of at most `r + 1` rows solved by `x` is covered by one row `a` solved by `x` and at most
`r` of its rows. -/
private lemma exists_forall_mem_eq_or_mem {R : Finset (ι → ℤ)} {r M : ℕ} (hR : #R ≤ r + 1)
    (hRM : ∀ a ∈ R, ∀ j, |a j| ≤ M) {x : ι → ℕ} (hx : ∀ a ∈ R, ∑ j, a j * x j = 0) :
    ∃ a R', R' ⊆ R ∧ (∀ b ∈ R, b = a ∨ b ∈ R') ∧ #R' ≤ r ∧ (∀ j, |a j| ≤ M) ∧
      ∑ j, a j * x j = 0 := by
  classical
  rcases R.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, ∅, by simp, by simp, by simp, by simp, by simp⟩
  exact ⟨a, R.erase a, erase_subset _ _,
    fun b hb => (eq_or_ne b a).imp_right fun hba => mem_erase.mpr ⟨hba, hb⟩,
    by grind [card_erase_of_mem], hRM a ha, hx a ha⟩

/- The nonzero solutions of total size at most `2 * M + 1` of one row `a` with `|a j| ≤ M` form a
set of at most `sizeBound M` vectors, of which every solution of `a` is a combination with
coefficients in `ℕ`. -/
private lemma exists_finset_sum_mul_eq {a : ι → ℤ} {M : ℕ} (hι : Fintype.card ι ≤ M)
    (ha : ∀ j, |a j| ≤ M) (x : ι → ℕ) (hx : ∑ j, a j * x j = 0) :
    ∃ S : Finset (ι → ℕ), #S ≤ sizeBound M ∧
      (∀ s ∈ S, s ≠ 0 ∧ ∑ j, a j * s j = 0 ∧ ∑ j, s j ≤ 2 * M + 1) ∧
      ∃ c : S → ℕ, ∀ j, ∑ s, c s * (s : ι → ℕ) j = x j := by
  classical
  refine ⟨{s ∈ Fintype.piFinset (fun _ : ι => range (2 * M + 1 + 1)) |
    s ≠ 0 ∧ ∑ j, a j * s j = 0 ∧ ∑ j, s j ≤ 2 * M + 1}, ?_, fun s hs => (mem_filter.mp hs).2,
    exists_sum_mul_eq ha _ (fun y hy0 hy hyM => mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j =>
      mem_range.mpr <| Nat.lt_succ_of_le <| (single_le_sum (fun j _ => Nat.zero_le (y j))
        (mem_univ j)).trans hyM, hy0, hy, hyM⟩) x hx⟩
  calc _ ≤ #(Fintype.piFinset fun _ : ι => range (2 * M + 1 + 1)) := card_filter_le _ _
    _ = (2 * M + 2) ^ Fintype.card ι := by simp
    _ ≤ (2 * M + 2) ^ M := Nat.pow_le_pow_right (by lia) hι
    _ ≤ sizeBound M := Nat.le_add_right _ _

/- A row with entries in `[-M, M]` takes values of absolute value at most `sizeBound M` on vectors
of total size at most `2 * M + 1`. -/
private lemma abs_sum_mul_le_sizeBound {r : ι → ℤ} {M : ℕ} (hr : ∀ j, |r j| ≤ M) {s : ι → ℕ}
    (hs : ∑ j, s j ≤ 2 * M + 1) : |∑ j, r j * s j| ≤ sizeBound M := by
  have hM : M * ∑ j, s j ≤ sizeBound M :=
    (Nat.mul_le_mul_left M hs).trans (Nat.le_add_left _ _)
  refine (abs_sum_le_sum_abs _ _).trans <| le_trans ?_ (Int.ofNat_le.mpr hM)
  push_cast
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_right (hr j) (Nat.cast_nonneg _)

/- Lifting back: a nonzero `c' ≤ c` that solves the rows of `R'` read over the unknowns `S` gives
the nonzero solution `∑ s, c' s • s ≤ x` of the rows of `R`, where `x = ∑ s, c s • s`. -/
private lemma exists_le_forall_sum_mul_eq_zero_of_multiplicities {a : ι → ℤ} {R R' : Finset (ι → ℤ)}
    (hRR' : ∀ b ∈ R, b = a ∨ b ∈ R') {M : ℕ} {S : Finset (ι → ℕ)}
    (hS : ∀ s ∈ S, s ≠ 0 ∧ ∑ j, a j * s j = 0 ∧ ∑ j, s j ≤ 2 * M + 1) {x : ι → ℕ} {c c' : S → ℕ}
    (hc : ∀ j, ∑ s, c s * (s : ι → ℕ) j = x j) (hc'0 : c' ≠ 0) (hc'c : c' ≤ c)
    (hc'R : ∀ b ∈ R', ∑ s : S, (∑ j, b j * (s : ι → ℕ) j) * c' s = 0) :
    ∃ y : ι → ℕ, y ≠ 0 ∧ y ≤ x ∧ (∀ b ∈ R, ∑ j, b j * y j = 0) ∧
      ∑ j, y j ≤ (2 * M + 1) * ∑ s, c' s := by
  refine ⟨fun j => ∑ s : S, c' s * (s : ι → ℕ) j, ?_,
    fun j => hc j ▸ sum_le_sum fun t _ => Nat.mul_le_mul_right _ (hc'c t), fun b hb => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := Function.ne_iff.mp hc'0
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hS t t.property).1
    refine Function.ne_iff.mpr ⟨j, ((Nat.pos_of_ne_zero (mul_ne_zero ht hj)).trans_le ?_).ne'⟩
    exact single_le_sum (f := fun t : S => c' t * (t : ι → ℕ) j) (fun _ _ => Nat.zero_le _)
      (mem_univ t)
  · suffices ∑ t : S, (∑ j, b j * (t : ι → ℕ) j : ℤ) * c' t = 0 by
      simpa [mul_sum, sum_mul, mul_comm, mul_left_comm, sum_comm (γ := S)] using this
    rcases hRR' b hb with rfl | hb'
    · exact sum_eq_zero fun t _ => by rw [(hS t t.property).2.1, zero_mul]
    · exact hc'R b hb'
  · rw [sum_comm, mul_sum]
    refine sum_le_sum fun t _ => ?_
    rw [← mul_sum, mul_comm (2 * M + 1)]
    exact Nat.mul_le_mul_left _ (hS t t.property).2.2

private lemma boundStep_apply (M P : ℕ) : boundStep (M, P) = (sizeBound M, P * (2 * M + 1)) :=
  rfl

/- The induction on the number of distinct equations. -/
private lemma exists_le_forall_sum_mul_eq_zero (r M P : ℕ) (R : Finset (ι → ℤ))
    (hι : Fintype.card ι ≤ M) (hR : #R ≤ r) (hRM : ∀ a ∈ R, ∀ j, |a j| ≤ M) (x : ι → ℕ)
    (hx : ∀ a ∈ R, ∑ j, a j * x j = 0) (hx0 : x ≠ 0) :
    ∃ y : ι → ℕ, y ≠ 0 ∧ y ≤ x ∧ (∀ a ∈ R, ∑ j, a j * y j = 0) ∧
      P * ∑ j, y j ≤ (boundStep^[r] (M, P)).2 := by
  induction r generalizing ι M P R x with
  | zero =>
    obtain ⟨y, hy0, hyx, -, hy⟩ :=
      exists_le_sum_mul_eq_zero (0 : ι → ℤ) 0 (by simp) x (by simp) hx0
    obtain rfl : R = ∅ := card_eq_zero.mp (Nat.le_zero.mp hR)
    exact ⟨y, hy0, hyx, by simp, by simpa using mul_le_of_le_one_right (Nat.zero_le P) hy⟩
  | succ r ih =>
    classical
    obtain ⟨a, R', hR'R, hRR', hR', ha, hxa⟩ := exists_forall_mem_eq_or_mem hR hRM hx
    obtain ⟨S, hScard, hS, c, hc⟩ := exists_finset_sum_mul_eq hι ha x hxa
    -- the multiplicities `c` solve the rows of `R'`, read as rows over the unknowns `S`
    obtain ⟨c', hc'0, hc'c, hc'R, hc'P⟩ := ih (sizeBound M) (P * (2 * M + 1))
      (R'.image fun b (s : S) => ∑ j, b j * (s : ι → ℕ) j) (by simpa using hScard)
      (card_image_le.trans hR')
      (by simpa only [forall_mem_image] using fun b hb (s : S) =>
        abs_sum_mul_le_sizeBound (hRM b (hR'R hb)) (hS s s.property).2.2)
      c
      (by
        simp only [forall_mem_image]
        intro b hb
        simpa [← hc, mul_sum, sum_mul, mul_comm, mul_left_comm, sum_comm (γ := S)] using
          hx b (hR'R hb))
      (fun hc0 => hx0 (funext fun j => by simp [← hc j, hc0]))
    obtain ⟨y, hy0, hyx, hyR, hy⟩ := exists_le_forall_sum_mul_eq_zero_of_multiplicities hRR' hS
      hc hc'0 hc'c fun b hb => hc'R _ (mem_image_of_mem _ hb)
    refine ⟨y, hy0, hyx, hyR, ?_⟩
    rw [Function.iterate_succ_apply, boundStep_apply]
    exact le_trans (by simpa [mul_assoc] using Nat.mul_le_mul_left P hy) hc'P

/- The rows of a matrix with entries in `[-M, M]` and at most `M` columns form a set of at most
`(2 * M + 1) ^ M` vectors with entries in `[-M, M]` and the same solutions. -/
private lemma exists_finset_forall_sum_mul_eq_zero_iff {m n : Type*} [Fintype n] {M : ℕ}
    (A : Matrix m n ℤ) (hn : Fintype.card n ≤ M) (hA : ∀ i j, |A i j| ≤ M) :
    ∃ R : Finset (n → ℤ), #R ≤ (2 * M + 1) ^ M ∧ (∀ r ∈ R, ∀ j, |r j| ≤ M) ∧
      ∀ x : n → ℕ, A *ᵥ (fun j => (x j : ℤ)) = 0 ↔ ∀ r ∈ R, ∑ j, r j * x j = 0 := by
  classical
  have hAR : ∀ i, A i ∈ Fintype.piFinset fun _ : n => Icc (-(M : ℤ)) M :=
    fun i => Fintype.mem_piFinset.mpr fun j => mem_Icc.mpr (abs_le.mp (hA i j))
  refine ⟨{r ∈ Fintype.piFinset fun _ : n => Icc (-(M : ℤ)) M | ∃ i, A i = r}, ?_, ?_, fun x => ?_⟩
  · calc _ ≤ #(Fintype.piFinset fun _ : n => Icc (-(M : ℤ)) M) := card_filter_le _ _
      _ = (2 * M + 1) ^ Fintype.card n := by
        simp only [Fintype.card_piFinset, Int.card_Icc, prod_const, card_univ]
        lia
      _ ≤ (2 * M + 1) ^ M := Nat.pow_le_pow_right (by lia) hn
  · simp only [mem_filter, and_imp, forall_exists_index]
    rintro _ - i rfl
    exact hA i
  · rw [funext_iff]
    simp only [mulVec, dotProduct, Pi.zero_apply, mem_filter, and_imp, forall_exists_index]
    exact ⟨fun h _ _ i hi => hi ▸ h i, fun h i => h _ (hAR i) i rfl⟩

/- The homogenization `A x - b t` of `A x = b`, with the unknown `t` at `none`. -/
private def homogenization {m n : Type*} (A : Matrix m n ℤ) (b : m → ℤ) : Matrix m (Option n) ℤ :=
  fun i o => o.elim (-b i) (A i)

private lemma mulVec_natCast_homogenization {m n : Type*} [Fintype n] (A : Matrix m n ℤ) (b : m → ℤ)
    (z : Option n → ℕ) : homogenization A b *ᵥ (fun o => (z o : ℤ)) =
      A *ᵥ (fun j => (z (some j) : ℤ)) - (z none : ℤ) • b := by
  funext i
  simp only [homogenization, mulVec, dotProduct, Fintype.sum_option, Option.elim_none,
    Option.elim_some, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma abs_homogenization_le {m n : Type*} {M : ℕ} {A : Matrix m n ℤ} {b : m → ℤ}
    (hA : ∀ i j, |A i j| ≤ M) (hb : ∀ i, |b i| ≤ M) (i : m) (o : Option n) :
    |homogenization A b i o| ≤ M := by
  cases o <;> simp [homogenization, hA, hb]

/- Below a solution of `A x = b` lies a solution with entries at most `B` if below every nonzero
solution of the homogenization lies a nonzero solution of total size at most `B`. -/
private lemma exists_le_mulVec_eq_of_homogenization {m n : Type*} [Fintype n] (A : Matrix m n ℤ)
    (b : m → ℤ) {B : ℕ} (hB : ∀ z : Option n → ℕ, homogenization A b *ᵥ (fun o => (z o : ℤ)) = 0 →
      z ≠ 0 → ∃ y : Option n → ℕ, y ≠ 0 ∧ y ≤ z ∧
        homogenization A b *ᵥ (fun o => (y o : ℤ)) = 0 ∧ ∑ o, y o ≤ B) (x : n → ℕ)
    (hx : A *ᵥ (fun j => (x j : ℤ)) = b) :
    ∃ y : n → ℕ, y ≤ x ∧ A *ᵥ (fun j => (y j : ℤ)) = b ∧ ∀ j, y j ≤ B := by
  induction hN : ∑ j, x j using Nat.strong_induction_on generalizing x with
  | _ N ih =>
  obtain ⟨y, hy0, hyx, hy, hyB⟩ := hB (fun o => o.elim 1 x)
    (by rw [mulVec_natCast_homogenization]; simp [hx]) (fun h => by simpa using congrFun h none)
  rw [mulVec_natCast_homogenization] at hy
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hyx none) with h0 | h1
  · -- `y` restricts to a nonzero solution of `A y' = 0` below `x`
    have hy'x : (fun j => y (some j)) ≤ x := fun j => hyx (some j)
    have hy'0 : (fun j => y (some j)) ≠ 0 := fun h => hy0 <| funext fun o => by
      cases o with
      | none => exact h0
      | some j => exact congrFun h j
    rw [h0, Nat.cast_zero, zero_smul, sub_zero] at hy
    obtain ⟨z, hzx, hz, hzB⟩ := ih _ (hN ▸ sum_tsub_lt_sum hy'x hy'0) _
      (by rw [← sub_zero b, ← hx, ← hy, ← mulVec_sub]; congr with j; simp [Nat.cast_sub (hy'x j)])
      rfl
    exact ⟨z, fun j => (hzx j).trans (Nat.sub_le _ _), hz, hzB⟩
  · rw [h1, sub_eq_zero] at hy
    refine ⟨fun j => y (some j), fun j => hyx (some j), by simpa using hy, fun j => ?_⟩
    exact (single_le_sum (fun o _ => Nat.zero_le (y o)) (mem_univ (some j))).trans hyB

/-- A nonzero solution in natural numbers of a homogeneous linear system with integer
coefficients lies coordinatewise above a nonzero solution whose entries add up to at most
`β M`, where `β` is primitive recursive and `M` bounds the number of unknowns and the absolute
values of the coefficients; the equations may be indexed by any type. -/
theorem exists_primrec_bound_le_mulVec_eq_zero :
    ∃ β : ℕ → ℕ, Primrec β ∧ ∀ {m : Type u} {n : Type v} [Fintype n] (M : ℕ) (A : Matrix m n ℤ),
      Fintype.card n ≤ M → (∀ i j, |A i j| ≤ M) → ∀ x : n → ℕ, A *ᵥ (fun j => (x j : ℤ)) = 0 →
        x ≠ 0 → ∃ y : n → ℕ, y ≠ 0 ∧ y ≤ x ∧ A *ᵥ (fun j => (y j : ℤ)) = 0 ∧ ∑ j, y j ≤ β M := by
  refine ⟨homogeneousBound, primrec_homogeneousBound, fun {m n} _ M A hn hA x hx hx0 => ?_⟩
  obtain ⟨R, hcard, hRM, hR⟩ := exists_finset_forall_sum_mul_eq_zero_iff A hn hA
  obtain ⟨y, hy0, hyx, hyR, hy⟩ :=
    exists_le_forall_sum_mul_eq_zero _ M 1 R hn hcard hRM x ((hR x).mp hx) hx0
  exact ⟨y, hy0, hyx, (hR y).mpr hyR, by simpa [homogeneousBound] using hy⟩

/-- **Small solutions of linear Diophantine systems.** There is a primitive-recursive function
`δ` such that below every solution in natural numbers of a system `A *ᵥ x = b` with integer
coefficients, at most `M` unknowns, coefficients and right-hand sides of absolute value at most
`M`, and any number of equations, lies a solution with all entries at most `δ M`. -/
theorem exists_primrec_bound_le_mulVec_eq :
    ∃ δ : ℕ → ℕ, Primrec δ ∧ ∀ {m : Type u} {n : Type v} [Fintype n] (M : ℕ) (A : Matrix m n ℤ)
      (b : m → ℤ), Fintype.card n ≤ M → (∀ i j, |A i j| ≤ M) → (∀ i, |b i| ≤ M) → ∀ x : n → ℕ,
        A *ᵥ (fun j => (x j : ℤ)) = b →
          ∃ y : n → ℕ, y ≤ x ∧ A *ᵥ (fun j => (y j : ℤ)) = b ∧ ∀ j, y j ≤ δ M := by
  obtain ⟨β, hβ, hβA⟩ := exists_primrec_bound_le_mulVec_eq_zero.{u, v}
  refine ⟨fun M => β (M + 1), hβ.comp .succ, fun {m n} _ M A b hn hA hb => ?_⟩
  exact exists_le_mulVec_eq_of_homogenization A b fun z => hβA (M + 1) (homogenization A b)
    (by simpa using hn) (abs_homogenization_le (fun i j => (hA i j).trans (by simp))
      fun i => (hb i).trans (by simp)) z

end TauCeti
