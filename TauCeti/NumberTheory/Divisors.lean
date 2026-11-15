/-
Copyright (c) 2023 Arend Mellendijk and 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Arend Mellendijk, OpenAI Codex
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Divisor equivalences, factor pairs, and shifted-index sums

For `N ≠ 0`, `Nat.divisorsEquiv` identifies `N.divisors` with `{M : ℕ // M ∣ N}`, and for `M ∣ N`,
`Nat.mulDvdEquivDivDivisors` identifies `{d : ℕ // d * M ∣ N}` with `(N / M).divisors`, giving
`Nat.card_mul_dvd` (`Nat.card {d : ℕ // d * M ∣ N} = (N / M).divisors.card`).

For `N ≠ 0`, the divisors `d` of `N` with `a = N + d` (respectively `a = N - d`) are at most one,
and such a divisor exists exactly when `a - N` divides `N` (respectively `N - a` divides `a`).
These lemmas evaluate the corresponding indicator sums over `N.divisors`.

`Nat.filter_dvd_divisors_mul` and `Nat.sum_divisors_filter_dvd` reindex divisors divisible by a
fixed `m ∣ n` as `m` times the divisors of `n / m`.

`Nat.sum_divisorsAntidiagonal_ite_dvd` regroups a sum over the factor pairs `(a, b)` of `n`,
restricted to `a ∣ m`, as a sum over the divisors of `gcd(m, n)`.

`Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat` and
`Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat` identify the pairs of
`n.toNat.divisorsAntidiagonal`, for an integer `n`, with the factorisations of `n` into two positive
integers.

`Nat.sum_divisorsAntidiagonal_filter_sub` evaluates differences over the factor pairs with
strictly increasing factors. `Nat.injOn_add_divisorsAntidiagonal_filter_lt` and
`Int.isSquare_sq_sub_four_mul_iff_exists_mem_divisorsAntidiagonal` identify those factor pairs
by their sum and by a positive square discriminant.

For radical `P`, `Nat.pairwiseDisjoint_divisors_pow_filter_dvd` states that the families of
divisors of `d ^ M` divisible by `d` are pairwise disjoint as `d` ranges over the divisors of `P`.

`TauCeti.nontrivialDivisorEquiv` identifies divisors greater than one with the subtype of
`N.divisors` omitting the unit divisor.
-/

public section

namespace Nat

/-- The divisors of `c * m` that are multiples of `c ≠ 0` are `c` times the divisors of `m`. -/
theorem filter_dvd_divisors_mul {c m : ℕ} (hc : c ≠ 0) :
    {d ∈ (c * m).divisors | c ∣ d} = m.divisors.map ⟨(c * ·), mul_right_injective₀ hc⟩ := by
  ext d
  simp only [Finset.mem_filter, mem_divisors, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨hdcm, hcm0⟩, k, rfl⟩
    exact ⟨k, ⟨(mul_dvd_mul_iff_left hc).mp hdcm, right_ne_zero_of_mul hcm0⟩, rfl⟩
  · rintro ⟨k, ⟨hkm, hm0⟩, rfl⟩
    exact ⟨⟨mul_dvd_mul_left c hkm, mul_ne_zero hc hm0⟩, dvd_mul_right c k⟩

/-- For `N ≠ 0`, the finset `N.divisors` is equivalent to `{M : ℕ // M ∣ N}`. -/
def divisorsEquiv (N : ℕ) [NeZero N] : ↥N.divisors ≃ {M : ℕ // M ∣ N} where
  toFun M := ⟨M.1, dvd_of_mem_divisors M.2⟩
  invFun M := ⟨M.1, mem_divisors.mpr ⟨M.2, NeZero.ne N⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem divisorsEquiv_apply (N : ℕ) [NeZero N] (M : ↥N.divisors) :
    divisorsEquiv N M = ⟨M.1, dvd_of_mem_divisors M.2⟩ :=
  (rfl)

@[simp]
theorem coe_divisorsEquiv_symm_apply (N : ℕ) [NeZero N] (M : {M : ℕ // M ∣ N}) :
    ((divisorsEquiv N).symm M : ℕ) = M.1 :=
  (rfl)

/-- For `M ∣ N` with `N ≠ 0`, natural numbers `d` with `d * M ∣ N` correspond to elements of
`(N / M).divisors`. -/
def mulDvdEquivDivDivisors {M N : ℕ} [NeZero N] (hM : M ∣ N) :
    {d : ℕ // d * M ∣ N} ≃ ↥(N / M).divisors where
  toFun d := ⟨d.1, mem_divisors.mpr
    ⟨by
      have hM0 : M ≠ 0 := by rintro rfl; exact NeZero.ne N (zero_dvd_iff.mp hM)
      refine (mul_dvd_mul_iff_left hM0).mp ?_
      rw [mul_comm, Nat.mul_div_cancel' hM]
      exact d.2,
      fun h0 ↦ NeZero.ne N
        (by have := Nat.mul_div_cancel' hM; rw [h0, mul_zero] at this; exact this.symm)⟩⟩
  invFun d := ⟨d.1,
    (mul_comm d.1 M ▸ mul_dvd_mul_left M (dvd_of_mem_divisors d.2)).trans
      (dvd_of_eq (Nat.mul_div_cancel' hM))⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_mulDvdEquivDivDivisors_apply {M N : ℕ} [NeZero N] (hM : M ∣ N)
    (d : {d : ℕ // d * M ∣ N}) :
    (mulDvdEquivDivDivisors hM d : ℕ) = d.1 :=
  (rfl)

@[simp]
theorem coe_mulDvdEquivDivDivisors_symm_apply {M N : ℕ} [NeZero N] (hM : M ∣ N)
    (d : ↥(N / M).divisors) :
    ((mulDvdEquivDivDivisors hM).symm d : ℕ) = d.1 :=
  (rfl)

/-- For `N ≠ 0`, there are only finitely many `d : ℕ` with `d * M ∣ N`. -/
instance instFiniteMulDvd {M N : ℕ} [NeZero N] : Finite {d : ℕ // d * M ∣ N} := by
  by_cases hM : M ∣ N
  · exact Finite.of_equiv _ (mulDvdEquivDivDivisors hM).symm
  · have : IsEmpty {d : ℕ // d * M ∣ N} := ⟨fun d ↦ hM (dvd_of_mul_left_dvd d.2)⟩
    infer_instance

/-- For `M ∣ N`, the cardinality of `{d : ℕ // d * M ∣ N}` is `(N / M).divisors.card`. -/
theorem card_mul_dvd {M N : ℕ} (hM : M ∣ N) :
    Nat.card {d : ℕ // d * M ∣ N} = (N / M).divisors.card := by
  rcases eq_or_ne N 0 with rfl | hN
  · have : Infinite {d : ℕ // d * M ∣ 0} :=
      Infinite.of_injective (fun d : ℕ ↦ ⟨d, dvd_zero _⟩) fun _ _ h ↦ Subtype.mk.inj h
    simp
  · have : NeZero N := ⟨hN⟩
    rw [Nat.card_congr (mulDvdEquivDivDivisors hM), Nat.card_eq_fintype_card, Fintype.card_coe]

variable {M : Type*} [AddCommMonoid M]

/-- The divisors of `n` divisible by `m ∣ n` are `m` times the divisors of `n / m`,
so a sum over those divisors can be reindexed by division by `m`. -/
theorem sum_divisors_filter_dvd {m n : ℕ} (h : m ∣ n) (f : ℕ → M) :
    (∑ d ∈ n.divisors with m ∣ d, f d) = ∑ d ∈ (n / m).divisors, f (m * d) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  have hm : m ≠ 0 := ne_zero_of_dvd_ne_zero hn h
  have hq : n / m ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨hm, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h⟩
  symm
  apply Finset.sum_bij (fun d _ ↦ m * d)
  · intro d hd
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(Nat.mul_dvd_mul_left m (Nat.dvd_of_mem_divisors hd)).trans
        (by rw [Nat.mul_div_cancel' h]), hn⟩, dvd_mul_right _ _⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) hab
  · intro d hd
    obtain ⟨hd, hmd⟩ := Finset.mem_filter.mp hd
    refine ⟨d / m, Nat.mem_divisors.mpr ⟨Nat.div_dvd_div hmd (Nat.dvd_of_mem_divisors hd), hq⟩, ?_⟩
    exact Nat.mul_div_cancel' hmd
  · intro d _
    rfl

/-- The sum over the divisors `d` of `N` of `f d` restricted to `a = N + d`. -/
theorem sum_divisors_ite_eq_add {N : ℕ} (hN : N ≠ 0) (a : ℕ) (f : ℕ → M) :
    ∑ d ∈ N.divisors, (if a = N + d then f d else 0) =
      if N < a ∧ a - N ∣ N then f (a - N) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (a - N)]
    · rw [ite_eq_left (by omega)]
    · intro d _ hd
      rw [ite_eq_right (by omega)]
    · intro h'
      exact absurd (Nat.mem_divisors.mpr ⟨h.2, hN⟩) h'
  · refine Finset.sum_eq_zero fun d hd ↦ ite_eq_right fun ha ↦ h ⟨?_, ?_⟩
    · have := Nat.pos_of_mem_divisors hd
      omega
    · have had : a - N = d := by omega
      rw [had]
      exact Nat.dvd_of_mem_divisors hd

/-- The sum over the divisors `d` of `N` of `f d` restricted to `a = N - d`. -/
theorem sum_divisors_ite_eq_sub {N : ℕ} (a : ℕ) (f : ℕ → M) :
    ∑ d ∈ N.divisors, (if a = N - d then f d else 0) =
      if a < N ∧ N - a ∣ a then f (N - a) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (N - a)]
    · rw [ite_eq_left (by omega)]
    · intro d hd hne
      have := Nat.divisor_le hd
      rw [ite_eq_right (by omega)]
    · refine fun h' ↦ absurd (Nat.mem_divisors.mpr ⟨?_, by omega⟩) h'
      have h'' := Nat.dvd_add_self_right.mpr h.2
      rwa [Nat.add_sub_cancel' h.1.le] at h''
  · refine Finset.sum_eq_zero fun d hd ↦ ite_eq_right fun ha ↦ h ⟨?_, ?_⟩
    · have := Nat.pos_of_mem_divisors hd
      have := Nat.divisor_le hd
      omega
    · have := Nat.divisor_le hd
      have had : N - a = d := by omega
      have hN' : N = a + d := by omega
      rw [had]
      have h' := Nat.dvd_of_mem_divisors hd
      rwa [hN', Nat.dvd_add_self_right] at h'

/-- Regrouping a sum over the factor pairs `(a, b)` of `n ≠ 0`, restricted to `a ∣ m`, by the
divisors `d` of `gcd(m, n)`: the pair `(d, n / d)` contributes `f d (m * n / d ^ 2)`, since
`(n / d) * (m / d) = m * n / d ^ 2`. -/
theorem sum_divisorsAntidiagonal_ite_dvd {n : ℕ} (hn : n ≠ 0) (m : ℕ) (f : ℕ → ℕ → M) :
    ∑ p ∈ n.divisorsAntidiagonal, (if p.1 ∣ m then f p.1 (p.2 * (m / p.1)) else 0) =
      ∑ d ∈ (m.gcd n).divisors, f d (m * n / d ^ 2) := by
  rw [Nat.sum_divisorsAntidiagonal fun a b ↦ if a ∣ m then f a (b * (m / a)) else 0,
    ← Finset.sum_filter]
  have hs : {a ∈ n.divisors | a ∣ m} = (m.gcd n).divisors := by
    ext a
    simp [Nat.dvd_gcd_iff, hn, Nat.gcd_eq_zero_iff, and_comm]
  rw [hs]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha' := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors ha)
  rw [Nat.div_mul_div_comm ha'.2 ha'.1, ← sq, mul_comm n m]

/-- On the factor pairs with increasing factors, subtracting the value at the smaller factor
from that at the larger factor is the full divisor sum minus the sum at the minimum factor. -/
theorem sum_divisorsAntidiagonal_filter_sub {A : Type*} [AddCommGroup A]
    (n : ℕ) (f : ℕ → A) :
    (∑ p ∈ n.divisorsAntidiagonal with p.1 < p.2, (f p.2 - f p.1)) =
      (∑ d ∈ n.divisors, f d) - ∑ p ∈ n.divisorsAntidiagonal, f (min p.1 p.2) := by
  classical
  rw [← sum_divisorsAntidiagonal' (fun _ d ↦ f d), ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.1 < p.2
  · simp [h, min_eq_left h.le]
  · simp [h, min_eq_right (by omega : p.2 ≤ p.1)]

/-- A factor pair with strictly increasing factors is determined by its sum. -/
theorem injOn_add_divisorsAntidiagonal_filter_lt (n : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2)
      ↑(n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2)) := by
  intro p hp q hq hsum
  obtain ⟨hp, hplt⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqlt⟩ := Finset.mem_filter.mp hq
  dsimp only at hsum
  have hmul : (p.1 : ℤ) * p.2 = (q.1 : ℤ) * q.2 := by
    exact_mod_cast (mem_divisorsAntidiagonal.mp hp).1.trans
      (mem_divisorsAntidiagonal.mp hq).1.symm
  have hprod : ((p.1 : ℤ) - q.1) * ((p.1 : ℤ) - q.2) = 0 := by nlinarith
  rcases _root_.mul_eq_zero.mp hprod with h | h
  · exact Prod.ext (by omega) (by omega)
  · omega

end Nat

namespace Int

variable {n : ℤ}

/-- The factors of a pair in `n.toNat.divisorsAntidiagonal` are positive integers with product
`n`. -/
theorem pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat {p : ℕ × ℕ}
    (hp : p ∈ n.toNat.divisorsAntidiagonal) :
    0 < (p.1 : ℤ) ∧ 0 < (p.2 : ℤ) ∧ (p.1 : ℤ) * p.2 = n := by
  obtain ⟨h, h0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  obtain ⟨h1, h2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
  refine ⟨by omega, by omega, ?_⟩
  rw [← Nat.cast_mul, h]
  omega

/-- A factorisation `n = u v` into positive integers is the pair `(u.toNat, v.toNat)` of
`n.toNat.divisorsAntidiagonal`. -/
theorem prodMk_toNat_mem_divisorsAntidiagonal_toNat {u v : ℤ} (hu : 0 < u) (hv : 0 < v)
    (h : u * v = n) : (u.toNat, v.toNat) ∈ n.toNat.divisorsAntidiagonal := by
  have hn : 0 < n := h ▸ mul_pos hu hv
  have h' : ((u.toNat * v.toNat : ℕ) : ℤ) = (n.toNat : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg hu.le, Int.toNat_of_nonneg hv.le, Int.toNat_of_nonneg hn.le, h]
  exact Nat.mem_divisorsAntidiagonal.mpr ⟨by exact_mod_cast h', by omega⟩

/-- At positive discriminant and determinant, a square discriminant is equivalent to a
positive factorisation with increasing factors and sum equal to the absolute trace. -/
theorem isSquare_sq_sub_four_mul_iff_exists_mem_divisorsAntidiagonal
    (n : ℕ) (hn : 0 < n) (t : ℤ) (hD : 4 * (n : ℤ) < t ^ 2) :
    IsSquare (t ^ 2 - 4 * (n : ℤ)) ↔
      ∃ p ∈ n.divisorsAntidiagonal, p.1 < p.2 ∧ |t| = (p.1 : ℤ) + p.2 := by
  constructor
  · rintro ⟨u, hu⟩
    have hu' : t ^ 2 - 4 * (n : ℤ) = |u| ^ 2 := by nlinarith [sq_abs u]
    -- The trace and the square root have the same parity, so both roots are integral.
    have hpar : (|t| - |u|) % 2 = 0 := by
      have he : Even (|t| ^ 2 - |u| ^ 2) := ⟨2 * n, by nlinarith [sq_abs t]⟩
      have heq : Even |t| ↔ Even |u| := by
        simpa only [Int.even_pow' (by decide : (2 : ℕ) ≠ 0)] using Int.even_sub.mp he
      exact Int.even_iff.mp (Int.even_sub.mpr heq)
    let a := (|t| - |u|) / 2
    let d := (|t| + |u|) / 2
    have hprod : (|t| - |u|) * (|t| + |u|) = 4 * n := by nlinarith [sq_abs t]
    have htu : |u| < |t| := by nlinarith [abs_nonneg t, abs_nonneg u, sq_abs t]
    have hu0 : 0 < |u| := by nlinarith [abs_nonneg u]
    have ha : 0 < a := by dsimp [a]; omega
    have had : a < d := by dsimp [a, d]; omega
    have hadd : a + d = |t| := by dsimp [a, d]; omega
    have hmul : a * d = n := by
      have ha2 : 2 * a = |t| - |u| := by dsimp [a]; omega
      have hd2 : 2 * d = |t| + |u| := by dsimp [d]; omega
      nlinarith [hd2]
    refine ⟨(a.toNat, d.toNat), ?_, by omega, by omega⟩
    simpa only [Int.toNat_natCast] using
      prodMk_toNat_mem_divisorsAntidiagonal_toNat ha (by omega) hmul
  · rintro ⟨p, hp, _, ht⟩
    have hm : (p.1 : ℤ) * p.2 = n := by exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
    refine ⟨(p.2 : ℤ) - p.1, ?_⟩
    nlinarith [sq_abs t]

end Int

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- Divisors greater than one correspond to positive divisors other than the unit divisor. -/
def nontrivialDivisorEquiv :
    {d : ℕ // 1 < d ∧ d ∣ N} ≃
      {d : N.divisors // d ≠ ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne N)⟩} where
  toFun d := ⟨⟨d.val, Nat.mem_divisors.mpr ⟨d.property.2, NeZero.ne N⟩⟩,
    fun h ↦ by have := congrArg Subtype.val h; simp at this; omega⟩
  invFun d := ⟨d.val.val, by
    have hdpos := Nat.pos_of_mem_divisors d.val.property
    have hdne : d.val.val ≠ 1 := fun h ↦ d.property (Subtype.ext h)
    exact ⟨by omega, Nat.dvd_of_mem_divisors d.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The divisor equivalence preserves the underlying natural number. -/
@[simp]
theorem nontrivialDivisorEquiv_apply_val (d : {d : ℕ // 1 < d ∧ d ∣ N}) :
    (nontrivialDivisorEquiv d).val.val = d.val := by rfl

/-- The inverse divisor equivalence preserves the underlying natural number. -/
@[simp]
theorem nontrivialDivisorEquiv_symm_apply_val
    (d : {d : N.divisors // d ≠ ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne N)⟩}) :
    (nontrivialDivisorEquiv.symm d).val = d.val.val := by rfl

end TauCeti

namespace Nat

open Finset

/-- For radical `P`, the divisors of `d ^ M` divisible by `d` are disjoint as `d` ranges
through the divisors of `P`. This is the prime-support partition used by the Selberg sieve. -/
theorem pairwiseDisjoint_divisors_pow_filter_dvd {P : ℕ} (hP : IsRadical P) (M : ℕ) :
    (P.divisors : Set ℕ).PairwiseDisjoint
      (fun d ↦ (d ^ M).divisors.filter (d ∣ ·)) := by
  intro i hi j hj hij
  have hPsq := IsRadical.squarefree (Nat.ne_zero_of_mem_divisors hi) hP
  apply Finset.disjoint_left.mpr
  intro m hmi hmj
  obtain ⟨hmi, him⟩ := mem_filter.mp hmi
  obtain ⟨hmj, hjm⟩ := mem_filter.mp hmj
  have hij' : i ∣ j := (hPsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hi)).isRadical
    M j (him.trans (Nat.dvd_of_mem_divisors hmj))
  have hji' : j ∣ i := (hPsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hj)).isRadical
    M i (hjm.trans (Nat.dvd_of_mem_divisors hmi))
  exact hij (Nat.dvd_antisymm hij' hji')

end Nat
