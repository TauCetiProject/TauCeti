/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Perfectoid.PerfectRing
import TauCeti.Analysis.Normed.Field.Basic

/-!
# Perfectoid fields

Fix a prime `p`. A *perfectoid field* is a complete nontrivially normed field `K` with an
ultrametric norm which is a perfectoid Tate ring at `p`. Here `K` carries its Tate ring structure
`TauCeti.Huber.IsTateRing.of_nontriviallyNormedField`: the power-bounded subring `K°` is the closed
unit ball and the pseudouniformisers are the nonzero elements of norm less than one.

The main result is Scholze's intrinsic characterisation: `K` is a perfectoid field exactly when

* (i) `K` is not discretely valued: its norms accumulate at `1`;
* (ii) `‖p‖ < 1`; and
* (iii) the `p`-th power map on `K° ⧸ p` is surjective.

Condition (i) cannot be dropped: `ℚ_p` satisfies (ii) and (iii) but is not perfectoid. On the way
we show that the value group of a perfectoid field is `p`-divisible: every norm `‖x‖` is the `p`-th
power of a norm. The proof of (i) iterates this, producing norms `‖ϖ‖ ^ (1 / p ^ n)` that tend to
`1`. Conversely, (i) and (ii) give a pseudouniformiser `ϖ` with `‖p‖ ≤ ‖ϖ‖ ^ p`, that is
`ϖ ^ p ∣ p` in `K°`, and (iii) is the Frobenius criterion
`TauCeti.Perfectoid.isPerfectoidTateRing_iff_frobenius_surjective_modP`.

## Main definitions

* `TauCeti.Perfectoid.IsPerfectoidField p K`: `K` is a perfectoid field.

## Main results

* `TauCeti.Perfectoid.isPerfectoidField_iff`: the characterisation by (i)–(iii).
* `TauCeti.Perfectoid.isPerfectoidField_iff_isPerfectoidTateRing`: a complete ultrametric
  nontrivially normed field is a perfectoid field exactly when it is a perfectoid Tate ring.
* `TauCeti.Perfectoid.IsPerfectoidField.norm_natCast_lt_one`: `‖p‖ < 1`.
* `TauCeti.Perfectoid.IsPerfectoidField.exists_norm_natCast_le_norm_pow`: some `ϖ` with
  `0 < ‖ϖ‖ < 1` has `‖p‖ ≤ ‖ϖ‖ ^ p`.
* `TauCeti.Perfectoid.IsPerfectoidField.exists_norm_pow_eq`: the value group is `p`-divisible.
* `TauCeti.Perfectoid.IsPerfectoidField.exists_one_lt_norm_lt`: the norms accumulate at `1`.
* `TauCeti.Perfectoid.isPerfectoidField_iff_perfectRing`: in characteristic `p`, a complete
  ultrametric nontrivially normed field is a perfectoid field exactly when it is perfect.

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 3.6 and Proposition 3.8.
* P. Scholze, *Perfectoid spaces*, Definition 3.1 and Lemma 3.2.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Definition 3.1.1 and Lemma 3.1.3.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

/-- A *perfectoid field* is a complete nontrivially normed field `K` with an ultrametric norm which
is a perfectoid Tate ring at `p` (Scholze, *Étale cohomology of diamonds*, Definition 3.6). Its
power-bounded subring `K°` is the closed unit ball. By `isPerfectoidField_iff` this is Scholze's
definition in *Perfectoid spaces*: `K` is not discretely valued, `‖p‖ < 1`, and the `p`-th power
map on `K° ⧸ p` is surjective. -/
class IsPerfectoidField (p : ℕ) (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Prop extends IsPerfectoidTateRing p K

variable {p : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- If every element of `K°` is a `p`-th power modulo `p`, then every `a ∈ K°` with `‖p‖ < ‖a‖`
has the norm of a `p`-th power. -/
private theorem exists_norm_pow_eq_of_natCast_lt_norm
    (hs : ∀ x : powerBoundedSubring K, ∃ y, (p : powerBoundedSubring K) ∣ x - y ^ p)
    {a : K} (hpa : ‖(p : K)‖ < ‖a‖) (ha : ‖a‖ ≤ 1) : ∃ b : K, ‖b‖ ^ p = ‖a‖ := by
  -- write `a = y ^ p + p c` with `y, c ∈ K°`; the error `p c` is smaller than `a`
  obtain ⟨y, hy⟩ := hs ⟨a, mem_powerBoundedSubring.mpr (isPowerBounded_iff_norm_le_one.mpr ha)⟩
  have hlt : ‖a + -(y : K) ^ p‖ < max ‖a‖ ‖-(y : K) ^ p‖ := by
    refine lt_max_of_lt_left (lt_of_le_of_lt ?_ hpa)
    simpa [sub_eq_add_neg] using powerBoundedSubring.dvd_iff_norm_le.mp hy
  refine ⟨y, ?_⟩
  rw [← norm_pow, IsUltrametricDist.norm_eq_of_add_norm_lt_max hlt, norm_neg]

variable [CompleteSpace K]

/-- **A complete ultrametric nontrivially normed field is a perfectoid field exactly when it is a
perfectoid Tate ring.** -/
theorem isPerfectoidField_iff_isPerfectoidTateRing :
    IsPerfectoidField p K ↔ IsPerfectoidTateRing p K :=
  ⟨fun h ↦ h.toIsPerfectoidTateRing, fun h ↦ { toIsPerfectoidTateRing := h }⟩

namespace IsPerfectoidField

variable [IsPerfectoidField p K]

variable (p K) in
/-- **A perfectoid field has an element `ϖ` with `0 < ‖ϖ‖ < 1` and `‖p‖ ≤ ‖ϖ‖ ^ p`**: a
pseudouniformiser `ϖ ∈ K°` with `ϖ ^ p ∣ p` in `K°`. -/
theorem exists_norm_natCast_le_norm_pow :
    ∃ ϖ : K, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ ‖(p : K)‖ ≤ ‖ϖ‖ ^ p := by
  obtain ⟨ϖ, hϖ, h, -, -⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := K)
  obtain ⟨hϖ0, hϖ1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp hϖ
  refine ⟨ϖ, norm_pos_iff.mpr hϖ0, hϖ1, ?_⟩
  simpa using powerBoundedSubring.dvd_iff_norm_le.mp h

variable (p K) in
/-- **In a perfectoid field `‖p‖ < 1`**, that is, `K` has residue characteristic `p`. -/
theorem norm_natCast_lt_one : ‖(p : K)‖ < 1 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  obtain ⟨ϖ, hϖ0, hϖ1, hpϖ⟩ := exists_norm_natCast_le_norm_pow p K
  exact hpϖ.trans_lt (pow_lt_one₀ hϖ0.le hϖ1 hp)

variable [Fact p.Prime]

/-- **The value group of a perfectoid field is `p`-divisible**: every norm `‖x‖` is the `p`-th
power of a norm (Scholze, *Perfectoid spaces*, Lemma 3.2). -/
theorem exists_norm_pow_eq (x : K) : ∃ y : K, ‖y‖ ^ p = ‖x‖ := by
  -- Elements of norm in `(‖p‖, 1]` are `p`-th powers modulo `p`, hence have the norm of a `p`-th
  -- power; multiplying by an integral power of a pseudouniformiser `ϖ` with `‖p‖ < ‖ϖ‖` moves
  -- any nonzero `x` into the annulus `‖ϖ‖ < ‖·‖ ≤ 1`.
  have hp := (Fact.out : p.Prime)
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp [hp.ne_zero]⟩
  obtain ⟨ϖ, hϖ0, hϖ1, hpϖ⟩ := exists_norm_natCast_le_norm_pow p K
  have hroot {a : K} (hpa : ‖(p : K)‖ < ‖a‖) (ha : ‖a‖ ≤ 1) : ∃ b : K, ‖b‖ ^ p = ‖a‖ :=
    exists_norm_pow_eq_of_natCast_lt_norm IsPerfectoidTateRing.exists_natCast_dvd_sub_pow hpa ha
  have hpϖ' : ‖(p : K)‖ < ‖ϖ‖ := hpϖ.trans_lt (pow_lt_self_of_lt_one₀ hϖ0 hϖ1 hp.one_lt)
  obtain ⟨s, hs⟩ := hroot hpϖ' hϖ1.le
  -- choose `n` with `‖ϖ‖ ^ (n + 1) ≤ ‖x‖⁻¹ < ‖ϖ‖ ^ n` and take a root of `x * ϖ ^ (n + 1)`
  obtain ⟨n, hn, hn'⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hx) ((one_lt_inv₀ hϖ0).mpr hϖ1)
  rw [inv_zpow] at hn hn'
  have hc : 0 < ‖ϖ‖ ^ (n + 1) := zpow_pos hϖ0 _
  have hlower : ‖(p : K)‖ < ‖x * ϖ ^ (n + 1)‖ := by
    rw [norm_mul, norm_zpow]
    calc ‖(p : K)‖ < ‖ϖ‖ := hpϖ'
      _ = (‖ϖ‖ ^ n)⁻¹ * ‖ϖ‖ ^ (n + 1) := by
        rw [zpow_add_one₀ hϖ0.ne', inv_mul_cancel_left₀ (zpow_pos hϖ0 n).ne']
      _ < ‖x‖ * ‖ϖ‖ ^ (n + 1) := by gcongr
  have hupper : ‖x * ϖ ^ (n + 1)‖ ≤ 1 := by
    rw [norm_mul, norm_zpow]
    calc ‖x‖ * ‖ϖ‖ ^ (n + 1) ≤ (‖ϖ‖ ^ (n + 1))⁻¹ * ‖ϖ‖ ^ (n + 1) := by gcongr
      _ = 1 := inv_mul_cancel₀ hc.ne'
  obtain ⟨b, hb⟩ := hroot hlower hupper
  refine ⟨b / s ^ (n + 1), ?_⟩
  have hsn : (‖s‖ ^ (n + 1)) ^ p = ‖ϖ‖ ^ (n + 1) := by
    rw [← hs, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [norm_div, div_pow, hb, norm_zpow, hsn, norm_mul, norm_zpow, mul_div_cancel_right₀ _ hc.ne']

variable (p) in
include p in
/-- **A perfectoid field is not discretely valued**: its norms accumulate at `1` from above
(Scholze, *Étale cohomology of diamonds*, Proposition 3.8). -/
theorem exists_one_lt_norm_lt {ε : ℝ} (hε : 1 < ε) : ∃ x : K, 1 < ‖x‖ ∧ ‖x‖ < ε := by
  -- Iterating `exists_norm_pow_eq` gives, for every `n`, an element `y` with
  -- `‖y‖ ^ p ^ n = ‖ϖ‖`, and `‖y⁻¹‖ = ‖ϖ‖ ^ (-1 / p ^ n)` tends to `1`.
  obtain ⟨ϖ, hϖ0, hϖ1, -⟩ := exists_norm_natCast_le_norm_pow p K
  have hroots (n : ℕ) : ∃ y : K, ‖y‖ ^ p ^ n = ‖ϖ‖ := by
    induction n with
    | zero => exact ⟨ϖ, pow_one _⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := exists_norm_pow_eq (p := p) y
      exact ⟨z, by rw [pow_succ', pow_mul, hz, hy]⟩
  have hε0 : 0 < ε := zero_lt_one.trans hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hϖ0 (inv_lt_one_of_one_lt₀ hε)
  obtain ⟨y, hy⟩ := hroots m
  have hy0 : 0 < ‖y‖ := by
    by_contra! h
    rw [norm_le_zero_iff.mp h, norm_zero, zero_pow (pow_ne_zero m (Fact.out : p.Prime).ne_zero)]
      at hy
    exact hϖ0.ne hy
  refine ⟨y⁻¹, ?_, ?_⟩
  · -- `‖y‖ < 1`, since otherwise `‖ϖ‖ = ‖y‖ ^ p ^ m ≥ 1`
    rw [norm_inv, one_lt_inv₀ hy0]
    by_contra! h
    exact hϖ1.not_ge (hy ▸ one_le_pow₀ h)
  · -- `ε⁻¹ < ‖y‖`, since otherwise `‖ϖ‖ = ‖y‖ ^ p ^ m ≤ ε⁻¹ ^ p ^ m ≤ ε⁻¹ ^ m < ‖ϖ‖`
    rw [norm_inv, inv_lt_comm₀ hy0 hε0]
    by_contra! h
    have hle : ε⁻¹ ^ p ^ m ≤ ε⁻¹ ^ m :=
      pow_le_pow_of_le_one (inv_nonneg.mpr hε0.le) (inv_le_one_of_one_le₀ hε.le)
        (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    exact hm.not_ge (hy ▸ (pow_le_pow_left₀ hy0.le h _).trans hle)

end IsPerfectoidField

section Characterisation

variable [Fact p.Prime]

/-- **Characterisation of perfectoid fields** (Scholze, *Étale cohomology of diamonds*,
Proposition 3.8): a complete ultrametric nontrivially normed field `K` is a perfectoid field
exactly when (i) it is not discretely valued, in the sense that its norms accumulate at `1`,
(ii) `‖p‖ < 1`, and (iii) the `p`-th power map on `K° ⧸ p` is surjective. This is Scholze's
definition of a perfectoid field in *Perfectoid spaces*, Definition 3.1. Condition (i) cannot be
dropped: `ℚ_p` satisfies (ii) and (iii). -/
theorem isPerfectoidField_iff :
    IsPerfectoidField p K ↔ (∀ ε : ℝ, 1 < ε → ∃ x : K, 1 < ‖x‖ ∧ ‖x‖ < ε) ∧ ‖(p : K)‖ < 1 ∧
      Function.Surjective fun x : ModP (powerBoundedSubring K) p ↦ x ^ p := by
  rw [surjective_pow_modP_iff]
  refine ⟨fun _ ↦ ⟨fun _ ↦ IsPerfectoidField.exists_one_lt_norm_lt p,
    IsPerfectoidField.norm_natCast_lt_one p K, IsPerfectoidTateRing.exists_natCast_dvd_sub_pow⟩,
    fun ⟨hacc, hp, hs⟩ ↦ ?_⟩
  obtain ⟨ϖ, hϖ0, hϖ1, hpϖ⟩ :=
    NormedField.exists_lt_norm_pow_of_forall_exists_one_lt_norm_lt hacc hp
      (Fact.out : p.Prime).ne_zero
  refine isPerfectoidField_iff_isPerfectoidTateRing.mpr
    (isPerfectoidTateRing_iff_frobenius_surjective_modP.mpr ⟨⟨ϖ, ?_⟩, ?_, ?_, hs⟩)
  · exact mem_powerBoundedSubring.mpr (isPowerBounded_iff_norm_le_one.mpr hϖ1.le)
  · exact isPseudoUniformizer_iff_norm_lt_one.mpr ⟨norm_pos_iff.mp hϖ0, hϖ1⟩
  · exact powerBoundedSubring.dvd_iff_norm_le.mpr (by simpa using hpϖ.le)

/-- **In characteristic `p`, perfectoid fields are the perfect ones**: a complete ultrametric
nontrivially normed field of characteristic `p` is a perfectoid field exactly when it is perfect
(Scholze, *Perfectoid spaces*, §3). -/
theorem isPerfectoidField_iff_perfectRing [CharP K p] :
    IsPerfectoidField p K ↔ PerfectRing K p :=
  isPerfectoidField_iff_isPerfectoidTateRing.trans isPerfectoidTateRing_iff_perfectRing

end Characterisation

end TauCeti.Perfectoid
