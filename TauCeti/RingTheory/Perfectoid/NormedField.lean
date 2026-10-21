/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Perfectoid.TateRing
public import Mathlib.NumberTheory.Padics.Complex

/-!
# Perfectoid normed fields

A complete nontrivially normed field `K` with an ultrametric norm is a Tate ring whose
power-bounded elements form the closed unit ball `K°`, and divisibility in `K°` is comparison of
norms. The definition of a perfectoid Tate ring therefore reads: some `ϖ` with `0 < ‖ϖ‖ < 1` has
`‖p‖ ≤ ‖ϖ‖ ^ p`, and every `x` with `‖x‖ ≤ 1` is within `‖ϖ‖ ^ p` of the `p`-th power of some `y`
with `‖y‖ ≤ 1`.

Two consequences delimit the notion.

* `ℚ_[p]` is not perfectoid, although Frobenius on `ℤ_[p] ⧸ p = 𝔽_p` is bijective: every
  pseudouniformiser has norm at most `p⁻¹`, so `‖ϖ‖ ^ p < ‖p‖`, and `ϖ ^ p` does not divide `p` in
  `ℤ_[p]`.
* An algebraically closed field with `‖p‖ < 1` is perfectoid: every element of `K°` is a `p`-th
  power of an element of `K°`, and a `p`-th root of `p` (or any element of norm less than one, when
  `p = 0` in `K`) is a pseudouniformiser `ϖ` with `ϖ ^ p ∣ p`. In particular `ℂ_[p]` is perfectoid.

## Main results

* `TauCeti.Perfectoid.isPerfectoidTateRing_iff_exists_norm`: the definition of a perfectoid Tate
  ring in terms of the norm.
* `TauCeti.Perfectoid.not_isPerfectoidTateRing_padic`: `ℚ_[p]` is not perfectoid.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_isAlgClosed`: an algebraically closed complete
  ultrametric field with `‖p‖ < 1` is perfectoid.
* `TauCeti.Perfectoid.isPerfectoidTateRing_padicComplex`: `ℂ_[p]` is perfectoid.

## References

* P. Scholze, *Étale cohomology of diamonds*, §3, Remark 3.3 and Definition 3.6.
* P. Scholze, *Perfectoid spaces*, Definition 3.1 and the examples following it.
-/

public section

namespace TauCeti.Perfectoid

open Huber

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- **Perfectoid normed fields, in terms of the norm.** A complete ultrametric nontrivially normed
field `K` is a perfectoid Tate ring exactly when some `ϖ ≠ 0` with `‖ϖ‖ < 1` has
`‖p‖ ≤ ‖ϖ‖ ^ p`, and every `x` with `‖x‖ ≤ 1` is within `‖ϖ‖ ^ p` of `y ^ p` for some `y` with
`‖y‖ ≤ 1`. -/
theorem isPerfectoidTateRing_iff_exists_norm :
    IsPerfectoidTateRing p K ↔ ∃ ϖ : K, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ‖(p : K)‖ ≤ ‖ϖ‖ ^ p ∧
      ∀ x : K, ‖x‖ ≤ 1 → ∃ y : K, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖ϖ‖ ^ p := by
  simp only [isPerfectoidTateRing_iff, surjective_frobeniusModPow_iff, dvd_iff_norm_le,
    IsUniform.of_normedDivisionRing, true_and, isPseudoUniformizer_iff_norm_lt_one,
    Subring.coe_pow, Subring.coe_natCast, AddSubgroupClass.coe_sub, norm_pow]
  constructor
  · rintro ⟨ϖ, ⟨hϖ0, hϖ1⟩, hdvd, hs⟩
    refine ⟨ϖ, hϖ0, hϖ1, hdvd, fun x hx ↦ ?_⟩
    obtain ⟨y, hy⟩ := hs ⟨x, mem_powerBoundedSubring_iff_norm_le_one.mpr hx⟩
    exact ⟨y, mem_powerBoundedSubring_iff_norm_le_one.mp y.2, hy⟩
  · rintro ⟨ϖ, hϖ0, hϖ1, hdvd, hs⟩
    refine ⟨⟨ϖ, mem_powerBoundedSubring_iff_norm_le_one.mpr hϖ1.le⟩,
      ⟨hϖ0, hϖ1⟩, hdvd, fun x ↦ ?_⟩
    obtain ⟨y, hy1, hy⟩ := hs x (mem_powerBoundedSubring_iff_norm_le_one.mp x.2)
    exact ⟨⟨y, mem_powerBoundedSubring_iff_norm_le_one.mpr hy1⟩, hy⟩

/-- **`ℚ_[p]` is not a perfectoid Tate ring** (Scholze, *Étale cohomology of diamonds*,
Remark 3.3). A pseudouniformiser `ϖ` has `‖ϖ‖ ≤ p⁻¹`, so `‖ϖ‖ ^ p < p⁻¹ = ‖p‖` and `ϖ ^ p` does
not divide `p` in `ℤ_[p]`, although Frobenius on `ℤ_[p] ⧸ p = 𝔽_p` is bijective. -/
theorem not_isPerfectoidTateRing_padic : ¬ IsPerfectoidTateRing p ℚ_[p] := by
  rw [isPerfectoidTateRing_iff_exists_norm]
  rintro ⟨ϖ, -, hϖ1, hdvd, -⟩
  have hp0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  -- Norms of `p`-adic numbers are integral powers of `p`, so `‖ϖ‖ < 1` gives `‖ϖ‖ ≤ p⁻¹`.
  have hϖ : ‖ϖ‖ ≤ (p : ℝ)⁻¹ := by
    simpa using (Padic.norm_le_pow_iff_norm_lt_pow_add_one ϖ (-1)).mpr (by simpa using hϖ1)
  rw [Padic.norm_p] at hdvd
  refine (pow_lt_self_of_lt_one₀ hp0 hp1 hp.out.one_lt).not_ge (hdvd.trans ?_)
  exact pow_le_pow_left₀ (norm_nonneg ϖ) hϖ p

/-- **Algebraically closed fields are perfectoid.** A complete ultrametric algebraically closed
field with `‖p‖ < 1` is a perfectoid Tate ring: every element of the closed unit ball is the
`p`-th power of an element of the closed unit ball, and a `p`-th root of `p` (or of any element
of norm less than one, if `p = 0` in `K`) is a pseudouniformiser `ϖ` with `ϖ ^ p ∣ p`. -/
theorem IsPerfectoidTateRing.of_isAlgClosed [IsAlgClosed K] (hpK : ‖(p : K)‖ < 1) :
    IsPerfectoidTateRing p K := by
  have hp0 : 0 < p := hp.out.pos
  -- A nonzero `t` with `‖p‖ ≤ ‖t‖ < 1`, whose `p`-th root will be the pseudouniformiser.
  obtain ⟨t, ht0, hpt, ht1⟩ : ∃ t : K, t ≠ 0 ∧ ‖(p : K)‖ ≤ ‖t‖ ∧ ‖t‖ < 1 := by
    by_cases h : (p : K) = 0
    · obtain ⟨t, ht0, ht1⟩ := NormedField.exists_norm_lt_one K
      exact ⟨t, norm_pos_iff.mp ht0, by simp [h], ht1⟩
    · exact ⟨p, h, le_rfl, hpK⟩
  obtain ⟨ϖ, rfl⟩ := IsAlgClosed.exists_pow_nat_eq t hp0
  rw [isPerfectoidTateRing_iff_exists_norm]
  refine ⟨ϖ, fun h ↦ ht0 (by simp [h, hp0.ne']), ?_, by rwa [← norm_pow], fun x hx ↦ ?_⟩
  · rwa [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) hp0.ne'] at ht1
  · obtain ⟨y, rfl⟩ := IsAlgClosed.exists_pow_nat_eq x hp0
    refine ⟨y, ?_, by simp⟩
    rwa [norm_pow, pow_le_one_iff_of_nonneg (norm_nonneg _) hp0.ne'] at hx

/-- **`ℂ_[p]` is a perfectoid Tate ring**: it is algebraically closed and `‖p‖ = p⁻¹ < 1`. -/
instance isPerfectoidTateRing_padicComplex : IsPerfectoidTateRing p ℂ_[p] :=
  IsPerfectoidTateRing.of_isAlgClosed p ℂ_[p] <| by
    simpa using (PadicComplex.norm_extends' p p).trans_lt Padic.norm_p_lt_one

end TauCeti.Perfectoid
