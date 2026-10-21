/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Perfectoid.Basic

/-!
# `ℂ_p` is perfectoid and `ℚ_p` is not

The `p`-adic complex numbers `ℂ_p` form a perfectoid Tate ring: `ϖ = p ^ (1 / p)` is a
pseudouniformiser with `ϖ ^ p = p`, and every element has a `p`-th root because `ℂ_p` is
algebraically closed. The `p`-adic numbers `ℚ_p` do not, even though Frobenius on
`ℤ_p ⧸ p = 𝔽_p` is bijective: no pseudouniformiser `ϖ` of `ℚ_p` has `ϖ ^ p ∣ p` in `ℤ_p`.

## Main results

* `TauCeti.Perfectoid.isPerfectoidTateRing_padicComplex`: `ℂ_p` is a perfectoid Tate ring.
* `TauCeti.Perfectoid.not_isPerfectoidTateRing_padic`: `ℚ_p` is not.

## References

* P. Scholze, *Étale cohomology of diamonds*, Remark 3.3.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

variable (p : ℕ) [Fact p.Prime]

/-- **`ℂ_p` is a perfectoid Tate ring**: `ϖ = p ^ (1 / p)` is a pseudouniformiser with
`ϖ ^ p = p`, and every element of `ℂ_p` has a `p`-th root. -/
instance isPerfectoidTateRing_padicComplex : IsPerfectoidTateRing p ℂ_[p] := by
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) (Nat.pos_of_ne_zero (NeZero.ne p))
  have hnorm : ‖ϖ‖ ^ p < 1 := by
    rw [← norm_pow, hϖ, ← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap',
      Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt)
  have hlt : ‖ϖ‖ < 1 := (pow_lt_one_iff_of_nonneg (norm_nonneg ϖ) (NeZero.ne p)).mp hnorm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne p)] at hϖ
    exact Nat.cast_ne_zero.mpr (NeZero.ne p) hϖ.symm
  refine .of_forall_exists_pow_eq
    ⟨ϖ, mem_powerBoundedSubring.mpr (isPowerBounded_iff_norm_le_one.mpr hlt.le)⟩
    (isPseudoUniformizer_iff_norm_lt_one.mpr ⟨hϖ0, hlt⟩) ⟨1, Subtype.ext (by simp [hϖ])⟩
    fun x ↦ IsAlgClosed.exists_pow_nat_eq (x : ℂ_[p]) (Nat.pos_of_ne_zero (NeZero.ne p))

/-- **`ℚ_p` is not a perfectoid Tate ring**, although Frobenius on `ℤ_p ⧸ p = 𝔽_p` is bijective:
a pseudouniformiser `ϖ` of `ℚ_p` has `‖ϖ‖ ≤ p⁻¹`, so `‖ϖ ^ p‖ < ‖p‖` and `ϖ ^ p ∤ p` in `ℤ_p`
(Scholze, *Étale cohomology of diamonds*, Remark 3.3). -/
theorem not_isPerfectoidTateRing_padic : ¬ IsPerfectoidTateRing p ℚ_[p] := by
  rintro ⟨-, ϖ, hϖ, ⟨c, hc⟩, -⟩
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have hϖ1 : ‖(ϖ : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one (ϖ : ℚ_[p]) (-1)).mpr
      (by simpa using (isPseudoUniformizer_iff_norm_lt_one.mp hϖ).2)
    simpa using this
  have hc1 : ‖(c : ℚ_[p])‖ ≤ 1 := isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp c.2)
  have hceq : (p : ℚ_[p]) = (ϖ : ℚ_[p]) ^ p * c := by
    simpa using congrArg Subtype.val hc
  have : (p : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ ^ p := by
    calc (p : ℝ)⁻¹ = ‖(p : ℚ_[p])‖ := Padic.norm_p.symm
      _ = ‖(ϖ : ℚ_[p])‖ ^ p * ‖(c : ℚ_[p])‖ := by rw [hceq, norm_mul, norm_pow]
      _ ≤ (p : ℝ)⁻¹ ^ p * 1 := by gcongr
      _ = (p : ℝ)⁻¹ ^ p := mul_one _
  have hp2 : 1 < p := (Fact.out : p.Prime).one_lt
  exact absurd this (not_le.mpr (pow_lt_self_of_lt_one₀ (by positivity)
    (inv_lt_one_of_one_lt₀ hp) hp2))

end TauCeti.Perfectoid
