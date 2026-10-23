/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Perfectoid.Basic

/-!
# Algebraically closed nonarchimedean fields are perfectoid

Let `K` be a complete algebraically closed nontrivially normed field with ultrametric norm, and let
`p ≠ 0` be a natural number with `‖p‖ < 1` in `K`. Then `K` is a perfectoid Tate ring at `p`: its
power-bounded subring is the closed unit ball, a `p`-th root `ϖ` of any `c ≠ 0` with
`‖p‖ ≤ ‖c‖ < 1` (for example `c = p` when `p ≠ 0` in `K`) is a pseudouniformiser with
`ϖ ^ p ∣ p` in `K°`, and every element of `K°` has a `p`-th root. Both characteristics are
covered: when `p = 0` in `K` the condition `‖p‖ < 1` is automatic.

## Main results

* `TauCeti.Perfectoid.isPerfectoidTateRing_of_isAlgClosed`: a complete algebraically closed
  ultrametric nontrivially normed field with `‖p‖ < 1` is a perfectoid Tate ring at `p`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 3.1.
* P. Scholze, *Perfectoid spaces*, Definition 3.1 and Proposition 3.8.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

/-- **A complete algebraically closed nonarchimedean field with `‖p‖ < 1` is perfectoid.** If `K`
is a complete algebraically closed ultrametric nontrivially normed field and `p ≠ 0` is a natural
number with `‖(p : K)‖ < 1`, then `K` is a perfectoid Tate ring at `p`. -/
theorem isPerfectoidTateRing_of_isAlgClosed {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] {p : ℕ} [NeZero p]
    (hpK : ‖(p : K)‖ < 1) : IsPerfectoidTateRing p K := by
  -- an element `c` with `0 < ‖c‖ < 1` and `‖p‖ ≤ ‖c‖`
  obtain ⟨c, hc0, hc1, hpc⟩ : ∃ c : K, c ≠ 0 ∧ ‖c‖ < 1 ∧ ‖(p : K)‖ ≤ ‖c‖ := by
    by_cases h : (p : K) = 0
    · obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
      exact ⟨c, norm_pos_iff.mp hc0, hc1, by simp [h]⟩
    · exact ⟨p, h, hpK, le_rfl⟩
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq c (NeZero.pos p)
  have hϖ1 : ‖ϖ‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg ϖ) (NeZero.ne p), ← norm_pow, hϖ]
    exact hc1
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hϖ, zero_pow (NeZero.ne p)])
  have hmem {x : K} (hx : ‖x‖ ≤ 1) : x ∈ powerBoundedSubring K :=
    mem_powerBoundedSubring.mpr (isPowerBounded_iff_norm_le_one.mpr hx)
  refine .of_forall_exists_pow_eq ⟨ϖ, hmem hϖ1.le⟩
    (isPseudoUniformizer_iff_norm_lt_one.mpr ⟨hϖ0, hϖ1⟩) ⟨⟨p / c, hmem ?_⟩, ?_⟩
    fun x ↦ IsAlgClosed.exists_pow_nat_eq (x : K) (NeZero.pos p)
  · rw [norm_div]
    exact div_le_one_of_le₀ hpc (norm_nonneg c)
  · ext
    simp [hϖ, mul_div_cancel₀ _ hc0]

end TauCeti.Perfectoid
