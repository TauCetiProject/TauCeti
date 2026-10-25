/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Perfectoid.Basic
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots
import TauCeti.RingTheory.Perfection

/-!
# Algebraically closed nonarchimedean fields are perfectoid

Let `K` be a complete algebraically closed nontrivially normed field with ultrametric norm, and let
`p ≠ 0` be a natural number with `‖p‖ < 1` in `K`. Then `K` is a perfectoid Tate ring at `p`: its
power-bounded subring is the closed unit ball, a `p`-th root `ϖ` of any `c ≠ 0` with
`‖p‖ ≤ ‖c‖ < 1` (for example `c = p` when `p ≠ 0` in `K`) is a pseudouniformiser with
`ϖ ^ p ∣ p` in `K°`, and every element of `K°` has a `p`-th root. Choosing compatible `p`-power
roots of `ϖ` gives a pseudouniformiser with compatible roots; completeness is not needed for this.
Both characteristics are covered: when `p = 0` in `K` the condition `‖p‖ < 1` is automatic.

## Main results

* `TauCeti.Perfectoid.nonempty_pseudoUniformizerRoots_of_isAlgClosed`: an algebraically closed
  ultrametric nontrivially normed field with `‖p‖ < 1` has a pseudouniformiser with compatible
  `p`-power roots.
* `TauCeti.Perfectoid.isPerfectoidTateRing_of_isAlgClosed`: a complete algebraically closed
  ultrametric nontrivially normed field with `‖p‖ < 1` is a perfectoid Tate ring at `p`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 3.1.
* P. Scholze, *Perfectoid spaces*, Definition 3.1 and Proposition 3.8.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

/-- **An algebraically closed nonarchimedean field with `‖p‖ < 1` has a pseudouniformiser with
compatible `p`-power roots.** If `K` is an algebraically closed ultrametric nontrivially normed
field and `p ≠ 0` is a natural number with `‖(p : K)‖ < 1`, then `K` has a pseudouniformiser
with compatible `p`-power roots. -/
theorem nonempty_pseudoUniformizerRoots_of_isAlgClosed {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [IsAlgClosed K] {p : ℕ} [NeZero p] (hpK : ‖(p : K)‖ < 1) :
    Nonempty (PseudoUniformizerRoots p K) := by
  -- take `c ≠ 0` with `‖p‖ ≤ ‖c‖ < 1` (`c = p` when `p ≠ 0` in `K`); any compatible system of
  -- `p`-power roots of a `p`-th root `ϖ` of `c` works, as `ϖ ^ p = c` divides `p` in `K°`
  obtain ⟨c, hc0, hc1, hpc⟩ : ∃ c : K, c ≠ 0 ∧ ‖c‖ < 1 ∧ ‖(p : K)‖ ≤ ‖c‖ := by
    by_cases h : (p : K) = 0
    · obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
      exact ⟨c, norm_pos_iff.mp hc0, hc1, by simp [h]⟩
    · exact ⟨p, h, hpK, le_rfl⟩
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq c (NeZero.pos p)
  obtain ⟨roots, hroots⟩ := Perfection.coeffMonoidHom_surjective
    (fun x ↦ IsAlgClosed.exists_pow_nat_eq x (NeZero.pos p)) 0 ϖ
  have hϖ1 : ‖ϖ‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg ϖ) (NeZero.ne p), ← norm_pow, hϖ]
    exact hc1
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hϖ, zero_pow (NeZero.ne p)])
  have hmem {x : K} (hx : ‖x‖ ≤ 1) : x ∈ powerBoundedSubring K :=
    mem_powerBoundedSubring.mpr (isPowerBounded_iff_norm_le_one.mpr hx)
  refine ⟨⟨roots, hroots ▸ isPseudoUniformizer_iff_norm_lt_one.mpr ⟨hϖ0, hϖ1⟩,
    ⟨⟨p / c, hmem ?_⟩, ?_⟩⟩⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ hpc (norm_nonneg c)
  · ext
    simp [hroots, hϖ, mul_div_cancel₀ _ hc0]

/-- **A complete algebraically closed nonarchimedean field with `‖p‖ < 1` is perfectoid.** If `K`
is a complete algebraically closed ultrametric nontrivially normed field and `p ≠ 0` is a natural
number with `‖(p : K)‖ < 1`, then `K` is a perfectoid Tate ring at `p`: a pseudouniformiser `ϖ`
with compatible roots (`nonempty_pseudoUniformizerRoots_of_isAlgClosed`) has `ϖ ^ p ∣ p` in `K°`,
and every element of `K°` has a `p`-th root. -/
theorem isPerfectoidTateRing_of_isAlgClosed {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] {p : ℕ} [NeZero p]
    (hpK : ‖(p : K)‖ < 1) : IsPerfectoidTateRing p K :=
  have ϖ := (nonempty_pseudoUniformizerRoots_of_isAlgClosed hpK).some
  .of_forall_exists_pow_eq (ϖ.rootPB 0) (by simpa using ϖ.isPseudoUniformizer_root 0)
    (ϖ.rootPB_pow_dvd 0) fun x ↦ IsAlgClosed.exists_pow_nat_eq (x : K) (NeZero.pos p)

end TauCeti.Perfectoid
