/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Connected
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.AlgebraicTopology.Singular.Sphere

/-!
# Counts satisfying the weak Morse inequalities and Euler's equality but not the strong ones

Let `bⱼ = dim Hⱼ(M; V)` for a finite-dimensional module `V` over a division ring, and let `cⱼ` be
the number of critical points of index `j` of a Morse function on `M`. Neither the weak inequalities
`bⱼ ≤ cⱼ dim V` nor Euler's equality `∑ⱼ (-1)ʲ bⱼ = ∑ⱼ (-1)ʲ cⱼ dim V` see the bound `c₀ ≤ c₁ + 1`
on a connected manifold (`TauCeti.IsMorse.criticalCount_zero_le_criticalCount_one_add_one`). On
the sphere `Sⁿ` of odd dimension `n ≥ 3`, whose homology has dimension `dim V` in degrees `0` and
`n` and vanishes otherwise, the counts `c₀ = cₙ = 2` and `cⱼ = 0` for all other `j` satisfy both:
the weak inequalities hold termwise, and both alternating sums vanish because `n` is odd. When
`dim V > 0` they violate the strong inequality in degree one,
`b₁ - b₀ = -dim V > -2 dim V = (c₁ - c₀) dim V`. Taking `V` nonzero, for instance `V = ℚ`, shows
that no Morse function on `Sⁿ` has two local minima, two local maxima and no other critical point,
whatever coefficients the weak inequalities and Euler's equality are checked with
(`TauCeti.finrank_singularHomology_sphere_le_and_sum_eq_and_not_exists_isMorse`). So the strong
inequalities, equivalently the nonnegativity of the coefficients of the polynomial `Q` in the Morse
polynomial identity `∑ⱼ cⱼ tʲ dim V = ∑ⱼ bⱼ tʲ + (1 + t) Q(t)`, are strictly stronger than the weak
inequalities together with Euler's equality. Here `∑ⱼ (cⱼ dim V - bⱼ) tʲ = (1 + tⁿ) dim V` and
`Q = (1 - t + t² - ⋯ + tⁿ⁻¹) dim V`, which has negative coefficients when `dim V > 0`. The parity of
`n` matters: on `S¹` the counts `c₀ = c₁ = 2` are those of a Morse function with two minima and two
maxima, and on even-dimensional spheres such counts already violate Euler's equality when
`dim V > 0`.

## Main results

* `TauCeti.finrank_singularHomology_sphere_le_and_sum_eq_and_not_exists_isMorse`: counts satisfying
  the weak inequalities and Euler's equality for `Sⁿ`, `n ≥ 3` odd, which are not the counts of a
  Morse function.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331--358, Section 1.
-/

public section

noncomputable section

open CategoryTheory Module Set
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The weak Morse inequalities and Euler's equality do not imply the strong ones.** Let `n ≥ 3`
be odd, and let `cⱼ = 2` for `j = 0` and `j = n`, and `cⱼ = 0` otherwise. For every
finite-dimensional module `V` over a division ring, the dimensions `bⱼ` of the homology
`Hⱼ(Sⁿ; V)` satisfy the weak Morse inequalities `bⱼ ≤ cⱼ dim V` and Euler's equality
`∑ⱼ (-1)ʲ bⱼ = (∑ⱼ (-1)ʲ cⱼ) dim V`, but no Morse function on `Sⁿ` has `cⱼ` critical points of index
`j` for every `j`. Indeed, whenever `dim V > 0` the strong inequality in degree one fails, since
`b₁ - b₀ = -dim V` while `(c₁ - c₀) dim V = -2 dim V`; the nonexistence is proved with the nonzero
coefficients `V = ℚ`, so it holds whatever `V` the first two statements are read with. -/
theorem finrank_singularHomology_sphere_le_and_sum_eq_and_not_exists_isMorse (hn : Odd n)
    (h3 : 3 ≤ n) {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] :
    (∀ j, finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj V).obj
        (TopCat.of (Metric.sphere (0 : E) 1))) ≤ (if j = 0 ∨ j = n then 2 else 0) * finrank k V) ∧
      ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j *
          finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj V).obj
            (TopCat.of (Metric.sphere (0 : E) 1))) =
        finrank k V * ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * (if j = 0 ∨ j = n then 2 else 0) ∧
      ¬ ∃ f : Metric.sphere (0 : E) 1 → ℝ, IsMorse (𝓡 n) f ∧
        ∀ j, criticalCount (𝓡 n) f j = if j = 0 ∨ j = n then 2 else 0 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hb (j : ℕ) := ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ V
    (E := E) (Fact.out : finrank ℝ E = n + 1) j
  have hn0 : n ≠ 0 := by omega
  refine ⟨fun j ↦ ?_, ?_, ?_⟩
  · rw [hb]
    by_cases hj0 : j = 0
    · subst hj0
      simp [Ne.symm hn0, two_mul]
    · by_cases hjn : j = n <;> simp [hj0, hjn, hn0, two_mul]
  · -- Both alternating sums vanish: the terms in degrees `0` and `n` cancel since `n` is odd.
    have key (g : ℕ → ℤ) (hg : ∀ j, j ≠ 0 → j ≠ n → g j = 0) :
        ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * g j = g 0 - g n := by
      rw [← Finset.sum_subset (s₁ := {0, n}) (by simp [Finset.insert_subset_iff])
          fun j _ hj ↦ by
            rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
            rw [hg j hj.1 hj.2, mul_zero],
        Finset.sum_pair (Ne.symm hn0), hn.neg_one_pow]
      ring
    rw [key _ fun j hj0 hjn ↦ by rw [hb]; simp [hj0, hjn],
      key _ fun j hj0 hjn ↦ by simp [hj0, hjn]]
    simp [hb, Ne.symm hn0, hn0]
  · rintro ⟨f, hf, hc⟩
    have : ConnectedSpace (Metric.sphere (0 : E) 1) :=
      isConnected_iff_connectedSpace.1 (isConnected_sphere (by
        rw [← finrank_eq_rank]; norm_cast; rw [Fact.out (p := finrank ℝ E = n + 1)]; omega)
        0 zero_le_one)
    have h := hf.criticalCount_one_ne_zero_of_two_le_criticalCount_zero (by rw [hc]; simp)
    rw [hc] at h
    exact h (ite_eq_right_iff.2 fun h1 ↦ absurd h1 (by omega))

end TauCeti
