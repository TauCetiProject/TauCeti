/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Inequalities
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.Geometry.Manifold.Topology

/-!
# Morse functions on connected manifolds

Let `f` be a Morse function on a compact connected boundaryless manifold `M` of dimension `m`, with
`cⱼ` critical points of index `j`, and let `bⱼ = dim Hⱼ(M; V)` for a finite-dimensional module `V`
over a division ring. Since `M` is path-connected, `b₀ = dim V`, and the strong Morse inequality in
degree one, `b₁ - b₀ ≤ (c₁ - c₀) dim V`, becomes `c₀ dim V + b₁ ≤ (c₁ + 1) dim V`
(`TauCeti.IsMorse.toNat_criticalCount_zero_mul_add_finrank_singularHomology_one_le`). In
particular `c₀ ≤ c₁ + 1`: a Morse function with `c₀` local minima has at least `c₀ - 1` critical
points of index one (`TauCeti.IsMorse.criticalCount_zero_le_criticalCount_one_add_one`), and so
has one as soon as it has two local minima
(`TauCeti.IsMorse.criticalCount_one_ne_zero_of_two_le_criticalCount_zero`). Applied to `-f`, whose
critical points of index `j` are those of `f` of index `m - j`, this gives `cₘ ≤ cₘ₋₁ + 1` for the
local maxima (`TauCeti.IsMorse.criticalCount_finrank_le_criticalCount_finrank_sub_one_add_one`).

Neither the weak inequalities `bⱼ ≤ cⱼ dim V` nor Euler's equality `∑ⱼ (-1)ʲ bⱼ = ∑ⱼ (-1)ʲ cⱼ dim V`
see this. On the sphere `Sⁿ` of odd dimension `n ≥ 3`, whose homology has dimension `dim V` in
degrees `0` and `n` and vanishes otherwise, the counts `c₀ = cₙ = 2` and `cⱼ = 0` for all other `j`
satisfy both: the weak inequalities hold termwise, and both alternating sums vanish because `n` is
odd. They violate the strong inequality in degree one,
`b₁ - b₀ = -dim V > -2 dim V = (c₁ - c₀) dim V`, so no Morse function on `Sⁿ` has two local
minima, two local maxima and no other critical point
(`TauCeti.finrank_singularHomology_sphere_le_and_sum_eq_and_not_exists_isMorse`). So the strong
inequalities, equivalently the nonnegativity of the coefficients of the polynomial `Q` in the Morse
polynomial identity `∑ⱼ cⱼ tʲ dim V = ∑ⱼ bⱼ tʲ + (1 + t) Q(t)`, are strictly stronger than the weak
inequalities together with Euler's equality. Here `∑ⱼ (cⱼ dim V - bⱼ) tʲ = (1 + tⁿ) dim V` and
`Q = (1 - t + t² - ⋯ + tⁿ⁻¹) dim V` has negative coefficients. The parity of `n` matters: on `S¹`
the counts `c₀ = c₁ = 2` are those of a Morse function with two minima and two maxima, and on
even-dimensional spheres such counts already violate Euler's equality.

## Main results

* `TauCeti.IsMorse.toNat_criticalCount_zero_mul_add_finrank_singularHomology_one_le`: on a compact
  connected manifold, `c₀ dim V + b₁ ≤ (c₁ + 1) dim V`.
* `TauCeti.IsMorse.criticalCount_zero_le_criticalCount_one_add_one` and
  `TauCeti.IsMorse.criticalCount_one_ne_zero_of_two_le_criticalCount_zero`: `c₀ ≤ c₁ + 1`, so two
  local minima force a critical point of index one.
* `TauCeti.IsMorse.criticalCount_finrank_le_criticalCount_finrank_sub_one_add_one`: dually,
  `cₘ ≤ cₘ₋₁ + 1`.
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

section Connected

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  {f : M → ℝ}

/-- **Index-one critical points on a connected manifold.** Let `f` be a Morse function on a compact
connected boundaryless manifold `M`, with `cⱼ` critical points of index `j`. For every
finite-dimensional module `V` over a division ring, `c₀ dim V + dim H₁(M; V) ≤ (c₁ + 1) dim V`.
This is the strong Morse inequality in degree one, since `H₀(M; V) ≅ V`. -/
theorem IsMorse.toNat_criticalCount_zero_mul_add_finrank_singularHomology_one_le
    {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] (hf : IsMorse I f) :
    (criticalCount I f 0).toNat * finrank k V +
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) 1).obj V).obj
          (TopCat.of M)) ≤
      ((criticalCount I f 1).toNat + 1) * finrank k V := by
  have : PathConnectedSpace M := I.pathConnectedSpace M
  have h₀ : finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) 0).obj V).obj
      (TopCat.of M)) = finrank k V :=
    (asIso ((TopCat.of M).singularHomology₀ε V)).toLinearEquiv.finrank_eq
  have h := hf.sum_range_neg_one_pow_mul_finrank_singularHomology_le V 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h₀] at h
  norm_num at h
  linarith

/-- **Local minima and critical points of index one.** A Morse function on a compact connected
boundaryless manifold has at most one more critical point of index `0` than of index `1`. -/
theorem IsMorse.criticalCount_zero_le_criticalCount_one_add_one (hf : IsMorse I f) :
    criticalCount I f 0 ≤ criticalCount I f 1 + 1 := by
  have h := hf.toNat_criticalCount_zero_mul_add_finrank_singularHomology_one_le
    (ModuleCat.of (ULift.{u} ℚ) (ULift.{u} ℚ))
  simp only [Module.finrank_self, mul_one] at h
  rw [← ENat.natCast_toNat (hf.criticalCount_ne_top 0),
    ← ENat.natCast_toNat (hf.criticalCount_ne_top 1)]
  exact_mod_cast (Nat.le_add_right _ _).trans h

/-- A Morse function on a compact connected boundaryless manifold with at least two critical
points of index `0`, that is two local minima, has a critical point of index `1`. -/
theorem IsMorse.criticalCount_one_ne_zero_of_two_le_criticalCount_zero (hf : IsMorse I f)
    (h : 2 ≤ criticalCount I f 0) : criticalCount I f 1 ≠ 0 := by
  intro h₁
  have := (h.trans hf.criticalCount_zero_le_criticalCount_one_add_one).trans_eq (by rw [h₁])
  exact absurd this (by decide)

/-- **The dual bound for the local maxima.** A Morse function on a compact connected boundaryless
manifold of dimension `m` has at most one more critical point of index `m` than of index
`m - 1`. -/
theorem IsMorse.criticalCount_finrank_le_criticalCount_finrank_sub_one_add_one
    (hf : IsMorse I f) :
    criticalCount I f (finrank ℝ E) ≤ criticalCount I f (finrank ℝ E - 1) + 1 := by
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with hE | hE
  · rw [hE]
    exact le_self_add
  have h := hf.neg.criticalCount_zero_le_criticalCount_one_add_one
  rwa [hf.criticalCount_neg (Nat.zero_le _), hf.criticalCount_neg hE, Nat.sub_zero] at h

end Connected

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The weak Morse inequalities and Euler's equality do not imply the strong ones.** Let `n ≥ 3`
be odd, and let `cⱼ = 2` for `j = 0` and `j = n`, and `cⱼ = 0` otherwise. For every
finite-dimensional module `V` over a division ring, the dimensions `bⱼ` of the homology
`Hⱼ(Sⁿ; V)` satisfy the weak Morse inequalities `bⱼ ≤ cⱼ dim V` and Euler's equality
`∑ⱼ (-1)ʲ bⱼ = (∑ⱼ (-1)ʲ cⱼ) dim V`, but no Morse function on `Sⁿ` has `cⱼ` critical points of index
`j` for every `j`: the strong inequality in degree one fails, since `b₁ - b₀ = -dim V` while
`(c₁ - c₀) dim V = -2 dim V`. -/
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

end Sphere

end TauCeti
