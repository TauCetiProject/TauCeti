/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Normed.Group.GlidingHump
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.Normed.Module.WeakDual.SeqCompact

/-!
# The Orlicz–Pettis theorem

A series `∑ xₙ` in a real or complex normed space is *weakly subseries summable* if for every set
`A ⊆ ℕ` of indices there is a vector `y_A` such that, for every continuous linear functional `f`,
the scalar series `∑_{n ∈ A} f (xₙ)` sums to `f (y_A)`. The **Orlicz–Pettis theorem** says that
such a series converges unconditionally in norm, to its weak sum
(`TauCeti.hasSum_of_forall_hasSum_strongDual_indicator`). The space need not be complete.

This is how weak countable additivity is upgraded to norm countable additivity: the values on a
disjoint sequence of sets of a set function that is countably additive against every functional
form a weakly subseries summable series. It applies, for instance, to the set integrals of a
Pettis integrable function.

## Proof

Suppose first that the terms `uₖ` of a weakly subseries summable series do not tend to zero, say
`‖uₖ‖ ≥ ε` along a subsequence, and choose functionals `gₖ` of norm at most one with
`gₖ (uₖ) = ‖uₖ‖`. All weak subseries sums lie in the closed linear span `X₀` of the terms, which
is separable, so by the sequential Banach–Alaoglu theorem the restrictions of the `gₖ` to `X₀`
have a weak-star convergent subsequence. Subtracting a Hahn–Banach extension `W` of the limit gives
functionals `zⱼ` that tend to zero on every weak subseries sum, while `zⱼ (uⱼ)` stays away from
zero after re-indexing. The scalar matrix `zⱼ (uₖ)` then contradicts the gliding hump lemma
`TauCeti.tendsto_diag_zero_of_forall_tendsto_tsum_indicator`. Hence the terms of every weakly
subseries summable series tend to zero in norm.

If a weakly subseries summable series were not unconditionally Cauchy, it would contain disjoint
finite blocks whose sums have norm at least some `ε > 0`. These block sums again form a weakly
subseries summable series, whose terms must tend to zero: a contradiction. Finally, an
unconditionally Cauchy series converges in norm to its weak sum, because the norm of a vector is
the supremum of its pairings with functionals of norm at most one.

## References

* J. Diestel and J. J. Uhl, Jr., *Vector Measures*, Mathematical Surveys 15, American
  Mathematical Society, 1977, Chapter I, §4, Corollary 4.
* J. Diestel, *Sequences and Series in Banach Spaces*, Graduate Texts in Mathematics 92,
  Springer, 1984, Chapter IV (the Orlicz–Pettis theorem) and Chapter VII (the gliding hump).
* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Springer, 2016, §1.2.c.
-/

public section

open Filter Finset Function Set Topology TopologicalSpace

namespace TauCeti

variable {𝕜 X : Type*} [RCLike 𝕜] [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Weak subseries summability passes to subsequences. -/
private theorem exists_hasSum_indicator_comp {u : ℕ → X}
    (hu : ∀ A : Set ℕ, ∃ y : X, ∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (A.indicator u n)) (f y))
    {φ : ℕ → ℕ} (hφ : Injective φ) (A : Set ℕ) :
    ∃ y : X, ∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (A.indicator (u ∘ φ) n)) (f y) := by
  obtain ⟨y, hy⟩ := hu (φ '' A)
  refine ⟨y, fun f ↦ ?_⟩
  have h0 : ∀ n ∉ range φ, f ((φ '' A).indicator u n) = 0 := fun n hn ↦ by
    rw [indicator_of_notMem (fun h ↦ hn (image_subset_range φ A h)), map_zero]
  simpa [Function.comp_def, indicator_image hφ] using (hφ.hasSum_iff h0).2 (hy f)

/-- Weak subseries summability passes to the sums over disjoint finite blocks. -/
private theorem exists_hasSum_indicator_sum {x : ℕ → X}
    (hx : ∀ A : Set ℕ, ∃ y : X, ∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (A.indicator x n)) (f y))
    {B : ℕ → Finset ℕ} (hB : Pairwise (Disjoint on B)) (K : Set ℕ) :
    ∃ y : X, ∀ f : StrongDual 𝕜 X,
      HasSum (fun k ↦ f (K.indicator (fun k ↦ ∑ n ∈ B k, x n) k)) (f y) := by
  set U : Set ℕ := ⋃ k ∈ K, (B k : Set ℕ)
  obtain ⟨y, hy⟩ := hx U
  refine ⟨y, fun f ↦ ?_⟩
  have hunique {k k' n : ℕ} (hk : n ∈ B k) (hk' : n ∈ B k') : k = k' := by
    by_contra hne
    exact Finset.disjoint_left.1 (hB hne) hk hk'
  -- Enumerate the indices in the blocks by the sigma type of the blocks.
  let e : (Σ k, (B k : Set ℕ)) → ℕ := fun p ↦ p.2
  have he : Injective e := by
    rintro ⟨k, n, hn⟩ ⟨k', n', hn'⟩ (rfl : n = n')
    obtain rfl := hunique hn hn'
    rfl
  have h0 : ∀ n ∉ range e, f (U.indicator x n) = 0 := by
    intro n hn
    rw [indicator_of_notMem, map_zero]
    simp only [U, mem_iUnion, Finset.mem_coe, not_exists]
    exact fun k _ hnk ↦ hn ⟨⟨k, n, hnk⟩, rfl⟩
  refine ((he.hasSum_iff h0).2 (hy f)).sigma fun k ↦ ?_
  convert (B k).hasSum (fun n ↦ f (U.indicator x n)) using 1
  · -- Both sides evaluate `n ↦ f (U.indicator x n)` at the elements of the block `B k`.
    rfl
  by_cases hk : k ∈ K
  · rw [indicator_of_mem hk, map_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [indicator_of_mem (mem_biUnion hk (Finset.mem_coe.2 hn))]
  · rw [indicator_of_notMem hk, map_zero, eq_comm]
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    rw [indicator_of_notMem, map_zero]
    simp only [U, mem_iUnion, Finset.mem_coe, not_exists]
    exact fun k' hk' hnk' ↦ hk (hunique hn hnk' ▸ hk')

/-- If functionals `zⱼ` tend to zero on every weak subseries sum of a weakly subseries summable
series `∑ uₖ`, then `zⱼ (uⱼ)` tends to zero. -/
private theorem tendsto_apply_diag_zero {u : ℕ → X}
    (hu : ∀ A : Set ℕ, ∃ y : X, ∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (A.indicator u n)) (f y))
    {z : ℕ → StrongDual 𝕜 X}
    (hz : ∀ (A : Set ℕ) (y : X), (∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (A.indicator u n)) (f y))
      → Tendsto (fun j ↦ z j y) atTop (𝓝 0)) :
    Tendsto (fun j ↦ z j (u j)) atTop (𝓝 0) := by
  refine tendsto_diag_zero_of_forall_tendsto_tsum_indicator (a := fun j k ↦ z j (u k))
    (fun j ↦ ?_) fun A ↦ ?_
  · obtain ⟨y, hy⟩ := hu univ
    exact summable_norm_iff.2 (by simpa using (hy (z j)).summable)
  · obtain ⟨y, hy⟩ := hu A
    refine (hz A y hy).congr fun j ↦ ?_
    rw [← (hy (z j)).tsum_eq]
    exact tsum_congr fun k ↦ by by_cases hk : k ∈ A <;> simp [hk]

/-- The terms of a weakly subseries summable series tend to zero in norm. -/
private theorem tendsto_zero_of_forall_hasSum_indicator {u : ℕ → X}
    (hu : ∀ A : Set ℕ, ∃ y : X, ∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (A.indicator u n)) (f y)) :
    Tendsto u atTop (𝓝 0) := by
  by_contra hne
  obtain ⟨ε, hε, hfreq⟩ : ∃ ε > 0, ∃ᶠ k in atTop, ε ≤ ‖u k‖ := by
    obtain ⟨s, hs, hfs⟩ := not_tendsto_iff_exists_frequently_notMem.1 hne
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
    exact ⟨ε, hε, hfs.mono fun k hk ↦ not_lt.1 fun hlt ↦ hk (hεs (mem_ball_zero_iff.2 hlt))⟩
  obtain ⟨φ₁, hφ₁, hφ₁ε⟩ := extraction_of_frequently_atTop hfreq
  -- Norming functionals `g k` at `u k`, along a subsequence converging pointwise on the closed
  -- linear span of the terms, to a functional `W`.
  choose g hg_norm hg_apply using fun k ↦ exists_dual_vector'' 𝕜 (u k)
  obtain ⟨ψ, hψ, W, -, hW⟩ := exists_strictMono_tendsto_apply_of_isSeparable
    (fun k ↦ hg_norm (φ₁ k)) (countable_range u).isSeparable
  set φ := φ₁ ∘ ψ
  have hφ : StrictMono φ := hφ₁.comp hψ
  -- The functionals `g (φ j) - W` tend to zero on every weak subseries sum of `u ∘ φ`.
  have hdiag : Tendsto (fun j ↦ (g (φ j) - W) (u (φ j))) atTop (𝓝 0) := by
    refine tendsto_apply_diag_zero (u := u ∘ φ) (exists_hasSum_indicator_comp hu hφ.injective)
      fun A y hy ↦ ?_
    have hy₀ := Submodule.topologicalClosure_mono
      (Submodule.span_mono (range_comp_subset_range φ u))
      (mem_topologicalClosure_span_range_of_forall_hasSum_indicator hy)
    simpa [φ] using (hW y hy₀).sub_const (W y)
  have hW0 : Tendsto (fun j ↦ W (u (φ j))) atTop (𝓝 0) := by
    obtain ⟨y, hy⟩ := exists_hasSum_indicator_comp hu hφ.injective univ
    exact (by simpa using (hy W).summable : Summable fun j ↦ W (u (φ j))).tendsto_atTop_zero
  -- Along the subsequence, `‖u (φ j)‖ = (g (φ j) - W) (u (φ j)) + W (u (φ j))` tends to zero.
  have hlim : Tendsto (fun j ↦ ((‖u (φ j)‖ : ℝ) : 𝕜)) atTop (𝓝 0) := by
    simpa [hg_apply] using hdiag.add hW0
  obtain ⟨j, hj⟩ := ((RCLike.continuous_re.tendsto _).comp hlim |>.eventually
    (gt_mem_nhds (by simpa using hε))).exists
  exact (hφ₁ε (ψ j)).not_gt (by simpa [φ] using hj)

/-- A weakly subseries summable series satisfies the unconditional Cauchy criterion. -/
private theorem exists_forall_disjoint_norm_sum_lt {x : ℕ → X}
    (hx : ∀ A : Set ℕ, ∃ y : X, ∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (A.indicator x n)) (f y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℕ, ∀ t : Finset ℕ, Disjoint t s → ‖∑ n ∈ t, x n‖ < ε := by
  -- Otherwise there are disjoint finite blocks whose sums have norm at least `ε`; these block sums
  -- form a weakly subseries summable series whose terms do not tend to zero.
  by_contra! h
  choose T hTs hTε using h
  -- Each finite family of blocks is avoided by a further block `T (⋃ S)`.
  obtain ⟨B, hBε, hdisj⟩ := exists_seq_of_forall_finset_exists'
    (fun B : Finset ℕ ↦ ε ≤ ‖∑ n ∈ B, x n‖) Disjoint fun S _ ↦
      ⟨T (S.biUnion id), hTε _,
        fun B hB ↦ ((Finset.disjoint_biUnion_right _ S id).1 (hTs _) B hB).symm⟩
  have h0 := tendsto_zero_of_forall_hasSum_indicator (exists_hasSum_indicator_sum hx hdisj)
  obtain ⟨k, hk⟩ := (h0.norm.eventually (gt_mem_nhds (by simpa using hε))).exists
  exact (hBε k).not_gt hk

/-- **Orlicz–Pettis theorem.** In a real or complex normed space, a series every subseries of
which is weakly summable converges unconditionally in norm to its weak sum: if for every set
`A ⊆ ℕ` the series `∑_{n ∈ A} xₙ` has a weak sum, and `∑ₙ xₙ` has weak sum `y`, then `∑ₙ xₙ`
converges to `y` in norm. -/
theorem hasSum_of_forall_hasSum_strongDual_indicator {x : ℕ → X}
    (hx : ∀ A : Set ℕ, ∃ y : X, ∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (A.indicator x n)) (f y))
    {y : X} (hy : ∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (x n)) (f y)) : HasSum x y := by
  -- An unconditionally Cauchy series converges in norm to its weak sum.
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨s, hs⟩ := exists_forall_disjoint_norm_sum_lt hx (half_pos hε)
  refine ⟨s, fun F hF ↦ ?_⟩
  rw [dist_eq_norm]
  refine (NormedSpace.norm_le_dual_bound 𝕜 _ (half_pos hε).le fun f ↦ ?_).trans_lt
    (half_lt_self hε)
  have hlim : Tendsto (fun t : Finset ℕ ↦ f (∑ n ∈ F, x n) - ∑ n ∈ t, f (x n)) atTop
      (𝓝 (f (∑ n ∈ F, x n - y))) := by
    rw [map_sub]
    exact tendsto_const_nhds.sub (hy f)
  refine le_of_tendsto hlim.norm (eventually_atTop.2 ⟨F, fun t ht ↦ ?_⟩)
  rw [← map_sum, ← map_sub, ← Finset.sum_sdiff ht, sub_add_cancel_right, map_neg, norm_neg,
    mul_comm]
  exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (hs _ (Finset.disjoint_of_subset_right hF sdiff_disjoint)).le (norm_nonneg f))

/-- **Orlicz–Pettis theorem.** In a real or complex normed space, a series every subseries of
which is weakly summable is unconditionally summable in norm. -/
theorem summable_of_forall_hasSum_strongDual_indicator {x : ℕ → X}
    (hx : ∀ A : Set ℕ, ∃ y : X, ∀ f : StrongDual 𝕜 X, HasSum (fun n ↦ f (A.indicator x n)) (f y)) :
    Summable x := by
  obtain ⟨y, hy⟩ := hx univ
  exact ⟨y, hasSum_of_forall_hasSum_strongDual_indicator hx (by simpa using hy)⟩

end TauCeti
