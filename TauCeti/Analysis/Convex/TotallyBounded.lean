/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.TotallyBounded
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import TauCeti.Analysis.Normed.Group.NullSequence

/-!
# Totally bounded sets lie in the closed convex hull of a null sequence

Grothendieck's compactness lemma: a subset `s` of a real seminormed space is totally bounded if
and only if there is a sequence `x : ℕ → E` tending to `0` whose range has `s` inside the closure
of its convex hull. In particular every relatively norm-compact set, being totally bounded, lies
in the closed convex hull of a null sequence. This is the reduction from compact sets to null
sequences used in Grothendieck's characterization of the approximation property by compact
operators.

Neither direction needs completeness. Over complex scalars, apply these results to the
underlying real space: convexity is real convexity.

## Main statements

* `TotallyBounded.exists_tendsto_zero_subset_closure_convexHull`: a totally bounded set lies in
  the closed convex hull of the range of a sequence tending to `0`.
* `TauCeti.totallyBounded_iff_exists_tendsto_zero_subset_closure_convexHull`: the converse also
  holds, so this characterizes totally bounded sets.

## References

* A. Grothendieck, *Produits tensoriels topologiques et espaces nucléaires*, Mem. Amer. Math.
  Soc. **16** (1955).
* R. E. Megginson, *An Introduction to Banach Space Theory*, §3.4 (the lemma preceding
  Grothendieck's approximation property theorem 3.4.32).
* J. Lindenstrauss and L. Tzafriri, *Classical Banach Spaces I*, §1.e.
-/

public section

open Filter Metric Set Topology
open scoped Pointwise

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

/-- A convex set containing `0` contains `c n` for every `n` once it contains `2 • c 0` and the
rescaled increments `2 ^ (k + 2) • (c (k + 1) - c k)`: `c n` is the sub-convex combination of
these with weights `(1 / 2) ^ (k + 1)`, the missing weight `(1 / 2) ^ (n + 1)` lying on `0`. -/
private lemma Convex.mem_of_two_pow_smul_sub_mem {C : Set E} (hC : Convex ℝ C) (hC0 : 0 ∈ C)
    {c : ℕ → E} (h0 : (2 : ℝ) • c 0 ∈ C) (hsucc : ∀ k, (2 : ℝ) ^ (k + 2) • (c (k + 1) - c k) ∈ C)
    (n : ℕ) : c n ∈ C := by
  have hweight (n : ℕ) : 1 - (1 / 2 : ℝ) ^ (n + 1) ∈ Icc 0 1 := by
    have := pow_le_one₀ (n := n + 1) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
    constructor <;> linarith
  -- Induction on `c n ∈ (1 - (1/2)^(n+1)) • C`, adding the weight `(1/2)^(n+2)` at each step.
  have hscaled (n : ℕ) : c n ∈ (1 - (1 / 2 : ℝ) ^ (n + 1)) • C := by
    induction n with
    | zero =>
      refine ⟨(2 : ℝ) • c 0, h0, ?_⟩
      simp only [smul_smul]
      norm_num
    | succ n ih =>
      have hsum : c n + (1 / 2 : ℝ) ^ (n + 2) • (2 : ℝ) ^ (n + 2) • (c (n + 1) - c n) ∈
          (1 - (1 / 2 : ℝ) ^ (n + 1) + (1 / 2) ^ (n + 2)) • C := by
        rw [hC.add_smul (hweight n).1 (by positivity)]
        exact add_mem_add ih (smul_mem_smul_set (hsucc n))
      have hc :
          c n + (1 / 2 : ℝ) ^ (n + 2) • (2 : ℝ) ^ (n + 2) • (c (n + 1) - c n) = c (n + 1) := by
        simp only [smul_smul, ← mul_pow]
        norm_num
      have hw : 1 - (1 / 2 : ℝ) ^ (n + 1) + (1 / 2) ^ (n + 2) = 1 - (1 / 2) ^ (n + 1 + 1) := by
        ring
      rwa [hc, hw] at hsum
  obtain ⟨z, hz, hzc⟩ := hscaled n
  rw [← hzc]
  exact hC.smul_mem_of_zero_mem hC0 hz (hweight n)

/-- If `y` is within `(1 / 4) ^ (k + 1)` of `a` and within `(1 / 4) ^ k` of `b`, then the rescaled
increment `2 ^ (k + 2) • (a - b)` has norm at most `8 * (1 / 2) ^ k`. -/
private lemma norm_two_pow_smul_sub_le {a b y : E} {k : ℕ} (ha : dist y a < (1 / 4 : ℝ) ^ (k + 1))
    (hb : dist y b < (1 / 4 : ℝ) ^ k) : ‖(2 : ℝ) ^ (k + 2) • (a - b)‖ ≤ 8 * (1 / 2 : ℝ) ^ k := by
  have h4 : (1 / 4 : ℝ) ^ (k + 1) ≤ (1 / 4) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) k.le_succ
  have hab : ‖a - b‖ ≤ 2 * (1 / 4 : ℝ) ^ k := by
    rw [← dist_eq_norm]
    linarith [dist_triangle_left a b y]
  have hpow : (2 : ℝ) ^ (k + 2) * (2 * (1 / 4 : ℝ) ^ k) = 8 * (1 / 2 : ℝ) ^ k := by
    have h4 : (1 / 4 : ℝ) ^ k = (1 / 2) ^ k * (1 / 2) ^ k := by rw [← mul_pow]; norm_num
    have h1 : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [h4, pow_add]
    linear_combination (8 * (1 / 2 : ℝ) ^ k) * h1
  rw [norm_smul, Real.norm_of_nonneg (by positivity), ← hpow]
  gcongr

/-- **Grothendieck's compactness lemma.** A totally bounded subset of a real seminormed space lies
in the closed convex hull of the range of a sequence tending to `0`. -/
theorem TotallyBounded.exists_tendsto_zero_subset_closure_convexHull (hs : TotallyBounded s) :
    ∃ x : ℕ → E, Tendsto x atTop (𝓝 0) ∧ s ⊆ _root_.closure (convexHull ℝ (range x)) := by
  -- Approximate each `y ∈ s` by points `c k y` of a finite `(1/4)^k`-net `N k` of `s`.
  choose N _ hNfin hNcover using fun k : ℕ ↦
    finite_approx_of_totallyBounded hs ((1 / 4 : ℝ) ^ k) (by positivity)
  have hc (k : ℕ) (y : E) : ∃ a, y ∈ s → a ∈ N k ∧ dist y a < (1 / 4 : ℝ) ^ k := by
    by_cases hy : y ∈ s
    · obtain ⟨a, ha, hya⟩ := mem_iUnion₂.1 (hNcover k hy)
      exact ⟨a, fun _ ↦ ⟨ha, hya⟩⟩
    · exact ⟨0, fun h ↦ absurd h hy⟩
  choose c hcN hcdist using hc
  -- The rescaled first approximations and increments range over finite sets, the `k`-th
  -- increments having norm at most `8 * (1/2)^k`; list them all in one null sequence `x`.
  obtain ⟨x, hx, hsub⟩ := TauCeti.exists_tendsto_zero_union_iUnion_subset_range
    (A := (fun y ↦ (2 : ℝ) • c 0 y) '' s)
    (B := fun k ↦ (fun y ↦ (2 : ℝ) ^ (k + 2) • (c (k + 1) y - c k y)) '' s)
    (((hNfin 0).image fun a ↦ (2 : ℝ) • a).subset <| by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_image_of_mem _ (hcN 0 y hy))
    (fun k ↦ ((hNfin (k + 1)).image2 (fun a b ↦ (2 : ℝ) ^ (k + 2) • (a - b)) (hNfin k)).subset <| by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_image2_of_mem (hcN (k + 1) y hy) (hcN k y hy))
    (by
      rintro k _ ⟨y, hy, rfl⟩
      exact norm_two_pow_smul_sub_le (hcdist (k + 1) y hy) (hcdist k y hy))
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 8)
  -- The closed convex hull contains `0 = lim x` and each `c n y`, hence each `y = lim c n y`.
  set C := _root_.closure (convexHull ℝ (range x))
  have hC : Convex ℝ C := (convex_convexHull ℝ _).closure
  have hC0 : (0 : E) ∈ C := mem_closure_of_tendsto hx <| Eventually.of_forall fun n ↦
    subset_convexHull ℝ _ (mem_range_self n)
  have hmem {z : E} (hz : z ∈ range x) : z ∈ C := subset_closure (subset_convexHull ℝ _ hz)
  refine ⟨x, hx, fun y hy ↦ isClosed_closure.mem_of_tendsto (f := fun n ↦ c n y) (b := atTop) ?_ ?_⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (dist_comm _ _).trans_le
      (hcdist n y hy).le) (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  · exact Eventually.of_forall <| hC.mem_of_two_pow_smul_sub_mem hC0
      (hmem (hsub (Or.inl ⟨y, hy, rfl⟩)))
      fun k ↦ hmem (hsub (Or.inr (mem_iUnion.2 ⟨k, y, hy, rfl⟩)))

namespace TauCeti

/-- A subset of a real seminormed space is totally bounded if and only if it lies in the closed
convex hull of the range of a sequence tending to `0`. -/
theorem totallyBounded_iff_exists_tendsto_zero_subset_closure_convexHull :
    TotallyBounded s ↔
      ∃ x : ℕ → E, Tendsto x atTop (𝓝 0) ∧ s ⊆ closure (convexHull ℝ (range x)) := by
  refine ⟨TotallyBounded.exists_tendsto_zero_subset_closure_convexHull, ?_⟩
  rintro ⟨x, hx, hsx⟩
  exact ((hx.isCompact_insert_range.totallyBounded.subset (subset_insert _ _)).convexHull.closure
    ).subset hsx

end TauCeti
