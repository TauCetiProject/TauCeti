/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Convex combinations: sub-convex combinations and the centroid

This file collects facts on two topics about finite convex combinations in a vector space over a
linearly ordered field: sub-convex combinations and the centroid.

A convex set containing `0` also contains every combination `∑ i, w i • z i` of its points with
nonnegative weights of total at most `1`, the missing weight being put on `0`
(`Convex.sum_mem_of_zero_mem`). If the set is moreover symmetric, the coefficients may have any
sign as long as their absolute values sum to at most `1` (`Convex.sum_mem_of_sum_abs_le_one`). In
particular such a set contains the weighted cross-polytope `{x | ∑ i, a i * |b.repr x i| ≤ 1}` as
soon as it contains each `(a i)⁻¹ • b i` for positive weights `a i`
(`Convex.weighted_crosspolytope_subset`). This containment is the step in the lower bound of
Minkowski's second theorem that places a cross-polytope spanned by vectors attaining the
successive minima inside the body; its volume is `OrthonormalBasis.volume_weighted_crosspolytope`.

Over a linearly ordered field there is no topology to speak of relative interiors, but the
centroid of a nonempty finite set `s` still behaves like a relative interior point of the convex
hull of `s`: for every point `p` of the affine span of `s`, the point slightly beyond the centroid
on the ray from `p` remains in the convex hull (`Finset.exists_lineMap_centroid_mem_convexHull`).

This is what makes a point outside a "visible" set lie off the affine span of every simplex in it,
as used for cones of geometric simplicial complexes.

## References

* J.-H. Evertse, *Geometry of Numbers*, §2.3, Lemma 2.10 and the lower-bound proof of
  Theorem 2.9, printed pp.26–27: <https://pub.math.leidenuniv.nl/~evertsejh/dio19-2.pdf>.
-/

public section

open Finset
open scoped Pointwise

variable {𝕜 E ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

namespace Convex

variable {s : Set E}

/-- A convex set containing `0` contains every combination of its points with nonnegative
weights of total at most `1`. -/
theorem sum_mem_of_zero_mem (hs : Convex 𝕜 s) (h₀ : (0 : E) ∈ s) {t : Finset ι} {w : ι → 𝕜}
    {z : ι → E} (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i ≤ 1) (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ s := by
  -- Put the remaining weight `1 - ∑ i ∈ t, w i` on the point `0`.
  have h := hs.sum_mem (t := t.insertNone) (w := fun o ↦ o.elim (1 - ∑ i ∈ t, w i) w)
    (z := fun o ↦ o.elim 0 z) (by simpa [Option.forall] using ⟨hw₁, hw₀⟩) (by simp)
    (by simpa [Option.forall] using ⟨h₀, hz⟩)
  simpa using h

/-- A convex set containing `0` and symmetric about it contains every combination of its points
whose coefficients have absolute values of total at most `1`. -/
theorem sum_mem_of_sum_abs_le_one (hs : Convex 𝕜 s) (h₀ : (0 : E) ∈ s)
    (hneg : ∀ x ∈ s, -x ∈ s) {t : Finset ι} {c : ι → 𝕜} {z : ι → E}
    (hc : ∑ i ∈ t, |c i| ≤ 1) (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, c i • z i ∈ s := by
  classical
  -- Move the sign of each coefficient onto its vector.
  have h (i : ι) : c i • z i = |c i| • if 0 ≤ c i then z i else -z i := by
    split_ifs with hci
    · rw [abs_of_nonneg hci]
    · rw [abs_of_neg (not_le.1 hci), neg_smul, smul_neg, neg_neg]
  simp only [h]
  refine hs.sum_mem_of_zero_mem h₀ (fun i _ ↦ abs_nonneg _) hc fun i hi ↦ ?_
  split_ifs
  exacts [hz i hi, hneg _ (hz i hi)]

/-- **A weighted cross-polytope inside a symmetric convex set.** Let `s` be a convex set
containing `0` and symmetric about it, `b` a basis and `a` positive weights with `b i ∈ a i • s`
for every `i`. Then `s` contains the weighted cross-polytope
`{x | ∑ i, a i * |b.repr x i| ≤ 1}`. -/
theorem weighted_crosspolytope_subset [Fintype ι] (hs : Convex 𝕜 s) (h₀ : (0 : E) ∈ s)
    (hneg : ∀ x ∈ s, -x ∈ s) (b : Module.Basis ι 𝕜 E) {a : ι → 𝕜} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, b i ∈ a i • s) :
    {x : E | ∑ i, a i * |b.repr x i| ≤ 1} ⊆ s := by
  intro x hx
  have hx' : x = ∑ i, (a i * b.repr x i) • (a i)⁻¹ • b i := by
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [smul_smul, mul_right_comm _ _ (a i)⁻¹, (ha i).ne']
  rw [hx']
  refine hs.sum_mem_of_sum_abs_le_one h₀ hneg ?_ fun i _ ↦
    (Set.mem_smul_set_iff_inv_smul_mem₀ (ha i).ne' _ _).1 (hb i)
  simpa [abs_mul, abs_of_pos (ha _)] using hx

end Convex

namespace Finset

/-- For every point `p` in the affine span of a nonempty finite set `s`, some point strictly beyond
the centroid of `s` on the ray from `p` still lies in the convex hull of `s`. -/
theorem exists_lineMap_centroid_mem_convexHull (s : Finset E) (hs : s.Nonempty) {p : E}
    (hp : p ∈ affineSpan 𝕜 (s : Set E)) :
    ∃ ε : 𝕜, 0 < ε ∧ AffineMap.lineMap p (s.centroid 𝕜 id) (1 + ε) ∈ convexHull 𝕜 (s : Set E) := by
  classical
  have hrange : (s : Set E) = Set.range ((↑) : s → E) := by simp
  rw [hrange] at hp
  obtain ⟨w, hw, hpw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  rw [affineCombination_eq_linear_combination _ _ _ hw] at hpw
  set n : 𝕜 := (#s : 𝕜)
  have hn : 0 < n := Nat.cast_pos.2 hs.card_pos
  have hc : s.centroid 𝕜 id = ∑ i : s, n⁻¹ • (i : E) := by
    rw [centroid_def, affineCombination_eq_linear_combination _ _ _
      (sum_centroidWeights_eq_one_of_nonempty 𝕜 _ hs)]
    simp only [centroidWeights_apply, id]
    exact (sum_coe_sort s fun i => n⁻¹ • i).symm
  -- `ε` is small enough that pushing past the centroid keeps every weight nonnegative
  set M : 𝕜 := ∑ i : s, |w i|
  have hM : 0 ≤ M := sum_nonneg fun i _ => abs_nonneg (w i)
  set ε : 𝕜 := (n * (M + 1))⁻¹
  have hε : 0 < ε := inv_pos.2 (mul_pos hn (by linarith))
  set μ : s → 𝕜 := fun i => (1 + ε) * n⁻¹ - ε * w i
  have hμ : ∀ i, 0 ≤ μ i := by
    intro i
    have hwi : ε * w i ≤ n⁻¹ := by
      calc ε * w i ≤ ε * M :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans
              (single_le_sum (f := fun i : s => |w i|) (fun i _ => abs_nonneg _) (mem_univ i)))
              hε.le
        _ ≤ ε * (M + 1) := by nlinarith
        _ = n⁻¹ := by
            simp only [ε, mul_inv]
            field_simp
    have : 0 ≤ ε * n⁻¹ := (mul_pos hε (inv_pos.2 hn)).le
    simp only [μ]
    nlinarith
  have hμsum : ∑ i : s, μ i = 1 := by
    simp only [μ, sum_sub_distrib, ← mul_sum, hw, sum_const, card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    field_simp
    ring
  refine ⟨ε, hε, ?_⟩
  have hq : AffineMap.lineMap p (s.centroid 𝕜 id) (1 + ε) = ∑ i : s, μ i • (i : E) := by
    rw [AffineMap.lineMap_apply_module', hc, hpw]
    simp only [μ, sub_smul, sum_sub_distrib, ← smul_sum, mul_smul]
    module
  rw [hq]
  exact (convex_convexHull 𝕜 _).sum_mem (fun i _ => hμ i) hμsum fun i _ => subset_convexHull 𝕜 _ i.2

end Finset
