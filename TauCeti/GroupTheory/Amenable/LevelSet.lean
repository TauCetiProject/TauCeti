/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import TauCeti.Algebra.BigOperators.Finset.LayerCake.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite layer cakes and translation boundaries

For a nonnegative finitely supported function `p`, put `F_t = {x | t < p x}` for `t ≥ 0`.
There are finitely many nonnegative layer widths `w t` such that

* `∑ p = ∑_t w t * |F_t|`;
* `∑_x |p (g⁻¹ • x) - p x| = ∑_t w t * |g • F_t △ F_t|` for every `g`.

The same weights work for all translations: they depend only on the finite set of values of
`p`, not on the translating element. These finite coarea identities are the counting version
of the layer-cake argument converting almost invariant probabilities into Følner sets.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, proof of Proposition G.5.2.
* A. Garrido, *An introduction to amenable groups*, proof of Theorem 3.6.
-/

public section

open Finset Function
open scoped Pointwise symmDiff

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- **Finite coarea identities.** The mass of a nonnegative finitely supported function and
all its translation distances are weighted sums of superlevel cardinalities and boundaries,
with common nonnegative weights. Each threshold with nonzero weight is zero or a value of `p`. -/
theorem exists_finsupp_layerCake {p : X → ℝ} (hp : 0 ≤ p) (hfin : p.HasFiniteSupport) :
    ∃ w : ℝ →₀ ℝ, 0 ≤ w ∧
      (∀ t ∈ w.support, 0 ≤ t ∧ t ∈ insert 0 (hfin.toFinset.image p)) ∧
      (∑' x, p x) = w.sum (fun t c => c * #(hfin.toFinset.filter (fun x => t < p x))) ∧
      ∀ g : G, (∑' x, |p (g⁻¹ • x) - p x|) =
        w.sum (fun t c => c * #((g • hfin.toFinset.filter (fun x => t < p x)) ∆
          hfin.toFinset.filter (fun x => t < p x))) := by
  classical
  let S := hfin.toFinset
  -- Choose the widths once, from the finite value set; these work for every translation.
  obtain ⟨w, hw, hws, hwe⟩ :=
    (insert 0 (S.image p)).exists_finsupp_sum_ite_lt_eq (by
      intro a ha
      rcases mem_insert.1 ha with rfl | ha
      · exact le_refl _
      · obtain ⟨x, _, rfl⟩ := mem_image.1 ha
        exact hp x)
  have hpS (x : X) (hx : x ∉ S) : p x = 0 :=
    not_not.1 fun h => hx (hfin.mem_toFinset.2 h)
  have hrep (x : X) : w.sum (fun t c => if t < p x then c else 0) = p x := by
    apply hwe
    by_cases hx : x ∈ S
    · exact mem_insert_of_mem (mem_image_of_mem _ hx)
    · simp [hpS x hx]
  have hdist (x y : X) : |p x - p y| = w.sum (fun t c => c *
      |(if t < p x then (1 : ℝ) else 0) - (if t < p y then (1 : ℝ) else 0)|) := by
    rw [← w.abs_sum_ite_lt_sub hw, hrep, hrep]
  refine ⟨w, hw, fun t ht => ⟨(hws t ht).1, by simpa only [insert_idem] using
    (hws t ht).2.1⟩, ?_, ?_⟩
  -- Summing the scalar decomposition counts each superlevel set.
  · calc
      (∑' x, p x) = ∑ x ∈ S, w.sum (fun t c => if t < p x then c else 0) := by
        simp only [hrep, tsum_eq_sum hpS]
      _ = w.sum (fun t c => c * #(S.filter (fun x => t < p x))) := by
        simp only [Finsupp.sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro t _
        simp [sum_ite, mul_comm]
  · intro g
    -- The distance is supported on this finite union, even when X is uncountable.
    let U := S ∪ g • S
    have hpgU (x : X) (hx : x ∉ U) : p (g⁻¹ • x) = 0 := by
      apply hpS
      intro h
      exact hx (mem_union_right _ (by simpa using smul_mem_smul_finset (a := g) h))
    have hpU (x : X) (hx : x ∉ U) : p x = 0 :=
      hpS x (fun h => hx (mem_union_left _ h))
    have hlevel (t : ℝ) (ht : 0 ≤ t) (x : X) :
        x ∈ S.filter (fun x => t < p x) ↔ t < p x := by
      simp only [mem_filter]
      exact ⟨And.right, fun h => ⟨hfin.mem_toFinset.2 (ne_of_gt (ht.trans_lt h)), h⟩⟩
    -- At each threshold the indicator distance counts the symmetric difference.
    have hboundary (t : ℝ) (ht : 0 ≤ t) :
        ∑ x ∈ U, |(if t < p (g⁻¹ • x) then (1 : ℝ) else 0) -
          (if t < p x then (1 : ℝ) else 0)| =
        (#((g • S.filter (fun x => t < p x)) ∆ S.filter (fun x => t < p x)) : ℝ) := by
      let B := (g • S.filter (fun x => t < p x)) ∆ S.filter (fun x => t < p x)
      have hBU : B ⊆ U := symmDiff_subset_union.trans (union_subset
        ((smul_finset_subset_smul_finset (filter_subset _ _)).trans subset_union_right)
        ((filter_subset _ _).trans subset_union_left))
      have hind (x : X) : |(if t < p (g⁻¹ • x) then (1 : ℝ) else 0) -
          (if t < p x then (1 : ℝ) else 0)| = if x ∈ B then 1 else 0 := by
        have hg : x ∈ g • S.filter (fun x => t < p x) ↔ t < p (g⁻¹ • x) := by
          simp only [mem_smul_finset, smul_eq_iff_eq_inv_smul, exists_eq_right, hlevel t ht]
        by_cases h₁ : t < p (g⁻¹ • x) <;> by_cases h₂ : t < p x <;>
          simp [B, mem_symmDiff, hg, hlevel t ht, h₁, h₂]
      simp_rw [hind]
      rw [sum_boole, filter_mem_eq_of_subset hBU]
    calc
      (∑' x, |p (g⁻¹ • x) - p x|) = ∑ x ∈ U, w.sum (fun t c => c *
          |(if t < p (g⁻¹ • x) then (1 : ℝ) else 0) -
            (if t < p x then (1 : ℝ) else 0)|) := by
        rw [tsum_eq_sum (fun x hx => by simp [hpgU x hx, hpU x hx])]
        exact sum_congr rfl fun x _ => hdist _ _
      _ = w.sum (fun t c => c * #((g • S.filter (fun x => t < p x)) ∆
          S.filter (fun x => t < p x))) := by
        simp only [Finsupp.sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro t ht
        rw [← mul_sum, hboundary t (hws t ht).1]

end TauCeti
