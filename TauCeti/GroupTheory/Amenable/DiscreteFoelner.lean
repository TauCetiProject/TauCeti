/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Average
public import TauCeti.GroupTheory.Amenable.Reiter
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Amenable discrete groups have Følner sets

Let `G` be a discrete group. We prove that `G` is amenable, in the sense of a left-invariant mean
on `TauCeti.UCB G` (which for discrete `G` consists of all bounded functions), exactly when it has
Følner sets: for every finite `K ⊆ G` and `ε > 0` there is a finite nonempty `F ⊆ G` with
`|gF △ F| < ε · |F|` for all `g ∈ K`.

The implication from Følner sets to amenability is `TauCeti.Amenable.of_hasFoelnerSets`. For the
converse we first establish **Reiter's condition**: for every finite `K ⊆ G` and `ε > 0` there is
a finitely supported probability density `p : G → ℝ` with

```text
∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε.
```

The proof is by Hahn–Banach separation in the finite product `K → ℓ¹(G)`. The vectors
`(p (g⁻¹ ·) - p)_{g ∈ K}` for finitely supported probabilities `p` form the convex hull of the
vectors `(δ_{g x} - δ_x)_{g ∈ K}`. If `0` were not in the closure of this convex set, a
continuous functional `Λ` would separate them, so that `Λ (δ_{g x} - δ_x)_{g ∈ K} ≥ u > 0` for
every `x`. Writing `f_g y = Λ (ι_g δ_y)`, these functions are bounded by `‖Λ‖`, and the bounded
function `x ↦ ∑_{g ∈ K} (f_g (g x) - f_g x)` is at least `u` everywhere; but a left-invariant mean
assigns it the value `0`. Reiter's condition then yields Følner sets among the superlevel sets of
`p`, by `TauCeti.hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt`.

## Main results

* `TauCeti.Amenable.exists_sum_tsum_abs_sub_lt`: an amenable discrete group satisfies Reiter's
  condition.
* `TauCeti.amenable_iff_exists_sum_tsum_abs_sub_lt`: a discrete group is amenable exactly when it
  satisfies Reiter's condition.
* `TauCeti.Amenable.hasFoelnerSets`: an amenable discrete group has Følner sets.
* `TauCeti.amenable_iff_hasFoelnerSets`: a discrete group is amenable exactly when it has Følner
  sets.
* `TauCeti.amenable_iff_exists_finset`: the same characterization in terms of finite sets.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.3.1 and
  Theorem G.5.1.
* A. Garrido, *An introduction to amenable groups*, Theorem 3.6.
-/

public section

noncomputable section

open Finset Function
open scoped Pointwise symmDiff

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The vector `(δ_{g x} - δ_x)_{g ∈ K}` in the finite product `K → ℓ¹(G)`. -/
private def translateSubSingle [DecidableEq G] (K : Finset G) (x : G) : K → lp (fun _ : G ↦ ℝ) 1 :=
  fun g ↦ lp.single 1 ((g : G) * x) 1 - lp.single 1 x 1

/-- For an amenable discrete group, `0` lies in the closure of the convex hull of the vectors
`(δ_{g x} - δ_x)_{g ∈ K}`. Otherwise a separating functional `Λ` gives bounded functions
`f_g y = Λ (ι_g δ_y)` with `∑_{g ∈ K} (f_g (g x) - f_g x)` bounded below by a positive constant,
contradicting left invariance of a mean. -/
private theorem zero_mem_closure_convexHull_range_translateSubSingle [DiscreteTopology G]
    [Amenable G] [DecidableEq G] (K : Finset G) :
    0 ∈ closure (convexHull ℝ (Set.range (translateSubSingle K))) := by
  classical
  by_contra h
  obtain ⟨Λ, u, hΛ0, hΛ⟩ :=
    geometric_hahn_banach_point_closed (convex_convexHull ℝ _).closure isClosed_closure h
  rw [map_zero] at hΛ0
  set f : K → G → ℝ := fun g y ↦ Λ (Pi.single g (lp.single 1 y 1))
  have hf (g : K) (y : G) : ‖f g y‖ ≤ ‖Λ‖ := by
    simpa [f, Pi.norm_single] using Λ.le_opNorm (Pi.single g (lp.single 1 y 1))
  have hv (x : G) : Λ (translateSubSingle K x) = ∑ g : K, (f g (g * x) - f g x) := by
    conv_lhs => rw [← Finset.univ_sum_single (translateSubSingle K x)]
    simp only [translateSubSingle, map_sum, Pi.single_sub, map_sub, sum_sub_distrib, f]
  -- The functions `f g` are bounded, hence lie in `UCB G` since `G` is discrete.
  let F (g : K) : UCB G :=
    ⟨.ofNormedAddCommGroupDiscrete (f g) ‖Λ‖ (hf g), by simp [ucb_eq_top]⟩
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  have h0 : m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) = 0 := by
    simp only [map_sum, map_sub, hm.apply_leftTranslation, sub_self, sum_const_zero]
  -- `map_inv` would turn `UCB.leftTranslation g⁻¹` into `(UCB.leftTranslation g).symm`.
  have hu : u ≤ m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) :=
    m.le_apply_of_forall_le fun x ↦ by
      simpa [hv, F, -map_inv] using (hΛ _ (subset_closure (subset_convexHull ℝ _ ⟨x, rfl⟩))).le
  linarith

/-- **Reiter's condition.** In an amenable discrete group, for every finite `K` and `ε > 0` there
is a finitely supported probability density `p` with `∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`. -/
theorem Amenable.exists_sum_tsum_abs_sub_lt [DiscreteTopology G] [Amenable G] (K : Finset G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
      ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε := by
  classical
  obtain ⟨c, hc, hcε⟩ := Metric.mem_closure_iff.1
    (zero_mem_closure_convexHull_range_translateSubSingle K) (ε / (#K + 1)) (by positivity)
  rw [dist_zero_left] at hcε
  rw [convexHull_range_eq_exists_affineCombination] at hc
  obtain ⟨s, w, hw0, hw1, rfl⟩ := hc
  rw [affineCombination_eq_linear_combination _ _ _ hw1] at hcε
  -- The convex combination `∑_{x ∈ s} w x • (δ_{g x} - δ_x)_{g ∈ K}` has components
  -- `p (g⁻¹ ·) - p` for the density `p = ∑_{x ∈ s} w x • δ_x`.
  set p : G → ℝ := fun y ↦ if y ∈ s then w y else 0
  have hcomp (g : K) :
      ⇑((∑ x ∈ s, w x • translateSubSingle K x) g) = fun y ↦ p ((g : G)⁻¹ * y) - p y := by
    ext y
    rw [Finset.sum_apply, lp.coeFn_sum, Finset.sum_apply]
    simp only [translateSubSingle, Pi.smul_apply, lp.coeFn_smul, lp.coeFn_sub, lp.coeFn_single,
      Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, sum_sub_distrib, mul_ite, mul_one,
      mul_zero, ← inv_mul_eq_iff_eq_mul, sum_ite_eq, p]
  have hnorm (g : K) : ∑' y, |p ((g : G)⁻¹ * y) - p y| ≤
      ‖∑ x ∈ s, w x • translateSubSingle K x‖ := by
    refine le_of_eq_of_le ?_ (norm_le_pi_norm _ g)
    rw [lp.norm_eq_tsum_rpow (by simp), hcomp]
    simp
  refine ⟨p, fun y ↦ ?_, ?_, ?_, ?_⟩
  · by_cases hy : y ∈ s <;> simp [p, hy, hw0]
  · rw [HasFiniteSupport]
    refine s.finite_toSet.subset fun y hy ↦ ?_
    by_contra hys
    exact hy (ite_eq_right hys)
  · rw [tsum_eq_sum fun y hy ↦ ite_eq_right hy, ← hw1]
    exact sum_congr rfl fun y hy ↦ ite_eq_left hy
  · calc ∑ g ∈ K, ∑' y, |p (g⁻¹ * y) - p y|
        = ∑ g : K, ∑' y, |p ((g : G)⁻¹ * y) - p y| := (sum_coe_sort K _).symm
      _ ≤ ∑ _g : K, ‖∑ x ∈ s, w x • translateSubSingle K x‖ := sum_le_sum fun g _ ↦ hnorm g
      _ = #K * ‖∑ x ∈ s, w x • translateSubSingle K x‖ := by simp
      _ ≤ #K * (ε / (#K + 1)) := by gcongr
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- A discrete group is amenable exactly when it satisfies **Reiter's condition**: for every
finite `K` and `ε > 0` there is a finitely supported probability density `p` with
`∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`. -/
theorem amenable_iff_exists_sum_tsum_abs_sub_lt [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
        ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε :=
  ⟨fun _ K _ hε ↦ Amenable.exists_sum_tsum_abs_sub_lt K hε,
    fun h ↦ .of_hasFoelnerSets (hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt h)⟩

/-- An amenable discrete group has Følner sets. -/
theorem Amenable.hasFoelnerSets [DiscreteTopology G] [Amenable G] : HasFoelnerSets G :=
  hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt fun K _ hε ↦
    Amenable.exists_sum_tsum_abs_sub_lt K hε

/-- A discrete group is amenable exactly when it has Følner sets. -/
theorem amenable_iff_hasFoelnerSets [DiscreteTopology G] : Amenable G ↔ HasFoelnerSets G :=
  ⟨fun _ ↦ Amenable.hasFoelnerSets, .of_hasFoelnerSets⟩

/-- A discrete group is amenable exactly when for every finite `K ⊆ G` and every `ε > 0` there is
a finite nonempty `F ⊆ G` with `|gF △ F| < ε · |F|` for all `g ∈ K`. -/
theorem amenable_iff_exists_finset [DiscreteTopology G] [DecidableEq G] :
    Amenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  rw [amenable_iff_hasFoelnerSets, hasFoelnerSets_iff]

end TauCeti
