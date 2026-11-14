/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.LeftTranslation
public import TauCeti.Analysis.Normed.Lp.PiLp
public import TauCeti.GroupTheory.Amenable.Average
public import TauCeti.GroupTheory.Amenable.Reiter
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Topology.Algebra.Group.UCB.Discrete

/-!
# Amenable discrete groups have Følner sets

Let `G` be a discrete group. We prove that `G` is amenable, in the sense of a left-invariant mean
on `TauCeti.UCB G` (which for discrete `G` consists of all bounded functions), exactly when it has
Følner sets: for every finite `K ⊆ G` and `ε > 0` there is a finite nonempty `F ⊆ G` with
`|gF △ F| < ε · |F|` for all `g ∈ K`.

The implication from Følner sets to amenability is `TauCeti.Amenable.of_hasFoelnerSets`. For the
converse we establish **Reiter's condition** directly on finitely supported probabilities
`p : Convexity.StdSimplex ℝ G` embedded in `ℓ¹(G)` via `Convexity.StdSimplex.toLp`: for every
finite `K ⊆ G` and `δ > 0` there is `p : StdSimplex ℝ G` such that

```text
∑_{g ∈ K} ‖lp.leftTranslation 1 ℝ g (p.toLp 1) - p.toLp 1‖ < δ.
```

The proof is by Hahn–Banach separation in the `ℓ¹` direct sum
`PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1)` equipped with the sum norm. The map
`TauCeti.stdSimplexLeftTranslationSub K` sends a finitely supported probability `p` to the family
`(L_g (p.toLp 1) - p.toLp 1)_{g ∈ K}`, whose norm is directly
`∑_{g ∈ K} ‖L_g (p.toLp 1) - p.toLp 1‖` and whose range is convex (and equal to the convex hull of
the point-mass differences `(δ_{g x} - δ_x)_{g ∈ K}`). If `0` were not in the norm closure of this
convex range, a continuous linear functional `Λ` would strictly separate them, giving `u > 0` with
`Λ (stdSimplexLeftTranslationSub K (.single x)) > u` for every `x : G`. Composing `Λ` with the
coordinate inclusions `PiLp.singleCLM` and identifying `(ℓ¹(G))*` with `G →ᵇ ℝ` via
`lp.bcfDualEquiv` produces bounded functions `f_g : G →ᵇ ℝ` with `f_g y = Λ (ι_g δ_y)` and
`‖f_g‖ ≤ ‖Λ‖` such that `∑_{g ∈ K} (f_g (g * x) - f_g x) ≥ u` uniformly in `x`, contradicting left
invariance of a mean on `UCB G`. Reiter's condition then yields Følner sets among the superlevel
sets of `p`, by `TauCeti.hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt`.

## Main definitions

* `TauCeti.stdSimplexLeftTranslationSub`: the translation-difference map
  `p ↦ (L_g (p.toLp 1) - p.toLp 1)_{g ∈ K}` into `PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1)`.

## Main results

* `TauCeti.Amenable.zero_mem_closure_range_stdSimplexLeftTranslationSub`: for an amenable discrete
  group, `0` lies in the norm closure of `Set.range (stdSimplexLeftTranslationSub K)`.
* `TauCeti.Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt`,
  `TauCeti.amenable_iff_exists_stdSimplex_sum_norm_leftTranslation_sub_lt`: Reiter's `ℓ¹`
  condition in terms of `Convexity.StdSimplex ℝ G`.
* `TauCeti.Amenable.exists_sum_tsum_abs_sub_lt`, `TauCeti.amenable_iff_exists_sum_tsum_abs_sub_lt`:
  Reiter's condition in coordinate form.
* `TauCeti.Amenable.hasFoelnerSets`, `TauCeti.amenable_iff_hasFoelnerSets`,
  `TauCeti.amenable_iff_exists_finset`: equivalence of amenability and Følner sets on discrete
  groups.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.3.1 and
  Theorem G.5.1.
* A. Garrido, *An introduction to amenable groups*, Theorem 3.6.
-/

public section

noncomputable section

open Convexity Finset Function
open scoped BoundedContinuousFunction Pointwise symmDiff

namespace TauCeti

section Group

variable {G : Type*} [Group G]

/-- Auxiliary `ℝ`-linear map sending `u ∈ ℓ¹(G)` to `(L_g u - u)_{g ∈ K}` in the `ℓ¹` direct sum
over `K`. -/
private def leftTranslationSubLinearMap (K : Finset G) :
    lp (fun _ : G ↦ ℝ) 1 →ₗ[ℝ] PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1) :=
  (WithLp.linearEquiv 1 ℝ (∀ _ : K, lp (fun _ : G ↦ ℝ) 1)).symm.toLinearMap.comp
    (LinearMap.pi fun g : K ↦
      (lp.leftTranslation 1 ℝ (g : G)).toLinearEquiv.toLinearMap - LinearMap.id)

/-- For a finite subset `K ⊆ G` and a finitely supported probability `p : StdSimplex ℝ G`, the
family `(L_g (p.toLp 1) - p.toLp 1)_{g ∈ K}` in the finite `ℓ¹` product
`PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1)` equipped with the sum norm. -/
def stdSimplexLeftTranslationSub (K : Finset G) (p : StdSimplex ℝ G) :
    PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1) :=
  leftTranslationSubLinearMap K (p.toLp 1)

@[simp]
theorem stdSimplexLeftTranslationSub_apply (K : Finset G) (p : StdSimplex ℝ G) (g : K) :
    stdSimplexLeftTranslationSub K p g = lp.leftTranslation 1 ℝ (g : G) (p.toLp 1) - p.toLp 1 := by
  rfl

/-- In `PiLp 1`, the norm of `stdSimplexLeftTranslationSub K p` is the sum over `g ∈ K` of the
`ℓ¹` translation errors `‖L_g (p.toLp 1) - p.toLp 1‖`. -/
@[simp]
theorem norm_stdSimplexLeftTranslationSub (K : Finset G) (p : StdSimplex ℝ G) :
    ‖stdSimplexLeftTranslationSub K p‖ =
      ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g (p.toLp 1) - p.toLp 1‖ := by
  rw [PiLp.norm_eq_sum (p := 1) (by simp)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one, stdSimplexLeftTranslationSub_apply,
    Finset.univ_eq_attach]
  exact K.sum_attach fun g ↦ ‖lp.leftTranslation 1 ℝ g (p.toLp 1) - p.toLp 1‖

/-- On a point mass `StdSimplex.single x`, the `g`-th coordinate of
`stdSimplexLeftTranslationSub K (.single x)` is `δ_{g * x} - δ_x`. -/
theorem stdSimplexLeftTranslationSub_single [DecidableEq G] (K : Finset G) (x : G) :
    stdSimplexLeftTranslationSub K (.single x) =
      WithLp.toLp 1 fun g : K ↦ lp.single 1 ((g : G) * x) 1 - lp.single 1 x 1 := by
  ext g y
  simp [smul_eq_mul]

/-- The set of translation-difference vectors `stdSimplexLeftTranslationSub K p` as `p` ranges over
finitely supported probabilities is convex. -/
theorem convex_range_stdSimplexLeftTranslationSub (K : Finset G) :
    Convex ℝ (Set.range (stdSimplexLeftTranslationSub K)) := by
  have h : Set.range (stdSimplexLeftTranslationSub K) =
      leftTranslationSubLinearMap K '' Set.range (fun p : StdSimplex ℝ G ↦ p.toLp 1) := by
    rw [← Set.range_comp]
    rfl
  rw [h]
  exact (StdSimplex.convex_range_toLp 1).linear_image (leftTranslationSubLinearMap K)

/-- The range of `stdSimplexLeftTranslationSub K` is the convex hull of its values on point
masses. -/
theorem range_stdSimplexLeftTranslationSub_eq_convexHull (K : Finset G) :
    Set.range (stdSimplexLeftTranslationSub K) =
      convexHull ℝ (Set.range fun x : G ↦ stdSimplexLeftTranslationSub K (.single x)) := by
  classical
  have h : Set.range (stdSimplexLeftTranslationSub K) =
      leftTranslationSubLinearMap K '' Set.range (fun p : StdSimplex ℝ G ↦ p.toLp 1) := by
    rw [← Set.range_comp]
    rfl
  rw [h, StdSimplex.range_toLp_eq_convexHull, LinearMap.image_convexHull, ← Set.range_comp]
  congr 1
  ext x
  simp [stdSimplexLeftTranslationSub]

end Group

section TopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For an amenable discrete group, `0` lies in the norm closure of the convex set
`Set.range (stdSimplexLeftTranslationSub K)` in `PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1)`.
Otherwise a separating functional `Λ` induces bounded functions `f_g y = Λ (ι_g δ_y)` via
`lp.bcfDualEquiv` with `∑_{g ∈ K} (f_g (g * x) - f_g x) ≥ u > 0` uniformly in `x`, contradicting
left invariance of a mean on `UCB G`. -/
theorem Amenable.zero_mem_closure_range_stdSimplexLeftTranslationSub [DiscreteTopology G]
    [Amenable G] (K : Finset G) :
    0 ∈ closure (Set.range (stdSimplexLeftTranslationSub K)) := by
  classical
  by_contra h
  obtain ⟨Λ, u, hΛ0, hΛ⟩ := geometric_hahn_banach_point_closed
    (convex_range_stdSimplexLeftTranslationSub K).closure isClosed_closure h
  rw [map_zero] at hΛ0
  -- Pull `Λ` back along each coordinate inclusion `ι_g` and identify `(ℓ¹(G))* ≃ₗᵢ (G →ᵇ ℝ)`.
  let f (g : K) : G →ᵇ ℝ :=
    (lp.bcfDualEquiv ℝ G).symm
      (Λ.comp (PiLp.singleCLM 1 ℝ (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1) g))
  have hv (x : G) :
      Λ (stdSimplexLeftTranslationSub K (.single x)) = ∑ g : K, (f g ((g : G) * x) - f g x) := by
    conv_lhs => rw [← PiLp.univ_sum_single (stdSimplexLeftTranslationSub K (.single x))]
    simp [stdSimplexLeftTranslationSub_single, map_sum, PiLp.single_sub, sum_sub_distrib, f]
  let F (g : K) : UCB G := ⟨f g, by simp [ucb_eq_top]⟩
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  have h0 : m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) = 0 := by
    simp only [map_sum, map_sub, hm.apply_leftTranslation, sub_self, sum_const_zero]
  -- `map_inv` would turn `UCB.leftTranslation g⁻¹` into `(UCB.leftTranslation g).symm`.
  have hu : u ≤ m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) :=
    m.le_apply_of_forall_le fun x ↦ by
      simpa [hv, F, -map_inv] using (hΛ _ (subset_closure ⟨.single x, rfl⟩)).le
  linarith

/-- **Reiter's condition in `ℓ¹(G)`.** In an amenable discrete group, for every finite `K ⊆ G` and
`δ > 0` there is a finitely supported probability `p : StdSimplex ℝ G` with
`∑_{g ∈ K} ‖L_g (p.toLp 1) - p.toLp 1‖ < δ`. -/
theorem Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt [DiscreteTopology G]
    [Amenable G] (K : Finset G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : StdSimplex ℝ G,
      ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g (p.toLp 1) - p.toLp 1‖ < δ := by
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := Metric.mem_closure_iff.1
    (Amenable.zero_mem_closure_range_stdSimplexLeftTranslationSub K) δ hδ
  exact ⟨p, by simpa [dist_zero_left] using hp⟩

/-- **Reiter's condition.** In an amenable discrete group, for every finite `K` and `ε > 0` there
is a finitely supported probability density `p` with `∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`. -/
theorem Amenable.exists_sum_tsum_abs_sub_lt [DiscreteTopology G] [Amenable G] (K : Finset G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
      ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε := by
  obtain ⟨p, hp⟩ := Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt K hε
  refine ⟨⇑p.weights, p.nonneg, p.weights.hasFiniteSupport, by simp, ?_⟩
  simpa [lp.norm_leftTranslation_sub_one, smul_eq_mul] using hp

/-- A discrete group is amenable exactly when for every finite `K ⊆ G` and `δ > 0` there is a
finitely supported probability `p : StdSimplex ℝ G` with
`∑_{g ∈ K} ‖L_g (p.toLp 1) - p.toLp 1‖ < δ`. -/
theorem amenable_iff_exists_stdSimplex_sum_norm_leftTranslation_sub_lt [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G, ∀ δ : ℝ, 0 < δ →
      ∃ p : StdSimplex ℝ G,
        ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g (p.toLp 1) - p.toLp 1‖ < δ := by
  refine ⟨fun _ K _ hδ ↦ Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt K hδ,
    fun h ↦ .of_hasFoelnerSets
      (hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt fun K ε hε ↦ ?_)⟩
  obtain ⟨p, hp⟩ := h K ε hε
  refine ⟨⇑p.weights, p.nonneg, p.weights.hasFiniteSupport, by simp, ?_⟩
  simpa [lp.norm_leftTranslation_sub_one, smul_eq_mul] using hp

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

end TopologicalGroup

end TauCeti
