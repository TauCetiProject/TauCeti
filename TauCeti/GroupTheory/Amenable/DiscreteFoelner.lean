/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Finsupp
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
converse we establish **Reiter's condition** in `ℓ¹(G)`: for every finite `K ⊆ G` and `δ > 0` there
is a finitely supported probability `μ : Convexity.StdSimplex ℝ G` with

```text
∑_{g ∈ K} ‖L_g μ - μ‖₁ = ∑_{g ∈ K} ∑_x |μ.weights (g⁻¹ x) - μ.weights x| < δ.
```

The proof is by Hahn–Banach separation in the sum-norm finite product `PiLp 1 (K → ℓ¹(G))`. The
translation-difference operator `TauCeti.lpTranslateSub K` sends `a ∈ ℓ¹(G)` to
`(L_g a - a)_{g ∈ K}` with exact norm `∑_{g ∈ K} ‖L_g a - a‖₁`. Its image
`TauCeti.lpTranslateSubSet K` of the finite-support probability simplex `Convexity.StdSimplex ℝ G`
is the convex hull of the point-mass images `(δ_{g x} - δ_x)_{g ∈ K}`. If `0` were not in the
closure of this convex set, a continuous linear functional `Λ` on `PiLp 1 (K → ℓ¹(G))` would
strictly separate `0` from it. Representing `Λ` by its coordinate bounded functions
`f_g = Λ.piLpCoordBCF g` (`ContinuousLinearMap.apply_eq_sum_pairingBCF`), the bounded function
`x ↦ ∑_{g ∈ K} (f_g (g x) - f_g x)` would be bounded below by a positive constant `u > 0`, whereas
any left-invariant mean on `TauCeti.UCB G` assigns it the value `0`. Reiter's condition then yields
Følner sets among the superlevel sets of `μ.weights`, by
`TauCeti.hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt`.

## Main definitions

* `TauCeti.lpTranslateSub`: the continuous linear operator `a ↦ (L_g a - a)_{g ∈ K}` from `ℓ¹(G)`
  into the sum-norm product `PiLp 1 (K → ℓ¹(G))`.
* `TauCeti.lpTranslateSubSet`: the image of `Convexity.StdSimplex ℝ G` under
  `TauCeti.lpTranslateSub K`.

## Main results

* `TauCeti.zero_mem_closure_lpTranslateSubSet`: for an amenable discrete group, `0` lies in the
  closure of `TauCeti.lpTranslateSubSet K` for every finite `K ⊆ G`.
* `TauCeti.Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt`: Reiter's condition for
  finitely supported probabilities `Convexity.StdSimplex ℝ G` in `ℓ¹(G)`.
* `TauCeti.Amenable.exists_sum_tsum_abs_sub_lt`: Reiter's condition in raw-function form.
* `TauCeti.amenable_iff_exists_sum_tsum_abs_sub_lt`,
  `TauCeti.amenable_iff_exists_stdSimplex_sum_norm_leftTranslation_sub_lt`,
  `TauCeti.amenable_iff_forall_zero_mem_closure_lpTranslateSubSet`: equivalence of amenability and
  Reiter's condition in its `ℓ¹` and separation forms.
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
open scoped Pointwise symmDiff BoundedContinuousFunction

namespace TauCeti

section TranslateSub

variable {G : Type*} [Group G]

/-- For a finite subset `K` of a group `G`, the continuous linear map
`a ↦ (L_g a - a)_{g ∈ K}` from `ℓ¹(G)` into the sum-norm finite product `PiLp 1 (K → ℓ¹(G))`. -/
def lpTranslateSub (K : Finset G) :
    lp (fun _ : G ↦ ℝ) 1 →L[ℝ] PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1) :=
  LinearMap.mkContinuous
    { toFun := fun a ↦ WithLp.toLp 1 fun g : K ↦ lp.leftTranslation 1 ℝ (g : G) a - a
      map_add' := fun a b ↦ by
        refine PiLp.ext fun g ↦ ?_
        simp only [WithLp.ofLp_add, Pi.add_apply, map_add]
        abel
      map_smul' := fun c a ↦ by
        refine PiLp.ext fun g ↦ ?_
        simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, map_smul, smul_sub] }
    (2 * #K) fun a ↦ by
      rw [PiLp.norm_eq_sum (by norm_num)]
      simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one]
      calc ∑ g : K, ‖lp.leftTranslation 1 ℝ (g : G) a - a‖
          ≤ ∑ _g : K, (2 * ‖a‖) := Finset.sum_le_sum fun g _ ↦ by
            calc ‖lp.leftTranslation 1 ℝ (g : G) a - a‖
                ≤ ‖lp.leftTranslation 1 ℝ (g : G) a‖ + ‖a‖ := norm_sub_le _ _
              _ = 2 * ‖a‖ := by rw [LinearIsometryEquiv.norm_map, two_mul]
        _ = 2 * #K * ‖a‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          ring

/-- The `g`-th coordinate of `lpTranslateSub K a` is `L_g a - a`. -/
@[simp]
theorem lpTranslateSub_apply (K : Finset G) (a : lp (fun _ : G ↦ ℝ) 1) (g : K) :
    lpTranslateSub K a g = lp.leftTranslation 1 ℝ (g : G) a - a :=
  (rfl)

/-- The norm of `lpTranslateSub K a` in the sum-norm product `PiLp 1` is the exact sum
`∑ g ∈ K, ‖L_g a - a‖`. -/
theorem norm_lpTranslateSub (K : Finset G) (a : lp (fun _ : G ↦ ℝ) 1) :
    ‖lpTranslateSub K a‖ = ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g a - a‖ := by
  rw [PiLp.norm_eq_sum (by norm_num)]
  simpa using Finset.sum_coe_sort K (fun g ↦ ‖lp.leftTranslation 1 ℝ g a - a‖)

/-- On a point mass `δ_x`, the `g`-th coordinate of `lpTranslateSub K` is `δ_{g x} - δ_x`. -/
theorem lpTranslateSub_single [DecidableEq G] (K : Finset G) (x : G) (g : K) :
    lpTranslateSub K (lp.single 1 x 1) g =
      lp.single 1 ((g : G) * x) 1 - lp.single 1 x 1 := by
  rw [lpTranslateSub_apply, lp.leftTranslation_single, smul_eq_mul]

/-- The image of the finite-support probability simplex `Convexity.StdSimplex ℝ G` under
`lpTranslateSub K`: the convex set of translation-difference vectors `(L_g μ - μ)_{g ∈ K}` in
`PiLp 1 (K → ℓ¹(G))`. -/
def lpTranslateSubSet (K : Finset G) :
    Set (PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1)) :=
  Set.range fun μ : Convexity.StdSimplex ℝ G ↦ lpTranslateSub K (μ.toLp 1)

theorem mem_lpTranslateSubSet_iff (K : Finset G)
    {v : PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1)} :
    v ∈ lpTranslateSubSet K ↔
      ∃ μ : Convexity.StdSimplex ℝ G, lpTranslateSub K (μ.toLp 1) = v :=
  Iff.rfl

/-- The image of a point mass `δ_x` under `lpTranslateSub K` belongs to `lpTranslateSubSet K`. -/
theorem lpTranslateSub_single_mem_lpTranslateSubSet [DecidableEq G] (K : Finset G) (x : G) :
    lpTranslateSub K (lp.single 1 x 1) ∈ lpTranslateSubSet K :=
  ⟨.single x, by simp⟩

/-- `lpTranslateSubSet K` is convex. -/
theorem convex_lpTranslateSubSet (K : Finset G) : Convex ℝ (lpTranslateSubSet K) := by
  change Convex ℝ (Set.range (⇑(lpTranslateSub K).toLinearMap ∘ Convexity.StdSimplex.toLp 1))
  rw [Set.range_comp]
  exact (Convexity.StdSimplex.convex_range_toLp 1).linear_image (lpTranslateSub K).toLinearMap

/-- `lpTranslateSubSet K` is the convex hull of the point-mass images
`lpTranslateSub K (lp.single 1 x 1)`. -/
theorem lpTranslateSubSet_eq_convexHull [DecidableEq G] (K : Finset G) :
    lpTranslateSubSet K =
      convexHull ℝ (Set.range fun x : G ↦ lpTranslateSub K (lp.single 1 x 1)) := by
  change Set.range (⇑(lpTranslateSub K).toLinearMap ∘ Convexity.StdSimplex.toLp 1) = _
  rw [Set.range_comp, Convexity.StdSimplex.range_toLp_eq_convexHull, LinearMap.image_convexHull,
    ← Set.range_comp]
  rfl

/-- `0` lies in the closure of `lpTranslateSubSet K` if and only if for every `δ > 0` there is a
finitely supported probability `μ : Convexity.StdSimplex ℝ G` with `∑ g ∈ K, ‖L_g μ - μ‖ < δ`. -/
theorem zero_mem_closure_lpTranslateSubSet_iff (K : Finset G) :
    0 ∈ closure (lpTranslateSubSet K) ↔
      ∀ δ : ℝ, 0 < δ → ∃ μ : Convexity.StdSimplex ℝ G,
        ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g (μ.toLp 1) - μ.toLp 1‖ < δ := by
  simp only [Metric.mem_closure_iff, dist_zero_left, mem_lpTranslateSubSet_iff]
  constructor
  · intro h δ hδ
    obtain ⟨v, ⟨μ, rfl⟩, hv⟩ := h δ hδ
    exact ⟨μ, norm_lpTranslateSub K (μ.toLp 1) ▸ hv⟩
  · intro h δ hδ
    obtain ⟨μ, hsum⟩ := h δ hδ
    exact ⟨lpTranslateSub K (μ.toLp 1), ⟨μ, rfl⟩,
      (norm_lpTranslateSub K (μ.toLp 1)).symm ▸ hsum⟩

end TranslateSub

section Amenable

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For an amenable discrete group, `0` lies in the closure of `lpTranslateSubSet K`. Otherwise a
separating functional `Λ` on `PiLp 1 (K → ℓ¹(G))` gives coordinate bounded functions
`f_g = Λ.piLpCoordBCF g` such that `x ↦ ∑_{g ∈ K} (f_g (g x) - f_g x)` is bounded below by a
positive constant, contradicting left invariance of a mean. -/
theorem zero_mem_closure_lpTranslateSubSet [DiscreteTopology G] [Amenable G] (K : Finset G) :
    0 ∈ closure (lpTranslateSubSet K) := by
  classical
  by_contra h
  obtain ⟨Λ, u, hΛ0, hΛ⟩ :=
    geometric_hahn_banach_point_closed (convex_lpTranslateSubSet K).closure isClosed_closure h
  rw [map_zero] at hΛ0
  -- Each coordinate functional `Λ.piLpCoordBCF g` is a bounded function, hence in `UCB G`.
  let F (g : K) : UCB G := (UCB.discreteAlgEquiv G).symm (Λ.piLpCoordBCF g)
  have hval (x : G) :
      Λ (lpTranslateSub K (lp.single 1 x 1)) =
        ((∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g) : UCB G) : G →ᵇ ℝ) x := by
    rw [Λ.apply_eq_sum_pairingBCF]
    simp only [lpTranslateSub_apply, map_sub, sub_apply, lp.pairingBCF_leftTranslation,
      lp.pairingBCF_single, one_mul, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_ofClass, Homeomorph.smul_apply, smul_eq_mul]
    simp [F, -map_inv]
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  have h0 : m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) = 0 := by
    simp only [map_sum, map_sub, hm.apply_leftTranslation, sub_self, sum_const_zero]
  have hu : u ≤ m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) :=
    m.le_apply_of_forall_le fun x ↦ by
      rw [← hval x]
      exact (hΛ _ (subset_closure (lpTranslateSub_single_mem_lpTranslateSubSet K x))).le
  linarith

/-- **Reiter's condition in `ℓ¹(G)`.** In an amenable discrete group, for every finite `K` and
`δ > 0` there is a finitely supported probability `μ : Convexity.StdSimplex ℝ G` with
`∑ g ∈ K, ‖L_g μ - μ‖ < δ`. -/
theorem Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt [DiscreteTopology G]
    [Amenable G] (K : Finset G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ μ : Convexity.StdSimplex ℝ G,
      ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g (μ.toLp 1) - μ.toLp 1‖ < δ :=
  (zero_mem_closure_lpTranslateSubSet_iff K).1 (zero_mem_closure_lpTranslateSubSet K) _ hδ

/-- **Reiter's condition.** In an amenable discrete group, for every finite `K` and `ε > 0` there
is a finitely supported probability density `p` with `∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`. -/
theorem Amenable.exists_sum_tsum_abs_sub_lt [DiscreteTopology G] [Amenable G] (K : Finset G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
      ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε := by
  obtain ⟨μ, hsum⟩ := Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt K hε
  refine ⟨μ.weights, μ.weights_nonneg, μ.weights.hasFiniteSupport, μ.tsum_weights, ?_⟩
  simpa only [Convexity.StdSimplex.norm_leftTranslation_sub_toLp_one, smul_eq_mul] using hsum

/-- A discrete group is amenable exactly when it satisfies **Reiter's condition**: for every
finite `K` and `ε > 0` there is a finitely supported probability density `p` with
`∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`. -/
theorem amenable_iff_exists_sum_tsum_abs_sub_lt [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
        ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε :=
  ⟨fun _ K _ hε ↦ Amenable.exists_sum_tsum_abs_sub_lt K hε,
    fun h ↦ .of_hasFoelnerSets (hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt h)⟩

/-- A discrete group is amenable exactly when it satisfies Reiter's condition in `ℓ¹(G)` for
finitely supported probabilities `μ : Convexity.StdSimplex ℝ G`. -/
theorem amenable_iff_exists_stdSimplex_sum_norm_leftTranslation_sub_lt [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G, ∀ δ : ℝ, 0 < δ →
      ∃ μ : Convexity.StdSimplex ℝ G,
        ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g (μ.toLp 1) - μ.toLp 1‖ < δ := by
  refine ⟨fun _ K _ hδ ↦ Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt K hδ,
    fun h ↦ ?_⟩
  rw [amenable_iff_exists_sum_tsum_abs_sub_lt]
  intro K ε hε
  obtain ⟨μ, hsum⟩ := h K ε hε
  refine ⟨μ.weights, μ.weights_nonneg, μ.weights.hasFiniteSupport, μ.tsum_weights, ?_⟩
  simpa only [Convexity.StdSimplex.norm_leftTranslation_sub_toLp_one, smul_eq_mul] using hsum

/-- A discrete group is amenable exactly when `0` belongs to the closure of `lpTranslateSubSet K`
for every finite `K ⊆ G`. -/
theorem amenable_iff_forall_zero_mem_closure_lpTranslateSubSet [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G, 0 ∈ closure (lpTranslateSubSet K) := by
  simp_rw [zero_mem_closure_lpTranslateSubSet_iff]
  exact amenable_iff_exists_stdSimplex_sum_norm_leftTranslation_sub_lt

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

end Amenable

end TauCeti
