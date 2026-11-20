/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.Analysis.Convex.Measure
public import TauCeti.Analysis.Convex.SubgradientImage
public import TauCeti.Topology.ClusterSet
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Subdifferentials as convex hulls of gradient cluster sets

Let `E` be a finite-dimensional real inner product space and let `f : E → EReal` be convex
(convex real epigraph, never `⊥`), with `D` the interior of its effective domain `{x | f x ≠ ⊤}`
and real representative `F x = (f x).toReal`. At every `x ∈ D`, the subdifferential of `f` for the
inner product is recovered from the nearby gradients of `F`: for any set `S` whose closure is a
neighbourhood of `x` and along which `F` is differentiable near `x`,

  `∂f(x) = convexHull ℝ (clusterSetOn (∇ F) S x)`

(`TauCeti.subdifferential_eq_convexHull_clusterSetOn`; Rockafellar, *Convex Analysis*, Theorem
25.6). Taking `S` to be the set of all differentiability points of `F`, which is dense in `D` by
Rademacher's theorem, removes `S` from the hypotheses
(`TauCeti.subdifferential_eq_convexHull_clusterSetOn_differentiableAt`).

The forward inclusion `convexHull ℝ (clusterSetOn (∇ F) S x) ⊆ ∂f(x)` comes from convexity of
`∂f(x)` and closedness of the subdifferential graph over a closed ball around `x` in `D`, since
`∇ F z ∈ ∂f(z)` at points of differentiability. For the reverse inclusion, local boundedness of
subgradients makes the cluster set `C = clusterSetOn (∇ F) S x` compact, so `convexHull ℝ C` is
compact by Carathéodory's theorem (`IsCompact.convexHull`) and hence closed, while `∇ F` tends to
`𝓝ˢ C` along `𝓝[S] x`. A subgradient `y₀ ∈ ∂f(x)` outside `convexHull ℝ C` is strictly separated
from it by some inner-product functional `⟪v, ·⟫`, so `⟪v, ∇ F z⟫ < α < ⟪v, y₀⟫` for `z ∈ S` near
`x`; stepping from `x` in the direction `v` and perturbing into the locally dense set `S` violates
monotonicity `⟪z - x, y₀ - ∇ F z⟫ ≤ 0` of `∂f`.

As a measure-theoretic consequence, if `U` is open, `f` is finite almost everywhere on `U` for an
additive Haar measure `ρ`, and `∇ F z ∈ Y` for `ρ`-almost every `z ∈ U`, then `U ⊆ D` and every
subgradient of `f` on `U` lies in `closedConvexHull ℝ Y`
(`TauCeti.subgradientImage_subset_closedConvexHull_of_ae_mem`), hence in `closure Y` when `Y` is
convex (`TauCeti.subgradientImage_subset_closure_of_convex_of_ae_mem`).

## Main statements

* `TauCeti.tendsto_gradient_toReal_nhdsSet_clusterSetOn` — along `𝓝[S] x`, the gradient tends to
  the neighbourhood filter of its cluster set;
* `TauCeti.isCompact_clusterSetOn_gradient_toReal` and
  `TauCeti.clusterSetOn_gradient_toReal_nonempty` — the gradient cluster set at `x ∈ D` is compact,
  and nonempty when `x ∈ closure S`;
* `TauCeti.clusterSetOn_gradient_toReal_subset_subdifferential` — every gradient cluster value at
  `x ∈ D` is a subgradient of `f` at `x`;
* `TauCeti.subdifferential_eq_convexHull_clusterSetOn` and
  `TauCeti.subdifferential_eq_convexHull_clusterSetOn_differentiableAt` — **Rockafellar's Theorem
  25.6**: `∂f(x)` is the convex hull of the gradient cluster set at `x`;
* `TauCeti.subgradientImage_subset_closedConvexHull_of_ae_mem` and
  `TauCeti.subgradientImage_subset_closure_of_convex_of_ae_mem` — almost-everywhere gradient bounds
  on an open set control the full subgradient image on that set.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 25.6.
* G. De Philippis and A. Figalli, *The Monge–Ampère equation and its link to optimal
  transportation*, Bull. Amer. Math. Soc. (N.S.) 51 (2014), 527–580, Step 2 of the proof of
  Theorem 3.3.
-/

public section

namespace TauCeti

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped Topology Gradient RealInnerProductSpace

section ClusterSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {S : Set E} {x : E}

/-- Near an interior point `x` of the effective domain of a convex `f : E → EReal`, on an approach
set `S` where the real representative is eventually differentiable, the gradient is eventually
subdifferential-valued and uniformly bounded in norm. -/
private lemma eventually_gradient_mem_subdifferential_and_closedBall
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hx : x ∈ interior {x' | f x' ≠ ⊤})
    (hdiff : ∀ᶠ z in 𝓝[S] x, DifferentiableAt ℝ (fun x' => (f x').toReal) z) :
    ∃ r > 0, ∃ R ≥ 0, closedBall x r ⊆ interior {x' | f x' ≠ ⊤} ∧
      ∀ᶠ z in 𝓝[S] x, z ∈ closedBall x r ∧
        (∇ fun x' => (f x').toReal) z ∈ subdifferential (innerₗ E) f z ∧
        (∇ fun x' => (f x').toReal) z ∈ closedBall (0 : E) R := by
  obtain ⟨r, hr, hrD⟩ : ∃ r > 0, closedBall x r ⊆ interior {x' | f x' ≠ ⊤} :=
    nhds_basis_closedBall.mem_iff.1 (isOpen_interior.mem_nhds hx)
  obtain ⟨R, hR⟩ := exists_norm_le_of_mem_subdifferential hf hbot (isCompact_closedBall x r) hrD
  refine ⟨r, hr, max R 0, le_max_right R 0, hrD, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (closedBall_mem_nhds x hr), hdiff] with z hzr hdz
  have hsub := gradient_toReal_mem_subdifferential hf hbot (interior_subset (hrD hzr)) hdz
  exact ⟨hzr, hsub, mem_closedBall_zero_iff.2 ((hR z hzr _ hsub).trans (le_max_left R 0))⟩

/-- Along any set `S` on which the real representative of a convex `f : E → EReal` is eventually
differentiable near `x ∈ interior {x' | f x' ≠ ⊤}`, the gradient tends to the neighbourhood filter
of its cluster set at `x`. -/
theorem tendsto_gradient_toReal_nhdsSet_clusterSetOn
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hx : x ∈ interior {x' | f x' ≠ ⊤})
    (hdiff : ∀ᶠ z in 𝓝[S] x, DifferentiableAt ℝ (fun x' => (f x').toReal) z) :
    Tendsto (∇ fun x' => (f x').toReal) (𝓝[S] x)
      (𝓝ˢ (clusterSetOn (∇ fun x' => (f x').toReal) S x)) := by
  obtain ⟨_, _, R, _, _, hev⟩ :=
    eventually_gradient_mem_subdifferential_and_closedBall hf hbot hx hdiff
  exact (isCompact_closedBall (0 : E) R).tendsto_nhdsSet_of_mapClusterPt
    (hev.mono fun _ hz => hz.2.2) fun _ _ hy => mem_clusterSetOn_iff.2 hy

/-- The cluster set of the gradient of a convex `f : E → EReal` at `x ∈ interior {x' | f x' ≠ ⊤}`,
along a set `S` where the real representative is eventually differentiable near `x`, is compact. -/
theorem isCompact_clusterSetOn_gradient_toReal
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hx : x ∈ interior {x' | f x' ≠ ⊤})
    (hdiff : ∀ᶠ z in 𝓝[S] x, DifferentiableAt ℝ (fun x' => (f x').toReal) z) :
    IsCompact (clusterSetOn (∇ fun x' => (f x').toReal) S x) := by
  obtain ⟨_, _, R, _, _, hev⟩ :=
    eventually_gradient_mem_subdifferential_and_closedBall hf hbot hx hdiff
  obtain ⟨V, hVo, hxV, hSV⟩ := mem_nhdsWithin.1 hev
  rw [← clusterSetOn_inter_of_mem_nhds (hVo.mem_nhds hxV)]
  exact isCompact_clusterSetOn (isCompact_closedBall (0 : E) R) fun z hz =>
    (hSV ⟨hz.2, hz.1⟩).2.2

/-- At an adherent point `x ∈ closure S` inside `interior {x' | f x' ≠ ⊤}`, the gradient cluster
set of a convex `f : E → EReal` along `S` is nonempty whenever the real representative is
eventually differentiable along `𝓝[S] x`. -/
theorem clusterSetOn_gradient_toReal_nonempty
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hx : x ∈ interior {x' | f x' ≠ ⊤}) (hxS : x ∈ closure S)
    (hdiff : ∀ᶠ z in 𝓝[S] x, DifferentiableAt ℝ (fun x' => (f x').toReal) z) :
    (clusterSetOn (∇ fun x' => (f x').toReal) S x).Nonempty := by
  obtain ⟨_, _, R, _, _, hev⟩ :=
    eventually_gradient_mem_subdifferential_and_closedBall hf hbot hx hdiff
  obtain ⟨V, hVo, hxV, hSV⟩ := mem_nhdsWithin.1 hev
  have hcl : x ∈ closure (S ∩ V) := by
    rw [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds
      (hVo.mem_nhds hxV)), ← mem_closure_iff_nhdsWithin_neBot]
    exact hxS
  rw [← clusterSetOn_inter_of_mem_nhds (hVo.mem_nhds hxV)]
  exact clusterSetOn_nonempty (isCompact_closedBall (0 : E) R)
    (fun z hz => (hSV ⟨hz.2, hz.1⟩).2.2) hcl

/-- Every cluster value of the gradient of a convex `f : E → EReal` at
`x ∈ interior {x' | f x' ≠ ⊤}`, along a set `S` where the real representative is eventually
differentiable near `x`, belongs to the subdifferential `∂f(x)`. -/
theorem clusterSetOn_gradient_toReal_subset_subdifferential
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hx : x ∈ interior {x' | f x' ≠ ⊤})
    (hdiff : ∀ᶠ z in 𝓝[S] x, DifferentiableAt ℝ (fun x' => (f x').toReal) z) :
    clusterSetOn (∇ fun x' => (f x').toReal) S x ⊆ subdifferential (innerₗ E) f x := by
  set G := ∇ fun x' => (f x').toReal
  obtain ⟨r, _, _, _, hrD, hev⟩ :=
    eventually_gradient_mem_subdifferential_and_closedBall hf hbot hx hdiff
  have hcl : IsClosed {p : E × E | p.1 ∈ closedBall x r ∧ p.2 ∈ subdifferential (innerₗ E) f p.1} :=
    isClosed_setOf_mem_subdifferential hbot isClosed_closedBall (hrD.trans interior_subset)
      ((convexOn_toReal hf hbot).continuousOn_interior.mono hrD)
  intro y hy
  have hcp : MapClusterPt (x, y) (𝓝[S] x) (fun z => (z, G z)) := by
    refine mapClusterPt_iff_frequently.2 fun W hW => ?_
    obtain ⟨U₁, hU₁, U₂, hU₂, hU⟩ := mem_nhds_prod_iff.1 hW
    exact ((mem_clusterSetOn_iff_frequently.1 hy U₂ hU₂).and_eventually
      (nhdsWithin_le_nhds hU₁)).mono fun z hz => hU ⟨hz.2, hz.1⟩
  exact (hcl.mem_of_mapClusterPt hcp (hev.mono fun z hz => ⟨hz.1, hz.2.1⟩)).2

omit [FiniteDimensional ℝ E] in
/-- If `y₀ ∈ ∂f(x)` while `⟪v, G z⟫ < α < ⟪v, y₀⟫` and `‖G z‖ ≤ R` on `S ∩ U` for a neighbourhood
`U` of `x` with `closure S ∈ 𝓝 x`, stepping from `x` along `v` into `S` contradicts monotonicity
of `∂f`. -/
private lemma false_of_mem_subdifferential_of_eventually_inner_lt
    {G : E → E} {y₀ v : E} {α R : ℝ} (hR : 0 ≤ R) (hS : closure S ∈ 𝓝 x)
    (hy₀ : y₀ ∈ subdifferential (innerₗ E) f x) (hα : α < ⟪v, y₀⟫)
    (hev : ∀ᶠ z in 𝓝[S] x, G z ∈ subdifferential (innerₗ E) f z ∧ ‖G z‖ ≤ R ∧ ⟪v, G z⟫ < α) :
    False := by
  obtain ⟨U, hUo, hxU, hSU⟩ := mem_nhdsWithin.1 hev
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (hUo.mem_nhds hxU) hS)
  set t := δ / (2 * (‖v‖ + 1))
  have ht : 0 < t := div_pos hδ (by positivity)
  have htv : ‖t • v‖ < δ / 2 := by
    rw [norm_smul, Real.norm_of_nonneg ht.le, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity)
      zero_lt_two]
    nlinarith [norm_nonneg v]
  set M := R + ‖y₀‖ + 1
  have hM : 0 < M := by positivity
  set ρ := min (δ / 2) ((t * (⟪v, y₀⟫ - α) / 2) / M)
  have hρ : 0 < ρ := lt_min (half_pos hδ)
    (div_pos (half_pos (mul_pos ht (sub_pos.2 hα))) hM)
  have hwcl : x + t • v ∈ closure S :=
    (hball (mem_ball_iff_norm.2 (by rw [add_sub_cancel_left]; exact htv.trans (half_lt_self hδ)))).2
  obtain ⟨z, hzρ, hzS⟩ := mem_closure_iff.1 hwcl _ isOpen_ball (mem_ball_self hρ)
  have hzδ : z ∈ ball x δ := by
    rw [mem_ball_iff_norm] at hzρ ⊢
    calc ‖z - x‖ = ‖(z - (x + t • v)) + t • v‖ := by congr 1; abel
      _ ≤ ‖z - (x + t • v)‖ + ‖t • v‖ := norm_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add_of_le_of_lt (hzρ.le.trans (min_le_left _ _)) htv
      _ = δ := add_halves δ
  obtain ⟨hGz, hGzR, hGzα⟩ := hSU ⟨(hball hzδ).1, hzS⟩
  have hmono : ⟪z - x, y₀ - G z⟫ ≤ 0 := by
    have h := apply_le_apply_of_mem_subdifferential (innerₗ E) hy₀ hGz
    simp only [innerₗ_apply_apply] at h
    rw [inner_sub_right]
    linarith
  have hdecomp : ⟪z - x, y₀ - G z⟫ =
      t * (⟪v, y₀⟫ - ⟪v, G z⟫) + ⟪z - (x + t • v), y₀ - G z⟫ := by
    have hzx : z - x = t • v + (z - (x + t • v)) := by abel
    rw [hzx, inner_add_left, inner_smul_left, inner_sub_right, RCLike.conj_to_real]
  have herr : |⟪z - (x + t • v), y₀ - G z⟫| < t * (⟪v, y₀⟫ - α) := by
    calc |⟪z - (x + t • v), y₀ - G z⟫|
        ≤ ‖z - (x + t • v)‖ * ‖y₀ - G z‖ := abs_real_inner_le_norm _ _
      _ ≤ ρ * M := mul_le_mul (mem_ball_iff_norm.1 hzρ).le
          ((norm_sub_le y₀ (G z)).trans (by linarith)) (norm_nonneg _) hρ.le
      _ ≤ t * (⟪v, y₀⟫ - α) / 2 := (le_div_iff₀ hM).1 (min_le_right _ _)
      _ < t * (⟪v, y₀⟫ - α) := half_lt_self (mul_pos ht (sub_pos.2 hα))
  have hgt : t * (⟪v, y₀⟫ - α) ≤ t * (⟪v, y₀⟫ - ⟪v, G z⟫) :=
    mul_le_mul_of_nonneg_left (by linarith) ht.le
  linarith [(abs_lt.1 herr).1, hdecomp, hgt, hmono]

/-- **Rockafellar's Theorem 25.6.** Let `f : E → EReal` be convex and never `⊥` on a
finite-dimensional real inner product space, let `x` lie in the interior of its effective domain,
and let `S` be a set with `closure S ∈ 𝓝 x` along which the real representative of `f` is
eventually differentiable near `x`. Then the subdifferential of `f` at `x` is the convex hull of
the cluster set of `∇ (fun x' => (f x').toReal)` along `S` at `x`. -/
theorem subdifferential_eq_convexHull_clusterSetOn
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hx : x ∈ interior {x' | f x' ≠ ⊤}) (hS : closure S ∈ 𝓝 x)
    (hdiff : ∀ᶠ z in 𝓝[S] x, DifferentiableAt ℝ (fun x' => (f x').toReal) z) :
    subdifferential (innerₗ E) f x =
      convexHull ℝ (clusterSetOn (∇ fun x' => (f x').toReal) S x) := by
  set G := ∇ fun x' => (f x').toReal
  set C := clusterSetOn G S x
  refine Subset.antisymm (fun y₀ hy₀ => ?_)
    (convexHull_min (clusterSetOn_gradient_toReal_subset_subdifferential hf hbot hx hdiff)
      (convex_subdifferential (innerₗ E) f x))
  by_contra hy₀C
  have hK : IsCompact (convexHull ℝ C) :=
    (isCompact_clusterSetOn_gradient_toReal hf hbot hx hdiff).convexHull
  obtain ⟨ℓ, α, hCα, hαy₀⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ C) hK.isClosed hy₀C
  set v : E := (toDual ℝ E).symm ℓ
  have hv (y : E) : ℓ y = ⟪v, y⟫ := by
    rw [← (toDual ℝ E).apply_symm_apply ℓ, toDual_apply_apply]
  have hHopen : IsOpen {y : E | ⟪v, y⟫ < α} :=
    isOpen_lt (continuous_const.inner continuous_id) continuous_const
  have hGH : ∀ᶠ z in 𝓝[S] x, ⟪v, G z⟫ < α :=
    (tendsto_gradient_toReal_nhdsSet_clusterSetOn hf hbot hx hdiff).eventually
      (hHopen.mem_nhdsSet.2 fun y hy => by
        simpa only [mem_ofPred_eq, ← hv y] using hCα y (subset_convexHull ℝ C hy))
  obtain ⟨_, _, R, hR, _, hev⟩ :=
    eventually_gradient_mem_subdifferential_and_closedBall hf hbot hx hdiff
  refine false_of_mem_subdifferential_of_eventually_inner_lt (G := G) hR hS hy₀ (hv y₀ ▸ hαy₀) ?_
  filter_upwards [hev, hGH] with z hz hzα
  exact ⟨hz.2.1, mem_closedBall_zero_iff.1 hz.2.2, hzα⟩

/-- **Rockafellar's Theorem 25.6 (differentiability-locus form).** At every interior point `x` of
the effective domain of a convex `f : E → EReal`, never `⊥`, on a finite-dimensional real inner
product space, the subdifferential `∂f(x)` is the convex hull of the cluster set of
`∇ (fun x' => (f x').toReal)` at `x` along the set of points where the real representative is
differentiable. -/
theorem subdifferential_eq_convexHull_clusterSetOn_differentiableAt
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hx : x ∈ interior {x' | f x' ≠ ⊤}) :
    subdifferential (innerₗ E) f x =
      convexHull ℝ (clusterSetOn (∇ fun x' => (f x').toReal)
        {z | DifferentiableAt ℝ (fun x' => (f x').toReal) z} x) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hcl : interior {x' | f x' ≠ ⊤} ⊆
      closure {z | DifferentiableAt ℝ (fun x' => (f x').toReal) z} :=
    isOpen_interior.subset_closure_of_ae_le (μ := Measure.addHaar)
      (convexOn_toReal hf hbot).ae_differentiableAt_of_mem_interior
  exact subdifferential_eq_convexHull_clusterSetOn hf hbot hx
    (mem_of_superset (isOpen_interior.mem_nhds hx) hcl) self_mem_nhdsWithin

end ClusterSet

section SubgradientImage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]
  {f : E → EReal} {U Y : Set E}

/-- **Almost-everywhere gradient bounds on an open set control the subgradient image.** Let
`f : E → EReal` be convex and never `⊥` on a finite-dimensional real inner product space with an
additive Haar measure `ρ`, and let `U` be an open set on which `f` is finite `ρ`-almost everywhere
and `∇ (fun x' => (f x').toReal) z ∈ Y` for `ρ`-almost every `z ∈ U`. Then `U` lies in the
interior of the effective domain of `f`, and `∂f(U) ⊆ closedConvexHull ℝ Y`. Neither `U` nor `Y`
need be convex or bounded, and `Y` need not be measurable. -/
theorem subgradientImage_subset_closedConvexHull_of_ae_mem
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) (hU : IsOpen U)
    (hdom : ∀ᵐ z ∂ρ, z ∈ U → f z ≠ ⊤)
    (hY : ∀ᵐ z ∂ρ, z ∈ U → (∇ fun x' => (f x').toReal) z ∈ Y) :
    U ⊆ interior {x' | f x' ≠ ⊤} ∧
      subgradientImage (innerₗ E) f U ⊆ closedConvexHull ℝ Y := by
  have hUD : U ⊆ interior {x' | f x' ≠ ⊤} :=
    hU.subset_interior_of_ae_le (convex_setOf_ne_top hf) hdom
  set G := ∇ fun x' => (f x').toReal
  set S := U ∩ {z | DifferentiableAt ℝ (fun x' => (f x').toReal) z ∧ G z ∈ Y}
  have hUS : U ≤ᵐ[ρ] S := by
    filter_upwards [(convexOn_toReal hf hbot).ae_differentiableAt_of_mem_interior, hY] with z hdz
      hzY hzU
    exact ⟨hzU, hdz (hUD hzU), hzY hzU⟩
  have hUcl : U ⊆ closure S := hU.subset_closure_of_ae_le hUS
  refine ⟨hUD, fun y hy => ?_⟩
  obtain ⟨x, hxU, hyx⟩ := (mem_subgradientImage_iff _).1 hy
  rw [subdifferential_eq_convexHull_clusterSetOn (S := S) hf hbot (hUD hxU)
    (mem_of_superset (hU.mem_nhds hxU) hUcl)
    (eventually_of_mem self_mem_nhdsWithin fun z (hz : z ∈ S) => hz.2.1)] at hyx
  exact convexHull_min (clusterSetOn_subset_closure_image.trans <|
    (closure_mono (image_subset_iff.2 fun z (hz : z ∈ S) => hz.2.2)).trans
      closure_subset_closedConvexHull) convex_closedConvexHull hyx

/-- **Subgradient image in a convex target.** Under the hypotheses of
`TauCeti.subgradientImage_subset_closedConvexHull_of_ae_mem`, if `Y` is convex then `U` lies in the
interior of the effective domain of `f` and `∂f(U) ⊆ closure Y`. -/
theorem subgradientImage_subset_closure_of_convex_of_ae_mem
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) (hU : IsOpen U)
    (hY : Convex ℝ Y) (hdom : ∀ᵐ z ∂ρ, z ∈ U → f z ≠ ⊤)
    (hGY : ∀ᵐ z ∂ρ, z ∈ U → (∇ fun x' => (f x').toReal) z ∈ Y) :
    U ⊆ interior {x' | f x' ≠ ⊤} ∧ subgradientImage (innerₗ E) f U ⊆ closure Y := by
  obtain ⟨hUD, hsub⟩ := subgradientImage_subset_closedConvexHull_of_ae_mem hf hbot hU hdom hGY
  exact ⟨hUD, hsub.trans (closedConvexHull_min subset_closure hY.closure isClosed_closure)⟩

end SubgradientImage

end TauCeti
