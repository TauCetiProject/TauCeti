/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MetricBridge
public import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Lipschitz bounds from the centre of an intrinsic ball

Let `M` be a Riemannian manifold whose distance is the Riemannian distance. If a map `f` from `M`
to a real normed space is `C¹` on the open ball `B(p, r)` and stretches tangent vectors at points
of that ball by a factor at most `K`, then `‖f x - f p‖ ≤ K d(p, x)` for every `x ∈ B(p, r)`.

Nothing is assumed outside the ball and no completeness is needed: a `C¹` path from `p` of length
less than `s < r` stays in `B(p, s)`, since the distance from `p` to each of its points is at most
the length of the initial piece of the path.

The ball displacement estimate is adapted from Giada Franz’s verified `ForTauCeti` formalization.
-/

public section

open Bundle Filter Manifold Metric Set
open scoped ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- **Lipschitz bound from the centre of a ball.** A map `f` into a real normed space which is
`C¹` on the open ball `B(p, r)` and whose differential at points of the ball stretches tangent
vectors by at most `K` satisfies `‖f x - f p‖ ≤ K d(p, x)` on the ball. -/
theorem norm_sub_le_mul_dist_of_mem_ball {f : M → F} {p x : M} {r K : ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ, F) 1 f (ball p r)) (hK0 : 0 ≤ K)
    (hK : ∀ y ∈ ball p r, ∀ v : TangentSpace I y, ‖mvfderiv I f y v‖ ≤ K * ‖v‖)
    (hx : x ∈ ball p r) : ‖f x - f p‖ ≤ K * dist p x := by
  have key : ∀ s, dist p x < s → s < r → ‖f x - f p‖ ≤ K * s := by
    intro s hs hsr
    obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ :=
      TauCeti.IsRiemannianManifold.exists_pathELength_lt_of_dist_lt I hs
    have hball : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ball p r := fun t ht ↦
      ball_subset_ball hsr.le (mem_ball_of_pathELength_lt hγ hγ0 hlen ht)
    have hfγ : ∀ t ∈ Icc (0 : ℝ) 1, ContMDiffAt I 𝓘(ℝ, F) 1 f (γ t) := fun t ht ↦
      hf.contMDiffAt (isOpen_ball.mem_nhds (hball t ht))
    have h := enorm_sub_le_mul_pathELength zero_le_one (hγ.mdifferentiableOn one_ne_zero)
      (fun t ht ↦ (hfγ t ht).comp_contMDiffWithinAt t (hγ t ht))
      (fun t ht ↦ (hfγ t ht).mdifferentiableAt one_ne_zero) (C := NNReal.mk K hK0) (fun t ht ↦ by
        -- Compare real norms: the canonical identification from the tangent space of `F`
        -- preserves them, so `mvfderiv` and `mfderiv` give definitionally equal bounds.
        simpa only [← ofReal_norm, ENNReal.ofReal_mul hK0,
          ENNReal.ofReal_eq_coe_nnreal hK0] using! ENNReal.ofReal_le_ofReal (hK _ (hball t ht) _))
    rw [hγ0, hγ1] at h
    have h' : ‖f x - f p‖ₑ ≤ ENNReal.ofReal (K * s) := by
      refine h.trans ?_
      simpa only [ENNReal.ofReal_mul hK0, ENNReal.ofReal_eq_coe_nnreal hK0] using
        mul_le_mul_right hlen.le (ENNReal.ofReal K)
    rw [← ofReal_norm] at h'
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 (dist_nonneg.trans hs.le))).1 h'
  have hlim : Tendsto (fun s : ℝ ↦ K * s) (𝓝[>] (dist p x)) (𝓝 (K * dist p x)) :=
    ((continuous_const_mul K).tendsto _).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  have hxr : dist p x < r := by rwa [dist_comm, ← mem_ball]
  filter_upwards [Ioo_mem_nhdsGT hxr]
    with s hs
  exact key s hs.1 hs.2

end TauCeti.Manifold
