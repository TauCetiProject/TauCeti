/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import TauCeti.Topology.ApproximateUnit

/-!
# Increasing approximate units: images and uniform convergence

A star-algebra homomorphism between C⋆-algebras is positive and contractive, so it maps the
positive part of the closed unit ball into itself. Hence the image of an increasing approximate
unit under a surjective homomorphism is an increasing approximate unit of the target,
`Filter.IsIncreasingApproximateUnit.map`. This transfers approximate-unit limits, such as the
norm of a positive functional, from a C⋆-algebra to its quotients.

Since an increasing approximate unit eventually lies in the closed unit ball, the convergence
`e * a → a` is uniform for `a` in a compact set,
`Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_right`. This controls
`e * α_r(b) → α_r(b)` uniformly along a compact set of group elements `r` for a continuous action
`α`.
-/

public section

open Filter
open scoped CStarAlgebra

namespace Filter.IsIncreasingApproximateUnit

section Uniform

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- Along an increasing approximate unit, `e * a → a` uniformly for `a` in a compact set. -/
theorem tendstoUniformlyOn_mul_right {l : Filter A} (hl : l.IsIncreasingApproximateUnit)
    {K : Set A} (hK : IsCompact K) : TendstoUniformlyOn (fun e a => e * a) id l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Cover `K` by finitely many balls of radius `ε / 3`, and use the eventual bound `‖e‖ ≤ 1`.
  obtain ⟨t, -, ht, hKt⟩ := hK.finite_cover_balls (e := ε / 3) (by positivity)
  have hconv : ∀ᶠ e in l, ∀ c ∈ t, dist c (e * c) < ε / 3 := (eventually_all_finite ht).2
    fun c _ => (Metric.tendsto_nhds.1 (hl.tendsto_mul_right c) (ε / 3) (by positivity)).mono
      fun _ h => by rwa [dist_comm]
  filter_upwards [hl.eventually_norm, hconv] with e he hc a ha
  obtain ⟨c, hct, hac⟩ := Set.mem_iUnion₂.1 (hKt ha)
  have hmul : dist (e * c) (e * a) ≤ dist c a := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) he)
  calc dist (id a) (e * a) ≤ dist a c + dist c (e * c) + dist (e * c) (e * a) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact Metric.mem_ball.1 hac
        · exact hc c hct
        · exact hmul.trans_lt (by rw [dist_comm]; exact Metric.mem_ball.1 hac)
    _ = ε := by ring

end Uniform

section Map

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- The image of an increasing approximate unit under a surjective star-algebra homomorphism of
C⋆-algebras is an increasing approximate unit. -/
theorem map {l : Filter A} (hl : l.IsIncreasingApproximateUnit) (f : F)
    (hf : Function.Surjective f) : (l.map f).IsIncreasingApproximateUnit where
  toIsApproximateUnit := hl.toIsApproximateUnit.map f (map_continuous f) hf
  eventually_nonneg := eventually_map.mpr <| hl.eventually_nonneg.mono fun _ hx => map_nonneg f hx
  eventually_norm := eventually_map.mpr <| hl.eventually_norm.mono fun a ha =>
    (NonUnitalStarAlgHom.norm_apply_le f a).trans ha

end Map

end Filter.IsIncreasingApproximateUnit
