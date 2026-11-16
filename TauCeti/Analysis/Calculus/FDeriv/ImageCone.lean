/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Asymptotics.Arith

/-!
# Tangent cones containing differentiable images

At a differentiability point of a parametrization with a Lipschitz inverse, the image lies
locally in every cone around the range of the derivative. The inverse bound is essential:
it prevents distant parameters from returning arbitrarily close to the image point.

This pointwise estimate is the geometric input for approximate tangent planes of rectifiable
sets. It does not require measurability, finite dimension, or injectivity of the derivative.
Along an inverse-Lipschitz parametrization `f`, differentiability of a composite `g ∘ f` within
`s` also pushes forward to differentiability of `g` within the image `f '' s`
(`HasFDerivWithinAt.of_comp_antilipschitzWith`). Along vectors in the tangent cone of the
parameter set, the Lipschitz lower bound passes to the derivative
(`HasFDerivWithinAt.le_mul_norm_of_mem_tangentConeAt`), making the derivative antilipschitz when
the tangent cone is the whole parameter space.
-/

public section

open Set Filter Metric
open scoped Topology NNReal

/-- Near the image of a differentiability point, an inverse-Lipschitz parametrization lies
in every cone about the range of its derivative. The estimate includes the cone vertex. -/
theorem HasFDerivWithinAt.exists_pos_forall_infDist_range_le
    {𝕜 U V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] {f : U → V} {s : Set U} {x : U}
    {A : U →L[𝕜] V} (hd : HasFDerivWithinAt f A s x) (hx : x ∈ s)
    {K : ℝ≥0} (hi : AntilipschitzWith K (s.domRestrict f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ y ∈ f '' s, dist y (f x) < r →
      infDist (y - f x) (LinearMap.range A.toLinearMap : Set V) ≤ ε * dist y (f x) := by
  let C : ℝ := K + 1
  have hC : 0 < C := by positivity
  have hbound := hd.isLittleO.bound (div_pos hε hC)
  obtain ⟨δ, hδ, hδbound⟩ := eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp hbound)
  refine ⟨δ / C, div_pos hδ hC, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ hdist
  have hinv : dist z x ≤ C * dist (f z) (f x) := by
    exact (hi.le_mul_dist ⟨z, hz⟩ ⟨x, hx⟩).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) dist_nonneg)
  have hzδ : z ∈ ball x δ := by
    rw [mem_ball]
    exact hinv.trans_lt (by simpa only [mul_comm] using (lt_div_iff₀ hC).mp hdist)
  calc
    infDist (f z - f x) (LinearMap.range A.toLinearMap : Set V) ≤ dist (f z - f x) (A (z - x)) :=
      infDist_le_dist_of_mem ⟨z - x, rfl⟩
    _ ≤ (ε / C) * ‖z - x‖ := by
      simpa only [dist_eq_norm] using hδbound z hzδ hz
    _ ≤ (ε / C) * (C * dist (f z) (f x)) := by
      gcongr
      simpa only [dist_eq_norm] using hinv
    _ = ε * dist (f z) (f x) := by field_simp

/-- Along an inverse-Lipschitz parametrization `f`, if `g ∘ f` has derivative `B` within `s` at
`x ∈ s` and `D : V →L[𝕜] W` satisfies `D (A u) = B u`, then `g` has derivative `D` within `f '' s`
at `f x`. -/
theorem HasFDerivWithinAt.of_comp_antilipschitzWith
    {𝕜 U V W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {f : U → V} {g : V → W} {s : Set U} {x : U}
    {A : U →L[𝕜] V} {B : U →L[𝕜] W} {D : V →L[𝕜] W}
    (hf : HasFDerivWithinAt f A s x) (hx : x ∈ s)
    {K : ℝ≥0} (hi : AntilipschitzWith K (s.domRestrict f))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x) (hD : ∀ u, D (A u) = B u) :
    HasFDerivWithinAt g D (f '' s) (f x) := by
  have hrem : (fun y => g (f y) - g (f x) - D (f y - f x)) =o[𝓝[s] x] (fun y => y - x) := by
    have heq : (fun y => g (f y) - g (f x) - D (f y - f x)) =
        fun y => (g (f y) - g (f x) - B (y - x)) - D (f y - f x - A (y - x)) :=
      funext fun y => by
        have hsp : D (f y - f x) = B (y - x) + D (f y - f x - A (y - x)) := by
          rw [← hD (y - x), ← map_add, add_sub_cancel]
        rw [hsp]
        abel
    rw [heq]
    exact hgf.isLittleO.sub ((D.isBigO_comp _ _).trans_isLittleO hf.isLittleO)
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  let C : ℝ := K + 1
  have hC : 0 < C := by positivity
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (hrem.bound (div_pos hc hC)))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨δ / C, div_pos hδ hC, ?_⟩
  rintro _ hz ⟨y, hys, rfl⟩
  have hdy : dist y x ≤ C * dist (f y) (f x) :=
    (hi.le_mul_dist ⟨y, hys⟩ ⟨x, hx⟩).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) dist_nonneg)
  have hyδ : dist y x < δ :=
    hdy.trans_lt ((mul_lt_mul_of_pos_left hz hC).trans_eq (by field_simp))
  calc ‖g (f y) - g (f x) - D (f y - f x)‖
      ≤ (c / C) * dist y x := by simpa only [dist_eq_norm] using hb hyδ hys
    _ ≤ (c / C) * (C * dist (f y) (f x)) := mul_le_mul_of_nonneg_left hdy (by positivity)
    _ = c * ‖f y - f x‖ := by rw [dist_eq_norm]; field_simp

/-- Along every vector in the tangent cone of the parameter set, an inverse-Lipschitz
parametrization transfers its lower bound to its derivative. -/
theorem HasFDerivWithinAt.le_mul_norm_of_mem_tangentConeAt
    {𝕜 U V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f : U → V} {s : Set U} {x : U} {A : U →L[𝕜] V} (hd : HasFDerivWithinAt f A s x) (hx : x ∈ s)
    {K : ℝ≥0} (hi : AntilipschitzWith K (s.domRestrict f)) {v : U} (hv : v ∈ tangentConeAt 𝕜 s x) :
    ‖v‖ ≤ K * ‖A v‖ := by
  obtain ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
  refine le_of_tendsto_of_tendsto hcd.norm ((hd.lim hd₀ hds hcd).norm.const_mul (K : ℝ))
    (hds.mono fun n hn => ?_)
  have hdist : dist (x + d n) x ≤ K * dist (f (x + d n)) (f x) :=
    hi.le_mul_dist ⟨x + d n, hn⟩ ⟨x, hx⟩
  simp only [norm_smul, dist_eq_norm, add_sub_cancel_left] at hdist ⊢
  nlinarith [norm_nonneg (c n)]

/-- When the tangent cone of the parameter set is the whole space, an inverse-Lipschitz
parametrization has an antilipschitz derivative with the same constant. -/
theorem HasFDerivWithinAt.antilipschitzWith_of_tangentConeAt_eq_univ
    {𝕜 U V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f : U → V} {s : Set U} {x : U} {A : U →L[𝕜] V} (hd : HasFDerivWithinAt f A s x) (hx : x ∈ s)
    {K : ℝ≥0} (hi : AntilipschitzWith K (s.domRestrict f)) (htc : tangentConeAt 𝕜 s x = univ) :
    AntilipschitzWith K A :=
  AddMonoidHomClass.antilipschitz_of_bound A fun v =>
    hd.le_mul_norm_of_mem_tangentConeAt hx hi (htc.symm ▸ mem_univ v)
