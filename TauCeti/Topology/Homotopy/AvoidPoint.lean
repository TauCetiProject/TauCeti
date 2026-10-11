/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Homotoping a map off a point of a higher-dimensional chart

Let `D` be a closed subset of a finite-dimensional real normed space `E`, let `Y` be a Hausdorff
space, and let `φ` be a chart of `Y` with values in a finite-dimensional real normed space `F`
whose target contains a ball `B = ball c r`. If `dim E < dim F`, then every map `f : D → Y` is
homotopic, relative to the points that `f` sends outside `φ⁻¹(B)`, to a map that misses a point
of `φ⁻¹(B)`.

This is the key lemma behind cellular approximation, where `D` is a cube or a disk, `Y` is a
complex `Z ∪ eⁿ` with a cell attached, and `φ` is the inverse of the characteristic map on the
open cell. Hatcher's proof approximates `f` by a map that is linear on the simplices of a fine
subdivision. Here the approximation is smooth instead:

* by the Tietze extension theorem, `φ ∘ f` restricted to the closed set of points sent into
  `φ⁻¹(closedBall c (r / 2))` extends to a continuous map `E → F`, which Mathlib approximates
  uniformly within `r / 8` by a smooth map `G : E → F`
  (`Continuous.exists_contDiff_approx`);
* since `dim E < dim F`, the complement of the range of `G` is dense
  (`Differentiable.dense_compl_range_of_finrank_lt_finrank`), so some point `p` of
  `ball c (r / 8)` is not a value of `G`;
* a bump function (`ContDiffBump`) equal to `1` on `closedBall c (r / 4)` and supported in
  `ball c (r / 2)` interpolates between `φ ∘ f` and `G`. The interpolated map agrees with `G`,
  hence avoids `p`, where `φ ∘ f` lies in `closedBall c (r / 4)`, and moves `φ ∘ f` by less than
  `r / 8` elsewhere, hence also avoids `p` there;
* the straight-line homotopy in the chart from `φ ∘ f` to the interpolated map stays in
  `ball c r` and is stationary wherever the bump function vanishes, so it glues with the constant
  homotopy outside the chart (`ContinuousMap.exists_homotopyRel_of_segment_subset_target`).

## Main results

* `ContinuousMap.exists_homotopyRel_of_segment_subset_target`: a map can be moved along straight
  lines in a chart, relative to the points that do not move, provided the closure of the moving
  points stays in the chart.
* `ContinuousMap.exists_homotopyRel_notMem_range`: a map from a closed subset of a space of
  smaller dimension is homotopic, relative to the preimage of the complement of `φ⁻¹(B)`, to a
  map missing a point of `φ⁻¹(B)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Lemma 4.10.
-/

public section

open Set Metric Module

namespace ContinuousMap

section Chart

variable {X Y F : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- **Straight-line homotopy inside a chart.** Let `φ` be a chart of `Y` with values in a real
topological vector space, and let `w` assign a new chart value, continuously, to each point that
`f` sends into the chart, so that the segment from `φ (f x)` to `w x` stays in the target. If the
closure of the set of points that actually move stays inside `f ⁻¹' φ.source`, then `f` is
homotopic, relative to any set of points that do not move, to the map equal to `φ.symm ∘ w` on
`f ⁻¹' φ.source` and to `f` elsewhere. -/
theorem exists_homotopyRel_of_segment_subset_target (f : C(X, Y)) (φ : OpenPartialHomeomorph Y F)
    {w : X → F} (hw : ContinuousOn w (f ⁻¹' φ.source))
    (hclosure : closure {x | f x ∈ φ.source ∧ w x ≠ φ (f x)} ⊆ f ⁻¹' φ.source)
    (hseg : ∀ x, f x ∈ φ.source → segment ℝ (φ (f x)) (w x) ⊆ φ.target)
    {S : Set X} (hS : ∀ x ∈ S, f x ∈ φ.source → w x = φ (f x)) :
    ∃ g : C(X, Y), (∀ x, f x ∈ φ.source → g x = φ.symm (w x)) ∧
      (∀ x, f x ∉ φ.source → g x = f x) ∧ Nonempty (f.HomotopyRel g S) := by
  classical
  have hmem : ∀ (t : unitInterval) x, f x ∈ φ.source →
      (t : ℝ) • (w x - φ (f x)) + φ (f x) ∈ φ.target := fun t x hx =>
    hseg x hx (AffineMap.lineMap_apply_module' (φ (f x)) (w x) (t : ℝ) ▸
      lineMap_mem_segment ℝ _ _ t.2)
  let H : unitInterval × X → Y := fun q =>
    if f q.2 ∈ φ.source then φ.symm ((q.1 : ℝ) • (w q.2 - φ (f q.2)) + φ (f q.2)) else f q.2
  have hH_eq : ∀ q : unitInterval × X, (f q.2 ∈ φ.source → w q.2 = φ (f q.2)) → H q = f q.2 := by
    intro q h
    simp only [H]
    split_ifs with hx
    · simp [h hx, φ.left_inv hx]
    · rfl
  have hHc : Continuous H := by
    set M := closure {x | f x ∈ φ.source ∧ w x ≠ φ (f x)}
    have hcover : {q : unitInterval × X | f q.2 ∈ φ.source} ∪ {q | q.2 ∉ M} = univ :=
      eq_univ_of_forall fun q => by
        by_cases hq : q.2 ∈ M
        · exact Or.inl (hclosure hq)
        · exact Or.inr hq
    rw [← continuousOn_univ, ← hcover]
    refine ContinuousOn.union_of_isOpen ?_ ?_
      (φ.open_source.preimage (f.continuous.comp continuous_snd))
      (isClosed_closure.isOpen_compl.preimage continuous_snd)
    · have hφf : ContinuousOn (fun q : unitInterval × X => φ (f q.2))
          {q | f q.2 ∈ φ.source} :=
        φ.continuousOn.comp (f.continuous.comp continuous_snd).continuousOn fun q hq => hq
      have hw' : ContinuousOn (fun q : unitInterval × X => w q.2) {q | f q.2 ∈ φ.source} :=
        hw.comp continuous_snd.continuousOn fun q hq => hq
      refine ContinuousOn.congr ?_ fun q hq => ite_eq_left hq
      exact φ.continuousOn_symm.comp
        ((ContinuousOn.smul (by fun_prop) (hw'.sub hφf)).add hφf) fun q hq => hmem q.1 q.2 hq
    · refine (f.continuous.comp continuous_snd).continuousOn.congr fun q hq =>
        hH_eq q fun hx => ?_
      by_contra hne
      exact hq (subset_closure ⟨hx, hne⟩)
  refine ⟨⟨fun x => H (1, x), hHc.comp (continuous_const.prodMk continuous_id)⟩,
    fun x hx => ?_, fun x hx => ite_eq_right hx,
    ⟨{ toFun := H
       continuous_toFun := hHc
       map_zero_left := fun x => ?_
       map_one_left := fun x => rfl
       prop' := fun t x hx => hH_eq (t, x) (hS x hx) }⟩⟩
  · simp [H, hx]
  · simp only [H]
    split_ifs with hx
    · simp [φ.left_inv hx]
    · rfl

end Chart

variable {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace Y] [T2Space Y]

/-- **Homotoping a map off a point of a higher-dimensional chart** (Hatcher, Lemma 4.10). Let
`D` be a closed subset of `E`, and let `φ` be a chart of the Hausdorff space `Y` into `F` whose
target contains `ball c r`. If `dim E < dim F`, then every map `f : D → Y` is homotopic, relative
to the points that `f` does not send into `φ.symm '' ball c r`, to a map `g` missing the point
`φ.symm p` for some `p ∈ ball c r`. -/
theorem exists_homotopyRel_notMem_range {D : Set E} (f : C(D, Y)) (hD : IsClosed D)
    (hEF : finrank ℝ E < finrank ℝ F) (φ : OpenPartialHomeomorph Y F) {c : F} {r : ℝ}
    (hr : 0 < r) (hφ : ball c r ⊆ φ.target) :
    ∃ g : C(D, Y), Nonempty (f.HomotopyRel g (f ⁻¹' (φ.symm '' ball c r))ᶜ) ∧
      ∃ p ∈ ball c r, φ.symm p ∉ range g := by
  -- The closed set `K` of points sent into the half-radius ball, where `φ ∘ f` is smoothed.
  have hsub : closedBall c (r / 2) ⊆ φ.target :=
    (closedBall_subset_ball (by linarith)).trans hφ
  set K : Set D := f ⁻¹' (φ.symm '' closedBall c (r / 2))
  have hK : IsClosed K :=
    ((isCompact_closedBall c _).image_of_continuousOn
      (φ.continuousOn_symm.mono hsub)).isClosed.preimage f.continuous
  have hKsource : K ⊆ f ⁻¹' φ.source := by
    rintro x ⟨y, hy, hxy⟩
    rw [mem_preimage, ← hxy]
    exact φ.map_target (hsub hy)
  -- Extend `φ ∘ f` from `K` to `E`, approximate the extension by a smooth map `G`, and choose a
  -- point `p` near `c` that `G` misses.
  obtain ⟨u, hu⟩ := ContinuousMap.exists_extension
    (hD.isClosedEmbedding_subtypeVal.comp hK.isClosedEmbedding_subtypeVal)
    ⟨fun x : K => φ (f x), φ.continuousOn.comp_continuous
      (f.continuous.comp continuous_subtype_val) fun x => hKsource x.2⟩
  have hu' : ∀ x ∈ K, u x = φ (f x) := fun x hx => congr($hu ⟨x, hx⟩)
  obtain ⟨G, hG, hGu, -⟩ := u.continuous.exists_contDiff_approx (1 : ℕ∞) continuous_const
    (fun _ => show (0 : ℝ) < r / 8 by positivity)
  obtain ⟨p, hp, hpG⟩ :=
    ((hG.differentiable one_ne_zero).dense_compl_range_of_finrank_lt_finrank
      hEF).inter_open_nonempty (ball c (r / 8)) isOpen_ball (nonempty_ball.2 (by positivity))
  -- Interpolate between `φ ∘ f` and `G` with a bump function equal to `1` on
  -- `closedBall c (r / 4)` and supported in `ball c (r / 2)`.
  let β : ContDiffBump c := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hβ_zero : ∀ y, β y ≠ 0 → dist y c < r / 2 := fun y hy => by
    by_contra! h
    exact hy (β.zero_of_le_dist h)
  let d : D → F := fun x => β (φ (f x)) • (G x - φ (f x))
  have hK_of : ∀ x, f x ∈ φ.source → β (φ (f x)) ≠ 0 → x ∈ K := fun x hx hβ =>
    ⟨φ (f x), mem_closedBall.2 (hβ_zero _ hβ).le, φ.left_inv hx⟩
  have hd_lt : ∀ x, f x ∈ φ.source → ‖d x‖ < r / 8 := by
    intro x hx
    by_cases hβ : β (φ (f x)) = 0
    · simpa [d, hβ] using (by positivity : (0 : ℝ) < r / 8)
    · calc ‖d x‖ = β (φ (f x)) * ‖G x - φ (f x)‖ := by
            simp [d, norm_smul, abs_of_nonneg β.nonneg]
        _ ≤ ‖G x - φ (f x)‖ := mul_le_of_le_one_left (norm_nonneg _) β.le_one
        _ < r / 8 := by
            rw [← hu' x (hK_of x hx hβ), ← dist_eq_norm]
            exact hGu x
  -- The segments from `φ ∘ f` to the interpolated map stay in the chart.
  have hseg : ∀ x, f x ∈ φ.source → segment ℝ (φ (f x)) (φ (f x) + d x) ⊆ φ.target := by
    intro x hx
    by_cases hβ : β (φ (f x)) = 0
    · simpa [d, hβ] using φ.map_source hx
    · refine ((convex_ball (φ (f x)) (r / 8)).segment_subset (mem_ball_self (by positivity))
        ?_).trans ((ball_subset_ball' ?_).trans hφ)
      · simpa [mem_ball, dist_eq_norm] using hd_lt x hx
      · linarith [hβ_zero _ hβ]
  obtain ⟨g, hg, hg', ⟨Hf⟩⟩ := f.exists_homotopyRel_of_segment_subset_target φ
    (w := fun x => φ (f x) + d x)
    (S := (f ⁻¹' (φ.symm '' ball c r))ᶜ)
    (by
      have hφf : ContinuousOn (fun x => φ (f x)) (f ⁻¹' φ.source) :=
        φ.continuousOn.comp f.continuous.continuousOn fun x hx => hx
      exact hφf.add ((β.continuous.comp_continuousOn hφf).smul
        ((hG.continuous.comp continuous_subtype_val).continuousOn.sub hφf)))
    (by
      refine (closure_minimal (fun x hx => hK_of x hx.1 fun hβ => hx.2 ?_) hK).trans hKsource
      simp [d, hβ])
    hseg
    (by
      intro x hx hs
      by_contra hne
      have hβ : β (φ (f x)) ≠ 0 := fun hβ => hne (by simp [d, hβ])
      exact hx ⟨φ (f x), mem_ball.2 ((hβ_zero _ hβ).trans (by linarith)), φ.left_inv hs⟩)
  refine ⟨g, ⟨Hf⟩, p, ball_subset_ball (by linarith) hp, ?_⟩
  rintro ⟨x, hx⟩
  have hpt : p ∈ φ.target := hφ (ball_subset_ball (by linarith) hp)
  by_cases hs : f x ∈ φ.source
  · -- Inside the chart, `g x = φ.symm (φ (f x) + d x)`, so `φ (f x) + d x = p`.
    have hv := φ.symm.injOn (by rw [φ.symm_source]; exact hseg x hs (right_mem_segment _ _ _))
      (by rw [φ.symm_source]; exact hpt) ((hg x hs).symm.trans hx)
    by_cases hc : dist (φ (f x)) c ≤ r / 4
    · exact hpG ⟨x, by rw [← hv]; simp [d, β.one_of_mem_closedBall (mem_closedBall.2 hc)]⟩
    · have := dist_triangle (φ (f x)) (φ (f x) + d x) c
      rw [dist_self_add_right] at this
      rw [mem_ball, ← hv] at hp
      linarith [hd_lt x hs]
  · rw [hg' x hs] at hx
    exact hs (hx ▸ φ.map_target hpt)

end ContinuousMap
