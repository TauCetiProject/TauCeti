/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UniformSpace.HeineCantor
public import TauCeti.Analysis.Calculus.ContinuousMap.Basic

/-!
# Local superposition on continuous maps

Postcomposition on a compact-domain continuous-map space is smooth wherever the original map
is smooth near the range. The operator need only be defined by postcomposition near the input
under consideration; no global extension, bump function, or finite-dimensional hypothesis is
required. This local formulation allows Picard integral equations for locally smooth fields on
Banach spaces to be differentiated in the uniform norm.

The uniform estimates use compactness of the input's range, rather than uniform continuity of
derivatives on a whole ball. Compare the global theorem `ContinuousMap.contDiff_postcomp`.

## References

* J. Appell and P. P. Zabrejko, *Nonlinear Superposition Operators*, Cambridge Tracts in
  Mathematics 95, Cambridge University Press, 1990.
-/

public section

open Filter Metric Set Topology
open scoped ContDiff

noncomputable section

namespace ContinuousMap

universe u v

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section FirstOrder

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An operator given locally by pointwise composition is continuous if the outer map is
continuous at every point of the compact input range. -/
theorem continuousAt_of_eventually_apply_eq {f : E → F} {g : C(K, E)}
    {Θ : C(K, E) → C(K, F)} (hf : ∀ t, ContinuousAt f (g t))
    (hΘ : ∀ᶠ h in 𝓝 g, ∀ t, Θ h t = f (h t)) : ContinuousAt Θ g := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_uniformity_dist.mp <|
    (isCompact_range g.continuous).uniformContinuousAt_of_continuousAt f
      (by rintro _ ⟨t, rfl⟩; exact hf t) (Metric.dist_mem_uniformity (half_pos hε))
  filter_upwards [hΘ, ball_mem_nhds g hδ] with h hh hball
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ((norm_le _ (half_pos hε).le).2 fun t ↦ ?_) (half_lt_self hε)
  simpa only [sub_apply, hh, hΘ.self_of_nhds, ← dist_eq_norm, dist_comm] using
    (hd (by simpa only [dist_comm] using (dist_apply_le_dist t).trans_lt hball)
      (mem_range_self t)).le

/-- A locally defined postcomposition operator has derivative given by pointwise application of
the derivatives of the outer map along the input. Only smoothness near that range is needed. -/
theorem hasFDerivAt_of_eventually_apply_eq {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn 𝕜 1 f s) {g : C(K, E)} (hg : ∀ t, g t ∈ s)
    {Θ : C(K, E) → C(K, F)} (hΘ : ∀ᶠ h in 𝓝 g, ∀ t, Θ h t = f (h t)) :
    HasFDerivAt Θ
      (applyContinuousLinearMap
        ⟨fun t ↦ fderiv 𝕜 f (g t),
          (hf.fderiv_of_isOpen hs (m := 0) (by simp)).continuousOn.comp_continuous
            g.continuous hg⟩) g := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hcompact := isCompact_range g.continuous
  obtain ⟨ρ, hρ, htube⟩ := hcompact.exists_thickening_subset_open hs (by
    rintro _ ⟨t, rfl⟩; exact hg t)
  have hdf := (hf.fderiv_of_isOpen hs (m := 0) (by simp)).continuousOn
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_uniformity_dist.mp <|
    hcompact.uniformContinuousAt_of_continuousAt (fderiv 𝕜 f)
      (by rintro _ ⟨t, rfl⟩; exact hdf.continuousAt (hs.mem_nhds (hg t)))
      (Metric.dist_mem_uniformity hc)
  filter_upwards [hΘ, ball_mem_nhds g (lt_min hρ hδ)] with h hh hball
  apply (norm_le _ (mul_nonneg hc.le (norm_nonneg _))).2
  intro t
  have hpoint : dist (h t) (g t) < min ρ δ := (dist_apply_le_dist t).trans_lt hball
  have hseg {z : E} (hz : z ∈ segment ℝ (g t) (h t)) : dist z (g t) < min ρ δ := by
    simpa only [dist_eq_norm] using (norm_sub_le_of_mem_segment hz).trans_lt
      (by simpa only [dist_eq_norm] using hpoint)
  have hmem {z : E} (hz : z ∈ segment ℝ (g t) (h t)) : z ∈ s :=
    htube (mem_thickening_iff.2 ⟨g t, mem_range_self t, (hseg hz).trans_le (min_le_left _ _)⟩)
  have hbound : ∀ z ∈ segment ℝ (g t) (h t),
      ‖fderiv 𝕜 f z - fderiv 𝕜 f (g t)‖ ≤ c := by
    intro z hz
    have hlt : dist (fderiv 𝕜 f (g t)) (fderiv 𝕜 f z) < c :=
      hd (by rw [dist_comm]; exact (hseg hz).trans_le (min_le_right _ _)) (mem_range_self t)
    simpa only [dist_eq_norm, norm_sub_rev] using hlt.le
  simp only [sub_apply, hh, hΘ.self_of_nhds, applyContinuousLinearMap_apply,
    ContinuousMap.coe_mk]
  exact ((convex_segment (𝕜 := ℝ) (g t) (h t)).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz ↦ (hf.contDiffAt (hs.mem_nhds (hmem hz))).differentiableAt one_ne_zero)
    hbound (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)).trans
      (mul_le_mul_of_nonneg_left (norm_coe_le_norm (h - g) t) hc.le)

end FirstOrder

-- The finite-order induction replaces the codomain by its space of linear maps.
variable {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem contDiffAt_of_eventually_apply_eq_nat (n : ℕ) {f : E → F} {s : Set E}
    (hs : IsOpen s) (hf : ContDiffOn 𝕜 n f s) {g : C(K, E)} (hg : ∀ t, g t ∈ s)
    {Θ : C(K, E) → C(K, F)} (hΘ : ∀ᶠ h in 𝓝 g, ∀ t, Θ h t = f (h t)) :
    ContDiffAt 𝕜 n Θ g := by
  induction n generalizing F g with
  | zero =>
    apply contDiffAt_zero.2
    have hevent : ∀ᶠ h in 𝓝 g, ContinuousAt Θ h := by
      filter_upwards [(eventually_eventually_nhds.2 hΘ),
        eventually_mapsTo isCompact_univ hs (fun t _ ↦ hg t)] with h hh hhs
      exact continuousAt_of_eventually_apply_eq
        (fun t ↦ hf.continuousOn.continuousAt (hs.mem_nhds (hhs (mem_univ t)))) hh
    exact ⟨{h | ContinuousAt Θ h}, hevent, fun h hh ↦ hh.continuousWithinAt⟩
  | succ n ih =>
    have hf₁ : ContDiffOn 𝕜 1 f s := hf.of_le (by exact_mod_cast Nat.succ_pos n)
    have hdf : ContDiffOn 𝕜 n (fderiv 𝕜 f) s :=
      hf.fderiv_of_isOpen hs (by simp)
    let D : C(K, E) → C(K, E →L[𝕜] F) :=
      fun h ↦ mkD (fun t ↦ fderiv 𝕜 f (h t)) 0
    have hD : ∀ᶠ h in 𝓝 g, ∀ t, D h t = fderiv 𝕜 f (h t) := by
      filter_upwards [eventually_mapsTo isCompact_univ hs (fun t _ ↦ hg t)] with h hh t
      exact mkD_apply_of_continuous
        (hdf.continuousOn.comp_continuous h.continuous (fun t ↦ hh (mem_univ t)))
    rw [Nat.cast_add, Nat.cast_one, contDiffAt_succ_iff_hasFDerivAt]
    have hA : ContDiff 𝕜 n
        (applyContinuousLinearMap (𝕜 := 𝕜) (K := K) (E := E) (F := F) :
          C(K, E →L[𝕜] F) → C(K, E) →L[𝕜] C(K, F)) := ContinuousLinearMap.contDiff _
    refine ⟨fun h ↦ applyContinuousLinearMap (D h), ?_,
      hA.comp_contDiffAt g (ih hdf hg hD)⟩
    rw [← Filter.eventually_iff_exists_mem]
    filter_upwards [eventually_eventually_nhds.2 hΘ, hD,
      eventually_mapsTo isCompact_univ hs (fun t _ ↦ hg t)] with h hh hd hhs
    convert hasFDerivAt_of_eventually_apply_eq hs hf₁
      (fun t ↦ hhs (mem_univ t)) hh using 1
    congr 1
    exact ContinuousMap.ext hd

/-- A superposition operator on compact-domain continuous maps is `C^n` at an input whose range
lies in an open set where the outer map is `C^n`. The operator need only agree with pointwise
composition near that input. No global regularity or completeness is assumed.

The codomain universe must be at least the domain universe, as required by the induction
through spaces of continuous linear maps. -/
theorem contDiffAt_of_eventually_apply_eq (n : ℕ∞) {f : E → F} {s : Set E}
    (hs : IsOpen s) (hf : ContDiffOn 𝕜 (n : ℕ∞ω) f s) {g : C(K, E)} (hg : ∀ t, g t ∈ s)
    {Θ : C(K, E) → C(K, F)} (hΘ : ∀ᶠ h in 𝓝 g, ∀ t, Θ h t = f (h t)) :
    ContDiffAt 𝕜 (n : ℕ∞ω) Θ g := by
  induction n using ENat.recTopCoe with
  | top =>
    rw [contDiffAt_infty]
    exact fun m ↦ contDiffAt_of_eventually_apply_eq_nat m hs
      (hf.of_le (by simp)) hg hΘ
  | coe n => exact contDiffAt_of_eventually_apply_eq_nat n hs hf hg hΘ

/-- If `f` is `C^n` on an open set, the totalized composition operator
`h ↦ mkD (f ∘ h) default` is `C^n` at every continuous map whose range lies in that set.
The codomain universe must be at least the domain universe, as in
`contDiffAt_of_eventually_apply_eq`. -/
theorem contDiffAt_mkD_comp (n : ℕ∞) {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn 𝕜 (n : ℕ∞ω) f s) {g : C(K, E)} (hg : ∀ t, g t ∈ s)
    (default : C(K, F)) :
    ContDiffAt 𝕜 (n : ℕ∞ω) (fun h : C(K, E) ↦ mkD (fun t ↦ f (h t)) default) g := by
  apply contDiffAt_of_eventually_apply_eq n hs hf hg
  filter_upwards [eventually_mapsTo isCompact_univ hs (fun t _ ↦ hg t)] with h hh t
  exact mkD_apply_of_continuous
    (hf.continuousOn.comp_continuous h.continuous (fun t ↦ hh (mem_univ t)))

/-- Pointwise postcomposition by a `C¹` map is Fréchet differentiable. Its derivative applies
the derivative of the original map pointwise along the input function. -/
theorem hasFDerivAt_postcomp (f : C(E, F)) (hf : ContDiff 𝕜 1 f) (g : C(K, E)) :
    HasFDerivAt (fun h : C(K, E) ↦ f.comp h)
      (applyContinuousLinearMap
        ((⟨fderiv 𝕜 f, hf.continuous_fderiv one_ne_zero⟩ : C(E, E →L[𝕜] F)).comp g)) g := by
  -- `ContinuousMap.comp` unfolds to pointwise composition, so its derivative map is the
  -- bundled map along `g` supplied by the local superposition theorem.
  exact hasFDerivAt_of_eventually_apply_eq isOpen_univ hf.contDiffOn
    (fun _ ↦ mem_univ _) (.of_forall fun _ _ ↦ rfl)

/-- Pointwise postcomposition by a `C^n` map is `C^n` on a compact-domain continuous-map space,
for every finite or infinite differentiability order `n`. The codomain universe must be at
least the domain universe, as in `contDiffAt_of_eventually_apply_eq`. -/
theorem contDiff_postcomp (n : ℕ∞) (f : C(E, F)) (hf : ContDiff 𝕜 (n : ℕ∞ω) f) :
    ContDiff 𝕜 (n : ℕ∞ω) (fun g : C(K, E) ↦ f.comp g) := by
  exact contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_of_eventually_apply_eq n
    isOpen_univ hf.contDiffOn (fun _ ↦ mem_univ _) (.of_forall fun _ _ ↦ rfl)

end ContinuousMap
