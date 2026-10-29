/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# Homogeneity of connected manifolds

For any two points `x` and `y` of a connected open subset `U` of a finite-dimensional
boundaryless manifold `M`, some diffeotopy of `M` which fixes every point outside a compact subset
of `U` carries `x` to `y`.
In particular the diffeomorphisms of a connected manifold isotopic to the identity act
transitively on it.

Near a point `x`, take a bump function `ρ` in a chart around `x` and, for a nearby point `y`, the
vector field `ρ • (y - x)` read in that chart. Extended by zero, it is a compactly supported
vector field on `M` whose flow line through `x` is the straight segment from `x` to `y` in the
chart, so its compactly supported flow diffeotopy moves `x` to `y`. Diffeotopies compose and
invert, and the points reachable in this way from a given point form an open and closed subset
of `U`.

This is the first step in comparing two ball embeddings in a connected manifold (the disc
theorem): it moves the centre of one ball to the centre of the other.

## Main results

* `TauCeti.exists_diffeotopy_final_apply_eq_of_isPreconnected`: a point of a preconnected
  open set `U` is carried to any other point of `U` by a diffeotopy fixing everything outside a
  compact subset of `U`.
* `TauCeti.exists_diffeotopy_final_apply_eq`: a point of a connected manifold is carried to any
  other point by a compactly supported diffeotopy.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, Homogeneity Lemma; the flow of a cut-off constant vector field is the one used
  there.
-/

public section

noncomputable section

open Set Filter Metric Topology VectorField
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-! ### Vector fields read in a chart -/

section ChartField

variable {x z : M} {w : (p : E) → TangentSpace 𝓘(ℝ, E) p}

/-- A vector field `w` on the model space, read in the extended chart at `x` and extended by zero
outside the chart domain. -/
private def chartField (x : M) (w : (p : E) → TangentSpace 𝓘(ℝ, E) p) (z : M) :
    TangentSpace I z :=
  letI := Classical.dec (z ∈ (extChartAt I x).source)
  if z ∈ (extChartAt I x).source then mpullback I 𝓘(ℝ, E) (extChartAt I x) w z else 0

private theorem chartField_of_mem (hz : z ∈ (extChartAt I x).source) :
    chartField (I := I) x w z = mpullback I 𝓘(ℝ, E) (extChartAt I x) w z := by
  simp only [chartField, hz, ↓reduceIte]

/-- If `w` vanishes outside `K ⊆ target`, the chart field vanishes outside the preimage of
`K`. -/
private theorem chartField_eq_zero {K : Set E}
    (hwK : ∀ p ∉ K, w p = 0) (hz : z ∉ (extChartAt I x).symm '' K) :
    chartField (I := I) x w z = 0 := by
  by_cases hs : z ∈ (extChartAt I x).source
  · have hK : extChartAt I x z ∉ K := fun h ↦ hz ⟨_, h, (extChartAt I x).left_inv hs⟩
    rw [chartField_of_mem hs, mpullback_apply, hwK _ hK, map_zero]
  · simp only [chartField, hs, ↓reduceIte]

variable [IsManifold I 1 M]

/-- Along a segment in the chart on which `w` is the constant `d`, the chart field is the image of
`d` under the derivative of the inverse chart. -/
private theorem chartField_extChartAt_symm {p : E} {d : TangentSpace 𝓘(ℝ, E) p}
    (hp : p ∈ (extChartAt I x).target) (hwp : w p = d) :
    chartField (I := I) x w ((extChartAt I x).symm p) =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) p d := by
  have hs := (extChartAt I x).map_target hp
  rw [chartField_of_mem hs, mpullback_apply, (isInvertible_mfderiv_extChartAt hs).inverse_apply_eq]
  have key : mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm p)
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) p d) = d :=
    DFunLike.congr_fun (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hp) d
  exact ((congrArg (fun a ↦ (w a : E)) ((extChartAt I x).right_inv hp)).trans hwp).trans key.symm

/-- A segment in a chart, along which `w` is the constant `d`, is an integral curve of the chart
field at every time at which it stays in an open set where `w = d`. -/
private theorem hasMFDerivAt_chartField {c d : E} {V : Set E}
    (hV : IsOpen V) (hVt : V ⊆ (extChartAt I x).target) (hwV : ∀ p ∈ V, w p = d) {t : ℝ}
    (ht : c + t • d ∈ V) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ (extChartAt I x).symm (c + s • d)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (chartField (I := I) x w ((extChartAt I x).symm (c + t • d)))) := by
  have hrange : range I ∈ 𝓝 (c + t • d) :=
    mem_of_superset (hV.mem_nhds ht) (hVt.trans (extChartAt_target_subset_range x))
  have hsymm :=
    (mdifferentiableWithinAt_extChartAt_symm (hVt ht)).hasMFDerivWithinAt.hasMFDerivAt hrange
  have hseg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ ↦ c + s • d) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight d) := by
    have h := ((hasDerivAt_id t).smul_const d).const_add c
    rw [one_smul] at h
    exact hasMFDerivAt_iff_hasFDerivAt.2 h
  have hder : (1 : ℝ →L[ℝ] ℝ).smulRight
      (chartField (I := I) x w ((extChartAt I x).symm (c + t • d))) =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (c + t • d)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight d) := by
    rw [chartField_extChartAt_symm (hVt ht) (hwV _ ht)]
    ext1
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
      one_smul]
    congr 1
    -- `smulRight` is evaluated in `E` rather than in the tangent space at `c + t • d`.
    exact (by simp : ((1 : ℝ →L[ℝ] ℝ).smulRight d) 1 = d).symm
  rw [hder]
  exact hsymm.comp t hseg

/-- The chart field of a `C^m` vector field supported in a compact subset of the chart target is
a `C^m` vector field on `M`, provided `M` is `C^(m + 1)`. -/
private theorem contMDiff_chartField [CompleteSpace E] [T2Space M] {n m : ℕ∞ω}
    [IsManifold I n M] (hmn : m + 1 ≤ n)
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent m (fun p ↦ (⟨p, w p⟩ : TangentBundle 𝓘(ℝ, E) E)))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x).target) (hwK : ∀ p ∉ K, w p = 0) :
    ContMDiff I I.tangent m (fun z ↦ (⟨z, chartField x w z⟩ : TangentBundle I M)) := by
  intro z
  by_cases hz : z ∈ (extChartAt I x).symm '' K
  · -- Near the support, the chart field is the pullback of `w` by the chart.
    obtain ⟨p, hp, rfl⟩ := hz
    have hs := (extChartAt I x).map_target (hKt hp)
    refine (ContMDiffAt.mpullback_vectorField_preimage (hw _)
      (contMDiffAt_extChartAt' (by rwa [← extChartAt_source (I := I)]))
      (isInvertible_mfderiv_extChartAt hs) hmn).congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_source_mem_nhds' hs] with y hy
    rw [chartField_of_mem hy]
  · -- Away from the compact support, the chart field is the zero section.
    have hL : IsClosed ((extChartAt I x).symm '' K) :=
      (hK.image_of_continuousOn ((continuousOn_extChartAt_symm x).mono hKt)).isClosed
    refine (Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _) z).congr_of_eventuallyEq ?_
    filter_upwards [hL.isOpen_compl.mem_nhds hz] with y hy
    rw [chartField_eq_zero hwK hy]
    rfl

end ChartField

/-! ### Homogeneity -/

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] {n : ℕ∞ω}
  [IsManifold I n M] {m : ℕ∞}

/-- Every point near `x` is reached from `x` by a diffeotopy fixing everything outside a compact
subset of a given open neighbourhood `U` of `x`. -/
private theorem eventually_exists_diffeotopy_final_apply_eq (hm : 1 ≤ m)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, ∃ (Φ : Diffeotopy I m M) (K : Set M), IsCompact K ∧ K ⊆ U ∧
      (∀ t, EqOn (fun z ↦ Φ (t, z)) id Kᶜ) ∧ Φ.final x = y := by
  have : IsManifold I m M := .of_le (le_self_add.trans hmn)
  have : IsManifold I 1 M := .of_le ((by exact_mod_cast hm : (1 : ℕ∞ω) ≤ m).trans
    (le_self_add.trans hmn))
  set e := extChartAt I x with he
  -- A ball around `e x` in the interior of the chart target whose preimage lies in `U`.
  have hW : IsOpen (interior e.target ∩ e.symm ⁻¹' U) :=
    ((continuousOn_extChartAt_symm x).mono interior_subset).isOpen_inter_preimage
      isOpen_interior hU
  have hxW : e x ∈ interior e.target ∩ e.symm ⁻¹' U :=
    ⟨(I.isInteriorPoint_iff).1 BoundarylessManifold.isInteriorPoint, by
      rwa [mem_preimage, he, extChartAt_to_inv]⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW (e x) hxW
  have hballt : ball (e x) r ⊆ e.target := fun p hp ↦ interior_subset (hrW hp).1
  filter_upwards [extChartAt_source_mem_nhds (I := I) x,
    (continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds (e x) (by positivity : 0 < r / 4))]
    with y hys hyr
  -- The vector field `ρ • d` in the chart, with `ρ = 1` on the ball of radius `r / 2`.
  set d : E := e y - e x with hd
  have hdr : ‖d‖ < r / 4 := by rwa [mem_preimage, mem_ball, dist_eq_norm] at hyr
  let ρ : ContDiffBump (e x) := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩
  let w : (p : E) → TangentSpace 𝓘(ℝ, E) p := fun p ↦ ρ p • d
  have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent m
      (fun p ↦ (⟨p, w p⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.2 (ρ.contDiff.smul contDiff_const)
  have hKr : closedBall (e x) (3 * r / 4) ⊆ ball (e x) r := closedBall_subset_ball (by linarith)
  have hwK : ∀ p ∉ closedBall (e x) (3 * r / 4), w p = 0 := fun p hp ↦ by
    have hρ : ρ p = 0 := Function.notMem_support.1 fun h ↦
      hp (ball_subset_closedBall (ρ.support_eq ▸ h))
    -- The zero of `TangentSpace 𝓘(ℝ, E) p` is the zero of `E` by definition.
    simp only [w, hρ, zero_smul]
    rfl
  have hwd : ∀ p ∈ ball (e x) (r / 2), w p = d := fun p hp ↦ by
    -- `TangentSpace 𝓘(ℝ, E) p` is `E` by definition.
    simp only [w, ρ.one_of_mem_closedBall (ball_subset_closedBall hp), one_smul]
    rfl
  have hv := contMDiff_chartField (I := I) hmn hw (isCompact_closedBall (e x) (3 * r / 4))
    (hKr.trans hballt) hwK
  have hL : IsCompact (e.symm '' closedBall (e x) (3 * r / 4)) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm x).mono (hKr.trans hballt))
  refine ⟨compactlySupportedFlowDiffeotopy hm hv hL (fun z hz ↦ chartField_eq_zero hwK hz) 1,
    _, hL, ?_, compactlySupportedFlowDiffeotopy_eqOn_compl hm hv hL _ 1, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hrW (hKr hp)).2
  -- The segment `s ↦ e.symm (e x + s • d)` is the flow line of `x`.
  have hseg : ∀ s ∈ Ioo (-2 : ℝ) 2, e x + s • d ∈ ball (e x) (r / 2) := fun s hs ↦ by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hs' : |s| < 2 := abs_lt.2 hs
    nlinarith [abs_nonneg s, norm_nonneg d]
  have hcurve : IsMIntegralCurveOn (fun s ↦ e.symm (e x + s • d)) (chartField x w)
      (Ioo (-2) 2) := fun s hs ↦
    (hasMFDerivAt_chartField isOpen_ball ((ball_subset_ball (by linarith)).trans hballt) hwd
      (hseg s hs)).hasMFDerivWithinAt
  have h1 := hcurve.eqOn_maximalIntegralCurve (x := x) (hv.of_le (by exact_mod_cast hm))
    (by norm_num) (by simp [he]) (by norm_num : (1 : ℝ) ∈ Ioo (-2) 2)
  rw [Diffeotopy.final_apply, compactlySupportedFlowDiffeotopy_apply]
  dsimp only
  rw [Set.Icc.coe_one, one_mul, h1]
  simp only [one_smul, hd, add_sub_cancel, e.left_inv hys]

/-- **Homogeneity lemma.** For two points `x` and `y` of a preconnected open subset `U` of a
finite-dimensional boundaryless manifold, some diffeotopy fixing everything outside a compact
subset of `U` has final map sending `x` to `y`. For a `C^n` manifold the diffeotopy is `C^m`
for every `m` with `1 ≤ m` and `m + 1 ≤ n`; in particular it is smooth on a smooth manifold. -/
theorem exists_diffeotopy_final_apply_eq_of_isPreconnected (hm : 1 ≤ m)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) {x y : M}
    (hx : x ∈ U) (hy : y ∈ U) :
    ∃ (Φ : Diffeotopy I m M) (K : Set M), IsCompact K ∧ K ⊆ U ∧
      (∀ t, EqOn (fun z ↦ Φ (t, z)) id Kᶜ) ∧ Φ.final x = y := by
  refine hUc.induction₂ _ (fun a ha ↦ nhdsWithin_le_nhds
    (eventually_exists_diffeotopy_final_apply_eq hm hmn hU ha)) ?_ ?_ hx hy
  · rintro a b c - - - ⟨Φ, K, hK, hKU, hΦK, hab⟩ ⟨Ψ, L, hL, hLU, hΨL, hbc⟩
    refine ⟨Φ.trans Ψ, K ∪ L, hK.union hL, union_subset hKU hLU, fun t z hz ↦ ?_, ?_⟩
    · rw [compl_union] at hz
      simp [hΦK t hz.1, hΨL t hz.2]
    · simp [hab, hbc]
  · rintro a b - - ⟨Φ, K, hK, hKU, hΦK, hab⟩
    refine ⟨Φ.symm, K, hK, hKU, fun t z hz ↦ Φ.symm_apply_eq_self_iff.2 (hΦK t hz), ?_⟩
    rw [Diffeotopy.final_symm, ← hab, Diffeomorph.symm_apply_apply]

/-- **Homogeneity lemma.** For two points `x` and `y` of a connected finite-dimensional
boundaryless manifold, some compactly supported diffeotopy has final map sending `x` to `y`.
For a `C^n` manifold the diffeotopy is `C^m` for every `m` with `1 ≤ m` and `m + 1 ≤ n`. -/
theorem exists_diffeotopy_final_apply_eq [PreconnectedSpace M] (hm : 1 ≤ m)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) (x y : M) :
    ∃ (Φ : Diffeotopy I m M) (K : Set M), IsCompact K ∧
      (∀ t, EqOn (fun z ↦ Φ (t, z)) id Kᶜ) ∧ Φ.final x = y := by
  obtain ⟨Φ, K, hK, -, hΦK, hxy⟩ :=
    exists_diffeotopy_final_apply_eq_of_isPreconnected (I := I) hm hmn isOpen_univ
      isPreconnected_univ (mem_univ x) (mem_univ y)
  exact ⟨Φ, K, hK, hΦK, hxy⟩

end TauCeti
