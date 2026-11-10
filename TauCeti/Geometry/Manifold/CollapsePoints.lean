/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homogeneity
public import TauCeti.Topology.Homotopy.Homotopic.Rel
import TauCeti.Geometry.Manifold.Diffeomorph.Extend

/-!
# Sending finitely many points of a manifold to a base point up to based homotopy

Let `M` be a preconnected Hausdorff `C^n` manifold, `n ≥ 2`, without boundary, modelled on a
finite-dimensional real normed space, and let `x₀ ∈ M`. For every finite set `S ⊆ M` there is a
continuous map `θ : M → M` which sends every point of `S` to `x₀` and is homotopic to the
identity relative to `x₀` (`Set.Finite.exists_homotopicRel_id_apply_eq`). No dimension hypothesis
is needed.

In Morse homology with local or differential graded coefficients (Barraud–Cornea), a trajectory
between two critical points `x` and `y` is a path from `x` to `y`; to read it as a loop at the base
point one joins the critical points to `x₀` by an embedded tree `T`, collapses `T` and returns to
`M` along a homotopy inverse of the collapse `M → M ⧸ T`. The composite is a self-map of `M`,
homotopic to the identity, sending every critical point to the image of the collapsed tree. A map
`θ` as above plays this role directly at the chosen base point: composing the paths with `θ` turns
them into loops at `x₀`, as `TauCeti.mooreLoopEvaluation` does. Since the homotopy from `θ` to the
identity fixes `x₀`, composing a loop at `x₀` with `θ` changes it only by a homotopy of loops
at `x₀`.

The proof has two steps.

* **Squashing a neighbourhood.** In the chart at `x₀`, the radial map that squashes a small ball
  about `x₀` to its centre, shrinks a larger ball onto itself and is the identity outside it,
  extends by the identity to a map `σ : M → M` homotopic to the identity relative to `x₀` and
  constant on a neighbourhood of `x₀` (`TauCeti.exists_homotopicRel_id_eventually_eq`).
* **Moving a point.** The points `y` admitting a map `θ ≃ id` relative to `x₀` with `θ y = x₀`
  form an open set, by composing with `σ`, and a closed one: a point `y ≠ x₀` is carried to every
  nearby point by a diffeotopy fixing `x₀` (`TauCeti.eventually_exists_diffeotopy_final_apply_eq`).
  On a preconnected manifold every point is such a `y`. For a finite set, compose these maps one
  point at a time.

## Main results

* `TauCeti.exists_homotopicRel_id_eventually_eq`: a self-map homotopic to the identity relative
  to `x₀` and constant equal to `x₀` near `x₀`.
* `Set.Finite.exists_homotopicRel_id_apply_eq`: a self-map homotopic to the identity relative to
  `x₀` sending a given finite set to `x₀`.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3.
-/

public section

noncomputable section

open Set Filter Metric Topology
open scoped Manifold ContDiff

namespace TauCeti

section Squash

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial squashing homotopy of `E` towards `c` at time `t`: the identity at `t = 0`, it
scales `v - c` by a factor in `[0, 1]`, which is `0` on `closedBall c (r / 4)` at time `1` and `1`
outside `ball c (r / 2)` at all times. -/
private def radialSquash (c : E) (r t : ℝ) (v : E) : E :=
  c + (1 - t * (1 - min 1 (max 0 (4 * ‖v - c‖ / r - 1)))) • (v - c)

private theorem continuous_radialSquash (c : E) (r : ℝ) :
    Continuous fun p : ℝ × E ↦ radialSquash c r p.1 p.2 := by
  unfold radialSquash
  fun_prop

private theorem radialSquash_zero (c : E) (r : ℝ) (v : E) : radialSquash c r 0 v = v := by
  simp [radialSquash]

private theorem radialSquash_self (c : E) (r t : ℝ) : radialSquash c r t c = c := by
  simp [radialSquash]

/-- Outside `ball c (r / 2)` the squashing homotopy is the identity. -/
private theorem radialSquash_of_le {c : E} {r : ℝ} (hr : 0 < r) (t : ℝ) {v : E}
    (hv : r / 2 ≤ ‖v - c‖) : radialSquash c r t v = v := by
  have : 1 ≤ 4 * ‖v - c‖ / r - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hr]
    linarith
  simp [radialSquash, max_eq_right (zero_le_one.trans this), min_eq_left this]

/-- At time `1` the squashing homotopy sends `closedBall c (r / 4)` to `c`. -/
private theorem radialSquash_one_of_le {c : E} {r : ℝ} (hr : 0 < r) {v : E}
    (hv : ‖v - c‖ ≤ r / 4) : radialSquash c r 1 v = c := by
  have : 4 * ‖v - c‖ / r - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hr]
    linarith
  simp [radialSquash, max_eq_left this]

/-- The squashing homotopy moves no point away from `c`. -/
private theorem norm_radialSquash_sub_le (c : E) (r : ℝ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (v : E) : ‖radialSquash c r t v - c‖ ≤ ‖v - c‖ := by
  set a := min 1 (max 0 (4 * ‖v - c‖ / r - 1))
  have ha₀ : 0 ≤ a := le_min zero_le_one (le_max_left _ _)
  have ha₁ : a ≤ 1 := min_le_left _ _
  have hk₀ : 0 ≤ 1 - t * (1 - a) := by nlinarith
  have hk₁ : 1 - t * (1 - a) ≤ 1 := by nlinarith
  rw [radialSquash, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hk₀]
  exact mul_le_of_le_one_left (norm_nonneg _) hk₁

variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ E]
  [BoundarylessManifold I M]

include I in
/-- **Squashing a neighbourhood of a point.** On a Hausdorff manifold without boundary modelled on a
finite-dimensional real normed space, some self-map `f` is homotopic to the identity relative to
`x₀` and sends a whole neighbourhood of `x₀` to `x₀`. -/
theorem exists_homotopicRel_id_eventually_eq (x₀ : M) :
    ∃ f : C(M, M), f.HomotopicRel (ContinuousMap.id M) {x₀} ∧ ∀ᶠ z in 𝓝 x₀, f z = x₀ := by
  set e := extChartAt I x₀
  set c := e x₀
  have hx₀ : x₀ ∈ e.source := mem_extChartAt_source x₀
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds
    (ModelWithCorners.isInteriorPoint_iff.1
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀))))
  have hKt : closedBall c (r / 2) ⊆ interior e.target :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrt
  have hc : e.symm c = x₀ := e.left_inv hx₀
  -- The squashing homotopy, read in the chart at `x₀` and extended by the identity.
  have hF : Continuous fun p : unitInterval × M ↦ chartExtend I (radialSquash c r p.1) x₀ p.2 :=
    contMDiff_zero_iff.1 <| contMDiff_chartExtend (I' := 𝓡∂ 1)
      (Φ := fun t : unitInterval ↦ radialSquash c r t)
      (contMDiff_zero_iff.2 ((continuous_radialSquash c r).comp
        (continuous_subtype_val.prodMap continuous_id)))
      (isCompact_closedBall c (r / 2)) hKt
      (fun t v hv ↦ by
        rw [mem_closedBall, dist_eq_norm] at hv ⊢
        exact (norm_radialSquash_sub_le c r t.2.1 t.2.2 v).trans hv)
      (fun t v hv ↦ radialSquash_of_le hr t (by
        rw [mem_closedBall, dist_eq_norm, not_le] at hv
        exact hv.le))
  refine ⟨⟨fun z ↦ chartExtend I (radialSquash c r 1) x₀ z,
    hF.comp (Continuous.prodMk_right (1 : unitInterval))⟩, ⟨ContinuousMap.HomotopyRel.symm
    { toFun p := chartExtend I (radialSquash c r p.1) x₀ p.2
      continuous_toFun := hF
      map_zero_left z := ?_
      map_one_left _ := rfl
      prop' t z hz := ?_ }⟩, ?_⟩
  · have h0 : radialSquash c r 0 = id := funext (radialSquash_zero c r)
    simp only [Icc.coe_zero, h0, chartExtend_id, id, ContinuousMap.id_apply]
  · rw [mem_singleton_iff.1 hz]
    change chartExtend I (radialSquash c r t) x₀ x₀ = x₀
    rw [chartExtend_of_mem hx₀, radialSquash_self, hc]
  · filter_upwards [(isOpen_extChartAt_preimage' x₀ isOpen_ball).mem_nhds
      (⟨hx₀, mem_ball_self (by positivity)⟩ : x₀ ∈ e.source ∩ e ⁻¹' ball c (r / 4))] with z hz
    rw [ContinuousMap.coe_mk, chartExtend_of_mem hz.1,
      radialSquash_one_of_le hr (by rw [← dist_eq_norm]; exact (mem_ball.1 hz.2).le), hc]

end Squash

section Collapse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I n M]

variable (I) in
include I in
/-- On a preconnected manifold, every point `y` is sent to `x₀` by some self-map homotopic to the
identity relative to `x₀`. -/
private theorem exists_homotopicRel_id_apply_eq_basePoint [PreconnectedSpace M] (hn : 2 ≤ n)
    (x₀ y : M) : ∃ θ : C(M, M), θ.HomotopicRel (ContinuousMap.id M) {x₀} ∧ θ y = x₀ := by
  set A := {y | ∃ θ : C(M, M), θ.HomotopicRel (ContinuousMap.id M) {x₀} ∧ θ y = x₀}
  have hx₀A : x₀ ∈ A := ⟨ContinuousMap.id M, .refl _, rfl⟩
  -- Composing with a map that squashes a neighbourhood of `x₀` shows that `A` is open.
  have hAo : IsOpen A := isOpen_iff_mem_nhds.2 fun y ⟨θ, hθ, hθy⟩ ↦ by
    obtain ⟨f, hf, hfx₀⟩ := exists_homotopicRel_id_eventually_eq I x₀
    have hfθ : (f.comp θ).HomotopicRel (ContinuousMap.id M) {x₀} := hf.comp_id hθ
    exact Filter.mem_of_superset (θ.continuous.continuousAt.preimage_mem_nhds
      (t := {z | f z = x₀}) (by rw [hθy]; exact hfx₀)) fun z hz ↦ ⟨f.comp θ, hfθ, hz⟩
  -- A point `y ≠ x₀` reaches every nearby point by a diffeotopy fixing `x₀`, so `A` is closed.
  have hAc : IsClosed A := isOpen_compl_iff.1 <| isOpen_iff_mem_nhds.2 fun y hy ↦ by
    have hyx₀ : y ∈ ({x₀}ᶜ : Set M) := fun h ↦ hy (mem_singleton_iff.1 h ▸ hx₀A)
    have hmn : ((1 : ℕ∞) : ℕ∞ω) + 1 ≤ n := le_of_eq_of_le (by norm_num) hn
    filter_upwards [eventually_exists_diffeotopy_final_apply_eq (I := I) (m := 1) le_rfl hmn
      isClosed_singleton.isOpen_compl hyx₀] with z hz hzA
    obtain ⟨D, K, -, hKU, hDK, hDy⟩ := hz
    obtain ⟨θ, hθ, hθz⟩ := hzA
    have hDf : D.toAmbientIsotopy.final.HomotopicRel (ContinuousMap.id M) {x₀} :=
      D.toAmbientIsotopy.final_homotopicRel_id fun t _ h ↦ by
        rw [mem_singleton_iff.1 h]
        exact (D.toAmbientIsotopy_apply (t, x₀)).trans (hDK t fun h ↦ hKU h rfl)
    refine hy ⟨θ.comp D.toAmbientIsotopy.final, hθ.comp_id hDf, ?_⟩
    · rw [ContinuousMap.comp_apply, Diffeotopy.toAmbientIsotopy_final_apply, hDy, hθz]
  exact eq_univ_iff_forall.1 (IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨x₀, hx₀A⟩) y

variable (I) in
include I in
/-- **Sending finitely many points to a base point.** Let `M` be a preconnected Hausdorff `C^n`
manifold, `n ≥ 2`, without boundary, modelled through `I` on a finite-dimensional real normed
space `E`. For every finite set `S ⊆ M` and every `x₀ ∈ M`, some self-map `θ` of `M`, homotopic
to the identity relative to `x₀`, sends every point of `S` to `x₀`. -/
theorem _root_.Set.Finite.exists_homotopicRel_id_apply_eq [PreconnectedSpace M] (hn : 2 ≤ n)
    {S : Set M} (hS : S.Finite) (x₀ : M) :
    ∃ θ : C(M, M), θ.HomotopicRel (ContinuousMap.id M) {x₀} ∧ ∀ s ∈ S, θ s = x₀ := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨ContinuousMap.id M, .refl _, by simp⟩
  | @insert a S _ _ ih =>
    obtain ⟨θ, hθ, hθS⟩ := ih
    obtain ⟨ψ, hψ, hψa⟩ := exists_homotopicRel_id_apply_eq_basePoint I hn x₀ (θ a)
    refine ⟨ψ.comp θ, ?_, ?_⟩
    · exact hψ.comp_id hθ
    · rintro s (rfl | hs)
      · exact hψa
      · rw [ContinuousMap.comp_apply, hθS s hs]
        exact hψ.mapsTo_self rfl

end Collapse

end TauCeti
