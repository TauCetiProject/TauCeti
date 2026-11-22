/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.DilationPerturbation
import TauCeti.Geometry.Manifold.Flow.NormedSpace
import TauCeti.Geometry.Manifold.Flow.Straightening
import TauCeti.LinearAlgebra.Eigenspace.Smul
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# Making every cover of a closed orbit on a manifold nondegenerate

Let `v` be a vector field on a smooth Hausdorff manifold `M` modelled on a finite-dimensional real
normed space `E`, with a closed orbit through `p` of least period `T₀ > 0`. This file perturbs `v`
near `p` so that, for all but countably many values of the perturbation parameter, the closed
orbit and all its covers become nondegenerate. It is the flow-box perturbation step of the
Kupka–Smale theorem for closed orbits on a manifold.

**The chart.** Since the orbit is not a rest point, `v p ≠ 0`. For a smooth field the flow-box
theorem (`TauCeti.exists_chart_mfderiv_eq_const`) gives a chart `e` of the smooth maximal atlas,
centred at `p`, in which `v` is a constant field `u ≠ 0`. In this chart the orbit starts along the
axis `ℝ • u`.

**The perturbation.** In the chart, the flow-box dilation field `W_E` of
`TauCeti.exists_contDiff_flowOf_const_add_smul_axis` is supported near a short segment of the
axis, away from the chart image of the rest of the orbit, and for every `a` the flow of
`u + a • W_E` dilates the directions transverse to the axis by `exp a`. Its pullback by the chart,
extended by zero, is a smooth field `W` on `M` with compact support near `p`, vanishing along the
orbit. Near the segment of the orbit through the chart, `v + a • W` is the pullback of
`u + a • W_E`, so its flow is read in the chart through the inverse chart
(`TauCeti.eventually_apply_flowOf_of_mfderiv_eq`), and its time-`σ` map at `p` is that of `v`
composed with the transverse dilation by `exp a`, conjugated by the chart. Off the support of `W`
the two fields agree, so by `TauCeti.returnDerivative_eq_smul_of_eqOn_compl`:

* the closed orbit of `v` through `p` is a closed orbit of every `v + a • W`, of the same period;
* the linearized return map of every section `{g = g p}` transverse to `v` is multiplied by
  `exp a`.

This needs `v` only `C¹`, given a smooth chart in which `v` is constant near `p`
(`TauCeti.exists_contMDiff_returnDerivative_add_smul_eq_exp_smul_of_chart`). For a smooth field the
flow-box chart is smooth (`TauCeti.exists_contMDiff_returnDerivative_add_smul_eq_exp_smul`); for a
`C^k` field it is only `C^k`, and the pulled-back perturbation loses a derivative. For a field on
`E` that is already constant near `0`, the identity chart is such a chart
(`TauCeti.exists_contDiff_returnDerivative_add_smul_eq_exp_smul`).

**Nondegeneracy of every cover.** The linearized return map at time `m * T₀` is the `m`-th power of
the one at time `T₀` (`TauCeti.returnDerivative_natCast_mul`), and by
`Module.End.countable_setOf_exists_hasEigenvalue_one_pow_smul` only countably many `a` give a
power of `exp a • DP` the eigenvalue `1`. For all other `a` the closed orbit of `v + a • W` and all
its covers are nondegenerate. The resonant case is included: for `DP = -1` the orbit itself is
nondegenerate but its double cover is not, while the rescalings `exp a • DP` with `a ≠ 0` have no
power with the eigenvalue `1`.

## Main results

* `TauCeti.exists_contMDiff_returnDerivative_add_smul_eq_exp_smul_of_chart`: for a `C¹` field
  that is constant near `p` in a smooth chart, a smooth field `W`, vanishing outside a compact
  subset of a given neighbourhood of `p` and along the orbit, such that `v + a • W` keeps the
  closed orbit and has linearized return map `exp a • DP`.
* `TauCeti.exists_contMDiff_returnDerivative_add_smul_eq_exp_smul`: the same for a smooth field.
* `TauCeti.exists_contMDiff_countable_setOf_hasEigenvalue_one_pow`: for a smooth field and all but
  countably many `a`, no positive power of the linearized return map of `v + a • W` has the
  eigenvalue `1`.
* `TauCeti.exists_contDiff_returnDerivative_add_smul_eq_exp_smul`,
  `TauCeti.exists_contDiff_countable_setOf_hasEigenvalue_one_pow`: the same two statements for a
  `C¹` field on `E` constant near `0`.

## References

* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2 (local perturbations of closed orbits in flow boxes).
* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §§3–4
  (the Kupka–Smale theorem).
-/

public section

noncomputable section

open Filter Function Metric Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {T₀ : ℝ} {p : M}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- A short initial segment `[0, σ] • u` of the axis, with `σ < T₀`, lies in a given ball around
`0`. -/
private theorem exists_forall_smul_mem_ball {u : E} {r : ℝ} (hr : 0 < r) (hT₀ : 0 < T₀) :
    ∃ σ, 0 < σ ∧ σ < T₀ ∧ ∀ τ ∈ Icc 0 σ, τ • u ∈ ball (0 : E) r := by
  refine ⟨min (r / (2 * (‖u‖ + 1))) (T₀ / 2), lt_min (by positivity) (by positivity),
    (min_le_right _ _).trans_lt (by linarith), fun τ hτ ↦ ?_⟩
  rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hτ.1]
  calc τ * ‖u‖ ≤ r / (2 * (‖u‖ + 1)) * (‖u‖ + 1) := by
        gcongr
        · exact hτ.2.trans (min_le_left _ _)
        · linarith
    _ = r / 2 := by field_simp
    _ < r := by linarith

omit [T2Space M] in
/-- A flow-box chart centred at a point where a smooth field does not vanish: a chart of the
smooth maximal atlas sending `p` to `0`, in which `v` is a constant field `u`. -/
private theorem exists_chart_mfderiv_eq_const_of_ne_zero
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hvp : v p ≠ 0) :
    ∃ (e : OpenPartialHomeomorph M E) (u : E), e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      p ∈ e.source ∧ e p = 0 ∧ ∀ y ∈ e.source, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y (v y) = u := by
  obtain ⟨e, u, he, hpe, -, heu⟩ := exists_chart_mfderiv_eq_const (I := 𝓘(ℝ, E)) (m := ⊤)
    (n := ∞) le_top (by simp) (BoundarylessManifold.isInteriorPoint) hv.contMDiffOn
    univ_mem hvp
  -- Translate the chart so that it sends `p` to `0`; this does not change its derivative.
  have hcoe : (e.transHomeomorph (Homeomorph.addRight (-e p)) : M → E) =
      (fun z ↦ z + -e p) ∘ e :=
    rfl
  refine ⟨e.transHomeomorph (Homeomorph.addRight (-e p)), u, ?_, hpe, by simp [hcoe],
    fun y hy ↦ ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
    refine trans_mem_maximalAtlas_of_contDiffAt he (fun _ _ ↦ ?_) fun _ _ ↦ ?_
    · simp only [Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_addRight]
      fun_prop
    · simp only [← Homeomorph.symm_toOpenPartialHomeomorph,
        Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.addRight_symm,
        Homeomorph.coe_addRight]
      fun_prop
  · have hy' : y ∈ e.source := hy
    have ht : HasFDerivAt (fun z : E ↦ z + -e p) (ContinuousLinearMap.id ℝ E) (e y) :=
      (hasFDerivAt_id _).add_const _
    have hd := ht.hasMFDerivAt.comp y
      (mdifferentiableAt_of_mem_maximalAtlas
        (IsManifold.maximalAtlas_subset_of_le (by simp) he) hy').hasMFDerivAt
    rw [hcoe, hd.mfderiv]
    have h := heu y hy'
    simp only [modelWithCornersSelf_coe, Function.id_comp] at h
    -- The translation has the identity as derivative.
    exact h

variable {e : OpenPartialHomeomorph M E}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- A chart of the `C¹` maximal atlas and its inverse are differentiable on their domains. -/
private theorem mdifferentiable_of_mem_maximalAtlas
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
  ⟨fun _ hy ↦ (mdifferentiableAt_of_mem_maximalAtlas he hy).mdifferentiableWithinAt,
    fun _ hz ↦ (mdifferentiableAt_symm_of_mem_maximalAtlas he hz).mdifferentiableWithinAt⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- The derivative of the inverse of a chart inverts that of the chart. -/
private theorem mfderiv_symm_apply_mfderiv (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    {y : M} (hy : y ∈ e.source) (w : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y w) = w := by
  have hmd := mdifferentiable_of_mem_maximalAtlas he
  exact ContinuousLinearMap.ext_iff.1 (hmd.symm_comp_deriv hy) w

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- The derivative of a chart inverts that of the inverse of the chart. -/
private theorem mfderiv_apply_mfderiv_symm (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    {y : M} (hy : y ∈ e.source) (w : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e y) w) = w := by
  have hmd := mdifferentiable_of_mem_maximalAtlas he
  have h := ContinuousLinearMap.ext_iff.1 (hmd.comp_symm_deriv (e.map_source hy)) w
  rw [e.left_inv hy] at h
  exact h

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- The derivative of the inverse of a chart, applied to a field `V` on the model space, is the
pullback of `V` by the chart, read at the inverse image. -/
private theorem mfderiv_symm_apply_eq_mpullback
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (V : (z : E) → TangentSpace 𝓘(ℝ, E) z)
    {z : E} (hz : z ∈ e.target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z (V z) =
      VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V (e.symm z) := by
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ e.source, e y = z := ⟨e.symm z, e.map_target hz, e.right_inv hz⟩
  rw [VectorField.mpullback_apply, e.left_inv hy,
    ← mfderiv_symm_apply_mfderiv he hy ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y).inverse (V (e y))),
    (isInvertible_mfderiv_chart he hy).self_apply_inverse]
  rfl

/-- The pullback by a chart of a smooth field `V` on the model space, compactly supported in the
chart target, extended by zero: a smooth field on `M`, equal to the pullback on the chart source
and vanishing off the inverse image of the support of `V`. -/
private theorem exists_contMDiff_eq_mpullback (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {V : E → E} (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (hVt : tsupport V ⊆ e.target) :
    ∃ W : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ y ∈ e.source, W y = VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) ∧
      ∀ y ∉ e.symm '' tsupport V, W y = 0 := by
  classical
  set W : (x : M) → TangentSpace 𝓘(ℝ, E) x := fun y ↦
    if y ∈ e.source then VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y else 0
  have hK : IsCompact (e.symm '' tsupport V) :=
    hVc.isCompact.image_of_continuousOn (e.continuousOn_symm.mono hVt)
  have hW0 : ∀ y ∉ e.symm '' tsupport V, W y = 0 := by
    intro y hy
    by_cases hys : y ∈ e.source
    · have hVy : V (e y) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
        hy ⟨e y, h, e.left_inv hys⟩
      simp only [W, hys, ite_true]
      -- The pullback is `(de_y)⁻¹ (V (e y))` by definition.
      exact (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y).inverse hVy).trans
        (ContinuousLinearMap.map_zero _)
    · simp [W, hys]
  refine ⟨W, fun y ↦ ?_, fun y hy ↦ ite_eq_left_iff.2 fun h ↦ (h hy).elim, hW0⟩
  by_cases hys : y ∈ e.source
  · -- On the chart source the field is the pullback, which is smooth there.
    refine ((contMDiffOn_mpullback he hV.contDiffOn).contMDiffAt
      (e.open_source.mem_nhds hys)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_source.mem_nhds hys] with y' hy'
    simp [W, hy']
  · -- Off the chart source the field vanishes near `y`, off the compact image of the support.
    have hyK : y ∉ e.symm '' tsupport V := fun ⟨z, hz, hzy⟩ ↦
      hys (hzy ▸ e.map_target (hVt hz))
    refine (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, E) : M → Type _)
      y).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hyK] with y' hy'
    simp [hW0 y' hy', Bundle.zeroSection]

/-- **Flows read through the inverse of a chart.** Let `e` be a chart, and let a field `V` on the
model space be carried to the field `w` on `M` by the inverse chart on an open set `U` of the
chart target. If the flow of `V` from `0` runs along the axis segment `[0, σ] • u` inside `U`, with
time-`σ` map of derivative `L` at `0`, then the flow of `w` from `e.symm 0` runs along the inverse
chart image of the segment, and its time-`σ` map has derivative `L` conjugated by the chart. -/
private theorem mfderiv_flowOf_eq_comp_of_chart (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    {w : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {V : E → E}
    (hV : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun z : E ↦ (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ e.target)
    (hVw : ∀ z ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z (V z) = w (e.symm z)) {u : E} {σ : ℝ}
    (hσ : 0 ≤ σ) (haxis : ∀ t ∈ Icc 0 σ, (t, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) V ∧
      flowOf (I := 𝓘(ℝ, E)) V t 0 = t • u)
    (hU0 : ∀ t ∈ Icc 0 σ, t • u ∈ U) {L : E →L[ℝ] E}
    (hL : HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) V σ) L 0) :
    (σ, e.symm 0) ∈ flowDomain w ∧ flowOf w σ (e.symm 0) = e.symm (σ • u) ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (flowOf w σ) (e.symm 0) =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (σ • u)).comp
          (L.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e.symm 0))) := by
  have hσσ : σ ∈ Icc 0 σ := ⟨hσ, le_rfl⟩
  have h0t : (0 : E) ∈ e.target := hUt (by simpa using hU0 0 ⟨le_rfl, hσ⟩)
  have hps : e.symm 0 ∈ e.source := e.map_target h0t
  have hev := eventually_apply_flowOf_of_mfderiv_eq hV hw hU
    (fun z hz ↦ mdifferentiableAt_symm_of_mem_maximalAtlas he (hUt hz)) hVw (haxis σ hσσ).1
    fun s hs ↦ by
      rw [uIcc_of_le hσ] at hs
      dsimp only
      rw [(haxis s hs).2]
      exact hU0 s hs
  obtain ⟨hdom, hval⟩ := hev.self_of_nhds
  rw [(haxis σ hσσ).2] at hval
  -- Near `e.symm 0`, the time-`σ` map of `w` is the conjugate of that of `V` by the chart.
  have hloc : flowOf w σ =ᶠ[𝓝 (e.symm 0)] e.symm ∘ flowOf (I := 𝓘(ℝ, E)) V σ ∘ e := by
    have hte : Tendsto (fun y ↦ (σ, e y)) (𝓝 (e.symm 0)) (𝓝 (σ, (0 : E))) := by
      have h := (e.continuousAt hps).tendsto
      rw [e.right_inv h0t] at h
      exact tendsto_const_nhds.prodMk_nhds h
    filter_upwards [hte.eventually hev, e.open_source.mem_nhds hps] with y hy hys
    rw [comp_apply, comp_apply, hy.2, e.left_inv hys]
  have hA := (mdifferentiableAt_of_mem_maximalAtlas he hps).hasMFDerivAt
  have hF : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (flowOf (I := 𝓘(ℝ, E)) V σ) (e (e.symm 0)) L := by
    rw [e.right_inv h0t]
    exact hL.hasMFDerivAt
  have hB : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm
      (flowOf (I := 𝓘(ℝ, E)) V σ (e (e.symm 0))) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (σ • u)) := by
    rw [e.right_inv h0t, (haxis σ hσσ).2]
    exact (mdifferentiableAt_symm_of_mem_maximalAtlas he (hUt (hU0 σ hσσ))).hasMFDerivAt
  exact ⟨hdom, hval.symm, ((hB.comp (e.symm 0) (hF.comp (e.symm 0) hA)).congr_of_eventuallyEq
    hloc).mfderiv⟩

/-- **The perturbing field of a closed orbit, in a flow-box chart.** Let the orbit of `p` under
`v`, of least period `T₀`, run along the inverse chart image of the axis segment `[0, σ] • u`,
inside a ball in the chart target. The flow-box dilation field `W_E` of the constant field `u`,
supported in the ball and away from the chart image of the rest of the orbit, pulls back to a
smooth field `W` on `M` vanishing off the compact inverse chart image `K` of the support of `W_E`,
which the rest of the orbit avoids. For every `a` the flow of `u + a • W_E` runs along the axis, and
for `t ≥ 2 σ / 3` its time-`t` map has derivative `L a` at `0`, where `L 0 = 1` and `L a` acts as
`exp a` modulo the axis `ℝ ∙ u`. -/
private theorem exists_flowBox_dilation_field
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf v t p ≠ p) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {u : E} (hu : u ≠ 0) {r σ : ℝ} (hσ : 0 < σ) (hrt : ball (0 : E) r ⊆ e.target)
    (hball : ∀ τ ∈ Icc 0 σ, τ • u ∈ ball (0 : E) r)
    (haxis : ∀ t ∈ Icc 0 σ, flowOf v t p = e.symm (t • u)) :
    ∃ (L : ℝ → E →L[ℝ] E) (WE : E → E) (W : (x : M) → TangentSpace 𝓘(ℝ, E) x),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      IsCompact (e.symm '' tsupport WE) ∧ tsupport WE ⊆ ball 0 r ∧
      (∀ x ∉ e.symm '' tsupport WE, W x = 0) ∧
      (∀ t ∈ Icc σ T₀, flowOf v t p ∉ e.symm '' tsupport WE) ∧
      (∀ z ∈ e.target, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z (WE z) = W (e.symm z)) ∧
      (∀ s : ℝ, WE (s • u) = 0) ∧ ContDiff ℝ ∞ WE ∧ L 0 = 1 ∧
      (∀ a η, L a η - Real.exp a • η ∈ ℝ ∙ u) ∧ ∀ a t : ℝ,
        (t, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) (fun z ↦ u + a • WE z) ∧
        flowOf (I := 𝓘(ℝ, E)) (fun z ↦ u + a • WE z) t 0 = t • u ∧
        (2 * σ / 3 ≤ t →
          HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) (fun z ↦ u + a • WE z) t) (L a) 0) := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  -- The rest of the orbit, the points at the times of `[σ, T₀]`, is compact and avoids the
  -- inverse chart image of the segment `[σ / 3, 2 σ / 3] • u`, since the period is least.
  set R : Set M := (fun t ↦ flowOf v t p) '' Icc σ T₀
  have hR : IsCompact R :=
    isCompact_Icc.image_of_continuousOn ((isMIntegralCurveOn_flowOf hv p).continuousOn.mono
      fun t ht ↦ uIcc_subset_setOf_mem_flowDomain hP (Icc_subset_uIcc ⟨hσ.le.trans ht.1, ht.2⟩))
  have hRu : ∀ s ∈ Icc (σ / 3) (2 * σ / 3), e.symm (s • u) ∉ R := by
    rintro s hs ⟨t, ht, hst⟩
    refine flowOf_ne_flowOf_of_lt (s := s) (t := t) hv hP hp hmin (by linarith [hs.1])
      (by linarith [hs.2, ht.1]) ht.2 ?_
    rw [haxis s ⟨by linarith [hs.1], by linarith [hs.2]⟩]
    exact hst.symm
  have hseg (s : ℝ) (hs : s ∈ Icc (σ / 3) (2 * σ / 3)) : s ∈ Icc 0 σ :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨ℓ, WE, -, hWE, hWEc, hWEΩ, hWEaxis, hWEa⟩ :=
    exists_contDiff_flowOf_const_add_smul_axis hu (by positivity : (0 : ℝ) ≤ σ / 3)
      (by linarith : σ / 3 < 2 * σ / 3)
      (isOpen_ball.inter (e.continuousOn_symm.isOpen_inter_preimage e.open_target
        hR.isClosed.isOpen_compl))
      fun s hs ↦ ⟨hball s (hseg s hs), hrt (hball s (hseg s hs)), hRu s hs⟩
  have hWEt : tsupport WE ⊆ e.target := fun z hz ↦ hrt (hWEΩ hz).1
  obtain ⟨W, hW, hWsrc, hW0⟩ := exists_contMDiff_eq_mpullback he hWE hWEc hWEt
  refine ⟨fun b ↦ 1 + (Real.exp b - 1) • (1 - ℓ.smulRight u), WE, W, hW,
    hWEc.isCompact.image_of_continuousOn (e.continuousOn_symm.mono hWEt),
    fun z hz ↦ (hWEΩ hz).1, hW0, ?_, fun z hz ↦ ?_, hWEaxis, hWE, by simp,
    fun a η ↦ ?_, hWEa⟩
  · rintro t ht ⟨z, hz, hzt⟩
    exact (hWEΩ hz).2.2 (hzt ▸ ⟨t, ht, rfl⟩)
  · rw [hWsrc _ (e.map_target hz), mfderiv_symm_apply_eq_mpullback he1 WE hz]
  · -- The dilation acts as `exp a` modulo the axis `ℝ ∙ u`.
    refine Submodule.mem_span_singleton.2 ⟨(1 - Real.exp a) * ℓ η, ?_⟩
    simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self]
    module

/-- **The return maps, read in a chart.** Let `e` be a chart sending `p` to `0`, let `u` be the
chart image of `v p`, and let the time-`σ` maps of `w` and `v` at `p` have derivatives `L` and the
identity, conjugated by the chart, where `L` acts as `c` modulo `ℝ ∙ u`. If `w` agrees with `v` off
a closed set avoided by the orbit of `p` from time `σ` to the period `T₀`, then `p` is a closed
orbit of `w` of the same period, with `c` times the linearized return maps of `v`. -/
private theorem returnDerivative_eq_smul_of_mfderiv_flowOf_eq_comp
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (hpe : p ∈ e.source) (hep : e p = 0)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p) {σ : ℝ} (hσ : 0 ≤ σ) (hσT : σ ≤ T₀)
    {w : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hwp : w p = v p) (hσw : (σ, p) ∈ flowDomain w) (hσvw : flowOf w σ p = flowOf v σ p)
    {u q : E} (hu : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm 0 u = v p) {c : ℝ} {L : E →L[ℝ] E}
    (hL : ∀ η, L η - c • η ∈ ℝ ∙ u)
    (hder : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (flowOf w σ) p =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm q).comp (L.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e p)))
    (hder₀ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (flowOf v σ) p =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm q).comp
        ((1 : E →L[ℝ] E).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e p)))
    {S : Set M} (hS : IsClosed S) (hwv : EqOn w v Sᶜ) (hSv : ∀ t ∈ Icc σ T₀, flowOf v t p ∉ S) :
    (T₀, p) ∈ flowDomain w ∧ flowOf w T₀ p = p ∧
      ∀ g : M → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 g p → mvfderiv 𝓘(ℝ, E) g p (v p) ≠ 0 →
        returnDerivative w g T₀ p = c • returnDerivative v g T₀ p := by
  set A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e p
  set A' : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm 0
  have hA'A (ξ : E) : A' (A ξ) = ξ := by
    have h := mfderiv_symm_apply_mfderiv he hpe ξ
    rwa [hep] at h
  have hAA' (η : E) : A (A' η) = η := by
    have h := mfderiv_apply_mfderiv_symm he hpe η
    rwa [hep] at h
  -- The monodromy of `w` is that of `v` composed with `D = A⁻¹ L A`, which acts as `c` modulo the
  -- flow line `ℝ ∙ v p = A⁻¹ (ℝ ∙ u)`.
  refine returnDerivative_eq_smul_of_eqOn_compl hv hP hp hσ hσT hw hwp hσw hσvw
    (D := fun ξ ↦ A' (L (A ξ))) (fun ξ ↦ ?_) (fun ξ ↦ ?_) hS hwv hSv
  · obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.1 (hL (A ξ))
    have h (x : E) (hx : k • u = L (A x) - c • A x) : k • A' u = A' (L (A x)) - c • x := by
      rw [← A'.map_smul, hx, A'.map_sub, A'.map_smul, hA'A]
    refine Submodule.mem_span_singleton.2 ⟨k, ?_⟩
    rw [← hu]
    exact h ξ hk
  · rw [hder, hder₀]
    exact congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm q : E →L[ℝ] E) (hAA' (L (A ξ))).symm

/-- **An axis segment of the orbit in a flow-box chart.** In a chart sending `p` to `0` in which
`v` is the constant field `u` on a ball, `u ≠ 0` since the orbit of `p` is not a rest point, and the
orbit of `p` starts along the inverse chart image of an axis segment `[0, σ] • u`, with
`0 < σ < T₀`, inside a smaller ball whose inverse chart image lies in a given neighbourhood `N` of
`p`. -/
private theorem exists_axis_segment_of_chart
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hT₀ : 0 < T₀) (hmin : ∀ t ∈ Ioo 0 T₀, flowOf v t p ≠ p)
    (he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (hpe : p ∈ e.source) (hep : e p = 0)
    {u : E} {r : ℝ} (hr : 0 < r) (hrt : ball (0 : E) r ⊆ e.target)
    (hvu : ∀ z ∈ ball (0 : E) r, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z u = v (e.symm z))
    {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ r' σ : ℝ, u ≠ 0 ∧ ball (0 : E) r' ⊆ ball 0 r ∧ (∀ z ∈ ball (0 : E) r', e.symm z ∈ N) ∧
      0 < σ ∧ σ < T₀ ∧ (∀ τ ∈ Icc 0 σ, τ • u ∈ ball (0 : E) r') ∧
      ∀ t ∈ Icc 0 σ, (t, p) ∈ flowDomain v ∧ flowOf v t p = e.symm (t • u) := by
  have hsymm0 : e.symm 0 = p := hep ▸ e.left_inv hpe
  have h0t : (0 : E) ∈ e.target := hep ▸ e.map_source hpe
  -- The orbit is not a rest point, so `u ≠ 0`.
  have hu : u ≠ 0 := by
    rintro rfl
    have h0 : v p = 0 := by
      rw [← hsymm0, ← hvu 0 (mem_ball_self hr)]
      exact ContinuousLinearMap.map_zero _
    exact hmin (T₀ / 2) ⟨by positivity, by linarith⟩
      (flowOf_eq_of_isMIntegralCurve hv (isMIntegralCurve_const h0) (T₀ / 2))
  -- A smaller ball whose inverse chart image lies in `N`, and an axis segment inside it.
  obtain ⟨r', hr', hr'N⟩ := Metric.mem_nhds_iff.1 (inter_mem (ball_mem_nhds (0 : E) hr)
    ((e.continuousAt_symm h0t).preimage_mem_nhds (hsymm0.symm ▸ hN)))
  have hr't : ball (0 : E) r' ⊆ e.target := fun z hz ↦ hrt (hr'N hz).1
  obtain ⟨σ, hσ, hσT, hball⟩ := exists_forall_smul_mem_ball (u := u) hr' hT₀
  have hconst := isCompleteVectorField_const u
  have hflow (t : ℝ) : flowOf (I := 𝓘(ℝ, E)) (fun _ : E ↦ u) t = fun x ↦ x + t • u :=
    funext (flowOf_const u t)
  -- Along the segment, the orbit of `v` is the inverse chart image of the axis.
  have hv_axis (t : ℝ) (ht : t ∈ Icc 0 σ) :
      (t, p) ∈ flowDomain v ∧ flowOf v t p = e.symm (t • u) := by
    have h := mfderiv_flowOf_eq_comp_of_chart he1 hv (V := fun _ ↦ u)
      (contMDiff_vectorSpace_iff_contDiff.2 contDiff_const) isOpen_ball hr't
      (fun z hz ↦ hvu z (hr'N hz).1) ht.1 (fun s _ ↦ ⟨hconst.mem_flowDomain _ _, by simp⟩)
      (fun s hs ↦ hball s ⟨hs.1, hs.2.trans ht.2⟩)
      (L := ContinuousLinearMap.id ℝ E) (by rw [hflow]; exact (hasFDerivAt_id (0 : E)).add_const _)
    rw [hsymm0] at h
    exact ⟨h.1, h.2.1⟩
  exact ⟨r', σ, hu, fun z hz ↦ (hr'N hz).1, fun z hz ↦ (hr'N hz).2, hσ, hσT, hball, hv_axis⟩

/-- **The flow-box dilation of a closed orbit, in a flow-box chart.** Let `v` be a `C¹` vector
field on `M` with a closed orbit through `p` of least period `T₀ > 0`, and let `e` be a chart of
the smooth maximal atlas sending `p` to `0`, in which `v` is a constant field `u` on a ball around
`0`. For every neighbourhood `N` of `p` there is a smooth field `W`, vanishing outside a compact
subset of `N` and along the orbit, such that for every `a` the closed orbit of `v` through `p` is a
closed orbit of `v + a • W` of the same period, and the linearized return map of every section
`{g = g p}` transverse to `v` is multiplied by `exp a`. -/
theorem exists_contMDiff_returnDerivative_add_smul_eq_exp_smul_of_chart
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hT₀ : 0 < T₀) (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf v t p ≠ p) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hpe : p ∈ e.source) (hep : e p = 0) {u : E} {r : ℝ} (hr : 0 < r)
    (hrt : ball (0 : E) r ⊆ e.target)
    (hvu : ∀ z ∈ ball (0 : E) r, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z u = v (e.symm z))
    {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ W : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∃ K, IsCompact K ∧ K ⊆ N ∧ ∀ x ∉ K, W x = 0) ∧
      (∀ t ∈ Icc 0 T₀, W (flowOf v t p) = 0) ∧
      ∀ a : ℝ, (T₀, p) ∈ flowDomain (v + a • W) ∧ flowOf (v + a • W) T₀ p = p ∧
        ∀ g : M → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 g p → mvfderiv 𝓘(ℝ, E) g p (v p) ≠ 0 →
          returnDerivative (v + a • W) g T₀ p = Real.exp a • returnDerivative v g T₀ p := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hsymm0 : e.symm 0 = p := hep ▸ e.left_inv hpe
  obtain ⟨r', σ, hu, hr'r, hr'N, hσ, hσT, hball, hv_axis⟩ :=
    exists_axis_segment_of_chart hv hT₀ hmin he1 hpe hep hr hrt hvu hN
  have hr't : ball (0 : E) r' ⊆ e.target := hr'r.trans hrt
  obtain ⟨L, WE, W, hW, hK, hWEr, hW0, hKR, hWrel, hWEaxis, hWE, hL0, hLa, hWEa⟩ :=
    exists_flowBox_dilation_field hv hP hp hmin he hu hσ hr't hball
      fun t ht ↦ (hv_axis t ht).2
  have horbit : ∀ t ∈ Icc 0 T₀, W (flowOf v t p) = 0 := by
    intro t ht
    rcases le_or_gt t σ with h | h
    · rw [(hv_axis t ⟨ht.1, h⟩).2, ← hWrel _ (hr't (hball t ⟨ht.1, h⟩))]
      exact (congrArg _ (hWEaxis t)).trans (ContinuousLinearMap.map_zero _)
    · exact hW0 _ (hKR t ⟨h.le, ht.2⟩)
  refine ⟨W, hW, ⟨_, hK, fun _ ⟨z, hz, hzy⟩ ↦ hzy ▸ hr'N z (hWEr hz), hW0⟩, horbit,
    fun a ↦ ?_⟩
  -- For every `b`, near the segment `v + b • W` is the pullback of `u + b • W_E`, whose time-`σ`
  -- map at `0` is the transverse dilation `L b` by `exp b`.
  have key (b : ℝ) := mfderiv_flowOf_eq_comp_of_chart he1 (w := v + b • W)
    (V := fun z ↦ u + b • WE z) (hv.add_section (hW.const_smul_section.of_le (by simp)))
    (contMDiff_vectorSpace_iff_contDiff.2 (contDiff_const.add ((hWE.of_le (by simp)).const_smul b)))
    isOpen_ball hr't (fun z hz ↦ by
      rw [Pi.add_apply, Pi.smul_apply, ← hvu z (hr'r hz), ← hWrel z (hr't hz)]
      exact (ContinuousLinearMap.map_add _ _ _).trans
        (congrArg _ (ContinuousLinearMap.map_smul _ _ _)))
    hσ.le (fun t _ ↦ ⟨(hWEa b t).1, (hWEa b t).2.1⟩) hball (L := L b)
    ((hWEa b σ).2.2 (by linarith))
  rw [hsymm0] at key
  obtain ⟨hdom, hval, hder⟩ := key a
  obtain ⟨-, hval₀, hder₀⟩ := key 0
  rw [zero_smul, add_zero] at hval₀ hder₀
  rw [hL0] at hder₀
  have hWp : W p = 0 := by
    have h := horbit 0 ⟨le_rfl, hT₀.le⟩
    rwa [flowOf_zero] at h
  have hu' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm 0 u = v p := by
    rw [hvu 0 (mem_ball_self hr), hsymm0]
  exact returnDerivative_eq_smul_of_mfderiv_flowOf_eq_comp he1 hpe hep hv hP hp hσ.le hσT.le
    (hv.add_section (hW.const_smul_section.of_le (by simp)))
    (by rw [Pi.add_apply, Pi.smul_apply, hWp, smul_zero, add_zero]) hdom
    (hval.trans hval₀.symm) hu' (hLa a) hder hder₀ hK.isClosed
    (fun x hx ↦ by rw [Pi.add_apply, Pi.smul_apply, hW0 x hx, smul_zero, add_zero]) hKR

/-- **The flow-box dilation of a closed orbit on a manifold.** Let `v` be a smooth vector field on
`M` with a closed orbit through `p` of least period `T₀ > 0`. For every neighbourhood `N` of `p`
there is a smooth field `W`, vanishing outside a compact subset of `N` and along the orbit, such
that for every `a` the closed orbit of `v` through `p` is a closed orbit of `v + a • W` of the same
period, and the linearized return map of every section `{g = g p}` transverse to `v` is multiplied
by `exp a`. -/
theorem exists_contMDiff_returnDerivative_add_smul_eq_exp_smul
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hT₀ : 0 < T₀) (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf v t p ≠ p) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ W : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∃ K, IsCompact K ∧ K ⊆ N ∧ ∀ x ∉ K, W x = 0) ∧
      (∀ t ∈ Icc 0 T₀, W (flowOf v t p) = 0) ∧
      ∀ a : ℝ, (T₀, p) ∈ flowDomain (v + a • W) ∧ flowOf (v + a • W) T₀ p = p ∧
        ∀ g : M → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 g p → mvfderiv 𝓘(ℝ, E) g p (v p) ≠ 0 →
          returnDerivative (v + a • W) g T₀ p = Real.exp a • returnDerivative v g T₀ p := by
  have hv1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) M)) := hv.of_le (by simp)
  -- The orbit is not a rest point, so `v p ≠ 0` and `v` is straightened by a chart centred at `p`.
  have hvp : v p ≠ 0 := fun h0 ↦ hmin (T₀ / 2) ⟨by positivity, by linarith⟩
    (flowOf_eq_of_isMIntegralCurve hv1 (isMIntegralCurve_const h0) (T₀ / 2))
  obtain ⟨e, u, he, hpe, hep, heu⟩ := exists_chart_mfderiv_eq_const_of_ne_zero hv hvp
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 e.open_target 0 (hep ▸ e.map_source hpe)
  refine exists_contMDiff_returnDerivative_add_smul_eq_exp_smul_of_chart hv1 hT₀ hP hp hmin he
    hpe hep (u := u) hr hrt (fun z hz ↦ ?_) hN
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ e.source, e y = z :=
    ⟨e.symm z, e.map_target (hrt hz), e.right_inv (hrt hz)⟩
  rw [e.left_inv hy, ← heu y hy]
  exact mfderiv_symm_apply_mfderiv (IsManifold.maximalAtlas_subset_of_le (by simp) he) hy (v y)

/-- **Every cover of a closed orbit on a manifold becomes nondegenerate under a flow-box
dilation.** Let `v` be a smooth vector field on `M` with a closed orbit through `p` of least period
`T₀ > 0`. For every neighbourhood `N` of `p` there is a smooth field `W`, vanishing outside a
compact subset of `N` and along the orbit, such that the closed orbit of `v` through `p` is a
closed orbit of every `v + a • W` of the same period and, for every section `{g = g p}` transverse
to `v`, only countably many `a` give a positive power of the linearized return map of `v + a • W`
the eigenvalue `1`. Since the linearized return map at time `m * T₀` is the `m`-th power of the one
at time `T₀` (`TauCeti.returnDerivative_natCast_mul`), for all other `a` the closed orbit and all
its covers are nondegenerate. -/
theorem exists_contMDiff_countable_setOf_hasEigenvalue_one_pow
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hT₀ : 0 < T₀) (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf v t p ≠ p) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ W : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∃ K, IsCompact K ∧ K ⊆ N ∧ ∀ x ∉ K, W x = 0) ∧
      (∀ t ∈ Icc 0 T₀, W (flowOf v t p) = 0) ∧
      (∀ a : ℝ, (T₀, p) ∈ flowDomain (v + a • W) ∧ flowOf (v + a • W) T₀ p = p) ∧
      ∀ g : M → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 g p → mvfderiv 𝓘(ℝ, E) g p (v p) ≠ 0 →
        {a : ℝ | ∃ m ≠ 0, (returnDerivative (v + a • W) g T₀ p ^ m).HasEigenvalue 1}.Countable := by
  obtain ⟨W, hW, hWK, hWorb, hWa⟩ :=
    exists_contMDiff_returnDerivative_add_smul_eq_exp_smul hv hT₀ hP hp hmin hN
  refine ⟨W, hW, hWK, hWorb, fun a ↦ ⟨(hWa a).1, (hWa a).2.1⟩, fun g hg hgv ↦ ?_⟩
  refine ((Module.End.countable_setOf_exists_hasEigenvalue_one_pow_smul
    (returnDerivative v g T₀ p)).preimage Real.exp_injective).mono fun a ha ↦ ?_
  rw [Set.mem_ofPred_eq, (hWa a).2.2 g hg hgv] at ha
  exact ha

section ModelSpace

/-- **The flow-box dilation of a closed orbit in a flow box of `E`.** Let `v` be a `C¹` field on
`E` with a closed orbit through `0` of least period `T₀ > 0`, equal to a constant field `u` near
`0`. For every neighbourhood `N` of `0` there is a smooth compactly supported field `W`, supported
in `N` and vanishing along the orbit, such that for every `a` the closed orbit of `v` through `0` is
a closed orbit of `v + a • W` of the same period, and the linearized return map of every section
`{g = g 0}` transverse to `v` is multiplied by `exp a`. -/
theorem exists_contDiff_returnDerivative_add_smul_eq_exp_smul {v : E → E} {u : E}
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun z : E ↦ (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hT₀ : 0 < T₀) (hP : (T₀, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) v)
    (hp : flowOf (I := 𝓘(ℝ, E)) v T₀ 0 = 0)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf (I := 𝓘(ℝ, E)) v t 0 ≠ 0)
    (hvu : ∀ᶠ z in 𝓝 0, v z = u) {N : Set E} (hN : N ∈ 𝓝 0) :
    ∃ W : E → E, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W ⊆ N ∧
      (∀ t ∈ Icc 0 T₀, W (flowOf (I := 𝓘(ℝ, E)) v t 0) = 0) ∧
      ∀ a : ℝ, (T₀, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) (v + a • W) ∧
        flowOf (I := 𝓘(ℝ, E)) (v + a • W) T₀ 0 = 0 ∧
        ∀ g : E → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 g 0 → mvfderiv 𝓘(ℝ, E) g 0 (v 0) ≠ 0 →
          returnDerivative (I := 𝓘(ℝ, E)) (v + a • W) g T₀ 0 =
            Real.exp a • returnDerivative (I := 𝓘(ℝ, E)) v g T₀ 0 := by
  -- In the identity chart of `E`, `v` is the constant field `u` on a ball around `0`.
  obtain ⟨r, hr, hrv⟩ := Metric.eventually_nhds_iff_ball.1 hvu
  obtain ⟨W, hW, ⟨K, hK, hKN, hW0⟩, horb, hWa⟩ :=
    exists_contMDiff_returnDerivative_add_smul_eq_exp_smul_of_chart (M := E)
      (e := OpenPartialHomeomorph.refl E) hv hT₀ hP hp hmin
      (StructureGroupoid.id_mem_maximalAtlas _) (mem_univ _) rfl (u := u) hr (subset_univ _)
      (fun z hz ↦ by
        -- The identity chart has the identity as derivative.
        have h : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (OpenPartialHomeomorph.refl E).symm z =
            ContinuousLinearMap.id ℝ E := mfderiv_id
        exact (congrArg (fun L : E →L[ℝ] E ↦ L u) h).trans (hrv z hz).symm) hN
  have hts : tsupport W ⊆ K :=
    closure_minimal (fun x hx ↦ by_contra fun h ↦ hx (hW0 x h)) hK.isClosed
  exact ⟨W, contMDiff_vectorSpace_iff_contDiff.1 hW,
    hK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKN, horb, hWa⟩

/-- **Every cover of a closed orbit becomes nondegenerate under a flow-box dilation.** Let `v` be
a `C¹` field on `E` with a closed orbit through `0` of least period `T₀ > 0`, equal to a constant
field `u` near `0`. For every neighbourhood `N` of `0` there is a smooth compactly supported
field `W`, supported in `N` and vanishing along the orbit, such that the closed orbit of `v`
through `0` is a closed orbit of every `v + a • W` of the same period and, for every section
`{g = g 0}` transverse to `v`, only countably many `a` give a positive power of the linearized
return map of `v + a • W` the eigenvalue `1`. -/
theorem exists_contDiff_countable_setOf_hasEigenvalue_one_pow {v : E → E} {u : E}
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun z : E ↦ (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hT₀ : 0 < T₀) (hP : (T₀, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) v)
    (hp : flowOf (I := 𝓘(ℝ, E)) v T₀ 0 = 0)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf (I := 𝓘(ℝ, E)) v t 0 ≠ 0)
    (hvu : ∀ᶠ z in 𝓝 0, v z = u) {N : Set E} (hN : N ∈ 𝓝 0) :
    ∃ W : E → E, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W ⊆ N ∧
      (∀ t ∈ Icc 0 T₀, W (flowOf (I := 𝓘(ℝ, E)) v t 0) = 0) ∧
      (∀ a : ℝ, (T₀, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) (v + a • W) ∧
        flowOf (I := 𝓘(ℝ, E)) (v + a • W) T₀ 0 = 0) ∧
      ∀ g : E → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 g 0 → mvfderiv 𝓘(ℝ, E) g 0 (v 0) ≠ 0 →
        {a : ℝ | ∃ m ≠ 0,
          (returnDerivative (I := 𝓘(ℝ, E)) (v + a • W) g T₀ 0 ^ m).HasEigenvalue 1}.Countable := by
  obtain ⟨W, hW, hWc, hWN, hWorb, hWa⟩ :=
    exists_contDiff_returnDerivative_add_smul_eq_exp_smul hv hT₀ hP hp hmin hvu hN
  refine ⟨W, hW, hWc, hWN, hWorb, fun a ↦ ⟨(hWa a).1, (hWa a).2.1⟩, fun g hg hgv ↦ ?_⟩
  refine ((Module.End.countable_setOf_exists_hasEigenvalue_one_pow_smul
    (returnDerivative (I := 𝓘(ℝ, E)) v g T₀ 0)).preimage Real.exp_injective).mono fun a ha ↦ ?_
  rw [Set.mem_ofPred_eq, (hWa a).2.2 g hg hgv] at ha
  exact ha

end ModelSpace

end TauCeti
