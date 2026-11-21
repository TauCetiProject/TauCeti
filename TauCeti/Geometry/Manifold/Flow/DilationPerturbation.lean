/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Monodromy
public import TauCeti.Geometry.Manifold.Flow.TransverseDilation
public import TauCeti.LinearAlgebra.Eigenspace.Smul
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Making every cover of a closed orbit nondegenerate by a flow-box dilation

Let `v` be a `C¹` vector field on a finite-dimensional real normed space `E` with a closed orbit
through `0` of least period `T₀ > 0`, and suppose that near `0` the field is a constant `u`: the
orbit runs through a flow box along the axis `ℝ • u`. This file perturbs `v` near a short segment
of the axis so that, for all but countably many values of the perturbation parameter, the closed
orbit and all its covers become nondegenerate.

**The perturbation.** Fix `ℓ` with `ℓ u = 1`. The transverse dilation fields of
`TauCeti.Geometry.Manifold.Flow.TransverseDilation` give a smooth field `Z` supported in a slab
`s₀ < ℓ z < s₁` and vanishing on the axis, such that `u + a • Z` dilates the directions of `ker ℓ`
by `exp a` across the slab. Cut off away from a compact segment of the axis, `W = χ • Z` is a
smooth compactly supported field, supported in any prescribed neighbourhood of `0`, and vanishing
along the closed orbit (`TauCeti.exists_contDiff_returnDerivative_add_smul_eq_exp_smul`):

* the closed orbit of `v` through `0` is a closed orbit of every `v + a • W`, with the same period;
* the monodromy of `v + a • W` is that of `v` composed with `w ↦ w + (exp a - 1) • (w - ℓ w • u)`,
  which is multiplication by `exp a` modulo the flow line `ℝ ∙ u`. Hence the linearized return map
  of every transverse section is multiplied by `exp a`
  (`TauCeti.returnDerivative_eq_smul_of_mfderiv_flowOf_eq`).

Since the orbit has least period `T₀`, it crosses the box only once in each period: the rest of the
orbit stays away from the segment where `W` is supported, which is where the leastness of the
period enters. The general composition of the flow through a region where two fields agree is
`TauCeti.mfderiv_flowOf_add_eq_of_eqOn`.

**Nondegeneracy of every cover.** The linearized return map at time `m * T₀` is the `m`-th power of
the one at time `T₀` (`TauCeti.returnDerivative_natCast_mul`), so the `m`-fold cover of the orbit
of `v + a • W` is nondegenerate when `(exp a • DP)ᵐ` has no eigenvalue `1`, for `DP` the linearized
return map of `v`. By `Module.End.countable_setOf_exists_hasEigenvalue_one_pow_smul` this fails
for only countably many `a` (`TauCeti.exists_contDiff_countable_setOf_hasEigenvalue_one_pow`). The
resonant case is included: for `DP = -1` the orbit itself is nondegenerate but its double cover is
not, while the rescalings `exp a • DP` with `a ≠ 0` have no power with the eigenvalue `1`.

This is the flow-box perturbation step of the Kupka–Smale theorem for closed orbits, in the
coordinates of a chart straightening the field near a point of the orbit
(`TauCeti.exists_chart_mfderiv_eq_const`). Transporting it to a closed orbit on a manifold through
such a chart is not done here.

## Main results

* `TauCeti.exists_contDiff_returnDerivative_add_smul_eq_exp_smul`: a smooth compactly supported
  field `W`, supported near `0` and vanishing on the orbit, such that `v + a • W` keeps the closed
  orbit and has linearized return map `exp a • DP`.
* `TauCeti.exists_contDiff_countable_setOf_hasEigenvalue_one_pow`: for all but countably many
  `a`, no power of the linearized return map of `v + a • W` has the eigenvalue `1`.

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
  {v : E → E} {T₀ : ℝ} {u : E}

/-- The closed orbit and the linearized return maps of a field `w` which agrees with `v` off a
closed set `S` avoided by the orbit of `0` after time `σ`, and whose time-`σ` map carries `0` to the
same point as that of `v`, with derivative `D` at `0` where that of `v` is the identity. If `D`
acts as multiplication by `c` modulo `ℝ ∙ v 0`, then `0` returns at time `T₀` under `w` too, and
the linearized return maps of `w` are `c` times those of `v`. -/
private theorem returnDerivative_eq_smul_of_eqOn_compl
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun z : E ↦ (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hP : (T₀, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) v)
    (hp : flowOf (I := 𝓘(ℝ, E)) v T₀ 0 = 0) {σ c : ℝ} (hσ : 0 < σ) (hσT : σ < T₀)
    {w : E → E}
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun z : E ↦ (⟨z, w z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hw0 : w 0 = v 0) (hσw : (σ, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) w)
    (hσvw : flowOf (I := 𝓘(ℝ, E)) w σ 0 = flowOf (I := 𝓘(ℝ, E)) v σ 0)
    (hv_deriv : HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) v σ) (1 : E →L[ℝ] E) 0) {D : E →L[ℝ] E}
    (hw_deriv : HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) w σ) D 0) (hD : ∀ ξ, D ξ - c • ξ ∈ ℝ ∙ v 0)
    {S : Set E} (hS : IsClosed S) (hwv : EqOn w v Sᶜ)
    (hSv : ∀ t ∈ Icc σ T₀, flowOf (I := 𝓘(ℝ, E)) v t 0 ∉ S) :
    (T₀, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) w ∧ flowOf (I := 𝓘(ℝ, E)) w T₀ 0 = 0 ∧
      ∀ g : E → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 g 0 → mvfderiv 𝓘(ℝ, E) g 0 (v 0) ≠ 0 →
        returnDerivative (I := 𝓘(ℝ, E)) w g T₀ 0 =
          c • returnDerivative (I := 𝓘(ℝ, E)) v g T₀ 0 := by
  have hdom : ∀ t ∈ Icc 0 T₀, (t, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) v := fun t ht ↦
    uIcc_subset_setOf_mem_flowDomain hP (Icc_subset_uIcc ht)
  have hσdom := hdom σ ⟨hσ.le, hσT.le⟩
  set q := flowOf (I := 𝓘(ℝ, E)) v σ 0
  -- After time `σ`, the trajectory runs where `w = v`, back to `0` at time `T₀`.
  have hleg : (T₀ - σ, q) ∈ flowDomain (I := 𝓘(ℝ, E)) v := by
    rw [mem_flowDomain_flowOf_iff hv hσdom, add_sub_cancel]
    exact hP
  have hlegS : MapsTo (fun s ↦ flowOf (I := 𝓘(ℝ, E)) v s q) (uIcc 0 (T₀ - σ)) Sᶜ := by
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    have hσs : σ + s ∈ Icc σ T₀ := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    dsimp only [q]
    rw [(flowOf_add hv hσdom ((mem_flowDomain_flowOf_iff hv hσdom).2
      (hdom _ ⟨hσ.le.trans hσs.1, hσs.2⟩))).2]
    exact hSv _ hσs
  obtain ⟨hdomw, hvalw, hderw⟩ :=
    mfderiv_flowOf_add_eq_of_eqOn hv hw hS.isOpen_compl hwv hσw hσvw hleg hlegS
  rw [add_sub_cancel] at hdomw hvalw hderw
  have hvalv : flowOf (I := 𝓘(ℝ, E)) v (T₀ - σ) q = 0 := by
    rw [(flowOf_add hv hσdom hleg).2, add_sub_cancel, hp]
  refine ⟨hdomw, hvalw.trans hvalv, fun g hg hgv ↦
    returnDerivative_eq_smul_of_mfderiv_flowOf_eq hv hP hp hg hgv hw hdomw (hvalw.trans hvalv)
      hw0 (D := fun ξ ↦ D ξ) hD fun ξ ↦ ?_⟩
  -- The monodromy of `w` is that of `v` composed with `D`.
  have h₁ := mfderiv_flowOf_add_apply hv hσdom rfl hleg (D ξ)
  rw [add_sub_cancel, hv_deriv.hasMFDerivAt.mfderiv] at h₁
  rw [hderw ξ, hw_deriv.hasMFDerivAt.mfderiv]
  exact h₁

omit [FiniteDimensional ℝ E] in
/-- A short initial segment `[0, σ] • u` of the axis, with `σ < T₀`, lies in a given ball around
`0`. -/
private theorem exists_forall_smul_mem_ball {r : ℝ} (hr : 0 < r) (hT₀ : 0 < T₀) :
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

omit [FiniteDimensional ℝ E] in
/-- On a closed orbit of least period `T₀` running along the axis `ℝ • u` up to time `σ < T₀`, a
segment `[s₀, s₁] • u` with `0 < s₀` and `s₁ < σ` is disjoint from the rest of the orbit, the
points at the times of `[σ, T₀]`. -/
private theorem disjoint_image_smul_image_flowOf
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun z : E ↦ (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hP : (T₀, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) v)
    (hp : flowOf (I := 𝓘(ℝ, E)) v T₀ 0 = 0)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf (I := 𝓘(ℝ, E)) v t 0 ≠ 0) {σ s₀ s₁ : ℝ}
    (haxis : ∀ t ∈ Icc 0 σ, flowOf (I := 𝓘(ℝ, E)) v t 0 = t • u) (hs₀ : 0 < s₀)
    (hs₁ : s₁ < σ) :
    Disjoint ((fun s : ℝ ↦ s • u) '' Icc s₀ s₁)
      ((fun t ↦ flowOf (I := 𝓘(ℝ, E)) v t 0) '' Icc σ T₀) := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hst⟩
  refine flowOf_ne_flowOf_of_lt hv hP hp hmin (hs₀.trans_le hs.1)
    ((hs.2.trans_lt hs₁).trans_le ht.1) ht.2 ?_
  rw [haxis s ⟨hs₀.le.trans hs.1, hs.2.trans hs₁.le⟩]
  exact hst.symm

/-- On a closed orbit of least period `T₀` running along the axis `ℝ • u` up to time `σ < T₀`
inside a ball `B` around `0`, a segment `[s₀, s₁] • u` with `0 < s₀` and `s₁ < σ` has a smooth
compactly supported cutoff, equal to `1` near the segment, supported in `B` and away from the rest
of the orbit, the points at the times of `[σ, T₀]`. -/
private theorem exists_contDiff_cutoff_axis
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun z : E ↦ (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hP : (T₀, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) v)
    (hp : flowOf (I := 𝓘(ℝ, E)) v T₀ 0 = 0)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf (I := 𝓘(ℝ, E)) v t 0 ≠ 0) {σ s₀ s₁ r : ℝ}
    (hball : ∀ τ ∈ Icc 0 σ, τ • u ∈ ball (0 : E) r)
    (haxis : ∀ t ∈ Icc 0 σ, flowOf (I := 𝓘(ℝ, E)) v t 0 = t • u) (hσ : 0 ≤ σ) (hs₀ : 0 < s₀)
    (hs₁ : s₁ < σ) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ ball 0 r ∧
      (∀ t ∈ Icc σ T₀, flowOf (I := 𝓘(ℝ, E)) v t 0 ∉ tsupport χ) ∧
      ∀ s ∈ Icc s₀ s₁, s • u ∈ interior (χ ⁻¹' {1}) := by
  have hR : IsCompact ((fun t ↦ flowOf (I := 𝓘(ℝ, E)) v t 0) '' Icc σ T₀) :=
    isCompact_Icc.image_of_continuousOn ((isMIntegralCurveOn_flowOf hv 0).continuousOn.mono
      fun t ht ↦ uIcc_subset_setOf_mem_flowDomain hP (Icc_subset_uIcc ⟨hσ.trans ht.1, ht.2⟩))
  obtain ⟨χ, hχ, -, hχ1, hχc, hχU⟩ :=
    (isCompact_Icc.image (continuous_id.smul continuous_const)).exists_contDiff_cutoff
      (isOpen_ball.inter hR.isClosed.isOpen_compl) <| by
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨hball s ⟨hs₀.le.trans hs.1, hs.2.trans hs₁.le⟩, Set.disjoint_left.1
          (disjoint_image_smul_image_flowOf hv hP hp hmin haxis hs₀ hs₁) ⟨s, hs, rfl⟩⟩
  exact ⟨χ, hχ, hχc, hχU.trans inter_subset_left, fun t ht h ↦ (hχU h).2 ⟨t, ht, rfl⟩,
    fun s hs ↦ hχ1 ⟨s, hs, rfl⟩⟩

omit [FiniteDimensional ℝ E] in
/-- If `v = u` on `B`, `Z` vanishes outside the slab `s₀ < ℓ z < s₁` and the dilation field of a
profile `Φ` is `u + a • Z`, then `v + a • (χ • Z)` is that dilation field on the points of `B` where
`χ = 1` nearby or outside the closed slab. -/
private theorem eqOn_add_smul_transverseDilationField {ℓ : StrongDual ℝ E} {Φ : ℝ → ℝ}
    {Z : E → E} {χ : E → ℝ} {a s₀ s₁ : ℝ} {B : Set E} (hvB : ∀ z ∈ B, v z = u)
    (hΦ : ∀ z, transverseDilationField u ℓ Φ z = u + a • Z z)
    (hZ : ∀ z, ℓ z ∉ Ioo s₀ s₁ → Z z = 0) :
    EqOn (v + a • fun z ↦ χ z • Z z) (transverseDilationField u ℓ Φ)
      (B ∩ (interior (χ ⁻¹' {1}) ∪ ℓ ⁻¹' (Icc s₀ s₁)ᶜ)) := by
  rintro z ⟨hzB, hz⟩
  simp only [hΦ, Pi.add_apply, Pi.smul_apply, hvB z hzB]
  rcases hz with hz | hz
  · rw [show χ z = 1 from interior_subset hz, one_smul]
  · rw [hZ z fun h ↦ hz (Ioo_subset_Icc_self h), smul_zero, smul_zero]

/-- **The flow-box dilation of a closed orbit.** Let `v` be a `C¹` field on `E` with a closed
orbit through `0` of least period `T₀ > 0`, equal to a constant field `u` near `0`. For every
neighbourhood `N` of `0` there is a smooth compactly supported field `W`, supported in `N` and
vanishing along the orbit, such that for every `a` the closed orbit of `v` through `0` is a closed
orbit of `v + a • W` of the same period, and the linearized return map of every section `{g = g 0}`
transverse to `v` is multiplied by `exp a`. -/
theorem exists_contDiff_returnDerivative_add_smul_eq_exp_smul
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
  obtain ⟨r, hr, hrv⟩ := Metric.eventually_nhds_iff_ball.1 (hvu.and hN)
  -- The orbit is not a rest point, so the field near `0` is a nonzero constant.
  have hu : u ≠ 0 := by
    rintro rfl
    have h := flowOf_eq_of_isMIntegralCurve hv
      (isMIntegralCurve_const (v := v) (x := (0 : E)) (hrv 0 (mem_ball_self hr)).1) (T₀ / 2)
    exact hmin (T₀ / 2) ⟨by positivity, by linarith⟩ h
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hu
  -- The flow box contains the axis segment `[0, σ] • u`, and `σ < T₀`; the dilation acts across
  -- `[s₀, s₁] ⊆ (0, σ)`.
  obtain ⟨σ, hσ, hσT, hball⟩ := exists_forall_smul_mem_ball (u := u) hr hT₀
  set s₀ := σ / 3
  set s₁ := 2 * σ / 3
  have hs₀ : 0 < s₀ := by positivity
  have hs₀₁ : s₀ < s₁ := by simp only [s₀, s₁]; linarith
  have hs₁ : s₁ < σ := by simp only [s₁]; linarith
  obtain ⟨Ψ, hΨ, hΨ₀, hΨ₁, -, Z, hZ, hZout, hZaxis, hZa⟩ :=
    exists_contDiff_hasFDerivAt_flowOf_add_smul (E := E) hℓ hs₀₁
  have haΨ (a : ℝ) : ContDiff ℝ 2 fun s ↦ a * Ψ s := contDiff_const.mul (hΨ.of_le (by simp))
  have hTDF (a : ℝ) (z : E) : transverseDilationField u ℓ (fun s ↦ a * Ψ s) z = u + a • Z z :=
    (congrFun (hZa a).1 z).symm
  -- Near `0` the flow of `v` itself runs along the axis, with the identity as derivative.
  have hvU : EqOn v (transverseDilationField u ℓ fun s ↦ 0 * Ψ s) (ball 0 r) := fun z hz ↦ by
    rw [hTDF, zero_smul, add_zero]
    exact (hrv z hz).1
  have hseg {U : Set E} (hU : ∀ τ ∈ Icc 0 σ, τ • u ∈ U) {t : ℝ} (ht : t ∈ Icc 0 σ) :
      ∀ τ ∈ uIcc 0 t, (0 + τ) • u ∈ U := fun τ hτ ↦ by
    rw [uIcc_of_le ht.1] at hτ
    simpa using hU τ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hσσ : σ ∈ Icc 0 σ := ⟨hσ.le, le_rfl⟩
  have hv_axis (t : ℝ) (ht : t ∈ Icc 0 σ) :
      (t, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) v ∧ flowOf (I := 𝓘(ℝ, E)) v t 0 = t • u := by
    simpa using flowOf_smul_of_eqOn_transverseDilationField hℓ (haΨ 0) hv isOpen_ball hvU
      (hseg hball ht)
  have hv_deriv := hasFDerivAt_flowOf_of_eqOn_transverseDilationField hℓ (haΨ 0) hv isOpen_ball
    hvU (hseg hball hσσ)
  -- The cut-off `χ` is `1` near the segment `[s₀, s₁] • u` carrying the dilation, and supported
  -- away from the rest of the orbit, since the orbit has least period `T₀`.
  obtain ⟨χ, hχ, hχc, hχB, hχR, hχ1⟩ := exists_contDiff_cutoff_axis hv hP hp hmin hball
    (fun t ht ↦ (hv_axis t ht).2) hσ.le hs₀ hs₁
  set W : E → E := fun z ↦ χ z • Z z
  have htsW : tsupport W ⊆ tsupport χ := tsupport_smul_subset_left χ Z
  have hWaxis (s : ℝ) : W (s • u) = 0 := by simp [W, hZaxis]
  refine ⟨W, hχ.smul hZ, hχc.smul_right, htsW.trans (hχB.trans fun z hz ↦ (hrv z hz).2),
    fun t ht ↦ ?_, fun a ↦ ?_⟩
  · rcases le_or_gt t σ with h | h
    · rw [(hv_axis t ⟨ht.1, h⟩).2]
      exact hWaxis t
    · exact image_eq_zero_of_notMem_tsupport fun hW ↦ hχR t ⟨h.le, ht.2⟩ (htsW hW)
  -- The perturbed field is the dilation field of `s ↦ a * Ψ s` near the axis segment, and `v`
  -- off the support of `W`.
  have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun z : E ↦ (⟨z, (v + a • W) z⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.2 ((contMDiff_vectorSpace_iff_contDiff.1 hv).add
      (((hχ.smul hZ).of_le (by simp)).const_smul a))
  set U₁ : Set E := ball 0 r ∩ (interior (χ ⁻¹' {1}) ∪ ℓ ⁻¹' (Icc s₀ s₁)ᶜ)
  have hwU : EqOn (v + a • W) (transverseDilationField u ℓ fun s ↦ a * Ψ s) U₁ :=
    eqOn_add_smul_transverseDilationField (fun z hz ↦ (hrv z hz).1) (hTDF a) hZout
  have hσU₁ : ∀ τ ∈ Icc 0 σ, τ • u ∈ U₁ := fun τ hτ ↦ by
    refine ⟨hball τ hτ, ?_⟩
    by_cases h : τ ∈ Icc s₀ s₁
    · exact Or.inl (hχ1 τ h)
    · exact Or.inr (by simpa [hℓ] using h)
  have hU₁ : IsOpen U₁ :=
    isOpen_ball.inter (isOpen_interior.union (isClosed_Icc.preimage ℓ.continuous).isOpen_compl)
  -- So the flow of `v + a • W` also runs along the axis up to time `σ`, now with derivative
  -- the transverse dilation by `exp a`.
  have hw_axis := flowOf_smul_of_eqOn_transverseDilationField hℓ (haΨ a) hw hU₁ hwU
    (hseg hσU₁ hσσ)
  have hw_deriv := hasFDerivAt_flowOf_of_eqOn_transverseDilationField hℓ (haΨ a) hw hU₁ hwU
    (hseg hσU₁ hσσ)
  rw [zero_add, zero_smul] at hw_axis
  rw [zero_add, zero_smul, hΨ₁ σ hs₁.le, hΨ₀ 0 hs₀.le, mul_one, mul_zero, sub_zero] at hw_deriv
  -- The dilation acts as `exp a` modulo the flow line `ℝ ∙ u`.
  have hD (ξ : E) : ((1 - Real.exp a) * ℓ ξ) • u =
      (1 + (Real.exp a - 1) • (1 - ℓ.smulRight u) : E →L[ℝ] E) ξ - Real.exp a • ξ := by
    simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self]
    module
  have hv0 : v 0 = u := (hrv 0 (mem_ball_self hr)).1
  have hW0 : W 0 = 0 := by simpa using hWaxis 0
  refine returnDerivative_eq_smul_of_eqOn_compl hv hP hp hσ hσT hw (by simp [hW0]) hw_axis.1
    (hw_axis.2.trans (hv_axis σ hσσ).2.symm) (by simpa using hv_deriv) hw_deriv
    (fun ξ ↦ Submodule.mem_span_singleton.2 ⟨(1 - Real.exp a) * ℓ ξ, by rw [hv0]; exact hD ξ⟩)
    (isClosed_tsupport W) (fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz])
    fun t ht hW ↦ hχR t ht (htsW hW)

/-- **Every cover of a closed orbit becomes nondegenerate under a flow-box dilation.** Let `v` be
a `C¹` field on `E` with a closed orbit through `0` of least period `T₀ > 0`, equal to a constant
field `u` near `0`. For every neighbourhood `N` of `0` there is a smooth compactly supported
field `W`, supported in `N` and vanishing along the orbit, such that the closed orbit of `v`
through `0` is a closed orbit of every `v + a • W` of the same period and, for every section
`{g = g 0}` transverse to `v`, only countably many `a` give a positive power of the linearized
return map of `v + a • W` the eigenvalue `1`. Since the linearized return map at time `m * T₀` is
the `m`-th power of the one at time `T₀` (`TauCeti.returnDerivative_natCast_mul`), for all other
`a` the closed orbit and all its covers are nondegenerate. -/
theorem exists_contDiff_countable_setOf_hasEigenvalue_one_pow
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

end TauCeti
