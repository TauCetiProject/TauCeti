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
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.Flow.NormedSpace
import TauCeti.Geometry.Manifold.Flow.PartialDiffeomorph
import TauCeti.Geometry.Manifold.Flow.Straightening
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

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
period enters. The comparison of the two return maps, for any field agreeing with `v` off a closed
set avoided by the rest of the orbit, holds on every manifold
(`TauCeti.returnDerivative_eq_smul_of_eqOn_compl`); it rests on the composition of the flow
through a region where two fields agree, `TauCeti.mfderiv_flowOf_add_eq_of_eqOn`.

**Nondegeneracy of every cover.** The linearized return map at time `m * T₀` is the `m`-th power of
the one at time `T₀` (`TauCeti.returnDerivative_natCast_mul`), so the `m`-fold cover of the orbit
of `v + a • W` is nondegenerate when `(exp a • DP)ᵐ` has no eigenvalue `1`, for `DP` the linearized
return map of `v`. By `Module.End.countable_setOf_exists_hasEigenvalue_one_pow_smul` this fails
for only countably many `a` (`TauCeti.exists_contDiff_countable_setOf_hasEigenvalue_one_pow`). The
resonant case is included: for `DP = -1` the orbit itself is nondegenerate but its double cover is
not, while the rescalings `exp a • DP` with `a ≠ 0` have no power with the eigenvalue `1`.

**Closed orbits on a manifold.** This is the flow-box perturbation step of the Kupka–Smale theorem
for closed orbits. Let `v` be a smooth vector field on a smooth manifold with
finite-dimensional boundaryless model, with a closed orbit through `p` of least period `T₀ > 0`.
A partial diffeomorphism `φ` centred at `p` straightens `v` to a constant field `u`
(`TauCeti.exists_partialDiffeomorph_mfderiv_eq_const`), so that up to a short time `σ` the orbit is
the image under `φ⁻¹` of the axis segment `[0, σ] • u`. The cut-off dilation field `χ • Z` is
transplanted through `φ` to a smooth field `W` on the manifold
(`PartialDiffeomorph.exists_contMDiff_mfderiv_apply_eq`), and the flow of `v + a • W` near the
orbit is read off the flow of `u + a • (χ • Z)` through `φ`
(`PartialDiffeomorph.hasMFDerivAt_flowOf`). The derivative of its time-`σ` map at `p` is that of
`v` composed with the dilation conjugated by `dφ_p`, which again acts as multiplication by `exp a`
modulo the flow line `ℝ ∙ v p`. Hence the same two conclusions hold on the manifold
(`TauCeti.exists_contMDiff_returnDerivative_add_smul_eq_exp_smul`,
`TauCeti.exists_contMDiff_countable_setOf_hasEigenvalue_one_pow`), with `W` vanishing outside a
compact subset of any prescribed neighbourhood of `p`. The field `v` is taken smooth, so that the
straightening chart and the transplanted field `W` are smooth.

## Main results

* `TauCeti.returnDerivative_eq_smul_of_eqOn_compl`: a field agreeing with `v` off a closed set
  avoided by the orbit after time `σ`, whose time-`σ` map at `p` differs from that of `v` by a map
  acting as `c` modulo `ℝ ∙ v p`, keeps the closed orbit and multiplies the linearized return maps
  by `c`.
* `TauCeti.exists_contDiff_returnDerivative_add_smul_eq_exp_smul`: a smooth compactly supported
  field `W`, supported near `0` and vanishing on the orbit, such that `v + a • W` keeps the closed
  orbit and has linearized return map `exp a • DP`.
* `TauCeti.exists_contDiff_countable_setOf_hasEigenvalue_one_pow`: for all but countably many
  `a`, no power of the linearized return map of `v + a • W` has the eigenvalue `1`.
* `TauCeti.exists_contMDiff_returnDerivative_add_smul_eq_exp_smul`,
  `TauCeti.exists_contMDiff_countable_setOf_hasEigenvalue_one_pow`: the same for a closed orbit of
  a smooth vector field on a manifold.

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

/-- **Perturbing a closed orbit off a closed set.** Let `p` return to itself at time `T₀` under a
`C¹` field `v`, and let `w` be a `C¹` field agreeing with `v` off a closed set `S` which the orbit
of `p` avoids after time `σ`, with `0 ≤ σ ≤ T₀`. Suppose that the time-`σ` maps of `w` and `v` carry
`p` to the same point, and that there the derivative of the time-`σ` map of `w` is that of `v`
composed with a map `D` acting as multiplication by `c` modulo `ℝ ∙ v p`. Then `p` returns to
itself at time `T₀` under `w` too, and the linearized return maps of `w` are `c` times those of
`v`. -/
theorem returnDerivative_eq_smul_of_eqOn_compl {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I 1 M] [BoundarylessManifold I M] {v w : (x : M) → TangentSpace I x} {p : M}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hP : (T₀, p) ∈ flowDomain v)
    (hp : flowOf v T₀ p = p) {σ c : ℝ} (hσ : 0 ≤ σ) (hσT : σ ≤ T₀)
    (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle I M))) (hw0 : w p = v p)
    (hσw : (σ, p) ∈ flowDomain w) (hσvw : flowOf w σ p = flowOf v σ p)
    {D : TangentSpace I p → TangentSpace I p} (hD : ∀ ξ, D ξ - c • ξ ∈ ℝ ∙ v p)
    (hM : ∀ ξ : TangentSpace I p,
      -- The tangent spaces at the two values are both the model space `E`.
      @Eq E (mfderiv I I (flowOf w σ) p ξ) (mfderiv I I (flowOf v σ) p (D ξ)))
    {S : Set M} (hS : IsClosed S) (hwv : EqOn w v Sᶜ)
    (hSv : ∀ t ∈ Icc σ T₀, flowOf v t p ∉ S) :
    (T₀, p) ∈ flowDomain w ∧ flowOf w T₀ p = p ∧
      ∀ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g p → mvfderiv I g p (v p) ≠ 0 →
        returnDerivative w g T₀ p = c • returnDerivative v g T₀ p := by
  have hdom : ∀ t ∈ Icc 0 T₀, (t, p) ∈ flowDomain v := fun t ht ↦
    uIcc_subset_setOf_mem_flowDomain hP (Icc_subset_uIcc ht)
  have hσdom := hdom σ ⟨hσ, hσT⟩
  set q := flowOf v σ p
  -- After time `σ`, the trajectory runs where `w = v`, back to `p` at time `T₀`.
  have hleg : (T₀ - σ, q) ∈ flowDomain v := by
    rw [mem_flowDomain_flowOf_iff hv hσdom, add_sub_cancel]
    exact hP
  have hlegS : MapsTo (fun s ↦ flowOf v s q) (uIcc 0 (T₀ - σ)) Sᶜ := by
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    have hσs : σ + s ∈ Icc σ T₀ := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    dsimp only [q]
    rw [(flowOf_add hv hσdom ((mem_flowDomain_flowOf_iff hv hσdom).2
      (hdom _ ⟨hσ.trans hσs.1, hσs.2⟩))).2]
    exact hSv _ hσs
  obtain ⟨hdomw, hvalw, hderw⟩ :=
    mfderiv_flowOf_add_eq_of_eqOn hv hw hS.isOpen_compl hwv hσw hσvw hleg hlegS
  rw [add_sub_cancel] at hdomw hvalw hderw
  have hvalv : flowOf v (T₀ - σ) q = p := by
    rw [(flowOf_add hv hσdom hleg).2, add_sub_cancel, hp]
  refine ⟨hdomw, hvalw.trans hvalv, fun g hg hgv ↦
    returnDerivative_eq_smul_of_mfderiv_flowOf_eq hv hP hp hg hgv hw hdomw (hvalw.trans hvalv)
      hw0 hD fun ξ ↦ ?_⟩
  -- The monodromy of `w` is that of `v` composed with `D`.
  have h₁ := mfderiv_flowOf_add_apply hv hσdom rfl hleg (D ξ)
  rw [add_sub_cancel] at h₁
  rw [hderw ξ, hM ξ]
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

omit [FiniteDimensional ℝ E] in
/-- **The cut-off dilation along the axis.** Let `v` be a `C¹` field equal to `u` on a ball
`ball 0 r` containing the axis segment `[0, σ] • u`, let `u + a • Z` be the transverse dilation
fields of the profiles `s ↦ a * Ψ s` of a step `Ψ` from `0` to `1` across `[s₀, s₁] ⊆ [0, σ]`,
with `Z` vanishing outside the slab `s₀ < ℓ z < s₁`, and let `χ` be a smooth cutoff equal to `1`
near `[s₀, s₁] • u`. Then `v + a • (χ • Z)` is `C¹`, keeps the axis as a trajectory up to time
`σ`, and its time-`σ` map has derivative `1 + (exp a - 1) • (1 - ℓ.smulRight u)` at `0`. -/
private theorem axis_add_smul_cutoff [CompleteSpace E] {ℓ : StrongDual ℝ E} (hℓ : ℓ u = 1)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) {s₀ s₁ σ r : ℝ} (hs₀ : 0 ≤ s₀) (hs₁ : s₁ ≤ σ)
    (hσ : 0 ≤ σ) (hΨ₀ : ∀ s ≤ s₀, Ψ s = 0) (hΨ₁ : ∀ s, s₁ ≤ s → Ψ s = 1) {Z : E → E}
    (hZ : ContDiff ℝ ∞ Z) (hZout : ∀ z, ℓ z ∉ Ioo s₀ s₁ → Z z = 0)
    (hTDF : ∀ (a : ℝ) (z : E), transverseDilationField u ℓ (fun s ↦ a * Ψ s) z = u + a • Z z)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ1 : ∀ s ∈ Icc s₀ s₁, s • u ∈ interior (χ ⁻¹' {1}))
    (hball : ∀ τ ∈ Icc 0 σ, τ • u ∈ ball (0 : E) r)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun z : E ↦ (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hvB : ∀ z ∈ ball (0 : E) r, v z = u) (a : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
        (fun z : E ↦ (⟨z, (v + a • fun z ↦ χ z • Z z) z⟩ : TangentBundle 𝓘(ℝ, E) E)) ∧
      (∀ t ∈ Icc 0 σ, (t, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) (v + a • fun z ↦ χ z • Z z) ∧
        flowOf (I := 𝓘(ℝ, E)) (v + a • fun z ↦ χ z • Z z) t 0 = t • u) ∧
      HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) (v + a • fun z ↦ χ z • Z z) σ)
        (1 + (Real.exp a - 1) • (1 - ℓ.smulRight u)) 0 := by
  have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun z : E ↦ (⟨z, (v + a • fun z ↦ χ z • Z z) z⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.2 ((contMDiff_vectorSpace_iff_contDiff.1 hv).add
      (((hχ.smul hZ).of_le (by simp)).const_smul a))
  have haΨ : ContDiff ℝ 2 fun s ↦ a * Ψ s := contDiff_const.mul (hΨ.of_le (by simp))
  -- The perturbed field is the dilation field of `s ↦ a * Ψ s` near the axis segment.
  set U₁ : Set E := ball 0 r ∩ (interior (χ ⁻¹' {1}) ∪ ℓ ⁻¹' (Icc s₀ s₁)ᶜ)
  have hwU : EqOn (v + a • fun z ↦ χ z • Z z) (transverseDilationField u ℓ fun s ↦ a * Ψ s) U₁ :=
    eqOn_add_smul_transverseDilationField hvB (hTDF a) hZout
  have hU₁ : IsOpen U₁ :=
    isOpen_ball.inter (isOpen_interior.union (isClosed_Icc.preimage ℓ.continuous).isOpen_compl)
  have hseg {t : ℝ} (ht : t ∈ Icc 0 σ) : ∀ τ ∈ uIcc 0 t, (0 + τ) • u ∈ U₁ := fun τ hτ ↦ by
    rw [uIcc_of_le ht.1] at hτ
    have hτσ : τ ∈ Icc 0 σ := ⟨hτ.1, hτ.2.trans ht.2⟩
    rw [zero_add]
    refine ⟨hball τ hτσ, ?_⟩
    by_cases h : τ ∈ Icc s₀ s₁
    · exact Or.inl (hχ1 τ h)
    · exact Or.inr (by simpa [hℓ] using h)
  refine ⟨hw, fun t ht ↦ ?_, ?_⟩
  · simpa using flowOf_smul_of_eqOn_transverseDilationField hℓ haΨ hw hU₁ hwU (hseg ht)
  · have h := hasFDerivAt_flowOf_of_eqOn_transverseDilationField hℓ haΨ hw hU₁ hwU
      (hseg ⟨hσ, le_rfl⟩)
    rwa [zero_add, zero_smul, hΨ₁ σ hs₁, hΨ₀ 0 hs₀, mul_one, mul_zero, sub_zero] at h

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
  -- The perturbed field is the dilation field of `s ↦ a * Ψ s` near the axis segment, so its flow
  -- also runs along the axis up to time `σ`, now with derivative the transverse dilation by
  -- `exp a`.
  obtain ⟨hw, hw_axis, hw_deriv⟩ := axis_add_smul_cutoff hℓ hΨ hs₀.le hs₁.le hσ.le hΨ₀ hΨ₁ hZ
    hZout hTDF hχ hχ1 hball hv (fun z hz ↦ (hrv z hz).1) a
  -- The dilation acts as `exp a` modulo the flow line `ℝ ∙ u`.
  have hD (ξ : E) : ((1 - Real.exp a) * ℓ ξ) • u =
      (1 + (Real.exp a - 1) • (1 - ℓ.smulRight u) : E →L[ℝ] E) ξ - Real.exp a • ξ := by
    simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self]
    module
  have hv0 : v 0 = u := (hrv 0 (mem_ball_self hr)).1
  have hW0 : W 0 = 0 := by simpa using hWaxis 0
  have hv_deriv' : HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) v σ) (1 : E →L[ℝ] E) 0 := by
    simpa using hv_deriv
  -- The tangent spaces of `E` are `E`, so `(v + a • W) 0 = v 0` holds up to these identifications.
  have hw0 : (v + a • W) 0 = v 0 := by
    simp only [Pi.add_apply, Pi.smul_apply, hW0, smul_zero, add_zero]
  refine returnDerivative_eq_smul_of_eqOn_compl hv hP hp hσ.le hσT.le hw hw0 (hw_axis σ hσσ).1
    ((hw_axis σ hσσ).2.trans (hv_axis σ hσσ).2.symm)
    (fun ξ ↦ Submodule.mem_span_singleton.2 ⟨(1 - Real.exp a) * ℓ ξ, by rw [hv0]; exact hD ξ⟩)
    (fun ξ ↦ by rw [hw_deriv.hasMFDerivAt.mfderiv, hv_deriv'.hasMFDerivAt.mfderiv]; rfl)
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

section Manifold

omit [FiniteDimensional ℝ E] in
/-- Conjugating the transverse dilation `1 + (c - 1) • (1 - ℓ.smulRight u)` by an isomorphism `A`
with `A x = u` gives a map acting as multiplication by `c` modulo the line `ℝ ∙ x`. -/
private theorem inverse_dilation_sub_smul_mem_span {X : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] {A : X →L[ℝ] E} (hA : A.IsInvertible) {x : X} (hx : A x = u)
    (ℓ : StrongDual ℝ E) (c : ℝ) (ξ : X) :
    A.inverse ((1 + (c - 1) • (1 - ℓ.smulRight u)) (A ξ)) - c • ξ ∈ ℝ ∙ x := by
  refine Submodule.mem_span_singleton.2 ⟨(1 - c) * ℓ (A ξ), hA.injective ?_⟩
  rw [map_smul, hx, map_sub, map_smul, hA.self_apply_inverse]
  simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self]
  module

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- **A trajectory along the axis, read through a centred partial diffeomorphism.** Let `φ` be a
partial diffeomorphism with `φ p = 0`, carrying a `C¹` field `w` on `M` to a `C¹` field `F` on `E`
whose trajectory through `0` runs along the axis segment `[0, σ] • u` inside the target of `φ`.
Then up to time `σ` the trajectory of `w` through `p` is the image of that segment under `φ⁻¹`,
and if the time-`σ` map of `F` has derivative `L` at `0`, then that of `w` has derivative
`dφ⁻¹ ∘ L ∘ dφ_p` at `p`. -/
private theorem flowOf_eq_symm_smul_of_axis [IsManifold I 1 M] [BoundarylessManifold I M]
    {n : ℕ∞ω} (hn : n ≠ 0) (φ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) {p : M}
    (hpφ : p ∈ φ.source) (hφp : φ p = 0) {w : (x : M) → TangentSpace I x} {F : E → E}
    (hw : CMDiff 1 (fun x ↦ (⟨x, w x⟩ : TangentBundle I M)))
    (hF : CMDiff 1 (fun z : E ↦ (⟨z, F z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hrel : ∀ y ∈ φ.source, mfderiv I 𝓘(ℝ, E) φ y (w y) = F (φ y)) {σ : ℝ} (hσ : 0 ≤ σ)
    (htarget : ∀ t ∈ Icc 0 σ, t • u ∈ φ.target)
    (haxis : ∀ t ∈ Icc 0 σ, (t, (0 : E)) ∈ flowDomain (I := 𝓘(ℝ, E)) F ∧
      flowOf (I := 𝓘(ℝ, E)) F t 0 = t • u)
    {L : E →L[ℝ] E} (hL : HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) F σ) L 0) :
    (∀ t ∈ Icc 0 σ, (t, p) ∈ flowDomain w ∧ flowOf w t p = φ.symm (t • u)) ∧
      ∀ ξ : TangentSpace I p, @Eq E (mfderiv I I (flowOf w σ) p ξ)
        (mfderiv 𝓘(ℝ, E) I φ.symm (σ • u) (L (mfderiv I 𝓘(ℝ, E) φ p ξ))) := by
  have htgt {t : ℝ} (ht : t ∈ Icc 0 σ) :
      ∀ s ∈ uIcc 0 t, flowOf (I := 𝓘(ℝ, E)) F s (φ p) ∈ φ.target := fun s hs ↦ by
    rw [uIcc_of_le ht.1] at hs
    have hsσ : s ∈ Icc 0 σ := ⟨hs.1, hs.2.trans ht.2⟩
    rw [hφp, (haxis s hsσ).2]
    exact htarget s hsσ
  refine ⟨fun t ht ↦ ?_, fun ξ ↦ ?_⟩
  · have h := φ.flowOf_eq_symm_flowOf hn hw hF hrel hpφ (hφp ▸ (haxis t ht).1) (htgt ht)
    rwa [hφp, (haxis t ht).2] at h
  · have hσσ : σ ∈ Icc 0 σ := ⟨hσ, le_rfl⟩
    rw [(φ.hasMFDerivAt_flowOf hn hw hF hrel hpφ (hφp ▸ (haxis σ hσσ).1) (htgt hσσ)
      (hφp ▸ hL.hasMFDerivAt)).mfderiv, hφp, (haxis σ hσσ).2]
    rfl

/-- **The cut-off field transplanted to the manifold.** Let `φ` be a smooth partial diffeomorphism
whose target contains a ball `ball 0 r` mapped by `φ⁻¹` into `N`, and let `R` be a compact subset
of `M` avoided by `φ⁻¹ (s • u)` for `s ∈ [s₀, s₁]`, where `[s₀, s₁] • u` lies in the ball. For a
smooth field `Z` on `E` there are a smooth cutoff `χ`, equal to `1` near `[s₀, s₁] • u`, and a
smooth field `W` on `M`, carried by `φ` to `χ • Z` and vanishing outside a compact subset of `N`
which avoids `R`. -/
private theorem exists_contMDiff_cutoff_transplant [IsManifold I ∞ M]
    (φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {N R : Set M} {r s₀ s₁ : ℝ}
    (hrN : ball (0 : E) r ⊆ φ.target ∩ φ.symm ⁻¹' N) (hR : IsCompact R)
    (hseg : ∀ s ∈ Icc s₀ s₁, s • u ∈ ball (0 : E) r ∧ φ.symm (s • u) ∉ R) {Z : E → E}
    (hZ : ContDiff ℝ ∞ Z) (hZaxis : ∀ s : ℝ, Z (s • u) = 0) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ (∀ s ∈ Icc s₀ s₁, s • u ∈ interior (χ ⁻¹' {1})) ∧
      ∃ W : (x : M) → TangentSpace I x,
        ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, W x⟩ : TangentBundle I M)) ∧
        (∀ y ∈ φ.source, mfderiv I 𝓘(ℝ, E) φ y (W y) = χ (φ y) • Z (φ y)) ∧
        (∀ s : ℝ, s • u ∈ φ.target → W (φ.symm (s • u)) = 0) ∧
        ∃ K ⊆ N, IsCompact K ∧ (∀ x ∉ K, W x = 0) ∧ ∀ x ∈ K, x ∉ R := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  set U : Set E := ball 0 r ∩ (φ.target ∩ φ.symm ⁻¹' Rᶜ)
  have hUo : IsOpen U := isOpen_ball.inter (φ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage
    φ.symm.open_source hR.isClosed.isOpen_compl)
  obtain ⟨χ, hχ, -, hχ1, hχc, hχU⟩ :=
    (isCompact_Icc.image (continuous_id.smul continuous_const)).exists_contDiff_cutoff hUo <| by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨(hseg s hs).1, (hrN (hseg s hs).1).1, (hseg s hs).2⟩
  set W₀ : E → E := fun z ↦ χ z • Z z
  have htsW₀ : tsupport W₀ ⊆ U := (tsupport_smul_subset_left χ Z).trans hχU
  have htsW₀' : tsupport W₀ ⊆ φ.target := htsW₀.trans fun z hz ↦ hz.2.1
  obtain ⟨W, hW, hWK, hWφ⟩ := φ.exists_contMDiff_mfderiv_apply_eq (m := ∞) (W₀ := W₀) (by simp)
    (hχ.smul hZ) hχc.smul_right htsW₀'
  refine ⟨χ, hχ, fun s hs ↦ hχ1 ⟨s, hs, rfl⟩, W, hW, hWφ, fun s hs ↦ ?_, φ.symm '' tsupport W₀,
    ?_, hχc.smul_right.isCompact.image_of_continuousOn
      (φ.symm.contMDiffOn.continuousOn.mono htsW₀'), hWK, ?_⟩
  · -- On the axis `W₀ = χ • Z` vanishes, and the differential of `φ` is injective.
    have hy : φ.symm (s • u) ∈ φ.source := φ.map_target hs
    refine (φ.isInvertible_mfderiv (by simp) hy).injective ?_
    rw [hWφ _ hy, map_zero, PartialDiffeomorph.symm_toPartialEquiv, φ.right_inv hs]
    simp only [W₀, hZaxis, smul_zero]
    rfl
  · rintro _ ⟨z, hz, rfl⟩
    exact (hrN (htsW₀ hz).1).2
  · rintro _ ⟨z, hz, rfl⟩
    exact (htsW₀ hz).2.2

variable [I.Boundaryless] [IsManifold I ∞ M]

/-- **A centred straightening chart along a closed orbit.** Let `v` be a smooth field with a closed
orbit through `p` of least period `T₀ > 0`, and `N` a neighbourhood of `p`. There are a smooth
partial diffeomorphism `φ` with `φ p = 0` carrying `v` to a constant field `u`, a functional `ℓ`
with `ℓ u = 1`, a ball `ball 0 r` in the target of `φ` which `φ⁻¹` maps into the interior of `N`,
and a time `0 < σ < T₀` such that the axis segment `[0, σ] • u` lies in the ball and `φ⁻¹` carries
it onto the orbit of `p` up to time `σ`, the time-`σ` map of `v` having derivative `dφ⁻¹ ∘ dφ_p`
at `p`. -/
private theorem exists_partialDiffeomorph_axis {v : (x : M) → TangentSpace I x} {p : M}
    (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hT₀ : 0 < T₀) (hmin : ∀ t ∈ Ioo 0 T₀, flowOf v t p ≠ p) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ (φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (u : E) (ℓ : StrongDual ℝ E) (r σ : ℝ),
      p ∈ φ.source ∧ φ p = 0 ∧ ℓ u = 1 ∧ (∀ y ∈ φ.source, mfderiv I 𝓘(ℝ, E) φ y (v y) = u) ∧
      ball (0 : E) r ⊆ φ.target ∩ φ.symm ⁻¹' interior N ∧ 0 < σ ∧ σ < T₀ ∧
      (∀ τ ∈ Icc 0 σ, τ • u ∈ ball (0 : E) r) ∧
      (∀ t ∈ Icc 0 σ, (t, p) ∈ flowDomain v ∧ flowOf v t p = φ.symm (t • u)) ∧
      ∀ ξ : TangentSpace I p, @Eq E (mfderiv I I (flowOf v σ) p ξ)
        (mfderiv 𝓘(ℝ, E) I φ.symm (σ • u) (mfderiv I 𝓘(ℝ, E) φ p ξ)) := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have hv1 : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) := hv.of_le (by simp)
  -- The orbit is not a rest point, so `v p ≠ 0`, and a partial diffeomorphism `φ` centred at `p`
  -- carries `v` to a constant field `u`.
  have hvp : v p ≠ 0 := fun h ↦ hmin (T₀ / 2) ⟨by positivity, by linarith⟩
    (flowOf_eq_of_isMIntegralCurve hv1 (isMIntegralCurve_const h) (T₀ / 2))
  obtain ⟨φ, u, hpφ, hφp, hu, hφv⟩ := exists_partialDiffeomorph_mfderiv_eq_const (m := ⊤)
    (n := ∞) le_top (by simp) hv.contMDiffOn univ_mem hvp
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hu
  -- A ball around `0 = φ p` in the target of `φ`, which `φ⁻¹` maps into the interior of `N`.
  have hO : φ.target ∩ φ.symm ⁻¹' interior N ∈ 𝓝 (0 : E) := by
    refine (φ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage φ.symm.open_source
      isOpen_interior).mem_nhds ⟨hφp ▸ φ.map_source hpφ, ?_⟩
    rw [mem_preimage, ← hφp, PartialDiffeomorph.symm_toPartialEquiv, φ.left_inv hpφ]
    exact mem_interior_iff_mem_nhds.2 hN
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.1 hO
  obtain ⟨σ, hσ, hσT, hball⟩ := exists_forall_smul_mem_ball (u := u) hr hT₀
  -- In `φ`, the flow of `v` is translation along `u`.
  obtain ⟨hv_axis, hv_deriv⟩ := flowOf_eq_symm_smul_of_axis (by simp) φ hpφ hφp hv1
    (contMDiff_vectorSpace_iff_contDiff.2 contDiff_const) hφv hσ.le
    (fun t ht ↦ (hrO (hball t ht)).1) (fun t _ ↦ ⟨(isCompleteVectorField_const u).mem_flowDomain
      t 0, by rw [flowOf_const, zero_add]⟩) (L := ContinuousLinearMap.id ℝ E)
    (by rw [funext (flowOf_const u σ)]; exact (hasFDerivAt_id (0 : E)).add_const (σ • u))
  exact ⟨φ, u, ℓ, r, σ, hpφ, hφp, hℓ, hφv, hrO, hσ, hσT, hball, hv_axis, hv_deriv⟩

/-- **The flow-box dilation of a closed orbit on a manifold.** Let `v` be a smooth vector field on
a smooth manifold with finite-dimensional boundaryless model, with a closed orbit through `p` of
least period `T₀ > 0`. For every neighbourhood `N` of `p` there is a smooth vector field `W`,
vanishing outside a compact subset of `N` and along the orbit, such that for every `a` the closed
orbit of `v` through `p` is a closed orbit of `v + a • W` of the same period, and the linearized
return map of every section `{g = g p}` transverse to `v` is multiplied by `exp a`. -/
theorem exists_contMDiff_returnDerivative_add_smul_eq_exp_smul {v : (x : M) → TangentSpace I x}
    {p : M} (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hT₀ : 0 < T₀) (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf v t p ≠ p) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ W : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, W x⟩ : TangentBundle I M)) ∧
      (∃ K ⊆ N, IsCompact K ∧ ∀ x ∉ K, W x = 0) ∧ (∀ t ∈ Icc 0 T₀, W (flowOf v t p) = 0) ∧
      ∀ a : ℝ, (T₀, p) ∈ flowDomain (v + a • W) ∧ flowOf (v + a • W) T₀ p = p ∧
        ∀ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g p → mvfderiv I g p (v p) ≠ 0 →
          returnDerivative (v + a • W) g T₀ p = Real.exp a • returnDerivative v g T₀ p := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have hv1 : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) := hv.of_le (by simp)
  have hn : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0 := by simp
  -- In a chart `φ` centred at `p`, `v` is the constant field `u` and the orbit runs along the axis
  -- segment `[0, σ] • u` up to time `σ`; the dilation acts across `[σ / 3, 2 * σ / 3]`.
  obtain ⟨φ, u, ℓ, r, σ, hpφ, hφp, hℓ, hφv, hrO, hσ, hσT, hball, hv_axis, hv_deriv⟩ :=
    exists_partialDiffeomorph_axis hv hT₀ hmin hN
  have hσσ : σ ∈ Icc 0 σ := ⟨hσ.le, le_rfl⟩
  obtain ⟨Ψ, hΨ, hΨ₀, hΨ₁, -, Z, hZ, hZout, hZaxis, hZa⟩ :=
    exists_contDiff_hasFDerivAt_flowOf_add_smul (E := E) hℓ (s₀ := σ / 3) (s₁ := 2 * σ / 3)
      (by linarith)
  -- The rest of the orbit, after time `σ`, is a compact set which the segment carrying the
  -- dilation avoids, since the orbit has least period `T₀`.
  have hR : IsCompact ((fun t ↦ flowOf v t p) '' Icc σ T₀) :=
    isCompact_Icc.image_of_continuousOn ((isMIntegralCurveOn_flowOf hv1 p).continuousOn.mono
      fun t ht ↦ uIcc_subset_setOf_mem_flowDomain hP (Icc_subset_uIcc ⟨hσ.le.trans ht.1, ht.2⟩))
  obtain ⟨χ, hχ, hχ1, W, hW, hWφ, hW_axis, K, hKN, hK, hWK, hKR⟩ :=
    exists_contMDiff_cutoff_transplant φ (N := interior N) (s₀ := σ / 3) (s₁ := 2 * σ / 3) hrO hR
      (fun s hs ↦ by
        have hsσ : s ∈ Icc 0 σ := ⟨by linarith [hs.1], by linarith [hs.2]⟩
        refine ⟨hball s hsσ, ?_⟩
        rintro ⟨t, ht, hts⟩
        rw [← (hv_axis s hsσ).2] at hts
        exact flowOf_ne_flowOf_of_lt hv1 hP hp hmin (by linarith [hs.1])
          (by linarith [hs.2, ht.1]) ht.2 hts.symm) hZ hZaxis
  have hW_orbit (t : ℝ) (ht : t ∈ Icc 0 T₀) : W (flowOf v t p) = 0 := by
    rcases le_or_gt t σ with h | h
    · rw [(hv_axis t ⟨ht.1, h⟩).2]
      exact hW_axis t (hrO (hball t ⟨ht.1, h⟩)).1
    · exact hWK _ fun hK' ↦ hKR _ hK' ⟨t, ⟨h.le, ht.2⟩, rfl⟩
  refine ⟨W, hW, ⟨K, hKN.trans interior_subset, hK, hWK⟩, hW_orbit, fun a ↦ ?_⟩
  -- In `φ`, the perturbed field `v + a • W` is `u + a • (χ • Z)`, whose flow runs along the axis
  -- up to time `σ` and dilates the transverse directions of its time-`σ` map by `exp a`.
  obtain ⟨hF, hF_axis, hF_deriv⟩ := axis_add_smul_cutoff hℓ hΨ (by positivity) (by linarith)
    hσ.le hΨ₀ hΨ₁ hZ hZout (fun a z ↦ (congrFun (hZa a).1 z).symm) hχ hχ1 hball
    (contMDiff_vectorSpace_iff_contDiff.2 contDiff_const) (fun _ _ ↦ rfl) a
  have hw : CMDiff 1 (fun x ↦ (⟨x, (v + a • W) x⟩ : TangentBundle I M)) :=
    (hv.add_section hW.const_smul_section).of_le (by simp)
  obtain ⟨hw_axis, hw_deriv⟩ := flowOf_eq_symm_smul_of_axis hn φ hpφ hφp hw hF (fun y hy ↦ by
    rw [Pi.add_apply, Pi.smul_apply, map_add, map_smul, hφv y hy, hWφ y hy]
    rfl) hσ.le (fun t ht ↦ (hrO (hball t ht)).1) hF_axis hF_deriv
  -- The differential of `φ` at `p`, with values in `E`.
  let A : TangentSpace I p →L[ℝ] E := mfderiv I 𝓘(ℝ, E) φ p
  have hA : A.IsInvertible := φ.isInvertible_mfderiv hn hpφ
  have hAv : A (v p) = u := hφv p hpφ
  have hWp : W p = 0 := by
    have h := hW_orbit 0 ⟨le_rfl, hT₀.le⟩
    rwa [flowOf_zero] at h
  -- After time `σ`, the orbit runs where `W` vanishes.
  exact returnDerivative_eq_smul_of_eqOn_compl hv1 hP hp hσ.le hσT.le hw
    (by simp only [Pi.add_apply, Pi.smul_apply, hWp, smul_zero, add_zero] : (v + a • W) p = v p)
    (hw_axis σ hσσ).1 ((hw_axis σ hσσ).2.trans (hv_axis σ hσσ).2.symm)
    (inverse_dilation_sub_smul_mem_span hA hAv ℓ (Real.exp a)) (fun ξ ↦ (hw_deriv ξ).trans
      ((congrArg _ (hA.self_apply_inverse _).symm).trans (hv_deriv _).symm)) hK.isClosed
    (fun x hx ↦ (by simp only [Pi.add_apply, Pi.smul_apply, hWK x hx, smul_zero, add_zero] :
      (v + a • W) x = v x))
    fun t ht hK' ↦ hKR _ hK' ⟨t, ht, rfl⟩

/-- **Every cover of a closed orbit on a manifold becomes nondegenerate under a flow-box
dilation.** Let `v` be a smooth vector field on a smooth manifold with finite-dimensional
boundaryless model, with a closed orbit through `p` of least period `T₀ > 0`. For every
neighbourhood `N` of `p` there is a smooth vector field `W`, vanishing outside a compact subset of
`N` and along the orbit, such that the closed orbit of `v` through `p` is a closed orbit of every
`v + a • W` of the same period and, for every section `{g = g p}` transverse to `v`, only countably
many `a` give a positive power of the linearized return map of `v + a • W` the eigenvalue `1`.
Since the linearized return map at time `m * T₀` is the `m`-th power of the one at time `T₀`
(`TauCeti.returnDerivative_natCast_mul`), for all other `a` the closed orbit and all its covers are
nondegenerate. -/
theorem exists_contMDiff_countable_setOf_hasEigenvalue_one_pow {v : (x : M) → TangentSpace I x}
    {p : M} (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hT₀ : 0 < T₀) (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
    (hmin : ∀ t ∈ Ioo 0 T₀, flowOf v t p ≠ p) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ W : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, W x⟩ : TangentBundle I M)) ∧
      (∃ K ⊆ N, IsCompact K ∧ ∀ x ∉ K, W x = 0) ∧ (∀ t ∈ Icc 0 T₀, W (flowOf v t p) = 0) ∧
      (∀ a : ℝ, (T₀, p) ∈ flowDomain (v + a • W) ∧ flowOf (v + a • W) T₀ p = p) ∧
      ∀ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g p → mvfderiv I g p (v p) ≠ 0 →
        {a : ℝ | ∃ m ≠ 0, (returnDerivative (v + a • W) g T₀ p ^ m).HasEigenvalue 1}.Countable := by
  obtain ⟨W, hW, hWK, hWorb, hWa⟩ :=
    exists_contMDiff_returnDerivative_add_smul_eq_exp_smul hv hT₀ hP hp hmin hN
  refine ⟨W, hW, hWK, hWorb, fun a ↦ ⟨(hWa a).1, (hWa a).2.1⟩, fun g hg hgv ↦ ?_⟩
  refine ((Module.End.countable_setOf_exists_hasEigenvalue_one_pow_smul
    (returnDerivative v g T₀ p)).preimage Real.exp_injective).mono fun a ha ↦ ?_
  rw [Set.mem_ofPred_eq, (hWa a).2.2 g hg hgv] at ha
  exact ha

end Manifold

end TauCeti
