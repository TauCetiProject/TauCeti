/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.Kernel.Dimension
import TauCeti.Analysis.PDE.Vortex.SobolevScale
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The weak gauge-fixed vortex kernel and elliptic kernel identification

This file defines the weak `L²` kernel `weakGaugeFixedKernel x` of the gauge-fixed linearized
vortex operator `L_x = d₀* ⊕ d₁` and identifies it via elliptic regularity with the classical
kernel `gaugeFixedKernel x`.

## Mathematical setup

For any field `x : ℂ → ℝ⁴`, `weakGaugeFixedKernel x` is defined as the orthogonal complement in
`L²(ℂ; ℝ⁴)` of the span of those `w ∈ L²` agreeing almost everywhere with `L_x* η` for a smooth
compactly supported test field `η`. As an orthogonal complement in a Hilbert space, it is a closed
complete subspace of `L²(ℂ; ℝ⁴)` with no regularity hypothesis on `x`
(`isClosed_weakGaugeFixedKernel`, `CompleteSpace (weakGaugeFixedKernel x)`).

When `x` is continuous:

* `u ∈ weakGaugeFixedKernel x` if and only if `∫ ⟪u, L_x* η⟫ = 0` for every compactly supported
  smooth test field `η` (`mem_weakGaugeFixedKernel_iff`), and by uniform `C¹` mollification of
  compactly supported fields the same holds against compactly supported `C¹` or `C²` test fields
  (`mem_weakGaugeFixedKernel_iff_contDiff_one`, `mem_weakGaugeFixedKernel_iff_contDiff_two`);
* integration by parts sends every `y ∈ gaugeFixedKernel x` to an element of
  `weakGaugeFixedKernel x`, giving an injective real-linear map
  `gaugeFixedKernelToWeak : gaugeFixedKernel x →ₗ[ℝ] weakGaugeFixedKernel x`.

When `x` is smooth and each coordinate of `x` has bounded iterated derivatives of every order:

* the elliptic bootstrap
  (`mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq`) places
  `(u : ℂ → ℝ⁴)` in `sobolevFields s` for every `s : ℝ` whenever `u ∈ weakGaugeFixedKernel x`;
* Sobolev embedding on `ℂ` and the fundamental lemma of the calculus of variations produce a
  unique smooth (`C^∞`) pointwise solution `y ∈ gaugeFixedKernel x` representing `u` almost
  everywhere (`exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel`), so
  `gaugeFixedKernelToWeak` is a real-linear isomorphism
  `gaugeFixedKernelEquivWeak : gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x`;
* the classical kernel on `C¹ ∩ H^s` is independent of the Sobolev order `s : ℝ`
  (`mem_gaugeFixedKernel_iff_mem_sobolevFields`).

Combining `gaugeFixedKernelEquivWeak` with `finrank_gaugeFixedKernel_eq_two_mul_card` and the
regularity bounds for `framedFieldSpace` shows that at any continuous field `x` lying in
`framedFieldSpace f m j` for all `j : ℕ` (such as a Coulomb-gauge plane vortex) and satisfying the
holomorphicity rows `∂bar_a α = 0`, both `gaugeFixedKernel x` and `weakGaugeFixedKernel x` have
real dimension `2 m`.

## Main declarations

* `TauCeti.Vortex.weakGaugeFixedKernel`: the weak `L²` kernel of `L_x` as a closed complete
  submodule of `L²(ℂ; ℝ⁴)`.
* `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff`,
  `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff_contDiff_one`,
  `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff_contDiff_two`: testing characterizations against
  compactly supported `C^∞`, `C¹`, and `C²` fields.
* `TauCeti.Vortex.gaugeFixedKernelToWeak`: the injective linear map from `gaugeFixedKernel x` to
  `weakGaugeFixedKernel x`.
* `TauCeti.Vortex.gaugeFixedKernelEquivWeak` and `TauCeti.Vortex.framedGaugeFixedKernelEquivWeak`:
  the elliptic linear equivalence `gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x` for smooth
  backgrounds with bounded derivatives and for continuous fields lying in every `A_m^j`.
* `TauCeti.Vortex.mem_gaugeFixedKernel_iff_mem_sobolevFields`: order-independence of the kernel on
  `C¹ ∩ H^s` across all `s : ℝ`.
* `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_card`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_of_forall_mem_framedFieldSpace`: exact
  real dimension `2 |D|` and `2 m` of the weak kernel.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179, §3.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff RealInnerProductSpace Topology ENNReal

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### The weak `L²` kernel and its testing characterizations -/

/-- The weak `L²` kernel of the gauge-fixed linearized vortex operator `L_x`: the orthogonal
complement in `L²(ℂ; ℝ⁴)` of the span of square-integrable representatives of `L_x* η` on smooth
compactly supported test fields `η`. -/
def weakGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :=
  (Submodule.span ℝ {w : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) |
    ∃ η : ℂ → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ w =ᵐ[volume] gaugeFixedAdjoint x η})ᗮ

/-- The weak kernel of `L_x` is a closed subspace of `L²(ℂ; ℝ⁴)`. -/
theorem isClosed_weakGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    IsClosed
      (weakGaugeFixedKernel x : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ))) :=
  Submodule.isClosed_orthogonal _

instance (x : ℂ → EuclideanSpace ℝ (Fin 4)) : CompleteSpace (weakGaugeFixedKernel x) :=
  (isClosed_weakGaugeFixedKernel x).completeSpace_coe

/-- **Testing against `C^∞` fields.** At a continuous field `x`, a square-integrable field `u`
lies in `weakGaugeFixedKernel x` if and only if `∫ ⟪u, L_x* η⟫ = 0` for every smooth compactly
supported test field `η`. -/
theorem mem_weakGaugeFixedKernel_iff (hx : Continuous x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  rw [weakGaugeFixedKernel, Submodule.mem_orthogonal']
  refine ⟨fun hu η hη hηc ↦ ?_, fun hu w hw ↦ ?_⟩
  · have hmem : MemLp (gaugeFixedAdjoint x η) 2 volume :=
      (continuous_gaugeFixedAdjoint hx (hη.of_le (by simp))).memLp_of_hasCompactSupport
        (hasCompactSupport_gaugeFixedAdjoint hηc)
    rw [← L2.inner_toLp u hmem]
    exact hu _ (Submodule.subset_span ⟨η, hη, hηc, hmem.coeFn_toLp⟩)
  · refine Submodule.span_induction ?_ (by simp)
      (fun v₁ v₂ _ _ h₁ h₂ ↦ by rw [inner_add_right, h₁, h₂, add_zero])
      (fun c v _ hv ↦ by rw [real_inner_smul_right, hv, mul_zero]) hw
    rintro v ⟨η, hη, hηc, hv⟩
    rw [L2.inner_def, ← hu η hη hηc]
    exact integral_congr_ae (hv.mono fun _ hz ↦ by simp only [hz])

/-- Pointwise bound on `L_x* δ` in terms of `‖fderiv ℝ δ‖` and `‖x‖ * ‖δ‖`. -/
private theorem norm_gaugeFixedAdjoint_le {δ : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hδ : DifferentiableAt ℝ δ z) :
    ‖gaugeFixedAdjoint x δ z‖ ≤ 4 * ‖fderiv ℝ δ z‖ + 8 * ‖x z‖ * ‖δ z‖ := by
  have hcoord (i : Fin 4) (v : ℂ) (hv : ‖v‖ = 1) :
      |fderiv ℝ (fun w ↦ δ w i) z v| ≤ ‖fderiv ℝ δ z‖ := by
    have hd : fderiv ℝ (fun w ↦ δ w i) z = (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ δ z) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z hδ.hasFDerivAt).fderiv
    rw [hd, ContinuousLinearMap.comp_apply, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ i).trans (by simpa [hv] using (fderiv ℝ δ z).le_opNorm v)
  have hmul (a b : Fin 4) : |x z a * δ z b| ≤ ‖x z‖ * ‖δ z‖ := by
    rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul (PiLp.norm_apply_le (x z) a) (PiLp.norm_apply_le (δ z) b)
      (norm_nonneg _) (norm_nonneg _)
  set B : ℝ := 2 * ‖fderiv ℝ δ z‖ + 4 * ‖x z‖ * ‖δ z‖
  have hB : 0 ≤ B := by positivity
  have hj (j : Fin 4) : |gaugeFixedAdjoint x δ z j| ≤ B := by
    have h₁ := fun i ↦ hcoord i 1 norm_one
    have hI := fun i ↦ hcoord i I norm_I
    match j with
    | 0 =>
      rw [gaugeFixedAdjoint_apply_zero, abs_le]
      constructor <;>
        linarith [abs_le.1 (h₁ 0), abs_le.1 (hI 1), abs_le.1 (hmul 2 3), abs_le.1 (hmul 3 2)]
    | 1 =>
      rw [gaugeFixedAdjoint_apply_one, abs_le]
      constructor <;>
        linarith [abs_le.1 (hI 0), abs_le.1 (h₁ 1), abs_le.1 (hmul 2 2), abs_le.1 (hmul 3 3)]
    | 2 =>
      rw [gaugeFixedAdjoint_apply_two, abs_le]
      constructor <;>
        linarith [abs_le.1 (h₁ 2), abs_le.1 (hI 3), abs_le.1 (hmul 1 2), abs_le.1 (hmul 0 3),
          abs_le.1 (hmul 3 0), abs_le.1 (hmul 2 1)]
    | 3 =>
      rw [gaugeFixedAdjoint_apply_three, abs_le]
      constructor <;>
        linarith [abs_le.1 (h₁ 3), abs_le.1 (hI 2), abs_le.1 (hmul 0 2), abs_le.1 (hmul 1 3),
          abs_le.1 (hmul 2 0), abs_le.1 (hmul 3 1)]
  have hsq : ‖gaugeFixedAdjoint x δ z‖ ^ 2 ≤ (2 * B) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    have hsqj (j : Fin 4) : gaugeFixedAdjoint x δ z j ^ 2 ≤ B ^ 2 := by
      have hj' := hj j
      exact sq_le_sq.2 (by rwa [abs_of_nonneg hB])
    nlinarith [hsqj 0, hsqj 1, hsqj 2, hsqj 3]
  have habs := sq_le_sq.1 hsq
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at habs
  linarith

/-- Integral bound for testing `u ∈ L²` against `L_x* δ` when `δ` is `C¹` with support in a
compact set `K` where `‖x‖ ≤ M` and `‖δ‖, ‖Dδ‖ ≤ ε`. -/
private theorem norm_integral_inner_gaugeFixedAdjoint_le (hx : Continuous x)
    {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : MemLp u 2 volume)
    {K : Set ℂ} (hK : IsCompact K) {M ε : ℝ} (hM : ∀ z ∈ K, ‖x z‖ ≤ M)
    {δ : ℂ → EuclideanSpace ℝ (Fin 4)} (hδ : ContDiff ℝ 1 δ) (hsupp : tsupport δ ⊆ K)
    (hδb : ∀ z ∈ K, ‖δ z‖ ≤ ε) (hdδb : ∀ z ∈ K, ‖fderiv ℝ δ z‖ ≤ ε) :
    ‖∫ z, ⟪u z, gaugeFixedAdjoint x δ z⟫‖ ≤ (4 + 8 * M) * ε * ∫ z in K, ‖u z‖ := by
  have hδc : HasCompactSupport δ := hK.of_isClosed_subset (isClosed_tsupport δ) hsupp
  have hint : Integrable (fun z ↦ ⟪u z, gaugeFixedAdjoint x δ z⟫) volume :=
    hu.integrable_inner
      ((continuous_gaugeFixedAdjoint hx hδ).memLp_of_hasCompactSupport
        (hasCompactSupport_gaugeFixedAdjoint hδc))
  have huK : IntegrableOn (fun z ↦ ‖u z‖) K volume :=
    ((hu.locallyIntegrable one_le_two).integrableOn_isCompact hK).norm
  have hzero (z : ℂ) (hz : z ∉ K) : ⟪u z, gaugeFixedAdjoint x δ z⟫ = 0 := by
    rw [gaugeFixedAdjoint_eq_zero_of_notMem_tsupport (fun h ↦ hz (hsupp h)), inner_zero_right]
  have hpt (z : ℂ) (hz : z ∈ K) :
      ‖⟪u z, gaugeFixedAdjoint x δ z⟫‖ ≤ ((4 + 8 * M) * ε) * ‖u z‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right
      ((norm_gaugeFixedAdjoint_le (hδ.differentiable one_ne_zero z)).trans ?_) (norm_nonneg _)
    nlinarith [hM z hz, hδb z hz, hdδb z hz, norm_nonneg (x z), norm_nonneg (δ z)]
  calc ‖∫ z, ⟪u z, gaugeFixedAdjoint x δ z⟫‖
      = ‖∫ z in K, ⟪u z, gaugeFixedAdjoint x δ z⟫‖ := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    _ ≤ ∫ z in K, ‖⟪u z, gaugeFixedAdjoint x δ z⟫‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in K, ((4 + 8 * M) * ε) * ‖u z‖ :=
        setIntegral_mono_on hint.integrableOn.norm (huK.const_mul _) hK.isClosed.measurableSet hpt
    _ = (4 + 8 * M) * ε * ∫ z in K, ‖u z‖ := integral_const_mul _ _

/-- Continuity of adjoint testing under uniform `C¹` approximation on a fixed compact set `K`. -/
private theorem norm_integral_inner_gaugeFixedAdjoint_sub_le (hx : Continuous x)
    {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : MemLp u 2 volume)
    {K : Set ℂ} (hK : IsCompact K) {M ε : ℝ} (hM : ∀ z ∈ K, ‖x z‖ ≤ M)
    {η₁ η₂ : ℂ → EuclideanSpace ℝ (Fin 4)} (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hsupp₁ : tsupport η₁ ⊆ K) (hsupp₂ : tsupport η₂ ⊆ K)
    (hdist : ∀ z ∈ K, dist (η₁ z) (η₂ z) ≤ ε ∧ dist (fderiv ℝ η₁ z) (fderiv ℝ η₂ z) ≤ ε) :
    ‖(∫ z, ⟪u z, gaugeFixedAdjoint x η₁ z⟫) - ∫ z, ⟪u z, gaugeFixedAdjoint x η₂ z⟫‖ ≤
      (4 + 8 * M) * ε * ∫ z in K, ‖u z‖ := by
  have hint {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 1 η) (hsupp : tsupport η ⊆ K) :
      Integrable (fun z ↦ ⟪u z, gaugeFixedAdjoint x η z⟫) volume :=
    hu.integrable_inner
      ((continuous_gaugeFixedAdjoint hx hη).memLp_of_hasCompactSupport
        (hasCompactSupport_gaugeFixedAdjoint (hK.of_isClosed_subset (isClosed_tsupport η) hsupp)))
  have hsub : (∫ z, ⟪u z, gaugeFixedAdjoint x η₁ z⟫) - ∫ z, ⟪u z, gaugeFixedAdjoint x η₂ z⟫ =
      ∫ z, ⟪u z, gaugeFixedAdjoint x (η₁ - η₂) z⟫ := by
    rw [← integral_sub (hint hη₁ hsupp₁) (hint hη₂ hsupp₂)]
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    have hadd := gaugeFixedAdjoint_add x (η := η₁ - η₂) (ν := η₂)
      ((hη₁.sub hη₂).differentiable one_ne_zero z) (hη₂.differentiable one_ne_zero z)
    rw [sub_add_cancel] at hadd
    dsimp only
    rw [hadd, inner_add_right, add_sub_cancel_right]
  rw [hsub]
  have hsupp : tsupport (η₁ - η₂) ⊆ K := by
    rw [sub_eq_add_neg]
    exact (tsupport_add η₁ (-η₂)).trans
      (union_subset hsupp₁ ((tsupport_neg η₂).trans_subset hsupp₂))
  refine norm_integral_inner_gaugeFixedAdjoint_le hx hu hK hM (hη₁.sub hη₂) hsupp
    (fun z hz ↦ by simpa [dist_eq_norm] using (hdist z hz).1)
    (fun z hz ↦ ?_)
  rw [show fderiv ℝ (η₁ - η₂) z = fderiv ℝ η₁ z - fderiv ℝ η₂ z from
    fderiv_sub (hη₁.differentiable one_ne_zero z) (hη₂.differentiable one_ne_zero z)]
  simpa [dist_eq_norm] using (hdist z hz).2

/-- **Testing against `C¹` fields.** At a continuous field `x`, a square-integrable field `u`
lies in `weakGaugeFixedKernel x` if and only if `∫ ⟪u, L_x* η⟫ = 0` for every compactly supported
`C¹` test field `η`. -/
theorem mem_weakGaugeFixedKernel_iff_contDiff_one (hx : Continuous x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 1 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  rw [mem_weakGaugeFixedKernel_iff hx]
  refine ⟨fun hu η hη hηc ↦ ?_, fun hu η hη hηc ↦ hu η (hη.of_le (by simp)) hηc⟩
  set K₁ : Set ℂ := Metric.cthickening 1 (tsupport η)
  have hK₁ : IsCompact K₁ := hηc.isCompact.cthickening
  obtain ⟨M₀, hM₀⟩ := hK₁.exists_bound_of_continuousOn hx.continuousOn
  set M : ℝ := max M₀ 0
  have hM (z : ℂ) (hz : z ∈ K₁) : ‖x z‖ ≤ M := (hM₀ z hz).trans (le_max_left _ _)
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  set U : ℝ := ∫ z in K₁, ‖u z‖
  have : 0 ≤ U := setIntegral_nonneg Metric.isClosed_cthickening.measurableSet fun _ _ ↦
    norm_nonneg _
  refine eq_of_abs_sub_le_all fun r hr ↦ ?_
  set C : ℝ := (4 + 8 * M) * (U + 1)
  have hC : 0 < C := by positivity
  obtain ⟨φ, hφK, hφε⟩ := hη.exists_testFunction_dist_le_and_dist_fderiv_le
    (Ω := (⊤ : Opens ℂ)) hηc.isCompact Subset.rfl zero_lt_one (subset_univ _) (div_pos hr hC)
  have hφ0 : ∫ z, ⟪u z, gaugeFixedAdjoint x φ z⟫ = 0 :=
    hu φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
  have hbound := norm_integral_inner_gaugeFixedAdjoint_sub_le hx (Lp.memLp u) hK₁ hM
    (φ.contDiff.of_le (by simp)) hη hφK (Metric.self_subset_cthickening (tsupport η))
    fun z _ ↦ hφε z
  rw [hφ0, zero_sub, norm_neg, Real.norm_eq_abs] at hbound
  rw [sub_zero]
  refine hbound.trans ?_
  have hle : (4 + 8 * M) * U ≤ C := by simp only [C]; nlinarith [hM_nonneg]
  calc (4 + 8 * M) * (r / C) * U = r * ((4 + 8 * M) * U / C) := by ring
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left ((div_le_one hC).2 hle) hr.le
    _ = r := mul_one r

/-- **Testing against `C²` fields.** At a continuous field `x`, a square-integrable field `u`
lies in `weakGaugeFixedKernel x` if and only if `∫ ⟪u, L_x* η⟫ = 0` for every compactly supported
`C²` test field `η`. This matches the orthogonality condition of the weak right inverse in
`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`. -/
theorem mem_weakGaugeFixedKernel_iff_contDiff_two (hx : Continuous x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 :=
  ⟨fun hu η hη hηc ↦ (mem_weakGaugeFixedKernel_iff_contDiff_one hx).1 hu η
    (hη.of_le (by norm_num)) hηc,
   fun hu ↦ (mem_weakGaugeFixedKernel_iff hx).2 fun η hη hηc ↦ hu η (hη.of_le (by simp)) hηc⟩

/-- **The weak right inverse takes values orthogonal to `weakGaugeFixedKernel x`.** At a `C¹`
solution `x` of the plane vortex equation with `|α|² → 1` at infinity, there is a bounded right
inverse `Q` on `L²(ℂ; ℝ⁴)` such that `Q f ∈ (weakGaugeFixedKernel x)ᗮ` for every `f ∈ L²`. -/
theorem exists_continuousLinearMap_mem_orthogonal_weakGaugeFixedKernel (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) ∧
      ∀ f, Q f ∈ (weakGaugeFixedKernel x)ᗮ := by
  obtain ⟨Q, hQ, hQK⟩ := exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) hx hsol hlim
  refine ⟨Q, hQ, fun f ↦ (Submodule.mem_orthogonal' _ _).2 fun u hu ↦ ?_⟩
  rw [L2.inner_def]
  exact hQK f u ((mem_weakGaugeFixedKernel_iff_contDiff_two hx.continuous).1 hu)

/-! ### From the classical kernel to the weak kernel -/

/-- A square-integrable `C¹` solution of `L_x y = 0` represents an element of
`weakGaugeFixedKernel x`. -/
theorem toLp_mem_weakGaugeFixedKernel_of_gaugeFixedOperator_eq_zero (hx : Continuous x)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 1 y) (hy₂ : MemLp y 2 volume)
    (hker : ∀ z, gaugeFixedOperator x y z = 0) :
    hy₂.toLp y ∈ weakGaugeFixedKernel x := by
  rw [mem_weakGaugeFixedKernel_iff hx]
  intro η hη hηc
  have hae : ∫ z, ⟪(hy₂.toLp y : ℂ → EuclideanSpace ℝ (Fin 4)) z, gaugeFixedAdjoint x η z⟫ =
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ :=
    integral_congr_ae (hy₂.coeFn_toLp.mono fun _ hz ↦ by simp only [hz])
  rw [hae, ← integral_inner_gaugeFixedOperator hx hy (hη.of_le (by simp)) (.inr hηc)]
  simp [hker]

/-- The real-linear map sending a classical solution `y ∈ gaugeFixedKernel x` to its `L²`
equivalence class in `weakGaugeFixedKernel x`. -/
def gaugeFixedKernelToWeak (hx : Continuous x) :
    gaugeFixedKernel x →ₗ[ℝ] weakGaugeFixedKernel x :=
  (gaugeFixedKernelToLp x).codRestrict (weakGaugeFixedKernel x) fun y ↦ by
    rw [gaugeFixedKernelToLp_apply]
    exact toLp_mem_weakGaugeFixedKernel_of_gaugeFixedOperator_eq_zero hx
      ((mem_gaugeFixedKernel.1 y.2).1.of_le (by norm_num))
      (mem_gaugeFixedKernel.1 y.2).2.1 (mem_gaugeFixedKernel.1 y.2).2.2

/-- The underlying `L²` class of `gaugeFixedKernelToWeak hx y` is `gaugeFixedKernelToLp x y`. -/
@[simp]
theorem coe_gaugeFixedKernelToWeak (hx : Continuous x) (y : gaugeFixedKernel x) :
    (gaugeFixedKernelToWeak hx y : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) =
      gaugeFixedKernelToLp x y := by
  rfl

/-- `gaugeFixedKernelToWeak` sends `y ∈ gaugeFixedKernel x` to an `L²` class agreeing almost
everywhere with `y`. -/
theorem coe_gaugeFixedKernelToWeak_ae_eq (hx : Continuous x) (y : gaugeFixedKernel x) :
    ((gaugeFixedKernelToWeak hx y : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :
      ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] (y : ℂ → EuclideanSpace ℝ (Fin 4)) := by
  rw [coe_gaugeFixedKernelToWeak]
  exact coe_gaugeFixedKernelToLp_ae_eq y

/-- `gaugeFixedKernelToWeak` is injective: continuous functions agreeing almost everywhere on `ℂ`
are equal everywhere. -/
theorem gaugeFixedKernelToWeak_injective (hx : Continuous x) :
    Function.Injective (gaugeFixedKernelToWeak hx) := by
  rw [gaugeFixedKernelToWeak, LinearMap.injective_codRestrict_iff]
  exact gaugeFixedKernelToLp_injective x

/-! ### Elliptic bootstrap and equivalence of weak and classical kernels -/

/-- **Sobolev regularity of the weak kernel.** At a smooth field `x` whose coordinates have bounded
iterated derivatives of each order, every `u ∈ weakGaugeFixedKernel x` lies in `sobolevFields s`
for every real order `s`. -/
theorem coeFn_mem_sobolevFields_of_mem_weakGaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} (hu : u ∈ weakGaugeFixedKernel x)
    (s : ℝ) :
    (u : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields s := by
  set k : ℕ := ⌈s⌉₊
  have hk : (u : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields (k + 1) :=
    mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx
      (fun i n _ ↦ hbound i n) (Lp.memLp u) (zero_mem _) fun η hη hηc ↦ by
        simpa using (mem_weakGaugeFixedKernel_iff hx.continuous).1 hu η hη hηc
  exact sobolevFields_mono (by linarith [Nat.le_ceil s]) hk

/-- **Smooth classical representative of a weak kernel element.** At a smooth field `x` whose
coordinates have bounded iterated derivatives of each order, every `u ∈ weakGaugeFixedKernel x`
agrees almost everywhere with a smooth field `y ∈ gaugeFixedKernel x` lying in `sobolevFields s`
for all `s : ℝ`. -/
theorem exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} (hu : u ∈ weakGaugeFixedKernel x) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ∞ y ∧ (∀ s, y ∈ sobolevFields s) ∧ y ∈ gaugeFixedKernel x ∧ u =ᵐ[volume] y := by
  obtain ⟨y, hys, huy, hyk, hker⟩ :=
    exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq hx hbound (Lp.memLp u)
      (fun _ ↦ zero_mem _) continuous_zero fun η hη hηc ↦ by
        simpa using (mem_weakGaugeFixedKernel_iff hx.continuous).1 hu η hη hηc
  have hyS (s : ℝ) : y ∈ sobolevFields s := sobolevFields_mono (Nat.le_ceil s) (hyk ⌈s⌉₊)
  exact ⟨y, hys, hyS,
    mem_gaugeFixedKernel.2 ⟨hys.of_le (by simp), memLp_of_mem_sobolevFields (hyS 0), hker⟩, huy⟩

/-- At a smooth field `x` with bounded derivatives, `gaugeFixedKernelToWeak` is surjective. -/
theorem gaugeFixedKernelToWeak_surjective (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    Function.Surjective (gaugeFixedKernelToWeak hx.continuous) := by
  intro u
  obtain ⟨y, -, -, hyk, huy⟩ :=
    exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel hx hbound u.2
  refine ⟨⟨y, hyk⟩, ?_⟩
  ext1
  exact Lp.ext_iff.2 ((coe_gaugeFixedKernelToWeak_ae_eq hx.continuous ⟨y, hyk⟩).trans huy.symm)

/-- **Elliptic identification of classical and weak kernels.** At a smooth field `x` whose
coordinates have bounded iterated derivatives of each order, `gaugeFixedKernelToWeak` is a
real-linear isomorphism `gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x`. -/
def gaugeFixedKernelEquivWeak (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x :=
  LinearEquiv.ofBijective (gaugeFixedKernelToWeak hx.continuous)
    ⟨gaugeFixedKernelToWeak_injective hx.continuous, gaugeFixedKernelToWeak_surjective hx hbound⟩

/-- `gaugeFixedKernelEquivWeak` agrees with `gaugeFixedKernelToWeak` on every element. -/
@[simp]
theorem gaugeFixedKernelEquivWeak_apply (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (y : gaugeFixedKernel x) :
    gaugeFixedKernelEquivWeak hx hbound y = gaugeFixedKernelToWeak hx.continuous y :=
  LinearEquiv.ofBijective_apply _ y

/-- `gaugeFixedKernelEquivWeak` sends `y ∈ gaugeFixedKernel x` to its `L²` equivalence class. -/
theorem coe_gaugeFixedKernelEquivWeak_ae_eq (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (y : gaugeFixedKernel x) :
    ((gaugeFixedKernelEquivWeak hx hbound y :
      Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :
        ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] (y : ℂ → EuclideanSpace ℝ (Fin 4)) := by
  rw [gaugeFixedKernelEquivWeak_apply]
  exact coe_gaugeFixedKernelToWeak_ae_eq hx.continuous y

/-- **Smoothness and all-order Sobolev regularity of the classical kernel.** At a smooth field `x`
with bounded derivatives, every `y ∈ gaugeFixedKernel x` is smooth and lies in `sobolevFields s`
for every real order `s`. -/
theorem contDiff_and_mem_sobolevFields_of_mem_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ ∞ y ∧ ∀ s, y ∈ sobolevFields s := by
  set u := gaugeFixedKernelToWeak hx.continuous ⟨y, hy⟩
  obtain ⟨y', hy's, hy'S, -, huy'⟩ :=
    exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel hx hbound u.2
  have hae : y' =ᵐ[volume] y :=
    huy'.symm.trans (coe_gaugeFixedKernelToWeak_ae_eq hx.continuous ⟨y, hy⟩)
  have heq : y' = y :=
    (hy's.continuous.ae_eq_iff_eq volume (mem_gaugeFixedKernel.1 hy).1.continuous).1 hae
  exact heq ▸ ⟨hy's, hy'S⟩

/-- **Order-independence of the Sobolev kernel.** At a smooth field `x` with bounded derivatives, a
field `y` lies in `gaugeFixedKernel x` if and only if `y` is `C¹`, lies in `sobolevFields s`, and
satisfies `L_x y = 0` pointwise, independently of the Sobolev order `s : ℝ`. -/
theorem mem_gaugeFixedKernel_iff_mem_sobolevFields (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (s : ℝ) {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    y ∈ gaugeFixedKernel x ↔
      ContDiff ℝ 1 y ∧ y ∈ sobolevFields s ∧ ∀ z, gaugeFixedOperator x y z = 0 := by
  refine ⟨fun hy ↦ ?_, fun ⟨hy₁, hyS, hker⟩ ↦ ?_⟩
  · obtain ⟨hys, hyall⟩ := contDiff_and_mem_sobolevFields_of_mem_gaugeFixedKernel hx hbound hy
    exact ⟨hys.of_le (by simp), hyall s, (mem_gaugeFixedKernel.1 hy).2.2⟩
  · have hy₂ : MemLp y 2 volume := memLp_of_mem_sobolevFields hyS
    have hu : hy₂.toLp y ∈ weakGaugeFixedKernel x :=
      toLp_mem_weakGaugeFixedKernel_of_gaugeFixedOperator_eq_zero hx.continuous hy₁ hy₂ hker
    obtain ⟨y', hy's, -, hy'k, huy'⟩ :=
      exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel hx hbound hu
    have heq : y' = y :=
      (hy's.continuous.ae_eq_iff_eq volume hy₁.continuous).1 (huy'.symm.trans hy₂.coeFn_toLp)
    exact heq ▸ hy'k

/-! ### Dimension of the weak kernel and framed-field specializations -/

/-- **Finite-dimensionality of the weak gauge-fixed kernel.** Let `x` be a smooth field with
bounded derivatives satisfying `∂bar_a α = 0` and `|α|² → 1` at infinity. Then
`weakGaugeFixedKernel x` is finite-dimensional over `ℝ`. -/
theorem finiteDimensional_weakGaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    FiniteDimensional ℝ (weakGaugeFixedKernel x) := by
  have := finiteDimensional_gaugeFixedKernel_of_tendsto_normSq (hx.of_le (by simp)) hhol hlim
  exact (gaugeFixedKernelEquivWeak hx hbound).finiteDimensional

/-- **The exact real dimension `2 |D|` of the weak gauge-fixed kernel.** Let `x` be a smooth field
with bounded derivatives, satisfying `∂bar_a α = 0`, `|α|² → 1` at infinity, and section zero
divisor `D`. Then `weakGaugeFixedKernel x` has real dimension `2 |D|`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * Multiset.card D := by
  rw [← (gaugeFixedKernelEquivWeak hx hbound).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD]

/-- **The exact real dimension `2 m` of the weak kernel at a degree-`m` framed field.** Let `x` be
a smooth field with bounded derivatives satisfying `∂bar_a α = 0` and the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`. Then `weakGaugeFixedKernel x` has real dimension `2 m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * m := by
  rw [← (gaugeFixedKernelEquivWeak hx hbound).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe]

/-- **Dimension `2 m` of `gaugeFixedKernel x` on `framedFieldSpace`.** For `s > 1`, at any smooth
field `x ∈ framedFieldSpace f m s` satisfying `∂bar_a α = 0`, `gaugeFixedKernel x` has real
dimension `2 m`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)}
    {m : ℕ} {s : ℝ} (hs : 1 < s) (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_eq_two_mul hxs hhol
    (tendsto_sectionValue_mul_inv_pow hs hx hxs.continuous)

/-- **Equivalence of classical and weak kernels for fields in every `A_m^j`.** A continuous field
`x` lying in `framedFieldSpace f m j` for every natural order `j` (such as a Coulomb-gauge plane
vortex, by `mem_framedFieldSpace_of_equation_eq_zero`) is smooth with bounded derivatives of all
orders, so `gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x`. -/
def framedGaugeFixedKernelEquivWeak {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j) (hcont : Continuous x) :
    gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x :=
  gaugeFixedKernelEquivWeak (contDiff_of_forall_mem_framedFieldSpace hcont hx) fun i n ↦
    exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hcont i n (hx (n + 2))

/-- `framedGaugeFixedKernelEquivWeak` agrees with `gaugeFixedKernelToWeak` on every element. -/
@[simp]
theorem framedGaugeFixedKernelEquivWeak_apply {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j) (hcont : Continuous x)
    (y : gaugeFixedKernel x) :
    framedGaugeFixedKernelEquivWeak hx hcont y = gaugeFixedKernelToWeak hcont y := by
  simp [framedGaugeFixedKernelEquivWeak]

/-- **Finite-dimensionality of `weakGaugeFixedKernel x` for fields in every `A_m^j`.** At a
continuous field `x` lying in every `framedFieldSpace f m j` and satisfying `∂bar_a α = 0`, the
weak kernel `weakGaugeFixedKernel x` is finite-dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel_of_forall_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j)
    (hcont : Continuous x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    FiniteDimensional ℝ (weakGaugeFixedKernel x) :=
  finiteDimensional_weakGaugeFixedKernel (contDiff_of_forall_mem_framedFieldSpace hcont hx)
    (fun i n ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hcont i n (hx (n + 2)))
    hhol (tendsto_normSq_of_mem_framedFieldSpace (s := (2 : ℝ)) one_lt_two (hx 2) hcont)

/-- **Exact real dimension `2 m` of `weakGaugeFixedKernel x` for fields in every `A_m^j`.** At a
continuous field `x` lying in every `framedFieldSpace f m j` and satisfying `∂bar_a α = 0`, the
weak `L²` kernel `weakGaugeFixedKernel x` has real dimension `2 m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_forall_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j)
    (hcont : Continuous x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * m := by
  rw [← (framedGaugeFixedKernelEquivWeak hx hcont).finrank_eq]
  exact finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace (s := (2 : ℝ)) one_lt_two
    (hx 2) (contDiff_of_forall_mem_framedFieldSpace hcont hx) hhol

end TauCeti.Vortex
