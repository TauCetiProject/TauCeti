/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Kernel.Dimension
public import TauCeti.Analysis.PDE.Vortex.SobolevScale
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Analysis.PDE.Vortex.Bootstrap
import TauCeti.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The weak `L²` kernel of the gauge-fixed vortex operator

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) has
formal adjoint `L_x*` (`gaugeFixedAdjoint`). Its **weak `L²` kernel**
(`TauCeti.Vortex.weakGaugeFixedKernel`) is the orthogonal complement in `L²(ℂ; ℝ⁴)` of the fields
`L_x* η`, `η` smooth and compactly supported. As an orthogonal complement in a Hilbert space, it is
a closed complete subspace of `L²(ℂ; ℝ⁴)` with no regularity hypothesis on `x`
(`isClosed_weakGaugeFixedKernel`, `CompleteSpace (weakGaugeFixedKernel x)`).

At a continuous field `x`:

* `u ∈ weakGaugeFixedKernel x` if and only if `∫ ⟪u, L_x* η⟫ = 0` for every smooth compactly
  supported test field `η` (`TauCeti.Vortex.mem_weakGaugeFixedKernel_iff`), and by uniform `C¹`
  mollification of compactly supported fields the same holds against compactly supported `C^n` test
  fields for any `1 ≤ n ≤ ∞` (`mem_weakGaugeFixedKernel_iff_contDiff_one`,
  `mem_weakGaugeFixedKernel_iff_contDiff_two`, `mem_weakGaugeFixedKernel_iff_contDiff`). In
  particular, the weak right inverse takes values orthogonal to `weakGaugeFixedKernel x`
  (`exists_continuousLinearMap_mem_orthogonal_weakGaugeFixedKernel`).
* A `C¹` square-integrable solution of `L_x y = 0` lies in `weakGaugeFixedKernel x` by integration
  by parts (`toLp_mem_weakGaugeFixedKernel_of_gaugeFixedOperator_eq_zero`), so taking `L²` classes
  maps `gaugeFixedKernel x` injectively into `weakGaugeFixedKernel x`
  (`gaugeFixedKernelToLp_mem_weakGaugeFixedKernel`, `gaugeFixedKernelToWeak`).

At an essentially bounded field these weak solutions lie in `H¹`
(`TauCeti.Vortex.mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`), so this is also
the kernel of `L_x` acting weakly on `H¹(ℂ)⁴`, the kernel in the Fredholm theory of
`L_x : H¹ → L²`.

At a `C³` field whose coordinates have bounded derivatives through order `3`:

* the elliptic bootstrap (`k = 3`) places every `u ∈ weakGaugeFixedKernel x` in `H⁴`, and Sobolev
  embedding into `C²` produces a unique classical representative `y ∈ gaugeFixedKernel x`
  (`existsUnique_mem_gaugeFixedKernel_ae_eq`), so the weak kernel is the range of
  `gaugeFixedKernelToLp x` (`range_gaugeFixedKernelToLp`) and `gaugeFixedKernelToWeak` is a
  real-linear isomorphism
  (`gaugeFixedKernelEquivWeak : gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x`), equating their
  dimensions (`finrank_weakGaugeFixedKernel_eq_finrank_gaugeFixedKernel`).

When `x` is smooth with all derivatives bounded:

* every `u ∈ weakGaugeFixedKernel x` lies in `sobolevFields s` for all `s : ℝ`
  (`coeFn_mem_sobolevFields_of_mem_weakGaugeFixedKernel`) with a smooth representative
  (`exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel`);
* every classical kernel element is smooth, lies in `sobolevFields s` for all `s : ℝ`
  (`contDiff_and_mem_sobolevFields_of_mem_gaugeFixedKernel`), and has all iterated derivatives
  vanishing at infinity (`tendsto_iteratedFDeriv_cocompact_of_mem_gaugeFixedKernel_apply`), so the
  Sobolev kernel on `C¹ ∩ L² ∩ H^s` (and on `C⁰ ∩ H^s` for `s > 2`) is independent of `s : ℝ`
  (`mem_gaugeFixedKernel_iff_mem_sobolevFields`,
  `mem_gaugeFixedKernel_iff_continuous_and_mem_sobolevFields`).

A continuous field in `A_m^s` for `s > 4` is `C³` with bounded derivatives through order `3`, so
when it satisfies `∂bar_a α = 0` its classical and weak kernels coincide and are finite-dimensional
(`finiteDimensional_weakGaugeFixedKernel_of_mem_framedFieldSpace`), and when it is smooth its weak
kernel has real dimension `2m` (`finrank_weakGaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace`).
In particular, a continuous field lying in `A_m^k` for every `k` has isomorphic classical and weak
kernels (`framedGaugeFixedKernelEquivWeak`), and when `∂bar_a α = 0` its weak kernel has real
dimension `2m` (`finrank_weakGaugeFixedKernel_eq_two_mul`). Separately, any `C¹` Coulomb-slice
vortex in `A_m^k` (`k ≥ 2`) lies in every `A_m^j` by `TauCeti.Analysis.PDE.Vortex.Bootstrap` and
satisfies the vortex equations, so its classical and weak kernels have real dimension `2m`
(`finrank_gaugeFixedKernel_eq_two_mul_of_equation_eq_zero`,
`finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero`).

## Main definitions

* `TauCeti.Vortex.weakGaugeFixedKernel x`: the weak `L²` kernel of `L_x`.
* `TauCeti.Vortex.gaugeFixedKernelToWeak`: the injective linear map from `gaugeFixedKernel x` to
  `weakGaugeFixedKernel x`.
* `TauCeti.Vortex.gaugeFixedKernelEquivWeak` and `TauCeti.Vortex.framedGaugeFixedKernelEquivWeak`:
  the elliptic linear equivalence `gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x`.

## Main results

* `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff`,
  `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff_contDiff_one`,
  `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff_contDiff_two`,
  `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff_contDiff`: at a continuous field, the weak kernel
  consists of the weak solutions of `L_x u = 0` against compactly supported `C^∞`, `C¹`, `C²`, and
  `C^n` (`1 ≤ n ≤ ∞`) test fields.
* `TauCeti.Vortex.range_gaugeFixedKernelToLp`: at a `C³` field with bounded derivatives through
  order `3`, the weak kernel is the space of `L²` classes of the classical kernel.
* `TauCeti.Vortex.mem_gaugeFixedKernel_iff_mem_sobolevFields`,
  `TauCeti.Vortex.mem_gaugeFixedKernel_iff_continuous_and_mem_sobolevFields`: order-independence of
  the kernel on `C¹ ∩ L² ∩ H^s` across all `s : ℝ`, and on `C⁰ ∩ H^s` for `s > 2`.
* `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_card`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero`: exact real
  dimension `2 |D|` and `2m` of the weak kernel.

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

open Complex Filter MeasureTheory Module Set TopologicalSpace
open scoped RealInnerProductSpace ContDiff Topology ENNReal

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### The weak `L²` kernel and its testing characterizations -/

/-- **The weak `L²` kernel of the gauge-fixed operator** `L_x = d₀* ⊕ d₁`: the orthogonal
complement in `L²(ℂ; ℝ⁴)` of the `L²` classes of the fields `L_x* η`, for smooth compactly
supported test fields `η`. At a continuous field it consists of the weak solutions of `L_x u = 0`
(`mem_weakGaugeFixedKernel_iff`). -/
def weakGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :=
  (Submodule.span ℝ {g | ∃ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η ∧
    HasCompactSupport η ∧ (g : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] gaugeFixedAdjoint x η})ᗮ

/-- The weak kernel of `L_x` is a closed subspace of `L²(ℂ; ℝ⁴)`. -/
theorem isClosed_weakGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    IsClosed
      (weakGaugeFixedKernel x : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ))) :=
  Submodule.isClosed_orthogonal _

-- `weakGaugeFixedKernel` is an unexposed semireducible `def` in a `module`, so downstream
-- modules cannot unfold it and typeclass synthesis cannot reach
-- `Submodule.instOrthogonalCompleteSpace`. Because `CompleteSpace` is `Prop`-valued, this
-- instance is definitionally equal to `Submodule.instOrthogonalCompleteSpace` once unfolded
-- (no diamond) and makes `HasOrthogonalProjection` / `orthogonalProjectionOnto` available.
/-- The weak kernel of `L_x` is a complete subspace of `L²(ℂ; ℝ⁴)`. -/
instance (x : ℂ → EuclideanSpace ℝ (Fin 4)) : CompleteSpace (weakGaugeFixedKernel x) :=
  (isClosed_weakGaugeFixedKernel x).completeSpace_coe

/-- **The weak kernel consists of the weak solutions of `L_x u = 0`.** At a continuous field `x`,
a square-integrable field `u` lies in the weak kernel of `L_x` exactly when
`∫ ⟪u, L_x* η⟫ = 0` for every smooth compactly supported test field `η`. -/
theorem mem_weakGaugeFixedKernel_iff (hx : Continuous x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  rw [weakGaugeFixedKernel, Submodule.mem_orthogonal]
  refine ⟨fun h η hη hηc ↦ ?_, fun h g hg ↦ ?_⟩
  · -- The field `L_x* η` is continuous with compact support, so it has an `L²` class.
    have hm : MemLp (gaugeFixedAdjoint x η) 2 volume :=
      memLp_gaugeFixedAdjoint hx (hη.of_le (by simp)) hηc
    rw [← L2.inner_toLp u hm, real_inner_comm]
    exact h _ (Submodule.subset_span ⟨η, hη, hηc, hm.coeFn_toLp⟩)
  · induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨η, hη, hηc, hgη⟩ := hg
      rw [L2.inner_def, ← h η hη hηc]
      exact integral_congr_ae (hgη.mono fun z hz ↦ by dsimp only; rw [hz, real_inner_comm])
    | zero => exact inner_zero_left u
    | add g g' _ _ hg hg' => rw [inner_add_left, hg, hg', add_zero]
    | smul c g _ hg => rw [real_inner_smul_left, hg, mul_zero]

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
  rw [fderiv_sub (hη₁.differentiable one_ne_zero z) (hη₂.differentiable one_ne_zero z)]
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

/-- **Testing against `C^n` fields (`1 ≤ n ≤ ∞`).** At a continuous field `x`, a square-integrable
field `u` lies in `weakGaugeFixedKernel x` if and only if `∫ ⟪u, L_x* η⟫ = 0` for every compactly
supported `C^n` test field `η`. -/
theorem mem_weakGaugeFixedKernel_iff_contDiff {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hn' : n ≤ (∞ : WithTop ℕ∞))
    (hx : Continuous x) {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ n η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 :=
  ⟨fun hu η hη hηc ↦ (mem_weakGaugeFixedKernel_iff_contDiff_one hx).1 hu η (hη.of_le hn) hηc,
   fun hu ↦ (mem_weakGaugeFixedKernel_iff hx).2 fun η hη hηc ↦ hu η (hη.of_le hn') hηc⟩

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
  rw [hae, ← integral_inner_gaugeFixedOperator hy (hη.of_le (by simp)) (.inr hηc)]
  simp [hker]

/-- **Classical kernel elements are weak solutions.** At a continuous field, the `L²` class of a
`C²` square-integrable solution of `L_x y = 0` lies in the weak kernel of `L_x`. -/
theorem gaugeFixedKernelToLp_mem_weakGaugeFixedKernel (hx : Continuous x)
    (y : gaugeFixedKernel x) : gaugeFixedKernelToLp x y ∈ weakGaugeFixedKernel x := by
  rw [gaugeFixedKernelToLp_apply]
  exact toLp_mem_weakGaugeFixedKernel_of_gaugeFixedOperator_eq_zero hx
    ((mem_gaugeFixedKernel.1 y.property).1.of_le one_le_two)
    (memLp_of_mem_gaugeFixedKernel y.property) (mem_gaugeFixedKernel.1 y.property).2.2

/-- The real-linear map sending a classical solution `y ∈ gaugeFixedKernel x` to its `L²`
equivalence class in `weakGaugeFixedKernel x`. -/
def gaugeFixedKernelToWeak (hx : Continuous x) :
    gaugeFixedKernel x →ₗ[ℝ] weakGaugeFixedKernel x :=
  (gaugeFixedKernelToLp x).codRestrict (weakGaugeFixedKernel x)
    (gaugeFixedKernelToLp_mem_weakGaugeFixedKernel hx)

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
  exact coeFn_gaugeFixedKernelToLp y

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
    mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k (hx.of_le (by simp))
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

/-- **Every weak kernel element has a unique classical representative.** When `x` is `C³` with
bounded derivatives through order `3`, every `u ∈ weakGaugeFixedKernel x` agrees almost everywhere
with a unique `y ∈ gaugeFixedKernel x`. -/
theorem existsUnique_mem_gaugeFixedKernel_ae_eq (hx : ContDiff ℝ 3 x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} (hu : u ∈ weakGaugeFixedKernel x) :
    ∃! y, y ∈ gaugeFixedKernel x ∧ (u : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] y := by
  have hus : (u : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields ((3 : ℕ) + 1) :=
    mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq 3 hx hbound
      (Lp.memLp u) (zero_mem _) fun η hη hηc ↦ by
        simpa using (mem_weakGaugeFixedKernel_iff hx.continuous).1 hu η hη hηc
  obtain ⟨y, hy, huy⟩ := exists_contDiff_ae_eq_of_mem_sobolevFields (k := 2) (by norm_num) hus
  have hyk : ∀ z, gaugeFixedOperator x y z = 0 :=
    (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) (f := 0) hx.continuous
      (hy.of_le (by simp)) continuous_zero).1 fun η hη hηc ↦ by
        have hcongr : ∫ z, ⟪(u : ℂ → EuclideanSpace ℝ (Fin 4)) z, gaugeFixedAdjoint x η z⟫ =
            ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ :=
          integral_congr_ae (huy.mono fun z hz ↦ by dsimp only; rw [hz])
        rw [← hcongr, (mem_weakGaugeFixedKernel_iff hx.continuous).1 hu η hη hηc]
        simp
  refine ⟨y, ⟨mem_gaugeFixedKernel.2 ⟨hy, (Lp.memLp u).ae_eq huy, hyk⟩, huy⟩, ?_⟩
  rintro y' ⟨hy', huy'⟩
  exact ((continuous_of_mem_gaugeFixedKernel hy').ae_eq_iff_eq volume hy.continuous).1
    (huy'.symm.trans huy)

/-- **Weak and classical `L²` kernels coincide.** Let `x` be a `C³` field whose coordinates have
bounded derivatives through order `3`. Then every weak `L²` solution of `L_x u = 0` is the `L²`
class of a `C²` square-integrable classical solution: the weak kernel of `L_x` is the image of
its classical kernel `gaugeFixedKernel x`. -/
theorem range_gaugeFixedKernelToLp (hx : ContDiff ℝ 3 x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    LinearMap.range (gaugeFixedKernelToLp x) = weakGaugeFixedKernel x := by
  refine le_antisymm ?_ fun u hu ↦ ?_
  · rintro _ ⟨y, rfl⟩
    exact gaugeFixedKernelToLp_mem_weakGaugeFixedKernel hx.continuous y
  obtain ⟨y, ⟨hyK, huy⟩, -⟩ := existsUnique_mem_gaugeFixedKernel_ae_eq hx hbound hu
  exact ⟨⟨y, hyK⟩, Lp.ext ((coeFn_gaugeFixedKernelToLp ⟨y, hyK⟩).trans huy.symm)⟩

/-- At a `C³` field `x` with bounded derivatives through order `3`, `gaugeFixedKernelToWeak` is
surjective. -/
theorem gaugeFixedKernelToWeak_surjective (hx : ContDiff ℝ 3 x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    Function.Surjective (gaugeFixedKernelToWeak hx.continuous) := by
  intro u
  have hu : (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) ∈
      LinearMap.range (gaugeFixedKernelToLp x) :=
    (range_gaugeFixedKernelToLp hx hbound).symm ▸ u.property
  obtain ⟨y, hy⟩ := hu
  exact ⟨y, Subtype.ext hy⟩

/-- **Elliptic identification of classical and weak kernels.** At a `C³` field `x` whose
coordinates have bounded iterated derivatives through order `3`, `gaugeFixedKernelToWeak` is a
real-linear isomorphism `gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x`. -/
def gaugeFixedKernelEquivWeak (hx : ContDiff ℝ 3 x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x :=
  LinearEquiv.ofBijective (gaugeFixedKernelToWeak hx.continuous)
    ⟨gaugeFixedKernelToWeak_injective hx.continuous, gaugeFixedKernelToWeak_surjective hx hbound⟩

/-- `gaugeFixedKernelEquivWeak` agrees with `gaugeFixedKernelToWeak` on every element. -/
@[simp]
theorem gaugeFixedKernelEquivWeak_apply (hx : ContDiff ℝ 3 x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (y : gaugeFixedKernel x) :
    gaugeFixedKernelEquivWeak hx hbound y = gaugeFixedKernelToWeak hx.continuous y :=
  LinearEquiv.ofBijective_apply _ y

/-- `gaugeFixedKernelEquivWeak` sends `y ∈ gaugeFixedKernel x` to its `L²` equivalence class. -/
theorem coe_gaugeFixedKernelEquivWeak_ae_eq (hx : ContDiff ℝ 3 x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (y : gaugeFixedKernel x) :
    ((gaugeFixedKernelEquivWeak hx hbound y :
      Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :
        ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] (y : ℂ → EuclideanSpace ℝ (Fin 4)) := by
  rw [gaugeFixedKernelEquivWeak_apply]
  exact coe_gaugeFixedKernelToWeak_ae_eq hx.continuous y

/-- At a `C³` field with bounded derivatives through order `3`, the weak kernel of `L_x` has the
dimension of its classical kernel. -/
theorem finrank_weakGaugeFixedKernel_eq_finrank_gaugeFixedKernel (hx : ContDiff ℝ 3 x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    finrank ℝ (weakGaugeFixedKernel x) = finrank ℝ (gaugeFixedKernel x) :=
  (gaugeFixedKernelEquivWeak hx hbound).finrank_eq.symm

/-- **Smoothness and all-order Sobolev regularity of the classical kernel.** At a smooth field `x`
with bounded derivatives, every `y ∈ gaugeFixedKernel x` is smooth and lies in `sobolevFields s`
for every real order `s`. -/
theorem contDiff_and_mem_sobolevFields_of_mem_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ ∞ y ∧ ∀ s, y ∈ sobolevFields s := by
  set u := gaugeFixedKernelToWeak hx.continuous ⟨y, hy⟩
  obtain ⟨y', hy's, hy'S, -, huy'⟩ :=
    exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel hx hbound u.property
  have hae : y' =ᵐ[volume] y :=
    huy'.symm.trans (coe_gaugeFixedKernelToWeak_ae_eq hx.continuous ⟨y, hy⟩)
  have heq : y' = y :=
    (hy's.continuous.ae_eq_iff_eq volume (continuous_of_mem_gaugeFixedKernel hy)).1 hae
  exact heq ▸ ⟨hy's, hy'S⟩

/-- **Iterated derivatives of kernel elements vanish at infinity.** When `x` is smooth with bounded
derivatives of all orders, every iterated derivative of each coordinate of `y ∈ gaugeFixedKernel x`
tends to zero at infinity. -/
theorem tendsto_iteratedFDeriv_cocompact_of_mem_gaugeFixedKernel_apply (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) (j : ℕ) (i : Fin 4) :
    Tendsto (iteratedFDeriv ℝ j fun z ↦ y z i) (cocompact ℂ) (𝓝 0) :=
  tendsto_iteratedFDeriv_cocompact_of_mem_sobolevFields_apply (s := (j : ℝ) + 2) (by linarith)
    ((contDiff_and_mem_sobolevFields_of_mem_gaugeFixedKernel hx hbound hy).2 ((j : ℝ) + 2))
    (continuous_of_mem_gaugeFixedKernel hy) i

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

/-- For `s > 2`, Sobolev embedding supplies `C¹` regularity automatically, so `gaugeFixedKernel x`
consists precisely of the continuous `H^s` fields solving `L_x y = 0`. -/
theorem mem_gaugeFixedKernel_iff_continuous_and_mem_sobolevFields {s : ℝ} (hs : 2 < s)
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    y ∈ gaugeFixedKernel x ↔
      Continuous y ∧ y ∈ sobolevFields s ∧ ∀ z, gaugeFixedOperator x y z = 0 := by
  rw [mem_gaugeFixedKernel_iff_mem_sobolevFields hx hbound s]
  refine ⟨fun ⟨hy₁, hys, hyk⟩ ↦ ⟨hy₁.continuous, hys, hyk⟩, fun ⟨hyc, hys, hyk⟩ ↦
    ⟨contDiff_of_mem_sobolevFields (n := 1) (by push_cast; linarith) hys hyc, hys, hyk⟩⟩

/-! ### Dimension of the weak kernel under asymptotic conditions -/

/-- **Finite-dimensionality of the weak gauge-fixed kernel under `|α|² → 1`.** Let `x` be a `C³`
field with bounded derivatives through order `3` satisfying `∂bar_a α = 0` and `|α|² → 1` at
infinity. Then `weakGaugeFixedKernel x` is finite-dimensional over `ℝ`. -/
theorem finiteDimensional_weakGaugeFixedKernel_of_tendsto_normSq (hx : ContDiff ℝ 3 x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    FiniteDimensional ℝ (weakGaugeFixedKernel x) := by
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume) (hx.of_le (by norm_num))
    hhol hlim fun _ ↦ mem_gaugeFixedKernel.1
  exact (gaugeFixedKernelEquivWeak hx hbound).finiteDimensional

/-- **The exact real dimension `2 |D|` of the weak gauge-fixed kernel.** Let `x` be a smooth field
with bounded derivatives through order `3`, satisfying `∂bar_a α = 0`, `|α|² → 1` at infinity, and
section zero divisor `D`. Then `weakGaugeFixedKernel x` has real dimension `2 |D|`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    finrank ℝ (weakGaugeFixedKernel x) = 2 * Multiset.card D := by
  rw [finrank_weakGaugeFixedKernel_eq_finrank_gaugeFixedKernel (hx.of_le (by simp)) hbound,
    finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD]

/-- **The exact real dimension `2m` of the weak kernel under the degree-`m` end framing.** Let `x`
be a smooth field with bounded derivatives through order `3` satisfying `∂bar_a α = 0` and the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then `weakGaugeFixedKernel x` has real dimension
`2m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow {m : ℕ}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    finrank ℝ (weakGaugeFixedKernel x) = 2 * m := by
  rw [finrank_weakGaugeFixedKernel_eq_finrank_gaugeFixedKernel (hx.of_le (by simp)) hbound,
    finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe]

/-! ### The weak kernel at a plane vortex -/

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ}

/-- **Dimension `2m` of `gaugeFixedKernel x` on `framedFieldSpace`.** For `s > 1`, at any smooth
field `x ∈ framedFieldSpace f m s` satisfying `∂bar_a α = 0`, `gaugeFixedKernel x` has real
dimension `2m`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace
    {s : ℝ} (hs : 1 < s) (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_eq_two_mul hxs hhol
    (tendsto_sectionValue_mul_inv_pow hs hx hxs.continuous)

/-- At any continuous field `x ∈ framedFieldSpace f m s`, `s > 4`, satisfying `∂bar_a α = 0`, the
weak `L²` kernel `weakGaugeFixedKernel x` is finite-dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel_of_mem_framedFieldSpace {s : ℝ} (hs : 4 < s)
    (hx : x ∈ framedFieldSpace f m s) (hxc : Continuous x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    FiniteDimensional ℝ (weakGaugeFixedKernel x) := by
  have hx3 : ContDiff ℝ 3 x := by
    have hd : ContDiff ℝ 3 (x - referenceField f m) :=
      contDiff_of_mem_sobolevFields (n := 3) (by push_cast; linarith) (mem_framedFieldSpace.1 hx)
        (hxc.sub (contDiff_referenceField f m).continuous)
    simpa using hd.add ((contDiff_referenceField f m).of_le (by simp))
  refine finiteDimensional_weakGaugeFixedKernel_of_tendsto_normSq hx3 (fun i n hn ↦ ?_) hhol
    (tendsto_normSq_of_mem_framedFieldSpace (by linarith) hx hxc)
  have hns : (n : ℝ) + 1 < s := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  exact exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace hns hx hxc i

/-- **Weak kernel dimension `2m` on `A_m^s`.** At any smooth field `x ∈ framedFieldSpace f m s`,
`s > 4`, satisfying `∂bar_a α = 0`, the weak `L²` kernel `weakGaugeFixedKernel x` has real
dimension `2m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace {s : ℝ} (hs : 4 < s)
    (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    finrank ℝ (weakGaugeFixedKernel x) = 2 * m := by
  refine finrank_weakGaugeFixedKernel_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow hxs
    (fun i n hn ↦ ?_) hhol (tendsto_sectionValue_mul_inv_pow (by linarith) hx hxs.continuous)
  have hns : (n : ℝ) + 1 < s := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  exact exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace hns hx hxs.continuous i

/-- **Equivalence of classical and weak kernels for fields in every `A_m^k`.** A continuous field
`x` lying in `framedFieldSpace f m k` for every natural order `k` (such as a Coulomb-gauge plane
vortex, by `mem_framedFieldSpace_of_equation_eq_zero`) is smooth with bounded derivatives of all
orders, so `gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x`. -/
def framedGaugeFixedKernelEquivWeak (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k) :
    gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x :=
  gaugeFixedKernelEquivWeak ((contDiff_of_forall_mem_framedFieldSpace hx hmem).of_le (by simp))
    fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2))

/-- `framedGaugeFixedKernelEquivWeak` agrees with `gaugeFixedKernelToWeak` on every element. -/
@[simp]
theorem framedGaugeFixedKernelEquivWeak_apply (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k) (y : gaugeFixedKernel x) :
    framedGaugeFixedKernelEquivWeak hx hmem y = gaugeFixedKernelToWeak hx y := by
  simp [framedGaugeFixedKernelEquivWeak]

/-- **The weak kernel at a plane vortex is finite-dimensional.** Let `x` be a continuous field
lying in the affine field space `A_m^k` for every `k` whose section satisfies the holomorphicity
rows `∂bar_a α = 0`, for instance a continuous plane vortex lying in every `A_m^k`. Then the weak
`L²` kernel of `L_x` is finite-dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    FiniteDimensional ℝ (weakGaugeFixedKernel x) := by
  have hxs := contDiff_of_forall_mem_framedFieldSpace hx hmem
  have := finiteDimensional_gaugeFixedKernel (hxs.of_le (by simp)) hhol
    (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hmem 2) hx)
  exact (framedGaugeFixedKernelEquivWeak hx hmem).finiteDimensional

/-- **The weak kernel at a plane vortex has dimension `2m`** (Taubes). Let `x` be a continuous
field lying in the affine field space `A_m^k` for every `k` whose section satisfies the
holomorphicity rows `∂bar_a α = 0`, for instance a continuous plane vortex lying in every `A_m^k`.
Then the weak `L²` kernel of `L_x` has real dimension `2m`, the dimension of the divisor space
`Sym^m ℂ`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    finrank ℝ (weakGaugeFixedKernel x) = 2 * m := by
  rw [← (framedGaugeFixedKernelEquivWeak hx hmem).finrank_eq]
  exact finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace (s := (2 : ℝ)) one_lt_two
    (by exact_mod_cast hmem 2) (contDiff_of_forall_mem_framedFieldSpace hx hmem) hhol

/-- **Kernel regularity at a Coulomb-slice vortex.** Let `x ∈ A_m^k`, `k ≥ 2`, be a `C¹` solution
of the vortex equation in the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` relative to a `C¹` base field
`x₀` lying in every `A_m^j`. Then every `y ∈ gaugeFixedKernel x` is smooth and lies in
`sobolevFields s` for all `s : ℝ`. -/
theorem contDiff_and_mem_sobolevFields_of_mem_gaugeFixedKernel_of_equation_eq_zero
    {k : ℕ} (hk : 1 < k) {x₀ x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ ∞ y ∧ ∀ s : ℝ, y ∈ sobolevFields s := by
  have hxs : ContDiff ℝ ∞ x := contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge
  exact contDiff_and_mem_sobolevFields_of_mem_gaugeFixedKernel hxs
    (fun i n ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hxc.continuous i n
      (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge (n + 2))) hy

/-- At any `C¹` Coulomb-slice vortex `x ∈ A_m^k`, `k ≥ 2`, relative to a `C¹` base field `x₀` lying
in every `A_m^j`, `gaugeFixedKernel x` is finite-dimensional. -/
theorem finiteDimensional_gaugeFixedKernel_of_equation_eq_zero
    {k : ℕ} (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    FiniteDimensional ℝ (gaugeFixedKernel x) :=
  finiteDimensional_gaugeFixedKernel
    ((contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge).of_le (by simp))
    (fun w ↦ by simp [heq w])
    (tendsto_sectionValue_mul_inv_pow (by exact_mod_cast hk) hx hxc.continuous)

/-- **Classical kernel dimension `2m` at a Coulomb-slice vortex.** Let `x ∈ A_m^k`, `k ≥ 2`, be a
`C¹` solution of the vortex equation in the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` relative to a
`C¹` base field `x₀` lying in every `A_m^j`. Then `gaugeFixedKernel x` has real dimension `2m`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_of_equation_eq_zero
    {k : ℕ} (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace (by exact_mod_cast hk) hx
    (contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge) fun w ↦ by simp [heq w]

/-- At any `C¹` Coulomb-slice vortex `x ∈ A_m^k`, `k ≥ 2`, relative to a `C¹` base field `x₀` lying
in every `A_m^j`, `weakGaugeFixedKernel x` is finite-dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel_of_equation_eq_zero
    {k : ℕ} (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    FiniteDimensional ℝ (weakGaugeFixedKernel x) :=
  finiteDimensional_weakGaugeFixedKernel hxc.continuous
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge)
    fun w ↦ by simp [heq w]

/-- **Weak kernel dimension `2m` at a Coulomb-slice vortex.** Let `x ∈ A_m^k`, `k ≥ 2`, be a `C¹`
solution of the vortex equation in the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` relative to a `C¹`
base field `x₀` lying in every `A_m^j`. Then `weakGaugeFixedKernel x` has real dimension `2m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero
    {k : ℕ} (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    finrank ℝ (weakGaugeFixedKernel x) = 2 * m :=
  finrank_weakGaugeFixedKernel_eq_two_mul hxc.continuous
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge)
    fun w ↦ by simp [heq w]

end TauCeti.Vortex
