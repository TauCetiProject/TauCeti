/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Index
public import TauCeti.Analysis.PDE.Vortex.Kernel.Projection
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.WindowEstimate
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.PiLp
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Weighted estimates for the parameter derivatives of the vortex splitting

At a plane vortex `x` with `L∞` class `a`, the realization `L_a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of the
gauge-fixed operator (`sobolevGaugeFixedOperator`) is Fredholm and onto. Its kernel projection `π`
along the `L²`-orthogonal complement (`ContinuousLinearMap.orthogonalKerProjection`) and its
right inverse `Q` with values in that complement (`ContinuousLinearMap.orthogonalRightInverse`)
split every `y ∈ H¹` as `y = π y + Q (L_a y)`. Along a family of coefficients `a(p)`, such as the
vortices of a family of divisors, `π` and `Q` depend smoothly on `p`. Gluing plane vortices into
solutions of the four-dimensional equations uses these operators and their derivatives in `p` on
errors that decay exponentially away from the vortex cores, measured with the weight
`exp(c ρ)`, `ρ(z) = √(1 + |z|²)`, `|c| < 1/2`. This file proves the weighted `L²` estimates for
`π`, `Q` and their first and second derivatives in `p`, and the weighted Sobolev estimates for
the first derivatives, with constants that depend only on the degree `m`, a radius `R₀`
containing the zeros, and `c` (and, for the Sobolev estimates, the order and a bound on the
derivatives of the vortex). They hold uniformly over a window of divisors, collisions included,
and their size is proportional to the size of the derivatives of the coefficient. Here `‖g‖_c`
denotes the weighted norm `‖exp(c ρ) g‖₂` of the values of `g`.

* **The splitting.** The kernel of `L_a` is the weak `L²` kernel (`sobolevGaugeFixedKernelEquiv`),
  whose elements decay at every rate below `1/2` uniformly over the window
  (`exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le`), so
  `‖k‖_c ≤ K ‖k‖₂` on the kernel of `L_a`
  (`exists_forall_eLpNorm_exp_mul_smul_le_of_mem_ker_of_forall_mem_norm_le`). The values of
  `Q f` are the weak solution of `L_x y = f` orthogonal to that kernel, so the weighted estimate
  for the weak right inverse (`exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le`)
  applies to them. This gives
  `‖Q f‖_c ≤ K ‖f‖_c`
  (`exists_forall_eLpNorm_exp_mul_smul_orthogonalRightInverse_le_of_forall_mem_norm_le`)
  and `‖π e‖_c ≤ K ‖e‖_c`
  (`exists_forall_eLpNorm_exp_mul_smul_orthogonalKerProjection_le_of_forall_mem_norm_le`).
* **The derivatives.** Write `π'`, `Q'` for the derivatives of `π`, `Q` along `v` and `b` for the
  derivative of the coefficient. The derivative of `L_a` is the zeroth-order operator
  `T' y = Z(b, y)` (`fderiv_sobolevGaugeFixedOperator_comp_apply`), so `‖T' y‖_c ≤ ‖Z‖ ‖b‖∞ ‖y‖_c`.
  The components of `π' e` and `Q' f` orthogonal to the kernel are `-Q T' π e` and `-Q T' Q f`,
  and their kernel components are determined by the pairings with the kernel
  `⟪π' e, k⟫ = -⟪e - π e, Q T' k⟫` and `⟪Q' f, k⟫ = ⟪Q f, Q T' k⟫`
  (`ContinuousLinearMap.IsFredholm.sub_orthogonalKerProjection_fderiv_orthogonalRightInverse_apply`,
  `ContinuousLinearMap.IsFredholm.inner_fderiv_orthogonalRightInverse_apply` and their analogues
  for `π`). For a kernel element `k` the weight costs a bounded factor at both rates `±c`, so
  moving the weight across the pairing
  (`TauCeti.eLpNorm_exp_mul_smul_le_of_sq_le_abs_inner`) bounds the kernel components. This gives
  `‖Q' f‖_c ≤ K ‖b‖∞ ‖f‖_c`
  (`exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le`)
  and `‖π' e‖_c ≤ K ‖b‖∞ ‖e‖_c`
  (`exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le`).
* **Weighted Sobolev estimates for the derivatives.** Suppose the derivative of the coefficient is
  the class of a smooth field `β` whose coordinates have derivatives bounded by `M` through order
  `k`. Differentiating `L Q = 1` and `L π = 0` gives `L_x (Q' f) = -Z(b, Q f)` and
  `L_x (π' e) = -Z(b, π e)`
  (`ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalRightInverse_apply`,
  `ContinuousLinearMap.IsFredholm.apply_fderiv_orthogonalKerProjection_apply`). The weighted
  elliptic estimate with a constant uniform in the field
  (`exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul`), applied to
  `Q f`, to the kernel element `π e` and then to the derivatives, together with multiplication by
  `β` on `H^k` and the weighted `L²` bounds above, gives
  `‖exp(c ρ) Q' f‖_(H^(k+1)) ≤ K M ‖exp(c ρ) f‖_(H^k)`
  (`exists_forall_norm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le`) and
  `‖exp(c ρ) π' e‖_(H^(k+1)) ≤ K M ‖e‖_c`
  (`exists_forall_norm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le`),
  with `K` depending only on `m`, `R₀`, `c`, `k` and a bound on the derivatives of the vortex
  through order `k`. Sobolev norms are those of the coordinates in Mathlib's Bessel-potential
  spaces `H^s(ℂ)`.

* **Second derivatives.** For a family `a` that is `C²` at `p₀`, write `Q''` and `π''` for the
  derivatives along `w` of `p ↦ DQ(p) v` and `p ↦ Dπ(p) v`, and `a''` for that of `p ↦ Da(p) v`.
  Differentiating the identities `L Q = 1`, `L π = 0` and the orthogonality relations twice gives
  the components of `Q'' f` and `π'' e` orthogonal to the kernel, `-Q (Z(a'', g₀) + Z(Da v, g₁) +
  Z(Da w, g₂))` with `gᵢ` among `Q f`, `Q' f`, `π e`, `π' e`, and the pairings of their kernel
  components with a kernel element `k` as sums of three pairings involving `Q (Z(·, k))` and `π' k`
  (`IsFredholm.sub_orthogonalKerProjection_fderiv_fun_fderiv_orthogonalRightInverse_apply`,
  `ContinuousLinearMap.IsFredholm.inner_fderiv_fun_fderiv_orthogonalRightInverse_apply` and their
  analogues for `π`). Moving the weight across each pairing
  (`TauCeti.eLpNorm_exp_mul_smul_le_of_sq_le_sum_abs_inner`), with the first-derivative estimates
  at both rates `±c`, gives
  `‖exp(c ρ) Q'' f‖₂ ≤ K (‖a''‖∞ + ‖Da v‖∞ ‖Da w‖∞) ‖exp(c ρ) f‖₂`
  (`exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le`) and
  `‖exp(c ρ) π'' e‖₂ ≤ K (‖a''‖∞ + ‖Da v‖∞ ‖Da w‖∞) ‖exp(c ρ) e‖₂`
  (`exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le`), with `K`
  depending only on `m`, `R₀` and `c`.

Derivatives in the parameter of order three and higher, and weighted Sobolev versions of the second
derivative estimates, are not treated here.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter TopologicalSpace ContinuousLinearMap BesselPotentialSpace
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff BesselPotentialSpace

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### Auxiliary facts about the weighted norms -/

/-- **The weighted norm of the zeroth-order part.** Multiplication by `Z(b, ·)`, for an essentially
bounded coefficient `b`, costs at most `‖Z‖ ‖b‖∞` in every weighted norm. -/
private theorem eLpNorm_exp_mul_smul_holderL_le (c : ℝ) (b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b g z) 2 μ⊤ ≤
        ‖gaugeFixedZerothOrder‖₊ * ‖b‖₊ *
          eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤ := by
  rw [holderL_apply_apply, eLpNorm_congr_ae ((gaugeFixedZerothOrder.coeFn_holder (r := 2) b g).mono
    fun z hz ↦ by rw [hz, ← map_smul])]
  refine (eLpNorm_le_eLpNorm_mul_eLpNorm (p := ∞) (q := 2)
    (g := fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) (fun v w ↦ gaugeFixedZerothOrder v w)
    ‖gaugeFixedZerothOrder‖₊ gaugeFixedZerothOrder.continuous₂ (Lp.aestronglyMeasurable b)
    ((continuous_exp_mul_sqrt_add_norm_sq c).aestronglyMeasurable.smul (Lp.aestronglyMeasurable g))
    (.of_forall fun _ ↦ gaugeFixedZerothOrder.le_opNorm₂ _ _)).trans_eq ?_
  rw [← Lp.eNorm_def, eNorm_eq_nnNorm]

/-- **The weak equation of the realization.** At a continuous field `x` with `L∞` class `a`, the
values of every `e ∈ H¹(ℂ)⁴` are a weak solution of `L_x y = L_a e`: tested against compactly
supported `C²` fields, `∫ ⟪e, L_x* η⟫ = ∫ ⟪L_a e, η⟫`. -/
private theorem integral_inner_sobolevFieldValues_gaugeFixedAdjoint
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
    (hax : a =ᵐ[μ⊤] x) (e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪sobolevFieldValues e z, gaugeFixedAdjoint x η z⟫ =
      ∫ z, ⟪sobolevGaugeFixedOperator a e z, η z⟫ := by
  rw [integral_inner_sobolevGaugeFixedOperator hx hax e (hη.of_le (by simp)) hηc]
  refine integral_congr_ae ?_
  filter_upwards [(sobolevFieldValues_ae_eq e).filter_mono
    (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z hz
  rw [hz]

/-! ### The splitting at a vortex of a window -/

/-- At a smooth plane vortex with the degree-`m` end framing, the realization at its `L∞` class is
Fredholm and onto. -/
private theorem isFredholm_and_surjective_sobolevGaugeFixedOperator {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).IsFredholm ∧
      Function.Surjective (sobolevGaugeFixedOperator a) := by
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by simp)
  exact ⟨isFredholm_sobolevGaugeFixedOperator hx1 hsol hlim
    (tendsto_covariantDerivative_cocompact (contDiff_euclidean.1 hx 0).continuous
      ((contDiff_euclidean.1 hx 2).of_le (by simp)) ((contDiff_euclidean.1 hx 3).of_le (by simp))
      hsol hlim 1) hax, sobolevGaugeFixedOperator_surjective hx1 hsol hlim hax⟩

/-- **Exponential decay of the kernel of the realization, uniformly over a window of divisors.**
For every degree `m`, radius `R₀` and rate `c < 1/2` there is a constant `K` with the following
property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end
framing whose zeros lie in the closed disc of radius `R₀` and whose coordinates have bounded
derivatives of every order, and let `a` be its `L∞` class. Then the values of every element `k` of
the kernel of the realization `L_a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` satisfy `‖exp(c ρ) k‖₂ ≤ K ‖k‖₂`. -/
theorem exists_forall_eLpNorm_exp_mul_smul_le_of_mem_ker_of_forall_mem_norm_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ k ∈ (sobolevGaugeFixedOperator a).ker,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues k z) 2 volume ≤
          K * eLpNorm (sobolevFieldValues k) 2 volume := by
  obtain ⟨K, hK⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le m R₀
      hc
  refine ⟨K, fun x D hx hbound hsol hframe hD hD₀ a hax k hk ↦ ?_⟩
  set u := sobolevGaugeFixedKernelEquiv hx.continuous hax ⟨k, hk⟩
  -- The values of `k` are the element `u` of the weak kernel.
  have hku : (sobolevFieldValues k : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] u := by
    filter_upwards [(sobolevFieldValues_ae_eq k).filter_mono
      (ae_mono (Measure.restrict_coe_opens_top _).ge),
      coeFn_sobolevGaugeFixedKernelEquiv hx.continuous hax ⟨k, hk⟩] with z h₁ h₂
    rw [h₁, h₂]
  rw [eLpNorm_congr_ae hku, eLpNorm_congr_ae (hku.mono fun z hz ↦ by rw [hz])]
  exact hK x D hx hbound hsol hframe hD hD₀ u u.property

/-- **The weighted estimate for the orthogonal right inverse, uniformly over a window of
divisors.** For every degree `m`, radius `R₀` and rate `|c| < 1/2` there is a constant `K` with the
following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the
degree-`m` end framing whose zeros lie in the closed disc of radius `R₀`, let `a` be its `L∞`
class, and let `Q` be the right inverse of the realization `L_a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` with values
`L²`-orthogonal to its kernel. Then `‖exp(c ρ) Q f‖₂ ≤ K ‖exp(c ρ) f‖₂` for every `f ∈ L²`, where
either side may be infinite. -/
theorem exists_forall_eLpNorm_exp_mul_smul_orthogonalRightInverse_le_of_forall_mem_norm_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
          (orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator a) f) z) 2 volume ≤
            K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
  have : (μ⊤).IsAddHaarMeasure := by
    rw [Measure.restrict_coe_opens_top]
    infer_instance
  obtain ⟨K, hK⟩ := exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le (μ := μ⊤) m R₀ hc
  refine ⟨K, fun x D hx hsol hframe hD hD₀ a hax f ↦ ?_⟩
  obtain ⟨hT, hsurj⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have hQ := hT.isOrthogonalRightInverse_orthogonalRightInverse sobolevFieldValues_injective hsurj
  set Q := orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator a)
  rw [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ),
    ← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)]
  refine hK x D hx hsol hframe hD hD₀ f (sobolevFieldValues (Q f)) (fun η hη hηc ↦ ?_)
    fun u hu ↦ ?_
  · -- The values of `Q f` solve `L_x y = f` weakly, by integration by parts.
    rw [integral_restrict_coe_opens_top, integral_restrict_coe_opens_top,
      integral_inner_sobolevFieldValues_gaugeFixedAdjoint hx.continuous hax (Q f) hη hηc,
      hQ.rightInverse f]
  · -- A weak solution `u` of `L_x u = 0` is the value of a kernel element `w`, orthogonal to `Q f`.
    obtain ⟨w, hwu, hw0⟩ :=
      exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq hx.continuous hax
        ((Lp.memLp u).mono_measure (Measure.restrict_coe_opens_top _).ge) (f := 0)
        fun η hη hηc ↦ by
          rw [← integral_restrict_coe_opens_top (volume : Measure ℂ), hu η (hη.of_le (by simp)) hηc,
            ← integral_restrict_coe_opens_top (volume : Measure ℂ),
            Lp.integral_inner_coeFn_zero_left]
    have hwu' : (sobolevFieldValues w : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[μ⊤] u := by
      filter_upwards [sobolevFieldValues_ae_eq w,
        (ae_all_iff.2 hwu).filter_mono (ae_mono (Measure.restrict_coe_opens_top _).le)]
        with z h₁ h₂
      rw [h₁]
      ext j
      exact h₂ j
    rw [integral_congr_ae (hwu'.mono fun z hz ↦ by rw [← hz]), ← L2.inner_def]
    exact hQ.inner_eq_zero f w (LinearMap.mem_ker.2 hw0)

/-- `Q (Z(b, y))` costs at most `q ‖Z‖ ‖b‖∞ r N` in a weighted norm in which `Q` costs at most `q`
and `y` at most `r N`. -/
private theorem eLpNorm_exp_mul_smul_sobolevFieldValues_holderL_le {c : ℝ} {q r : ℝ≥0}
    {N : ℝ≥0∞}
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    (hQ : ∀ g, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (Q g) z) 2 μ⊤ ≤
      q * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤)
    (b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) {y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (hy : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2 μ⊤ ≤ r * N) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (Q (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b (sobolevFieldValues y))) z) 2 μ⊤ ≤
        (q * ‖gaugeFixedZerothOrder‖₊ * ‖b‖₊ * r : ℝ≥0) * N := by
  refine (hQ _).trans ?_
  calc _ ≤ (q : ℝ≥0∞) * (‖gaugeFixedZerothOrder‖₊ * ‖b‖₊ * (r * N)) := by
        gcongr
        exact (eLpNorm_exp_mul_smul_holderL_le c b _).trans (by gcongr)
    _ = _ := by
      push_cast
      ring

/-- **The kernel component.** Let `π` be the projection onto the kernel of `T` along its
`L²`-orthogonal complement, and let `y`, `eᵢ`, `Aᵢ` be such that the pairings of `y` with the
kernel are bounded by sums of pairings, `|⟪y, k⟫| ≤ ∑ i ∈ s, |⟪eᵢ k, Aᵢ⟫|`. If the weight costs at
most `kc` on the kernel at the rate `c`, and at most `qᵢ` on `eᵢ k` at the rate `-c` relative to
`‖k‖₂`, then

`‖exp(c ρ) y‖₂ ≤ kc ∑ i ∈ s, qᵢ ‖exp(c ρ) Aᵢ‖₂ + ‖exp(c ρ) (y - π y)‖₂`. -/
private theorem eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le_sum_abs_inner {c : ℝ}
    {kc : ℝ≥0} {ι : Type*} {s : Finset ι} {q : ι → ℝ≥0}
    {T : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    {π : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    (hπ : IsOrthogonalKerProjection sobolevFieldValues T π)
    (hkc : ∀ k ∈ T.ker, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues k z) 2 μ⊤ ≤ kc * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    {e : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) → ι → Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    (he : ∀ k ∈ T.ker, ∀ i ∈ s, eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • e k i z) 2 μ⊤ ≤
      q i * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) {A : ι → Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    (hpair : ∀ k ∈ T.ker, |⟪sobolevFieldValues y, sobolevFieldValues k⟫| ≤
      ∑ i ∈ s, |⟪e k i, A i⟫|) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2 μ⊤ ≤
      kc * ∑ i ∈ s, q i * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • A i z) 2 μ⊤ +
      eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (y - π y) z) 2 μ⊤ := by
  have hp := hπ.mem_ker y
  -- `‖π y‖₂² = ⟪y, π y⟫`, since `y - π y` is orthogonal to the kernel.
  have hinner : ‖sobolevFieldValues (π y)‖ ^ 2 ≤ ∑ i ∈ s, |⟪e (π y) i, A i⟫| :=
    hπ.real_inner_apply_eq_norm_sq y ▸ (le_abs_self _).trans (hpair _ hp)
  refine (le_of_eq_of_le ?_ (Lp.eLpNorm_smul_add_le one_le_two _ _ _)).trans (add_le_add_left
    (TauCeti.eLpNorm_exp_mul_smul_le_of_sq_le_sum_abs_inner (hkc _ hp) (he _ hp) hinner) _)
  rw [← map_add, add_sub_cancel]

/-- **The kernel component for one pairing.** Let `π` be the projection onto the kernel of `T`
along its `L²`-orthogonal complement and `Q` a right inverse of `T`, and let `y`, `A` be such that
the pairings of `y` with the kernel are bounded by `|⟪y, k⟫| ≤ |⟪Q (Z(b, k)), A⟫|`. If the weight
costs at most `kc`, `kn` on the kernel at the rates `c`, `-c`, and at most `qn` on `Q` at the rate
`-c`, then the kernel component of `y` costs at most `kc qn ‖Z‖ ‖b‖∞ kn ‖exp(c ρ) A‖₂`:

`‖exp(c ρ) y‖₂ ≤ kc qn ‖Z‖ ‖b‖∞ kn ‖exp(c ρ) A‖₂ + ‖exp(c ρ) (y - π y)‖₂`. -/
private theorem eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le {c : ℝ}
    {kc kn qn : ℝ≥0}
    {T : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    {π : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    (hπ : IsOrthogonalKerProjection sobolevFieldValues T π)
    (hkc : ∀ k ∈ T.ker, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues k z) 2 μ⊤ ≤ kc * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (hkn : ∀ k ∈ T.ker, eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues k z) 2 μ⊤ ≤ kn * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (hQn : ∀ g, eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (Q g) z) 2
      μ⊤ ≤ qn * eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤)
    (b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    {A : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    (hpair : ∀ k ∈ T.ker, |⟪sobolevFieldValues y, sobolevFieldValues k⟫| ≤
      |⟪sobolevFieldValues (Q (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b (sobolevFieldValues k))),
        A⟫|) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2 μ⊤ ≤
      (kc * (qn * ‖gaugeFixedZerothOrder‖₊ * ‖b‖₊ * kn) : ℝ≥0) *
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • A z) 2 μ⊤ +
      eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (y - π y) z) 2 μ⊤ := by
  -- The weight `exp(-c ρ)` costs at most `qn ‖Z‖ ‖b‖∞ kn` on `Q (Z(b, k))`, relative to `‖k‖₂`.
  simpa [mul_assoc] using eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le_sum_abs_inner
    (s := Finset.univ) (q := fun _ : Unit ↦ qn * ‖gaugeFixedZerothOrder‖₊ * ‖b‖₊ * kn)
    (e := fun k _ ↦ sobolevFieldValues
      (Q (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b (sobolevFieldValues k))))
    (A := fun _ ↦ A) hπ hkc
    (fun k hk _ _ ↦ eLpNorm_exp_mul_smul_sobolevFieldValues_holderL_le hQn b (hkn k hk)) y
    (fun k hk ↦ by simpa using hpair k hk)

/-- The weighted estimates for the kernel of the realization and for its orthogonal right inverse,
at the rates `c` and `-c`, with constants common to a window of divisors, in the volume restricted
to the plane. -/
private theorem exists_forall_ker_and_orthogonalRightInverse_le (m : ℕ) (R₀ : ℝ) {c : ℝ}
    (hc : |c| < 1 / 2) :
    ∃ kc kn qc qn : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      (∀ k ∈ (sobolevGaugeFixedOperator a).ker, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
        sobolevFieldValues k z) 2 μ⊤ ≤ kc * eLpNorm (sobolevFieldValues k) 2 μ⊤) ∧
      (∀ k ∈ (sobolevGaugeFixedOperator a).ker, eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) •
        sobolevFieldValues k z) 2 μ⊤ ≤ kn * eLpNorm (sobolevFieldValues k) 2 μ⊤) ∧
      (∀ g, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
        (orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator a) g) z) 2 μ⊤ ≤
          qc * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤) ∧
      (∀ g, eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
        (orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator a) g) z) 2 μ⊤ ≤
          qn * eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤) := by
  obtain ⟨kc, hkc⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_le_of_mem_ker_of_forall_mem_norm_le m R₀
      ((le_abs_self c).trans_lt hc)
  obtain ⟨kn, hkn⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_le_of_mem_ker_of_forall_mem_norm_le m R₀
      ((neg_le_abs c).trans_lt hc)
  obtain ⟨qc, hqc⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀ hc
  obtain ⟨qn, hqn⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀
      (c := -c) (by rwa [abs_neg])
  refine ⟨kc, kn, qc, qn, fun x D hx hbound hsol hframe hD hD₀ a hax ↦
    ⟨fun k hk ↦ ?_, fun k hk ↦ ?_, fun g ↦ ?_, fun g ↦ ?_⟩⟩ <;>
    simp only [eLpNorm_restrict_coe_opens_top]
  exacts [hkc x D hx hbound hsol hframe hD hD₀ a hax k hk,
    hkn x D hx hbound hsol hframe hD hD₀ a hax k hk, hqc x D hx hsol hframe hD hD₀ a hax g,
    hqn x D hx hsol hframe hD hD₀ a hax g]

/-- **The weighted estimate for the orthogonal kernel projection, uniformly over a window of
divisors.** For every degree `m`, radius `R₀` and rate `|c| < 1/2` there is a constant `K` with the
following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the
degree-`m` end framing whose zeros lie in the closed disc of radius `R₀` and whose coordinates have
bounded derivatives of every order, let `a` be its `L∞` class, and let `π` be the projection of
`H¹(ℂ)⁴` onto the kernel of the realization `L_a` along its `L²`-orthogonal complement. Then every
`e ∈ H¹(ℂ)⁴` satisfies `‖exp(c ρ) π e‖₂ ≤ K ‖exp(c ρ) e‖₂`, where either side may be infinite. -/
theorem exists_forall_eLpNorm_exp_mul_smul_orthogonalKerProjection_le_of_forall_mem_norm_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
          (orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator a) e) z) 2 volume ≤
            K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2
              volume := by
  obtain ⟨kc, kn, _, _, hest⟩ := exists_forall_ker_and_orthogonalRightInverse_le m R₀ hc
  refine ⟨kc * kn, fun x D hx hbound hsol hframe hD hD₀ a hax e ↦ ?_⟩
  obtain ⟨hkc, hkn, -, -⟩ := hest x D hx hbound hsol hframe hD hD₀ a hax
  obtain ⟨hT, -⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection sobolevFieldValues_injective
    (sobolevGaugeFixedOperator a)
  set π := orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator a)
  have hk := hπ.mem_ker e
  rw [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ),
    ← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)]
  -- `‖π e‖₂² = ⟪π e, e⟫`, since `e - π e` is orthogonal to the kernel.
  have hinner : ‖sobolevFieldValues (π e)‖ ^ 2 ≤
      |⟪sobolevFieldValues (π e), sobolevFieldValues e⟫| := by
    rw [real_inner_comm, hπ.real_inner_apply_eq_norm_sq e]
    exact le_abs_self _
  exact TauCeti.eLpNorm_exp_mul_smul_le_of_sq_le_abs_inner (hkc (π e) hk) (hkn (π e) hk) hinner

/-- Along a family of coefficients differentiable at `p₀`, whose value at `p₀` is the class of a
smooth plane vortex with the degree-`m` end framing, the realizations are differentiable at `p₀`,
and at `p₀` the realization is Fredholm and onto, with its orthogonal kernel projection. -/
private theorem isFredholm_and_differentiableAt_sobolevGaugeFixedOperator {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X} (hax : a p₀ =ᵐ[μ⊤] x)
    (ha : DifferentiableAt ℝ a p₀) :
    (sobolevGaugeFixedOperator (a p₀)).IsFredholm ∧
      Function.Surjective (sobolevGaugeFixedOperator (a p₀)) ∧
      DifferentiableAt ℝ (fun p ↦ sobolevGaugeFixedOperator (a p)) p₀ ∧
      IsOrthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
        (orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))) := by
  obtain ⟨hT, hsurj⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have := hT.finite_ker
  exact ⟨hT, hsurj,
    differentiableAt_sobolevGaugeFixedOperator_comp ha,
    isOrthogonalKerProjection_orthogonalKerProjection sobolevFieldValues_injective _⟩

/-- **The weighted estimate for the parameter derivative of the orthogonal right inverses,
uniformly over a window of divisors.** For every degree `m`, radius `R₀` and rate `|c| < 1/2`
there is a constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a
smooth plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of radius
`R₀` and whose coordinates have bounded derivatives of every order. Let `a` be a family of `L∞`
coefficients, differentiable at `p₀`, with `a p₀` the class of `x`, and let `Q p` be the right
inverse of the realization `L_(a p)` with values `L²`-orthogonal to its kernel. Then the
derivative `Q'` of `Q` at `p₀` in the direction `v` satisfies

`‖exp(c ρ) Q' f‖₂ ≤ K ‖Da(p₀) v‖∞ ‖exp(c ρ) f‖₂`

for every `f ∈ L²`, where either side may be infinite. -/
theorem exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        DifferentiableAt ℝ a p₀ → ∀ (v : X) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤),
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
          (fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
            (sobolevGaugeFixedOperator (a p))) p₀ v f) z) 2 volume ≤
          K * ‖fderiv ℝ a p₀ v‖₊ * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2
            volume := by
  obtain ⟨kc, kn, qc, qn, hest⟩ := exists_forall_ker_and_orthogonalRightInverse_le m R₀ hc
  set Z := ‖gaugeFixedZerothOrder‖₊
  refine ⟨kc * (qn * Z * kn) * qc + qc * Z * qc, ?_⟩
  intro x D hx hbound hsol hframe hD hD₀ X _ _ a p₀ hax ha v f
  obtain ⟨hkc', hkn', hqc', hqn'⟩ := hest x D hx hbound hsol hframe hD hD₀ (a p₀) hax
  obtain ⟨hT, hsurj, hd, hπ⟩ :=
    isFredholm_and_differentiableAt_sobolevGaugeFixedOperator hx hsol hframe hax ha
  -- The component of `y = Q' f` orthogonal to the kernel is `y - π y = -Q (T' (Q f))`, and its
  -- kernel component is determined by `⟪y, k⟫ = ⟪Q f, Q (T' k)⟫`, where `T' w = Z(b, w)`.
  have hsplit := hT.sub_orthogonalKerProjection_fderiv_orthogonalRightInverse_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hd v f
  have hpair := fun k (hk : k ∈ (sobolevGaugeFixedOperator (a p₀)).ker) ↦
    hT.inner_fderiv_orthogonalRightInverse_apply (T := fun p ↦ sobolevGaugeFixedOperator (a p))
      sobolevFieldValues_injective hsurj hd v f hk
  simp only [fderiv_sobolevGaugeFixedOperator_comp_apply ha v] at hsplit hpair
  set b := fderiv ℝ a p₀ v
  set Q := orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  set π := orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  set y := fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
    (sobolevGaugeFixedOperator (a p))) p₀ v f
  rw [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ),
    ← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)]
  have hperp : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues (y - π y) z) 2 μ⊤ ≤
        (qc * Z * ‖b‖₊ * qc : ℝ≥0) *
          eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ⊤ := by
    rw [hsplit, map_neg, Lp.eLpNorm_smul_neg]
    exact eLpNorm_exp_mul_smul_sobolevFieldValues_holderL_le hqc' b (hqc' f)
  refine (eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le hπ hkc' hkn' hqn' b y
    (A := sobolevFieldValues (Q f)) fun k hk ↦ by rw [hpair k hk, real_inner_comm]).trans ?_
  calc _ ≤ (kc * (qn * Z * ‖b‖₊ * kn) : ℝ≥0) * ((qc : ℝ≥0∞) *
          eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ⊤) +
        (qc * Z * ‖b‖₊ * qc : ℝ≥0) *
          eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ⊤ :=
      add_le_add (mul_le_mul_right (hqc' f) _) hperp
    _ = _ := by
      push_cast
      ring

/-- If `‖exp(c ρ) π e‖₂ ≤ kπ ‖exp(c ρ) e‖₂`, then
`‖exp(c ρ) (e - π e)‖₂ ≤ (1 + kπ) ‖exp(c ρ) e‖₂`. -/
private theorem eLpNorm_exp_mul_smul_sobolevFieldValues_sub_le {c : ℝ} {kπ : ℝ≥0}
    {π : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    {e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (h : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (π e) z) 2 μ⊤ ≤
      kπ * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 μ⊤) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (e - π e) z) 2 μ⊤ ≤
      ((1 + kπ : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 μ⊤ := by
  rw [map_sub, sub_eq_add_neg, ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]
  refine (Lp.eLpNorm_smul_add_le one_le_two _ _ _).trans (add_le_add le_rfl ?_)
  rwa [Lp.eLpNorm_smul_neg]

/-- **The weighted estimate for the parameter derivative of the orthogonal kernel projections,
uniformly over a window of divisors.** For every degree `m`, radius `R₀` and rate `|c| < 1/2`
there is a constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a
smooth plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of radius
`R₀` and whose coordinates have bounded derivatives of every order. Let `a` be a family of `L∞`
coefficients, differentiable at `p₀`, with `a p₀` the class of `x`, and let `π p` be the projection
of `H¹(ℂ)⁴` onto the kernel of the realization `L_(a p)` along its `L²`-orthogonal complement. Then
the derivative `π'` of `π` at `p₀` in the direction `v` satisfies

`‖exp(c ρ) π' e‖₂ ≤ K ‖Da(p₀) v‖∞ ‖exp(c ρ) e‖₂`

for every `e ∈ H¹(ℂ)⁴`, where either side may be infinite. -/
theorem exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        DifferentiableAt ℝ a p₀ → ∀ (v : X) (e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
          (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
            (sobolevGaugeFixedOperator (a p))) p₀ v e) z) 2 volume ≤
          K * ‖fderiv ℝ a p₀ v‖₊ *
            eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 volume := by
  obtain ⟨kc, kn, qc, qn, hest⟩ := exists_forall_ker_and_orthogonalRightInverse_le m R₀ hc
  obtain ⟨kπ, hkπ⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalKerProjection_le_of_forall_mem_norm_le
      m R₀ hc
  set Z := ‖gaugeFixedZerothOrder‖₊
  refine ⟨kc * (qn * Z * kn) * (1 + kπ) + qc * Z * kπ, ?_⟩
  intro x D hx hbound hsol hframe hD hD₀ X _ _ a p₀ hax ha v e
  obtain ⟨hkc', hkn', hqc', hqn'⟩ := hest x D hx hbound hsol hframe hD hD₀ (a p₀) hax
  obtain ⟨hT, hsurj, hd, hπ⟩ :=
    isFredholm_and_differentiableAt_sobolevGaugeFixedOperator hx hsol hframe hax ha
  -- The component of `y = π' e` orthogonal to the kernel is `y - π y = -Q (T' (π e))`, and its
  -- kernel component is determined by `⟪y, k⟫ = -⟪e - π e, Q (T' k)⟫`, where `T' w = Z(b, w)`.
  have hsplit := hT.sub_orthogonalKerProjection_fderiv_orthogonalKerProjection_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hd v e
  have hpair := fun k (hk : k ∈ (sobolevGaugeFixedOperator (a p₀)).ker) ↦
    hT.inner_fderiv_orthogonalKerProjection_apply (T := fun p ↦ sobolevGaugeFixedOperator (a p))
      sobolevFieldValues_injective hsurj hd v e hk
  simp only [fderiv_sobolevGaugeFixedOperator_comp_apply ha v] at hsplit hpair
  have hkπ' := hkπ x D hx hbound hsol hframe hD hD₀ (a p₀) hax e
  set b := fderiv ℝ a p₀ v
  set Q := orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  set π := orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  set y := fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
    (sobolevGaugeFixedOperator (a p))) p₀ v e
  rw [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ),
    ← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)] at hkπ'
  rw [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ),
    ← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)]
  set N := eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 μ⊤
  have hperp : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues (y - π y) z) 2 μ⊤ ≤ (qc * Z * ‖b‖₊ * kπ : ℝ≥0) * N := by
    rw [hsplit, map_neg, Lp.eLpNorm_smul_neg]
    exact eLpNorm_exp_mul_smul_sobolevFieldValues_holderL_le hqc' b hkπ'
  -- The field `A = e - π e` paired with the kernel component has `‖A‖_c ≤ (1 + kπ) ‖e‖_c`.
  have hA := eLpNorm_exp_mul_smul_sobolevFieldValues_sub_le hkπ'
  refine (eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le hπ hkc' hkn' hqn' b y
    (A := sobolevFieldValues (e - π e))
    fun k hk ↦ by rw [hpair k hk, abs_neg, real_inner_comm]).trans ?_
  calc _ ≤ (kc * (qn * Z * ‖b‖₊ * kn) : ℝ≥0) * (((1 + kπ : ℝ≥0) : ℝ≥0∞) * N) +
        (qc * Z * ‖b‖₊ * kπ : ℝ≥0) * N :=
      add_le_add (mul_le_mul_right hA _) hperp
    _ = _ := by
      push_cast
      ring

/-! ### The weighted estimates for the second parameter derivatives -/

/-- Along a family of coefficients `C²` at `p₀`, whose value at `p₀` is the class of a smooth plane
vortex with the degree-`m` end framing, the realizations are `C²` at `p₀`, and at `p₀` the
realization is Fredholm and onto, with its orthogonal kernel projection. -/
private theorem isFredholm_and_contDiffAt_sobolevGaugeFixedOperator {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X} (hax : a p₀ =ᵐ[μ⊤] x)
    (ha : ContDiffAt ℝ 2 a p₀) :
    (sobolevGaugeFixedOperator (a p₀)).IsFredholm ∧
      Function.Surjective (sobolevGaugeFixedOperator (a p₀)) ∧ DifferentiableAt ℝ a p₀ ∧
      ContDiffAt ℝ 2 (fun p ↦ sobolevGaugeFixedOperator (a p)) p₀ ∧
      IsOrthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
        (orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))) := by
  have hd : DifferentiableAt ℝ a p₀ := ha.differentiableAt (by simp)
  obtain ⟨hT, hsurj, -, hπ⟩ :=
    isFredholm_and_differentiableAt_sobolevGaugeFixedOperator hx hsol hframe hax hd
  exact ⟨hT, hsurj, hd, contDiff_sobolevGaugeFixedOperator.contDiffAt.comp p₀ ha, hπ⟩

/-- `Q (Z(b₀, g₀) + Z(b₁, g₁) + Z(b₂, g₂))` costs at most `q ‖Z‖ (‖b₀‖∞ r₀ + ‖b₁‖∞ r₁ + ‖b₂‖∞ r₂) N`
in a weighted norm in which `Q` costs at most `q` and each `gᵢ` at most `rᵢ N`. -/
private theorem eLpNorm_exp_mul_smul_sobolevFieldValues_holderL_add_add_le {c : ℝ} {q : ℝ≥0}
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    (hQ : ∀ g, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (Q g) z) 2 μ⊤ ≤
      q * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤)
    (b₀ b₁ b₂ : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    {g₀ g₁ g₂ : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2} {N : ℝ≥0∞} {r₀ r₁ r₂ : ℝ≥0}
    (h₀ : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues g₀ z) 2 μ⊤ ≤ r₀ * N)
    (h₁ : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues g₁ z) 2 μ⊤ ≤ r₁ * N)
    (h₂ : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues g₂ z) 2 μ⊤ ≤
      r₂ * N) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (Q (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₀ (sobolevFieldValues g₀) +
        gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₁ (sobolevFieldValues g₁) +
        gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₂ (sobolevFieldValues g₂))) z) 2 μ⊤ ≤
      (q * ‖gaugeFixedZerothOrder‖₊ * (‖b₀‖₊ * r₀ + ‖b₁‖₊ * r₁ + ‖b₂‖₊ * r₂) : ℝ≥0) * N := by
  set Z := ‖gaugeFixedZerothOrder‖₊
  have hb (b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) {g : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
      {r : ℝ≥0} (hg : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues g z) 2
        μ⊤ ≤ r * N) :
      eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
        gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b (sobolevFieldValues g) z) 2 μ⊤ ≤
          (Z * ‖b‖₊ * r : ℝ≥0) * N := by
    refine (eLpNorm_exp_mul_smul_holderL_le c b _).trans ?_
    calc _ ≤ (Z * ‖b‖₊ : ℝ≥0∞) * (r * N) := by gcongr
      _ = _ := by push_cast; ring
  refine (hQ _).trans ?_
  calc _ ≤ (q : ℝ≥0∞) * ((Z * ‖b₀‖₊ * r₀ : ℝ≥0) * N + (Z * ‖b₁‖₊ * r₁ : ℝ≥0) * N +
        (Z * ‖b₂‖₊ * r₂ : ℝ≥0) * N) := by
        gcongr
        refine (Lp.eLpNorm_smul_add_le one_le_two _ _ _).trans (add_le_add ?_ (hb b₂ h₂))
        exact (Lp.eLpNorm_smul_add_le one_le_two _ _ _).trans (add_le_add (hb b₀ h₀) (hb b₁ h₁))
    _ = _ := by push_cast; ring

/-- **The second-derivative estimate.** Let `π` be the projection onto the kernel of `T` along its
`L²`-orthogonal complement and `Q` a right inverse of `T`, with weighted bounds at the rates `c`
and `-c` on the kernel and on `Q`, and let `P₁`, `P₂` cost at most `p₁`, `p₂` from `L²` on the
kernel at the rate `-c`. Suppose that the component of `y` orthogonal to the kernel is
`-Q (Z(b₀, g₀) + Z(b₁, g₁) + Z(b₂, g₂))` and that its pairings with the kernel are bounded by
`|⟪Q (Z(b₀, k) + Z(b₁, P₁ k) + Z(b₂, P₂ k)), A₀⟫| + |⟪P₁ k, A₁⟫| + |⟪P₂ k, A₂⟫|`, where the `gᵢ`
and `Aᵢ` cost at most `rᵢ N` and `sᵢ N` at the rate `c`. Then `y` costs at most an explicit
multiple of `N` at the rate `c`. -/
private theorem eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_sub_and_abs_inner_le {c : ℝ}
    {kc kn qc qn p₁ p₂ r₀ r₁ r₂ s₀ s₁ s₂ : ℝ≥0} {N : ℝ≥0∞}
    {T : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    {π : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    (hπ : IsOrthogonalKerProjection sobolevFieldValues T π)
    (hkc : ∀ k ∈ T.ker, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues k z) 2 μ⊤ ≤ kc * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (hkn : ∀ k ∈ T.ker, eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues k z) 2 μ⊤ ≤ kn * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (hQc : ∀ g, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (Q g) z) 2
      μ⊤ ≤ qc * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤)
    (hQn : ∀ g, eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (Q g) z) 2
      μ⊤ ≤ qn * eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤)
    {P₁ P₂ : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) → (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    (hP₁ : ∀ k ∈ T.ker, eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues (P₁ k) z) 2 μ⊤ ≤ p₁ * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (hP₂ : ∀ k ∈ T.ker, eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues (P₂ k) z) 2 μ⊤ ≤ p₂ * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (b₀ b₁ b₂ : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    {y g₀ g₁ g₂ : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    {A₀ A₁ A₂ : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    (hg₀ : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues g₀ z) 2 μ⊤ ≤ r₀ * N)
    (hg₁ : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues g₁ z) 2 μ⊤ ≤ r₁ * N)
    (hg₂ : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues g₂ z) 2 μ⊤ ≤ r₂ * N)
    (hA₀ : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • A₀ z) 2 μ⊤ ≤ s₀ * N)
    (hA₁ : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • A₁ z) 2 μ⊤ ≤ s₁ * N)
    (hA₂ : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • A₂ z) 2 μ⊤ ≤ s₂ * N)
    (hsplit : y - π y = -Q (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₀ (sobolevFieldValues g₀) +
      gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₁ (sobolevFieldValues g₁) +
      gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₂ (sobolevFieldValues g₂)))
    (hpair : ∀ k ∈ T.ker, |⟪sobolevFieldValues y, sobolevFieldValues k⟫| ≤
      |⟪sobolevFieldValues (Q (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₀ (sobolevFieldValues k) +
        gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₁ (sobolevFieldValues (P₁ k)) +
        gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₂ (sobolevFieldValues (P₂ k)))), A₀⟫| +
      |⟪sobolevFieldValues (P₁ k), A₁⟫| + |⟪sobolevFieldValues (P₂ k), A₂⟫|) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2 μ⊤ ≤
      (kc * (qn * ‖gaugeFixedZerothOrder‖₊ * (‖b₀‖₊ * kn + ‖b₁‖₊ * p₁ + ‖b₂‖₊ * p₂) * s₀ +
          p₁ * s₁ + p₂ * s₂) +
        qc * ‖gaugeFixedZerothOrder‖₊ * (‖b₀‖₊ * r₀ + ‖b₁‖₊ * r₁ + ‖b₂‖₊ * r₂) : ℝ≥0) * N := by
  set Z := ‖gaugeFixedZerothOrder‖₊
  -- The component orthogonal to the kernel.
  have hperp : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues (y - π y) z) 2 μ⊤ ≤
        (qc * Z * (‖b₀‖₊ * r₀ + ‖b₁‖₊ * r₁ + ‖b₂‖₊ * r₂) : ℝ≥0) * N := by
    rw [hsplit, map_neg, Lp.eLpNorm_smul_neg]
    exact eLpNorm_exp_mul_smul_sobolevFieldValues_holderL_add_add_le hQc b₀ b₁ b₂ hg₀ hg₁ hg₂
  -- The kernel component is bounded by the three pairings.
  have hker := eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le_sum_abs_inner
    (s := Finset.univ) (q := ![qn * Z * (‖b₀‖₊ * kn + ‖b₁‖₊ * p₁ + ‖b₂‖₊ * p₂), p₁, p₂])
    (e := fun k ↦ ![sobolevFieldValues (Q (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₀
      (sobolevFieldValues k) +
      gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₁ (sobolevFieldValues (P₁ k)) +
      gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₂ (sobolevFieldValues (P₂ k)))),
      sobolevFieldValues (P₁ k), sobolevFieldValues (P₂ k)])
    (A := ![A₀, A₁, A₂]) hπ hkc
    (fun k hk i _ ↦ by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exacts [eLpNorm_exp_mul_smul_sobolevFieldValues_holderL_add_add_le hQn b₀ b₁ b₂ (hkn k hk)
        (hP₁ k hk) (hP₂ k hk), hP₁ k hk, hP₂ k hk])
    y fun k hk ↦ by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exact hpair k hk
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hker
  refine hker.trans ?_
  calc _ ≤ (kc : ℝ≥0∞) * ((qn * Z * (‖b₀‖₊ * kn + ‖b₁‖₊ * p₁ + ‖b₂‖₊ * p₂) : ℝ≥0) * (s₀ * N) +
        p₁ * (s₁ * N) + p₂ * (s₂ * N)) +
        (qc * Z * (‖b₀‖₊ * r₀ + ‖b₁‖₊ * r₁ + ‖b₂‖₊ * r₂) : ℝ≥0) * N := by gcongr
    _ = _ := by push_cast; ring

/-- A constant `C = A x + B y z` is at most `(A + B) (x + y z)`, so `C N ≤ (A + B) (x + y z) N`. -/
private theorem coe_mul_le_coe_add_mul_add_mul {A B C x y z : ℝ≥0} (h : C = A * x + B * (y * z))
    (N : ℝ≥0∞) : (C : ℝ≥0∞) * N ≤ ((A + B : ℝ≥0) : ℝ≥0∞) * (x + y * z) * N := by
  gcongr
  norm_cast
  rw [h, add_mul, mul_add, mul_add]
  exact add_le_add (le_add_of_nonneg_right zero_le) (le_add_of_nonneg_left zero_le)

/-- **The weighted estimate for the second parameter derivative of the orthogonal right inverses,
uniformly over a window of divisors.** For every degree `m`, radius `R₀` and rate `|c| < 1/2`
there is a constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a
smooth plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of radius
`R₀` and whose coordinates have bounded derivatives of every order. Let `a` be a family of `L∞`
coefficients, `C²` at `p₀`, with `a p₀` the class of `x`, and let `Q p` be the right inverse of
the realization `L_(a p)` with values `L²`-orthogonal to its kernel. Write `Q''` for the derivative
at `p₀` along `w` of `p ↦ DQ(p) v` and `a''` for that of `p ↦ Da(p) v`. Then

`‖exp(c ρ) Q'' f‖₂ ≤ K (‖a''‖∞ + ‖Da(p₀) v‖∞ ‖Da(p₀) w‖∞) ‖exp(c ρ) f‖₂`

for every `f ∈ L²`, where either side may be infinite. -/
theorem exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        ContDiffAt ℝ 2 a p₀ → ∀ (v w : X) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤),
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
          (fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
            (sobolevGaugeFixedOperator (a p))) p v f) p₀ w) z) 2 volume ≤
          K * (‖fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w‖₊ +
            ‖fderiv ℝ a p₀ v‖₊ * ‖fderiv ℝ a p₀ w‖₊) *
            eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
  obtain ⟨kc, kn, qc, qn, hest⟩ := exists_forall_ker_and_orthogonalRightInverse_le m R₀ hc
  obtain ⟨KQ, hKQ⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le
      m R₀ hc
  obtain ⟨Kπ, hKπ⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le
      m R₀ (c := -c) (by rwa [abs_neg])
  set Z := ‖gaugeFixedZerothOrder‖₊
  refine ⟨kc * qn * Z * kn * qc + qc * Z * qc +
    2 * (kc * qn * Z * Kπ * kn * qc + kc * Kπ * kn * KQ + qc * Z * KQ), ?_⟩
  intro x D hx hbound hsol hframe hD hD₀ X _ _ a p₀ hax ha v w f
  obtain ⟨hkc, hkn, hqc, hqn⟩ := hest x D hx hbound hsol hframe hD hD₀ (a p₀) hax
  obtain ⟨hT, hsurj, hd, hT2, hπ⟩ :=
    isFredholm_and_contDiffAt_sobolevGaugeFixedOperator hx hsol hframe hax ha
  -- The splitting and kernel pairings of `Q''`, with `T' = Z(Da v, ·)` and `T'' = Z(a'', ·)`.
  have hsplit := hT.sub_orthogonalKerProjection_fderiv_fun_fderiv_orthogonalRightInverse_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hT2 v w f
  have hpair := fun k (hk : k ∈ (sobolevGaugeFixedOperator (a p₀)).ker) ↦
    hT.inner_fderiv_fun_fderiv_orthogonalRightInverse_apply
      (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hT2 v w f
      hk
  simp only [fderiv_sobolevGaugeFixedOperator_comp_apply hd,
    fderiv_fun_fderiv_sobolevGaugeFixedOperator_comp_apply ha] at hsplit hpair
  -- The first derivatives of `Q` at the rate `c` and of `π` at the rate `-c`.
  set bv := fderiv ℝ a p₀ v
  set bw := fderiv ℝ a p₀ w
  have hQ' (u : X) (g) := hKQ x D hx hbound hsol hframe hD hD₀ hax hd u g
  have hπ' (u : X) (k) := hKπ x D hx hbound hsol hframe hD hD₀ hax hd u k
  simp only [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)] at hQ' hπ' ⊢
  have hP (u : X) (k) (hk : k ∈ (sobolevGaugeFixedOperator (a p₀)).ker) :=
    (hπ' u k).trans (mul_le_mul_right (hkn k hk) _)
  set N := eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ⊤
  refine (eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_sub_and_abs_inner_le hπ hkc hkn hqc hqn
    (p₁ := Kπ * ‖bw‖₊ * kn) (p₂ := Kπ * ‖bv‖₊ * kn) (r₀ := qc) (r₁ := KQ * ‖bw‖₊)
    (r₂ := KQ * ‖bv‖₊) (s₀ := qc) (s₁ := KQ * ‖bv‖₊) (s₂ := KQ * ‖bw‖₊)
    (fun k hk ↦ (hP w k hk).trans_eq (by push_cast; ring))
    (fun k hk ↦ (hP v k hk).trans_eq (by push_cast; ring))
    _ _ _ (hqc f) ((hQ' w f).trans_eq (by push_cast; ring))
    ((hQ' v f).trans_eq (by push_cast; ring)) (hqc f)
    ((hQ' v f).trans_eq (by push_cast; ring)) ((hQ' w f).trans_eq (by push_cast; ring)) hsplit
    fun k hk ↦ ?_).trans ?_
  · have hcomm (u u' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) : |⟪u, u'⟫| ≤ |⟪u', u⟫| :=
      (congrArg abs (real_inner_comm u' u)).le
    rw [hpair k hk]
    exact (abs_sub _ _).trans
      (add_le_add ((abs_sub _ _).trans (add_le_add (hcomm _ _) (hcomm _ _))) (hcomm _ _))
  · exact coe_mul_le_coe_add_mul_add_mul (by ring) _

/-- **The weighted estimate for the second parameter derivative of the orthogonal kernel
projections, uniformly over a window of divisors.** For every degree `m`, radius `R₀` and rate
`|c| < 1/2` there is a constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let
`x` be a smooth plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of
radius `R₀` and whose coordinates have bounded derivatives of every order. Let `a` be a family of
`L∞` coefficients, `C²` at `p₀`, with `a p₀` the class of `x`, and let `π p` be the projection of
`H¹(ℂ)⁴` onto the kernel of the realization `L_(a p)` along its `L²`-orthogonal complement. Write
`π''` for the derivative at `p₀` along `w` of `p ↦ Dπ(p) v` and `a''` for that of `p ↦ Da(p) v`.
Then

`‖exp(c ρ) π'' e‖₂ ≤ K (‖a''‖∞ + ‖Da(p₀) v‖∞ ‖Da(p₀) w‖∞) ‖exp(c ρ) e‖₂`

for every `e ∈ H¹(ℂ)⁴`, where either side may be infinite. -/
theorem exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        ContDiffAt ℝ 2 a p₀ → ∀ (v w : X) (e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
          (fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
            (sobolevGaugeFixedOperator (a p))) p v e) p₀ w) z) 2 volume ≤
          K * (‖fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w‖₊ +
            ‖fderiv ℝ a p₀ v‖₊ * ‖fderiv ℝ a p₀ w‖₊) *
            eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 volume := by
  obtain ⟨kc, kn, qc, qn, hest⟩ := exists_forall_ker_and_orthogonalRightInverse_le m R₀ hc
  obtain ⟨kπ, hkπ⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalKerProjection_le_of_forall_mem_norm_le m R₀ hc
  obtain ⟨Kc, hKc⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le
      m R₀ hc
  obtain ⟨Kn, hKn⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le
      m R₀ (c := -c) (by rwa [abs_neg])
  set Z := ‖gaugeFixedZerothOrder‖₊
  refine ⟨kc * qn * Z * kn * (1 + kπ) + qc * Z * kπ +
    2 * (kc * qn * Z * Kn * kn * (1 + kπ) + kc * Kn * kn * Kc + qc * Z * Kc), ?_⟩
  intro x D hx hbound hsol hframe hD hD₀ X _ _ a p₀ hax ha v w e
  obtain ⟨hkc, hkn, hqc, hqn⟩ := hest x D hx hbound hsol hframe hD hD₀ (a p₀) hax
  obtain ⟨hT, hsurj, hd, hT2, hπ⟩ :=
    isFredholm_and_contDiffAt_sobolevGaugeFixedOperator hx hsol hframe hax ha
  -- The splitting and kernel pairings of `π''`, with `T' = Z(Da v, ·)` and `T'' = Z(a'', ·)`.
  have hsplit := hT.sub_orthogonalKerProjection_fderiv_fun_fderiv_orthogonalKerProjection_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hT2 v w e
  have hpair := fun k (hk : k ∈ (sobolevGaugeFixedOperator (a p₀)).ker) ↦
    hT.inner_fderiv_fun_fderiv_orthogonalKerProjection_apply
      (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hT2 v w e
      hk
  simp only [fderiv_sobolevGaugeFixedOperator_comp_apply hd,
    fderiv_fun_fderiv_sobolevGaugeFixedOperator_comp_apply ha] at hsplit hpair
  set bv := fderiv ℝ a p₀ v
  set bw := fderiv ℝ a p₀ w
  have hπe := hkπ x D hx hbound hsol hframe hD hD₀ (a p₀) hax e
  have hπ'c (u : X) := hKc x D hx hbound hsol hframe hD hD₀ hax hd u e
  have hπ'n (u : X) (k) := hKn x D hx hbound hsol hframe hD hD₀ hax hd u k
  simp only [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)] at hπe hπ'c hπ'n ⊢
  have hP (u : X) (k) (hk : k ∈ (sobolevGaugeFixedOperator (a p₀)).ker) :=
    (hπ'n u k).trans (mul_le_mul_right (hkn k hk) _)
  set N := eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 μ⊤
  refine (eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_sub_and_abs_inner_le hπ hkc hkn hqc hqn
    (p₁ := Kn * ‖bw‖₊ * kn) (p₂ := Kn * ‖bv‖₊ * kn) (r₀ := kπ) (r₁ := Kc * ‖bw‖₊)
    (r₂ := Kc * ‖bv‖₊) (s₀ := 1 + kπ) (s₁ := Kc * ‖bv‖₊) (s₂ := Kc * ‖bw‖₊)
    (fun k hk ↦ (hP w k hk).trans_eq (by push_cast; ring))
    (fun k hk ↦ (hP v k hk).trans_eq (by push_cast; ring))
    _ _ _ hπe ((hπ'c w).trans_eq (by push_cast; ring)) ((hπ'c v).trans_eq (by push_cast; ring))
    (eLpNorm_exp_mul_smul_sobolevFieldValues_sub_le hπe)
    ((hπ'c v).trans_eq (by push_cast; ring)) ((hπ'c w).trans_eq (by push_cast; ring)) hsplit
    fun k hk ↦ ?_).trans ?_
  · have hcomm (u u' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) : |⟪u, u'⟫| ≤ |⟪u', u⟫| :=
      (congrArg abs (real_inner_comm u' u)).le
    rw [hpair k hk]
    exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
      (add_le_add ((abs_neg _).trans_le (hcomm _ _)) (hcomm _ _))) (hcomm _ _))
  · exact coe_mul_le_coe_add_mul_add_mul (by ring) _

/-! ### The weighted Sobolev estimate for the parameter derivative -/

/-- An `L∞` class equal almost everywhere to a field whose coordinates are bounded by `M` has
norm at most `2 M`. -/
private theorem norm_le_two_mul_of_ae_eq_of_forall_norm_apply_le
    {b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {β : ℂ → EuclideanSpace ℝ (Fin 4)} {M : ℝ}
    (hb : b =ᵐ[μ⊤] β) (hβb : ∀ i z, ‖β z i‖ ≤ M) : ‖b‖ ≤ 2 * M := by
  have h := Lp.norm_le_sqrt_card_mul_of_ae_norm_apply_le ((norm_nonneg _).trans (hβb 0 0))
    (hb.mono fun z hz i ↦ hz ▸ hβb i z)
  rwa [Fintype.card_fin, Nat.cast_ofNat, show √(4 : ℝ) = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]] at h

/-- **The coordinates of the zeroth-order term.** For every order `k` there is a constant `C` with
the following property. If `β` is a smooth field whose coordinates have derivatives bounded by `M`
through order `k`, and `u : Fin 4 → H^(k+1)(ℂ)` are coordinates of a field `Y`, then
`-Z(β, Y)` has coordinates `W : Fin 4 → H^k(ℂ)` with `‖W‖ ≤ C M ‖u‖`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_neg_gaugeFixedZerothOrder (k : ℕ) :
    ∃ C ≥ 0, ∀ β : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ β → ∀ M : ℝ,
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) →
      ∀ (Y : ℂ → EuclideanSpace ℝ (Fin 4)) (u : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
      (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (Y z a : ℂ)) →
      ∃ W : Fin 4 → H^{(k : ℝ)}(ℂ),
        (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (W a)) =ᵐ[volume]
          fun z ↦ ((-gaugeFixedZerothOrder (β z) (Y z)) a : ℂ)) ∧ ‖W‖ ≤ C * M * ‖u‖ := by
  obtain ⟨C, hC, hCb⟩ := exists_forall_exists_inclusionLp_ae_eq_add_mulVec (le_refl k)
  refine ⟨C, hC, fun β hβ M hβb Y u hu ↦ ?_⟩
  have hZ (i j : Fin 4) :=
    contDiff_and_norm_iteratedFDeriv_gaugeFixedZerothOrderMatrix_le hβ hβb i j
  have hk : (k : ℝ) ≤ k + 1 := by linarith
  -- `-Z(β, Y)` is `0 + A Y` for the matrix `A = -gaugeFixedZerothOrderMatrix β`.
  obtain ⟨W, hW, hWn⟩ := hCb (fun i j z ↦ -gaugeFixedZerothOrderMatrix (β z) i j)
    (fun i j ↦ (hZ i j).1.neg) M
    (fun i j n hn z ↦ (norm_iteratedFDeriv_fun_neg _ n z).trans_le ((hZ i j).2 n hn z)) Y 0
    (fun a ↦ inclusion hk (u a)) 0 (fun a ↦ by rw [inclusionLp_inclusion]; exact hu a)
    (fun a ↦ by simpa [Pi.zero_def] using Lp.coeFn_zero ℂ 2 volume)
  refine ⟨W, fun a ↦ (hW a).trans (.of_forall fun z ↦ ?_), hWn.trans ?_⟩
  · simp [gaugeFixedZerothOrder_apply, Finset.sum_neg_distrib]
  · rw [norm_zero, zero_add]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hβb 0 0 (Nat.zero_le k) 0)
    gcongr
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun a ↦
      (norm_inclusion_apply_le hk _).trans (norm_le_pi_norm u a)

/-- **The weighted Sobolev estimate for a solution of `L_a y = -Z(b, e₀)`.** For every order `k`,
bound `B` and rate `c` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth field with `L∞` class `a` whose coordinates have
derivatives bounded by `B` through order `k`, and let `b` be the class of a smooth field `β` whose
coordinates have derivatives bounded by `M` through order `k`. Let `e₀, y ∈ H¹(ℂ)⁴` with
`L_a y = -Z(b, e₀)`, where the coordinates of `exp(c ρ) e₀` are given by
`u₀ : Fin 4 → H^(k+1)(ℂ)` and `‖exp(c ρ) y‖₂ ≤ N`. Then the coordinates of `exp(c ρ) y` are given
by some `u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K (M ‖u₀‖ + N)`. This is the step shared by the
parameter derivatives of the right inverse and of the kernel projection, for which `e₀` is `Q f`
and `π e`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg
    (k : ℕ) (B c : ℝ) :
    ∃ K ≥ 0, ∀ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ (b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (β : ℂ → EuclideanSpace ℝ (Fin 4)) (M : ℝ),
      b =ᵐ[μ⊤] β → ContDiff ℝ ∞ β →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) →
      ∀ (e₀ y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (u₀ : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
      (∀ i, ⇑(inclusionLp (by positivity) (u₀ i)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e₀ z) i : ℂ)) →
      sobolevGaugeFixedOperator a y =
        -gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b (sobolevFieldValues e₀) →
      ∀ N : ℝ, MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2 volume →
      (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2
        volume).toReal ≤ N →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) i : ℂ)) ∧
        ‖u‖ ≤ K * (M * ‖u₀‖ + N) := by
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul k B c
  obtain ⟨C, hC, hCb⟩ := exists_forall_exists_inclusionLp_ae_eq_neg_gaugeFixedZerothOrder k
  refine ⟨K₁ * (C + 1), by positivity, ?_⟩
  intro x hx hxb a hax b β M hb hβ hβb e₀ y u₀ hu₀ hTy N hym hyn
  have hM : 0 ≤ M := (norm_nonneg _).trans (hβb 0 0 (Nat.zero_le k) 0)
  have hN : 0 ≤ N := ENNReal.toReal_nonneg.trans hyn
  set G := -gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b (sobolevFieldValues e₀) with hG
  -- The coordinates of `exp(c ρ) G = -Z(β, exp(c ρ) e₀)`.
  obtain ⟨W, hW, hWn⟩ := hCb β hβ M hβb _ u₀ hu₀
  have hWG : ∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (W i)) =ᵐ[volume]
      fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • G z) i : ℂ) := fun i ↦ (hW i).trans <| by
    filter_upwards [(Lp.coeFn_neg (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b
      (sobolevFieldValues e₀))).filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge),
      (gaugeFixedZerothOrder.coeFn_holder (r := 2) b (sobolevFieldValues e₀)).filter_mono
        (ae_mono (Measure.restrict_coe_opens_top _).ge),
      hb.filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z h₁ h₂ h₃
    rw [hG, h₁, Pi.neg_apply, holderL_apply_apply, h₂, h₃, map_smul, smul_neg]
  -- `y` solves `L_x y = G` weakly, and the weighted elliptic estimate concludes.
  obtain ⟨u, hu, hun⟩ := hK₁b x hx hxb G _
    ((Lp.memLp G).mono_measure (Measure.restrict_coe_opens_top _).ge)
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge) (fun η hη hηc ↦ by
      rw [integral_inner_sobolevFieldValues_gaugeFixedAdjoint hx.continuous hax y hη hηc, hTy])
    hym W hWG
  refine ⟨u, hu, hun.trans ?_⟩
  calc K₁ * (‖W‖ + _) ≤ K₁ * (C * M * ‖u₀‖ + N) := by gcongr
    _ ≤ K₁ * ((C + 1) * (M * ‖u₀‖ + N)) := by gcongr; nlinarith [norm_nonneg u₀]
    _ = K₁ * (C + 1) * (M * ‖u₀‖ + N) := by ring

/-- **The weighted Sobolev estimate for the parameter derivative of the orthogonal right
inverses, uniformly over a window of divisors.** For every degree `m`, radius `R₀`, bound `B`,
rate `|c| < 1/2` and order `k` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `R₀` and whose coordinates have bounded derivatives of every
order, bounded by `B` through order `k`. Let `a` be a family of `L∞` coefficients, differentiable
at `p₀`, with `a p₀` the class of `x`, and let `Q p` be the right inverse of the realization
`L_(a p)` with values `L²`-orthogonal to its kernel. Suppose the derivative `Da(p₀) v` of the
coefficient is the class of a smooth field `β` whose coordinates have derivatives bounded by `M`
through order `k`. If the coordinates of `exp(c ρ) f` are given by `w : Fin 4 → H^k(ℂ)`, then
those of `exp(c ρ) Q' f`, for the derivative `Q'` of `Q` at `p₀` in the direction `v`, are given
by some `u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K M ‖w‖`. That is,

`‖exp(c ρ) Q' f‖_(H^(k+1)) ≤ K M ‖exp(c ρ) f‖_(H^k)`,

with `K` depending only on `m`, `R₀`, `B`, `c` and `k`. The weighted `L²` estimate is
`exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le`. -/
theorem exists_forall_norm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le
    (m : ℕ) (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        DifferentiableAt ℝ a p₀ → ∀ (v : X) (β : ℂ → EuclideanSpace ℝ (Fin 4)) (M : ℝ),
        fderiv ℝ a p₀ v =ᵐ[μ⊤] β → ContDiff ℝ ∞ β →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) →
        ∀ (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (w : Fin 4 → H^{(k : ℝ)}(ℂ)),
        (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (w i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) i : ℂ)) →
        ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
              (fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
                (sobolevGaugeFixedOperator (a p))) p₀ v f) z) i : ℂ)) ∧
          ‖u‖ ≤ K * M * ‖w‖ := by
  obtain ⟨qc, hqc⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀ hc
  obtain ⟨K₂, hK₂⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀
      hc
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul k B c
  obtain ⟨K₃, hK₃, hK₃b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg k B c
  refine ⟨K₃ * (K₁ * (1 + 4 * qc) + 8 * K₂), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax ha v β M hb hβ hβb f w hw
  obtain ⟨hT, hsurj, hd, -⟩ :=
    isFredholm_and_differentiableAt_sobolevGaugeFixedOperator hx hsol hframe hax ha
  have hQ := hT.isOrthogonalRightInverse_orthogonalRightInverse sobolevFieldValues_injective hsurj
  set Q := orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  have hM : 0 ≤ M := (norm_nonneg _).trans (hβb 0 0 (Nat.zero_le k) 0)
  have hf := eLpNorm_le_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hw
  -- The values of `Q f` solve `L_x Y = f` weakly, with weighted `L²` norm at most `4 qc ‖w‖`, so
  -- `exp(c ρ) Q f` has coordinates `u₀` in `H^(k+1)`.
  obtain ⟨hQm, hQn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul (by positivity)
    (hqc x D hx hsol hframe hD hD₀ (a p₀) hax f) hf
  obtain ⟨u₀, hu₀, hu₀n⟩ := hK₁b x hx hxb f _
    ((Lp.memLp f).mono_measure (Measure.restrict_coe_opens_top _).ge)
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge) (fun η hη hηc ↦ by
      rw [integral_inner_sobolevFieldValues_gaugeFixedAdjoint hx.continuous hax (Q f) hη hηc,
        hQ.rightInverse f]) hQm w hw
  -- The derivative `y = Q' f` solves `L_x y = -Z(b, Q f)`, with weighted `L²` norm at most
  -- `4 K₂ ‖b‖∞ ‖w‖`, where `‖b‖∞ ≤ 2 M`.
  obtain ⟨hym, hyn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul
    (K := K₂ * ‖fderiv ℝ a p₀ v‖₊) (by positivity)
    (by simpa only [ENNReal.coe_mul] using hK₂ x D hx hbound hsol hframe hD hD₀ hax ha v f) hf
  have hb2 := norm_le_two_mul_of_ae_eq_of_forall_norm_apply_le hb fun i z ↦ by
    simpa only [norm_iteratedFDeriv_zero] using hβb i 0 (Nat.zero_le k) z
  obtain ⟨u, hu, hun⟩ := hK₃b x hx hxb (a p₀) hax _ β M hb hβ hβb (Q f) _ u₀ hu₀ (by
    rw [hT.apply_fderiv_orthogonalRightInverse_apply (T := fun p ↦ sobolevGaugeFixedOperator (a p))
      sobolevFieldValues_injective hsurj hd, fderiv_sobolevGaugeFixedOperator_comp_apply ha v])
    _ hym hyn
  refine ⟨u, hu, hun.trans ?_⟩
  push_cast
  calc K₃ * (M * ‖u₀‖ + K₂ * ‖fderiv ℝ a p₀ v‖ * (4 * ‖w‖)) ≤
        K₃ * (M * (K₁ * (‖w‖ + qc * (4 * ‖w‖))) + K₂ * (2 * M) * (4 * ‖w‖)) := by
        gcongr
        exact hu₀n.trans (by gcongr)
    _ = K₃ * (K₁ * (1 + 4 * qc) + 8 * K₂) * M * ‖w‖ := by ring

/-- **The weighted Sobolev estimate for the parameter derivative of the orthogonal kernel
projections, uniformly over a window of divisors.** For every degree `m`, radius `R₀`, bound `B`,
rate `|c| < 1/2` and order `k` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `R₀` and whose coordinates have bounded derivatives of every
order, bounded by `B` through order `k`. Let `a` be a family of `L∞` coefficients, differentiable
at `p₀`, with `a p₀` the class of `x`, and let `π p` be the projection of `H¹(ℂ)⁴` onto the kernel
of the realization `L_(a p)` along its `L²`-orthogonal complement. Suppose the derivative
`Da(p₀) v` of the coefficient is the class of a smooth field `β` whose coordinates have derivatives
bounded by `M` through order `k`. If `exp(c ρ) e` is square integrable, then the coordinates of
`exp(c ρ) π' e`, for the derivative `π'` of `π` at `p₀` in the direction `v`, are given by some
`u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K M ‖exp(c ρ) e‖₂`. That is,

`‖exp(c ρ) π' e‖_(H^(k+1)) ≤ K M ‖exp(c ρ) e‖₂`,

with `K` depending only on `m`, `R₀`, `B`, `c` and `k`. The weighted `L²` estimate is
`exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le`. -/
theorem exists_forall_norm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le
    (m : ℕ) (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        DifferentiableAt ℝ a p₀ → ∀ (v : X) (β : ℂ → EuclideanSpace ℝ (Fin 4)) (M : ℝ),
        fderiv ℝ a p₀ v =ᵐ[μ⊤] β → ContDiff ℝ ∞ β →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) →
        ∀ e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
        MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 volume →
        ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
              (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
                (sobolevGaugeFixedOperator (a p))) p₀ v e) z) i : ℂ)) ∧
          ‖u‖ ≤ K * M * (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
            sobolevFieldValues e z) 2 volume).toReal := by
  obtain ⟨kπ, hkπ⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalKerProjection_le_of_forall_mem_norm_le m R₀ hc
  obtain ⟨K₂, hK₂⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le m R₀
      hc
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul k B c
  obtain ⟨K₃, hK₃, hK₃b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg k B c
  refine ⟨K₃ * (K₁ * kπ + 2 * K₂), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax ha v β M hb hβ hβb e he
  obtain ⟨hT, hsurj, hd, hπ⟩ :=
    isFredholm_and_differentiableAt_sobolevGaugeFixedOperator hx hsol hframe hax ha
  set π := orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  set N := (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2
    volume).toReal
  have hM : 0 ≤ M := (norm_nonneg _).trans (hβb 0 0 (Nat.zero_le k) 0)
  have he' := (ENNReal.ofReal_toReal he.eLpNorm_lt_top.ne).ge
  -- `π e` is a weak solution of `L_x Y = 0` with weighted `L²` norm at most `kπ N`, so
  -- `exp(c ρ) π e` has coordinates `u₀` in `H^(k+1)`.
  obtain ⟨hπm, hπn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul (by positivity)
    (hkπ x D hx hbound hsol hframe hD hD₀ (a p₀) hax e) he'
  have hπ0 : sobolevGaugeFixedOperator (a p₀) (π e) = 0 := hπ.mem_ker e
  obtain ⟨u₀, hu₀, hu₀n⟩ := hK₁b x hx hxb (0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) _
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge)
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge) (fun η hη hηc ↦ by
      rw [integral_inner_sobolevFieldValues_gaugeFixedAdjoint hx.continuous hax (π e) hη hηc,
        hπ0]) hπm 0 fun i ↦ .of_forall fun z ↦ by simp
  -- The derivative `y = π' e` solves `L_x y = -Z(b, π e)`, with weighted `L²` norm at most
  -- `K₂ ‖b‖∞ N`, where `‖b‖∞ ≤ 2 M`.
  obtain ⟨hym, hyn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul
    (K := K₂ * ‖fderiv ℝ a p₀ v‖₊) (by positivity)
    (by simpa only [ENNReal.coe_mul] using hK₂ x D hx hbound hsol hframe hD hD₀ hax ha v e) he'
  have hb2 := norm_le_two_mul_of_ae_eq_of_forall_norm_apply_le hb fun i z ↦ by
    simpa only [norm_iteratedFDeriv_zero] using hβb i 0 (Nat.zero_le k) z
  obtain ⟨u, hu, hun⟩ := hK₃b x hx hxb (a p₀) hax _ β M hb hβ hβb (π e) _ u₀ hu₀ (by
    rw [hT.apply_fderiv_orthogonalKerProjection_apply (T := fun p ↦ sobolevGaugeFixedOperator (a p))
      sobolevFieldValues_injective hsurj hd, fderiv_sobolevGaugeFixedOperator_comp_apply ha v])
    _ hym hyn
  refine ⟨u, hu, hun.trans ?_⟩
  rw [norm_zero, zero_add] at hu₀n
  push_cast
  calc K₃ * (M * ‖u₀‖ + K₂ * ‖fderiv ℝ a p₀ v‖ * N) ≤
        K₃ * (M * (K₁ * (kπ * N)) + K₂ * (2 * M) * N) := by
        gcongr
        exact hu₀n.trans (by gcongr)
    _ = K₃ * (K₁ * kπ + 2 * K₂) * M * N := by ring

end TauCeti.Vortex
