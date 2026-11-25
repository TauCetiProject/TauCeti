/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Index
public import TauCeti.Analysis.PDE.Vortex.Kernel.Projection
public import TauCeti.Analysis.PDE.Vortex.RightInverse
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp
import TauCeti.MeasureTheory.Function.Lp.Norm
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
`π`, `Q` and their first derivatives in `p`, with constants that depend only on the degree `m`,
a radius `R₀` containing the zeros, and `c`. They hold uniformly over a window of divisors,
collisions included, and their size is proportional to the size of the derivative of the
coefficient. Here `‖g‖_c` denotes the weighted norm `‖exp(c ρ) g‖₂` of the values of `g`.

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

The estimates are stated for the `L²` values of the `H¹` fields; weighted Sobolev versions and
higher derivatives in the parameter are not treated here.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter TopologicalSpace ContinuousLinearMap
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff

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
    have h := integral_inner_sobolevGaugeFixedOperator hx.continuous hax (Q f)
      (hη.of_le (by simp)) hηc
    rw [hQ.rightInverse f] at h
    rw [integral_restrict_coe_opens_top, integral_restrict_coe_opens_top, h]
    refine integral_congr_ae ?_
    filter_upwards [(sobolevFieldValues_ae_eq (Q f)).filter_mono
      (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z hz
    rw [hz]
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
`L²`-orthogonal complement and `Q` a right inverse of `T`, and let `y`, `A` be such that the
pairings of `y` with the kernel are bounded by `|⟪y, k⟫| ≤ |⟪Q (Z(b, k)), A⟫|`. If the weight
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
  have hp := hπ.mem_ker y
  -- `‖π y‖₂² = ⟪y, π y⟫`, since `y - π y` is orthogonal to the kernel.
  have hinner : ‖sobolevFieldValues (π y)‖ ^ 2 ≤
      |⟪sobolevFieldValues (Q (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b
        (sobolevFieldValues (π y)))), A⟫| := by
    have h := hπ.inner_apply_eq_norm_sq y
    rw [RCLike.ofReal_real_eq_id, id] at h
    exact h ▸ (le_abs_self _).trans (hpair _ hp)
  -- The weight `exp(-c ρ)` costs at most `qn ‖Z‖ ‖b‖∞ kn` on `Q (Z(b, π y))`, relative to `‖π y‖₂`.
  have hqe : eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (Q (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b (sobolevFieldValues (π y)))) z) 2 μ⊤ ≤
        (qn * ‖gaugeFixedZerothOrder‖₊ * ‖b‖₊ * kn : ℝ≥0) *
          eLpNorm (sobolevFieldValues (π y)) 2 μ⊤ :=
    eLpNorm_exp_mul_smul_sobolevFieldValues_holderL_le hQn b (hkn _ hp)
  refine (le_of_eq_of_le ?_ (Lp.eLpNorm_smul_add_le one_le_two _ _ _)).trans (add_le_add_left
    (TauCeti.eLpNorm_exp_mul_smul_le_of_sq_le_abs_inner (hkc _ hp) hqe hinner) _)
  rw [← map_add, add_sub_cancel]

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
    have h := hπ.inner_apply_eq_norm_sq e
    rw [RCLike.ofReal_real_eq_id, id] at h
    rw [real_inner_comm, h]
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
    ((contDiff_sobolevGaugeFixedOperator (n := 1)).differentiable one_ne_zero).differentiableAt.comp
      p₀ ha,
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
  have hA : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues (e - π e) z) 2 μ⊤ ≤ ((1 + kπ : ℝ≥0) : ℝ≥0∞) * N := by
    rw [map_sub, sub_eq_add_neg, ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]
    refine (Lp.eLpNorm_smul_add_le one_le_two _ _ _).trans (add_le_add le_rfl ?_)
    rwa [Lp.eLpNorm_smul_neg]
  refine (eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le hπ hkc' hkn' hqn' b y
    (A := sobolevFieldValues (e - π e))
    fun k hk ↦ by rw [hpair k hk, abs_neg, real_inner_comm]).trans ?_
  calc _ ≤ (kc * (qn * Z * ‖b‖₊ * kn) : ℝ≥0) * (((1 + kπ : ℝ≥0) : ℝ≥0∞) * N) +
        (qc * Z * ‖b‖₊ * kπ : ℝ≥0) * N :=
      add_le_add (mul_le_mul_right hA _) hperp
    _ = _ := by
      push_cast
      ring

end TauCeti.Vortex
