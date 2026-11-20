/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.ContDiff.Adjoint
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.Local.Approximation
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher

/-!
# Order-zero regularity for real Cauchy–Riemann equations with Sobolev coefficients

Write `z = s + i t` on `ℂ`, let `V` be a finite-dimensional real inner product space and consider
the real Cauchy–Riemann operator `D ξ = ∂_s ξ + J ∂_t ξ + S ξ` on an open set `Ω`, with
`J ∈ W^{1,p}_loc(Ω)`, `J² = -1` almost everywhere and `S ∈ Lᵖ_loc(Ω)`, for `2 < p < ∞`
(`TauCeti.IsSobolevCRCoefficients`). This file proves the order-zero step of interior
regularity (McDuff–Salamon, Lemma B.4.6): if `1/p + 1/q = 1/r` with `r > 1`, a weak solution
`ξ ∈ L^q_loc(Ω)` of `D ξ = η` (`TauCeti.IsWeakCRSolution`) with `η ∈ Lʳ_loc(Ω)` lies in
`W^{1,r}_loc(Ω)` (`TauCeti.IsWeakCRSolution.memWkpLoc_one`).

## The argument

The proof rewrites the first-order equation as a divergence-form Laplace equation. Formally,
applying `∂_s - J ∂_t` to `D ξ = η` and using `J² = -1` gives

`Δξ = ∂_s f + ∂_t g`,  `f = η + (∂_t J) ξ - S ξ`,
`g = -J η - (∂_s J) ξ - (∂_t J) (J ξ) - J ((∂_t J) ξ) + J (S ξ)`,

where `∂_s J` and `∂_t J` are the weak derivatives. Every product here pairs a locally bounded or
`Lᵖ` coefficient with `ξ ∈ L^q` or `η ∈ Lʳ`, so `f, g ∈ Lʳ_loc` by Hölder's inequality, and the
regularity of the divergence-form Laplace equation
(`TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq`) puts `ξ` in `W^{1,r}_loc`.

To derive the divergence-form equation weakly, test the weak equation against
`Φ = -∂_s ψ v₀ + ∂_t ψ A* v₀` for a real test function `ψ`, a vector `v₀` and a coefficient `A`;
with `A = J` this produces `∫ ⟪v₀, Δψ ξ + ∂_s ψ f + ∂_t ψ g⟫ = 0`. Since `J` is only Sobolev, `Φ`
is not a test function. By Morrey's embedding (`p > 2`) `J` has a continuous representative, which
is approximated on the support of `ψ` by smooth maps `A` uniformly, with `fderiv A` close to the
weak derivative of `J` in `Lᵖ` (`TauCeti.exists_contDiff_dist_le_and_eLpNorm_fderiv_sub_le`).
For smooth `A` the weak equation applies. The tested expression is affine in `(A, DA)`, and its
error is bounded by `sup ‖J - A‖` times an integrable function plus, through Hölder's inequality,
`‖DJ - DA‖_{Lᵖ}` times a constant, so it vanishes in the limit.

Climbing the exponent ladder to `W^{1,p}_loc` and the higher-order estimates are separate.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set TopologicalSpace ContinuousLinearMap LineDeriv
open scoped ENNReal NNReal InnerProductSpace Topology ContDiff Distributions Laplacian

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace OrderZero

/-! ### The pointwise algebra -/

section Algebra

variable (ψ : ℂ → ℝ) (v₀ : V) (J : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V)
  (S : ℂ → V →L[ℝ] V) (ξ η : ℂ → V)

/-- The derivative `∂_t ψ` of a real function on the plane. -/
private abbrev dt (z : ℂ) : ℝ := fderiv ℝ ψ z I

/-- The derivative `∂_s ψ` of a real function on the plane. -/
private abbrev ds (z : ℂ) : ℝ := fderiv ℝ ψ z 1

/-- The coefficient field paired with the zeroth-order coefficient in the error term. -/
private def fieldX (z : ℂ) : V :=
  -(fderiv ℝ (dt ψ) z 1) • ξ z - fderiv ℝ (dt ψ) z I • J z (ξ z) - dt ψ z • DJ z I (ξ z) +
    dt ψ z • S z (ξ z) - dt ψ z • η z

/-- The field paired with `∂_s` of the coefficient in the error term. -/
private def fieldY (z : ℂ) : V := -dt ψ z • ξ z

/-- The field paired with `∂_t` of the coefficient in the error term. -/
private def fieldZ (z : ℂ) : V := -dt ψ z • J z (ξ z)

/-- The part of the tested weak equation that depends on the coefficient `A` replacing `J` in
the test field, and on its derivative `DA`. It is linear in `(A, DA)`. -/
private def coeffTerm (A : ℂ → V →L[ℝ] V) (DA : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (z : ℂ) : ℝ :=
  ⟪v₀, A z (fieldX ψ J DJ S ξ η z) + DA z 1 (fieldY ψ ξ z) + DA z I (fieldZ ψ J ξ z)⟫_ℝ

/-- The part of the tested weak equation that does not depend on the coefficient of the test
field. -/
private def constTerm (z : ℂ) : ℝ :=
  fderiv ℝ (ds ψ) z 1 * ⟪v₀, ξ z⟫_ℝ + fderiv ℝ (ds ψ) z I * ⟪v₀, J z (ξ z)⟫_ℝ +
    ds ψ z * ⟪v₀, DJ z I (ξ z)⟫_ℝ - ds ψ z * ⟪v₀, S z (ξ z)⟫_ℝ + ds ψ z * ⟪v₀, η z⟫_ℝ

/-- The first divergence-form datum `f = η + (∂_t J) ξ - S ξ`. -/
private def divS (z : ℂ) : V := η z + DJ z I (ξ z) - S z (ξ z)

/-- The second divergence-form datum
`g = -J η - (∂_s J) ξ - (∂_t J) (J ξ) - J ((∂_t J) ξ) + J (S ξ)`. -/
private def divT (z : ℂ) : V :=
  -J z (η z) - DJ z 1 (ξ z) - DJ z I (J z (ξ z)) - J z (DJ z I (ξ z)) + J z (S z (ξ z))

variable {ψ v₀ J DJ S ξ η}

/-- The coefficient term is linear in the coefficient and its derivative. -/
private theorem coeffTerm_sub (A B : ℂ → V →L[ℝ] V) (DA DB : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (z : ℂ) :
    coeffTerm ψ v₀ J DJ S ξ η A DA z - coeffTerm ψ v₀ J DJ S ξ η B DB z =
      coeffTerm ψ v₀ J DJ S ξ η (A - B) (DA - DB) z := by
  simp only [coeffTerm, Pi.sub_apply, sub_apply, ← inner_sub_right]
  congr 1
  abel

/-- The pointwise bound for the coefficient term. -/
private theorem norm_coeffTerm_le (B : ℂ → V →L[ℝ] V) (DB : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (z : ℂ) :
    ‖coeffTerm ψ v₀ J DJ S ξ η B DB z‖ ≤ ‖v₀‖ * (‖B z‖ * ‖fieldX ψ J DJ S ξ η z‖ +
      ‖DB z‖ * (‖fieldY ψ ξ z‖ + ‖fieldZ ψ J ξ z‖)) := by
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have h1 : ‖DB z 1‖ ≤ ‖DB z‖ := by simpa using (DB z).le_opNorm 1
  have hI : ‖DB z I‖ ≤ ‖DB z‖ := by simpa using (DB z).le_opNorm I
  calc _ ≤ ‖B z (fieldX ψ J DJ S ξ η z)‖ + ‖DB z 1 (fieldY ψ ξ z)‖ +
        ‖DB z I (fieldZ ψ J ξ z)‖ := norm_add₃_le
    _ ≤ ‖B z‖ * ‖fieldX ψ J DJ S ξ η z‖ + ‖DB z 1‖ * ‖fieldY ψ ξ z‖ +
        ‖DB z I‖ * ‖fieldZ ψ J ξ z‖ := by
      gcongr <;> exact le_opNorm _ _
    _ ≤ _ := by
      have := norm_nonneg (fieldY ψ ξ z)
      have := norm_nonneg (fieldZ ψ J ξ z)
      nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg (fieldY ψ ξ z)),
        mul_le_mul_of_nonneg_right hI (norm_nonneg (fieldZ ψ J ξ z))]

/-- With the coefficient `J` itself, the tested equation is the divergence-form Laplace equation
`Δψ ⟪v₀, ξ⟫ + ∂_s ψ ⟪v₀, f⟫ + ∂_t ψ ⟪v₀, g⟫`, where `J² = -1` and the mixed second derivatives
of `ψ` agree. -/
private theorem constTerm_add_coeffTerm_self {z : ℂ} (hJJ : J z (J z (ξ z)) = -ξ z)
    (hsym : fderiv ℝ (ds ψ) z I = fderiv ℝ (dt ψ) z 1) :
    constTerm ψ v₀ J DJ S ξ η z + coeffTerm ψ v₀ J DJ S ξ η J DJ z =
      (fderiv ℝ (ds ψ) z 1 + fderiv ℝ (dt ψ) z I) * ⟪v₀, ξ z⟫_ℝ +
        ds ψ z * ⟪v₀, divS DJ S ξ η z⟫_ℝ + dt ψ z * ⟪v₀, divT J DJ S ξ η z⟫_ℝ := by
  simp only [constTerm, coeffTerm, fieldX, fieldY, fieldZ, divS, divT, map_add, map_sub,
    map_smul, hJJ, inner_add_right, inner_sub_right, inner_neg_right,
    inner_smul_right, hsym]
  ring

end Algebra

/-! ### Derivatives of the test function -/

section Derivatives

variable {ψ : ℂ → ℝ} {z : ℂ}

/-- Off the support of `ψ`, every first derivative of `ψ` vanishes. -/
private theorem fderiv_apply_eq_zero (hz : z ∉ tsupport ψ) (e : ℂ) : fderiv ℝ ψ z e = 0 := by
  simp [fderiv_of_notMem_tsupport ℝ hz]

/-- Off the support of `ψ`, every second derivative of `ψ` vanishes. -/
private theorem fderiv_fderiv_apply_eq_zero (hz : z ∉ tsupport ψ) (e e' : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ ψ w e) z e' = 0 := by
  have hsub : tsupport (fun w => fderiv ℝ ψ w e) ⊆ tsupport ψ :=
    (tsupport_comp_subset (g := fun L : ℂ →L[ℝ] ℝ => L e) rfl (fderiv ℝ ψ)).trans
      (tsupport_fderiv_subset ℝ)
  simp [fderiv_of_notMem_tsupport ℝ fun h => hz (hsub h)]

/-- A first derivative of a smooth function is smooth. -/
private theorem contDiff_fderiv_apply (hψ : ContDiff ℝ ∞ ψ) (e : ℂ) :
    ContDiff ℝ ∞ (fun w => fderiv ℝ ψ w e) :=
  (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The second derivative of `ψ` in the directions `e`, `e'`, in the order of
`fun w => fderiv ℝ ψ w e`. -/
private theorem fderiv_fderiv_apply (hψ : ContDiff ℝ ∞ ψ) (e e' : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ ψ w e) z e' = fderiv ℝ (fderiv ℝ ψ) z e' e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    ((hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) z
  rw [fderiv_clm_apply hd (differentiableAt_const e)]
  simp

/-- The mixed second derivatives of a smooth function agree. -/
private theorem fderiv_ds_I (hψ : ContDiff ℝ ∞ ψ) :
    fderiv ℝ (ds ψ) z I = fderiv ℝ (dt ψ) z 1 := by
  rw [fderiv_fderiv_apply hψ, fderiv_fderiv_apply hψ]
  exact ContDiffAt.isSymmSndFDerivAt (n := ∞) (hψ.contDiffAt (x := z)) (by simp) I 1

variable [CompleteSpace V] (v₀ : V)

/-- The test field `-∂_s ψ v₀ + ∂_t ψ A* v₀`, where `A*` is the adjoint of the coefficient `A`.
Tested against a weak solution, it produces `Δψ ⟪v₀, ξ⟫` when `A = J`. -/
private def testField (ψ : ℂ → ℝ) (A : ℂ → V →L[ℝ] V) (z : ℂ) : V :=
  -ds ψ z • v₀ + dt ψ z • adjoint (A z) v₀

variable {v₀}

/-- The test field vanishes off the support of `ψ`. -/
private theorem testField_eq_zero {A : ℂ → V →L[ℝ] V} (hz : z ∉ tsupport ψ) :
    testField v₀ ψ A z = 0 := by
  simp [testField, fderiv_apply_eq_zero hz]

/-- The derivative of the test field. -/
private theorem fderiv_testField {A : ℂ → V →L[ℝ] V} (hψ : ContDiff ℝ ∞ ψ)
    (hA : DifferentiableAt ℝ A z) (e : ℂ) :
    fderiv ℝ (testField v₀ ψ A) z e = -fderiv ℝ (ds ψ) z e • v₀ +
      (fderiv ℝ (dt ψ) z e • adjoint (A z) v₀ + dt ψ z • adjoint (fderiv ℝ A z e) v₀) := by
  have hs := ((contDiff_fderiv_apply hψ 1).differentiable (by simp) z).hasFDerivAt
  have ht := ((contDiff_fderiv_apply hψ I).differentiable (by simp) z).hasFDerivAt
  have hadj := (ContinuousLinearMap.apply ℝ V v₀).hasFDerivAt.comp z
    ((adjointRealCLM (𝕜 := ℝ) (V := V) (W := V)).hasFDerivAt.comp z hA.hasFDerivAt)
  have h := (hs.smul_const v₀).neg.add (ht.smul hadj)
  have hfun : testField v₀ ψ A = (-fun y => fderiv ℝ ψ y 1 • v₀) +
      (fun w => fderiv ℝ ψ w I) • (ContinuousLinearMap.apply ℝ V v₀ ∘ adjointRealCLM ∘ A) := by
    funext w
    simp [testField, adjointRealCLM_apply, neg_smul]
  rw [hfun, h.fderiv]
  simp [adjointRealCLM_apply, neg_smul, add_comm]

/-- Testing the weak equation against the test field of a differentiable coefficient `A` gives the
constant term plus the coefficient term of `(A, fderiv A)`. -/
private theorem inner_crFormalAdjoint_testField_sub {J : ℂ → V →L[ℝ] V}
    {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V} {A : ℂ → V →L[ℝ] V}
    (hψ : ContDiff ℝ ∞ ψ) (hA : DifferentiableAt ℝ A z) :
    ⟪crFormalAdjoint J DJ S (testField v₀ ψ A) z, ξ z⟫_ℝ - ⟪testField v₀ ψ A z, η z⟫_ℝ =
      constTerm ψ v₀ J DJ S ξ η z + coeffTerm ψ v₀ J DJ S ξ η A (fderiv ℝ A) z := by
  rw [inner_crFormalAdjoint, fderiv_testField hψ hA, fderiv_testField hψ hA]
  simp only [testField, constTerm, coeffTerm, fieldX, fieldY, fieldZ, inner_add_left,
    real_inner_smul_left, adjoint_inner_left, map_add, map_sub, map_smul, inner_add_right,
    inner_sub_right, real_inner_smul_right]
  ring

end Derivatives

/-! ### Estimates for the error term -/

section Estimates

/-- Hölder's inequality on a finite measure, in the form used for the error term: for
`1/p + 1/q = 1/r` with `r ≥ 1`, `∫ ‖f‖ ‖w‖ ≤ ‖f‖_p ‖w‖_q μ(univ)^(1 - 1/r)`. -/
private theorem lintegral_enorm_mul_le {E : Type*} [NormedAddCommGroup E] {μ : Measure ℂ}
    {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r] (hr : 1 ≤ r) {f : ℂ → E} {w : ℂ → ℝ}
    (hf : AEStronglyMeasurable f μ) (hw : AEStronglyMeasurable w μ) :
    ∫⁻ z, ‖f z‖ₑ * ‖w z‖ₑ ∂μ ≤
      eLpNorm f p μ * eLpNorm w q μ * μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal) := by
  have hm : AEStronglyMeasurable (fun z => ‖f z‖ * w z) μ := hf.norm.mul hw
  have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (μ := μ) (p := p) (q := q) (r := r)
    (fun (L : E) (t : ℝ) => ‖L‖ * t) (1 : ℝ≥0)
    ((continuous_norm.comp continuous_fst).mul continuous_snd) hf hw
    (Eventually.of_forall fun z => by simp [norm_mul])
  simp only [ENNReal.coe_one, one_mul] at hH
  calc ∫⁻ z, ‖f z‖ₑ * ‖w z‖ₑ ∂μ = eLpNorm (fun z => ‖f z‖ * w z) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_eNorm hm]
        refine lintegral_congr fun z => ?_
        simp [eNorm_mul]
    _ ≤ eLpNorm (fun z => ‖f z‖ * w z) r μ * μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hr hm
    _ ≤ _ := by gcongr

variable {ψ : ℂ → ℝ} {v₀ : V} {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
  {S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V}

/-- The integral of the coefficient term over `K` is controlled by the size of the coefficient
on `K` and the size of its derivative. -/
private theorem setLIntegral_coeffTerm_le {K : Set ℂ} {B : ℂ → V →L[ℝ] V}
    {DB : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {δ : ℝ} (hδ : 0 ≤ δ) (hK : MeasurableSet K)
    (hB : ∀ z ∈ K, ‖B z‖ ≤ δ)
    (hX : AEMeasurable (fun z => ‖fieldX ψ J DJ S ξ η z‖ₑ) (volume.restrict K)) :
    ∫⁻ z in K, ‖coeffTerm ψ v₀ J DJ S ξ η B DB z‖ₑ ≤
      ‖v₀‖ₑ * (ENNReal.ofReal δ * (∫⁻ z in K, ‖fieldX ψ J DJ S ξ η z‖ₑ) +
        ∫⁻ z in K, ‖DB z‖ₑ * ‖‖fieldY ψ ξ z‖ + ‖fieldZ ψ J ξ z‖‖ₑ) := by
  calc ∫⁻ z in K, ‖coeffTerm ψ v₀ J DJ S ξ η B DB z‖ₑ
      ≤ ∫⁻ z in K, ‖v₀‖ₑ * (ENNReal.ofReal δ * ‖fieldX ψ J DJ S ξ η z‖ₑ +
          ‖DB z‖ₑ * ‖‖fieldY ψ ξ z‖ + ‖fieldZ ψ J ξ z‖‖ₑ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hK] with z hz
        have h : ‖coeffTerm ψ v₀ J DJ S ξ η B DB z‖ ≤ ‖v₀‖ * (δ * ‖fieldX ψ J DJ S ξ η z‖ +
            ‖DB z‖ * (‖fieldY ψ ξ z‖ + ‖fieldZ ψ J ξ z‖)) :=
          (norm_coeffTerm_le B DB z).trans (by gcongr; exact hB z hz)
        rw [← ofReal_norm]
        refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
        rw [ENNReal.ofReal_mul (norm_nonneg v₀), ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_mul hδ, ENNReal.ofReal_mul (norm_nonneg (DB z)),
          ofReal_norm, ofReal_norm, ofReal_norm,
          Real.eNorm_eq_ofReal (by positivity : 0 ≤ ‖fieldY ψ ξ z‖ + ‖fieldZ ψ J ξ z‖)]
    _ = _ := by
        rw [lintegral_const_mul' _ _ eNorm_ne_top, lintegral_add_left' (hX.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Estimates


/-! ### The tested equation for continuous coefficients -/

variable [CompleteSpace V] {p q r : ℝ≥0∞} {Ω : Opens ℂ} {J : ℂ → V →L[ℝ] V}
  {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V}

/-- For a smooth coefficient `A`, the test field of `A` is a test function, so the weak equation
applies to it: the integral of `constTerm + coeffTerm A (fderiv A)` vanishes. -/
private theorem integral_constTerm_add_coeffTerm_eq_zero (hξ : IsWeakCRSolution q Ω J DJ S ξ η)
    (ψ : 𝓓(Ω, ℝ)) (v₀ : V) {A : ℂ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) :
    Integrable (fun z => constTerm ψ v₀ J DJ S ξ η z +
      coeffTerm ψ v₀ J DJ S ξ η A (fderiv ℝ A) z) ∧
    ∫ z, (constTerm ψ v₀ J DJ S ξ η z + coeffTerm ψ v₀ J DJ S ξ η A (fderiv ℝ A) z) = 0 := by
  have hψ : ContDiff ℝ ∞ (ψ : ℂ → ℝ) := ψ.contDiff
  have hsub : Function.support (testField v₀ (ψ : ℂ → ℝ) A) ⊆ tsupport ψ := fun z hz => by
    by_contra h
    exact hz (testField_eq_zero h)
  have hΦc : ContDiff ℝ ∞ (testField v₀ (ψ : ℂ → ℝ) A) :=
    ((contDiff_fderiv_apply hψ 1).neg.smul contDiff_const).add
      ((contDiff_fderiv_apply hψ I).smul (hA.adjoint.clm_apply contDiff_const))
  let Φ : 𝓓(Ω, V) := ⟨testField v₀ ψ A, hΦc, ψ.hasCompactSupport.mono' hsub,
    (closure_minimal hsub (isClosed_tsupport _)).trans ψ.tsupport_subset⟩
  have heq : (fun z => constTerm ψ v₀ J DJ S ξ η z + coeffTerm ψ v₀ J DJ S ξ η A (fderiv ℝ A) z) =
      fun z => ⟪crFormalAdjoint J DJ S Φ z, ξ z⟫_ℝ - ⟪(Φ : ℂ → V) z, η z⟫_ℝ := by
    funext z
    exact (inner_crFormalAdjoint_testField_sub hψ (hA.differentiable (by simp) z)).symm
  have hi := hξ.integrable_inner_crFormalAdjoint Φ
  have hη := TestFunction.integrable_inner hξ.locallyIntegrableOn Φ
  rw [heq]
  exact ⟨hi.sub hη, by rw [integral_sub hi hη, hξ.integral_inner_crFormalAdjoint Φ, sub_self]⟩

omit [CompleteSpace V] in
/-- With the coefficient `J` itself, `constTerm + coeffTerm J DJ` is almost everywhere the
divergence-form integrand `⟪v₀, Δψ ξ + ∂_s ψ f + ∂_t ψ g⟫`, since `J² = -1` almost everywhere on
`Ω` and every term vanishes off the support of `ψ`. -/
private theorem inner_ae_eq_constTerm_add_coeffTerm
    (hJJ : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (ψ : 𝓓(Ω, ℝ)) (v₀ : V) :
    (fun z => ⟪v₀, Δ (ψ : ℂ → ℝ) z • ξ z +
      (ds ψ z • divS DJ S ξ η z + dt ψ z • divT J DJ S ξ η z)⟫_ℝ) =ᵐ[volume]
      fun z => constTerm ψ v₀ J DJ S ξ η z + coeffTerm ψ v₀ J DJ S ξ η J DJ z := by
  have hψ : ContDiff ℝ ∞ (ψ : ℂ → ℝ) := ψ.contDiff
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hJJ] with z hz
  rw [laplacian_eq_fderiv_fderiv_apply_one_add_fderiv_fderiv_apply_I
    (((hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) z)]
  by_cases hzK : z ∈ tsupport (ψ : ℂ → ℝ)
  · rw [constTerm_add_coeffTerm_self (by rw [← mul_apply_eq_comp, hz (ψ.tsupport_subset hzK)]; simp)
      (fderiv_ds_I hψ)]
    simp only [inner_add_right, real_inner_smul_right]
    ring
  · simp [constTerm, coeffTerm, fieldX, fieldY, fieldZ, fderiv_apply_eq_zero hzK,
      fderiv_fderiv_apply_eq_zero hzK]

/-- The fields of the error term are locally integrable, and those paired with the derivative of
the coefficient are locally `L^q`. -/
private theorem memLpLoc_fieldX_and_fieldYZ [ENNReal.HolderTriple p q r] (hr : 1 ≤ r)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJc : ContinuousOn J Ω)
    (hξ : IsWeakCRSolution q Ω J DJ S ξ η) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    MemLpLoc 1 Ω (fieldX ψ J DJ S ξ η) ∧
      MemLpLoc q Ω (fun z => ‖fieldY ψ ξ z‖ + ‖fieldZ ψ J ξ z‖) := by
  have hq : 1 ≤ q := hr.trans (ENNReal.HolderTriple.le q p r)
  have hc1 (e : ℂ) : ContinuousOn (fun z => fderiv ℝ (dt ψ) z e) Ω :=
    (contDiff_fderiv_apply (contDiff_fderiv_apply hψ I) e).continuous.continuousOn
  have hct : ContinuousOn (dt ψ) Ω := (contDiff_fderiv_apply hψ I).continuous.continuousOn
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hη1 : MemLpLoc 1 Ω η :=
    (memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).2 hξ.locallyIntegrableOn
  have hJξ : MemLpLoc q Ω (fun z => J z (ξ z)) := hξ.memLpLoc.continuousOn_clm_apply hJc
  refine ⟨?_, memLpLoc_iff.2 fun K hK hKc =>
    (memLpLoc_iff.1 (hξ.memLpLoc.continuousOn_smul hct.neg) K hK hKc).norm.add
      (memLpLoc_iff.1 (hJξ.continuousOn_smul hct.neg) K hK hKc).norm⟩
  exact (((((hξ.memLpLoc.mono_exponent hq).continuousOn_smul (hc1 1).neg).sub
    ((hJξ.mono_exponent hq).continuousOn_smul (hc1 I))).sub
    (((hDJI.clm_apply hξ.memLpLoc).mono_exponent hr).continuousOn_smul hct)).add
    (((hc.memLpLoc_zeroth.clm_apply hξ.memLpLoc).mono_exponent hr).continuousOn_smul hct)).sub
    (hη1.continuousOn_smul hct)

/-- **The error of a smooth approximation.** If the smooth coefficient `A` is within `δ` of `J`
uniformly on the support `K` of `ψ`, and `fderiv A` is within `δ` of `DJ` in `Lᵖ(K)`, then the
coefficient term of `(J - A, DJ - fderiv A)` has integral at most `δ` times a constant independent
of `A`. -/
private theorem lintegral_enorm_coeffTerm_le [ENNReal.HolderTriple p q r] (hr : 1 ≤ r)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJc : ContinuousOn J Ω)
    (hξ : IsWeakCRSolution q Ω J DJ S ξ η) (ψ : 𝓓(Ω, ℝ)) (v₀ : V) {A : ℂ → V →L[ℝ] V}
    (hA : ContDiff ℝ ∞ A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hAK : ∀ z ∈ tsupport ψ, dist (A z) (J z) ≤ δ)
    (hAD : eLpNorm (fun z => fderiv ℝ A z - DJ z) p (volume.restrict (tsupport ψ)) ≤
      ENNReal.ofReal δ) :
    ∫⁻ z, ‖coeffTerm ψ v₀ J DJ S ξ η (J - A) (DJ - fderiv ℝ A) z‖ₑ ≤
      ENNReal.ofReal δ * (‖v₀‖ₑ * ((∫⁻ z in tsupport ψ, ‖fieldX ψ J DJ S ξ η z‖ₑ) +
        eLpNorm (fun z => ‖fieldY ψ ξ z‖ + ‖fieldZ ψ J ξ z‖) q (volume.restrict (tsupport ψ)) *
          (volume.restrict (tsupport ψ)) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal))) := by
  set K := tsupport (ψ : ℂ → ℝ)
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  have hKΩ : K ⊆ Ω := ψ.tsupport_subset
  obtain ⟨hX, hW⟩ := memLpLoc_fieldX_and_fieldYZ hr hc hJc hξ ψ.contDiff
  have hXK := memLpLoc_iff.1 hX K hKΩ hK
  have hWK := memLpLoc_iff.1 hW K hKΩ hK
  -- The coefficient term vanishes off `K`.
  have hsupp : Function.support
      (fun z => ‖coeffTerm ψ v₀ J DJ S ξ η (J - A) (DJ - fderiv ℝ A) z‖ₑ) ⊆ K := by
    intro z hz
    by_contra hzK
    exact hz (by simp [coeffTerm, fieldX, fieldY, fieldZ, fderiv_apply_eq_zero hzK,
      fderiv_fderiv_apply_eq_zero hzK])
  -- Hölder's inequality for the term with the derivative of the coefficient.
  have hDBm : AEStronglyMeasurable (DJ - fderiv ℝ A) (volume.restrict K) :=
    (memLpLoc_iff.1 hc.memLpLoc_deriv K hKΩ hK).aestronglyMeasurable.sub
      (hA.continuous_fderiv (by simp)).aestronglyMeasurable
  have hneg : (fun z => fderiv ℝ A z - DJ z) = -(DJ - fderiv ℝ A) := by
    funext z
    simp
  have hHolder := (lintegral_enorm_mul_le (E := ℂ →L[ℝ] V →L[ℝ] V) (p := p) (q := q) hr hDBm
    hWK.aestronglyMeasurable).trans (mul_le_mul_left (mul_le_mul_left
      ((eLpNorm_neg (DJ - fderiv ℝ A) p _).symm.trans_le (hneg ▸ hAD)) _) _)
  rw [← setLIntegral_eq_of_support_subset hsupp]
  refine (setLIntegral_coeffTerm_le hδ hK.measurableSet (fun z hz => ?_)
    hXK.aestronglyMeasurable.eNorm).trans ?_
  · rw [Pi.sub_apply, ← dist_eq_norm, dist_comm]
    exact hAK z hz
  · calc _ ≤ ‖v₀‖ₑ * (ENNReal.ofReal δ * (∫⁻ z in K, ‖fieldX ψ J DJ S ξ η z‖ₑ) +
          ENNReal.ofReal δ * eLpNorm (fun z => ‖fieldY ψ ξ z‖ + ‖fieldZ ψ J ξ z‖) q
            (volume.restrict K) * (volume.restrict K) univ ^
              (1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal)) := by gcongr
      _ = _ := by ring

/-- The divergence-form integrand `⟪v₀, Δψ ξ + ∂_s ψ f + ∂_t ψ g⟫` is integrable: `ξ` is locally
`L^q` and `f`, `g` are locally integrable by Hölder's inequality. -/
private theorem integrable_inner_divergenceIntegrand [ENNReal.HolderTriple p q r] (hr : 1 ≤ r)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJc : ContinuousOn J Ω)
    (hξ : IsWeakCRSolution q Ω J DJ S ξ η) (ψ : 𝓓(Ω, ℝ)) (v₀ : V) :
    Integrable (fun z => ⟪v₀, Δ (ψ : ℂ → ℝ) z • ξ z +
      (ds ψ z • divS DJ S ξ η z + dt ψ z • divT J DJ S ξ η z)⟫_ℝ) := by
  have hq : 1 ≤ q := hr.trans (ENNReal.HolderTriple.le q p r)
  have hΩ := Ω.isOpen.isLocallyClosed
  have hξq : MemLpLoc q Ω ξ := hξ.memLpLoc
  have hη1 : MemLpLoc 1 Ω η := (memLpLoc_one_iff_locallyIntegrableOn hΩ).2 hξ.locallyIntegrableOn
  have hDJ (e : ℂ) : MemLpLoc p Ω (fun z => DJ z e) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) e)
  have hDJIξ : MemLpLoc r Ω (fun z => DJ z I (ξ z)) := (hDJ I).clm_apply hξq
  have hSξ : MemLpLoc r Ω (fun z => S z (ξ z)) := hc.memLpLoc_zeroth.clm_apply hξq
  have hdivS : LocallyIntegrableOn (divS DJ S ξ η) Ω :=
    (memLpLoc_one_iff_locallyIntegrableOn hΩ).1
      ((hη1.add (hDJIξ.mono_exponent hr)).sub (hSξ.mono_exponent hr))
  have hdivT : LocallyIntegrableOn (divT J DJ S ξ η) Ω :=
    (memLpLoc_one_iff_locallyIntegrableOn hΩ).1
      ((((((hη1.continuousOn_clm_apply hJc).neg).sub
        (((hDJ 1).clm_apply hξq).mono_exponent hr)).sub
        (((hDJ I).clm_apply (hξq.continuousOn_clm_apply hJc)).mono_exponent hr)).sub
        ((hDJIξ.mono_exponent hr).continuousOn_clm_apply hJc)).add
        ((hSξ.mono_exponent hr).continuousOn_clm_apply hJc))
  refine Integrable.const_inner v₀ (Integrable.add ?_
    ((integrable_fderiv_smul_of_locallyIntegrableOn hdivS ψ 1).add
      (integrable_fderiv_smul_of_locallyIntegrableOn hdivT ψ I)))
  simpa only [TestFunction.laplacianCLM_apply] using
    (laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) ψ).integrable_smul (hξq.locallyIntegrableOn hq hΩ)

/-- **The divergence-form equation of a weak solution, tested in one direction.** For a
coefficient `J` continuous on `Ω` with `J² = -1` almost everywhere, a weak solution `ξ` of
`∂_s ξ + J ∂_t ξ + S ξ = η` satisfies `∫ ⟪v₀, Δψ ξ + ∂_s ψ f + ∂_t ψ g⟫ = 0` for every real
test function `ψ` and every `v₀ ∈ V`. -/
private theorem integral_inner_eq_zero (hp_top : p ≠ ⊤) [ENNReal.HolderTriple p q r]
    (hr : 1 ≤ r) (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJc : ContinuousOn J Ω)
    (hJJ : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hξ : IsWeakCRSolution q Ω J DJ S ξ η)
    (ψ : 𝓓(Ω, ℝ)) (v₀ : V) :
    ∫ z, ⟪v₀, Δ (ψ : ℂ → ℝ) z • ξ z +
      (ds ψ z • divS DJ S ξ η z + dt ψ z • divT J DJ S ξ η z)⟫_ℝ = 0 := by
  set K := tsupport (ψ : ℂ → ℝ)
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  have hKΩ : K ⊆ Ω := ψ.tsupport_subset
  have hp : 1 ≤ p := hr.trans (ENNReal.HolderTriple.le p q r)
  have hint := integrable_inner_divergenceIntegrand hr hc hJc hξ ψ v₀
  -- Smooth approximations `A n` of `J` on `K`, at distance `1 / (n + 1)`.
  choose A hAc hAK hAD using fun n : ℕ => exists_contDiff_dist_le_and_eLpNorm_fderiv_sub_le hp
    hp_top hJc hc.hasWeakFDerivOn hc.memLpLoc_deriv hK hKΩ
    (η := 1 / ((n : ℝ) + 1)) (by positivity)
  -- The constant of the error estimate is finite.
  obtain ⟨hX, hW⟩ := memLpLoc_fieldX_and_fieldYZ hr hc hJc hξ ψ.contDiff
  set M := ‖v₀‖ₑ * ((∫⁻ z in K, ‖fieldX ψ J DJ S ξ η z‖ₑ) +
    eLpNorm (fun z => ‖fieldY ψ ξ z‖ + ‖fieldZ ψ J ξ z‖) q (volume.restrict K) *
      (volume.restrict K) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal))
  have hM : M ≠ ⊤ := by
    have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal := by
      rcases eq_or_ne r ⊤ with rfl | hrt
      · simp
      · simp only [ENNReal.toReal_one, div_one, sub_nonneg]
        exact div_le_one_of_le₀ (by simpa using ENNReal.toReal_mono hrt hr) (by positivity)
    have hXK := memLpLoc_iff.1 hX K hKΩ hK
    refine ENNReal.mul_ne_top eNorm_ne_top (ENNReal.add_ne_top.2 ⟨?_,
      ENNReal.mul_ne_top (memLpLoc_iff.1 hW K hKΩ hK).eLpNorm_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hexp (by simpa using hK.measure_lt_top.ne))⟩)
    rw [← eLpNorm_one_eq_lintegral_eNorm hXK.aestronglyMeasurable]
    exact hXK.eLpNorm_ne_top
  -- The integral is the error of each approximation, which tends to zero.
  have hbound (n : ℕ) : ‖∫ z, ⟪v₀, Δ (ψ : ℂ → ℝ) z • ξ z +
      (ds ψ z • divS DJ S ξ η z + dt ψ z • divT J DJ S ξ η z)⟫_ℝ‖ₑ ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) * M := by
    have htest := integral_constTerm_add_coeffTerm_eq_zero hξ ψ v₀ (hAc n)
    rw [← sub_zero (∫ z, _), ← htest.2, ← integral_sub hint htest.1]
    refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq_of_le (lintegral_congr_ae ?_)
      (lintegral_enorm_coeffTerm_le hr hc hJc hξ ψ v₀ (hAc n) (by positivity) (hAK n) (hAD n)))
    filter_upwards [inner_ae_eq_constTerm_add_coeffTerm hJJ ψ v₀] with z hz
    rw [hz, add_sub_add_left_eq_sub, coeffTerm_sub]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)) * M) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using ENNReal.Tendsto.mul_const h (Or.inr hM)
  exact eNorm_eq_zero.1 (le_antisymm (ge_of_tendsto' hlim hbound) (by positivity))

end OrderZero

open OrderZero in
/-- **Order-zero regularity for real Cauchy–Riemann equations with Sobolev coefficients**
(McDuff–Salamon, Lemma B.4.6). Let `V` be finite-dimensional, `2 < p < ∞` and
`1/p + 1/q = 1/r` with `r > 1`. Let the coefficients of `∂_s + J ∂_t + S` be Sobolev on the open
set `Ω` (`J ∈ W^{1,p}_loc` with weak derivative `DJ`, and `S ∈ Lᵖ_loc`), with `J² = -1` almost
everywhere on `Ω`. Then every weak solution `ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η` with
`η ∈ Lʳ_loc(Ω)` lies in `W^{1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one [FiniteDimensional ℝ V] {p q r : ℝ≥0∞}
    {Ω : Opens ℂ} {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {S : ℂ → V →L[ℝ] V}
    {ξ η : ℂ → V} (hξ : IsWeakCRSolution q Ω J DJ S ξ η) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpqr : p⁻¹ + q⁻¹ = r⁻¹) (hr : 1 < r) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJJ : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc r Ω η) :
    MemWkpLoc r Ω 1 ξ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have : ENNReal.HolderTriple p q r := ⟨hpqr⟩
  have hr_top : r ≠ ⊤ := ne_top_of_le_ne_top hp_top (ENNReal.HolderTriple.le p q r)
  have hq : 1 ≤ q := hr.le.trans (ENNReal.HolderTriple.le q p r)
  have hΩ := Ω.isOpen.isLocallyClosed
  -- By Morrey's embedding, `J` has a representative `J'` continuous on `Ω`.
  have hJW : MemWkpLoc p Ω (0 + 1) J :=
    memWkpLoc_succ_iff_of_isOpen.2 ⟨hc.memLpLoc_coeff, DJ, hc.hasWeakFDerivOn,
      memWkpLoc_zero_iff.2 hc.memLpLoc_deriv⟩
  obtain ⟨J', hJ'c, hJJ'⟩ := hJW.exists_contDiffOn_ae_eq hp
  replace hJ'c : ContinuousOn J' Ω := hJ'c.continuousOn
  have hc' : IsSobolevCRCoefficients p Ω J' DJ S :=
    ⟨hc.hasWeakFDerivOn.congr_ae hJJ', hc.memLpLoc_coeff.congr_ae hJJ', hc.memLpLoc_deriv,
      hc.memLpLoc_zeroth⟩
  have hξ' : IsWeakCRSolution q Ω J' DJ S ξ η :=
    (isWeakCRSolution_congr_ae hJJ' (ae_eq_refl _) (ae_eq_refl _) (ae_eq_refl _)
      (ae_eq_refl _)).1 hξ
  have hJJ'' : ∀ᵐ z ∂volume.restrict Ω, J' z * J' z = -1 := by
    filter_upwards [hJJ, hJJ'] with z h₁ h₂
    rwa [← h₂]
  -- The data `f` and `g` of the divergence-form equation lie in `Lʳ_loc`.
  have hξq : MemLpLoc q Ω ξ := hξ'.memLpLoc
  have hJξ : MemLpLoc q Ω (fun z => J' z (ξ z)) := hξq.continuousOn_clm_apply hJ'c
  have hDJ1 : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hDJIξ : MemLpLoc r Ω (fun z => DJ z I (ξ z)) := hDJI.clm_apply hξq
  have hSξ : MemLpLoc r Ω (fun z => S z (ξ z)) := hc.memLpLoc_zeroth.clm_apply hξq
  have hf : MemLpLoc r Ω (divS DJ S ξ η) := (hη.add hDJIξ).sub hSξ
  have hg : MemLpLoc r Ω (divT J' DJ S ξ η) :=
    ((((hη.continuousOn_clm_apply hJ'c).neg.sub (hDJ1.clm_apply hξq)).sub
      (hDJI.clm_apply hJξ)).sub (hDJIξ.continuousOn_clm_apply hJ'c)).add
      (hSξ.continuousOn_clm_apply hJ'c)
  refine memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr hr_top
    (hξq.locallyIntegrableOn hq hΩ) hf hg fun ψ => ?_
  -- `Δξ = ∂_s f + ∂_t g` weakly, tested against every vector `v₀`.
  have h₁ : Integrable fun z => Δ (ψ : ℂ → ℝ) z • ξ z := by
    simpa only [TestFunction.laplacianCLM_apply] using
      (laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) ψ).integrable_smul (hξq.locallyIntegrableOn hq hΩ)
  have h₂ : Integrable fun z => fderiv ℝ (ψ : ℂ → ℝ) z 1 • divS DJ S ξ η z +
      fderiv ℝ (ψ : ℂ → ℝ) z I • divT J' DJ S ξ η z :=
    (integrable_fderiv_smul_of_locallyIntegrableOn (hf.locallyIntegrableOn hr.le hΩ) ψ 1).add
      (integrable_fderiv_smul_of_locallyIntegrableOn (hg.locallyIntegrableOn hr.le hΩ) ψ I)
  have h₃ : Integrable fun z => Δ (ψ : ℂ → ℝ) z • ξ z + (fderiv ℝ (ψ : ℂ → ℝ) z 1 •
      divS DJ S ξ η z + fderiv ℝ (ψ : ℂ → ℝ) z I • divT J' DJ S ξ η z) := h₁.add h₂
  rw [eq_neg_iff_add_eq_zero, ← integral_add h₁ h₂]
  refine ext_inner_left ℝ fun v₀ => ?_
  rw [inner_zero_right, ← integral_inner h₃]
  exact integral_inner_eq_zero hp_top hr.le hc' hJ'c hJJ'' hξ' ψ v₀

end TauCeti
