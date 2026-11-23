/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.Flux.Basic
public import TauCeti.RingTheory.Polynomial.PrescribedPowerSums
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Analysis.Polynomial.AtInfinity

/-!
# The flux moments of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)` and curvature `iF_a = -(∂₁ b₂ - ∂₂ b₁) ds ∧ dt`
(`TauCeti.Vortex.curvature`). For a vortex, `∂₁ b₂ - ∂₂ b₁ = -(1 - |α|²) / 8`, so the flux
density `(2π)⁻¹ iF_a` is the nonnegative density `(1 - |α|²) / (16π)`. Its total mass is the
number of zeros of `α`, counted with multiplicity
(`TauCeti.Vortex.integral_one_sub_normSq_eq_mul_finsum`).
This file shows that the flux density has the same holomorphic moments as the counting measure of
the zeros: for every complex polynomial `P`,

`∫ P(z) (1 - |α(z)|²) = 16π ∑_{z ∈ D} P(z)`,

where `D` is the zero divisor of `α` (`TauCeti.Vortex.integral_one_sub_normSq_smul_eval_eq`).
Applied to its real and imaginary parts, this is the moment identity against harmonic weights of
polynomial growth (`TauCeti.Vortex.integral_mul_one_sub_normSq_eq_mul_finsum`), since the real
linear functionals of a holomorphic polynomial are harmonic.

In Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic curve, the normalized
curvature slices `μ_z` have moments `M_k = ∫ Wᵏ dμ_z`, whose Newton coefficients are the
coefficients of the monic polynomial `P_z` locating the branches of the limiting curve
(`TauCeti.newtonPolynomial`, `TauCeti.exists_forall_abs_integral_sub_sum_roots_le`). For a plane
vortex the flux moments `M_k = (2π)⁻¹ ∫ zᵏ iF_a` (`TauCeti.Vortex.fluxMoment`) are exactly the
power sums of its zeros (`TauCeti.Vortex.fluxMoment_eq_sum_map_pow`), so its moment polynomial is
`∏_{z ∈ D} (W - z)` (`TauCeti.Vortex.newtonPolynomial_fluxMoment`). In particular the divisor of a
smooth framed degree-`m` vortex is the root multiset of the degree-`m` Newton polynomial of its
flux moments (`TauCeti.Vortex.framedVortexDivisor_eq_roots_newtonPolynomial_fluxMoment`), and its
elementary symmetric functions, the coordinates of `Sym ℂ m ≃ ℂᵐ`, are the Newton coefficients of
the flux moments (`TauCeti.Vortex.esymm_framedVortexDivisor_eq_newtonCoeff_fluxMoment`). The
divisor map behind Taubes's identification of the framed vortex moduli with `Sym ℂ m`
(`TauCeti.Vortex.framedVortexModuliEquiv`) is thus computed by integrals of the curvature.

## Main results

* `TauCeti.Vortex.integral_one_sub_normSq_smul_eval_eq`: the moment identity for a complex
  polynomial weight, in terms of the zero divisor.
* `TauCeti.Vortex.integral_curvature_smul_eval_eq`: the same identity for the curvature.
* `TauCeti.Vortex.fluxMoment_eq_sum_map_pow`: the flux moments are the power sums of the zeros.
* `TauCeti.Vortex.newtonPolynomial_fluxMoment`, `TauCeti.Vortex.roots_newtonPolynomial_fluxMoment`:
  the moment polynomial of a vortex is the polynomial of its zero divisor.
* `TauCeti.Vortex.framedVortexDivisor_eq_roots_newtonPolynomial_fluxMoment`,
  `TauCeti.Vortex.esymm_framedVortexDivisor_eq_newtonCoeff_fluxMoment`: the divisor of a framed
  vortex from its flux moments.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Asymptotics Complex Filter Metric MeasureTheory Polynomial Set Topology InnerProductSpace
  Laplacian
open scoped Distributions ContDiff Real

namespace TauCeti.Vortex

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Polynomial weights -/

/-- The moment identity for the harmonic weight `L ∘ P`, where `P` is a complex polynomial and `L`
a real linear functional on `ℂ`, in terms of the zero divisor `D`. -/
private theorem integral_clm_eval_mul_one_sub_normSq_eq
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) (D.count ·)) (P : ℂ[X]) (L : ℂ →L[ℝ] ℝ) :
    ∫ z, L (P.eval z) * (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) =
      16 * π * (D.map fun z ↦ L (P.eval z)).sum := by
  have hP : ContDiff ℂ ∞ fun z ↦ P.eval z := P.differentiable.contDiff
  -- `L ∘ P` is harmonic, as the real part of a holomorphic function is.
  have hΔ : Δ (fun z ↦ L (P.eval z)) = 0 :=
    funext fun z ↦ ((hP.contDiffAt.of_le (by simp)).harmonicAt.comp_CLM L).2.self_of_nhds
  -- `‖D(L ∘ P)‖ ≤ ‖L‖ ‖P'‖`.
  have hfd (z : ℂ) : ‖fderiv ℝ (fun z ↦ L (P.eval z)) z‖ ≤ ‖L‖ * ‖P.derivative.eval z‖ := by
    have hd : HasFDerivAt (fun w ↦ P.eval w)
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (P.derivative.eval z)).restrictScalars
          ℝ) z := (P.hasDerivAt z).hasFDerivAt.restrictScalars ℝ
    have hfd : fderiv ℝ (fun z ↦ L (P.eval z)) z = L.comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (P.derivative.eval z)).restrictScalars
          ℝ) := (L.hasFDerivAt.comp z hd).fderiv
    rw [hfd]
    exact (L.opNorm_comp_le _).trans_eq (by rw [ContinuousLinearMap.norm_restrictScalars,
      ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul])
  have h := integral_mul_one_sub_normSq_eq_mul_finsum hb₁ hb₂ hp hq hsol hlim
    (isZeroMultiplicity_iff.1 hD) (h := fun z ↦ L (P.eval z))
    (L.contDiff.comp (hP.restrict_scalars ℝ)) hΔ
    ((L.isBigO_comp _ _).trans (Metric.cobounded_eq_cocompact (α := ℂ) ▸
      isBigO_cobounded_eval_norm_pow_of_natDegree_le le_rfl))
    ((isBigO_of_le _ fun z ↦ (hfd z).trans_eq (Real.norm_of_nonneg (by positivity)).symm).trans
      (((isBigO_refl _ _).const_mul_left ‖L‖).trans (Metric.cobounded_eq_cocompact (α := ℂ) ▸
        isBigO_cobounded_eval_norm_pow_of_natDegree_le
          ((natDegree_derivative_le P).trans (Nat.sub_le _ _))).norm_left))
  -- The sum against the multiplicities of `D` is the sum over `D`.
  simp_rw [h, ← nsmul_eq_mul, Multiset.finsum_count_nsmul_eq_sum_map]

/-- **The holomorphic moments of a plane vortex.** Let `x` be a `C²` vortex on the whole plane
whose section satisfies `|α| → 1` at infinity, with zero divisor `D`. For every complex polynomial
`P`, `∫ P(z) (1 - |α(z)|²) = 16π ∑_{z ∈ D} P(z)`: the modulus defect `(1 - |α|²) / 16π` has the
same holomorphic moments as the counting measure of the zeros. -/
theorem integral_one_sub_normSq_smul_eval_eq
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) (D.count ·)) (P : ℂ[X]) :
    ∫ z, (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) • P.eval z = 16 * π * (D.map fun z ↦ P.eval z).sum := by
  have hint := integrable_one_sub_normSq_smul_of_isBigO volume hp hq hsol hlim P.continuous
    (Metric.cobounded_eq_cocompact (α := ℂ) ▸
      isBigO_cobounded_eval_norm_pow_of_natDegree_le le_rfl)
  have h16 : (16 * π * (D.map fun z ↦ P.eval z).sum : ℂ) =
      (16 * π : ℝ) • (D.map fun z ↦ P.eval z).sum := by
    rw [Complex.real_smul]
    push_cast
    ring
  -- Both sides have the same image under every real linear functional `L`.
  have hL (L : ℂ →L[ℝ] ℝ) : L (∫ z, (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) • P.eval z) =
      L (16 * π * (D.map fun z ↦ P.eval z).sum) := by
    simp only [← L.integral_comp_comm hint, h16, map_smul, map_multiset_sum, Multiset.map_map,
      Function.comp_def, smul_eq_mul]
    rw [← integral_clm_eval_mul_one_sub_normSq_eq hb₁ hb₂ hp hq hsol hlim hD P L]
    exact integral_congr_ae (.of_forall fun z ↦ by ring)
  exact Complex.ext (hL reCLM) (hL imCLM)

/-- **The holomorphic moments of the curvature of a plane vortex.** Let `x` be a `C²` vortex on the
whole plane whose section satisfies `|α| → 1` at infinity, with zero divisor `D`. For every complex
polynomial `P`, the curvature coefficient `∂₁ b₂ - ∂₂ b₁` satisfies
`∫ P(z) (∂₁ b₂ - ∂₂ b₁) = -2π ∑_{z ∈ D} P(z)`; equivalently, since
`iF_a = -(∂₁ b₂ - ∂₂ b₁) ds ∧ dt`, `(2π)⁻¹ ∫ P iF_a = ∑_{z ∈ D} P(z)`. -/
theorem integral_curvature_smul_eval_eq
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) (D.count ·)) (P : ℂ[X]) :
    ∫ z, curvature x z • P.eval z = -(2 * π * (D.map fun z ↦ P.eval z).sum) := by
  have h : (fun z ↦ curvature x z • P.eval z) =
      fun z ↦ (-(1 / 8) : ℝ) • ((1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) • P.eval z) := by
    funext z
    rw [curvature_apply, curvature_eq_of_equation_eq_zero (hsol z), smul_smul]
    ring_nf
  rw [h, integral_smul, integral_one_sub_normSq_smul_eval_eq hb₁ hb₂ hp hq hsol hlim hD,
    Complex.real_smul]
  push_cast
  ring

/-! ### Flux moments and the moment polynomial -/

/-- The `k`-th moment `∫ zᵏ dμ` of the flux density `μ = (2π)⁻¹ iF_a` of a field `x`. Since
`iF_a = -(∂₁ b₂ - ∂₂ b₁) ds ∧ dt`, this is `-(2π)⁻¹ ∫ zᵏ (∂₁ b₂ - ∂₂ b₁)`. -/
def fluxMoment (x : ℂ → EuclideanSpace ℝ (Fin 4)) (k : ℕ) : ℂ :=
  -(2 * π : ℂ)⁻¹ * ∫ z, curvature x z • z ^ k

/-- The defining formula of `TauCeti.Vortex.fluxMoment`. -/
theorem fluxMoment_def (x : ℂ → EuclideanSpace ℝ (Fin 4)) (k : ℕ) :
    fluxMoment x k = -(2 * π : ℂ)⁻¹ * ∫ z, curvature x z • z ^ k :=
  (rfl)

/-- **The flux moments of a plane vortex are the power sums of its zeros.** For a `C²` vortex on
the whole plane whose section satisfies `|α| → 1` at infinity, with zero divisor `D`, the moment
`(2π)⁻¹ ∫ zᵏ iF_a` is `∑_{z ∈ D} zᵏ`. For `k = 0` this is the flux identity. -/
theorem fluxMoment_eq_sum_map_pow
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) (D.count ·)) (k : ℕ) :
    fluxMoment x k = (D.map (· ^ k)).sum := by
  have h := integral_curvature_smul_eval_eq hb₁ hb₂ hp hq hsol hlim hD (X ^ k)
  simp only [eval_pow, eval_X] at h
  rw [fluxMoment_def, h]
  field_simp

/-- The flux moments of a plane vortex, as a sequence, are the power sums of its zeros. -/
theorem fluxMoment_eq_fun_sum_map_pow
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) (D.count ·)) :
    fluxMoment x = fun k ↦ (D.map (· ^ k)).sum :=
  funext (fluxMoment_eq_sum_map_pow hb₁ hb₂ hp hq hsol hlim hD)

/-- **The moment polynomial of a plane vortex.** For a `C²` vortex on the whole plane whose section
satisfies `|α| → 1` at infinity, with zero divisor `D`, the monic polynomial of degree `deg D`
whose Newton coefficients are given by the flux moments is `∏_{z ∈ D} (W - z)`. -/
theorem newtonPolynomial_fluxMoment
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) (D.count ·)) :
    newtonPolynomial (fluxMoment x) (Multiset.card D) = (D.map fun z ↦ X - C z).prod := by
  rw [fluxMoment_eq_fun_sum_map_pow hb₁ hb₂ hp hq hsol hlim hD, newtonPolynomial_sum_map_pow]

/-- **The zero divisor of a plane vortex from its flux moments.** For a `C²` vortex on the whole
plane whose section satisfies `|α| → 1` at infinity, with zero divisor `D`, the roots of the monic
polynomial of degree `deg D` whose Newton coefficients are given by the flux moments are the
points of `D`, with multiplicity. -/
theorem roots_newtonPolynomial_fluxMoment
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) (D.count ·)) :
    (newtonPolynomial (fluxMoment x) (Multiset.card D)).roots = D := by
  rw [newtonPolynomial_fluxMoment hb₁ hb₂ hp hq hsol hlim hD, roots_multiset_prod_X_sub_C]

/-! ### The divisor of a framed vortex -/

variable {m : ℕ}

/-- The flux moments of a smooth framed degree-`m` vortex of coupling one are the power sums of
its divisor. -/
theorem fluxMoment_eq_sum_map_pow_framedVortexDivisor (x : framedVortexSubMulAction 1 m)
    (k : ℕ) :
    fluxMoment x k = ((framedVortexDivisor x : Multiset ℂ).map (· ^ k)).sum := by
  obtain ⟨hx, hsol, hframe⟩ := mem_framedVortexSubMulAction.1 x.property
  simp only [coupledEquation_one] at hsol
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w i :=
    ((contDiff_piLp 2).1 hx i).of_le (by simp)
  exact fluxMoment_eq_sum_map_pow (hxi 0) (hxi 1) (hxi 2) (hxi 3) hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
    (isZeroMultiplicity_sectionValue_framedVortexDivisor x) k

/-- The flux moments of a smooth framed degree-`m` vortex, as a sequence, are the power sums of
its divisor. -/
theorem fluxMoment_eq_fun_sum_map_pow_framedVortexDivisor (x : framedVortexSubMulAction 1 m) :
    fluxMoment x = fun k ↦ ((framedVortexDivisor x : Multiset ℂ).map (· ^ k)).sum :=
  funext (fluxMoment_eq_sum_map_pow_framedVortexDivisor x)

/-- **The divisor of a framed vortex from its flux moments.** The divisor of a smooth framed
degree-`m` vortex is the multiset of roots of the monic polynomial of degree `m` whose Newton
coefficients are given by its flux moments `(2π)⁻¹ ∫ zᵏ iF_a`. -/
theorem framedVortexDivisor_eq_roots_newtonPolynomial_fluxMoment
    (x : framedVortexSubMulAction 1 m) :
    (framedVortexDivisor x : Multiset ℂ) = (newtonPolynomial (fluxMoment x) m).roots := by
  have h := roots_newtonPolynomial_sum_map_pow (framedVortexDivisor x : Multiset ℂ)
  rw [Sym.card_coe, ← fluxMoment_eq_fun_sum_map_pow_framedVortexDivisor] at h
  exact h.symm

/-- **Symmetric coordinates of a framed vortex.** The elementary symmetric functions of the
divisor of a smooth framed degree-`m` vortex, the coordinates of `Sym ℂ m ≃ ℂᵐ`, are the Newton
coefficients of its flux moments `(2π)⁻¹ ∫ zᵏ iF_a`. -/
theorem esymm_framedVortexDivisor_eq_newtonCoeff_fluxMoment (x : framedVortexSubMulAction 1 m)
    (j : ℕ) : (framedVortexDivisor x : Multiset ℂ).esymm j = newtonCoeff (fluxMoment x) j := by
  rw [fluxMoment_eq_fun_sum_map_pow_framedVortexDivisor, newtonCoeff_sum_map_pow]

end TauCeti.Vortex
