/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Basic
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The Christoffel–Darboux identity for the Dirac system

For a potential `q` integrable on `[0, t]` and two spectral parameters `λ, z ∈ ℂ`, the fundamental
matrix `M = M_q` of the Dirac system `Ω X' = z X - Q_q X` (`TauCeti.diracFundamentalMatrix`)
satisfies the Christoffel–Darboux identity
`M(t, λ)* Ω M(t, z) - Ω = (z - conj λ) ∫₀ᵗ M(s, λ)* M(s, z) ds`
(`TauCeti.diracFundamentalMatrix_christoffelDarboux`). It is stated for the operators on
`EuclideanSpace ℂ (Fin 2)` (`Matrix.toEuclideanCLM`), where `*` is the adjoint. On the real axis
the right side vanishes, so `M(t, x)` is `Ω`-unitary
(`TauCeti.star_diracFundamentalMatrix_mul_mul_ofReal`).

The proof differentiates `G(s) = M(s, λ)* Ω M(s, z)`. Writing `P_w(s) = -Ω(w - Q_q(s))` for the
coefficient, at almost every `s` the derivative is `M(s, λ)* (P_λ(s)* Ω + Ω P_z(s)) M(s, z)`, and
`P_λ* Ω + Ω P_z = z - conj λ` because `Ω* = -Ω` and `Q_q(s)` is Hermitian
(`TauCeti.conjTranspose_diracCoeff_mul_add_mul_diracCoeff`). The curve `G` is absolutely
continuous, so the fundamental theorem of calculus for absolutely continuous curves gives the
identity, with `G(0) = Ω`.

## References

* R. Romanov, *Canonical systems and de Branges spaces*, arXiv:1408.6022, §1, identity (12).
-/

public section

open MeasureTheory Set Matrix ComplexConjugate

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

/-- The algebraic identity behind the Christoffel–Darboux formula: for the coefficient
`P_w(s) = -Ω(w - Q_q(s))`, `P_λ(s)* Ω + Ω P_z(s) = z - conj λ`. -/
theorem conjTranspose_diracCoeff_mul_add_mul_diracCoeff (q : ℝ → ℂ) (lam z : ℂ) (s : ℝ) :
    (diracCoeff q lam s)ᴴ * !![0, 1; -1, 0] + !![0, 1; -1, 0] * diracCoeff q z s =
      (z - conj lam) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracCoeff_def, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring

/-- `star` on the operators of `EuclideanSpace ℂ (Fin 2)`, as a real-linear isometry. -/
private noncomputable def starRealIsometry :
    (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ≃ₗᵢ[ℝ]
      (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
  (starₗᵢ ℂ).toIsometryEquiv.toRealLinearIsometryEquiv

private theorem starRealIsometry_apply
    (X : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :
    starRealIsometry X = star X := by
  simp [starRealIsometry]

/-- `r ↦ f(r)* J g(r)` is absolutely continuous when `f` and `g` are. -/
private theorem absolutelyContinuousOnInterval_star_mul_mul
    {f g : ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)} {a b : ℝ}
    (J : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun r ↦ star (f r) * J * g r) a b := by
  have hφ : ContDiff ℝ 1 fun p : (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ×
      (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ↦
        starRealIsometry p.1 * J * p.2 :=
    ((starRealIsometry.contDiff.comp contDiff_fst).mul contDiff_const).mul contDiff_snd
  have h := (hf.prodMk hg).comp_of_contDiffAt fun _ _ ↦ hφ.contDiffAt
  simpa only [Function.comp_def, starRealIsometry_apply] using h

/-- The derivative of `r ↦ f(r)* J g(r)`. -/
private theorem hasDerivAt_star_mul_mul
    {f g : ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)}
    {f' g' : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)} {r : ℝ}
    (J : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    (hf : HasDerivAt f f' r) (hg : HasDerivAt g g' r) :
    HasDerivAt (fun r ↦ star (f r) * J * g r) (star f' * J * g r + star (f r) * J * g') r := by
  have hstar : HasDerivAt (fun r ↦ star (f r)) (star f') r := by
    simp_rw [← starRealIsometry_apply]
    exact starRealIsometry.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt r hf
  exact (hstar.mul_const J).mul hg

/-- **The Christoffel–Darboux identity.** If `q` is integrable on `[0, t]` with `0 ≤ t`, then for
all `λ, z ∈ ℂ`, as operators on `EuclideanSpace ℂ (Fin 2)`,
`M(t, λ)* Ω M(t, z) - Ω = (z - conj λ) ∫₀ᵗ M(s, λ)* M(s, z) ds`, with `Ω = [[0, 1], [-1, 0]]`. -/
theorem diracFundamentalMatrix_christoffelDarboux (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (lam z : ℂ) :
    star (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q t lam)) *
        toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; -1, 0] *
          toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q t z) -
        toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; -1, 0] =
      (z - conj lam) • ∫ s in (0 : ℝ)..t,
        star (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q s lam)) *
          toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q s z) := by
  set P : ℂ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun w s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q w s)
  set J := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![(0 : ℂ), 1; -1, 0]
  have hP (w : ℂ) : IntegrableOn (P w) (Icc 0 t) := integrableOn_toEuclideanCLM_diracCoeff hq w
  have h0 : (0 : ℝ) ∈ Icc 0 t := left_mem_Icc.2 ht
  simp only [toEuclideanCLM_diracFundamentalMatrix]
  set N : ℂ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun w r ↦ propagator (P w) r 0
  change star (N lam t) * J * N z t - J =
    (z - conj lam) • ∫ s in (0 : ℝ)..t, star (N lam s) * N z s
  have hd (w : ℂ) : ∀ᵐ r, r ∈ Ioo 0 t → HasDerivAt (N w) (P w r ∘L N w r) r :=
    ae_hasDerivAt_propagator_left (hP w) h0
  have hN0 (w : ℂ) : N w 0 = 1 := propagator_self _ _
  -- The curve `G(s) = M(s, λ)* Ω M(s, z)` is absolutely continuous.
  have hG : AbsolutelyContinuousOnInterval (fun r ↦ star (N lam r) * J * N z r) 0 t :=
    absolutelyContinuousOnInterval_star_mul_mul J
    (absolutelyContinuousOnInterval_propagator_left (hP lam) h0)
    (absolutelyContinuousOnInterval_propagator_left (hP z) h0)
  clear_value N
  -- Its derivative is `(z - conj λ) M(s, λ)* M(s, z)` almost everywhere.
  have hkey (r : ℝ) : star (P lam r) * J + J * P z r = (z - conj lam) • 1 := by
    simp only [P, J, ← map_star, ← map_mul, ← map_add, star_eq_conjTranspose,
      conjTranspose_diracCoeff_mul_add_mul_diracCoeff, map_smul, map_one]
  have hder : ∀ᵐ r, r ∈ uIoc 0 t → HasDerivAt (fun r ↦ star (N lam r) * J * N z r)
      ((z - conj lam) • (star (N lam r) * N z r)) r := by
    filter_upwards [hd lam, hd z, Measure.ae_ne volume t] with r hl hz hrt hr
    rw [uIoc_of_le ht] at hr
    have hr' : r ∈ Ioo 0 t := ⟨hr.1, lt_of_le_of_ne hr.2 hrt⟩
    refine (hasDerivAt_star_mul_mul J (hl hr') (hz hr')).congr_deriv ?_
    simp only [← ContinuousLinearMap.mul_def, star_mul]
    calc star (N lam r) * star (P lam r) * J * N z r + star (N lam r) * J * (P z r * N z r)
        = star (N lam r) * (star (P lam r) * J + J * P z r) * N z r := by noncomm_ring
      _ = (z - conj lam) • (star (N lam r) * N z r) := by
        rw [hkey]
        ext1 v
        simp
  have h := hG.integral_eq_sub_of_ae_hasDerivAt hder
  rw [intervalIntegral.integral_smul] at h
  rw [h, hN0, hN0, star_one, one_mul, mul_one]

/-- On the real axis the fundamental matrix is `Ω`-unitary: for `x : ℝ`,
`M(t, x)* Ω M(t, x) = Ω`. -/
theorem star_diracFundamentalMatrix_mul_mul_ofReal (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (x : ℝ) :
    star (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q t x)) *
        toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; -1, 0] *
          toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q t x) =
      toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; -1, 0] := by
  have h := diracFundamentalMatrix_christoffelDarboux hq ht x x
  have h0 (X : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) : (0 : ℂ) • X = 0 := by
    ext1 v
    simp
  rw [Complex.conj_ofReal, sub_self, h0] at h
  exact sub_eq_zero.1 h

end TauCeti
