/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The Christoffel–Darboux identity for the Dirac system

For a potential `q` integrable on `[0, t]` (or `[t, 0]`) and two spectral parameters `λ, z ∈ ℂ`,
the fundamental matrix `M = M_q` of the Dirac system `Ω X' = z X - Q_q X`
(`TauCeti.diracFundamentalMatrix`) satisfies the Christoffel–Darboux identity
`M(t, λ)* Ω M(t, z) - Ω = (z - conj λ) ∫₀ᵗ M(s, λ)* M(s, z) ds`
(`TauCeti.diracFundamentalMatrix_christoffelDarboux`). It is stated for the operators on
`EuclideanSpace ℂ (Fin 2)` (`Matrix.toEuclideanCLM`), where `*` is the adjoint. On the real axis
the right side vanishes, so the matrix `M(t, x)` is `Ω`-unitary
(`TauCeti.conjTranspose_diracFundamentalMatrix_mul_mul_ofReal`).

Entrywise (`TauCeti.diracFundamentalMatrix_christoffelDarboux_apply`), the diagonal entries give
the kernel identity of each column `(X₀, X₁)` of `M`, namely of the Neumann solution `Θ = (A, C)`
and of the Dirichlet solution `Φ = (B, D)`:
`X₀(t, z) conj X₁(t, w) - X₁(t, z) conj X₀(t, w) = (conj w - z) ∫₀ᵗ X(s, w)* X(s, z) ds`
(`TauCeti.diracFundamentalMatrix_mul_conj_sub_mul_conj`). At `w = z` this reads
`Im (conj X₀(t, z) X₁(t, z)) = Im z ∫₀ᵗ |X(s, z)|² ds`
(`TauCeti.im_conj_mul_diracFundamentalMatrix`), the identity behind the Hermite–Biehler property
of `A - iC` and `B - iD`.

The proof differentiates `G(s) = M(s, λ)* Ω M(s, z)`. Writing `P_w(s) = -Ω(w - Q_q(s))` for the
coefficient, at almost every `s` the derivative is `M(s, λ)* (P_λ(s)* Ω + Ω P_z(s)) M(s, z)`, and
`P_λ* Ω + Ω P_z = z - conj λ` because `Ω* = -Ω` and `Q_q(s)` is Hermitian
(`TauCeti.conjTranspose_diracCoeff_mul_add_mul_diracCoeff`). The curve `G` is absolutely
continuous (`AbsolutelyContinuousOnInterval.star` and `AbsolutelyContinuousOnInterval.mul'`), so
the fundamental theorem of calculus for absolutely continuous curves gives the identity, with
`G(0) = Ω`.

## References

* R. Romanov, *Canonical systems and de Branges spaces*, arXiv:1408.6022, §1, identity (12).
* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
-/

public section

open MeasureTheory Set Matrix ComplexConjugate

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ}

/-- **The Christoffel–Darboux identity.** If `q` is integrable on `[0, t]` (or `[t, 0]`), then for
all `λ, z ∈ ℂ`, as operators on `EuclideanSpace ℂ (Fin 2)`,
`M(t, λ)* Ω M(t, z) - Ω = (z - conj λ) ∫₀ᵗ M(s, λ)* M(s, z) ds`, with `Ω = [[0, 1], [-1, 0]]`. -/
theorem diracFundamentalMatrix_christoffelDarboux (hq : IntegrableOn q (uIcc 0 t)) (lam z : ℂ) :
    star (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q t lam)) *
        toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; -1, 0] *
          toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q t z) -
        toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; -1, 0] =
      (z - conj lam) • ∫ s in (0 : ℝ)..t,
        star (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q s lam)) *
          toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q s z) := by
  set J := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![(0 : ℂ), 1; -1, 0]
  let P : ℂ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun w s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q w s)
  let N : ℂ → ℝ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    fun w r ↦ propagator (P w) r 0
  have hN (w : ℂ) (r : ℝ) :
      toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q r w) = N w r :=
    toEuclideanCLM_diracFundamentalMatrix q r w
  simp only [hN]
  have hP (w : ℂ) : IntegrableOn (P w) (uIcc 0 t) := integrableOn_toEuclideanCLM_diracCoeff hq w
  have h0 : (0 : ℝ) ∈ uIcc 0 t := left_mem_uIcc
  have hd (w : ℂ) : ∀ᵐ r, r ∈ Ioo (0 ⊓ t) (0 ⊔ t) → HasDerivAt (N w) (P w r ∘L N w r) r :=
    ae_hasDerivAt_propagator_left (hP w) h0
  have hN0 (w : ℂ) : N w 0 = 1 := propagator_self _ _
  -- The curve `G(s) = M(s, λ)* Ω M(s, z)` is absolutely continuous.
  have hG : AbsolutelyContinuousOnInterval (fun r ↦ star (N lam r) * J * N z r) 0 t :=
    (((absolutelyContinuousOnInterval_propagator_left (hP lam) h0).star.fun_mul'
      (contDiffOn_const.absolutelyContinuousOnInterval)).fun_mul'
      (absolutelyContinuousOnInterval_propagator_left (hP z) h0)).mono
      (uIcc_of_le inf_le_sup).ge
  clear_value N
  -- Its derivative is `(z - conj λ) M(s, λ)* M(s, z)` almost everywhere.
  have hkey (r : ℝ) : star (P lam r) * J + J * P z r = (z - conj lam) • 1 := by
    simp only [P, J, ← map_star, ← map_mul, ← map_add, star_eq_conjTranspose,
      conjTranspose_diracCoeff_mul_add_mul_diracCoeff, map_smul, map_one]
  have hder : ∀ᵐ r, r ∈ uIoc 0 t → HasDerivAt (fun r ↦ star (N lam r) * J * N z r)
      ((z - conj lam) • (star (N lam r) * N z r)) r := by
    filter_upwards [hd lam, hd z, Measure.ae_ne volume 0, Measure.ae_ne volume t]
      with r hl hz hr0 hrt hr
    have hr' : r ∈ Ioo (0 ⊓ t) (0 ⊔ t) :=
      ⟨hr.1, hr.2.lt_of_ne <| by rcases max_choice 0 t with h | h <;> rw [h] <;> assumption⟩
    refine (((hl hr').star.mul_const J).mul (hz hr')).congr_deriv ?_
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
`M(t, x)ᴴ Ω M(t, x) = Ω`. -/
theorem conjTranspose_diracFundamentalMatrix_mul_mul_ofReal (hq : IntegrableOn q (uIcc 0 t))
    (x : ℝ) :
    (diracFundamentalMatrix q t x)ᴴ * !![0, 1; -1, 0] * diracFundamentalMatrix q t x =
      !![0, 1; -1, 0] := by
  apply EquivLike.injective (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
  have h := diracFundamentalMatrix_christoffelDarboux hq x x
  -- `zero_smul` does not unify with this `ℂ`-action on the operators of
  -- `EuclideanSpace ℂ (Fin 2)`, even by `rw` or as a term, so `0 • X = 0` is checked pointwise.
  have h0 (X : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) : (0 : ℂ) • X = 0 := by
    ext1 v
    simp
  rw [Complex.conj_ofReal, sub_self, h0] at h
  rw [map_mul, map_mul, ← star_eq_conjTranspose, map_star]
  exact sub_eq_zero.1 h

/-- **The Christoffel–Darboux identity, entrywise.** If `q` is integrable on `[0, t]` (or
`[t, 0]`), then for all `λ, z ∈ ℂ` and indices `i, j`,
`(M(t, λ)ᴴ Ω M(t, z))ᵢⱼ - Ωᵢⱼ = (z - conj λ) ∫₀ᵗ (M(s, λ)ᴴ M(s, z))ᵢⱼ ds`, with
`Ω = [[0, 1], [-1, 0]]`. -/
theorem diracFundamentalMatrix_christoffelDarboux_apply (hq : IntegrableOn q (uIcc 0 t))
    (lam z : ℂ) (i j : Fin 2) :
    ((diracFundamentalMatrix q t lam)ᴴ * !![0, 1; -1, 0] * diracFundamentalMatrix q t z :
          Matrix (Fin 2) (Fin 2) ℂ) i j - !![(0 : ℂ), 1; -1, 0] i j =
      (z - conj lam) * ∫ s in (0 : ℝ)..t,
        ((diracFundamentalMatrix q s lam)ᴴ * diracFundamentalMatrix q s z) i j := by
  have hc (w : ℂ) : ContinuousOn
      (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q s w)) (uIcc 0 t) := by
    simp only [toEuclideanCLM_diracFundamentalMatrix]
    exact continuousOn_propagator_left (integrableOn_toEuclideanCLM_diracCoeff hq w) left_mem_uIcc
  -- The integrand of the operator identity is continuous, so the evaluation at the basis vector
  -- `eⱼ` followed by the `i`-th coordinate commutes with the integral.
  have hFc : ContinuousOn (fun s ↦
      star (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q s lam)) *
        toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q s z)) (uIcc 0 t) :=
    ((star_isometry (E := EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))).continuous
      |>.comp_continuousOn (hc lam)).mul (hc z)
  have h := congrArg (fun X ↦ EuclideanSpace.proj (𝕜 := ℂ) i (X (EuclideanSpace.single j 1)))
    (diracFundamentalMatrix_christoffelDarboux hq lam z)
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.intervalIntegral_apply hFc.intervalIntegrable, map_sub, map_smul] at h
  rw [← (EuclideanSpace.proj (𝕜 := ℂ) i).intervalIntegral_comp_comm
    (hFc.clm_apply continuousOn_const).intervalIntegrable] at h
  have he (X : Matrix (Fin 2) (Fin 2) ℂ) :
      EuclideanSpace.proj (𝕜 := ℂ) i (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) X
        (EuclideanSpace.single j 1)) = X i j := by
    simp
  have hs (X : Matrix (Fin 2) (Fin 2) ℂ) :
      star (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) X) = toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) Xᴴ := by
    rw [← star_eq_conjTranspose, map_star]
  simp only [hs, ← map_mul, he] at h
  simpa using h

/-- **The kernel identity of a column.** If `q` is integrable on `[0, t]` (or `[t, 0]`), the `j`-th
column `X = (X₀, X₁)` of the fundamental matrix (the Neumann solution `Θ = (A, C)` for `j = 0`,
the Dirichlet solution `Φ = (B, D)` for `j = 1`) satisfies, for all `w, z ∈ ℂ`,
`X₀(t, z) conj X₁(t, w) - X₁(t, z) conj X₀(t, w) = (conj w - z) ∫₀ᵗ X(s, w)* X(s, z) ds`. -/
theorem diracFundamentalMatrix_mul_conj_sub_mul_conj (hq : IntegrableOn q (uIcc 0 t))
    (w z : ℂ) (j : Fin 2) :
    diracFundamentalMatrix q t z 0 j * conj (diracFundamentalMatrix q t w 1 j) -
        diracFundamentalMatrix q t z 1 j * conj (diracFundamentalMatrix q t w 0 j) =
      (conj w - z) * ∫ s in (0 : ℝ)..t,
        (conj (diracFundamentalMatrix q s w 0 j) * diracFundamentalMatrix q s z 0 j +
          conj (diracFundamentalMatrix q s w 1 j) * diracFundamentalMatrix q s z 1 j) := by
  have h := diracFundamentalMatrix_christoffelDarboux_apply hq w z j j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply] at h
  fin_cases j <;> simp at h ⊢ <;> linear_combination -h

/-- **The kernel identity on the diagonal.** If `q` is integrable on `[0, t]` (or `[t, 0]`), the
`j`-th column `X = (X₀, X₁)` of the fundamental matrix satisfies
`Im (conj X₀(t, z) X₁(t, z)) = Im z ∫₀ᵗ (|X₀(s, z)|² + |X₁(s, z)|²) ds`. -/
theorem im_conj_mul_diracFundamentalMatrix (hq : IntegrableOn q (uIcc 0 t)) (z : ℂ)
    (j : Fin 2) :
    (conj (diracFundamentalMatrix q t z 0 j) * diracFundamentalMatrix q t z 1 j).im =
      z.im * ∫ s in (0 : ℝ)..t,
        (‖diracFundamentalMatrix q s z 0 j‖ ^ 2 + ‖diracFundamentalMatrix q s z 1 j‖ ^ 2) := by
  have h := diracFundamentalMatrix_mul_conj_sub_mul_conj hq z z j
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_add,
    intervalIntegral.integral_ofReal] at h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im] at this
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  linarith

end TauCeti
