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

The proof differentiates `G(s) = M(s, λ)* Ω M(s, z)`. Writing `P_w(s) = -Ω(w - Q_q(s))` for the
coefficient, at almost every `s` the derivative is `M(s, λ)* (P_λ(s)* Ω + Ω P_z(s)) M(s, z)`, and
`P_λ* Ω + Ω P_z = z - conj λ` because `Ω* = -Ω` and `Q_q(s)` is Hermitian
(`TauCeti.conjTranspose_diracCoeff_mul_add_mul_diracCoeff`). The curve `G` is absolutely
continuous (`AbsolutelyContinuousOnInterval.star` and `AbsolutelyContinuousOnInterval.mul'`), so
the fundamental theorem of calculus for absolutely continuous curves gives the identity, with
`G(0) = Ω`.

## References

* R. Romanov, *Canonical systems and de Branges spaces*, arXiv:1408.6022, §1, identity (12).
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

end TauCeti
