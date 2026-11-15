/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.Quaternion.Basic
public import TauCeti.Analysis.Quaternion.Fueter
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Quaternion.Analytic
import TauCeti.Analysis.Quaternion.PartialDeriv

/-!
# Fueter regular functions are harmonic

Write `e = (1, i, j, k)` for the standard orthonormal basis `Quaternion.orthonormalBasisOneIJK`
of `ℍ`. The conjugate of the left Fueter operator
`∂ₜ + i ∂ₓ + j ∂ᵧ + k ∂_z` is `∂ₜ - i ∂ₓ - j ∂ᵧ - k ∂_z`, and their composite is the Laplacian:

`(∂ₜ - i ∂ₓ - j ∂ᵧ - k ∂_z) (∂ₜ + i ∂ₓ + j ∂ᵧ + k ∂_z) = ∂ₜ² + ∂ₓ² + ∂ᵧ² + ∂_z²`.

The square terms give `-i * i = 1` and so on, and the mixed terms cancel in pairs, such as
`-i * j ∂ₓ∂ᵧ - j * i ∂ᵧ∂ₓ = 0`, once the mixed partial derivatives commute. The same holds on the
right, with the units multiplying from the right. At the level of second derivatives this is an
identity for every symmetric real bilinear map `B : ℍ →L[ℝ] ℍ →L[ℝ] ℍ`:

`∑ₙ star (e n) * fueterLeft (B (e n)) = ∑ₙ B (e n) (e n)`,

and its right counterpart with `fueterRight (B (e n)) * star (e n)`.

Because pointwise left or right Fueter regularity on a neighbourhood of `q` already implies real
analyticity and `C^∞` smoothness at `q` (`TauCeti.LeftFueterOn.contDiffAt`,
`TauCeti.RightFueterOn.contDiffAt`), the second derivative exists automatically and is symmetric by
`second_derivative_symmetric_of_eventually`. Consequently every left or right Fueter regular
function on an open set is unconditionally harmonic (`Δ f q = 0` and
`InnerProductSpace.HarmonicOnNhd f s`), with no extra `C²` hypothesis. The converse fails:
`q ↦ t² - x²` is harmonic on all of `ℍ` (`harmonicOnNhd_re_sq_sub_imI_sq`) yet neither left nor
right Fueter regular at `1`.

## Main declarations

* `TauCeti.sum_star_orthonormalBasisOneIJK_mul_fueterLeft`,
  `TauCeti.sum_fueterRight_mul_star_orthonormalBasisOneIJK`: the conjugate operators compose with
  the Fueter operators to the trace of a symmetric bilinear map.
* `TauCeti.LeftFueterOn.laplacian_eq_zero`, `TauCeti.RightFueterOn.laplacian_eq_zero`,
  `TauCeti.LeftFueterOn.laplacian_eq_zero_of_isOpen`,
  `TauCeti.RightFueterOn.laplacian_eq_zero_of_isOpen`: pointwise Fueter regularity on a
  neighbourhood of `q` (in particular on an open set containing `q`) forces `Δ f q = 0`.
* `TauCeti.LeftFueterOn.harmonicAt`, `TauCeti.RightFueterOn.harmonicAt`,
  `TauCeti.LeftFueterOn.harmonicOnNhd`, `TauCeti.RightFueterOn.harmonicOnNhd`: Fueter regular
  functions satisfy `InnerProductSpace.HarmonicAt` and `InnerProductSpace.HarmonicOnNhd`.
* `TauCeti.harmonicOnNhd_re_sq_sub_imI_sq`, `TauCeti.not_leftFueterAt_re_sq_sub_imI_sq`,
  `TauCeti.not_rightFueterAt_re_sq_sub_imI_sq`: `q ↦ t² - x²` is harmonic everywhere on `ℍ` but
  Fueter regular on neither side.

## References

* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, equation (17) and the remark after Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Quaternion Filter Set Topology
open scoped Laplacian

namespace TauCeti

variable {f : ℍ → ℍ} {s : Set ℍ} {q : ℍ}

/-- For a symmetric real bilinear map `B`, such as a second derivative, the conjugate operator
`∂ₜ - i ∂ₓ - j ∂ᵧ - k ∂_z` applied to `v ↦ fueterLeft (B v)` is the trace of `B`:
`∑ₙ star (e n) * fueterLeft (B (e n)) = ∑ₙ B (e n) (e n)` for the basis `e = (1, i, j, k)`. -/
theorem sum_star_orthonormalBasisOneIJK_mul_fueterLeft {B : ℍ →L[ℝ] ℍ →L[ℝ] ℍ}
    (hB : ∀ v w, B v w = B w v) :
    ∑ n : Fin 4, star (orthonormalBasisOneIJK n) *
        fueterLeft (B (orthonormalBasisOneIJK n)) =
      ∑ n : Fin 4, B (orthonormalBasisOneIJK n)
        (orthonormalBasisOneIJK n) := by
  simp only [Fin.sum_univ_four, coe_orthonormalBasisOneIJK, Matrix.cons_val, fueterLeft_apply]
  rw [hB ⟨0, 1, 0, 0⟩ 1, hB ⟨0, 0, 1, 0⟩ 1, hB ⟨0, 0, 0, 1⟩ 1, hB ⟨0, 0, 1, 0⟩ ⟨0, 1, 0, 0⟩,
    hB ⟨0, 0, 0, 1⟩ ⟨0, 1, 0, 0⟩, hB ⟨0, 0, 0, 1⟩ ⟨0, 0, 1, 0⟩]
  ext <;> simp <;> ring

/-- For a symmetric real bilinear map `B`, such as a second derivative, the conjugate operator
`∂ₜ - ∂ₓ i - ∂ᵧ j - ∂_z k` applied to `v ↦ fueterRight (B v)` is the trace of `B`:
`∑ₙ fueterRight (B (e n)) * star (e n) = ∑ₙ B (e n) (e n)` for the basis `e = (1, i, j, k)`. -/
theorem sum_fueterRight_mul_star_orthonormalBasisOneIJK {B : ℍ →L[ℝ] ℍ →L[ℝ] ℍ}
    (hB : ∀ v w, B v w = B w v) :
    ∑ n : Fin 4, fueterRight (B (orthonormalBasisOneIJK n)) *
        star (orthonormalBasisOneIJK n) =
      ∑ n : Fin 4, B (orthonormalBasisOneIJK n)
        (orthonormalBasisOneIJK n) := by
  simp only [Fin.sum_univ_four, coe_orthonormalBasisOneIJK, Matrix.cons_val, fueterRight_apply]
  rw [hB ⟨0, 1, 0, 0⟩ 1, hB ⟨0, 0, 1, 0⟩ 1, hB ⟨0, 0, 0, 1⟩ 1, hB ⟨0, 0, 1, 0⟩ ⟨0, 1, 0, 0⟩,
    hB ⟨0, 0, 0, 1⟩ ⟨0, 1, 0, 0⟩, hB ⟨0, 0, 0, 1⟩ ⟨0, 0, 1, 0⟩]
  ext <;> simp <;> ring

/-- A function pointwise left Fueter regular on a neighbourhood of `q` has vanishing Laplacian at
`q`, with no smoothness beyond pointwise first-order regularity assumed. -/
theorem LeftFueterOn.laplacian_eq_zero (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) : Δ f q = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (((hf.contDiffAt hs (n := 2)).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)
  have hev : ∀ᶠ x in 𝓝 q, LeftFueterAt f x := eventually_of_mem hs (leftFueterOn_iff.1 hf)
  have hB := second_derivative_symmetric_of_eventually
    (hev.mono fun _ hx ↦ hx.differentiableAt.hasFDerivAt) hd.hasFDerivAt
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f orthonormalBasisOneIJK]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sum_star_orthonormalBasisOneIJK_mul_fueterLeft hB]
  have hL (w : ℍ) : fueterLeft (fderiv ℝ (fderiv ℝ f) q w) = 0 := by
    simpa using clm_apply_fderiv_eq_zero (𝕜 := ℝ) (L := LinearMap.toContinuousLinearMap fueterLeft)
      (g := fderiv ℝ f) (hev.mono fun _ hx ↦ by simpa using hx.fueterLeft_fderiv) w
  simp [hL]

/-- A function pointwise right Fueter regular on a neighbourhood of `q` has vanishing Laplacian at
`q`, with no smoothness beyond pointwise first-order regularity assumed. -/
theorem RightFueterOn.laplacian_eq_zero (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) : Δ f q = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (((hf.contDiffAt hs (n := 2)).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)
  have hev : ∀ᶠ x in 𝓝 q, RightFueterAt f x := eventually_of_mem hs (rightFueterOn_iff.1 hf)
  have hB := second_derivative_symmetric_of_eventually
    (hev.mono fun _ hx ↦ hx.differentiableAt.hasFDerivAt) hd.hasFDerivAt
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f orthonormalBasisOneIJK]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sum_fueterRight_mul_star_orthonormalBasisOneIJK hB]
  have hL (w : ℍ) : fueterRight (fderiv ℝ (fderiv ℝ f) q w) = 0 := by
    simpa using clm_apply_fderiv_eq_zero (𝕜 := ℝ) (L := LinearMap.toContinuousLinearMap fueterRight)
      (g := fderiv ℝ f) (hev.mono fun _ hx ↦ by simpa using hx.fueterRight_fderiv) w
  simp [hL]

/-- Every left Fueter regular function on an open set has vanishing Laplacian there. -/
theorem LeftFueterOn.laplacian_eq_zero_of_isOpen (hf : LeftFueterOn f s) (hs : IsOpen s)
    (hq : q ∈ s) : Δ f q = 0 :=
  hf.laplacian_eq_zero (hs.mem_nhds hq)

/-- Every right Fueter regular function on an open set has vanishing Laplacian there. -/
theorem RightFueterOn.laplacian_eq_zero_of_isOpen (hf : RightFueterOn f s) (hs : IsOpen s)
    (hq : q ∈ s) : Δ f q = 0 :=
  hf.laplacian_eq_zero (hs.mem_nhds hq)

/-- Pointwise left Fueter regularity on a neighbourhood of `q` implies `HarmonicAt` at `q`. -/
theorem LeftFueterOn.harmonicAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) :
    InnerProductSpace.HarmonicAt f q := by
  refine ⟨hf.contDiffAt hs, ?_⟩
  filter_upwards [eventually_mem_nhds_iff.2 hs] with x hx
  exact hf.laplacian_eq_zero hx

/-- Pointwise right Fueter regularity on a neighbourhood of `q` implies `HarmonicAt` at `q`. -/
theorem RightFueterOn.harmonicAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) :
    InnerProductSpace.HarmonicAt f q := by
  refine ⟨hf.contDiffAt hs, ?_⟩
  filter_upwards [eventually_mem_nhds_iff.2 hs] with x hx
  exact hf.laplacian_eq_zero hx

/-- Every left Fueter regular function on an open set `s` is harmonic on a neighbourhood of `s`. -/
theorem LeftFueterOn.harmonicOnNhd (hf : LeftFueterOn f s) (hs : IsOpen s) :
    InnerProductSpace.HarmonicOnNhd f s :=
  fun _ hq ↦ hf.harmonicAt (hs.mem_nhds hq)

/-- Every right Fueter regular function on an open set `s` is harmonic on a neighbourhood of `s`. -/
theorem RightFueterOn.harmonicOnNhd (hf : RightFueterOn f s) (hs : IsOpen s) :
    InnerProductSpace.HarmonicOnNhd f s :=
  fun _ hq ↦ hf.harmonicAt (hs.mem_nhds hq)

/-- The scalar harmonic polynomial `q ↦ t² - x²` (embedded into `ℍ`) is harmonic on all of `ℍ`. -/
theorem harmonicOnNhd_re_sq_sub_imI_sq :
    InnerProductSpace.HarmonicOnNhd (fun q : ℍ ↦ ((q.re ^ 2 - q.imI ^ 2 : ℝ) : ℍ)) univ := by
  have hreg : LeftFueterOn (fun q : ℍ ↦ (((⟨q.re, q.imI⟩ : ℂ) ^ 2 : ℂ) : ℍ)) univ :=
    leftFueterOn_coeComplex_comp isOpen_univ (differentiable_id.pow 2).differentiableOn
  let reL : ℍ →L[ℝ] ℍ := (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.smulRight 1
  convert (hreg.harmonicOnNhd isOpen_univ).comp_CLM reL using 1
  ext q <;> simp [reL, sq]

private theorem hasFDerivAt_re_sq_sub_imI_sq_one :
    ∃ D : ℍ →L[ℝ] ℍ, HasFDerivAt (fun q : ℍ ↦ ((q.re ^ 2 - q.imI ^ 2 : ℝ) : ℍ)) D 1 ∧
      D 1 = 2 ∧ D ⟨0, 1, 0, 0⟩ = 0 ∧ D ⟨0, 0, 1, 0⟩ = 0 ∧ D ⟨0, 0, 0, 1⟩ = 0 := by
  have h1 : (⟨(1 : ℍ).re, (1 : ℍ).imI⟩ : ℂ) = 1 := by apply Complex.ext <;> simp
  have hderiv : HasDerivAt (fun z : ℂ ↦ z ^ 2) 2 ⟨(1 : ℍ).re, (1 : ℍ).imI⟩ := by
    rw [h1]
    simpa using hasDerivAt_pow 2 (1 : ℂ)
  obtain ⟨E, hE, hE1, hEi, hEj, hEk⟩ := exists_hasFDerivAt_coeComplex_comp (q := 1) hderiv
  let reL : ℍ →L[ℝ] ℍ := (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap.smulRight 1
  have heq : (fun q : ℍ ↦ ((q.re ^ 2 - q.imI ^ 2 : ℝ) : ℍ)) =
      reL ∘ fun q : ℍ ↦ (((⟨q.re, q.imI⟩ : ℂ) ^ 2 : ℂ) : ℍ) := by
    ext q <;> simp [reL, sq]
  refine ⟨reL.comp E, heq ▸ reL.hasFDerivAt.comp (1 : ℍ) hE, ?_, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.comp_apply, hE1]
    simp only [reL, ContinuousLinearMap.smulRight_apply, Algebra.smul_def, mul_one]
    norm_cast
  · rw [ContinuousLinearMap.comp_apply, hEi]
    simp [reL]
  · simp [hEj]
  · simp [hEk]

/-- Harmonicity does not imply left Fueter regularity: `q ↦ t² - x²` is harmonic on `ℍ`
(`harmonicOnNhd_re_sq_sub_imI_sq`) yet not left Fueter regular at `1`. -/
theorem not_leftFueterAt_re_sq_sub_imI_sq :
    ¬ LeftFueterAt (fun q : ℍ ↦ ((q.re ^ 2 - q.imI ^ 2 : ℝ) : ℍ)) 1 := by
  obtain ⟨D, hD, h1, hi, hj, hk⟩ := hasFDerivAt_re_sq_sub_imI_sq_one
  rw [hD.leftFueterAt_iff, fueterLeft_apply, h1, hi, hj, hk]
  intro h0
  simpa [QuaternionAlgebra.re_ofNat] using congrArg QuaternionAlgebra.re h0

/-- Harmonicity does not imply right Fueter regularity: `q ↦ t² - x²` is harmonic on `ℍ` yet not
right Fueter regular at `1`. -/
theorem not_rightFueterAt_re_sq_sub_imI_sq :
    ¬ RightFueterAt (fun q : ℍ ↦ ((q.re ^ 2 - q.imI ^ 2 : ℝ) : ℍ)) 1 := by
  obtain ⟨D, hD, h1, hi, hj, hk⟩ := hasFDerivAt_re_sq_sub_imI_sq_one
  rw [hD.rightFueterAt_iff, fueterRight_apply, h1, hi, hj, hk]
  intro h0
  simpa [QuaternionAlgebra.re_ofNat] using congrArg QuaternionAlgebra.re h0

end TauCeti
