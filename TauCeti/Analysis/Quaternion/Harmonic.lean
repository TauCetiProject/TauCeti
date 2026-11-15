/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Quaternion.Basic
public import TauCeti.Analysis.Quaternion.Fueter
public import TauCeti.Analysis.Quaternion.Kernel
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Quaternion.Regularity

/-!
# Fueter regular functions are harmonic

Write `e = (1, i, j, k)` for the standard orthonormal basis `Quaternion.orthonormalBasisOneIJK`
of `ℍ`. The conjugate of the left Fueter operator `∂ₜ + i ∂ₓ + j ∂ᵧ + k ∂_z` is
`∂ₜ - i ∂ₓ - j ∂ᵧ - k ∂_z`, and their composite is the Euclidean Laplacian:

`(∂ₜ - i ∂ₓ - j ∂ᵧ - k ∂_z) (∂ₜ + i ∂ₓ + j ∂ᵧ + k ∂_z) = ∂ₜ² + ∂ₓ² + ∂ᵧ² + ∂_z²`.

The square terms give `-i * i = 1` and so on, and the mixed terms cancel in pairs, such as
`-i * j ∂ₓ∂ᵧ - j * i ∂ᵧ∂ₓ = 0`, once the mixed partial derivatives commute. The same holds on the
right, with the units multiplying from the right. At the level of second derivatives this is an
identity for every symmetric real bilinear map `B : ℍ →L[ℝ] ℍ →L[ℝ] ℍ`:

`∑ₙ star (e n) * fueterLeft (B (e n)) = ∑ₙ B (e n) (e n)`,

and its right counterpart with `fueterRight (B (e n)) * star (e n)`.

Because every function that is pointwise Fueter regular on a neighbourhood of `q` is automatically
real analytic, and hence smooth, at `q` (`TauCeti.LeftFueterOn.contDiffAt`,
`TauCeti.RightFueterOn.contDiffAt`), its first derivative is automatically differentiable at `q`
with symmetric second derivative (`second_derivative_symmetric_of_eventually`). Consequently, every
left or right Fueter regular function on a neighbourhood of `q` (and in particular on any open set)
is harmonic without any auxiliary `C²` hypothesis.

The converse fails: `q ↦ ((q.re ^ 2 - q.imI ^ 2 : ℝ) : ℍ)` (`t² - x²`) is harmonic everywhere on
`ℍ` yet is neither left nor right Fueter regular away from the plane `{q.re = 0 ∧ q.imI = 0}`.

## Main declarations

* `TauCeti.sum_star_orthonormalBasisOneIJK_mul_fueterLeft`,
  `TauCeti.sum_fueterRight_mul_star_orthonormalBasisOneIJK`: the conjugate operators compose with
  the Fueter operators to the trace of a symmetric bilinear map.
* `TauCeti.LeftFueterOn.laplacian_eq_zero`, `TauCeti.RightFueterOn.laplacian_eq_zero`: a function
  that is pointwise Fueter regular on a neighbourhood of `q` has vanishing Laplacian at `q`.
* `TauCeti.LeftFueterOn.laplacian_eq_zero_of_isOpen`,
  `TauCeti.RightFueterOn.laplacian_eq_zero_of_isOpen`: every left or right Fueter regular function
  on an open set is harmonic there.
* `TauCeti.laplacian_cauchyFueterKernel_eq_zero`: the Cauchy–Fueter kernel is harmonic away from
  its pole.
* `TauCeti.laplacian_re_sq_sub_imI_sq_eq_zero`,
  `TauCeti.not_leftFueterAt_re_sq_sub_imI_sq`,
  `TauCeti.not_rightFueterAt_re_sq_sub_imI_sq`: `t² - x²` is harmonic everywhere on `ℍ` but
  neither left nor right Fueter regular when `q.re ≠ 0` or `q.imI ≠ 0`.

## References

* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 3, equation (17) and the remark
  after Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Quaternion Filter Topology
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

/-- A function that is pointwise left Fueter regular on a neighbourhood of `q` has vanishing
Laplacian at `q`; no continuity or differentiability of `fderiv ℝ f` need be assumed. -/
theorem LeftFueterOn.laplacian_eq_zero (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) : Δ f q = 0 := by
  have h : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (((hf.contDiffAt (n := 2) hs).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)
  have hev : ∀ᶠ x in 𝓝 q, LeftFueterAt f x := eventually_of_mem hs (leftFueterOn_iff.1 hf)
  have hB := second_derivative_symmetric_of_eventually
    (hev.mono fun _ hx ↦ hx.differentiableAt.hasFDerivAt) h.hasFDerivAt
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f orthonormalBasisOneIJK]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sum_star_orthonormalBasisOneIJK_mul_fueterLeft hB]
  have hL (w : ℍ) : fueterLeft (fderiv ℝ (fderiv ℝ f) q w) = 0 := by
    simpa using clm_apply_fderiv_eq_zero (𝕜 := ℝ) (L := LinearMap.toContinuousLinearMap fueterLeft)
      (g := fderiv ℝ f) (hev.mono fun _ hx ↦ by simpa using hx.fueterLeft_fderiv) w
  simp [hL]

/-- A function that is pointwise right Fueter regular on a neighbourhood of `q` has vanishing
Laplacian at `q`; no continuity or differentiability of `fderiv ℝ f` need be assumed. -/
theorem RightFueterOn.laplacian_eq_zero (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) : Δ f q = 0 := by
  have h : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (((hf.contDiffAt (n := 2) hs).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)
  have hev : ∀ᶠ x in 𝓝 q, RightFueterAt f x := eventually_of_mem hs (rightFueterOn_iff.1 hf)
  have hB := second_derivative_symmetric_of_eventually
    (hev.mono fun _ hx ↦ hx.differentiableAt.hasFDerivAt) h.hasFDerivAt
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f orthonormalBasisOneIJK]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sum_fueterRight_mul_star_orthonormalBasisOneIJK hB]
  have hL (w : ℍ) : fueterRight (fderiv ℝ (fderiv ℝ f) q w) = 0 := by
    simpa using clm_apply_fderiv_eq_zero (𝕜 := ℝ) (L := LinearMap.toContinuousLinearMap fueterRight)
      (g := fderiv ℝ f) (hev.mono fun _ hx ↦ by simpa using hx.fueterRight_fderiv) w
  simp [hL]

/-- **Left Fueter regular functions are harmonic.** Every pointwise left Fueter regular function on
an open set has vanishing Laplacian at every point of that set. -/
theorem LeftFueterOn.laplacian_eq_zero_of_isOpen (hf : LeftFueterOn f s) (hs : IsOpen s)
    (hq : q ∈ s) : Δ f q = 0 :=
  hf.laplacian_eq_zero (hs.mem_nhds hq)

/-- **Right Fueter regular functions are harmonic.** Every pointwise right Fueter regular function
on an open set has vanishing Laplacian at every point of that set. -/
theorem RightFueterOn.laplacian_eq_zero_of_isOpen (hf : RightFueterOn f s) (hs : IsOpen s)
    (hq : q ∈ s) : Δ f q = 0 :=
  hf.laplacian_eq_zero (hs.mem_nhds hq)

/-- The Cauchy–Fueter kernel `x ↦ cauchyFueterKernel x q₀` is harmonic away from its pole `q₀`. -/
theorem laplacian_cauchyFueterKernel_eq_zero {q q₀ : ℍ} (hq : q ≠ q₀) :
    Δ (fun x ↦ cauchyFueterKernel x q₀) q = 0 :=
  (leftFueterOn_cauchyFueterKernel (s := {q₀}ᶜ) (by simp)).laplacian_eq_zero_of_isOpen
    isOpen_compl_singleton hq

/-! ### Failure of the converse: harmonic does not imply Fueter regular -/

private noncomputable def reSubImIBilinear : ℍ →L[ℝ] ℍ →L[ℝ] ℍ :=
  let L₀ : ℍ →L[ℝ] ℝ := (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap
  let L₁ : ℍ →L[ℝ] ℝ := (QuaternionAlgebra.imIₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap
  let ι : ℝ →L[ℝ] ℍ := (Algebra.linearMap ℝ ℍ).toContinuousLinearMap
  ((2 : ℝ) • L₀).smulRight (ι.comp L₀) - ((2 : ℝ) • L₁).smulRight (ι.comp L₁)

private theorem hasFDerivAt_re_sq_sub_imI_sq (q : ℍ) :
    HasFDerivAt (fun x : ℍ ↦ ((x.re ^ 2 - x.imI ^ 2 : ℝ) : ℍ)) (reSubImIBilinear q) q := by
  let L₀ : ℍ →L[ℝ] ℝ := (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap
  let L₁ : ℍ →L[ℝ] ℝ := (QuaternionAlgebra.imIₗ (-1 : ℝ) 0 (-1)).toContinuousLinearMap
  let ι : ℝ →L[ℝ] ℍ := (Algebra.linearMap ℝ ℍ).toContinuousLinearMap
  have h0 := (hasDerivAt_pow 2 (L₀ q)).comp_hasFDerivAt q L₀.hasFDerivAt
  have h1 := (hasDerivAt_pow 2 (L₁ q)).comp_hasFDerivAt q L₁.hasFDerivAt
  have hcomp := ι.hasFDerivAt.comp q (h0.sub h1)
  have hfn : (ι ∘ (((· ^ 2) ∘ L₀) - ((· ^ 2) ∘ L₁))) =
      fun x : ℍ ↦ ((x.re ^ 2 - x.imI ^ 2 : ℝ) : ℍ) := rfl
  rw [hfn] at hcomp
  convert hcomp using 1
  ext h <;> simp [reSubImIBilinear, ι, L₀, L₁, mul_comm]

/-- The quadratic harmonic polynomial `q ↦ (q.re ^ 2 - q.imI ^ 2 : ℍ)` (`t² - x²`) has vanishing
Laplacian everywhere on `ℍ`. -/
theorem laplacian_re_sq_sub_imI_sq_eq_zero (q : ℍ) :
    Δ (fun x : ℍ ↦ ((x.re ^ 2 - x.imI ^ 2 : ℝ) : ℍ)) q = 0 := by
  have hfderiv : fderiv ℝ (fun x : ℍ ↦ ((x.re ^ 2 - x.imI ^ 2 : ℝ) : ℍ)) = reSubImIBilinear := by
    funext x
    exact (hasFDerivAt_re_sq_sub_imI_sq x).fderiv
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ orthonormalBasisOneIJK]
  simp only [iteratedFDeriv_two_apply, hfderiv, ContinuousLinearMap.fderiv,
    Fin.sum_univ_four, coe_orthonormalBasisOneIJK, Matrix.cons_val]
  ext <;> simp [reSubImIBilinear]

/-- Harmonicity does not imply left Fueter regularity: `q ↦ (q.re ^ 2 - q.imI ^ 2 : ℍ)` is not left
Fueter regular at any `q` with `q.re ≠ 0` or `q.imI ≠ 0`. -/
theorem not_leftFueterAt_re_sq_sub_imI_sq {q : ℍ} (hq : q.re ≠ 0 ∨ q.imI ≠ 0) :
    ¬ LeftFueterAt (fun x : ℍ ↦ ((x.re ^ 2 - x.imI ^ 2 : ℝ) : ℍ)) q := by
  rw [(hasFDerivAt_re_sq_sub_imI_sq q).leftFueterAt_iff, fueterLeft_apply]
  intro h0
  rcases hq with hre | him
  · exact hre (by simpa [reSubImIBilinear] using congrArg QuaternionAlgebra.re h0)
  · exact him (by simpa [reSubImIBilinear] using congrArg QuaternionAlgebra.imI h0)

/-- Harmonicity does not imply right Fueter regularity: `q ↦ (q.re ^ 2 - q.imI ^ 2 : ℍ)` is not
right Fueter regular at any `q` with `q.re ≠ 0` or `q.imI ≠ 0`. -/
theorem not_rightFueterAt_re_sq_sub_imI_sq {q : ℍ} (hq : q.re ≠ 0 ∨ q.imI ≠ 0) :
    ¬ RightFueterAt (fun x : ℍ ↦ ((x.re ^ 2 - x.imI ^ 2 : ℝ) : ℍ)) q := by
  rw [(hasFDerivAt_re_sq_sub_imI_sq q).rightFueterAt_iff, fueterRight_apply]
  intro h0
  rcases hq with hre | him
  · exact hre (by simpa [reSubImIBilinear] using congrArg QuaternionAlgebra.re h0)
  · exact him (by simpa [reSubImIBilinear] using congrArg QuaternionAlgebra.imI h0)

end TauCeti
