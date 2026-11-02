/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Quaternion.Basic
public import TauCeti.Analysis.Quaternion.Fueter

/-!
# Twice differentiable Fueter regular functions are harmonic

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

Applied to the second derivative of a function that is Fueter regular near `q` and whose
derivative is differentiable at `q`, the left side vanishes, because the Fueter operator applied
to the first derivative vanishes near `q`, and the right side is the Laplacian, computed in the
orthonormal basis `e`. The second derivative is symmetric by
`second_derivative_symmetric_of_eventually`; no continuity of the second derivative is needed.

## Main declarations

* `TauCeti.sum_star_orthonormalBasisOneIJK_mul_fueterLeft`,
  `TauCeti.sum_fueterRight_mul_star_orthonormalBasisOneIJK`: the conjugate operators compose with
  the Fueter operators to the trace of a symmetric bilinear map.
* `TauCeti.LeftFueterOn.laplacian_eq_zero`, `TauCeti.RightFueterOn.laplacian_eq_zero`: a function
  that is Fueter regular on a neighbourhood of `q`, with derivative differentiable at `q`, has
  vanishing Laplacian at `q`.
* `TauCeti.LeftFueterOn.laplacian_eq_zero_of_contDiffOn` and its right counterpart: a Fueter
  regular function of class `C²` on an open set is harmonic there.

## References

* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, equation (17) and the remark after Theorem 9.
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

/-- If a linear map `L` on a finite-dimensional space vanishes on `g` near `x`, and `g` is
differentiable at `x`, then `L` vanishes on every directional derivative of `g` at `x`. Applied
with `g = fderiv ℝ f` and `L` a Fueter operator. -/
private theorem linearMap_fderiv_eq_zero {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : E → F} {x : E} (L : F →ₗ[ℝ] G) (hL : ∀ᶠ y in 𝓝 x, L (g y) = 0)
    (h : DifferentiableAt ℝ g x) (w : E) : L (fderiv ℝ g x w) = 0 := by
  have hc := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp x h.hasFDerivAt
  simpa using congrArg (· w) (hc.unique ((hasFDerivAt_const 0 x).congr_of_eventuallyEq hL))

/-- A function that is left Fueter regular on a neighbourhood of `q`, and whose derivative is
differentiable at `q`, has vanishing Laplacian at `q`. -/
theorem LeftFueterOn.laplacian_eq_zero (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q)
    (h : DifferentiableAt ℝ (fderiv ℝ f) q) : Δ f q = 0 := by
  have hev : ∀ᶠ x in 𝓝 q, LeftFueterAt f x := eventually_of_mem hs (leftFueterOn_iff.1 hf)
  have hB := second_derivative_symmetric_of_eventually
    (hev.mono fun _ hx ↦ hx.differentiableAt.hasFDerivAt) h.hasFDerivAt
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f orthonormalBasisOneIJK]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sum_star_orthonormalBasisOneIJK_mul_fueterLeft hB]
  simp [linearMap_fderiv_eq_zero (g := fderiv ℝ f) fueterLeft
    (hev.mono fun _ hx ↦ hx.fueterLeft_fderiv) h]

/-- A function that is right Fueter regular on a neighbourhood of `q`, and whose derivative is
differentiable at `q`, has vanishing Laplacian at `q`. -/
theorem RightFueterOn.laplacian_eq_zero (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q)
    (h : DifferentiableAt ℝ (fderiv ℝ f) q) : Δ f q = 0 := by
  have hev : ∀ᶠ x in 𝓝 q, RightFueterAt f x := eventually_of_mem hs (rightFueterOn_iff.1 hf)
  have hB := second_derivative_symmetric_of_eventually
    (hev.mono fun _ hx ↦ hx.differentiableAt.hasFDerivAt) h.hasFDerivAt
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f orthonormalBasisOneIJK]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sum_fueterRight_mul_star_orthonormalBasisOneIJK hB]
  simp [linearMap_fderiv_eq_zero (g := fderiv ℝ f) fueterRight
    (hev.mono fun _ hx ↦ hx.fueterRight_fderiv) h]

/-- A left Fueter regular function of class `C²` on an open set is harmonic there. -/
theorem LeftFueterOn.laplacian_eq_zero_of_contDiffOn (hf : LeftFueterOn f s) (hs : IsOpen s)
    (h₂ : ContDiffOn ℝ 2 f s) (hq : q ∈ s) : Δ f q = 0 :=
  hf.laplacian_eq_zero (hs.mem_nhds hq)
    (((h₂.contDiffAt (hs.mem_nhds hq)).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)

/-- A right Fueter regular function of class `C²` on an open set is harmonic there. -/
theorem RightFueterOn.laplacian_eq_zero_of_contDiffOn (hf : RightFueterOn f s) (hs : IsOpen s)
    (h₂ : ContDiffOn ℝ 2 f s) (hq : q ∈ s) : Δ f q = 0 :=
  hf.laplacian_eq_zero (hs.mem_nhds hq)
    (((h₂.contDiffAt (hs.mem_nhds hq)).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)

end TauCeti
