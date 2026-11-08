/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Gaussian
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MulVolume
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.TraceDual

/-!
# The theta inversion with one parameter per infinite place

For a parameter `y` with one positive coordinate per infinite place, the archimedean Gaussian
`archGaussian y x = exp (-π ∑ w, y w * |x w|²)` has Fourier transform

`mixedFourier K (archGaussian y) = N(y)^(-1/2) • archGaussian y⁻¹`,

where `N(y) = archNorm y = ∏ w, y w ^ mult w` (`mixedFourier_archGaussian`). At `y = 1` this is the
self-duality of `exp (-π ‖x‖²)` in Mathlib's Euclidean model of the mixed space
(`mixedFourier_archGaussian_one`); the general case follows from the coordinatewise substitution
`x ↦ √y * x`, whose Jacobian is `N(y)^(1/2)` because a complex coordinate is two real ones.

Poisson summation over a full lattice `L` of the mixed space then gives the transformation law of
its theta series (`latticeTheta_inv`),

`θ_L(y) = covol(L)⁻¹ N(y)^(-1/2) θ_{L^∨}(y⁻¹)`,

against the Euclidean dual `L^∨ = mixedDual K L`. This is Neukirch's (3.6) on the imaginary axis,
with one parameter per infinite place. It holds for every full lattice, not only for ideal
lattices, because the transformation law of the Mellin kernel of a partial zeta function is
stated for lattices whose dual is identified with an ideal lattice only afterwards.

That identification moves a lattice by `traceToEuclidean K`, which multiplies the absolute value
at `w` by `mult w`; on the theta series this multiplies the parameter by `(mult w ^ 2)_w`
(`latticeTheta_map_traceToEuclidean`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §3 and §5.
-/

public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped Real FourierTransform

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **Self-duality of the Gaussian at the constant parameter `1`**: `exp (-π ‖x‖²)` is its own
Fourier transform for the Euclidean pairing `mixedInner` and the measure `volume`. -/
@[simp]
theorem mixedFourier_archGaussian_one (ξ : mixedSpace K) :
    mixedFourier K (archGaussian 1) ξ = archGaussian 1 ξ := by
  have h (x : euclidean.mixedSpace K) :
      archGaussian 1 (euclidean.toMixed K x) = cexp (-π * ‖x‖ ^ 2) := by
    rw [archGaussian_one, mixedInner_toMixed, real_inner_self_eq_norm_sq]
    push_cast
    ring_nf
  obtain ⟨η, rfl⟩ := (euclidean.toMixed K).surjective ξ
  rw [mixedFourier_toMixed, h]
  simp_rw [h]
  rw [fourier_gaussian_innerProductSpace (by simpa using Real.pi_pos),
    div_self (by exact_mod_cast Real.pi_ne_zero), one_cpow, one_mul]
  congr 1
  field_simp

/-- **The Fourier transform of the archimedean Gaussian**,
`𝓕 (archGaussian y) = N(y)^(-1/2) • archGaussian y⁻¹`, with `N(y) = archNorm y`. In
`archNorm y = ∏ w, y w ^ mult w` a complex place counts twice, as a complex coordinate is two real
ones, even though the Gaussian itself counts a complex coordinate once. -/
theorem mixedFourier_archGaussian (y : realSpace K) (hy : ∀ w, 0 < y w) (ξ : mixedSpace K) :
    mixedFourier K (archGaussian y) ξ =
      (((√(archNorm y))⁻¹ : ℝ) : ℂ) * archGaussian y⁻¹ ξ := by
  classical
  have hy' : ∀ w, 0 < y⁻¹ w := fun w ↦ inv_pos.mpr (hy w)
  set c : mixedSpace K := mixedSpaceOfRealSpace fun w ↦ √(y w)
  set c' : mixedSpace K := mixedSpaceOfRealSpace fun w ↦ √(y⁻¹ w)
  have hcc' : c * c' = 1 := by
    ext w <;> simp [c, c', mixedSpaceOfRealSpace_apply, (Real.sqrt_pos.mpr (hy _)).ne']
  have hc : mixedEmbedding.norm c = √(archNorm y) :=
    norm_mixedSpaceOfRealSpace_sqrt fun w ↦ (hy w).le
  have hc0 : mixedEmbedding.norm c ≠ 0 := by
    rw [hc]
    exact (Real.sqrt_pos.mpr (archNorm_pos hy)).ne'
  -- Substitute `x ↦ c * x`: the pairing becomes `mixedInner (c * x) (c' * ξ)` since `c * c' = 1`,
  -- and the Gaussian becomes the Gaussian at the parameter `1`.
  have hint (x : mixedSpace K) : 𝐞 (-mixedInner K x ξ) • archGaussian y x =
      𝐞 (-mixedInner K (c * x) (c' * ξ)) • archGaussian 1 (c * x) := by
    rw [mixedInner_mixedSpaceOfRealSpace_mul, ← mul_assoc, hcc', one_mul,
      ← archGaussian_one_archGaussianDilation y hy, archGaussianDilation_apply]
  rw [mixedFourier_apply]
  simp_rw [hint]
  rw [integral_comp_mul_left (fun z ↦ 𝐞 (-mixedInner K z (c' * ξ)) • archGaussian 1 z) hc0,
    ← mixedFourier_apply, mixedFourier_archGaussian_one, ← archGaussianDilation_apply y⁻¹ hy',
    archGaussian_one_archGaussianDilation, hc, Complex.real_smul]

open scoped Classical in
/-- **The theta transformation with one parameter per infinite place**, Neukirch VII (3.6) on the
imaginary axis: for every full lattice `L` of the mixed space and every positive parameter `y`,
`θ_L(y) = covol(L)⁻¹ N(y)^(-1/2) θ_{L^∨}(y⁻¹)`, the dual being the Euclidean dual `mixedDual`. -/
theorem latticeTheta_inv (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    (y : realSpace K) (hy : ∀ w, 0 < y w) :
    latticeTheta L y = (ZLattice.covolume L : ℂ)⁻¹ * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
      latticeTheta (mixedDual K L) y⁻¹ := by
  have hF : mixedFourier K (archGaussianSchwartz y hy) = mixedFourier K (archGaussian y) :=
    congrArg _ (funext (archGaussianSchwartz_apply y hy))
  have h := tsum_eq_tsum_mixedDual_mixedFourier K L (archGaussianSchwartz y hy) 0
  simp only [zero_add, archGaussianSchwartz_apply, hF, mixedFourier_archGaussian y hy,
    ← mixedInnerBilin_apply, map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one] at h
  rw [latticeTheta_def, h, tsum_mul_left, mul_assoc, latticeTheta_def]

/-- `traceToEuclidean K` on the lattice variable multiplies the parameter of the archimedean
Gaussian by `(mult w ^ 2)_w`. -/
theorem latticeTheta_map_traceToEuclidean (L : Submodule ℤ (mixedSpace K))
    (y : realSpace K) :
    latticeTheta (L.map ((traceToEuclidean K).toLinearMap.restrictScalars ℤ)) y =
      latticeTheta L ((fun w ↦ (mult w : ℝ) ^ 2) * y) := by
  let e := Submodule.equivMapOfInjective ((traceToEuclidean K).toLinearMap.restrictScalars ℤ)
    (traceToEuclidean K).injective L
  rw [latticeTheta_def, latticeTheta_def, ← e.toEquiv.tsum_eq]
  refine tsum_congr fun x ↦ ?_
  have he : (e x : mixedSpace K) = traceToEuclidean K x :=
    Submodule.coe_equivMapOfInjective_apply _ _ _ x
  rw [LinearEquiv.coe_toEquiv, he]
  simp only [archGaussian_apply, normAtPlace_traceToEuclidean, Pi.mul_apply]
  congr 4 with w
  ring

end TauCeti.LFunctions
