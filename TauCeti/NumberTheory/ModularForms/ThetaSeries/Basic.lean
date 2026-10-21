/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Algebra.Module.ZLattice.Summable

/-!
# The theta series of a lattice

For a `ℤ`-submodule `L` of a real normed space `E` and `τ` in the upper half-plane `ℍ`, the
*theta series* of `L` is

`Θ_L(τ) = ∑_{v ∈ L} exp (π i ‖v‖² τ)`,

and for `γ : E` the theta series of the translate `γ + L` is

`θ_{γ+L}(τ) = ∑_{v ∈ L} exp (π i ‖γ + v‖² τ)`.

In the applications `E` is a real inner product space, so that `‖v‖²` is the positive definite
quadratic form of the inner product; the definitions and the results here use only the norm.
The exponent is `π i ‖v‖² τ` rather than `2 π i ‖v‖² τ`: for an even lattice the `q`-expansion
in `q = exp (2 π i τ)` is then indexed by the half-norms `‖v‖² / 2`. In rank one, for `L = ℤ ⊆ ℝ`,
`Θ_L` is the Jacobi theta function `jacobiTheta`. When `γ` lies in the dual lattice, `θ_{γ+L}` is
the coset theta series of the coset `γ + L`.

This file defines both series and proves that they converge and are holomorphic, for a discrete
subgroup `L` (of any rank, not necessarily full) of a finite-dimensional real normed space. The
term of index `v` has norm `exp (-π ‖γ + v‖² im τ)`, so on every half-plane `{τ | y ≤ im τ}`,
`0 < y`, the terms are dominated by the summable Gaussian `exp (-π y ‖γ + v‖²)` of
`ZLattice.summable_exp_neg_mul_norm_add_sq`. Hence the series converge uniformly on these
half-planes and locally uniformly on `ℍ`, and are holomorphic, both as functions of `z : ℂ` on
`{z | 0 < im z}` and in the manifold sense on `ℍ`, which is what a bundled modular form requires.

## Main definitions

* `ZLattice.thetaSeries L`: the theta series `Θ_L : ℍ → ℂ`.
* `ZLattice.thetaCoset L γ`: the theta series `θ_{γ+L} : ℍ → ℂ` of the translate `γ + L`.

## Main statements

* `Complex.norm_exp_pi_mul_I_mul_ofReal_mul`: `‖exp (π i t z)‖ = exp (-π t im z)` for real `t`,
  so the term of index `v` has norm `exp (-π ‖γ + v‖² im τ)`.
* `ZLattice.summable_thetaCoset`: the series converge at every `τ : ℍ`.
* `ZLattice.hasSumUniformlyOn_thetaCoset`: uniform convergence on `{τ | y ≤ im τ}` for `0 < y`.
* `ZLattice.hasSumLocallyUniformly_thetaCoset`: locally uniform convergence on `ℍ`.
* `ZLattice.differentiableOn_thetaCoset`, `ZLattice.mdifferentiable_thetaCoset`: holomorphy.

Each statement about `thetaCoset` has a `thetaSeries` counterpart, obtained from
`ZLattice.thetaCoset_zero : thetaCoset L 0 = thetaSeries L`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Filter Topology
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos mdifferentiable_iff)
open scoped Real Manifold UpperHalfPlane

namespace Complex

/-- For real `t`, `‖exp (π i t z)‖ = exp (-π t im z)`; with `t = ‖γ + v‖²` this is the norm of
the term of index `v` of a theta series. -/
theorem norm_exp_pi_mul_I_mul_ofReal_mul (t : ℝ) (z : ℂ) :
    ‖cexp (π * I * t * z)‖ = Real.exp (-(π * t) * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

/-- For `0 ≤ t`, on the half-plane `{z | y ≤ im z}` the function `exp (π i t z)` is bounded in
norm by `exp (-π y t)`; this dominates the terms of a theta series by a Gaussian. -/
theorem norm_exp_pi_mul_I_mul_ofReal_mul_le {t y : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : y ≤ z.im) :
    ‖cexp (π * I * t * z)‖ ≤ Real.exp (-(π * y) * t) := by
  rw [norm_exp_pi_mul_I_mul_ofReal_mul, Real.exp_le_exp]
  have : 0 ≤ π * t := by positivity
  nlinarith

end Complex

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E]

/-- The theta series `Θ_L(τ) = ∑_{v ∈ L} exp (π i ‖v‖² τ)` of `L : Submodule ℤ E`. It converges
on `ℍ` when `L` is discrete and `E` is finite-dimensional (`ZLattice.summable_thetaSeries`). -/
noncomputable def thetaSeries (L : Submodule ℤ E) (τ : ℍ) : ℂ :=
  ∑' v : L, cexp (π * I * (‖(v : E)‖ ^ 2 : ℝ) * τ)

/-- The theta series `θ_{γ+L}(τ) = ∑_{v ∈ L} exp (π i ‖γ + v‖² τ)` of the translate `γ + L` of
`L : Submodule ℤ E`. For `γ` in the dual lattice this is the coset theta series of the coset
`γ + L`. -/
noncomputable def thetaCoset (L : Submodule ℤ E) (γ : E) (τ : ℍ) : ℂ :=
  ∑' v : L, cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ)

variable (L : Submodule ℤ E)

theorem thetaSeries_apply (τ : ℍ) :
    thetaSeries L τ = ∑' v : L, cexp (π * I * (‖(v : E)‖ ^ 2 : ℝ) * τ) :=
  (rfl)

theorem thetaCoset_apply (γ : E) (τ : ℍ) :
    thetaCoset L γ τ = ∑' v : L, cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ) :=
  (rfl)

/-- The theta series of the translate `0 + L` is the theta series of `L`. -/
@[simp]
theorem thetaCoset_zero : thetaCoset L 0 = thetaSeries L := by
  ext τ
  simp [thetaCoset_apply, thetaSeries_apply]

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L]

/-- The theta series of a translate of a discrete subgroup converges at every point of
the upper half-plane. -/
theorem summable_thetaCoset (γ : E) (τ : ℍ) :
    Summable fun v : L => cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ) :=
  .of_norm_bounded (summable_exp_neg_mul_norm_add_sq L (c := π * τ.im) (by positivity) γ)
    fun v => norm_exp_pi_mul_I_mul_ofReal_mul_le (by positivity) le_rfl

/-- The theta series of a discrete subgroup converges at every point of the upper
half-plane. -/
theorem summable_thetaSeries (τ : ℍ) :
    Summable fun v : L => cexp (π * I * (‖(v : E)‖ ^ 2 : ℝ) * τ) := by
  simpa using summable_thetaCoset L 0 τ

/-- The theta series of a translate converges uniformly on each half-plane `{τ | y ≤ im τ}` with
`0 < y`. -/
theorem hasSumUniformlyOn_thetaCoset (γ : E) {y : ℝ} (hy : 0 < y) :
    HasSumUniformlyOn (fun (v : L) (τ : ℍ) => cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ))
      (thetaCoset L γ) {τ : ℍ | y ≤ τ.im} :=
  HasSumUniformlyOn.of_norm_le_summable
    (summable_exp_neg_mul_norm_add_sq L (c := π * y) (by positivity) γ)
    fun v _ hτ => norm_exp_pi_mul_I_mul_ofReal_mul_le (by positivity) hτ

/-- The theta series converges uniformly on each half-plane `{τ | y ≤ im τ}` with `0 < y`. -/
theorem hasSumUniformlyOn_thetaSeries {y : ℝ} (hy : 0 < y) :
    HasSumUniformlyOn (fun (v : L) (τ : ℍ) => cexp (π * I * (‖(v : E)‖ ^ 2 : ℝ) * τ))
      (thetaSeries L) {τ : ℍ | y ≤ τ.im} := by
  simpa using hasSumUniformlyOn_thetaCoset L 0 hy

/-- The theta series of a translate converges locally uniformly on the upper half-plane. -/
theorem hasSumLocallyUniformly_thetaCoset (γ : E) :
    HasSumLocallyUniformly (fun (v : L) (τ : ℍ) => cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ))
      (thetaCoset L γ) := by
  refine hasSumLocallyUniformly_of_of_forall_exists_nhds fun τ =>
    ⟨{τ' : ℍ | τ.im / 2 ≤ τ'.im}, ?_, hasSumUniformlyOn_thetaCoset L γ (by positivity)⟩
  exact mem_of_superset ((isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds
    (half_lt_self τ.im_pos)) fun _ h => le_of_lt h

/-- The theta series converges locally uniformly on the upper half-plane. -/
theorem hasSumLocallyUniformly_thetaSeries :
    HasSumLocallyUniformly (fun (v : L) (τ : ℍ) => cexp (π * I * (‖(v : E)‖ ^ 2 : ℝ) * τ))
      (thetaSeries L) := by
  simpa using hasSumLocallyUniformly_thetaCoset L 0

/-- The theta series of a translate is holomorphic on the upper half-plane, as a function of
`z : ℂ`. -/
theorem differentiableOn_thetaCoset (γ : E) :
    DifferentiableOn ℂ (thetaCoset L γ ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  intro z hz
  set U : Set ℂ := {w : ℂ | z.im / 2 < w.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by
    simp only [U, Set.mem_ofPred_eq]
    exact half_lt_self hz
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => ∑' v : L, cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * w)) U :=
    differentiableOn_tsum_of_summable_norm (summable_exp_neg_mul_norm_add_sq L (c := π * (z.im / 2))
      (mul_pos Real.pi_pos (half_pos hz)) γ)
      (fun v => ((differentiable_id.const_mul _).cexp).differentiableOn) hU
      fun v w hw => norm_exp_pi_mul_I_mul_ofReal_mul_le (by positivity) (le_of_lt hw)
  refine ((hdiff z hzU).differentiableAt (hU.mem_nhds hzU)).congr_of_eventuallyEq ?_
    |>.differentiableWithinAt
  filter_upwards [hU.mem_nhds hzU] with w hw
  have hw' : 0 < w.im := lt_trans (half_pos hz) hw
  simp [thetaCoset_apply, ofComplex_apply_of_im_pos hw']

/-- The theta series is holomorphic on the upper half-plane, as a function of `z : ℂ`. -/
theorem differentiableOn_thetaSeries :
    DifferentiableOn ℂ (thetaSeries L ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  simpa using differentiableOn_thetaCoset L 0

/-- The theta series of a translate is holomorphic on the upper half-plane `ℍ`. -/
theorem mdifferentiable_thetaCoset (γ : E) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaCoset L γ) :=
  mdifferentiable_iff.mpr (differentiableOn_thetaCoset L γ)

/-- The theta series is holomorphic on the upper half-plane `ℍ`. -/
theorem mdifferentiable_thetaSeries : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaSeries L) :=
  mdifferentiable_iff.mpr (differentiableOn_thetaSeries L)

end ZLattice
