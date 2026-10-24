/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Translation
import Mathlib.Analysis.Normed.Group.Tannery
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.SpecialFunctions.Gaussian.Bounds

/-!
# Theta series at the cusp `∞`

Let `L` be a discrete subgroup of a finite-dimensional real normed space `E`. This file studies
the theta series `Θ_L(τ) = ∑_{v ∈ L} exp (π i ‖v‖² τ)` and the theta series
`θ_{γ+L}(τ) = ∑_{v ∈ L} exp (π i ‖γ + v‖² τ)` of a translate as `im τ → ∞`, and on the imaginary
axis.

The term of index `v` has norm `exp (-π ‖γ + v‖² im τ)`. On a half-plane `{τ | y ≤ im τ}`,
`0 < y`, the terms are therefore dominated by the summable Gaussian `exp (-π y ‖γ + v‖²)`, so the
series are bounded at `i∞`; and as `im τ → ∞` every term tends to `0`, except the term of the
vector `v = -γ`, which is constantly `1` and exists only when `γ ∈ L`. By dominated convergence,
`Θ_L(τ) → 1`, while `θ_{γ+L}(τ) → 0` for `γ ∉ L`. Together with holomorphy and periodicity this
identifies the constant term of the `q`-expansion of `Θ_L`: it is `1`, in `q = exp (2 π i τ)` for
an even lattice and in `exp (π i τ)` for an integral one.

On the imaginary axis `τ = i y` every term is the positive real number `exp (-π y ‖γ + v‖²)`, so
`θ_{γ+L}(i y)` is a positive real number and `Θ_L(i y) ≥ 1`. In particular `Θ_L` does not vanish
there; this is the nonvanishing used to show that the rank of an even unimodular lattice is
divisible by `8`.

## Main statements

* `ZLattice.isBoundedAtImInfty_thetaCoset`, `ZLattice.isBoundedAtImInfty_thetaSeries`: the theta
  series are bounded at `i∞`.
* `ZLattice.tendsto_thetaSeries_atImInfty`, `ZLattice.valueAtInfty_thetaSeries`: `Θ_L(τ) → 1` as
  `im τ → ∞`.
* `ZLattice.isZeroAtImInfty_thetaCoset`: `θ_{γ+L}(τ) → 0` as `im τ → ∞` when `γ ∉ L`.
* `ZLattice.IsEven.qExpansion_thetaSeries_coeff_zero`: for even `L` the constant term of the
  `q`-expansion of `Θ_L` is `1`; `ZLattice.IsIntegral.qExpansion_two_thetaSeries_coeff_zero` is
  the same statement in `exp (π i τ)` for integral `L`.
* `ZLattice.thetaCoset_eq_ofReal_of_re_eq_zero`, `ZLattice.re_thetaCoset_pos`,
  `ZLattice.one_le_re_thetaSeries`: on the imaginary axis `θ_{γ+L}` is real and positive, and
  `Θ_L ≥ 1`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Filter Topology
open UpperHalfPlane (atImInfty IsBoundedAtImInfty IsZeroAtImInfty valueAtInfty qExpansion
  ofComplex)
open scoped Real UpperHalfPlane

namespace ZLattice

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]

/-- On the half-plane `{τ | y ≤ im τ}`, `0 < y`, the theta series of `γ + L` is bounded in norm
by `∑_{v ∈ L} exp (-π y ‖γ + v‖²)`, its value at `i y`. -/
theorem norm_thetaCoset_le (γ : E) {y : ℝ} (hy : 0 < y) {τ : ℍ} (hτ : y ≤ τ.im) :
    ‖thetaCoset L γ τ‖ ≤ ∑' v : L, Real.exp (-(π * y) * ‖γ + (v : E)‖ ^ 2) := by
  rw [thetaCoset_apply]
  exact tsum_of_norm_bounded (summable_exp_neg_mul_norm_add_sq L (by positivity) γ).hasSum
    fun _ => norm_exp_pi_mul_I_mul_ofReal_mul_le (by positivity) hτ

/-- The theta series of a translate of a discrete subgroup is bounded at `i∞`. -/
theorem isBoundedAtImInfty_thetaCoset (γ : E) : IsBoundedAtImInfty (thetaCoset L γ) :=
  UpperHalfPlane.isBoundedAtImInfty_iff.mpr
    ⟨_, 1, fun _ hτ => norm_thetaCoset_le L γ one_pos hτ⟩

/-- The theta series of a discrete subgroup is bounded at `i∞`. -/
theorem isBoundedAtImInfty_thetaSeries : IsBoundedAtImInfty (thetaSeries L) := by
  simpa using isBoundedAtImInfty_thetaCoset L 0

open Classical in
/-- The theta series of `γ + L` tends at `i∞` to the number of vectors `v ∈ L` with `γ + v = 0`,
by dominated convergence: the term of such a `v` is constantly `1`, and every other term tends
to `0`. -/
private theorem tendsto_thetaCoset_atImInfty_tsum_ite (γ : E) :
    Tendsto (thetaCoset L γ) atImInfty (𝓝 (∑' v : L, if γ + (v : E) = 0 then 1 else 0)) := by
  refine (tendsto_tsum_of_dominated_convergence
    (summable_exp_neg_mul_norm_add_sq L (c := π * 1) (by positivity) γ) (fun v => ?_) ?_).congr
    fun τ => (thetaCoset_apply L γ τ).symm
  · split_ifs with hv
    · simp [hv]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_exp_pi_mul_I_mul_ofReal_mul, UpperHalfPlane.coe_im]
    exact Real.tendsto_exp_atBot.comp <|
      (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop).const_mul_atTop_of_neg
        (neg_lt_zero.mpr (mul_pos Real.pi_pos (pow_pos (norm_pos_iff.mpr hv) 2)))
  · filter_upwards [(UpperHalfPlane.atImInfty_mem {τ : ℍ | 1 ≤ τ.im}).mpr ⟨1, fun _ h => h⟩]
      with τ hτ v
    exact norm_exp_pi_mul_I_mul_ofReal_mul_le (by positivity) hτ

/-- The theta series of a discrete subgroup tends to `1` at `i∞`: every term except the term
`exp 0 = 1` of the zero vector tends to `0`. -/
theorem tendsto_thetaSeries_atImInfty : Tendsto (thetaSeries L) atImInfty (𝓝 1) := by
  classical
  convert tendsto_thetaCoset_atImInfty_tsum_ite L 0 using 2
  · simp
  · rw [← tsum_ite_eq (0 : L) fun _ => (1 : ℂ)]
    exact tsum_congr fun v => by split_ifs <;> simp_all

/-- The value of the theta series of a discrete subgroup at the cusp `∞` is `1`. -/
@[simp]
theorem valueAtInfty_thetaSeries : valueAtInfty (thetaSeries L) = 1 :=
  (tendsto_thetaSeries_atImInfty L).limUnder_eq

/-- For `γ ∉ L` the theta series of the translate `γ + L` tends to `0` at `i∞`, since no vector
of `γ + L` is zero. -/
theorem isZeroAtImInfty_thetaCoset {γ : E} (hγ : γ ∉ L) : IsZeroAtImInfty (thetaCoset L γ) := by
  have h (v : L) : γ + (v : E) ≠ 0 := fun h0 => hγ <| by
    rw [eq_neg_of_add_eq_zero_left h0]
    exact neg_mem v.2
  simpa [h, UpperHalfPlane.IsZeroAtImInfty, ZeroAtFilter] using
    tendsto_thetaCoset_atImInfty_tsum_ite L γ

/-- For `γ ∉ L` the value of the theta series of `γ + L` at the cusp `∞` is `0`. -/
theorem valueAtInfty_thetaCoset {γ : E} (hγ : γ ∉ L) : valueAtInfty (thetaCoset L γ) = 0 :=
  (isZeroAtImInfty_thetaCoset L hγ).valueAtInfty_eq_zero

/-- The constant term of the `q`-expansion with period `h` of the theta series of a discrete
subgroup is `1`, whenever the theta series has period `h`. -/
theorem qExpansion_thetaSeries_coeff_zero {h : ℝ} (hh : 0 < h)
    (hper : ∀ τ : ℍ, thetaSeries L (h +ᵥ τ) = thetaSeries L τ) :
    (qExpansion h (thetaSeries L)).coeff 0 = 1 := by
  have hper' := UpperHalfPlane.periodic_comp_ofComplex hper
  rw [UpperHalfPlane.qExpansion_coeff_zero hh (UpperHalfPlane.analyticAt_cuspFunction_zero hh hper'
    (mdifferentiable_thetaSeries L) (isBoundedAtImInfty_thetaSeries L)) hper',
    valueAtInfty_thetaSeries]

variable {L} in
/-- For an even lattice, the constant term of the `q`-expansion of `Θ_L` in
`q = exp (2 π i τ)` is `1`. -/
theorem IsEven.qExpansion_thetaSeries_coeff_zero (hL : IsEven L) :
    (qExpansion 1 (thetaSeries L)).coeff 0 = 1 :=
  ZLattice.qExpansion_thetaSeries_coeff_zero L one_pos hL.thetaSeries_one_vadd

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L]

/-- For an integral lattice, the constant term of the `q`-expansion of `Θ_L` with period `2`, in
`exp (π i τ)`, is `1`. -/
theorem IsIntegral.qExpansion_two_thetaSeries_coeff_zero (hL : IsIntegral L) :
    (qExpansion 2 (thetaSeries L)).coeff 0 = 1 :=
  ZLattice.qExpansion_thetaSeries_coeff_zero L two_pos hL.thetaSeries_two_vadd

end InnerProduct

section ImaginaryAxis

variable {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)

/-- On the imaginary axis the theta series of `γ + L` is real:
`θ_{γ+L}(i y) = ∑_{v ∈ L} exp (-π y ‖γ + v‖²)`. -/
theorem thetaCoset_eq_ofReal_of_re_eq_zero (γ : E) {τ : ℍ} (hτ : τ.re = 0) :
    thetaCoset L γ τ = ((∑' v : L, Real.exp (-(π * τ.im) * ‖γ + (v : E)‖ ^ 2) : ℝ) : ℂ) := by
  have hτ' : (τ : ℂ) = τ.im * I := Complex.ext (by simp [hτ]) (by simp)
  rw [thetaCoset_apply, ofReal_tsum]
  refine tsum_congr fun v => ?_
  rw [hτ', ofReal_exp]
  congr 1
  push_cast
  linear_combination (π * ‖γ + (v : E)‖ ^ 2 * τ.im : ℂ) * I_sq

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L]

/-- On the imaginary axis the theta series of `γ + L` has positive real part (and is real, by
`ZLattice.thetaCoset_eq_ofReal_of_re_eq_zero`). -/
theorem re_thetaCoset_pos (γ : E) {τ : ℍ} (hτ : τ.re = 0) : 0 < (thetaCoset L γ τ).re := by
  rw [thetaCoset_eq_ofReal_of_re_eq_zero L γ hτ, ofReal_re]
  exact (summable_exp_neg_mul_norm_add_sq L (by positivity) γ).tsum_pos
    (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- On the imaginary axis the theta series of a discrete subgroup has real part at least `1`, the
contribution of the zero vector (and is real, by `ZLattice.thetaCoset_eq_ofReal_of_re_eq_zero`). -/
theorem one_le_re_thetaSeries {τ : ℍ} (hτ : τ.re = 0) : 1 ≤ (thetaSeries L τ).re := by
  rw [← thetaCoset_zero, thetaCoset_eq_ofReal_of_re_eq_zero L 0 hτ, ofReal_re]
  simpa using (summable_exp_neg_mul_norm_add_sq L (c := π * τ.im) (by positivity) 0).le_tsum 0
    fun _ _ => (Real.exp_pos _).le

/-- The theta series of a discrete subgroup does not vanish on the imaginary axis. -/
theorem thetaSeries_ne_zero_of_re_eq_zero {τ : ℍ} (hτ : τ.re = 0) : thetaSeries L τ ≠ 0 :=
  fun h => (one_le_re_thetaSeries L hτ).not_gt (by rw [h, zero_re]; exact one_pos)

end ImaginaryAxis

end ZLattice
