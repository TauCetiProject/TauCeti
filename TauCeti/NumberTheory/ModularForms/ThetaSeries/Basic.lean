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

The series `θ_{γ+L}` depends only on the class of `γ` modulo `L`, and `θ_{-γ+L} = θ_{γ+L}`. For a
subgroup `M ≤ L`, splitting `L` into the classes of `L` modulo `M` writes `Θ_L` as the sum of the
series `θ_{y+M}` over those classes.

## Main definitions

* `ZLattice.thetaSeries L`: the theta series `Θ_L : ℍ → ℂ`.
* `ZLattice.thetaCoset L γ`: the theta series `θ_{γ+L} : ℍ → ℂ` of the translate `γ + L`.

## Main statements

* `Complex.norm_exp_pi_mul_I_mul_ofReal_mul`: `‖exp (π i t z)‖ = exp (-π t im z)` for real `t`,
  so the term of index `v` has norm `exp (-π ‖γ + v‖² im τ)`.
* `ZLattice.thetaCoset_eq_of_sub_mem`, `ZLattice.thetaCoset_neg`: `θ_{γ+L}` depends only on
  `γ` modulo `L`, and `θ_{-γ+L} = θ_{γ+L}`.
* `ZLattice.summable_thetaCoset`: the series converge at every `τ : ℍ`.
* `ZLattice.hasSum_thetaCoset_out`: for `M ≤ L`, `Θ_L` is the sum of the `θ_{y+M}` over the classes
  `y` of `L` modulo `M`.
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

/-- Translating `γ` by a vector of `L` does not change the theta series of the translate `γ + L`:
the series is reindexed by `v ↦ w + v`. -/
theorem thetaCoset_add_mem (γ : E) {w : E} (hw : w ∈ L) :
    thetaCoset L (γ + w) = thetaCoset L γ := by
  ext τ
  simp only [thetaCoset_apply, add_assoc]
  exact (Equiv.addLeft (⟨w, hw⟩ : L)).tsum_eq
    fun v : L => cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ)

/-- The theta series of the translate `γ + L` depends only on the class of `γ` modulo `L`. -/
theorem thetaCoset_eq_of_sub_mem {γ δ : E} (h : γ - δ ∈ L) : thetaCoset L γ = thetaCoset L δ := by
  rw [← thetaCoset_add_mem L δ h, add_sub_cancel]

/-- For `γ ∈ L` the translate `γ + L` is `L` itself, with the same theta series. -/
theorem thetaCoset_of_mem {γ : E} (hγ : γ ∈ L) : thetaCoset L γ = thetaSeries L := by
  rw [← thetaCoset_zero, thetaCoset_eq_of_sub_mem L (δ := 0) (by simpa using hγ)]

/-- The theta series of the translates `-γ + L` and `γ + L` agree: the series is reindexed by
`v ↦ -v`. -/
@[simp]
theorem thetaCoset_neg (γ : E) : thetaCoset L (-γ) = thetaCoset L γ := by
  ext τ
  rw [thetaCoset_apply, thetaCoset_apply,
    ← (Equiv.neg L).tsum_eq fun v : L => cexp (π * I * (‖-γ + (v : E)‖ ^ 2 : ℝ) * τ)]
  refine tsum_congr fun v => ?_
  rw [Equiv.neg_apply, Submodule.coe_neg, ← neg_add, norm_neg]

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

/-- **Splitting a theta series into cosets.** For `M ≤ L`, the theta series of `L` is the sum of
the theta series of the translates `y + M` over the classes `y` of `L` modulo `M`, each class
represented by `Quotient.out` (by `thetaCoset_eq_of_sub_mem` the representative does not matter).
The sum is finite when `M` has finite index in `L`. -/
theorem hasSum_thetaCoset_out {M : Submodule ℤ E} (hML : M ≤ L) (τ : ℍ) :
    HasSum (fun y : L ⧸ M.submoduleOf L => thetaCoset M ((Quotient.out y : L) : E) τ)
      (thetaSeries L τ) := by
  -- The vectors of `L` in the class `y` are the translates `out y + v`, `v ∈ M`: the fibre of
  -- the quotient map over `y` is identified with its kernel `M.submoduleOf L`, and then with `M`.
  have hfiber (y : L ⧸ M.submoduleOf L) :
      ∑' b : (Submodule.Quotient.mk ⁻¹' {y} : Set L), cexp (π * I * (‖((b : L) : E)‖ ^ 2 : ℝ) * τ) =
        thetaCoset M (Quotient.out y : L) τ := by
    let f := (M.submoduleOf L).mkQ.toAddMonoidHom
    have hker (x : L) : x ∈ M.submoduleOf L ↔ x ∈ f.ker := by simp [f]
    have hset : f ⁻¹' {f (Quotient.out y)} = Submodule.Quotient.mk ⁻¹' {y} := by ext; simp [f]
    let e : M ≃ (Submodule.Quotient.mk ⁻¹' {y} : Set L) :=
      ((Submodule.submoduleOfEquivOfLe hML).toEquiv.symm.trans (Equiv.subtypeEquivRight hker)).trans
        ((f.fiberEquivKer (Quotient.out y)).symm.trans (Set.equivOfEq hset))
    -- `e v = out y + v`, by `AddMonoidHom.fiberEquivKer_symm_apply` and the definition of the
    -- inverse of `Submodule.submoduleOfEquivOfLe`.
    have he (v : M) : ((e v : L) : E) = ((Quotient.out y : L) : E) + v := by
      have hv : (((Submodule.submoduleOfEquivOfLe hML).symm v : L) : E) = v := rfl
      simp [e, AddMonoidHom.fiberEquivKer_symm_apply, hv]
    rw [thetaCoset_apply, ← e.tsum_eq]
    exact tsum_congr fun v => by rw [he]
  rw [← funext hfiber, thetaSeries_apply]
  exact (summable_thetaSeries L τ).hasSum.tsum_fiberwise _

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
