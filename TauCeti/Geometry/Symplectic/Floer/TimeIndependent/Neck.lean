/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.Neck
public import TauCeti.Analysis.ODE.TrajectoryOperator.Tanh
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Index
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Kernel and cokernel cancellation on a neck, for Cauchy–Riemann operators on the cylinder

For a real coefficient `c : ℝ → ℝ` and a finite-dimensional complex inner product space `F`, this
file studies the real Cauchy–Riemann operator

`∂s + i ∂t - c(s) : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)`

(`TauCeti.CylinderSobolev.scalarCauchyRiemannOperator`), and realizes on it the cancellation of a
kernel against a cokernel that the linear gluing of Cauchy–Riemann operators has to account for.

* **A linearized Floer operator.** `∂s + i ∂t - c(s)` is the Sobolev realization of the linearized
  Floer operator of the Hamiltonians `H_s(y) = (c(s) / 2) ‖y‖²` for the symplectic form
  `Im ⟪·, ·⟫` and the complex structure `i`, along any map of the cylinder
  (`TauCeti.CylinderSobolev.floerSobolevOperator_div_two_mul_norm_sq`). The comparison of the
  linearized operator along a time-independent cylinder with its zero Fourier mode
  (`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Index`) therefore applies.
* **The zero mode.** When `c` is `C²` with `|c| ≤ a < 2π`, the nonzero Fourier modes have the
  uniform gap `(2π - a)² ‖x‖² ≤ ((2π)² + 1) ‖(∂s + i ∂t - c) x‖²` and contribute neither kernel
  nor cokernel. On the zero mode `(s, t) ↦ ζ(s)` the operator is `ζ ↦ ζ' - c ζ` on
  `W^{1,2}(ℝ, F)`, and the two operators have the same kernel, are onto together, are Fredholm
  together and have the same index.
* **The tanh pieces.** Hence `∂s + i ∂t + tanh s` is onto, with a kernel of real dimension
  `2 dim_ℂ F` and index `2 dim_ℂ F`, and `∂s + i ∂t - tanh s` is injective, with a cokernel of real
  dimension `2 dim_ℂ F` and index `-2 dim_ℂ F`; on the line these are the operators
  `d/ds ± tanh s` of `TauCeti.Analysis.ODE.TrajectoryOperator.Tanh`, complexified. For `F = ℂ`
  the piece spaces have real dimension `2`.
* **The glued operator.** Gluing the positive end of the first piece to the negative end of the
  second along a neck of length `2R` gives `∂s + i ∂t - a_R(s)` with
  `a_R(s) = 1 - tanh (s + R) + tanh (s - R)` (`TauCeti.neckCoeff`). It is bijective, so its index
  `0 = 2 dim_ℂ F + (-2 dim_ℂ F)` is the sum of the indices of the pieces while its kernel and
  cokernel are not the sums of theirs. Its inverse is not uniformly bounded, not even on values:
  every bound `‖x‖_{L²} ≤ C ‖(∂s + i ∂t - a_R) x‖` has `C ≥ exp (2 R) / 2`, and so does every bound
  `‖x‖ ≤ C ‖(∂s + i ∂t - a_R) x‖`. For `R ≥ 0` one has `|a_R| ≤ 1`, so the
  gap on the nonzero Fourier modes is uniform in `R` and this growth is carried by the zero mode
  alone.

## Main declarations

* `TauCeti.CylinderSobolev.scalarCauchyRiemannOperator`: the operator `∂s + i ∂t - c(s)`, with
  `TauCeti.CylinderSobolev.coeFn_scalarCauchyRiemannOperator` computing it on jets.
* `TauCeti.CylinderSobolev.ker_scalarCauchyRiemannOperator_eq_map_zeroModeL`,
  `surjective_scalarCauchyRiemannOperator_iff_surjective_trajectoryOperator`,
  `isFredholm_scalarCauchyRiemannOperator_iff_isFredholm_trajectoryOperator` and
  `index_scalarCauchyRiemannOperator_eq_index_trajectoryOperator`: the comparison with
  `d/ds - c(s)`.
* `TauCeti.CylinderSobolev.finrank_ker_scalarCauchyRiemannOperator_neg_tanh` and
  `TauCeti.CylinderSobolev.finrank_quotient_range_scalarCauchyRiemannOperator_tanh`: the piece
  kernel and the piece cokernel have real dimension `2 dim_ℂ F`.
* `TauCeti.CylinderSobolev.bijective_scalarCauchyRiemannOperator_neckCoeff` and
  `TauCeti.CylinderSobolev.index_scalarCauchyRiemannOperator_neckCoeff_eq_add`: the glued
  operator is invertible, and the index is additive.
* `exp_div_two_le_of_forall_norm_valueL_le_mul_norm_scalarCauchyRiemannOperator_neckCoeff`:
  the values of its inverse are not bounded uniformly in `R`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Chapter 10 (linear gluing of Cauchy–Riemann operators on
  cylindrical ends).
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the additivity of the index of
  trajectory operators under gluing).
* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221 (the linearized operator along a time-independent cylinder).
-/

public section

noncomputable section

open Real MeasureTheory ContinuousLinearMap TopologicalSpace
open TauCeti.StripSobolev TauCeti.SymplecticForm
open TauCeti.WeakDerivStep (prev weakFDeriv)
open scoped ENNReal

namespace TauCeti.CylinderSobolev

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-! ### The operator `∂s + i ∂t - c(s)` -/

variable (F) in
/-- **The Cauchy–Riemann operator `∂s + i ∂t - c(s)` on the cylinder.** For a real coefficient
`c : ℝ → ℝ` and a finite-dimensional complex inner product space `F`, the operator
`ξ ↦ ∂s ξ + i ∂t ξ - c(s) ξ` from `W^{1,2}(ℝ × S¹, F)` to `L²(ℝ × S¹, F)`, the first-order
operator (`TauCeti.jetOperator`) of the coefficient field `(v, v_s, v_t) ↦ v_s + i v_t - c(s) v` on
jets. It is `0` by convention when `c` is not essentially bounded. -/
def scalarCauchyRiemannOperator (c : ℝ → ℝ) : H1 F →L[ℝ] Lp F 2 stripMeasure :=
  (jetOperator 2 stripMeasure fun z ↦ firstOrderJetCoeff
    (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
      (-c z.1 • ContinuousLinearMap.id ℝ F)).comp (H1 F).subtypeL

/-- The definition of `∂s + i ∂t - c(s)`: the first-order operator of its coefficient field on
jets, restricted to `W^{1,2}(ℝ × S¹, F)`. -/
theorem scalarCauchyRiemannOperator_def (c : ℝ → ℝ) :
    scalarCauchyRiemannOperator F c = (jetOperator 2 stripMeasure fun z ↦ firstOrderJetCoeff
      (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
        (-c z.1 • ContinuousLinearMap.id ℝ F)).comp (H1 F).subtypeL :=
  (rfl)

/-- For a continuous bounded `c`, the coefficient field of `∂s + i ∂t - c(s)` is essentially
bounded on the cylinder. -/
private theorem memLp_scalarCauchyRiemannJetCoeff {c : ℝ → ℝ} (hc : Continuous c) {a : ℝ}
    (hca : ∀ s, |c s| ≤ a) :
    MemLp (fun z : ℝ × ℝ ↦ firstOrderJetCoeff
      (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
        (-c z.1 • ContinuousLinearMap.id ℝ F)) ∞ stripMeasure := by
  set Jc := (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
  have hcont : Continuous fun z : ℝ × ℝ ↦
      firstOrderJetCoeff Jc (-c z.1 • ContinuousLinearMap.id ℝ F) :=
    continuous_iff_continuousAt.2 fun _ ↦ continuousAt_firstOrderJetCoeff continuousAt_const
      ((hc.comp continuous_fst).neg.smul continuous_const).continuousAt
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ ↦
      firstOrderJetCoeff Jc (-c z.1 • ContinuousLinearMap.id ℝ F)) stripMeasure :=
    hcont.aestronglyMeasurable
  -- The codomain is given explicitly: unifying the topology of the operator space with the one of
  -- its norm would unfold the norm of `ℂ`, which the module system does not expose.
  refine memLp_top_of_bound (E := F × F × F →L[ℝ] F) hm (1 + ‖Jc‖ + a) (.of_forall fun z ↦ ?_)
  refine (norm_firstOrderJetCoeff_le _ _).trans ?_
  rw [norm_smul, norm_neg, Real.norm_eq_abs]
  gcongr
  exact (mul_le_of_le_one_right (abs_nonneg _) norm_id_le).trans (hca z.1)

/-- **The operator `∂s + i ∂t - c(s)` on jets.** For a continuous bounded `c`, the operator
`TauCeti.CylinderSobolev.scalarCauchyRiemannOperator` sends an element `x` of
`W^{1,2}(ℝ × S¹, F)` with `L²` jet `(ξ, ξ_s, ξ_t)` to `ξ_s + i ξ_t - c(s) ξ`. -/
theorem coeFn_scalarCauchyRiemannOperator {c : ℝ → ℝ} (hc : Continuous c) {a : ℝ}
    (hca : ∀ s, |c s| ≤ a) (x : H1 F) :
    scalarCauchyRiemannOperator F c x =ᵐ[stripMeasure] fun z ↦
      ((x : Lp (F × F × F) 2 stripMeasure) z).2.1 +
        Complex.I • ((x : Lp (F × F × F) 2 stripMeasure) z).2.2 -
          c z.1 • ((x : Lp (F × F × F) 2 stripMeasure) z).1 := by
  filter_upwards [coeFn_jetOperator (p := 2) (memLp_scalarCauchyRiemannJetCoeff hc hca)
    (x : Lp (F × F × F) 2 stripMeasure)] with z hz
  rw [scalarCauchyRiemannOperator_def, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    hz, firstOrderJetCoeff_apply]
  simp [AlmostComplexStructure.ofComplexModule_apply, sub_eq_add_neg]

omit [FiniteDimensional ℂ F] in
/-- The metric `Im ⟪·, i ·⟫` of the symplectic form `Im ⟪·, ·⟫` and the complex structure `i` is the
real inner product `Re ⟪·, ·⟫`. -/
private theorem imInnerSymplecticForm_apply_ofComplexModule (v w : F) :
    imInnerSymplecticForm F v (AlmostComplexStructure.ofComplexModule F w) =
      @inner ℝ F InnerProductSpace.complexToReal.toInner v w :=
  (imInnerSymplecticForm F).apply_ofComplexModule_eq_inner imInnerSymplecticForm_apply v w

/-- The linearized Hamiltonian vector field of the quadratic Hamiltonian `y ↦ (c / 2) ‖y‖²` for
`Im ⟪·, ·⟫`, composed with `-i`, is `-c`. -/
private theorem neg_comp_fderiv_hamiltonianVectorField_div_two_mul_norm_sq (c : ℝ) (y : F) :
    -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
      (fderiv ℝ ((imInnerSymplecticForm F).hamiltonianVectorField fun y ↦ c / 2 * ‖y‖ ^ 2) y)) =
      -c • ContinuousLinearMap.id ℝ F := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [SymplecticForm.hamiltonianVectorField_div_two_mul_norm_sq
    imInnerSymplecticForm_apply_ofComplexModule c, ContinuousLinearMap.fderiv]
  ext v
  simp [AlmostComplexStructure.ofComplexModule_apply, smul_smul]

/-- **`∂s + i ∂t - c(s)` is a linearized Floer operator.** The Sobolev realization of the
linearized Floer operator of the Hamiltonians `H_s(y) = (c(s) / 2) ‖y‖²` for the symplectic form
`Im ⟪·, ·⟫` and the complex structure `i`, along any map `u` of the cylinder, is
`∂s + i ∂t - c(s)`: the Hamiltonian vector field of `H_s` is `-c(s) i`, whose linearization does not
depend on the point. -/
theorem floerSobolevOperator_div_two_mul_norm_sq (c : ℝ → ℝ) (u : ℝ × ℝ → F) :
    (imInnerSymplecticForm F).floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z y ↦ c z.1 / 2 * ‖y‖ ^ 2) u =
      scalarCauchyRiemannOperator F c := by
  rw [SymplecticForm.floerSobolevOperator_def, scalarCauchyRiemannOperator_def]
  congr 2
  funext z
  rw [SymplecticForm.floerJetCoeff_const_eq,
    neg_comp_fderiv_hamiltonianVectorField_div_two_mul_norm_sq]

/-! ### Comparison with the zero mode -/

omit [FiniteDimensional ℂ F] in
/-- The quadratic Hamiltonians `H_s(y) = (c(s) / 2) ‖y‖²` of a `C²` coefficient are jointly
`C²`. -/
private theorem contDiff_uncurry_div_two_mul_norm_sq {c : ℝ → ℝ} (hc : ContDiff ℝ 2 c) :
    ContDiff ℝ 2 (Function.uncurry fun s (y : F) ↦ c s / 2 * ‖y‖ ^ 2) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact ((hc.comp contDiff_fst).div_const 2).mul ((contDiff_norm_sq ℝ).comp contDiff_snd)

/-- The `L∞` class of `s ↦ -c(s) • id` is the coefficient `s ↦ -i dX_{H_s}(0)` of the Morse
operator of the quadratic Hamiltonians `H_s(y) = (c(s) / 2) ‖y‖²`. -/
private theorem ae_eq_neg_comp_fderiv_hamiltonianVectorField {c : ℝ → ℝ}
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -c s • ContinuousLinearMap.id ℝ F) :
    ⇑AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦
      -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ ((imInnerSymplecticForm F).hamiltonianVectorField
          fun y ↦ c s / 2 * ‖y‖ ^ 2) 0)) := by
  filter_upwards [hAL] with s hs
  rw [hs, neg_comp_fderiv_hamiltonianVectorField_div_two_mul_norm_sq]

/-- If `|c(s)| ≤ a`, the linearized Hamiltonian vector fields of the quadratic Hamiltonians
`H_s(y) = (c(s) / 2) ‖y‖²` for `Im ⟪·, ·⟫` have norm at most `a`. -/
private theorem norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le_of_abs_le {c : ℝ → ℝ}
    {a : ℝ} (hca : ∀ s, |c s| ≤ a) (s : ℝ) (y : F) :
    ‖fderiv ℝ ((imInnerSymplecticForm F).hamiltonianVectorField fun y ↦ c s / 2 * ‖y‖ ^ 2) y‖ ≤
      a := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact (norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le
    imInnerSymplecticForm_apply_ofComplexModule _ _).trans (hca s)

variable {c : ℝ → ℝ} {a : ℝ}
  {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- **The kernel of `∂s + i ∂t - c(s)` is that of `d/ds - c(s)`.** Let `c` be `C²` with
`|c(s)| ≤ a < 2π`, and let `AL` be the `L∞` class of `s ↦ -c(s) • id`. The kernel of
`∂s + i ∂t - c(s)` on `W^{1,2}(ℝ × S¹, F)` is the image under the zero mode of the kernel of the
trajectory operator `u ↦ u' - c u` on `W^{1,2}(ℝ, F)`: the nonzero Fourier modes carry no
kernel. -/
theorem ker_scalarCauchyRiemannOperator_eq_map_zeroModeL (hc : ContDiff ℝ 2 c) (ha : a < 2 * π)
    (hca : ∀ s, |c s| ≤ a)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -c s • ContinuousLinearMap.id ℝ F) :
    (scalarCauchyRiemannOperator F c).ker =
      (WeakDerivStep.trajectoryOperator (p := 2) AL).ker.map (zeroModeL F).toLinearMap := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [← floerSobolevOperator_div_two_mul_norm_sq c fun _ ↦ 0]
  exact SymplecticForm.ker_floerSobolevOperator_eq_map_zeroModeL
    (H := fun s y ↦ c s / 2 * ‖y‖ ^ 2) (γ := fun _ ↦ 0)
    imInnerSymplecticForm_apply_ofComplexModule
    (contDiff_uncurry_div_two_mul_norm_sq hc) continuous_const ha
    (norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le_of_abs_le hca · _)
    (ae_eq_neg_comp_fderiv_hamiltonianVectorField hAL)

/-- **`∂s + i ∂t - c(s)` on the zero mode is `d/ds - c(s)`.** Let `c` be `C²` and bounded, and
let `AL` be the `L∞` class of `s ↦ -c(s) • id`. On the zero mode `(s, t) ↦ ζ(s)` of a path
`ζ ∈ W^{1,2}(ℝ, F)` the operator `∂s + i ∂t - c(s)` is the zero mode of `ζ' - c ζ`. -/
theorem scalarCauchyRiemannOperator_zeroModeL (hc : ContDiff ℝ 2 c) (hca : ∀ s, |c s| ≤ a)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -c s • ContinuousLinearMap.id ℝ F)
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    scalarCauchyRiemannOperator F c (zeroModeL F u) =
      zeroModeLp F (WeakDerivStep.trajectoryOperator AL u) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [← floerSobolevOperator_div_two_mul_norm_sq c fun _ ↦ 0]
  exact floerSobolevOperator_zeroModeL (H := fun s y ↦ c s / 2 * ‖y‖ ^ 2) (γ := fun _ ↦ 0)
    (contDiff_uncurry_div_two_mul_norm_sq hc) continuous_const
    (norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le_of_abs_le hca · _)
    (ae_eq_neg_comp_fderiv_hamiltonianVectorField hAL) u

/-- **Surjectivity of `∂s + i ∂t - c(s)` is that of `d/ds - c(s)`.** Let `c` be `C²` with
`|c(s)| ≤ a < 2π`, and let `AL` be the `L∞` class of `s ↦ -c(s) • id`. Then `∂s + i ∂t - c(s)`
maps `W^{1,2}(ℝ × S¹, F)` onto `L²(ℝ × S¹, F)` exactly when `u ↦ u' - c u` maps `W^{1,2}(ℝ, F)`
onto `L²(ℝ, F)`: the nonzero Fourier modes lie in the range. -/
theorem surjective_scalarCauchyRiemannOperator_iff_surjective_trajectoryOperator
    (hc : ContDiff ℝ 2 c) (ha : a < 2 * π) (hca : ∀ s, |c s| ≤ a)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -c s • ContinuousLinearMap.id ℝ F) :
    Function.Surjective (scalarCauchyRiemannOperator F c) ↔
      Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) AL) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [← floerSobolevOperator_div_two_mul_norm_sq c fun _ ↦ 0]
  exact surjective_floerSobolevOperator_iff_surjective_trajectoryOperator
    (H := fun s y ↦ c s / 2 * ‖y‖ ^ 2) (γ := fun _ ↦ 0) imInnerSymplecticForm_apply
    (contDiff_uncurry_div_two_mul_norm_sq hc) continuous_const ha
    (norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le_of_abs_le hca · _)
    (ae_eq_neg_comp_fderiv_hamiltonianVectorField hAL)

/-- **`∂s + i ∂t - c(s)` is Fredholm exactly when `d/ds - c(s)` is.** Let `c` be `C²` with
`|c(s)| ≤ a < 2π`, and let `AL` be the `L∞` class of `s ↦ -c(s) • id`. Then `∂s + i ∂t - c(s)` on
`W^{1,2}(ℝ × S¹, F)` is Fredholm exactly when `u ↦ u' - c u` on `W^{1,2}(ℝ, F)` is. -/
theorem isFredholm_scalarCauchyRiemannOperator_iff_isFredholm_trajectoryOperator
    (hc : ContDiff ℝ 2 c) (ha : a < 2 * π) (hca : ∀ s, |c s| ≤ a)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -c s • ContinuousLinearMap.id ℝ F) :
    (scalarCauchyRiemannOperator F c).IsFredholm ↔
      (WeakDerivStep.trajectoryOperator (p := 2) AL).IsFredholm := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [← floerSobolevOperator_div_two_mul_norm_sq c fun _ ↦ 0]
  exact SymplecticForm.isFredholm_floerSobolevOperator_iff_isFredholm_trajectoryOperator
    (H := fun s y ↦ c s / 2 * ‖y‖ ^ 2) (γ := fun _ ↦ 0) imInnerSymplecticForm_apply
    (contDiff_uncurry_div_two_mul_norm_sq hc) continuous_const ha
    (norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le_of_abs_le hca · _)
    (ae_eq_neg_comp_fderiv_hamiltonianVectorField hAL)

/-- **The index of `∂s + i ∂t - c(s)` is that of `d/ds - c(s)`.** Let `c` be `C²` with
`|c(s)| ≤ a < 2π`, and let `AL` be the `L∞` class of `s ↦ -c(s) • id`. Then `∂s + i ∂t - c(s)` on
`W^{1,2}(ℝ × S¹, F)` and `u ↦ u' - c u` on `W^{1,2}(ℝ, F)` have the same index. -/
theorem index_scalarCauchyRiemannOperator_eq_index_trajectoryOperator
    (hc : ContDiff ℝ 2 c) (ha : a < 2 * π) (hca : ∀ s, |c s| ≤ a)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -c s • ContinuousLinearMap.id ℝ F) :
    (scalarCauchyRiemannOperator F c).index =
      (WeakDerivStep.trajectoryOperator (p := 2) AL).index := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [← floerSobolevOperator_div_two_mul_norm_sq c fun _ ↦ 0]
  exact SymplecticForm.index_floerSobolevOperator_eq_index_trajectoryOperator
    (H := fun s y ↦ c s / 2 * ‖y‖ ^ 2) (γ := fun _ ↦ 0) imInnerSymplecticForm_apply
    (contDiff_uncurry_div_two_mul_norm_sq hc) continuous_const ha
    (norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le_of_abs_le hca · _)
    (ae_eq_neg_comp_fderiv_hamiltonianVectorField hAL)

/-- **The nonzero Fourier modes are bounded below.** Let `c` be `C²` with `|c(s)| ≤ a ≤ 2π`.
Every element `x` of `W^{1,2}(ℝ × S¹, F)` whose slice average vanishes satisfies
`(2π - a)² ‖x‖² ≤ ((2π)² + 1) ‖(∂s + i ∂t - c(s)) x‖²`. The constant depends on `c` only through
the bound `a`; for the neck coefficient `a_R`, `R ≥ 0`, one can take `a = 1`
(`TauCeti.abs_neckCoeff_le_one`), uniformly in the length of the neck. -/
theorem mul_sq_norm_le_mul_sq_norm_scalarCauchyRiemannOperator_of_sliceAverageL_eq_zero
    (hc : ContDiff ℝ 2 c) (ha : a ≤ 2 * π) (hca : ∀ s, |c s| ≤ a) {x : H1 F}
    (hx : sliceAverageL x = 0) :
    (2 * π - a) ^ 2 * ‖x‖ ^ 2 ≤
      ((2 * π) ^ 2 + 1) * ‖scalarCauchyRiemannOperator F c x‖ ^ 2 := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [← floerSobolevOperator_div_two_mul_norm_sq c fun _ ↦ 0]
  exact SymplecticForm.mul_sq_norm_le_mul_sq_norm_floerSobolevOperator_of_sliceAverageL_eq_zero
    (H := fun s y ↦ c s / 2 * ‖y‖ ^ 2) (γ := fun _ ↦ 0)
    imInnerSymplecticForm_apply_ofComplexModule
    (contDiff_uncurry_div_two_mul_norm_sq hc) continuous_const ha
    (norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le_of_abs_le hca · _) hx

/-! ### The tanh pieces -/

/-- `1 < 2π`, the spectral gap bound used for coefficients bounded by `1`. -/
private theorem one_lt_two_mul_pi : (1 : ℝ) < 2 * π := by linarith [two_le_pi]

/-- The coefficient `tanh` is bounded by `1`. -/
private theorem abs_tanh_le_one (s : ℝ) : |tanh s| ≤ 1 :=
  (abs_tanh_lt_one s).le

/-- The coefficient `-tanh` is bounded by `1`. -/
private theorem abs_neg_tanh_le_one (s : ℝ) : |-tanh s| ≤ 1 := by
  rw [abs_neg]
  exact abs_tanh_le_one s

/-- `3 < 2π`, the spectral gap bound used for coefficients bounded by `3`. -/
private theorem three_lt_two_mul_pi : (3 : ℝ) < 2 * π := by linarith [two_le_pi]

omit [FiniteDimensional ℂ F] in
/-- The coefficient `-tanh` of `∂s + i ∂t + tanh s` has an `L∞` class of `s ↦ tanh(s) • id`, which
is also the class of `s ↦ -(-tanh s) • id`. -/
private theorem exists_ae_eq_tanh_smul_id :
    ∃ AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      (AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ -(-tanh s) • ContinuousLinearMap.id ℝ F) ∧
      AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ tanh s • ContinuousLinearMap.id ℝ F := by
  obtain ⟨AL, hAL⟩ := exists_ae_eq_neg_smul_id (F := F) (c := fun s ↦ -tanh s)
    continuous_tanh.neg abs_neg_tanh_le_one
  refine ⟨AL, hAL, ?_⟩
  filter_upwards [hAL] with s hs
  rw [hs, neg_neg]

omit [FiniteDimensional ℂ F] in
/-- The coefficient `tanh` of `∂s + i ∂t - tanh s` has an `L∞` class of `s ↦ -tanh(s) • id`. -/
private theorem exists_ae_eq_neg_tanh_smul_id :
    ∃ AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ -tanh s • ContinuousLinearMap.id ℝ F :=
  exists_ae_eq_neg_smul_id continuous_tanh abs_tanh_le_one

/-- **The kernel of `∂s + i ∂t + tanh s`.** The cylinder operator `∂s + i ∂t + tanh s` has a
kernel of real dimension `2 dim_ℂ F`: it consists of the zero modes of the kernel of `d/ds + tanh s`
on `W^{1,2}(ℝ, F)`, the paths `(cosh s)⁻¹ • x`, `x ∈ F`
(`TauCeti.WeakDerivStep.mem_ker_trajectoryOperator_tanh_smul_id_iff`). For `F = ℂ` it is the
complexification of the line spanned by `sech s`, of real dimension `2`. -/
theorem finrank_ker_scalarCauchyRiemannOperator_neg_tanh :
    Module.finrank ℝ (scalarCauchyRiemannOperator F fun s ↦ -tanh s).ker =
      2 * Module.finrank ℂ F := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨AL, hAL, hAL'⟩ := exists_ae_eq_tanh_smul_id (F := F)
  rw [ker_scalarCauchyRiemannOperator_eq_map_zeroModeL contDiff_tanh.neg one_lt_two_mul_pi
    abs_neg_tanh_le_one hAL,
    (Submodule.equivMapOfInjective _ zeroModeL_injective _).finrank_eq.symm,
    WeakDerivStep.finrank_ker_trajectoryOperator_tanh_smul_id hAL', finrank_real_of_complex]

/-- **`∂s + i ∂t + tanh s` is onto.** Its cokernel is zero. -/
theorem surjective_scalarCauchyRiemannOperator_neg_tanh :
    Function.Surjective (scalarCauchyRiemannOperator F fun s ↦ -tanh s) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨AL, hAL, hAL'⟩ := exists_ae_eq_tanh_smul_id (F := F)
  exact (surjective_scalarCauchyRiemannOperator_iff_surjective_trajectoryOperator contDiff_tanh.neg
    one_lt_two_mul_pi abs_neg_tanh_le_one hAL).2
      (LinearMap.range_eq_top.1 (WeakDerivStep.range_trajectoryOperator_tanh_smul_id hAL'))

/-- **`∂s + i ∂t + tanh s` is Fredholm.** -/
theorem isFredholm_scalarCauchyRiemannOperator_neg_tanh :
    (scalarCauchyRiemannOperator F fun s ↦ -tanh s).IsFredholm := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨AL, hAL, hAL'⟩ := exists_ae_eq_tanh_smul_id (F := F)
  exact (isFredholm_scalarCauchyRiemannOperator_iff_isFredholm_trajectoryOperator contDiff_tanh.neg
    one_lt_two_mul_pi abs_neg_tanh_le_one hAL).2
      (WeakDerivStep.isFredholm_trajectoryOperator_tanh_smul_id hAL')

/-- **The index of `∂s + i ∂t + tanh s` is `2 dim_ℂ F`.** For `F = ℂ` it is `2`. -/
theorem index_scalarCauchyRiemannOperator_neg_tanh :
    (scalarCauchyRiemannOperator F fun s ↦ -tanh s).index = 2 * Module.finrank ℂ F := by
  rw [index_of_surjective _ surjective_scalarCauchyRiemannOperator_neg_tanh,
    finrank_ker_scalarCauchyRiemannOperator_neg_tanh]
  norm_cast

/-- **The kernel of `∂s + i ∂t - tanh s` is zero.** -/
theorem ker_scalarCauchyRiemannOperator_tanh :
    (scalarCauchyRiemannOperator F tanh).ker = ⊥ := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨AL, hAL⟩ := exists_ae_eq_neg_tanh_smul_id (F := F)
  rw [ker_scalarCauchyRiemannOperator_eq_map_zeroModeL contDiff_tanh one_lt_two_mul_pi
    abs_tanh_le_one hAL,
    WeakDerivStep.ker_trajectoryOperator_neg_tanh_smul_id hAL, Submodule.map_bot]

/-- **`∂s + i ∂t - tanh s` is Fredholm.** -/
theorem isFredholm_scalarCauchyRiemannOperator_tanh :
    (scalarCauchyRiemannOperator F tanh).IsFredholm := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨AL, hAL⟩ := exists_ae_eq_neg_tanh_smul_id (F := F)
  exact (isFredholm_scalarCauchyRiemannOperator_iff_isFredholm_trajectoryOperator contDiff_tanh
    one_lt_two_mul_pi abs_tanh_le_one hAL).2
    (WeakDerivStep.isFredholm_trajectoryOperator_neg_tanh_smul_id hAL)

/-- **The index of `∂s + i ∂t - tanh s` is `-2 dim_ℂ F`.** For `F = ℂ` it is `-2`. -/
theorem index_scalarCauchyRiemannOperator_tanh :
    (scalarCauchyRiemannOperator F tanh).index = -(2 * Module.finrank ℂ F : ℤ) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨AL, hAL⟩ := exists_ae_eq_neg_tanh_smul_id (F := F)
  rw [index_scalarCauchyRiemannOperator_eq_index_trajectoryOperator contDiff_tanh
    one_lt_two_mul_pi abs_tanh_le_one hAL,
    WeakDerivStep.index_trajectoryOperator_neg_tanh_smul_id hAL, finrank_real_of_complex]
  norm_cast

/-- **The cokernel of `∂s + i ∂t - tanh s`.** It has real dimension `2 dim_ℂ F`, that of the
cokernel of `d/ds - tanh s` on the line, which is spanned by the paths `(cosh s)⁻¹ • x`, `x ∈ F`.
For `F = ℂ` its real dimension is `2`. -/
theorem finrank_quotient_range_scalarCauchyRiemannOperator_tanh :
    Module.finrank ℝ (Lp F 2 stripMeasure ⧸ (scalarCauchyRiemannOperator F tanh).range) =
      2 * Module.finrank ℂ F := by
  have h := index_scalarCauchyRiemannOperator_tanh (F := F)
  rw [index_of_injective _ (LinearMap.ker_eq_bot.1 ker_scalarCauchyRiemannOperator_tanh),
    neg_inj] at h
  exact_mod_cast h

/-! ### The glued operator -/

/-- **The glued cylinder operator is invertible.** The cylinder operator `∂s + i ∂t - a_R(s)`
obtained by gluing `∂s + i ∂t + tanh s` to `∂s + i ∂t - tanh s` along a neck of length `2R`
(`TauCeti.neckCoeff`) is a bijection from `W^{1,2}(ℝ × S¹, F)` onto `L²(ℝ × S¹, F)`: the kernel of
the first piece has cancelled against the cokernel of the second. -/
theorem bijective_scalarCauchyRiemannOperator_neckCoeff (R : ℝ) :
    Function.Bijective (scalarCauchyRiemannOperator F (neckCoeff R)) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨AL, hAL⟩ := exists_ae_eq_neg_smul_id (F := F) (continuous_neckCoeff R)
    (abs_neckCoeff_le_three R)
  refine ⟨LinearMap.ker_eq_bot.1 ?_,
    (surjective_scalarCauchyRiemannOperator_iff_surjective_trajectoryOperator
      (contDiff_neckCoeff R) three_lt_two_mul_pi (abs_neckCoeff_le_three R) hAL).2
        (WeakDerivStep.bijective_trajectoryOperator_neg_neckCoeff_smul_id (p := 2) R
          ENNReal.ofNat_ne_top AL hAL).2⟩
  rw [ker_scalarCauchyRiemannOperator_eq_map_zeroModeL (contDiff_neckCoeff R) three_lt_two_mul_pi
    (abs_neckCoeff_le_three R) hAL,
    WeakDerivStep.ker_trajectoryOperator_neg_neckCoeff_smul_id R AL hAL, Submodule.map_bot]

/-- **The index is additive under gluing.** The index `0` of the glued operator
`∂s + i ∂t - a_R(s)` is the sum of the indices `2 dim_ℂ F` of `∂s + i ∂t + tanh s` and
`-2 dim_ℂ F` of `∂s + i ∂t - tanh s`, while its kernel and cokernel are zero: the kernels and the
cokernels are not separately additive. -/
theorem index_scalarCauchyRiemannOperator_neckCoeff_eq_add (R : ℝ) :
    (scalarCauchyRiemannOperator F (neckCoeff R)).index =
      (scalarCauchyRiemannOperator F fun s ↦ -tanh s).index +
        (scalarCauchyRiemannOperator F tanh).index := by
  rw [index_eq_zero_of_bijective _ (bijective_scalarCauchyRiemannOperator_neckCoeff R),
    index_scalarCauchyRiemannOperator_neg_tanh, index_scalarCauchyRiemannOperator_tanh,
    add_neg_cancel]

/-- **The values of the inverse of the glued cylinder operator are not uniformly bounded.** If
`‖x‖_{L²} ≤ C ‖(∂s + i ∂t - a_R(s)) x‖` for the value `x ↦ ξ` of every
`x ∈ W^{1,2}(ℝ × S¹, F)`, with `F ≠ 0`, then `C ≥ exp (2 R) / 2`. The test element is the zero mode
of the path `sech (s + R) • e`, the kernel element of the first piece moved to the left end of the
neck. -/
theorem exp_div_two_le_of_forall_norm_valueL_le_mul_norm_scalarCauchyRiemannOperator_neckCoeff
    [Nontrivial F] (R : ℝ) {C : ℝ}
    (hC : ∀ x, ‖valueL 2 x‖ ≤ C * ‖scalarCauchyRiemannOperator F (neckCoeff R) x‖) :
    exp (2 * R) / 2 ≤ C := by
  obtain ⟨AL, hAL⟩ := exists_ae_eq_neg_smul_id (F := F) (continuous_neckCoeff R)
    (abs_neckCoeff_le_three R)
  refine WeakDerivStep.exp_div_two_le_of_forall_norm_prev_le_mul_norm_trajectoryOperator_neckCoeff
    R AL hAL fun u ↦ ?_
  rw [← LinearIsometry.norm_map (zeroModeLp F) (prev _ u), ← valueL_zeroModeL,
    ← LinearIsometry.norm_map (zeroModeLp F) (WeakDerivStep.trajectoryOperator AL u),
    ← scalarCauchyRiemannOperator_zeroModeL (contDiff_neckCoeff R) (abs_neckCoeff_le_three R) hAL]
  exact hC _

/-- **The inverse of the glued cylinder operator is not uniformly bounded.** If
`‖x‖ ≤ C ‖(∂s + i ∂t - a_R(s)) x‖` for every `x ∈ W^{1,2}(ℝ × S¹, F)`, with `F ≠ 0`, then
`C ≥ exp (2 R) / 2`. -/
theorem exp_div_two_le_of_forall_norm_le_mul_norm_scalarCauchyRiemannOperator_neckCoeff
    [Nontrivial F] (R : ℝ) {C : ℝ}
    (hC : ∀ x, ‖x‖ ≤ C * ‖scalarCauchyRiemannOperator F (neckCoeff R) x‖) :
    exp (2 * R) / 2 ≤ C :=
  exp_div_two_le_of_forall_norm_valueL_le_mul_norm_scalarCauchyRiemannOperator_neckCoeff R
    fun x ↦ (norm_valueL_le x).trans (hC x)

end TauCeti.CylinderSobolev
