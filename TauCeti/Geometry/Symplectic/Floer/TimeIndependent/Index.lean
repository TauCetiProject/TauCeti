/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Sobolev
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Fredholm.Criteria
import TauCeti.Analysis.Fredholm.Prod
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Stationary
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Coprod

/-!
# The index of the linearized operator along a time-independent cylinder

Let `F` be a finite-dimensional complex inner product space with the symplectic form
`ω = Im ⟪·, ·⟫` and the complex structure `i`, a unitary trivialization, let `H : F → ℝ` be a `C²`
autonomous Hamiltonian and `γ` a continuous curve with `‖dX_H(γ(s))‖ ≤ a < 2π` for every `s`, and
let

`D ξ = ∂s ξ + i (∂t ξ - dX_H(γ(s)) ξ)`

be the Sobolev realization `W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator
along the time-independent cylinder `(s, t) ↦ γ(s)`. By
`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Sobolev`, `D` commutes with the slice average
`P`, the projection onto the zero Fourier mode, it is bounded below on the nonzero modes, and on the
zero mode it is the Morse operator `M ζ = ζ' - i dX_H(γ) ζ` on `W^{1,2}(ℝ, F)`, so that `D` and `M`
have the same kernel. This file compares their cokernels, and hence their Fredholm properties and
indices.

* **The nonzero modes are onto.** Every `y ∈ L²` with `P y = 0` is `D x` for some `x` with `P x = 0`
  (`TauCeti.SymplecticForm.exists_sliceAverageL_eq_zero_and_floerSobolevOperator_eq`). The proof is
  the method of continuity (`ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap`) along
  the Hamiltonians
  `(1 - τ) H + τ π ‖v‖² / 2`, `τ ∈ [0, 1]`. Their linearized operators along `γ` are the affine
  combinations of the two ends, and since `‖dX‖ ≤ max a π < 2π` along the whole path, the gap
  estimate on the nonzero modes holds uniformly. At `τ = 1` the operator is
  `∂s + i ∂t - π`, a stationary operator at a nondegenerate orbit, since the return map of
  `ζ' = -π i ζ` is `-1`; it is an isomorphism
  (`TauCeti.Floer.bijective_stationarySobolevOperator_ofComplexModule`), and so onto the nonzero
  modes.
* **The splitting.** Every `x ∈ W^{1,2}(ℝ × S¹, F)` is uniquely the zero mode of a path in
  `W^{1,2}(ℝ, F)` plus an element with vanishing slice average
  (`TauCeti.CylinderSobolev.sliceAverageL_eq_self_iff`), and likewise on `L²`
  (`TauCeti.CylinderSobolev.sliceAverageLp_eq_self_iff`). In these splittings `D` is the product
  of `M` and its restriction to the nonzero modes, which is an isomorphism.
* **Consequences.** `D` is onto exactly when `M` is
  (`TauCeti.SymplecticForm.surjective_floerSobolevOperator_iff_surjective_trajectoryOperator`), `D`
  is Fredholm exactly when `M` is
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_iff_isFredholm_trajectoryOperator`), and
  then they have the same index
  (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_index_trajectoryOperator`).

The coefficient of `M` is `A(s) = -i dX_H(γ(s))`, minus the Hessian of `H` at `γ(s)`. When it has
hyperbolic limits `A±` at `±∞`, for instance when `γ` runs between nondegenerate critical points
`p±` of `H`, the index of `M` is `dim Eˢ(A⁻) - dim Eˢ(A⁺)` for the stable subspaces of the limits
(`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_stableSubspace_sub_finrank`); at
nondegenerate critical points this is the difference `ind(p₊) - ind(p₋)` of their Morse indices.
Through the theorems of this file it is then also the index of `D`.

## References

* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the linearized operator at
  time-independent solutions of a small Hamiltonian.
* D. Gilbarg and N. S. Trudinger, *Elliptic partial differential equations of second order*,
  Theorem 5.2, for the method of continuity.
-/

public section

noncomputable section

open Real Set Function MeasureTheory ContinuousLinearMap
open TauCeti.StripSobolev TauCeti.CylinderSobolev
open scoped RealInnerProductSpace ENNReal

namespace TauCeti.SymplecticForm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {ω : SymplecticForm F} {H : F → ℝ} {γ : ℝ → F}
  {A : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}

/-- Multiplication by `i` on `F`, as a continuous real-linear map. -/
local notation "𝕁" => LinearMap.toContinuousLinearMap
  (AlmostComplexStructure.toLinearMap (AlmostComplexStructure.ofComplexModule F))

/-- `𝔻 K c` is the Sobolev realization of the linearized operator of the autonomous Hamiltonian `K`
along the time-independent cylinder `(s, t) ↦ c(s)`, in the trivialization `i`. -/
local notation:max "𝔻" K:max c:max => SymplecticForm.floerSobolevOperator ω (fun _ _ ↦ 𝕁)
  (fun _ _ ↦ 0) (fun _ ↦ K) (fun z ↦ c (Prod.fst z))

section Homotopy

/-! ### The homotopy to a quadratic Hamiltonian -/

/-- In a unitary trivialization, the Hamiltonian vector field of `π ‖v‖² / 2` is `-π i v`. -/
private theorem hamiltonianVectorField_pi_div_two_mul_norm_sq
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) :
    ω.hamiltonianVectorField (fun v ↦ π / 2 * ‖v‖ ^ 2) = ⇑(-(π • 𝕁)) := by
  funext x
  have h : (fun v : F ↦ π / 2 * ‖v‖ ^ 2) = fun v ↦ π * (‖v‖ ^ 2 / 2) := by
    funext v
    ring
  rw [h, hamiltonianVectorField_const_mul, hamiltonianVectorField_half_norm_sq_eq_neg_I_smul hω]
  simp

/-- The derivative of the Hamiltonian vector field of `π ‖v‖² / 2` is the constant `-π i`. -/
private theorem fderiv_hamiltonianVectorField_pi_div_two_mul_norm_sq
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (y : F) :
    fderiv ℝ (ω.hamiltonianVectorField fun v ↦ π / 2 * ‖v‖ ^ 2) y = -(π • 𝕁) := by
  rw [hamiltonianVectorField_pi_div_two_mul_norm_sq hω, ContinuousLinearMap.fderiv]

/-- The norm of `-π i` is at most `π`. -/
private theorem norm_neg_pi_smul_ofComplexModule_le : ‖-(π • 𝕁)‖ ≤ π := by
  rw [norm_neg, norm_smul, Real.norm_of_nonneg pi_pos.le]
  exact mul_le_of_le_one_right pi_pos.le (opNorm_le_bound _ zero_le_one fun v ↦ by simp [norm_smul])

omit [FiniteDimensional ℂ F] in
/-- The Hamiltonians `(1 - τ) H + τ π ‖v‖² / 2` are `C²`. -/
private theorem contDiff_homotopy (hH : ContDiff ℝ 2 H) (τ : ℝ) :
    ContDiff ℝ 2 fun v ↦ (1 - τ) * H v + τ * (π / 2 * ‖v‖ ^ 2) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact (contDiff_const.mul hH).add (contDiff_const.mul (contDiff_const.mul (contDiff_norm_sq ℝ)))

/-- The derivative of the Hamiltonian vector field of `(1 - τ) H + τ π ‖v‖² / 2` is the affine
combination `(1 - τ) dX_H - τ π i`. -/
private theorem fderiv_hamiltonianVectorField_homotopy (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hH : ContDiff ℝ 2 H) (τ : ℝ) (y : F) :
    fderiv ℝ (ω.hamiltonianVectorField fun v ↦ (1 - τ) * H v + τ * (π / 2 * ‖v‖ ^ 2)) y =
      (1 - τ) • fderiv ℝ (ω.hamiltonianVectorField H) y + τ • -(π • 𝕁) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  set S₀ : F →L[ℝ] F := -(π • 𝕁)
  have hQ : Differentiable ℝ fun v : F ↦ π / 2 * ‖v‖ ^ 2 :=
    ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero).const_mul _
  have hXH : Differentiable ℝ (ω.hamiltonianVectorField H) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) hH).differentiable one_ne_zero
  have hX : (ω.hamiltonianVectorField fun v ↦ (1 - τ) * H v + τ * (π / 2 * ‖v‖ ^ 2)) =
      fun y ↦ (1 - τ) • ω.hamiltonianVectorField H y + τ • S₀ y := by
    funext y
    rw [hamiltonianVectorField_const_mul_add_const_mul ω (G := fun v ↦ π / 2 * ‖v‖ ^ 2)
      (hH.differentiable two_ne_zero y) (hQ y), hamiltonianVectorField_pi_div_two_mul_norm_sq hω]
  rw [hX]
  exact (((hXH y).hasFDerivAt.const_smul (1 - τ)).add (S₀.hasFDerivAt.const_smul τ)).fderiv

/-- Along the homotopy, the derivative of the Hamiltonian vector field stays below `max a π`. -/
private theorem norm_fderiv_hamiltonianVectorField_homotopy_le
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) {a τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) {y : F} (hy : ‖fderiv ℝ (ω.hamiltonianVectorField H) y‖ ≤ a) :
    ‖fderiv ℝ (ω.hamiltonianVectorField fun v ↦ (1 - τ) * H v + τ * (π / 2 * ‖v‖ ^ 2)) y‖ ≤
      max a π := by
  rw [fderiv_hamiltonianVectorField_homotopy hω hH]
  have h₁ : ‖(1 - τ) • fderiv ℝ (ω.hamiltonianVectorField H) y‖ ≤ (1 - τ) * a := by
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hτ.2)]
    exact mul_le_mul_of_nonneg_left hy (sub_nonneg.2 hτ.2)
  have h₂ : ‖τ • -(π • 𝕁)‖ ≤ τ * π := by
    rw [norm_smul, Real.norm_of_nonneg hτ.1]
    exact mul_le_mul_of_nonneg_left norm_neg_pi_smul_ofComplexModule_le hτ.1
  refine (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans ?_)
  nlinarith [le_max_left a π, le_max_right a π, hτ.1, hτ.2]

/-- **The linearized operators along the homotopy are affine.** Along `(s, t) ↦ γ(s)`, the
linearized operator of `(1 - τ) H + τ π ‖v‖² / 2` is `(1 - τ) D_H + τ D_Q` for the linearized
operators `D_H` of `H` and `D_Q` of `Q(v) = π ‖v‖² / 2`. -/
private theorem floerSobolevOperator_homotopy_apply (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) (x : H1 F) :
    𝔻 (fun v ↦ (1 - τ) * H v + τ * (π / 2 * ‖v‖ ^ 2)) γ x =
      (1 - τ) • 𝔻 H γ x + τ • 𝔻 (fun v ↦ π / 2 * ‖v‖ ^ 2) γ x := by
  have hMτ := memLp_floerJetCoeff_const_comp_fst (J := AlmostComplexStructure.ofComplexModule F)
    (contDiff_homotopy hH τ) hγ fun s ↦ norm_fderiv_hamiltonianVectorField_homotopy_le hω hH hτ
      (haγ s)
  have hM₀ := memLp_floerJetCoeff_const_comp_fst (J := AlmostComplexStructure.ofComplexModule F)
    hH hγ haγ
  have hM₁ := memLp_floerJetCoeff_const_comp_fst (J := AlmostComplexStructure.ofComplexModule F)
    (by simpa using contDiff_homotopy (F := F) hH 1) hγ fun s ↦
      (fderiv_hamiltonianVectorField_pi_div_two_mul_norm_sq hω (γ s)).symm ▸
        norm_neg_pi_smul_ofComplexModule_le
  set D₀ := 𝔻 H γ
  set D₁ := 𝔻 (fun v ↦ π / 2 * ‖v‖ ^ 2) γ
  refine Lp.ext ?_
  filter_upwards [coeFn_floerSobolevOperator ω hMτ x, coeFn_floerSobolevOperator ω hM₀ x,
    coeFn_floerSobolevOperator ω hM₁ x, Lp.coeFn_add ((1 - τ) • D₀ x) (τ • D₁ x),
    Lp.coeFn_smul (1 - τ) (D₀ x), Lp.coeFn_smul τ (D₁ x)] with z h hD₀ hD₁ hadd hs₀ hs₁
  simp only [D₀, D₁, h, hadd, hs₀, hs₁, hD₀, hD₁, Pi.add_apply, Pi.smul_apply,
    floerJetCoeff_const_eq, fderiv_hamiltonianVectorField_homotopy hω hH,
    fderiv_hamiltonianVectorField_pi_div_two_mul_norm_sq hω, firstOrderJetCoeff_apply, neg_apply,
    ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_add, map_smul, map_neg]
  module

end Homotopy

section Endpoint

/-! ### The endpoint `∂s + i ∂t - π` -/

/-- The return map of `ζ' = -π i ζ` is `-1`: the left Dyson series of the constant path `-π i` at
time `1` is `-1`. -/
private theorem dysonSeriesLeft_neg_pi_smul_ofComplexModule_one :
    dysonSeriesLeft (fun _ : ℝ ↦ -(π • 𝕁)) 1 = -1 := by
  have hJ : 𝕁 * 𝕁 = -1 := by
    ext v
    simp
  -- The solution of `f' = -π i f` with `f 0 = 1` is `f t = cos (π t) - sin (π t) i`.
  set f : ℝ → F →L[ℝ] F := fun t ↦ Real.cos (π * t) • 1 - Real.sin (π * t) • 𝕁
  have hf (t : ℝ) : HasDerivAt f (-(π • 𝕁) * f t) t := by
    have hc : HasDerivAt (fun t ↦ Real.cos (π * t)) (-Real.sin (π * t) * π) t := by
      simpa using ((hasDerivAt_id t).const_mul π).cos
    have hs : HasDerivAt (fun t ↦ Real.sin (π * t)) (Real.cos (π * t) * π) t := by
      simpa using ((hasDerivAt_id t).const_mul π).sin
    convert (hc.smul_const (1 : F →L[ℝ] F)).sub (hs.smul_const 𝕁) using 1
    rw [mul_sub, mul_smul_comm, mul_smul_comm, mul_one, neg_mul, smul_mul_assoc, hJ]
    module
  have h := eq_dysonSeriesLeft_mul continuous_const hf 1
  simp only [f, mul_one, mul_zero, Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero, one_smul,
    zero_smul, sub_zero, neg_smul] at h
  exact h.symm

/-- **The linearized operator of `π ‖v‖² / 2` is an isomorphism.** In a unitary trivialization, the
linearized operator along `(s, t) ↦ γ(s)` of the Hamiltonian `π ‖v‖² / 2` is the stationary
operator `∂s + i ∂t - π`, which is bijective from `W^{1,2}(ℝ × S¹, F)` onto `L²(ℝ × S¹, F)`. -/
private theorem bijective_floerSobolevOperator_pi_div_two_mul_norm_sq
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) :
    Bijective (𝔻 (fun v ↦ π / 2 * ‖v‖ ^ 2) γ) := by
  set S₀ : F →L[ℝ] F := -(π • 𝕁)
  have hD : 𝔻 (fun v ↦ π / 2 * ‖v‖ ^ 2) γ = Floer.stationarySobolevOperator
        (fun _ ↦ AlmostComplexStructure.ofComplexModule F)
        (fun t : ℝ ↦ (ContinuousMap.const (AddCircle (1 : ℝ)) S₀) t) := by
    rw [floerSobolevOperator_def, Floer.stationarySobolevOperator_def]
    congr 2
    funext z
    rw [floerJetCoeff_const_eq, fderiv_hamiltonianVectorField_pi_div_two_mul_norm_sq hω]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp only [firstOrderJetCoeff_apply, Floer.stationaryJetCoeff_apply, neg_apply,
      ContinuousMap.const_apply, map_sub, S₀]
    abel
  have hS (t : AddCircle (1 : ℝ)) (v w : F) :
      (inner ℂ ((ContinuousMap.const (AddCircle (1 : ℝ)) S₀) t v) w).im +
        (inner ℂ v ((ContinuousMap.const (AddCircle (1 : ℝ)) S₀) t w)).im = 0 := by
    simp [S₀, AlmostComplexStructure.ofComplexModule_apply, ← Complex.coe_smul, inner_smul_left,
      inner_smul_right]
  have hdet : LinearMap.det ((1 - dysonSeriesLeft
      (fun t : ℝ ↦ (ContinuousMap.const (AddCircle (1 : ℝ)) S₀) t) 1 : F →L[ℝ] F) :
        F →ₗ[ℝ] F) ≠ 0 := by
    have h₁ : (1 - dysonSeriesLeft
        (fun t : ℝ ↦ (ContinuousMap.const (AddCircle (1 : ℝ)) S₀) t) 1 : F →L[ℝ] F) =
          (2 : ℝ) • (1 : F →L[ℝ] F) := by
      simp only [ContinuousMap.const_apply, S₀, dysonSeriesLeft_neg_pi_smul_ofComplexModule_one]
      module
    rw [h₁, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
    simp
  rw [hD]
  exact Floer.bijective_stationarySobolevOperator_ofComplexModule contDiff_const hS hdet

end Endpoint

section NonzeroModes

/-! ### The nonzero modes -/

variable (F) in
/-- The nonzero modes of `W^{1,2}(ℝ × S¹, F)`: the elements with vanishing slice average. -/
private abbrev nonzeroModeSobolev : Submodule ℝ (H1 F) :=
  LinearMap.ker (sliceAverageL : H1 F →L[ℝ] H1 F).toLinearMap

variable (F) in
/-- The nonzero modes of `L²(ℝ × S¹, F)`: the elements with vanishing slice average. -/
private abbrev nonzeroModeLp : Submodule ℝ (Lp F 2 stripMeasure) :=
  LinearMap.ker (sliceAverageLp : Lp F 2 stripMeasure →L[ℝ] Lp F 2 stripMeasure).toLinearMap

private theorem mem_nonzeroModeSobolev {x : H1 F} :
    x ∈ nonzeroModeSobolev F ↔ sliceAverageL x = 0 :=
  LinearMap.mem_ker

omit [FiniteDimensional ℂ F] in
private theorem mem_nonzeroModeLp {y : Lp F 2 stripMeasure} :
    y ∈ nonzeroModeLp F ↔ sliceAverageLp y = 0 :=
  LinearMap.mem_ker

private theorem sliceAverageL_coe_nonzeroModeSobolev (x : nonzeroModeSobolev F) :
    sliceAverageL (x : H1 F) = 0 :=
  mem_nonzeroModeSobolev.1 x.property

omit [FiniteDimensional ℂ F] in
private theorem sliceAverageLp_coe_nonzeroModeLp (y : nonzeroModeLp F) :
    sliceAverageLp (y : Lp F 2 stripMeasure) = 0 :=
  mem_nonzeroModeLp.1 y.property

variable (ω) in
/-- The restriction to the nonzero modes of the linearized operator of an autonomous Hamiltonian
`K` along the time-independent cylinder `(s, t) ↦ c(s)`: it maps nonzero modes to nonzero modes,
since it commutes with the slice averages. -/
private def nonzeroModes (K : F → ℝ) (c : ℝ → F) :
    nonzeroModeSobolev F →L[ℝ] nonzeroModeLp F :=
  ((𝔻 K c).comp (nonzeroModeSobolev F).subtypeL).codRestrict _
    fun x ↦ mem_nonzeroModeLp.2 (by
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        ← floerSobolevOperator_sliceAverageL, sliceAverageL_coe_nonzeroModeSobolev, map_zero])

private theorem coe_nonzeroModes_apply (K : F → ℝ) (c : ℝ → F) (x : nonzeroModeSobolev F) :
    (nonzeroModes ω K c x : Lp F 2 stripMeasure) = 𝔻 K c x := by
  rw [nonzeroModes, coe_codRestrict_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

/-- **The nonzero modes are onto**, as a statement about the restriction to the nonzero modes. -/
private theorem surjective_nonzeroModes (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) :
    Surjective (nonzeroModes ω H γ) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hg := ω.apply_ofComplexModule_eq_real_inner hω
  set Q : F → ℝ := fun v ↦ π / 2 * ‖v‖ ^ 2
  set L₀ := nonzeroModes ω H γ
  set L₁ := nonzeroModes ω Q γ
  set b := max a π
  have hb : b < 2 * π := max_lt ha (by linarith [pi_pos])
  have : CompleteSpace (nonzeroModeSobolev F) :=
    (ContinuousLinearMap.isClosed_ker (sliceAverageL : H1 F →L[ℝ] H1 F)).completeSpace_coe
  refine (surjective_iff_of_forall_norm_le_lineMap (𝕜 := ℝ) (E := nonzeroModeSobolev F)
    (F := nonzeroModeLp F) (L₀ := L₀) (L₁ := L₁)
    (C := √((2 * π) ^ 2 + 1) / (2 * π - b)) fun τ hτ x ↦ ?_).2 fun y ↦ ?_
  · -- The a priori estimate along the homotopy is the gap estimate on the nonzero modes.
    have hgap := mul_sq_norm_le_mul_sq_norm_floerSobolevOperator_of_sliceAverageL_eq_zero hg
      (contDiff_homotopy hH τ) hγ hb.le
      (fun s ↦ norm_fderiv_hamiltonianVectorField_homotopy_le hω hH hτ (haγ s))
      (sliceAverageL_coe_nonzeroModeSobolev x)
    rw [floerSobolevOperator_homotopy_apply hω hH hγ haγ hτ] at hgap
    rw [← Submodule.norm_coe x, ← Submodule.norm_coe (s := nonzeroModeLp F)]
    simp only [L₀, L₁, Q, AffineMap.lineMap_apply_module, add_apply, smul_apply, Submodule.coe_add,
      Submodule.coe_smul, coe_nonzeroModes_apply]
    -- Take square roots in `(2π - b)² ‖x‖² ≤ ((2π)² + 1) ‖D x‖²`.
    rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.2 hb)]
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    linarith
  -- At the endpoint the operator is bijective, and the preimages of nonzero modes are nonzero
  -- modes.
  have hbij := bijective_floerSobolevOperator_pi_div_two_mul_norm_sq (γ := γ) hω
  obtain ⟨x, hx⟩ := hbij.2 (y : Lp F 2 stripMeasure)
  have hPx : sliceAverageL x = 0 := hbij.1 (by
    rw [floerSobolevOperator_sliceAverageL, hx, sliceAverageLp_coe_nonzeroModeLp, map_zero])
  exact ⟨⟨x, mem_nonzeroModeSobolev.2 hPx⟩, Subtype.ext hx⟩

/-- **The nonzero modes are onto.** In a unitary trivialization, let `H` be a `C²` autonomous
Hamiltonian and `γ` a continuous curve with `‖dX_H(γ(s))‖ ≤ a < 2π` for every `s`. Every
`y ∈ L²(ℝ × S¹, F)` with vanishing slice average is `D x` for some `x ∈ W^{1,2}(ℝ × S¹, F)` with
vanishing slice average, where `D` is the Sobolev realization of the linearized operator along the
time-independent cylinder `(s, t) ↦ γ(s)`. -/
theorem exists_sliceAverageL_eq_zero_and_floerSobolevOperator_eq
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    {y : Lp F 2 stripMeasure} (hy : sliceAverageLp y = 0) :
    ∃ x : H1 F, sliceAverageL x = 0 ∧ 𝔻 H γ x = y := by
  obtain ⟨x, hx⟩ := surjective_nonzeroModes hω hH hγ ha haγ ⟨y, mem_nonzeroModeLp.2 hy⟩
  exact ⟨x, sliceAverageL_coe_nonzeroModeSobolev x, congrArg Subtype.val hx⟩

/-- The restriction of the linearized operator to the nonzero modes is bijective. -/
private theorem bijective_nonzeroModes (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) :
    Bijective (nonzeroModes ω H γ) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hg := ω.apply_ofComplexModule_eq_real_inner hω
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ Subtype.ext ?_,
    surjective_nonzeroModes hω hH hγ ha haγ⟩
  -- A kernel element is its own slice average, which vanishes on the nonzero modes.
  have hD := congrArg Subtype.val hx
  rw [coe_nonzeroModes_apply, Submodule.coe_zero] at hD
  rw [← sliceAverageL_eq_self_of_floerSobolevOperator_eq_zero hg hH hγ ha haγ hD,
    sliceAverageL_coe_nonzeroModeSobolev, Submodule.coe_zero]

end NonzeroModes

section Splitting

/-! ### The splitting into the zero mode and the nonzero modes -/

variable (F) in
/-- `L²(ℝ, F)`, the zero mode of `L²(ℝ × S¹, F)`. -/
private abbrev pathLp := Lp F 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))

variable (F) in
/-- `W^{1,2}(ℝ, F)`, the zero mode of `W^{1,2}(ℝ × S¹, F)`. -/
private abbrev pathSobolev := WeakDerivStep volume ⊤ 2 (ContinuousLinearMap.id ℝ (pathLp F))

variable (F) in
/-- `W^{1,2}(ℝ × S¹, F)` is the zero mode of `W^{1,2}(ℝ, F)` plus the nonzero modes. -/
private def zeroModeProdEquiv : (pathSobolev F × nonzeroModeSobolev F) ≃L[ℝ] H1 F :=
  have h := ContinuousLinearMap.bijective_coprod_subtypeL_ker (U := zeroModeL F) zeroModeL_injective
    sliceAverageL_zeroModeL sliceAverageL_mem_range_zeroModeL
  ContinuousLinearEquiv.ofBijective (𝕜 := ℝ) (E := pathSobolev F × nonzeroModeSobolev F)
    (F := H1 F) ((zeroModeL F).coprod (nonzeroModeSobolev F).subtypeL)
    (LinearMap.ker_eq_bot.2 h.1) (LinearMap.range_eq_top.2 h.2)

variable (F) in
/-- `L²(ℝ × S¹, F)` is the zero mode of `L²(ℝ, F)` plus the nonzero modes. -/
private def zeroModeLpProdEquiv : (pathLp F × nonzeroModeLp F) ≃L[ℝ] Lp F 2 stripMeasure :=
  have h := ContinuousLinearMap.bijective_coprod_subtypeL_ker
    (U := (zeroModeLp F).toContinuousLinearMap) (zeroModeLp F).injective sliceAverageLp_zeroModeLp
    sliceAverageLp_mem_range_zeroModeLp
  ContinuousLinearEquiv.ofBijective (𝕜 := ℝ) (E := pathLp F × nonzeroModeLp F)
    (F := Lp F 2 stripMeasure)
    ((zeroModeLp F).toContinuousLinearMap.coprod (nonzeroModeLp F).subtypeL)
    (LinearMap.ker_eq_bot.2 h.1) (LinearMap.range_eq_top.2 h.2)

/-- In the splittings into the zero mode and the nonzero modes, the linearized operator along a
time-independent cylinder is the product of the Morse operator and its restriction to the nonzero
modes. -/
private theorem floerSobolevOperator_comp_zeroModeProdEquiv (hH : ContDiff ℝ 2 H)
    (hγ : Continuous γ) {a : ℝ} (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(𝕁 ∘L fderiv ℝ (ω.hamiltonianVectorField H) (γ s))) :
    (𝔻 H γ).comp (zeroModeProdEquiv F : _ →L[ℝ] H1 F) =
      (zeroModeLpProdEquiv F : _ →L[ℝ] Lp F 2 stripMeasure).comp
        ((WeakDerivStep.trajectoryOperator (p := 2) A).prodMap
          (nonzeroModes ω H γ)) := by
  refine ContinuousLinearMap.ext fun p ↦ ?_
  simp [zeroModeProdEquiv, zeroModeLpProdEquiv, coe_nonzeroModes_apply,
    ContinuousLinearEquiv.coe_ofBijective, floerSobolevOperator_zeroModeL hH hγ haγ hA]

end Splitting

section Index

/-! ### The cokernel, the Fredholm property and the index -/

/-- The linearized operator along a time-independent cylinder, conjugated by the splittings into the
zero mode and the nonzero modes. -/
private theorem floerSobolevOperator_eq_comp (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(𝕁 ∘L fderiv ℝ (ω.hamiltonianVectorField H) (γ s))) :
    𝔻 H γ =
      (zeroModeLpProdEquiv F : _ →L[ℝ] Lp F 2 stripMeasure).comp
        (((WeakDerivStep.trajectoryOperator (p := 2) A).prodMap
          (nonzeroModes ω H γ)).comp
            ((zeroModeProdEquiv F).symm : H1 F →L[ℝ] _)) := by
  ext1 x
  have h := congrArg (fun T ↦ T ((zeroModeProdEquiv F).symm x))
    (floerSobolevOperator_comp_zeroModeProdEquiv (A := A) hH hγ haγ hA)
  simpa using h

/-- **The linearized operator is onto exactly when the Morse operator is.** In a unitary
trivialization, let `H` be a `C²` autonomous Hamiltonian and `γ` a continuous curve with
`‖dX_H(γ(s))‖ ≤ a < 2π` for every `s`, and let `A` be the `L∞` class of `s ↦ -i dX_H(γ(s))`. The
Sobolev realization of the linearized operator along the time-independent cylinder
`(s, t) ↦ γ(s)` is onto `L²(ℝ × S¹, F)` exactly when the Morse operator `ζ ↦ ζ' - i dX_H(γ) ζ` is
onto `L²(ℝ, F)`. -/
theorem surjective_floerSobolevOperator_iff_surjective_trajectoryOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(𝕁 ∘L fderiv ℝ (ω.hamiltonianVectorField H) (γ s))) :
    Surjective (𝔻 H γ) ↔
      Surjective (WeakDerivStep.trajectoryOperator (p := 2) A) := by
  rw [floerSobolevOperator_eq_comp hH hγ haγ hA, coe_comp, coe_comp,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
    Surjective.of_comp_iff' (zeroModeLpProdEquiv F).bijective,
    Surjective.of_comp_iff _ (zeroModeProdEquiv F).symm.surjective,
    coe_prodMap', Prod.map_surjective]
  exact and_iff_left (bijective_nonzeroModes hω hH hγ ha haγ).2

/-- **The linearized operator is Fredholm exactly when the Morse operator is.** Under the hypotheses
of `TauCeti.SymplecticForm.surjective_floerSobolevOperator_iff_surjective_trajectoryOperator`, the
Sobolev realization of the linearized operator along the time-independent cylinder
`(s, t) ↦ γ(s)` is Fredholm exactly when the Morse operator `ζ ↦ ζ' - i dX_H(γ) ζ` is. -/
theorem isFredholm_floerSobolevOperator_iff_isFredholm_trajectoryOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(𝕁 ∘L fderiv ℝ (ω.hamiltonianVectorField H) (γ s))) :
    (𝔻 H γ).IsFredholm ↔
      (WeakDerivStep.trajectoryOperator (p := 2) A).IsFredholm := by
  -- Explicit types let the instances of the splittings be synthesized rather than unified.
  have hconj : ((zeroModeLpProdEquiv F).symm : Lp F 2 stripMeasure →L[ℝ] _).comp (𝔻 H γ) =
      ((WeakDerivStep.trajectoryOperator (p := 2) A).prodMap
        (nonzeroModes ω H γ)).comp
          ((zeroModeProdEquiv F).symm : H1 F →L[ℝ] _) := by
    conv_lhs => rw [floerSobolevOperator_eq_comp hH hγ haγ hA]
    refine ContinuousLinearMap.ext fun x ↦ ?_
    simp
  rw [isFredholm_iff_of_comp_eq (𝕜 := ℝ) (E := H1 F) (F := Lp F 2 stripMeasure)
      (G := pathSobolev F × nonzeroModeSobolev F) (H := pathLp F × nonzeroModeLp F)
      (zeroModeProdEquiv F).symm (zeroModeLpProdEquiv F).symm hconj,
    isFredholm_prodMap_iff (K := ℝ) (E₁ := pathSobolev F) (E₂ := nonzeroModeSobolev F)
      (F₁ := pathLp F) (F₂ := nonzeroModeLp F)]
  exact and_iff_left (.of_bijective (K := ℝ) (E := nonzeroModeSobolev F) (F := nonzeroModeLp F)
    (bijective_nonzeroModes hω hH hγ ha haγ))

/-- **The index of the linearized operator is the index of the Morse operator.** Under the
hypotheses of
`TauCeti.SymplecticForm.surjective_floerSobolevOperator_iff_surjective_trajectoryOperator`, if the
Morse operator `ζ ↦ ζ' - i dX_H(γ) ζ` is Fredholm, then the Sobolev realization of the linearized
operator along the time-independent cylinder `(s, t) ↦ γ(s)` has the same index. -/
theorem index_floerSobolevOperator_eq_index_trajectoryOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(𝕁 ∘L fderiv ℝ (ω.hamiltonianVectorField H) (γ s)))
    (hM : (WeakDerivStep.trajectoryOperator (p := 2) A).IsFredholm) :
    (𝔻 H γ).index =
      (WeakDerivStep.trajectoryOperator (p := 2) A).index := by
  have hQ := bijective_nonzeroModes hω hH hγ ha haγ
  rw [floerSobolevOperator_eq_comp hH hγ haγ hA,
    index_equiv_comp (𝕜 := ℝ) (E := H1 F) (F := pathLp F × nonzeroModeLp F)
      (G := Lp F 2 stripMeasure),
    index_comp_equiv (𝕜 := ℝ) (E := pathSobolev F × nonzeroModeSobolev F)
      (F := pathLp F × nonzeroModeLp F) (G := H1 F),
    hM.index_prodMap (K := ℝ) (E₁ := pathSobolev F) (E₂ := nonzeroModeSobolev F)
      (F₁ := pathLp F) (F₂ := nonzeroModeLp F)
      (.of_bijective (K := ℝ) (E := nonzeroModeSobolev F) (F := nonzeroModeLp F) hQ),
    index_eq_zero_of_bijective (𝕜 := ℝ) (E := nonzeroModeSobolev F) (F := nonzeroModeLp F) _ hQ,
    add_zero]

end Index

end TauCeti.SymplecticForm
