/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.WeightCrossing
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Index
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Hamiltonian.Basic

/-!
# The weighted linearized operator along a time-independent cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space with a compatible complex structure
`J`, let `H : V → ℝ` be an autonomous Hamiltonian and `γ` a curve, and let `D` be the linearized
Floer operator along the time-independent cylinder `(s, t) ↦ γ(s)`,
`D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)`. On the Sobolev spaces with the exponential weight
`e^{δ s}` of constant slope `δ`, `D` acts as the operator `D - δ`
(`TauCeti.SymplecticForm.floerWeightedSobolevOperator` with the slope `fun _ ↦ δ`). This file
computes its index. All declarations below are in the namespace `TauCeti.SymplecticForm`.

* **A constant slope is a quadratic Hamiltonian.** For `Q(y) = (δ / 2) ‖y‖²`, where the inner
  product is the metric `ω(·, J ·)`, the Hamiltonian vector field is `X_Q = -δ J`, so
  `-J dX_{H + Q} = -J dX_H - δ`
  (`neg_comp_fderiv_hamiltonianVectorField_add_div_two_mul_norm_sq`). Hence `D - δ` is the
  linearized operator of the Hamiltonian `H + Q` along the same cylinder
  (`floerWeightedSobolevOperator_eq_floerSobolevOperator_add_div_two_mul_norm_sq`). The curve `γ`
  need not be a solution for either Hamiltonian.
* **Fredholm property and index.** In a unitary trivialization, where `V = F` is a complex inner
  product space with `ω = Im ⟪·, ·⟫` and `J = i`, the linearized operator of an autonomous
  Hamiltonian along `(s, t) ↦ γ(s)` with `‖dX(γ(s))‖ < 2π` has the index of its zero-mode Morse
  operator (`index_floerSobolevOperator_eq_index_trajectoryOperator`). For `H + Q` this operator
  is the trajectory operator of `A - δ` with `A(s) = -i dX_H(γ(s))`, the trajectory operator on
  the spaces of weight `e^{δ s}`. Suppose `γ` converges to `p±` at `±∞` and
  `‖dX_H(γ(s))‖ + |δ| < 2π`. If `δ` is not an eigenvalue of the asymptotic operators
  `A(p±) = -i dX_H(p±)`, the negatives of the Hessians of `H` at `p±`, then `D - δ` is Fredholm
  (`isFredholm_floerWeightedSobolevOperator_comp_fst`) of index
  `n_{< δ}(A(p₋)) - n_{< δ}(A(p₊))`, where `n_{< δ}(B)` is the number of eigenvalues of `B` below
  `δ`, counted with multiplicity
  (`index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank`). The points
  `p±` need not be nondegenerate critical points: `A(p±)` has finitely many eigenvalues, so every
  small nonzero weight `δ` is non-exceptional even where `A(p±)` has a kernel.
* **Crossing an eigenvalue.** Hence the index depends on `δ` only through its position relative
  to the two spectra, and as `δ` increases from `δ₁` to `δ₂` the index decreases by the number of
  eigenvalues of `A(p₊)` in `[δ₁, δ₂)` and increases by the number of eigenvalues of `A(p₋)` there
  (`index_floerWeightedSobolevOperator_eq_add_finrank_pointSpectralSubspace_Ico`). The weight
  `e^{δ s}` is a decay weight at `+∞` and a growth weight at `-∞` when `δ > 0`: as `δ` increases
  through one exceptional value of `A(p₊)` alone, the index decreases by the dimension of its
  eigenspace (`index_floerWeightedSobolevOperator_eq_add_finrank_eigenspace_atTop`), and through
  one exceptional value of `A(p₋)` alone it increases by that dimension
  (`index_floerWeightedSobolevOperator_eq_add_finrank_eigenspace_atBot`).

These are the statements of `TauCeti.Analysis.ODE.EnergyEstimate.WeightCrossing` for the trajectory
operator, carried to the Floer operator by the zero mode.

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) **12** (1985), 409–447 (the index on weighted spaces
  is locally constant in the weight and jumps at the exceptional weights by the dimension of the
  crossed asymptotic eigenspace).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the linearized operator at
  time-independent solutions of a small Hamiltonian.
-/

public section

noncomputable section

open Real Set Filter Topology MeasureTheory ContinuousLinearMap
open TauCeti.CylinderSobolev
open scoped RealInnerProductSpace ENNReal

namespace TauCeti.SymplecticForm

section Quadratic

/-! ### A constant weight slope as a quadratic Hamiltonian -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ}

/-- **A constant weight slope is a quadratic Hamiltonian, on coefficients.** If the inner product
of `V` is the metric `ω(·, J ·)`, then for the constant structure `J`, the perturbation `K = H dt`
of an autonomous Hamiltonian and any map `u`, the coefficient field of `D_u - δ` on jets at `z` is
that of the linearized operator of the Hamiltonian `H + (δ / 2) ‖·‖²`, as soon as `X_H` is
differentiable at `u z`. -/
theorem floerJetCoeff_add_div_two_mul_norm_sq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : Differentiable ℝ H) {u : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hX : DifferentiableAt ℝ (ω.hamiltonianVectorField H) (u z)) (δ : ℝ) :
    ω.floerJetCoeff (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ x ↦ H x + δ / 2 * ‖x‖ ^ 2) u z =
      ω.floerJetCoeff (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ ↦ H) u z - δ • fst ℝ V (V × V) := by
  rw [floerJetCoeff_const_eq, floerJetCoeff_const_eq,
    neg_comp_fderiv_hamiltonianVectorField_add_div_two_mul_norm_sq hg hH hX δ]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [sub_eq_add_neg, add_assoc]

/-- **A constant weight slope is a quadratic Hamiltonian.** If the inner product of `V` is the
metric `ω(·, J ·)`, and `H` and its Hamiltonian vector field are differentiable, the linearized
Floer operator of the data `(J, 0, H dt)` along any map `u`, conjugated by the exponential weight
`e^{δ s}` of constant slope `δ`, is the linearized operator of the Hamiltonian
`H + (δ / 2) ‖·‖²` along `u`, on `W^{1,2}(ℝ × S¹, V)`. -/
theorem floerWeightedSobolevOperator_eq_floerSobolevOperator_add_div_two_mul_norm_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : Differentiable ℝ H)
    (hX : Differentiable ℝ (ω.hamiltonianVectorField H)) (u : ℝ × ℝ → V) (δ : ℝ) :
    ω.floerWeightedSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ ↦ H) u (fun _ ↦ δ) =
      ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ x ↦ H x + δ / 2 * ‖x‖ ^ 2) u := by
  have hcoeff : (fun z ↦ ω.floerJetCoeff (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ ↦ H) u z - (fun _ ↦ δ) z.1 • fst ℝ V (V × V)) =
      ω.floerJetCoeff (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ x ↦ H x + δ / 2 * ‖x‖ ^ 2) u := by
    funext z
    exact (floerJetCoeff_add_div_two_mul_norm_sq hg hH (hX _) δ).symm
  rw [floerWeightedSobolevOperator_def, floerSobolevOperator_def, hcoeff]

end Quadratic

section Unitary

/-! ### The index in a unitary trivialization -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {ω : SymplecticForm F} {H : F → ℝ} {γ : ℝ → F}

/-- At every point, `-i dX_H(p)` is symmetric for the real inner product `Re ⟪·, ·⟫`: it is the
negative of the Hessian of `H` at `p`. -/
private theorem isSymmetric_neg_comp_fderiv_hamiltonianVectorField
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (p : F) :
    let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
      (fderiv ℝ (ω.hamiltonianVectorField H) p)) : F →L[ℝ] F) : F →ₗ[ℝ] F).IsSymmetric := by
  intro _ u v
  have hg := ω.apply_ofComplexModule_eq_inner hω
  have h := (ω.invariant_of_apply_apply_eq_inner
    hg).associatedBilinForm_apply_fderiv_hamiltonianVectorField_comm (hH.contDiffAt (x := p)) u v
  rw [associatedBilinForm_apply, associatedBilinForm_apply, hg, hg] at h
  simpa [inner_neg_left, inner_neg_right] using h

/-- The coefficient `y ↦ -i dX_H(y)` of the Morse operator of a `C²` Hamiltonian is continuous. -/
private theorem continuous_neg_comp_fderiv_hamiltonianVectorField (hH : ContDiff ℝ 2 H) :
    Continuous fun y ↦
      -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) y)) :=
  (continuous_const.clm_comp
    ((ω.contDiff_hamiltonianVectorField (n := 1) hH).continuous_fderiv one_ne_zero)).neg

/-- The reduction of the weighted operator to a trajectory operator. Under the hypotheses of
`index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank`, there is an
`L∞` class `B` of the coefficient `s ↦ A(s) - δ` with `A(s) = -i dX_H(γ(s))`, such that the
weighted operator `D - δ` is Fredholm exactly when the trajectory operator of `B` is, and has the
same index. -/
private theorem exists_trajectoryOperator_floerWeightedSobolevOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a δ : ℝ}
    (ha : a + |δ| < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) :
    ∃ B : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)),
      B =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
        (fun s ↦ -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
          (fderiv ℝ (ω.hamiltonianVectorField H) (γ s))) - δ • ContinuousLinearMap.id ℝ F) ∧
      ((ω.floerWeightedSobolevOperator
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ).IsFredholm ↔
        (WeakDerivStep.trajectoryOperator (p := 2) B).IsFredholm) ∧
      (ω.floerWeightedSobolevOperator
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ).index =
        (WeakDerivStep.trajectoryOperator (p := 2) B).index := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hg := ω.apply_ofComplexModule_eq_inner hω
  set Jc := (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
  have hH₁ : Differentiable ℝ H := hH.differentiable two_ne_zero
  have hX : Differentiable ℝ (ω.hamiltonianVectorField H) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) hH).differentiable one_ne_zero
  -- The shifted Hamiltonian `H + (δ / 2) ‖·‖²` is `C²`, with `‖dX(γ(s))‖ ≤ a + |δ| < 2π`.
  have hH' : ContDiff ℝ 2 fun x : F ↦ H x + δ / 2 * ‖x‖ ^ 2 :=
    hH.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  have haγ' (s : ℝ) :
      ‖fderiv ℝ (ω.hamiltonianVectorField fun x ↦ H x + δ / 2 * ‖x‖ ^ 2) (γ s)‖ ≤ a + |δ| :=
    (norm_fderiv_hamiltonianVectorField_add_div_two_mul_norm_sq_le hg hH₁ (hX _) δ).trans
      (add_le_add_left (haγ s) _)
  -- The coefficient `s ↦ -i dX_H(γ(s)) - δ` is continuous and bounded.
  have hAc := continuous_neg_comp_fderiv_hamiltonianVectorField (ω := ω) hH
  have hBL : MemLp (fun s ↦ -(Jc.comp (fderiv ℝ (ω.hamiltonianVectorField H) (γ s))) -
      δ • ContinuousLinearMap.id ℝ F) ∞
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)) := by
    refine memLp_top_of_bound ((hAc.comp hγ).sub continuous_const).aestronglyMeasurable
      (‖Jc‖ * a + ‖δ • ContinuousLinearMap.id ℝ F‖) (.of_forall fun s ↦ ?_)
    refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
    rw [norm_neg]
    exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (haγ s) (norm_nonneg _))
  -- It is `-i dX_{H + Q}(γ(s))`, the coefficient of the Morse operator of the shifted Hamiltonian.
  have hB : ⇑(hBL.toLp _) =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(Jc.comp
        (fderiv ℝ (ω.hamiltonianVectorField fun x ↦ H x + δ / 2 * ‖x‖ ^ 2) (γ s))) := by
    filter_upwards [hBL.coeFn_toLp] with s hs
    rw [hs, neg_comp_fderiv_hamiltonianVectorField_add_div_two_mul_norm_sq hg hH₁ (hX _) δ]
  have hW := floerWeightedSobolevOperator_eq_floerSobolevOperator_add_div_two_mul_norm_sq hg hH₁ hX
    (fun z ↦ γ z.1) δ
  refine ⟨hBL.toLp _, hBL.coeFn_toLp, ?_, ?_⟩
  · rw [hW]
    exact isFredholm_floerSobolevOperator_iff_isFredholm_trajectoryOperator hω hH' hγ ha haγ' hB
  · rw [hW]
    exact index_floerSobolevOperator_eq_index_trajectoryOperator hω hH' hγ ha haγ' hB

/-- **The weighted operator along a gradient line is Fredholm.** Let `F` be a finite-dimensional
complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H` be a `C²` autonomous
Hamiltonian and `γ` a continuous curve with `‖dX_H(γ(s))‖ ≤ a` for every `s`, converging to `p₋` at
`-∞` and to `p₊` at `+∞`, and let `δ` be a weight slope with `a + |δ| < 2π` which is an eigenvalue
neither of `-i dX_H(p₋)` nor of `-i dX_H(p₊)`. Then the linearized operator along `(s, t) ↦ γ(s)`
on the spaces of weight `e^{δ s}`, the operator `D - δ : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)`, is
Fredholm. -/
theorem isFredholm_floerWeightedSobolevOperator_comp_fst
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a δ : ℝ}
    (ha : a + |δ| < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    {pminus pplus : F} (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    (hδminus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ)
    (hδplus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ) :
    (ω.floerWeightedSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ).IsFredholm := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨B, hB, hF, -⟩ := exists_trajectoryOperator_floerWeightedSobolevOperator hω hH hγ ha haγ
  have hAc := continuous_neg_comp_fderiv_hamiltonianVectorField (ω := ω) hH
  exact hF.2 (WeakDerivStep.isFredholm_trajectoryOperator_sub_smul_id (hAc.comp hγ)
    (isSymmetric_neg_comp_fderiv_hamiltonianVectorField hω hH pminus)
    (isSymmetric_neg_comp_fderiv_hamiltonianVectorField hω hH pplus)
    ((hAc.tendsto pminus).comp hbot) ((hAc.tendsto pplus).comp htop) continuous_const
    tendsto_const_nhds tendsto_const_nhds hδminus hδplus B hB)

open WeakDerivStep in
/-- **The index of the weighted operator along a gradient line.** Let `F` be a finite-dimensional
complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H` be a `C²` autonomous
Hamiltonian and `γ` a continuous curve with `‖dX_H(γ(s))‖ ≤ a` for every `s`, converging to `p₋` at
`-∞` and to `p₊` at `+∞`, and let `δ` be a weight slope with `a + |δ| < 2π` which is an eigenvalue
neither of `A(p₋)` nor of `A(p₊)`, where `A(p) = -i dX_H(p)` is the negative of the Hessian of `H`
at `p`. Then the linearized operator along `(s, t) ↦ γ(s)` on the spaces of weight `e^{δ s}`, the
operator `D - δ : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)`, has index `n_{< δ}(A(p₋)) - n_{< δ}(A(p₊))`,
where `n_{< δ}(B)` is the number of eigenvalues of `B` below `δ`, counted with multiplicity. -/
theorem index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a δ : ℝ}
    (ha : a + |δ| < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    {pminus pplus : F} (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    (hδminus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ)
    (hδplus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ) :
    (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace
        ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
          (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) (Iio δ)) :
            ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) (Iio δ)) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  obtain ⟨B, hB, -, hI⟩ := exists_trajectoryOperator_floerWeightedSobolevOperator hω hH hγ ha haγ
  have hAc := continuous_neg_comp_fderiv_hamiltonianVectorField (ω := ω) hH
  rw [hI]
  exact index_trajectoryOperator_sub_smul_id_eq_finrank_pointSpectralSubspace_sub_finrank
    (hAc.comp hγ) (isSymmetric_neg_comp_fderiv_hamiltonianVectorField hω hH pminus)
    (isSymmetric_neg_comp_fderiv_hamiltonianVectorField hω hH pplus)
    ((hAc.tendsto pminus).comp hbot) ((hAc.tendsto pplus).comp htop) continuous_const
    tendsto_const_nhds tendsto_const_nhds hδminus hδplus B hB

/-- **The index jumps by the eigenvalues crossed by the weight.** Under the hypotheses of
`index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank` for two weight
slopes `δ₁ ≤ δ₂`, the index of `D - δ₁` is the index of `D - δ₂`, plus the number of eigenvalues
of `A(p₊) = -i dX_H(p₊)` in `[δ₁, δ₂)`, minus the number of eigenvalues of `A(p₋)` in `[δ₁, δ₂)`,
counted with multiplicity. -/
theorem index_floerWeightedSobolevOperator_eq_add_finrank_pointSpectralSubspace_Ico
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ)
    {a δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) (ha₁ : a + |δ₁| < 2 * π) (ha₂ : a + |δ₂| < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    {pminus pplus : F} (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    (hδ₁minus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₁)
    (hδ₁plus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₁)
    (hδ₂minus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₂)
    (hδ₂plus : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₂) :
    (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ₁).index =
      (ω.floerWeightedSobolevOperator
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ₂).index +
        Module.finrank ℝ (Module.End.pointSpectralSubspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F)
              (Ico δ₁ δ₂)) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F)
              (Ico δ₁ δ₂)) := by
  rw [index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank hω hH hγ ha₁
      haγ hbot htop hδ₁minus hδ₁plus,
    index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank hω hH hγ ha₂
      haγ hbot htop hδ₂minus hδ₂plus]
  simp only [Module.End.finrank_pointSpectralSubspace_Iio_eq_add hδ]
  push_cast
  ring

/-- **Crossing one exceptional value of the limit at `+∞`.** Under the hypotheses of
`index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank` for two weight
slopes `δ₁ < δ₂`, suppose that `ν ∈ (δ₁, δ₂)` is the only eigenvalue of `A(p₊) = -i dX_H(p₊)` in
`[δ₁, δ₂]`, and that `A(p₋)` has no eigenvalue in `[δ₁, δ₂]`. Then the index of `D - δ₁` exceeds
that of `D - δ₂` by the multiplicity of `ν`: as the weight `e^{δ s}`, a decay weight at `+∞`,
increases through `ν`, the index decreases by the dimension of the eigenspace of `A(p₊)` at
`ν`. -/
theorem index_floerWeightedSobolevOperator_eq_add_finrank_eigenspace_atTop
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ)
    {a δ₁ δ₂ ν : ℝ} (hν : ν ∈ Ioo δ₁ δ₂) (ha₁ : a + |δ₁| < 2 * π) (ha₂ : a + |δ₂| < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    {pminus pplus : F} (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    (hminus : ∀ μ ∈ Icc δ₁ δ₂, ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) μ)
    (hδ₁ : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₁)
    (hδ₂ : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₂)
    (hother : ∀ μ ∈ Ioo δ₁ δ₂, μ ≠ ν → ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) μ) :
    (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ₁).index =
      (ω.floerWeightedSobolevOperator
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ₂).index +
        Module.finrank ℝ (Module.End.eigenspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) ν) := by
  have hle : δ₁ ≤ δ₂ := (hν.1.trans hν.2).le
  rw [index_floerWeightedSobolevOperator_eq_add_finrank_pointSpectralSubspace_Ico hω hH hγ hle ha₁
      ha₂ haγ hbot htop (hminus δ₁ (left_mem_Icc.2 hle)) hδ₁ (hminus δ₂ (right_mem_Icc.2 hle)) hδ₂,
    Module.End.pointSpectralSubspace_eq_bot_iff.2 fun μ hμ ↦ hminus μ (Ico_subset_Icc_self hμ),
    finrank_bot, Nat.cast_zero, sub_zero,
    Module.End.pointSpectralSubspace_Ico_eq_eigenspace (𝕜 := ℝ) (Ioo_subset_Ico_self hν) hδ₁
      hother,
    RCLike.ofReal_real_eq_id, id_eq]

/-- **Crossing one exceptional value of the limit at `-∞`.** Under the hypotheses of
`index_floerWeightedSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank` for two weight
slopes `δ₁ < δ₂`, suppose that `ν ∈ (δ₁, δ₂)` is the only eigenvalue of `A(p₋) = -i dX_H(p₋)` in
`[δ₁, δ₂]`, and that `A(p₊)` has no eigenvalue in `[δ₁, δ₂]`. Then the index of `D - δ₂` exceeds
that of `D - δ₁` by the multiplicity of `ν`: as the weight `e^{δ s}`, a growth weight at `-∞`
when `δ > 0`, increases through `ν`, the index increases by the dimension of the eigenspace of
`A(p₋)` at `ν`. -/
theorem index_floerWeightedSobolevOperator_eq_add_finrank_eigenspace_atBot
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ)
    {a δ₁ δ₂ ν : ℝ} (hν : ν ∈ Ioo δ₁ δ₂) (ha₁ : a + |δ₁| < 2 * π) (ha₂ : a + |δ₂| < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    {pminus pplus : F} (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    (hplus : ∀ μ ∈ Icc δ₁ δ₂, ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) μ)
    (hδ₁ : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₁)
    (hδ₂ : ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) δ₂)
    (hother : ∀ μ ∈ Ioo δ₁ δ₂, μ ≠ ν → ¬Module.End.HasEigenvalue
      ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) μ) :
    (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ₂).index =
      (ω.floerWeightedSobolevOperator
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) fun _ ↦ δ₁).index +
        Module.finrank ℝ (Module.End.eigenspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField H) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) ν) := by
  have hle : δ₁ ≤ δ₂ := (hν.1.trans hν.2).le
  rw [index_floerWeightedSobolevOperator_eq_add_finrank_pointSpectralSubspace_Ico hω hH hγ hle ha₁
      ha₂ haγ hbot htop hδ₁ (hplus δ₁ (left_mem_Icc.2 hle)) hδ₂ (hplus δ₂ (right_mem_Icc.2 hle)),
    Module.End.pointSpectralSubspace_eq_bot_iff.2 fun μ hμ ↦ hplus μ (Ico_subset_Icc_self hμ),
    finrank_bot, Nat.cast_zero, add_zero,
    Module.End.pointSpectralSubspace_Ico_eq_eigenspace (𝕜 := ℝ) (Ioo_subset_Ico_self hν) hδ₁
      hother,
    RCLike.ofReal_real_eq_id, id_eq]
  ring

end Unitary

end TauCeti.SymplecticForm
