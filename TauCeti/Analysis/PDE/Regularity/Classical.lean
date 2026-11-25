/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Smooth
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.PDE.EnergyForm.LowerOrder

/-!
# Classical representatives of constant-coefficient weak solutions

A `C²` representative of a weak solution of `-div(A ∇u) = f`, with constant matrix `A` and
continuous `f`, satisfies this equation at every point of the open domain. No boundary condition
or symmetry of `A` is needed. For uniformly elliptic `A`, a weak solution of the homogeneous
equation has a smooth representative whose classical gradient agrees almost everywhere with its
weak gradient. This allows classical interior estimates to be applied to weak solutions of the
frozen coefficient equation.

The operator is the existing `TauCeti.PDE.divMatrixGradient`, with the sign convention
`-divMatrixGradient (fun _ => A) u = f`. The coordinate formula
`divMatrixGradient_eq_sum_fderiv_fderiv_apply` identifies it with the contraction of `A` against the
Hessian, including nonsymmetric matrices.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §6.1 (freezing coefficients) and §8.1 (weak solutions).
-/

public section

open InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped Distributions Gradient InnerProductSpace ContDiff

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {Omega : Opens (EuclideanSpace ℝ ι)}
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {A : Matrix ι ι ℝ} {g f : EuclideanSpace ℝ ι → ℝ}

/-- Green's identity for a `C²` representative of a Sobolev function, tested against a compactly
supported smooth function. No ellipticity, boundary condition, or global Hessian bound is used. -/
theorem energyFormH1_ofTestFunction_eq_neg_setIntegral_divMatrixGradient
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} (hg : ContDiffOn ℝ 2 g Omega)
    (hq : ∀ i, ContDiffOn ℝ 1
      (fun x ↦ matrixBilinearForm (a x) (EuclideanSpace.basisFun ι ℝ i) (∇ g x)) Omega)
    {u : W1p mu Omega 2}
    (hug : W1p.value u =ᵐ[mu.restrict Omega] g) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      -∫ x in Omega, φ x * divMatrixGradient a g x ∂mu := by
  have hgrad := W1p.gradient_ae_eq_of_contDiffOn u (hg.of_le one_le_two) hug
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc
    ∫ x in Omega, matrixBilinearForm (a x)
        (W1p.gradient (W1p.ofTestFunctionₗ mu Omega 2 φ) x) (W1p.gradient u x) ∂mu =
        ∫ x in Omega, matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ ι → ℝ) x) (∇ g x) ∂mu := by
      refine integral_congr_ae ?_
      filter_upwards [hgrad, gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx hφx
      rw [W1p.gradient_ofTestFunctionₗ, hφx, hx]
    _ = ∫ x, matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ ι → ℝ) x) (∇ g x) ∂mu :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        rw [gradient_of_notMem_tsupport (fun h ↦ hx (φ.tsupport_subset h)), map_zero, zero_apply])
    _ = -∫ x, φ x * divMatrixGradient a g x ∂mu :=
      integral_matrixGradient_eq_neg_integral_divMatrixGradient hq φ
    _ = -∫ x in Omega, φ x * divMatrixGradient a g x ∂mu := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ by simp [φ.zero_on_compl hx])]

/-- Green's identity for a `C²` representative of a Sobolev function, tested against a compactly
supported smooth function. No ellipticity, boundary condition, or global Hessian bound is used. -/
theorem energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_divMatrixGradient
    (hg : ContDiffOn ℝ 2 g Omega) {u : W1p mu Omega 2}
    (hug : W1p.value u =ᵐ[mu.restrict Omega] g) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      -∫ x in Omega, φ x * divMatrixGradient (fun _ => A) g x ∂mu := by
  have hg₁ : ContDiffOn ℝ 1 (∇ g) Omega :=
    (toDual ℝ (EuclideanSpace ℝ ι)).symm.contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen Omega.isOpen (by norm_num))
  exact energyFormH1_ofTestFunction_eq_neg_setIntegral_divMatrixGradient hg
    (fun i ↦ (matrixBilinearForm A (EuclideanSpace.basisFun ι ℝ i)).contDiff.comp_contDiffOn hg₁)
    hug φ

/-- A `C²` representative of a weak solution with continuous forcing satisfies
`-div(A ∇g) = f` pointwise. Only compactly supported test functions are required in the weak
formulation, and the matrix need not be elliptic or symmetric. -/
theorem divMatrixGradient_eq_neg_of_forall_energyFormH1_eq
    (hg : ContDiffOn ℝ 2 g Omega) (hf : ContinuousOn f Omega) {u : W1p mu Omega 2}
    (hug : W1p.value u =ᵐ[mu.restrict Omega] g)
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
        ∫ x in Omega, f x * φ x ∂mu) :
    ∀ x ∈ Omega, divMatrixGradient (fun _ => A) g x = -f x := by
  have hD := continuousOn_divMatrixGradient (A := A) hg
  have hDl : LocallyIntegrableOn (divMatrixGradient (fun _ => A) g) Omega mu :=
    hD.locallyIntegrableOn Omega.isOpen.measurableSet
  have hfl : LocallyIntegrableOn f Omega mu := hf.locallyIntegrableOn Omega.isOpen.measurableSet
  have hzero : ∀ᵐ x ∂mu, x ∈ Omega → divMatrixGradient (fun _ => A) g x + f x = 0 := by
    refine Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hDl.add hfl) fun φ hφ hφc hφs => ?_
    let ψ : 𝓓(Omega, ℝ) := ⟨φ, hφ, hφc, hφs⟩
    have he := energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_divMatrixGradient (A := A) hg hug ψ
    rw [hu ψ] at he
    have hfi := ψ.integrable_smul hfl
    have hDi := ψ.integrable_smul hDl
    have hset : ∫ x in Omega, f x * ψ x ∂mu = ∫ x, ψ x * f x ∂mu := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by simp [ψ.zero_on_compl hx])]
      simp only [mul_comm]
    rw [hset, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [ψ.zero_on_compl hx])] at he
    have hψ : (ψ : EuclideanSpace ℝ ι → ℝ) = φ := TestFunction.coe_mk
    simp only [hψ, smul_eq_mul] at hDi hfi he
    simp only [smul_eq_mul, mul_add]
    rw [integral_add hDi hfi]
    linarith
  have hae : (fun x => divMatrixGradient (fun _ => A) g x + f x) =ᵐ[mu.restrict Omega] 0 :=
    (ae_restrict_iff' Omega.isOpen.measurableSet).2 hzero
  have hpoint := Measure.eqOn_open_of_ae_eq hae Omega.isOpen (hD.add hf) continuousOn_const
  intro x hx
  exact eq_neg_iff_add_eq_zero.mpr (hpoint hx)

/-- Every weak solution of a homogeneous, constant, uniformly elliptic equation has a smooth
classical representative. Its classical gradient is the weak gradient almost everywhere.
There is no boundary condition on the solution or regularity assumption on the boundary. -/
theorem UniformlyEllipticOn.exists_contDiffOn_ae_eq_and_divMatrixGradient_eq_zero
    {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => A) 0 0 u (v : W1p volume Omega 2) = 0) :
    ∃ g : EuclideanSpace ℝ ι → ℝ, ContDiffOn ℝ ∞ g Omega ∧
      W1p.value u =ᵐ[volume.restrict Omega] g ∧
      W1p.gradient u =ᵐ[volume.restrict Omega] ∇ g ∧
      ∀ x ∈ Omega, divMatrixGradient (fun _ => A) g x = 0 := by
  have hf : ∀ x ∈ Omega, ∃ V : Opens (EuclideanSpace ℝ ι), x ∈ V ∧
      ∀ k, ∃ F : Wkp volume V 2 k,
        (Wkp.value k F : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict V]
          (0 : EuclideanSpace ℝ ι → ℝ) := by
    intro x hx
    refine ⟨Omega, hx, fun k => ⟨0, ?_⟩⟩
    rw [← Wkp.valueL_apply, map_zero]
    exact Lp.coeFn_zero _ _ _
  obtain ⟨g, hg, hug⟩ := UniformlyEllipticOn.exists_contDiffOn_ae_eq hlam hA (b := 0) (c := 0)
    contDiffOn_const contDiffOn_const hf
    (fun v => by simpa using hu v)
  refine ⟨g, hg, hug, W1p.gradient_ae_eq_of_contDiffOn u (hg.of_le (by simp)) hug, ?_⟩
  have hp := divMatrixGradient_eq_neg_of_forall_energyFormH1_eq
    (hg.of_le (by simp)) (f := 0) continuousOn_const hug fun φ => by
      simpa using hu ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  simpa using hp

variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

/-- Green's identity gives the weak equation against smooth test functions for a `C²` solution
of the full homogeneous divergence equation holding almost everywhere, with essentially bounded
lower-order coefficients. -/
theorem energyFormH1_ofTestFunction_eq_zero_of_divMatrixGradient_eq_lowerOrder
    (hg : ContDiffOn ℝ 2 g Omega)
    (hq : ∀ i, ContDiffOn ℝ 1
      (fun x ↦ matrixBilinearForm (a x) (EuclideanSpace.basisFun ι ℝ i) (∇ g x)) Omega)
    (hA : MemLp (fun x ↦ energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {u : W1p mu Omega 2} (hu : W1p.value u =ᵐ[mu.restrict Omega] g)
    (heq : ∀ᵐ x ∂mu.restrict Omega, divMatrixGradient a g x = ⟪b x, ∇ g x⟫_ℝ + c x * g x)
    (φ : 𝓓(Omega, ℝ)) : energyFormH1 a b c u (W1p.ofTestFunctionₗ mu Omega 2 φ) = 0 := by
  rw [energyFormH1_eq_principal_add_setIntegral hA hb hc,
    energyFormH1_ofTestFunction_eq_neg_setIntegral_divMatrixGradient hg hq hu, neg_add_eq_zero]
  apply integral_congr_ae
  filter_upwards [heq, hu,
    W1p.gradient_ae_eq_of_contDiffOn u (hg.of_le one_le_two) hu,
    W1p.value_ofTestFunctionₗ_ae (mu := mu) (p := 2) φ] with x hx hux hgrad hφ
  rw [hx, hux, hgrad, hφ, mul_comm]

end TauCeti.PDE
