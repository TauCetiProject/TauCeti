/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.CanonicalLine
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# The flat four-dimensional Seiberg–Witten operators and their linearization

On an oriented four-dimensional real inner product space `V` with Clifford module `W = W⁺ ⊕ W⁻`
and compatible almost complex structure `J`, this file defines the flat chiral Dirac operator
`flatDirac` (`D_b χ = ∑ₖ c(eₖ) ∇_{b, eₖ} χ`) built from `spinorCovariantDeriv`, the unit-symbol
self-dual curvature defect `flatCurvatureDefect`, their pointwise directional linearizations (first
variations) `linearizedFlatCurvature` and `linearizedFlatDirac` (`hasDerivAt_flatCurvatureDefect`,
`hasDerivAt_flatDirac`), the formal infinitesimal gauge-fixing adjoint `flatGaugeAdjoint`
(`mul_flatGaugeAdjoint_eq`), and the combined eight-real-component linearized gauge-fixed operator
`gaugeFixedFlatOperator`, together with orthonormal-frame independence and linearity properties.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open CliffordAlgebra Complex Module exteriorPower
open scoped RealInnerProductSpace InnerProductSpace

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

attribute [local instance] finiteDimensional_of_finrank_four

omit [FiniteDimensional ℂ W] in
/-- **Covariant derivative of a positive half-spinor field** `∇_a χ = dχ + i b χ` for `a = i b`. -/
def spinorCovariantDeriv (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    V →L[ℝ] positiveHalfSpinors o ρ :=
  fderiv ℝ χ p +
    ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (b p)).smulRight (I • χ p)

omit [FiniteDimensional ℂ W] in
/-- Pointwise directional evaluation of `spinorCovariantDeriv`. -/
@[simp] theorem spinorCovariantDeriv_apply (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (p v : V) :
    spinorCovariantDeriv b χ p v = fderiv ℝ χ p v + b p (fun _ ↦ v) • (I • χ p) := by
  simp [spinorCovariantDeriv, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply]

omit [FiniteDimensional ℂ W] in
/-- `spinorCovariantDeriv` is additive in the spinor field at a point of differentiability. -/
theorem spinorCovariantDeriv_add (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    {χ₁ χ₂ : V → positiveHalfSpinors o ρ} {p : V}
    (h₁ : DifferentiableAt ℝ χ₁ p) (h₂ : DifferentiableAt ℝ χ₂ p) :
    spinorCovariantDeriv b (χ₁ + χ₂) p =
      spinorCovariantDeriv b χ₁ p + spinorCovariantDeriv b χ₂ p :=
  ContinuousLinearMap.ext fun v ↦ by simp [fderiv_add h₁ h₂, smul_add]; abel

omit [FiniteDimensional ℂ W] in
/-- `spinorCovariantDeriv` is `ℂ`-homogeneous in the spinor field for constant complex scalars. -/
theorem spinorCovariantDeriv_smul (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (c : ℂ)
    (χ : V → positiveHalfSpinors o ρ) (p : V) :
    spinorCovariantDeriv b (c • χ) p = c • spinorCovariantDeriv b χ p :=
  ContinuousLinearMap.ext fun v ↦ by
    simp only [smul_apply, spinorCovariantDeriv_apply, fderiv_const_smul_field, Pi.smul_apply,
      ← Complex.coe_smul]; module

omit [FiniteDimensional ℂ W] in
/-- `spinorCovariantDeriv` sends the zero spinor field to zero. -/
@[simp] theorem spinorCovariantDeriv_zero (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (p : V) :
    spinorCovariantDeriv b (0 : V → positiveHalfSpinors o ρ) p = 0 :=
  ContinuousLinearMap.ext fun v ↦ by simp [spinorCovariantDeriv_apply]

omit [FiniteDimensional ℂ W] in
/-- Along a constant spinor direction `ψ₀`, `spinorCovariantDeriv` acts via `covariantDeriv b`. -/
theorem spinorCovariantDeriv_smul_const (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) {α : V → ℂ} {p : V}
    (hα : DifferentiableAt ℝ α p) (ψ₀ : positiveHalfSpinors o ρ) (v : V) :
    spinorCovariantDeriv b (fun q ↦ α q • ψ₀) p v = covariantDeriv b α p v • ψ₀ := by
  rw [spinorCovariantDeriv_apply, fderiv_smul_const hα ψ₀, ContinuousLinearMap.smulRight_apply,
    covariantDeriv_apply, add_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  congr 2; simp only [Complex.real_smul]; ring

omit [FiniteDimensional ℂ W] in variable (o ρ e) in
/-- **The flat chiral Dirac operator** `D_b χ = ∑ₖ c(eₖ) ∇_{b, eₖ} χ : W⁺ → W⁻`. -/
def flatDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  ∑ k, halfSpinCliffordMul o ρ 1 (e k)
    (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
      (spinorCovariantDeriv b χ p (e k)))

omit [FiniteDimensional ℂ W] in
/-- Ambient Clifford-module expression for `flatDirac`. -/
@[simp] theorem coe_flatDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (p : V) :
    (flatDirac o ρ e b χ p : W) = ∑ k, ρ (ι Q (e k)) (spinorCovariantDeriv b χ p (e k)) := by
  simp [flatDirac]

omit [FiniteDimensional ℂ W] in
/-- `flatDirac` is independent of the choice of orthonormal basis of `V`. -/
theorem flatDirac_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatDirac o ρ e b χ p = flatDirac o ρ e' b χ p :=
  e.sum_apply_self_eq e' <|
    ((LinearMap.restrictScalarsₗ ℝ ℂ _ _ ℝ).comp (halfSpinCliffordMul o ρ 1)).compl₂
      (((LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)).toLinearMap.restrictScalars
        ℝ).comp (spinorCovariantDeriv b χ p).toLinearMap)

omit [FiniteDimensional ℂ W] in
/-- `flatDirac` is additive in the spinor field at a point of differentiability. -/
theorem flatDirac_add (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) {χ₁ χ₂ : V → positiveHalfSpinors o ρ} {p : V}
    (h₁ : DifferentiableAt ℝ χ₁ p) (h₂ : DifferentiableAt ℝ χ₂ p) :
    flatDirac o ρ e b (χ₁ + χ₂) p = flatDirac o ρ e b χ₁ p + flatDirac o ρ e b χ₂ p := by
  simp [flatDirac, spinorCovariantDeriv_add b h₁ h₂, Finset.sum_add_distrib]

omit [FiniteDimensional ℂ W] in
/-- `flatDirac` is `ℂ`-homogeneous in the spinor field for constant complex scalars. -/
theorem flatDirac_smul (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (c : ℂ)
    (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatDirac o ρ e b (c • χ) p = c • flatDirac o ρ e b χ p := by
  simp [flatDirac, spinorCovariantDeriv_smul, Finset.smul_sum]

omit [FiniteDimensional ℂ W] in
/-- `flatDirac` sends the zero spinor field to zero. -/
@[simp] theorem flatDirac_zero (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (p : V) :
    flatDirac o ρ e b 0 p = 0 := by
  simp [flatDirac]

omit [FiniteDimensional ℂ W] in
/-- Action of `flatDirac` on a scalar multiple `α • ψ₀` of a constant positive half-spinor. -/
theorem coe_flatDirac_smul_const (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) {α : V → ℂ} {p : V}
    (hα : DifferentiableAt ℝ α p) (ψ₀ : positiveHalfSpinors o ρ) :
    (flatDirac o ρ e b (fun q ↦ α q • ψ₀) p : W) =
      ∑ k, covariantDeriv b α p (e k) • ρ (ι Q (e k)) ψ₀ := by
  simp [spinorCovariantDeriv_smul_const b hα]

variable (o ρ J) in
/-- **Self-dual curvature defect** `(√2 / 2) (F + ⋆F - ω / 8 + q(χ) / 2) ∈ Λ⁺ V`, `F = -db`. -/
def flatCurvatureDefect (hkl : 2 + 2 = finrank ℝ V)
    (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  (√2 : ℝ) • o.selfDualProj even_two hkl ((alternatingFormEquiv V 2).symm (-extDeriv b p)) -
    (8⁻¹ : ℝ) • J.kahlerSelfDual o hkl hω + (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p)

/-- Unfolding formula for `flatCurvatureDefect`. -/
theorem flatCurvatureDefect_apply (hkl : 2 + 2 = finrank ℝ V)
    (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatCurvatureDefect o ρ J hkl hω b χ p =
      (√2 : ℝ) • o.selfDualProj even_two hkl ((alternatingFormEquiv V 2).symm (-extDeriv b p)) -
        (8⁻¹ : ℝ) • J.kahlerSelfDual o hkl hω +
        (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p) :=
  (rfl)

/-- `flatCurvatureDefect` vanishes iff `F + ⋆F = ω / 8 - q(χ) / 2` for `F = -db`. -/
theorem flatCurvatureDefect_eq_zero_iff (hkl : 2 + 2 = finrank ℝ V)
    (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatCurvatureDefect o ρ J hkl hω b χ p = 0 ↔
      let F := (alternatingFormEquiv V 2).symm (-extDeriv b p)
      F + o.hodgeStar hkl F =
        (8⁻¹ : ℝ) • J.kahlerForm - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (χ p) : ⋀[ℝ]^2 V) := by
  set F := (alternatingFormEquiv V 2).symm (-extDeriv b p)
  have hcoe : (flatCurvatureDefect o ρ J hkl hω b χ p : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • ((F + o.hodgeStar hkl F) - ((8⁻¹ : ℝ) • J.kahlerForm -
        (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (χ p) : ⋀[ℝ]^2 V))) := by
    simp only [flatCurvatureDefect, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Orientation.coe_selfDualProj_apply, AlmostComplexStructure.coe_kahlerSelfDual, F]
    module
  rw [← Submodule.coe_eq_zero, hcoe, smul_eq_zero_iff_right (by positivity), sub_eq_zero]

variable (o ρ) in
/-- **Linearized self-dual curvature operator** `(√2 / 2) (δF + ⋆δF) + (√2 / 4) q'(χ, ζ)`. -/
def linearizedFlatCurvature (hkl : 2 + 2 = finrank ℝ V) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  (√2 : ℝ) • o.selfDualProj even_two hkl ((alternatingFormEquiv V 2).symm (-extDeriv δb p)) +
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (χ p) (ζ p)

/-- Unfolding formula for `linearizedFlatCurvature`. -/
theorem linearizedFlatCurvature_apply (hkl : 2 + 2 = finrank ℝ V)
    (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatCurvature o ρ hkl χ δb ζ p =
      (√2 : ℝ) • o.selfDualProj even_two hkl ((alternatingFormEquiv V 2).symm (-extDeriv δb p)) +
        (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (χ p) (ζ p) :=
  (rfl)

/-- `linearizedFlatCurvature` is additive in the perturbation `(δb, ζ)` at a point of
differentiability of the connection perturbations. -/
theorem linearizedFlatCurvature_add (hkl : 2 + 2 = finrank ℝ V) (χ : V → positiveHalfSpinors o ρ)
    {δb₁ δb₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ} (ζ₁ ζ₂ : V → positiveHalfSpinors o ρ) {p : V}
    (h₁ : DifferentiableAt ℝ δb₁ p) (h₂ : DifferentiableAt ℝ δb₂ p) :
    linearizedFlatCurvature o ρ hkl χ (δb₁ + δb₂) (ζ₁ + ζ₂) p =
      linearizedFlatCurvature o ρ hkl χ δb₁ ζ₁ p +
        linearizedFlatCurvature o ρ hkl χ δb₂ ζ₂ p := by
  simp only [linearizedFlatCurvature_apply, Pi.add_apply, extDeriv_add h₁ h₂, neg_add, map_add,
    smul_add]
  abel

/-- `linearizedFlatCurvature` commutes with real scalar multiplication of `(δb, ζ)`. -/
theorem linearizedFlatCurvature_smul (hkl : 2 + 2 = finrank ℝ V) (χ : V → positiveHalfSpinors o ρ)
    (r : ℝ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatCurvature o ρ hkl χ (r • δb) (r • ζ) p =
      r • linearizedFlatCurvature o ρ hkl χ δb ζ p := by
  simp only [linearizedFlatCurvature_apply, Pi.smul_apply, extDeriv_smul, ← smul_neg, map_smul,
    smul_add]
  rw [smul_comm (√2 : ℝ) r, smul_comm (√2 / 4 : ℝ) r]

/-- `linearizedFlatCurvature` sends the zero perturbation to zero. -/
@[simp] theorem linearizedFlatCurvature_zero (hkl : 2 + 2 = finrank ℝ V)
    (χ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatCurvature o ρ hkl χ 0 0 p = 0 := by
  simpa using linearizedFlatCurvature_smul hkl χ 0 0 0 p

omit [FiniteDimensional ℂ W] in variable (o ρ e) in
/-- **Linearized chiral Dirac operator** `D_b ζ + ∑ₖ c(eₖ) (i δb(eₖ) χ)`. -/
def linearizedFlatDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  flatDirac o ρ e b ζ p + ∑ k, halfSpinCliffordMul o ρ 1 (e k)
    (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
      (δb p (fun _ ↦ e k) • (I • χ p)))

omit [FiniteDimensional ℂ W] in
/-- Unfolding formula for `linearizedFlatDirac`. -/
theorem linearizedFlatDirac_apply (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatDirac o ρ e b χ δb ζ p =
      flatDirac o ρ e b ζ p + ∑ k, halfSpinCliffordMul o ρ 1 (e k)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
          (δb p (fun _ ↦ e k) • (I • χ p))) :=
  (rfl)

omit [FiniteDimensional ℂ W] in
/-- `linearizedFlatDirac` is independent of the choice of orthonormal basis of `V`. -/
theorem linearizedFlatDirac_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatDirac o ρ e b χ δb ζ p = linearizedFlatDirac o ρ e' b χ δb ζ p := by
  let T := (((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (δb p)).smulRight
    (I • χ p)).toLinearMap
  let B := ((LinearMap.restrictScalarsₗ ℝ ℂ _ _ ℝ).comp (halfSpinCliffordMul o ρ 1)).compl₂
    (((LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)).toLinearMap.restrictScalars
      ℝ).comp T)
  exact congrArg₂ (· + ·) (flatDirac_congr_orthonormalBasis e' b ζ p) <| by
    simpa [B, T, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply] using
      e.sum_apply_self_eq e' B

omit [FiniteDimensional ℂ W] in
/-- `linearizedFlatDirac` is additive in the perturbation `(δb, ζ)` at a point of
differentiability of the spinor perturbations. -/
theorem linearizedFlatDirac_add (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb₁ δb₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ) {ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} {p : V}
    (h₁ : DifferentiableAt ℝ ζ₁ p) (h₂ : DifferentiableAt ℝ ζ₂ p) :
    linearizedFlatDirac o ρ e b χ (δb₁ + δb₂) (ζ₁ + ζ₂) p =
      linearizedFlatDirac o ρ e b χ δb₁ ζ₁ p + linearizedFlatDirac o ρ e b χ δb₂ ζ₂ p := by
  simp only [linearizedFlatDirac_apply, flatDirac_add b h₁ h₂, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, add_smul, map_add, Finset.sum_add_distrib]
  abel

omit [FiniteDimensional ℂ W] in
/-- `linearizedFlatDirac` commutes with real scalar multiplication of `(δb, ζ)`. -/
theorem linearizedFlatDirac_smul (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (r : ℝ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatDirac o ρ e b χ (r • δb) (r • ζ) p =
      r • linearizedFlatDirac o ρ e b χ δb ζ p := by
  have hζ : r • ζ = (r : ℂ) • ζ := funext fun q ↦ (Complex.coe_smul (r : ℝ) (ζ q)).symm
  rw [linearizedFlatDirac_apply, linearizedFlatDirac_apply, hζ, flatDirac_smul, Complex.coe_smul,
    smul_add, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    ← mul_smul, ← Complex.coe_smul, map_smul, ofReal_mul, mul_assoc]

omit [FiniteDimensional ℂ W] in
/-- `linearizedFlatDirac` sends the zero perturbation to zero. -/
@[simp] theorem linearizedFlatDirac_zero (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatDirac o ρ e b χ 0 0 p = 0 := by
  simp [linearizedFlatDirac_apply]

/-- `linearizedFlatCurvature` is the directional derivative of `flatCurvatureDefect` along
`(b + t • δb, χ + t • ζ)` at `t = 0`. -/
theorem hasDerivAt_flatCurvatureDefect (hkl : 2 + 2 = finrank ℝ V)
    (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    {b δb : V → V [⋀^Fin 1]→L[ℝ] ℝ} (χ ζ : V → positiveHalfSpinors o ρ) {p : V}
    (hb : DifferentiableAt ℝ b p) (hδb : DifferentiableAt ℝ δb p) :
    HasDerivAt (fun t : ℝ ↦ flatCurvatureDefect o ρ J hkl hω (b + t • δb) (χ + t • ζ) p)
      (linearizedFlatCurvature o ρ hkl χ δb ζ p) 0 := by
  let L := (((√2 : ℝ) • o.selfDualProj even_two hkl).toContinuousLinearMap).comp
    (LinearEquiv.toContinuousLinearEquiv (alternatingFormEquiv V 2).symm).toContinuousLinearMap
  have hcurv (t : ℝ) :
      (√2 : ℝ) • o.selfDualProj even_two hkl
        ((alternatingFormEquiv V 2).symm (-extDeriv (b + t • δb) p)) =
      L (-extDeriv b p) + t • L (-extDeriv δb p) := by
    have hd : -extDeriv (b + t • δb) p = -extDeriv b p + t • (-extDeriv δb p) := by
      rw [extDeriv_add hb (hδb.const_smul t), extDeriv_smul]; module
    rw [hd, map_add, map_smul, map_add, map_smul, smul_add, smul_comm (√2 : ℝ) t]
    simp [L]
  have hF : HasFDerivAt (quadraticTwoForm o ρ hkl) (quadraticTwoFormPolar o ρ hkl (χ p))
      (χ p + (0 : ℝ) • ζ p) := by simpa using hasFDerivAt_quadraticTwoForm o ρ hkl (χ p)
  exact ((((((hasDerivAt_id (0 : ℝ)).smul_const (L (-extDeriv δb p))).const_add
      (L (-extDeriv b p))).sub_const ((8⁻¹ : ℝ) • J.kahlerSelfDual o hkl hω)).fun_add
    ((hF.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const (ζ p)).const_add (χ p)))
      |>.const_smul (√2 / 4 : ℝ))).congr_deriv
    (by simp [L, linearizedFlatCurvature])).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun t ↦ by
      simp only [flatCurvatureDefect, Pi.add_apply, Pi.smul_apply, hcurv t, id_eq,
        Function.comp_apply]

/-- `linearizedFlatDirac` is the directional derivative of `flatDirac` along
`(b + t • δb, χ + t • ζ)` at `t = 0`. -/
theorem hasDerivAt_flatDirac (b δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    {χ ζ : V → positiveHalfSpinors o ρ} {p : V}
    (hχ : DifferentiableAt ℝ χ p) (hζ : DifferentiableAt ℝ ζ p) :
    HasDerivAt (fun t : ℝ ↦ flatDirac o ρ e (b + t • δb) (χ + t • ζ) p)
      (linearizedFlatDirac o ρ e b χ δb ζ p) 0 := by
  have : FiniteDimensional ℝ (positiveHalfSpinors o ρ) := FiniteDimensional.trans ℝ ℂ _
  let C (k : Fin 4) :
      positiveHalfSpinors o ρ →L[ℝ] Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
    (((halfSpinCliffordMul o ρ 1 (e k)).comp
      (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)).toLinearMap).restrictScalars
      ℝ).toContinuousLinearMap
  let d₁ (k : Fin 4) := spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)
  let d₂ (k : Fin 4) := δb p (fun _ ↦ e k) • (I • ζ p)
  have hcov (t : ℝ) (k : Fin 4) : spinorCovariantDeriv (b + t • δb) (χ + t • ζ) p (e k) =
      spinorCovariantDeriv b χ p (e k) + t • d₁ k + (t * t) • d₂ k := by
    rw [spinorCovariantDeriv_apply, (hχ.hasFDerivAt.add (hζ.hasFDerivAt.const_smul t)).fderiv]
    simp only [d₁, d₂, spinorCovariantDeriv_apply, add_apply, smul_apply, Pi.add_apply,
      Pi.smul_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, ← Complex.coe_smul]; push_cast; module
  have hterm (k : Fin 4) : HasDerivAt
      (fun t : ℝ ↦ C k (spinorCovariantDeriv (b + t • δb) (χ + t • ζ) p (e k))) (C k (d₁ k)) 0 :=
    ((C k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (((((hasDerivAt_id (0 : ℝ)).smul_const
        (d₁ k)).const_add (spinorCovariantDeriv b χ p (e k))).fun_add
      (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).smul_const (d₂ k))).congr_deriv
        (by simp))).congr_of_eventuallyEq <| Filter.Eventually.of_forall fun t ↦
          congrArg (C k) (hcov t k)
  have hlin : linearizedFlatDirac o ρ e b χ δb ζ p = ∑ k : Fin 4, C k (d₁ k) := by
    simp [C, d₁, linearizedFlatDirac_apply, flatDirac, Finset.sum_add_distrib]
  rw [hlin]
  exact (HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) ↦ hterm k).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun t ↦ by simp [C, flatDirac]

omit [FiniteDimensional ℂ W] in variable (e) in
/-- **Formal adjoint of the 4D infinitesimal gauge action** `f ↦ (-df, i f χ)` with respect to the
spinor-weighted metric `‖δb‖² + ‖ζ‖² / 4`: `∑ₖ ∂_{eₖ}(δb(eₖ)) + Im⟪χ, ζ⟫ / 4`. -/
def flatGaugeAdjoint (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) : ℝ :=
  (∑ k, (fderiv ℝ δb p (e k)) (fun _ ↦ e k)) + (⟪χ p, ζ p⟫_ℂ).im / 4

omit [FiniteDimensional ℂ W] in
/-- Definitional unfolding of `flatGaugeAdjoint`. -/
theorem flatGaugeAdjoint_def (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    flatGaugeAdjoint e χ δb ζ p =
      (∑ k, (fderiv ℝ δb p (e k)) (fun _ ↦ e k)) + (⟪χ p, ζ p⟫_ℂ).im / 4 :=
  (rfl)

omit [FiniteDimensional ℂ W] in
/-- `flatGaugeAdjoint` is independent of the choice of orthonormal basis of `V`. -/
theorem flatGaugeAdjoint_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    flatGaugeAdjoint e χ δb ζ p = flatGaugeAdjoint e' χ δb ζ p := by
  let B := (ContinuousLinearMap.coeLM ℝ).comp
    ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm.toLinearMap.comp
      (fderiv ℝ δb p).toLinearMap)
  exact congrArg (· + _) (e.sum_apply_self_eq e' B)

omit [FiniteDimensional ℂ W] in
/-- `flatGaugeAdjoint` is additive in the perturbation `(δb, ζ)` at a point of differentiability
of the connection perturbations. -/
theorem flatGaugeAdjoint_add (χ : V → positiveHalfSpinors o ρ) {δb₁ δb₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    (ζ₁ ζ₂ : V → positiveHalfSpinors o ρ) {p : V}
    (h₁ : DifferentiableAt ℝ δb₁ p) (h₂ : DifferentiableAt ℝ δb₂ p) :
    flatGaugeAdjoint e χ (δb₁ + δb₂) (ζ₁ + ζ₂) p =
      flatGaugeAdjoint e χ δb₁ ζ₁ p + flatGaugeAdjoint e χ δb₂ ζ₂ p := by
  simp only [flatGaugeAdjoint_def, fderiv_add h₁ h₂, add_apply, ContinuousAlternatingMap.add_apply,
    Finset.sum_add_distrib, Pi.add_apply, inner_add_right, add_im]
  ring

omit [FiniteDimensional ℂ W] in
/-- `flatGaugeAdjoint` commutes with real scalar multiplication of `(δb, ζ)`. -/
theorem flatGaugeAdjoint_smul (χ : V → positiveHalfSpinors o ρ) (r : ℝ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    flatGaugeAdjoint e χ (r • δb) (r • ζ) p = r * flatGaugeAdjoint e χ δb ζ p := by
  have hf : fderiv ℝ (r • δb) p = r • fderiv ℝ δb p :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := δb) r) p
  simp only [flatGaugeAdjoint_def, hf, smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    ← Finset.mul_sum, Pi.smul_apply, ← Complex.coe_smul, inner_smul_right, mul_im, ofReal_re,
    ofReal_im]
  ring

omit [FiniteDimensional ℂ W] in
/-- `flatGaugeAdjoint` sends the zero perturbation to zero. -/
@[simp] theorem flatGaugeAdjoint_zero (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatGaugeAdjoint e χ 0 0 p = 0 := by
  simp [flatGaugeAdjoint_def]

omit [FiniteDimensional ℂ W] in
/-- Pointwise divergence identity pairing a real gauge generator `f` against `flatGaugeAdjoint`
with the 4D infinitesimal gauge action `(-df, i f χ)` in the spinor-weighted pairing
`⟪δb₁, δb₂⟫ + Re⟪ζ₁, ζ₂⟫_ℂ / 4`. -/
theorem mul_flatGaugeAdjoint_eq {f : V → ℝ} (χ : V → positiveHalfSpinors o ρ)
    {δb : V → V [⋀^Fin 1]→L[ℝ] ℝ} (ζ : V → positiveHalfSpinors o ρ) {p : V}
    (hf : DifferentiableAt ℝ f p) (hδb : DifferentiableAt ℝ δb p) :
    f p * flatGaugeAdjoint e χ δb ζ p =
      (-(∑ k, fderiv ℝ f p (e k) * δb p (fun _ ↦ e k)) + (⟪f p • (I • χ p), ζ p⟫_ℂ).re / 4) +
        ∑ k, fderiv ℝ (fun q ↦ f q * δb q (fun _ ↦ e k)) p (e k) := by
  have hprod (k : Fin 4) : fderiv ℝ (fun q ↦ f q * δb q (fun _ ↦ e k)) p (e k) =
      fderiv ℝ f p (e k) * δb p (fun _ ↦ e k) + f p * (fderiv ℝ δb p (e k)) (fun _ ↦ e k) := by
    have hδbk : HasFDerivAt (fun q ↦ δb q (fun _ ↦ e k))
        ((ContinuousAlternatingMap.apply ℝ V ℝ (fun _ : Fin 1 ↦ e k)).comp (fderiv ℝ δb p)) p :=
      (ContinuousAlternatingMap.apply ℝ V ℝ (fun _ : Fin 1 ↦ e k)).hasFDerivAt.comp p
        hδb.hasFDerivAt
    rw [(hf.hasFDerivAt.fun_mul hδbk).fderiv]; simp; ring
  have hspin : (⟪f p • (I • χ p), ζ p⟫_ℂ).re = f p * (⟪χ p, ζ p⟫_ℂ).im := by
    rw [← Complex.coe_smul, inner_smul_left, inner_smul_left]; simp
  simp_rw [hprod, Finset.sum_add_distrib, ← Finset.mul_sum, hspin, flatGaugeAdjoint]; ring

variable (o ρ e) in
/-- **The eight-real-component linearized gauge-fixed flat Seiberg–Witten operator** at `(b, χ)`,
sending `(δb, ζ)` to `(flatGaugeAdjoint e χ δb ζ, linearizedFlatCurvature o ρ hkl χ δb ζ,
linearizedFlatDirac o ρ e b χ δb ζ)`. -/
def gaugeFixedFlatOperator (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    ℝ × Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ×
      Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  (flatGaugeAdjoint e χ δb ζ p, linearizedFlatCurvature o ρ hkl χ δb ζ p,
   linearizedFlatDirac o ρ e b χ δb ζ p)

/-- Unfolding formula for `gaugeFixedFlatOperator`. -/
theorem gaugeFixedFlatOperator_apply (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p =
      (flatGaugeAdjoint e χ δb ζ p, linearizedFlatCurvature o ρ hkl χ δb ζ p,
       linearizedFlatDirac o ρ e b χ δb ζ p) :=
  (rfl)

/-- `gaugeFixedFlatOperator` is independent of the choice of orthonormal basis of `V`. -/
theorem gaugeFixedFlatOperator_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p = gaugeFixedFlatOperator o ρ e' hkl b χ δb ζ p := by
  rw [gaugeFixedFlatOperator, gaugeFixedFlatOperator, flatGaugeAdjoint_congr_orthonormalBasis e',
    linearizedFlatDirac_congr_orthonormalBasis e']

/-- `gaugeFixedFlatOperator` is additive in the perturbation `(δb, ζ)` at a point of
differentiability. -/
theorem gaugeFixedFlatOperator_add (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) {δb₁ δb₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} {p : V}
    (hb₁ : DifferentiableAt ℝ δb₁ p) (hb₂ : DifferentiableAt ℝ δb₂ p)
    (hζ₁ : DifferentiableAt ℝ ζ₁ p) (hζ₂ : DifferentiableAt ℝ ζ₂ p) :
    gaugeFixedFlatOperator o ρ e hkl b χ (δb₁ + δb₂) (ζ₁ + ζ₂) p =
      gaugeFixedFlatOperator o ρ e hkl b χ δb₁ ζ₁ p +
        gaugeFixedFlatOperator o ρ e hkl b χ δb₂ ζ₂ p :=
  Prod.ext (flatGaugeAdjoint_add χ ζ₁ ζ₂ hb₁ hb₂) <|
    Prod.ext (linearizedFlatCurvature_add hkl χ ζ₁ ζ₂ hb₁ hb₂)
      (linearizedFlatDirac_add b χ δb₁ δb₂ hζ₁ hζ₂)

/-- `gaugeFixedFlatOperator` commutes with real scalar multiplication of `(δb, ζ)`. -/
theorem gaugeFixedFlatOperator_smul (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (r : ℝ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ (r • δb) (r • ζ) p =
      r • gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p :=
  Prod.ext (flatGaugeAdjoint_smul χ r δb ζ p) <|
    Prod.ext (linearizedFlatCurvature_smul hkl χ r δb ζ p)
      (linearizedFlatDirac_smul b χ r δb ζ p)

/-- `gaugeFixedFlatOperator` sends the zero perturbation to zero. -/
@[simp] theorem gaugeFixedFlatOperator_zero (hkl : 2 + 2 = finrank ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ 0 0 p = 0 := by
  simp [gaugeFixedFlatOperator_apply]

end TauCeti.SeibergWitten
