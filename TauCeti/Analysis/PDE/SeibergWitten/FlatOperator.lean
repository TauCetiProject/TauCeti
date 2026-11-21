/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.CanonicalLine
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.SeibergWitten.FlatWeitzenbock
public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# The flat four-dimensional Seiberg–Witten operators and their linearization

On an oriented four-dimensional real inner product space `V` with Clifford module `W = W⁺ ⊕ W⁻`
and compatible almost complex structure `J`, this file defines the chiral restriction
`flatChiralDirac` (`W⁺ → W⁻`) of `TauCeti.SeibergWitten.flatDirac`, the unit-symbol
self-dual curvature defect `flatCurvatureDefect`, their pointwise directional linearizations (first
variations) `linearizedFlatCurvature` and `linearizedFlatDirac` (`hasDerivAt_flatCurvatureDefect`,
`hasDerivAt_flatChiralDirac`), the formal infinitesimal gauge-fixing adjoint `flatGaugeAdjoint`
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

private theorem fderiv_coe_positiveHalfSpinors (χ : V → positiveHalfSpinors o ρ) (p v : V) :
    fderiv ℝ (fun q ↦ (χ q : W)) p v = (fderiv ℝ χ p v : W) := by
  let ιL : positiveHalfSpinors o ρ →L[ℝ] W :=
    (positiveHalfSpinors o ρ).subtypeL.restrictScalars ℝ
  let πL : W →L[ℝ] positiveHalfSpinors o ρ :=
    (positiveHalfSpinors o ρ).orthogonalProjectionOnto.restrictScalars ℝ
  by_cases hχ : DifferentiableAt ℝ χ p
  · exact congrArg (· v) (ιL.hasFDerivAt.comp p hχ.hasFDerivAt).fderiv
  · have hcoe : ¬DifferentiableAt ℝ (fun q ↦ (χ q : W)) p := fun h ↦
      hχ <| (πL.differentiableAt.comp p h).congr_of_eventuallyEq <|
        Filter.Eventually.of_forall fun q ↦
          (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _).symm
    rw [fderiv_zero_of_not_differentiableAt hcoe, fderiv_zero_of_not_differentiableAt hχ]
    simp

private theorem covariantDeriv_coe_positiveHalfSpinors (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (p v : V) :
    covariantDeriv b (fun q ↦ (χ q : W)) p v = (covariantDeriv b χ p v : W) := by
  simp only [covariantDeriv_apply, fderiv_coe_positiveHalfSpinors, Submodule.coe_add,
    Submodule.coe_smul_of_tower]

variable (o ρ) in
/-- **The flat chiral Dirac operator** `D_b⁺ χ = D_b χ : W⁺ → W⁻`, restricting
`TauCeti.SeibergWitten.flatDirac` to positive half-spinor fields. -/
def flatChiralDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  ⟨flatDirac ρ b (fun q ↦ (χ q : W)) p, by
    let e₀ : OrthonormalBasis (Fin 4) ℝ V :=
      (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
    rw [flatDirac_eq_sum ρ e₀]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [covariantDeriv_coe_positiveHalfSpinors,
      ← LinearEquiv.coe_ofEq_apply (positiveHalfSpinors_eq_eigenspace o ρ)
        (covariantDeriv b χ p (e₀ k)),
      ← coe_halfSpinCliffordMul_apply_apply (o := o) (ρ := ρ) (ε := 1) (v := e₀ k)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
          (covariantDeriv b χ p (e₀ k)))]
    exact (halfSpinCliffordMul o ρ 1 (e₀ k) _).property⟩

/-- Ambient Clifford-module expression for `flatChiralDirac`. -/
@[simp] theorem coe_flatChiralDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (p : V) :
    (flatChiralDirac o ρ b χ p : W) = flatDirac ρ b (fun q ↦ (χ q : W)) p :=
  (rfl)

/-- Basis expansion of `flatChiralDirac` in any orthonormal basis `e` of `V`. -/
theorem flatChiralDirac_eq_sum (e : OrthonormalBasis (Fin 4) ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatChiralDirac o ρ b χ p = ∑ k, halfSpinCliffordMul o ρ 1 (e k)
      (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
        (covariantDeriv b χ p (e k))) := by
  apply Subtype.ext
  rw [coe_flatChiralDirac, flatDirac_eq_sum ρ e, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [covariantDeriv_coe_positiveHalfSpinors, coe_halfSpinCliffordMul_apply_apply,
    LinearEquiv.coe_ofEq_apply]

/-- `flatChiralDirac` is additive in the spinor field at a point of differentiability. -/
theorem flatChiralDirac_add (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) {χ₁ χ₂ : V → positiveHalfSpinors o ρ}
    {p : V} (h₁ : DifferentiableAt ℝ χ₁ p) (h₂ : DifferentiableAt ℝ χ₂ p) :
    flatChiralDirac o ρ b (χ₁ + χ₂) p =
      flatChiralDirac o ρ b χ₁ p + flatChiralDirac o ρ b χ₂ p := by
  let e₀ : OrthonormalBasis (Fin 4) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  simp [flatChiralDirac_eq_sum e₀, covariantDeriv_add b h₁ h₂, Finset.sum_add_distrib]

/-- `flatChiralDirac` is `ℂ`-homogeneous in the spinor field for constant complex scalars. -/
theorem flatChiralDirac_smul (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (c : ℂ)
    (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatChiralDirac o ρ b (c • χ) p = c • flatChiralDirac o ρ b χ p := by
  let e₀ : OrthonormalBasis (Fin 4) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  simp [flatChiralDirac_eq_sum e₀, covariantDeriv_smul, Finset.smul_sum]

/-- `flatChiralDirac` sends the zero spinor field to zero. -/
@[simp] theorem flatChiralDirac_zero (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (p : V) :
    flatChiralDirac o ρ b 0 p = 0 := by
  let e₀ : OrthonormalBasis (Fin 4) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  simp [flatChiralDirac_eq_sum e₀]

/-- Action of `flatChiralDirac` on a scalar multiple `α • ψ₀` of a constant positive
half-spinor. -/
theorem coe_flatChiralDirac_smul_const (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) {α : V → ℂ} {p : V}
    (hα : DifferentiableAt ℝ α p) (ψ₀ : positiveHalfSpinors o ρ)
    (e : OrthonormalBasis (Fin 4) ℝ V) :
    (flatChiralDirac o ρ b (fun q ↦ α q • ψ₀) p : W) =
      ∑ k, covariantDeriv b α p (e k) • ρ (ι Q (e k)) ψ₀ := by
  simpa [coe_flatChiralDirac] using flatDirac_smul_const ρ hα (ψ₀ : W) e


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

variable (o ρ e) in
/-- **Linearized chiral Dirac operator** `D_b ζ + ∑ₖ c(eₖ) (i δb(eₖ) χ)`. -/
def linearizedFlatDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  flatChiralDirac o ρ b ζ p + ∑ k, halfSpinCliffordMul o ρ 1 (e k)
    (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
      (δb p (fun _ ↦ e k) • (I • χ p)))

/-- Unfolding formula for `linearizedFlatDirac`. -/
theorem linearizedFlatDirac_apply (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatDirac o ρ e b χ δb ζ p =
      flatChiralDirac o ρ b ζ p + ∑ k, halfSpinCliffordMul o ρ 1 (e k)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
          (δb p (fun _ ↦ e k) • (I • χ p))) :=
  (rfl)

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
  exact congrArg (flatChiralDirac o ρ b ζ p + ·) <| by
    simpa [B, T, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply] using
      e.sum_apply_self_eq e' B

/-- `linearizedFlatDirac` is additive in the perturbation `(δb, ζ)` at a point of
differentiability of the spinor perturbations. -/
theorem linearizedFlatDirac_add (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb₁ δb₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ) {ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} {p : V}
    (h₁ : DifferentiableAt ℝ ζ₁ p) (h₂ : DifferentiableAt ℝ ζ₂ p) :
    linearizedFlatDirac o ρ e b χ (δb₁ + δb₂) (ζ₁ + ζ₂) p =
      linearizedFlatDirac o ρ e b χ δb₁ ζ₁ p + linearizedFlatDirac o ρ e b χ δb₂ ζ₂ p := by
  simp only [linearizedFlatDirac_apply, flatChiralDirac_add b h₁ h₂, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, add_smul, map_add, Finset.sum_add_distrib]
  abel

/-- `linearizedFlatDirac` commutes with real scalar multiplication of `(δb, ζ)`. -/
theorem linearizedFlatDirac_smul (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (r : ℝ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatDirac o ρ e b χ (r • δb) (r • ζ) p =
      r • linearizedFlatDirac o ρ e b χ δb ζ p := by
  have hζ : r • ζ = (r : ℂ) • ζ := funext fun q ↦ (Complex.coe_smul (r : ℝ) (ζ q)).symm
  rw [linearizedFlatDirac_apply, linearizedFlatDirac_apply, hζ, flatChiralDirac_smul,
    Complex.coe_smul, smul_add, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    ← mul_smul, ← Complex.coe_smul, map_smul, ofReal_mul, mul_assoc]

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

/-- `linearizedFlatDirac` is the directional derivative of `flatChiralDirac` along
`(b + t • δb, χ + t • ζ)` at `t = 0`. -/
theorem hasDerivAt_flatChiralDirac (b δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    {χ ζ : V → positiveHalfSpinors o ρ} {p : V}
    (hχ : DifferentiableAt ℝ χ p) (hζ : DifferentiableAt ℝ ζ p) :
    HasDerivAt (fun t : ℝ ↦ flatChiralDirac o ρ (b + t • δb) (χ + t • ζ) p)
      (linearizedFlatDirac o ρ e b χ δb ζ p) 0 := by
  have : FiniteDimensional ℝ (positiveHalfSpinors o ρ) := FiniteDimensional.trans ℝ ℂ _
  let C (k : Fin 4) :
      positiveHalfSpinors o ρ →L[ℝ] Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
    (((halfSpinCliffordMul o ρ 1 (e k)).comp
      (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)).toLinearMap).restrictScalars
      ℝ).toContinuousLinearMap
  let d₁ (k : Fin 4) := covariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)
  let d₂ (k : Fin 4) := δb p (fun _ ↦ e k) • (I • ζ p)
  have hcov (t : ℝ) (k : Fin 4) : covariantDeriv (b + t • δb) (χ + t • ζ) p (e k) =
      covariantDeriv b χ p (e k) + t • d₁ k + (t * t) • d₂ k := by
    rw [covariantDeriv_apply, (hχ.hasFDerivAt.add (hζ.hasFDerivAt.const_smul t)).fderiv]
    simp only [d₁, d₂, covariantDeriv_apply, add_apply, smul_apply, Pi.add_apply,
      Pi.smul_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, ← Complex.coe_smul]; push_cast; module
  have hterm (k : Fin 4) : HasDerivAt
      (fun t : ℝ ↦ C k (covariantDeriv (b + t • δb) (χ + t • ζ) p (e k))) (C k (d₁ k)) 0 :=
    ((C k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (((((hasDerivAt_id (0 : ℝ)).smul_const
        (d₁ k)).const_add (covariantDeriv b χ p (e k))).fun_add
      (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).smul_const (d₂ k))).congr_deriv
        (by simp))).congr_of_eventuallyEq <| Filter.Eventually.of_forall fun t ↦
          congrArg (C k) (hcov t k)
  have hlin : linearizedFlatDirac o ρ e b χ δb ζ p = ∑ k : Fin 4, C k (d₁ k) := by
    simp [C, d₁, linearizedFlatDirac_apply, flatChiralDirac_eq_sum e, Finset.sum_add_distrib]
  rw [hlin]
  exact (HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) ↦ hterm k).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun t ↦ by
      simp [C, flatChiralDirac_eq_sum e]

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
