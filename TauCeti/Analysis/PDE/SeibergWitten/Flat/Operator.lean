/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.Canonical.Line
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.SeibergWitten.Flat.Weitzenbock
public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# The flat four-dimensional Seiberg–Witten operators and their linearization

On an oriented four-dimensional real inner product space `V` with Clifford module `W = W⁺ ⊕ W⁻`
and compatible almost complex structure `J`, this file defines the chiral restriction
`flatChiralDirac` (`W⁺ → W⁻`) of `TauCeti.SeibergWitten.flatDirac`, the unit-symbol
self-dual curvature defect `flatCurvatureDefect`, the gauge-fixing, curvature, and Dirac rows
`flatDeformationGauge`, `flatDeformationCurvature`, and `flatDeformationDirac` of the linearized
equations (`hasDerivAt_flatCurvatureDefect`, `hasDerivAt_flatChiralDirac`,
`mul_flatDeformationGauge_eq`), and the combined eight-real-component linearized gauge-fixed
operator `gaugeFixedFlatOperator`, together with orthonormal-frame independence and linearity
properties.

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

private abbrev refBasis (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (finrank ℝ V = 4)] : OrthonormalBasis (Fin 4) ℝ V :=
  (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)

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
    rw [flatDirac_eq_sum ρ (refBasis V)]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [covariantDeriv_coe_positiveHalfSpinors,
      ← LinearEquiv.coe_ofEq_apply (positiveHalfSpinors_eq_eigenspace o ρ)
        (covariantDeriv b χ p (refBasis V k)),
      ← coe_halfSpinCliffordMul_apply_apply (o := o) (ρ := ρ) (ε := 1) (v := refBasis V k)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
          (covariantDeriv b χ p (refBasis V k)))]
    exact (halfSpinCliffordMul o ρ 1 (refBasis V k) _).property⟩

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
  simp [flatChiralDirac_eq_sum (refBasis V), covariantDeriv_add b h₁ h₂, Finset.sum_add_distrib]

/-- `flatChiralDirac` is `ℂ`-homogeneous in the spinor field for constant complex scalars. -/
theorem flatChiralDirac_smul (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (c : ℂ)
    (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatChiralDirac o ρ b (c • χ) p = c • flatChiralDirac o ρ b χ p := by
  simp [flatChiralDirac_eq_sum (refBasis V), covariantDeriv_smul, Finset.smul_sum]

/-- `flatChiralDirac` sends the zero spinor field to zero. -/
@[simp] theorem flatChiralDirac_zero (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (p : V) :
    flatChiralDirac o ρ b 0 p = 0 := by
  simp [flatChiralDirac_eq_sum (refBasis V)]

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

/-! ### The gauge-fixed linearization of the flat limiting equations -/

section Deformation

omit [FiniteDimensional ℂ W] in variable (e) in
/-- The **gauge-fixing row** of the linearized flat limiting equations at a spinor `ψ`, applied to
a variation `(b', ζ)` of the connection `a = i b` and of the spinor: the formal `L²` adjoint
`d₀*(b', ζ) = div b' + Re⟪i ψ, ζ⟫ / 4` of the charge-one infinitesimal gauge action
`d₀ f = (-df, i f ψ)`, for the coefficient metric `|b'|² + |ζ|² / 4`. -/
def flatDeformationGauge (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ ζ : V → positiveHalfSpinors o ρ)
    (y : V) : ℝ :=
  ∑ k, fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e k)) y (e k) + (⟪I • (ψ y : W), (ζ y : W)⟫_ℂ).re / 4

omit [FiniteDimensional ℂ W] in
/-- Definitional unfolding of `flatDeformationGauge`. -/
theorem flatDeformationGauge_def (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationGauge e b' ψ ζ y =
      ∑ k, fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e k)) y (e k) +
        (⟪I • (ψ y : W), (ζ y : W)⟫_ℂ).re / 4 :=
  (rfl)

omit [FiniteDimensional ℂ W] in
/-- `flatDeformationGauge` is independent of the choice of orthonormal basis of `V` at points of
differentiability of the connection perturbation. -/
theorem flatDeformationGauge_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    {b' : V → V [⋀^Fin 1]→L[ℝ] ℝ} (ψ ζ : V → positiveHalfSpinors o ρ) {y : V}
    (hb' : DifferentiableAt ℝ b' y) :
    flatDeformationGauge e b' ψ ζ y = flatDeformationGauge e' b' ψ ζ y := by
  let B := (ContinuousLinearMap.coeLM ℝ).comp
    ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm.toLinearMap.comp
      (fderiv ℝ b' y).toLinearMap)
  refine congrArg (· + _) ?_
  simp only [fderiv_continuousAlternatingMap_apply_const_apply hb']
  exact e.sum_apply_self_eq e' B

omit [FiniteDimensional ℂ W] in
/-- `flatDeformationGauge` is additive in the perturbation `(b', ζ)` at a point of
differentiability of the connection perturbations. -/
theorem flatDeformationGauge_add {b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    (ψ ζ₁ ζ₂ : V → positiveHalfSpinors o ρ) {y : V}
    (h₁ : DifferentiableAt ℝ b₁ y) (h₂ : DifferentiableAt ℝ b₂ y) :
    flatDeformationGauge e (b₁ + b₂) ψ (ζ₁ + ζ₂) y =
      flatDeformationGauge e b₁ ψ ζ₁ y + flatDeformationGauge e b₂ ψ ζ₂ y := by
  have hd {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hb : DifferentiableAt ℝ b y) (k : Fin 4) :
      DifferentiableAt ℝ (fun y' ↦ b y' (fun _ ↦ e k)) y :=
    (ContinuousAlternatingMap.apply ℝ V ℝ (fun _ : Fin 1 ↦ e k)).differentiableAt.comp y hb
  have hsum (k : Fin 4) :
      fderiv ℝ (fun y' ↦ (b₁ + b₂) y' (fun _ ↦ e k)) y (e k) =
        fderiv ℝ (fun y' ↦ b₁ y' (fun _ ↦ e k)) y (e k) +
          fderiv ℝ (fun y' ↦ b₂ y' (fun _ ↦ e k)) y (e k) := by
    simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply]
    rw [fderiv_fun_add (hd h₁ k) (hd h₂ k), add_apply]
  rw [flatDeformationGauge_def, flatDeformationGauge_def, flatDeformationGauge_def]
  simp_rw [hsum]
  simp only [Finset.sum_add_distrib, Pi.add_apply, Submodule.coe_add, inner_add_right, add_re]
  ring

omit [FiniteDimensional ℂ W] in
/-- `flatDeformationGauge` commutes with real scalar multiplication of `(b', ζ)`. -/
theorem flatDeformationGauge_smul (r : ℝ) (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationGauge e (r • b') ψ (r • ζ) y = r * flatDeformationGauge e b' ψ ζ y := by
  have hf (k : Fin 4) : fderiv ℝ (fun y' ↦ r * b' y' (fun _ ↦ e k)) y =
      r • fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e k)) y :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fun y' ↦ b' y' (fun _ ↦ e k)) r) y
  simp only [flatDeformationGauge_def, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, hf, smul_apply, ← Finset.mul_sum, Submodule.coe_smul_of_tower, ← Complex.coe_smul,
    inner_smul_right, mul_re, ofReal_re, ofReal_im]
  ring

omit [FiniteDimensional ℂ W] in
/-- `flatDeformationGauge` sends the zero perturbation to zero. -/
@[simp] theorem flatDeformationGauge_zero (ψ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationGauge e 0 ψ 0 y = 0 := by
  simp [flatDeformationGauge_def]

omit [FiniteDimensional ℂ W] in
/-- Pointwise divergence identity pairing a real gauge generator `f` against `flatDeformationGauge`
with the 4D infinitesimal gauge action `(-df, i f ψ)` in the spinor-weighted pairing
`⟪b₁, b₂⟫ + Re⟪ζ₁, ζ₂⟫_ℂ / 4`. -/
theorem mul_flatDeformationGauge_eq {f : V → ℝ} {b' : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    (ψ ζ : V → positiveHalfSpinors o ρ) {y : V}
    (hf : DifferentiableAt ℝ f y) (hb' : DifferentiableAt ℝ b' y) :
    f y * flatDeformationGauge e b' ψ ζ y =
      (-(∑ k, fderiv ℝ f y (e k) * b' y (fun _ ↦ e k)) + (⟪f y • (I • ψ y), ζ y⟫_ℂ).re / 4) +
        ∑ k, fderiv ℝ (fun y' ↦ f y' * b' y' (fun _ ↦ e k)) y (e k) := by
  have hprod (k : Fin 4) : fderiv ℝ (fun y' ↦ f y' * b' y' (fun _ ↦ e k)) y (e k) =
      fderiv ℝ f y (e k) * b' y (fun _ ↦ e k) +
        f y * fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e k)) y (e k) := by
    have hb'k : DifferentiableAt ℝ (fun y' ↦ b' y' (fun _ ↦ e k)) y :=
      (ContinuousAlternatingMap.apply ℝ V ℝ (fun _ : Fin 1 ↦ e k)).differentiableAt.comp y hb'
    rw [(hf.hasFDerivAt.fun_mul hb'k.hasFDerivAt).fderiv]
    simp; ring
  have hspin : (⟪f y • (I • ψ y), ζ y⟫_ℂ).re = f y * (⟪I • (ψ y : W), (ζ y : W)⟫_ℂ).re := by
    rw [← Complex.coe_smul, inner_smul_left, ← Submodule.coe_smul (I : ℂ) (ψ y),
      Submodule.coe_inner]
    simp
  simp_rw [hprod, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hspin, flatDeformationGauge_def]
  ring

variable (o ρ) in
/-- The **curvature row** of the linearized flat limiting equations at a spinor `ψ`, applied to a
variation `(b', ζ)`: the derivative `F' + ⋆F' + q'(ψ, ζ) / 2`, `F' = -db'`, of the flat curvature
equation `F + ⋆F = ω / 8 - q(ψ) / 2`
(`sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff`), with the real curvature
`F = -db` read as a two-vector. -/
def flatDeformationCurvature (hkl : 2 + 2 = finrank ℝ V) (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) : ⋀[ℝ]^2 V :=
  (alternatingFormEquiv V 2).symm (-extDeriv b' y) +
      o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b' y)) +
    (2⁻¹ : ℝ) • (quadraticTwoFormPolar o ρ hkl (ψ y) (ζ y) : ⋀[ℝ]^2 V)

/-- Definitional unfolding of `flatDeformationCurvature`. -/
theorem flatDeformationCurvature_def (hkl : 2 + 2 = finrank ℝ V)
    (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationCurvature o ρ hkl b' ψ ζ y =
      (alternatingFormEquiv V 2).symm (-extDeriv b' y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b' y)) +
        (2⁻¹ : ℝ) • (quadraticTwoFormPolar o ρ hkl (ψ y) (ζ y) : ⋀[ℝ]^2 V) :=
  (rfl)

/-- The curvature row is self-dual. -/
theorem hodgeStar_flatDeformationCurvature (hkl : 2 + 2 = finrank ℝ V)
    (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    o.hodgeStar hkl (flatDeformationCurvature o ρ hkl b' ψ ζ y) =
      flatDeformationCurvature o ρ hkl b' ψ ζ y := by
  rw [flatDeformationCurvature, map_add, map_add, map_smul,
    o.hodgeStar_hodgeStar_of_even even_two hkl, o.hodgeStar_coe_of_mem_eigenspace_one hkl]
  abel

/-- `flatDeformationCurvature` sends the zero perturbation to zero. -/
@[simp] theorem flatDeformationCurvature_zero (hkl : 2 + 2 = finrank ℝ V)
    (ψ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationCurvature o ρ hkl 0 ψ 0 y = 0 := by
  have h0 : extDeriv (0 : V → V [⋀^Fin 1]→L[ℝ] ℝ) y = 0 := by
    simpa using extDeriv_smul (0 : ℝ) (0 : V → V [⋀^Fin 1]→L[ℝ] ℝ) (x := y)
  simp [flatDeformationCurvature, h0]

/-- `(√2 / 2) • flatDeformationCurvature` is the directional derivative of `flatCurvatureDefect`
along `(b + t • δb, χ + t • ζ)` at `t = 0`. -/
theorem hasDerivAt_flatCurvatureDefect (hkl : 2 + 2 = finrank ℝ V)
    (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    {b δb : V → V [⋀^Fin 1]→L[ℝ] ℝ} (χ ζ : V → positiveHalfSpinors o ρ) {p : V}
    (hb : DifferentiableAt ℝ b p) (hδb : DifferentiableAt ℝ δb p) :
    HasDerivAt (fun t : ℝ ↦ flatCurvatureDefect o ρ J hkl hω (b + t • δb) (χ + t • ζ) p)
      ⟨(√2 / 2 : ℝ) • flatDeformationCurvature o ρ hkl δb χ ζ p,
        Submodule.smul_mem _ _ (by
          rw [Module.End.mem_eigenspace_iff, one_smul]
          exact hodgeStar_flatDeformationCurvature hkl δb χ ζ p)⟩ 0 := by
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
  have hL (α : V [⋀^Fin 2]→L[ℝ] ℝ) : (L α : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • ((alternatingFormEquiv V 2).symm α +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm α)) := by
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearEquiv.coe_toContinuousLinearEquiv', LinearMap.coe_toContinuousLinearMap',
      LinearMap.smul_apply, Submodule.coe_smul, Orientation.coe_selfDualProj_apply]
    module
  have hF : HasFDerivAt (quadraticTwoForm o ρ hkl) (quadraticTwoFormPolar o ρ hkl (χ p))
      (χ p + (0 : ℝ) • ζ p) := by simpa using hasFDerivAt_quadraticTwoForm o ρ hkl (χ p)
  have hcurvDeriv : HasDerivAt
      (fun t : ℝ ↦
        L (-extDeriv b p) + t • L (-extDeriv δb p) - (8⁻¹ : ℝ) • J.kahlerSelfDual o hkl hω)
      (L (-extDeriv δb p)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (L (-extDeriv δb p))).const_add
      (L (-extDeriv b p))).sub_const ((8⁻¹ : ℝ) • J.kahlerSelfDual o hkl hω)
  have hquadDeriv : HasDerivAt
      (fun t : ℝ ↦ (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p + t • ζ p))
      ((√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (χ p) (ζ p)) 0 := by
    have hspin : HasDerivAt (fun t : ℝ ↦ χ p + t • ζ p) (ζ p) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ζ p)).const_add (χ p)
    exact (hF.comp_hasDerivAt (0 : ℝ) hspin).const_smul (√2 / 4 : ℝ)
  refine ((hcurvDeriv.fun_add hquadDeriv).congr_deriv ?_).congr_of_eventuallyEq ?_
  · refine Subtype.ext ?_
    simp only [Submodule.coe_add, Submodule.coe_smul, hL, flatDeformationCurvature]
    module
  · exact Filter.Eventually.of_forall fun t ↦ by
      simp only [flatCurvatureDefect, Pi.add_apply, Pi.smul_apply, hcurv t]

section

omit [FiniteDimensional ℂ W]

variable (e) in
/-- The **Dirac row** of the linearized flat limiting equations at a pair `(b, ψ)`, applied to a
variation `(b', ζ)`: the derivative `∑ₖ c(eₖ) (∇_{eₖ} ζ + i b'(eₖ) ψ)`, `∇ = d + i b`, of the flat
Dirac operator `∑ₖ c(eₖ) ∇_{eₖ} ψ`. -/
def flatDeformationDirac (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ ζ : V → positiveHalfSpinors o ρ)
    (y : V) : W :=
  ∑ k, ρ (ι Q (e k)) (fderiv ℝ (fun y' ↦ (ζ y' : W)) y (e k) +
    (I * b y (fun _ ↦ e k)) • (ζ y : W) + (I * b' y (fun _ ↦ e k)) • (ψ y : W))

/-- Definitional unfolding of `flatDeformationDirac`. -/
theorem flatDeformationDirac_def (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationDirac e b b' ψ ζ y =
      ∑ k, ρ (ι Q (e k)) (fderiv ℝ (fun y' ↦ (ζ y' : W)) y (e k) +
        (I * b y (fun _ ↦ e k)) • (ζ y : W) + (I * b' y (fun _ ↦ e k)) • (ψ y : W)) :=
  (rfl)

end

/-- Ambient-space identification of `flatDeformationDirac` as the chiral Dirac operator on `ζ` plus
the zero-order connection variation term. -/
theorem flatDeformationDirac_eq_coe_flatChiralDirac_add (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationDirac e b b' ψ ζ y =
      (flatChiralDirac o ρ b ζ y : W) + ∑ k, (halfSpinCliffordMul o ρ 1 (e k)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
          (b' y (fun _ ↦ e k) • (I • ψ y))) : W) := by
  rw [flatDeformationDirac_def, flatChiralDirac_eq_sum e, Submodule.coe_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coe_halfSpinCliffordMul_apply_apply, coe_halfSpinCliffordMul_apply_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.coe_ofEq_apply,
    ← covariantDeriv_coe_positiveHalfSpinors, covariantDeriv_apply, fderiv_coe_positiveHalfSpinors]
  simp only [Submodule.coe_smul_of_tower, ← Complex.coe_smul, smul_smul,
    mul_comm I (_ : ℂ), map_add]

/-- `flatDeformationDirac` takes values in the negative half-spinors `W⁻`. -/
theorem mem_eigenspace_flatDeformationDirac (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationDirac e b b' ψ ζ y ∈ Module.End.eigenspace (ρ (chirality Q o)) (-1) := by
  rw [flatDeformationDirac_eq_coe_flatChiralDirac_add]
  exact Submodule.add_mem _ (flatChiralDirac o ρ b ζ y).property
    (Submodule.sum_mem _ fun k _ ↦ (halfSpinCliffordMul o ρ 1 (e k) _).property)

/-- `flatDeformationDirac` is independent of the choice of orthonormal basis of `V`. -/
theorem flatDeformationDirac_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationDirac e b b' ψ ζ y = flatDeformationDirac e' b b' ψ ζ y := by
  let T := (((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (b' y)).smulRight
    (I • ψ y)).toLinearMap
  let B := ((LinearMap.restrictScalarsₗ ℝ ℂ _ _ ℝ).comp (halfSpinCliffordMul o ρ 1)).compl₂
    (((LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)).toLinearMap.restrictScalars
      ℝ).comp T)
  have hsum :
      (∑ k, halfSpinCliffordMul o ρ 1 (e k)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
          (b' y (fun _ ↦ e k) • (I • ψ y))) :
        Module.End.eigenspace (ρ (chirality Q o)) (-1)) =
      ∑ k, halfSpinCliffordMul o ρ 1 (e' k)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
          (b' y (fun _ ↦ e' k) • (I • ψ y))) := by
    simpa [B, T, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply] using
      e.sum_apply_self_eq e' B
  rw [flatDeformationDirac_eq_coe_flatChiralDirac_add (e := e),
    flatDeformationDirac_eq_coe_flatChiralDirac_add (e := e')]
  simpa [Submodule.coe_sum] using congrArg (fun ν : Module.End.eigenspace (ρ (chirality Q o)) (-1) ↦
    (flatChiralDirac o ρ b ζ y : W) + (ν : W)) hsum

/-- `flatDeformationDirac` sends the zero perturbation to zero. -/
@[simp] theorem flatDeformationDirac_zero (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationDirac e b 0 ψ 0 y = 0 := by
  simp [flatDeformationDirac_eq_coe_flatChiralDirac_add]

/-- `flatDeformationDirac` is the directional derivative of `flatChiralDirac` along
`(b + t • δb, χ + t • ζ)` at `t = 0`. -/
theorem hasDerivAt_flatChiralDirac (b δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    {χ ζ : V → positiveHalfSpinors o ρ} {p : V}
    (hχ : DifferentiableAt ℝ χ p) (hζ : DifferentiableAt ℝ ζ p) :
    HasDerivAt (fun t : ℝ ↦ flatChiralDirac o ρ (b + t • δb) (χ + t • ζ) p)
      ⟨flatDeformationDirac e b δb χ ζ p,
        mem_eigenspace_flatDeformationDirac b δb χ ζ p⟩ 0 := by
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
  have hcovDeriv (k : Fin 4) : HasDerivAt
      (fun t : ℝ ↦ covariantDeriv b χ p (e k) + t • d₁ k + (t * t) • d₂ k) (d₁ k) 0 := by
    have hlin : HasDerivAt (fun t : ℝ ↦ covariantDeriv b χ p (e k) + t • d₁ k) (d₁ k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (d₁ k)).const_add (covariantDeriv b χ p (e k))
    have hquad : HasDerivAt (fun t : ℝ ↦ (t * t) • d₂ k) (0 : positiveHalfSpinors o ρ) 0 := by
      have hsq : HasDerivAt (fun t : ℝ ↦ t * t) 0 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).fun_mul (hasDerivAt_id (0 : ℝ))
      simpa using hsq.smul_const (d₂ k)
    simpa using hlin.fun_add hquad
  have hterm (k : Fin 4) : HasDerivAt
      (fun t : ℝ ↦ C k (covariantDeriv (b + t • δb) (χ + t • ζ) p (e k))) (C k (d₁ k)) 0 :=
    ((C k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hcovDeriv k)).congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun t ↦ congrArg (C k) (hcov t k)
  have hlin : (⟨flatDeformationDirac e b δb χ ζ p,
      mem_eigenspace_flatDeformationDirac b δb χ ζ p⟩ :
      Module.End.eigenspace (ρ (chirality Q o)) (-1)) = ∑ k : Fin 4, C k (d₁ k) := by
    apply Subtype.ext
    dsimp only
    rw [flatDeformationDirac_eq_coe_flatChiralDirac_add, flatChiralDirac_eq_sum e,
      Submodule.coe_sum, Submodule.coe_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [C, d₁]
  rw [hlin]
  exact (HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) ↦ hterm k).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun t ↦ by
      simp [C, flatChiralDirac_eq_sum e]

end Deformation

variable (o ρ e) in
/-- **The eight-real-component linearized gauge-fixed flat Seiberg–Witten operator** at `(b, χ)`,
sending `(δb, ζ)` to `(flatDeformationGauge e δb χ ζ,
(√2 / 2) • flatDeformationCurvature o ρ hkl δb χ ζ, flatDeformationDirac e b δb χ ζ)`. -/
def gaugeFixedFlatOperator (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    ℝ × Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ×
      Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  (flatDeformationGauge e δb χ ζ p,
   ⟨(√2 / 2 : ℝ) • flatDeformationCurvature o ρ hkl δb χ ζ p,
     Submodule.smul_mem _ _ (by
       rw [Module.End.mem_eigenspace_iff, one_smul]
       exact hodgeStar_flatDeformationCurvature hkl δb χ ζ p)⟩,
   ⟨flatDeformationDirac e b δb χ ζ p,
     mem_eigenspace_flatDeformationDirac b δb χ ζ p⟩)

/-- Unfolding formula for `gaugeFixedFlatOperator`. -/
theorem gaugeFixedFlatOperator_apply (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p =
      (flatDeformationGauge e δb χ ζ p,
       ⟨(√2 / 2 : ℝ) • flatDeformationCurvature o ρ hkl δb χ ζ p,
         Submodule.smul_mem _ _ (by
           rw [Module.End.mem_eigenspace_iff, one_smul]
           exact hodgeStar_flatDeformationCurvature hkl δb χ ζ p)⟩,
       ⟨flatDeformationDirac e b δb χ ζ p,
         mem_eigenspace_flatDeformationDirac b δb χ ζ p⟩) :=
  (rfl)

/-- Coercion of the self-dual curvature component of `gaugeFixedFlatOperator` to `⋀[ℝ]^2 V`. -/
theorem coe_gaugeFixedFlatOperator_snd_fst (hkl : 2 + 2 = finrank ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    ((gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p).2.1 : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • flatDeformationCurvature o ρ hkl δb χ ζ p :=
  (rfl)

/-- `gaugeFixedFlatOperator` is independent of the choice of orthonormal basis of `V` at points
of differentiability of the connection perturbation. -/
theorem gaugeFixedFlatOperator_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    {δb : V → V [⋀^Fin 1]→L[ℝ] ℝ} (ζ : V → positiveHalfSpinors o ρ) {p : V}
    (hδb : DifferentiableAt ℝ δb p) :
    gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p = gaugeFixedFlatOperator o ρ e' hkl b χ δb ζ p := by
  refine Prod.ext (flatDeformationGauge_congr_orthonormalBasis e' χ ζ hδb) <|
    Prod.ext rfl (Subtype.ext ?_)
  exact flatDeformationDirac_congr_orthonormalBasis e' b δb χ ζ p

/-- `gaugeFixedFlatOperator` is additive in the perturbation `(δb, ζ)` at a point of
differentiability. -/
theorem gaugeFixedFlatOperator_add (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) {δb₁ δb₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} {p : V}
    (hb₁ : DifferentiableAt ℝ δb₁ p) (hb₂ : DifferentiableAt ℝ δb₂ p)
    (hζ₁ : DifferentiableAt ℝ ζ₁ p) (hζ₂ : DifferentiableAt ℝ ζ₂ p) :
    gaugeFixedFlatOperator o ρ e hkl b χ (δb₁ + δb₂) (ζ₁ + ζ₂) p =
      gaugeFixedFlatOperator o ρ e hkl b χ δb₁ ζ₁ p +
        gaugeFixedFlatOperator o ρ e hkl b χ δb₂ ζ₂ p := by
  rw [gaugeFixedFlatOperator_apply, gaugeFixedFlatOperator_apply, gaugeFixedFlatOperator_apply]
  refine Prod.ext (flatDeformationGauge_add χ ζ₁ ζ₂ hb₁ hb₂) <|
    Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp only [Prod.snd_add, Prod.fst_add, Submodule.coe_add, flatDeformationCurvature,
      Pi.add_apply, extDeriv_add hb₁ hb₂, neg_add, map_add, smul_add]
    abel
  · simp only [Prod.snd_add, Submodule.coe_add, flatDeformationDirac_eq_coe_flatChiralDirac_add,
      flatChiralDirac_add b hζ₁ hζ₂]
    simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply, add_smul, map_add,
      Submodule.coe_add, Finset.sum_add_distrib]
    abel

/-- `gaugeFixedFlatOperator` commutes with real scalar multiplication of `(δb, ζ)`. -/
theorem gaugeFixedFlatOperator_smul (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (r : ℝ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ (r • δb) (r • ζ) p =
      r • gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p := by
  rw [gaugeFixedFlatOperator_apply, gaugeFixedFlatOperator_apply]
  refine Prod.ext (flatDeformationGauge_smul r δb χ ζ p) <|
    Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp only [Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul, flatDeformationCurvature,
      Pi.smul_apply, extDeriv_smul, ← smul_neg, map_smul, smul_add]
    module
  · have hζ : r • ζ = (r : ℂ) • ζ := funext fun q ↦ (Complex.coe_smul (r : ℝ) (ζ q)).symm
    simp only [Prod.smul_snd, Submodule.coe_smul_of_tower]
    rw [flatDeformationDirac_eq_coe_flatChiralDirac_add,
      flatDeformationDirac_eq_coe_flatChiralDirac_add, hζ, flatChiralDirac_smul,
      Complex.coe_smul, Submodule.coe_smul_of_tower, smul_add, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      ← mul_smul, ← Complex.coe_smul, map_smul, Submodule.coe_smul_of_tower, ofReal_mul, mul_assoc]

/-- `gaugeFixedFlatOperator` sends the zero perturbation to zero. -/
@[simp] theorem gaugeFixedFlatOperator_zero (hkl : 2 + 2 = finrank ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ 0 0 p = 0 := by
  simp [gaugeFixedFlatOperator_apply]

end TauCeti.SeibergWitten
