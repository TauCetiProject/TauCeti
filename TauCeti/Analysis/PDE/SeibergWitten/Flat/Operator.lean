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
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import TauCeti.Analysis.InnerProductSpace.Trace.Basic

/-!
# The flat four-dimensional Seiberg–Witten operators and their linearization

On an oriented four-dimensional real inner product space `V` with Clifford module `W = W⁺ ⊕ W⁻`
and compatible almost complex structure `J`, this file defines the chiral restriction
`flatChiralDirac` of `TauCeti.SeibergWitten.flatDirac` (a first-order operator on positive
half-spinor fields producing negative half-spinor fields, evaluated at `p`), the flat curvature
`flatCurvature` and unit-symbol self-dual curvature defect `flatCurvatureDefect`, the
gauge-fixing, curvature, and Dirac rows `flatDeformationGauge`, `flatDeformationCurvature`, and
`flatDeformationDirac` of the linearized equations (`hasDerivAt_flatCurvatureDefect`,
`hasDerivAt_flatChiralDirac`, `mul_flatDeformationGauge_eq`), and the combined
eight-real-component linearized gauge-fixed operator `gaugeFixedFlatOperator`, together with
orthonormal-frame independence and linearity properties.

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

private theorem covariantDeriv_coe_positiveHalfSpinors (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (p v : V) :
    covariantDeriv b (fun q ↦ (χ q : W)) p v = (covariantDeriv b χ p v : W) := by
  simp only [covariantDeriv_apply,
    (positiveHalfSpinors o ρ).isClosed_of_finiteDimensional.fderiv_coe_apply,
    Submodule.coe_add, Submodule.coe_smul_of_tower]

variable (o ρ) in
/-- **The flat chiral Dirac operator** `D_b⁺`: a first-order operator on positive half-spinor
fields `χ : V → W⁺` producing negative half-spinor fields in `W⁻`, evaluated at `p : V` as
`TauCeti.SeibergWitten.flatDirac ρ b (fun q ↦ (χ q : W)) p`. -/
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

variable (o ρ) in
/-- The **curvature side of the flat limiting curvature equation** at a pair `(b, ψ)`:
`F + ⋆F + q(ψ) / 2`, with the real curvature `F = -db` read as a two-vector. The flat limiting
curvature equation is `flatCurvature b ψ x = ω / 8` (`flatCurvature_eq_iff`). -/
def flatCurvature (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ : V → positiveHalfSpinors o ρ) (x : V) : ⋀[ℝ]^2 V :=
  (alternatingFormEquiv V 2).symm (-extDeriv b x) +
      o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) +
    (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ψ x) : ⋀[ℝ]^2 V)

theorem flatCurvature_def (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ : V → positiveHalfSpinors o ρ) (x : V) :
    flatCurvature o ρ hkl b ψ x =
      (alternatingFormEquiv V 2).symm (-extDeriv b x) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) +
        (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ψ x) : ⋀[ℝ]^2 V) :=
  (rfl)

/-- The flat limiting curvature equation `flatCurvature b ψ x = ω / 8` is the equation
`F + ⋆F = ω / 8 - q(ψ) / 2` of the rescaled limits. -/
theorem flatCurvature_eq_iff (hkl : 2 + 2 = finrank ℝ V) {b : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ψ : V → positiveHalfSpinors o ρ} {x : V} (ω : ⋀[ℝ]^2 V) :
    flatCurvature o ρ hkl b ψ x = (8⁻¹ : ℝ) • ω ↔
      (alternatingFormEquiv V 2).symm (-extDeriv b x) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
        (8⁻¹ : ℝ) • ω - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ψ x) : ⋀[ℝ]^2 V) := by
  rw [flatCurvature_def, eq_sub_iff_add_eq]

/-- The curvature side of the flat limiting curvature equation is self-dual. -/
@[simp]
theorem hodgeStar_flatCurvature (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ : V → positiveHalfSpinors o ρ) (x : V) :
    o.hodgeStar hkl (flatCurvature o ρ hkl b ψ x) = flatCurvature o ρ hkl b ψ x := by
  rw [flatCurvature_def, map_add, map_add, map_smul,
    o.hodgeStar_hodgeStar_of_even even_two hkl, o.hodgeStar_coe_of_mem_eigenspace_one hkl]
  abel

variable (o ρ J) in
/-- **Self-dual curvature defect** `(√2 / 2) (F + ⋆F - ω / 8 + q(χ) / 2) ∈ Λ⁺ V`, defined as the
self-dual restriction of `(√2 / 2) • (flatCurvature o ρ hkl b χ p - ω / 8)`. -/
def flatCurvatureDefect (hkl : 2 + 2 = finrank ℝ V)
    (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  ⟨(√2 / 2 : ℝ) • (flatCurvature o ρ hkl b χ p - (8⁻¹ : ℝ) • J.kahlerForm),
    Submodule.smul_mem _ _ <| Submodule.sub_mem _
      (Module.End.mem_eigenspace_iff.2 <| by simp [hodgeStar_flatCurvature])
      (Submodule.smul_mem _ _ <| Module.End.mem_eigenspace_iff.2 <| by simp [hω])⟩

/-- Ambient self-dual expression for `flatCurvatureDefect`. -/
@[simp] theorem coe_flatCurvatureDefect (hkl : 2 + 2 = finrank ℝ V)
    (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    (flatCurvatureDefect o ρ J hkl hω b χ p : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • (flatCurvature o ρ hkl b χ p - (8⁻¹ : ℝ) • J.kahlerForm) :=
  (rfl)

/-- Unfolding formula for `flatCurvatureDefect`. -/
theorem flatCurvatureDefect_apply (hkl : 2 + 2 = finrank ℝ V)
    (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatCurvatureDefect o ρ J hkl hω b χ p =
      ⟨(√2 / 2 : ℝ) • (flatCurvature o ρ hkl b χ p - (8⁻¹ : ℝ) • J.kahlerForm),
        Submodule.smul_mem _ _ <| Submodule.sub_mem _
          (Module.End.mem_eigenspace_iff.2 <| by simp [hodgeStar_flatCurvature])
          (Submodule.smul_mem _ _ <| Module.End.mem_eigenspace_iff.2 <| by simp [hω])⟩ :=
  (rfl)

/-- `flatCurvatureDefect` vanishes iff `F + ⋆F = ω / 8 - q(χ) / 2` for `F = -db`. -/
theorem flatCurvatureDefect_eq_zero_iff (hkl : 2 + 2 = finrank ℝ V)
    (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatCurvatureDefect o ρ J hkl hω b χ p = 0 ↔
      let F := (alternatingFormEquiv V 2).symm (-extDeriv b p)
      F + o.hodgeStar hkl F =
        (8⁻¹ : ℝ) • J.kahlerForm - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (χ p) : ⋀[ℝ]^2 V) := by
  rw [← Submodule.coe_eq_zero, coe_flatCurvatureDefect, smul_eq_zero_iff_right (by positivity),
    sub_eq_zero, flatCurvature_eq_iff]

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
  exact (LinearMap.BilinMap.metricTrace_eq_sum B e).symm.trans
    (LinearMap.BilinMap.metricTrace_eq_sum B e')

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

/-- The curvature row of the normal model is linear in the variation `(b', ζ)`: scaling both by
`t` scales the row by `t`. -/
theorem flatDeformationCurvature_smul (hkl : 2 + 2 = finrank ℝ V)
    {b' : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ ζ : V → positiveHalfSpinors o ρ} {x : V} (t : ℝ) :
    flatDeformationCurvature o ρ hkl (t • b') ψ (t • ζ) x =
      t • flatDeformationCurvature o ρ hkl b' ψ ζ x := by
  simp only [flatDeformationCurvature_def, extDeriv_smul, ← smul_neg, map_smul, Pi.smul_apply,
    Submodule.coe_smul, smul_add, smul_comm t (2⁻¹ : ℝ)]

/-- The curvature row of the normal model is additive in the variation `(b', ζ)`, for connection
variations differentiable at the point. -/
theorem flatDeformationCurvature_add (hkl : 2 + 2 = finrank ℝ V)
    {b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} {x : V}
    (hb₁ : DifferentiableAt ℝ b₁ x) (hb₂ : DifferentiableAt ℝ b₂ x) :
    flatDeformationCurvature o ρ hkl (b₁ + b₂) ψ (ζ₁ + ζ₂) x =
      flatDeformationCurvature o ρ hkl b₁ ψ ζ₁ x + flatDeformationCurvature o ρ hkl b₂ ψ ζ₂ x := by
  simp only [flatDeformationCurvature_def, extDeriv_add hb₁ hb₂, Pi.add_apply, neg_add, map_add,
    Submodule.coe_add, smul_add]
  abel

/-- **The exact expansion of the flat curvature equation**: for connection forms `b` and `b'`
differentiable at `x`,

`flatCurvature (b + b') (ψ + ζ) = flatCurvature b ψ + F'_ψ(b', ζ) + q(ζ) / 2`,

where `F'` is the curvature row of the normal model (`flatDeformationCurvature`). -/
theorem flatCurvature_add (hkl : 2 + 2 = finrank ℝ V)
    {b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ ζ : V → positiveHalfSpinors o ρ} {x : V}
    (hb : DifferentiableAt ℝ b x) (hb' : DifferentiableAt ℝ b' x) :
    flatCurvature o ρ hkl (b + b') (ψ + ζ) x =
      flatCurvature o ρ hkl b ψ x + flatDeformationCurvature o ρ hkl b' ψ ζ x +
        (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ x) : ⋀[ℝ]^2 V) := by
  rw [flatCurvature_def, flatCurvature_def, flatDeformationCurvature_def, extDeriv_add hb hb',
    Pi.add_apply, quadraticTwoForm_add]
  simp only [neg_add, map_add, Submodule.coe_add, smul_add]
  abel

/-- **The flat curvature equation along a line is quadratic**: for connection forms `b` and `b'`
differentiable at `x` and every real `t`,

`flatCurvature (b + t b') (ψ + t ζ) = flatCurvature b ψ + t F'_ψ(b', ζ) + t² q(ζ) / 2`. -/
theorem flatCurvature_add_smul (hkl : 2 + 2 = finrank ℝ V)
    {b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ ζ : V → positiveHalfSpinors o ρ} {x : V}
    (hb : DifferentiableAt ℝ b x) (hb' : DifferentiableAt ℝ b' x) (t : ℝ) :
    flatCurvature o ρ hkl (b + t • b') (ψ + t • ζ) x =
      flatCurvature o ρ hkl b ψ x + t • flatDeformationCurvature o ρ hkl b' ψ ζ x +
        t ^ 2 • (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ x) : ⋀[ℝ]^2 V) := by
  have hq : quadraticTwoForm o ρ hkl ((t • ζ) x) = t ^ 2 • quadraticTwoForm o ρ hkl (ζ x) := by
    rw [Pi.smul_apply, ← Complex.coe_smul, quadraticTwoForm_smul, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [flatCurvature_add hkl hb (hb'.const_smul t), flatDeformationCurvature_smul, hq,
    Submodule.coe_smul, smul_comm (2⁻¹ : ℝ)]

/-- **The curvature row of the normal model is the first variation of the flat curvature
equation**: for connection forms differentiable at `x`, the derivative of
`t ↦ flatCurvature (b + t b') (ψ + t ζ) x` at `t = 0` is `flatDeformationCurvature` at `ψ`
applied to `(b', ζ)`. -/
theorem hasDerivAt_flatCurvature_add_smul (hkl : 2 + 2 = finrank ℝ V)
    {b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ ζ : V → positiveHalfSpinors o ρ} {x : V}
    (hb : DifferentiableAt ℝ b x) (hb' : DifferentiableAt ℝ b' x) :
    HasDerivAt (fun t : ℝ ↦ flatCurvature o ρ hkl (b + t • b') (ψ + t • ζ) x)
      (flatDeformationCurvature o ρ hkl b' ψ ζ x) 0 := by
  simp_rw [flatCurvature_add_smul hkl hb hb']
  exact hasDerivAt_add_smul_add_sq_smul _ _ _

private theorem hasDerivAt_submodule {𝕜' F : Type*} [NontriviallyNormedField 𝕜']
    [NormedAlgebra ℝ 𝕜'] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜' F]
    [IsScalarTower ℝ 𝕜' F] {S : Submodule 𝕜' F} {g : ℝ → S} {d : S} {t₀ : ℝ}
    (hg : HasDerivAt (fun t ↦ (g t : F)) (d : F) t₀) :
    HasDerivAt g d t₀ := by
  let incl : S →L[ℝ] F := S.subtypeL.restrictScalars ℝ
  have hcomp : incl.comp (ContinuousLinearMap.toSpanSingleton ℝ d) =
      ContinuousLinearMap.toSpanSingleton ℝ (d : F) := by
    ext; simp [incl]
  simpa using (HasFDerivAt.of_comp_of_isEmbedding (f := incl) (f' := incl) (g := g)
    (g' := ContinuousLinearMap.toSpanSingleton ℝ d)
    (Topology.IsEmbedding.subtypeVal.continuousAt_iff.2 hg.continuousAt)
    incl.hasFDerivAt Topology.IsEmbedding.subtypeVal
    (by rw [hcomp]; exact hg.hasFDerivAt) Filter.EventuallyEq.rfl).hasDerivAt

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
          exact hodgeStar_flatDeformationCurvature hkl δb χ ζ p)⟩ 0 :=
  hasDerivAt_submodule <| by
    simpa only [coe_flatCurvatureDefect, Pi.smul_def] using
      ((hasDerivAt_flatCurvature_add_smul hkl hb hδb).sub_const
        ((8⁻¹ : ℝ) • J.kahlerForm)).const_smul (√2 / 2 : ℝ)

section

omit [FiniteDimensional ℂ W]

private theorem coe_comp_add (ψ ζ : V → positiveHalfSpinors o ρ) :
    (fun y ↦ ((ψ + ζ) y : W)) = (fun y ↦ (ψ y : W)) + fun y ↦ (ζ y : W) :=
  rfl

private theorem coe_comp_smul (t : ℝ) (ζ : V → positiveHalfSpinors o ρ) :
    (fun y ↦ ((t • ζ) y : W)) = (t : ℂ) • fun y ↦ (ζ y : W) :=
  funext fun _ ↦ (Complex.coe_smul t _).symm

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

variable (ρ) in
/-- **The Dirac row of the normal model through the flat Dirac operator**:
`flatDeformationDirac` at `(b, ψ)` applied to `(b', ζ)` is `D_b ζ + i c(b') ψ`, the flat Dirac
operator of `ζ` plus the Clifford multiplication of `ψ` by `b'`. -/
theorem flatDeformationDirac_eq_flatDirac_add_flatDirac (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (x : V) :
    flatDeformationDirac e b b' ψ ζ x =
      flatDirac ρ b (fun y ↦ (ζ y : W)) x + flatDirac ρ b' (fun _ ↦ (ψ x : W)) x := by
  rw [flatDeformationDirac_def, flatDirac_eq_sum ρ e, flatDirac_eq_sum ρ e,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [covariantDeriv_apply, fderiv_fun_const, Pi.zero_apply, zero_apply, zero_add,
    ← map_add, mul_comm I, mul_smul, Complex.coe_smul]

/-- The Dirac row of the normal model is linear in the variation `(b', ζ)`: scaling both by
`t` scales the row by `t`. -/
theorem flatDeformationDirac_smul {b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ψ ζ : V → positiveHalfSpinors o ρ} {x : V} (t : ℝ) :
    flatDeformationDirac e b (t • b') ψ (t • ζ) x = t • flatDeformationDirac e b b' ψ ζ x := by
  rw [flatDeformationDirac_eq_flatDirac_add_flatDirac ρ, coe_comp_smul, flatDirac_smul,
    Complex.coe_smul, flatDirac_smul_connection_const,
    flatDeformationDirac_eq_flatDirac_add_flatDirac ρ, smul_add]

/-- The Dirac row of the normal model is additive in the variation `(b', ζ)`, for spinor
variations differentiable at the point. -/
theorem flatDeformationDirac_add {b b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ψ ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} {x : V}
    (hζ₁ : DifferentiableAt ℝ (fun y ↦ (ζ₁ y : W)) x)
    (hζ₂ : DifferentiableAt ℝ (fun y ↦ (ζ₂ y : W)) x) :
    flatDeformationDirac e b (b₁ + b₂) ψ (ζ₁ + ζ₂) x =
      flatDeformationDirac e b b₁ ψ ζ₁ x + flatDeformationDirac e b b₂ ψ ζ₂ x := by
  simp only [flatDeformationDirac_eq_flatDirac_add_flatDirac ρ]
  rw [coe_comp_add, flatDirac_add ρ hζ₁ hζ₂, flatDirac_add_connection]
  abel

variable (e) in
/-- **The exact expansion of the flat Dirac operator**: for spinor fields `ψ` and `ζ`
differentiable at `x`,

`D_{b + b'} (ψ + ζ) = D_b ψ + D'_{(b, ψ)}(b', ζ) + i c(b') ζ`,

where `D'` is the Dirac row of the normal model (`flatDeformationDirac`) and the remainder
`i c(b') ζ` is the flat Dirac operator of the constant field with value `ζ x` for the
connection `b'`. -/
theorem flatDirac_add_eq_add_flatDeformationDirac_add
    {b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ ζ : V → positiveHalfSpinors o ρ} {x : V}
    (hψ : DifferentiableAt ℝ (fun y ↦ (ψ y : W)) x)
    (hζ : DifferentiableAt ℝ (fun y ↦ (ζ y : W)) x) :
    flatDirac ρ (b + b') (fun y ↦ ((ψ + ζ) y : W)) x =
      flatDirac ρ b (fun y ↦ (ψ y : W)) x + flatDeformationDirac e b b' ψ ζ x +
        flatDirac ρ b' (fun _ ↦ (ζ x : W)) x := by
  have hconst : flatDirac ρ b' (fun _ ↦ (ψ x : W) + (ζ x : W)) x =
      flatDirac ρ b' (fun _ ↦ (ψ x : W)) x + flatDirac ρ b' (fun _ ↦ (ζ x : W)) x :=
    flatDirac_add ρ (differentiableAt_const _) (differentiableAt_const _)
  rw [coe_comp_add, flatDirac_add_connection, flatDirac_add ρ hψ hζ, Pi.add_apply, hconst,
    flatDeformationDirac_eq_flatDirac_add_flatDirac ρ]
  abel

variable (e) in
/-- **The flat Dirac operator along a line is quadratic**: for spinor fields `ψ` and `ζ`
differentiable at `x` and every real `t`,

`D_{b + t b'} (ψ + t ζ) = D_b ψ + t D'_{(b, ψ)}(b', ζ) + t² i c(b') ζ`. -/
theorem flatDirac_add_smul {b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ ζ : V → positiveHalfSpinors o ρ}
    {x : V} (hψ : DifferentiableAt ℝ (fun y ↦ (ψ y : W)) x)
    (hζ : DifferentiableAt ℝ (fun y ↦ (ζ y : W)) x) (t : ℝ) :
    flatDirac ρ (b + t • b') (fun y ↦ ((ψ + t • ζ) y : W)) x =
      flatDirac ρ b (fun y ↦ (ψ y : W)) x + t • flatDeformationDirac e b b' ψ ζ x +
        t ^ 2 • flatDirac ρ b' (fun _ ↦ (ζ x : W)) x := by
  have htζ : DifferentiableAt ℝ (fun y ↦ ((t • ζ) y : W)) x := by
    rw [coe_comp_smul]
    exact hζ.const_smul _
  have hconst : (fun _ : V ↦ ((t • ζ) x : W)) = (t : ℂ) • fun _ ↦ (ζ x : W) :=
    coe_comp_smul t fun _ ↦ ζ x
  rw [flatDirac_add_eq_add_flatDeformationDirac_add e hψ htζ, flatDeformationDirac_smul, hconst,
    flatDirac_smul, Complex.coe_smul, flatDirac_smul_connection_const, smul_smul, ← sq]

variable (e) in
/-- **The Dirac row of the normal model is the first variation of the flat Dirac operator**:
for spinor fields differentiable at `x`, the derivative of `t ↦ D_{b + t b'} (ψ + t ζ)` at `x`
at `t = 0` is `flatDeformationDirac` at `(b, ψ)` applied to `(b', ζ)`. -/
theorem hasDerivAt_flatDirac_add_smul {b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ψ ζ : V → positiveHalfSpinors o ρ} {x : V}
    (hψ : DifferentiableAt ℝ (fun y ↦ (ψ y : W)) x)
    (hζ : DifferentiableAt ℝ (fun y ↦ (ζ y : W)) x) :
    HasDerivAt (fun t : ℝ ↦ flatDirac ρ (b + t • b') (fun y ↦ ((ψ + t • ζ) y : W)) x)
      (flatDeformationDirac e b b' ψ ζ x) 0 := by
  simp_rw [flatDirac_add_smul e hψ hζ]
  exact hasDerivAt_add_smul_add_sq_smul _ _ _

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
    ← covariantDeriv_coe_positiveHalfSpinors, covariantDeriv_apply,
    (positiveHalfSpinors o ρ).isClosed_of_finiteDimensional.fderiv_coe_apply]
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
      (LinearMap.BilinMap.metricTrace_eq_sum B e).symm.trans
        (LinearMap.BilinMap.metricTrace_eq_sum B e')
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
        mem_eigenspace_flatDeformationDirac b δb χ ζ p⟩ 0 :=
  hasDerivAt_submodule <| hasDerivAt_flatDirac_add_smul e
    (((positiveHalfSpinors o ρ).subtypeL.restrictScalars ℝ).differentiableAt.comp p hχ)
    (((positiveHalfSpinors o ρ).subtypeL.restrictScalars ℝ).differentiableAt.comp p hζ)

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
  have hζ₁' : DifferentiableAt ℝ (fun q ↦ (ζ₁ q : W)) p :=
    ((positiveHalfSpinors o ρ).subtypeL.restrictScalars ℝ).differentiableAt.comp p hζ₁
  have hζ₂' : DifferentiableAt ℝ (fun q ↦ (ζ₂ q : W)) p :=
    ((positiveHalfSpinors o ρ).subtypeL.restrictScalars ℝ).differentiableAt.comp p hζ₂
  rw [gaugeFixedFlatOperator_apply, gaugeFixedFlatOperator_apply, gaugeFixedFlatOperator_apply]
  refine Prod.ext (flatDeformationGauge_add χ ζ₁ ζ₂ hb₁ hb₂) <|
    Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp only [Prod.snd_add, Prod.fst_add, Submodule.coe_add,
      flatDeformationCurvature_add hkl hb₁ hb₂, smul_add]
  · simp only [Prod.snd_add, Submodule.coe_add, flatDeformationDirac_add hζ₁' hζ₂']

/-- `gaugeFixedFlatOperator` commutes with real scalar multiplication of `(δb, ζ)`. -/
theorem gaugeFixedFlatOperator_smul (hkl : 2 + 2 = finrank ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (r : ℝ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ (r • δb) (r • ζ) p =
      r • gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p := by
  rw [gaugeFixedFlatOperator_apply, gaugeFixedFlatOperator_apply]
  refine Prod.ext (flatDeformationGauge_smul r δb χ ζ p) <|
    Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp only [Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul,
      flatDeformationCurvature_smul hkl r, smul_comm r (√2 / 2 : ℝ)]
  · simp only [Prod.smul_snd, Submodule.coe_smul_of_tower, flatDeformationDirac_smul r]

/-- `gaugeFixedFlatOperator` sends the zero perturbation to zero. -/
@[simp] theorem gaugeFixedFlatOperator_zero (hkl : 2 + 2 = finrank ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ 0 0 p = 0 := by
  simp [gaugeFixedFlatOperator_apply]

end TauCeti.SeibergWitten
