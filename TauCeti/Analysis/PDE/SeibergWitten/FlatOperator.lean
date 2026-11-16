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
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# The flat four-dimensional Seiberg–Witten operators and their linearization

On an oriented four-dimensional real inner product space `V` with Clifford module `W = W⁺ ⊕ W⁻`
and compatible almost complex structure `J`, this file defines the flat chiral Dirac operator
`flatDirac` (`D_b χ = ∑ₖ c(eₖ) ∇_{b, eₖ} χ`) built from `spinorCovariantDeriv`, the unit-symbol
self-dual curvature defect `flatCurvatureDefect`, their Fréchet/directional linearizations
`linearizedFlatCurvature` and `linearizedFlatDirac` (`hasDerivAt_flatCurvatureDefect`,
`hasDerivAt_flatDirac`), the formal infinitesimal gauge-fixing adjoint `flatGaugeAdjoint`
(`mul_flatGaugeAdjoint_eq`), and the combined eight-real-component linearized gauge-fixed operator
`gaugeFixedFlatOperator`, together with orthonormal-frame independence and `ℂ`-linearity of
`flatDirac`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open CliffordAlgebra Complex Module exteriorPower
open scoped RealInnerProductSpace InnerProductSpace ComplexConjugate

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

attribute [local instance] finiteDimensional_of_finrank_four

/-- Scoped shorthand for continuous real `1`-forms on `V`. -/
scoped notation "OneForm(" V ")" => ((V) [⋀^Fin 1]→L[ℝ] ℝ)
/-- Scoped shorthand for the `+1`-eigenspace `Λ⁺ V` of the Hodge star on `⋀[ℝ]^2 V`. -/
scoped notation "SD(" V ", " o ", " hkl ")" =>
  (Module.End.eigenspace (Orientation.hodgeStar (o) (hkl) : Module.End ℝ (⋀[ℝ]^2 (V))) 1)
/-- Scoped shorthand for the positive half-spinor space `W⁺`. -/
scoped notation "PosSpin(" o ", " ρ ")" => (positiveHalfSpinors (o) (ρ))
/-- Scoped shorthand for the negative half-spinor space `W⁻`. -/
scoped notation "NegSpin(" Q ", " o ", " ρ ")" =>
  (Module.End.eigenspace ((ρ) (chirality (Q) (o))) (-1))
/-- Scoped shorthand for odd Clifford multiplication `W⁺ → W⁻` via
`CliffordAlgebra.halfSpinCliffordMul o ρ 1` and `positiveHalfSpinors_eq_eigenspace`. -/
scoped notation "cMul(" o ", " ρ ", " v ", " ψ ")" =>
  (CliffordAlgebra.halfSpinCliffordMul (o) (ρ) 1 (v)
    (LinearEquiv.ofEq _ _ (CliffordAlgebra.positiveHalfSpinors_eq_eigenspace (o) (ρ)) (ψ)))

omit [FiniteDimensional ℂ W] in
private def cliffordMulRightBilin (T : V →ₗ[ℝ] PosSpin(o, ρ)) :
    V →ₗ[ℝ] V →ₗ[ℝ] NegSpin(Q, o, ρ) :=
  LinearMap.mk₂ ℝ (fun u v ↦ cMul(o, ρ, u, T v))
    (fun _ _ _ ↦ by rw [map_add, LinearMap.add_apply])
    (fun _ _ _ ↦ by rw [map_smul, LinearMap.smul_apply])
    (fun _ _ _ ↦ by simp only [map_add])
    (fun _ _ _ ↦ by rw [map_smul, ← Complex.coe_smul, map_smul, map_smul, Complex.coe_smul])

omit [FiniteDimensional ℂ W] in
/-- **Covariant derivative of a positive half-spinor field** `∇_a χ = dχ + i b χ` for `a = i b`. -/
def spinorCovariantDeriv (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ)) (p : V) :
    V →L[ℝ] PosSpin(o, ρ) :=
  fderiv ℝ χ p +
    ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (b p)).smulRight (I • χ p)
omit [FiniteDimensional ℂ W] in @[simp] theorem spinorCovariantDeriv_apply (b : V → OneForm(V))
    (χ : V → PosSpin(o, ρ)) (p v : V) :
    spinorCovariantDeriv b χ p v = fderiv ℝ χ p v + b p (fun _ ↦ v) • (I • χ p) := by
  simp [spinorCovariantDeriv, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply]
omit [FiniteDimensional ℂ W] in
/-- `spinorCovariantDeriv` is additive in the spinor field at a point of differentiability. -/
theorem spinorCovariantDeriv_add (b : V → OneForm(V)) {χ₁ χ₂ : V → PosSpin(o, ρ)} {p : V}
    (h₁ : DifferentiableAt ℝ χ₁ p) (h₂ : DifferentiableAt ℝ χ₂ p) :
    spinorCovariantDeriv b (χ₁ + χ₂) p =
      spinorCovariantDeriv b χ₁ p + spinorCovariantDeriv b χ₂ p :=
  ContinuousLinearMap.ext fun v ↦ by simp [fderiv_add h₁ h₂, smul_add]; abel
omit [FiniteDimensional ℂ W] in
/-- `spinorCovariantDeriv` is `ℂ`-homogeneous in the spinor field for constant complex scalars. -/
theorem spinorCovariantDeriv_smul (b : V → OneForm(V)) (c : ℂ) (χ : V → PosSpin(o, ρ)) (p : V) :
    spinorCovariantDeriv b (c • χ) p = c • spinorCovariantDeriv b χ p :=
  ContinuousLinearMap.ext fun v ↦ by
    simp only [smul_apply, spinorCovariantDeriv_apply, fderiv_const_smul_field, Pi.smul_apply,
      ← Complex.coe_smul]; module
omit [FiniteDimensional ℂ W] in
/-- Along a constant spinor direction `ψ₀`, `spinorCovariantDeriv` acts via `covariantDeriv b`. -/
theorem spinorCovariantDeriv_smul_const (b : V → OneForm(V)) {α : V → ℂ} {p : V}
    (hα : DifferentiableAt ℝ α p) (ψ₀ : PosSpin(o, ρ)) (v : V) :
    spinorCovariantDeriv b (fun q ↦ α q • ψ₀) p v = covariantDeriv b α p v • ψ₀ := by
  let L : ℂ →L[ℝ] PosSpin(o, ρ) := ((ContinuousLinearMap.id ℂ ℂ).smulRight ψ₀).restrictScalars ℝ
  have hf : fderiv ℝ (fun q ↦ α q • ψ₀) p v = fderiv ℝ α p v • ψ₀ := by
    rw [show (fun q ↦ α q • ψ₀) = L ∘ α from funext fun _ ↦ by simp [L],
      (L.hasFDerivAt.comp p hα.hasFDerivAt).fderiv]; simp [L]
  rw [spinorCovariantDeriv_apply, hf, covariantDeriv_apply, add_smul, ← Complex.coe_smul,
    smul_smul, smul_smul]; congr 2; ring
omit [FiniteDimensional ℂ W] in variable (o ρ e) in
/-- **The flat chiral Dirac operator** `D_b χ = ∑ₖ c(eₖ) ∇_{b, eₖ} χ : W⁺ → W⁻`. -/
def flatDirac (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ)) (p : V) : NegSpin(Q, o, ρ) :=
  ∑ k, cMul(o, ρ, e k, spinorCovariantDeriv b χ p (e k))
omit [FiniteDimensional ℂ W] in @[simp] theorem coe_flatDirac (b : V → OneForm(V))
    (χ : V → PosSpin(o, ρ)) (p : V) :
    (flatDirac o ρ e b χ p : W) = ∑ k, ρ (ι Q (e k)) (spinorCovariantDeriv b χ p (e k)) := by
  simp [flatDirac]
omit [FiniteDimensional ℂ W] in
/-- `flatDirac` is independent of the choice of orthonormal basis of `V`. -/
theorem flatDirac_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ)) (p : V) :
    flatDirac o ρ e b χ p = flatDirac o ρ e' b χ p :=
  e.sum_apply_self_eq e' (cliffordMulRightBilin (spinorCovariantDeriv b χ p).toLinearMap)
omit [FiniteDimensional ℂ W] in
/-- `flatDirac` is additive in the spinor field at a point of differentiability. -/
theorem flatDirac_add (b : V → OneForm(V)) {χ₁ χ₂ : V → PosSpin(o, ρ)} {p : V}
    (h₁ : DifferentiableAt ℝ χ₁ p) (h₂ : DifferentiableAt ℝ χ₂ p) :
    flatDirac o ρ e b (χ₁ + χ₂) p = flatDirac o ρ e b χ₁ p + flatDirac o ρ e b χ₂ p := by
  simp [flatDirac, spinorCovariantDeriv_add b h₁ h₂, Finset.sum_add_distrib]
omit [FiniteDimensional ℂ W] in
/-- `flatDirac` is `ℂ`-homogeneous in the spinor field for constant complex scalars. -/
theorem flatDirac_smul (b : V → OneForm(V)) (c : ℂ) (χ : V → PosSpin(o, ρ)) (p : V) :
    flatDirac o ρ e b (c • χ) p = c • flatDirac o ρ e b χ p := by
  simp [flatDirac, spinorCovariantDeriv_smul, Finset.smul_sum]
omit [FiniteDimensional ℂ W] in
/-- Action of `flatDirac` on a scalar multiple `α • ψ₀` of a constant positive half-spinor. -/
theorem coe_flatDirac_smul_const (b : V → OneForm(V)) {α : V → ℂ} {p : V}
    (hα : DifferentiableAt ℝ α p) (ψ₀ : PosSpin(o, ρ)) :
    (flatDirac o ρ e b (fun q ↦ α q • ψ₀) p : W) =
      ∑ k, covariantDeriv b α p (e k) • ρ (ι Q (e k)) ψ₀ := by
  simp [spinorCovariantDeriv_smul_const b hα]
variable (o) in
/-- **Unit-symbol self-dual projection** `F ↦ (√2 / 2) (F + ⋆F) ∈ Λ⁺ V`. -/
def selfDualTwoVector (hkl : 2 + 2 = finrank ℝ V) : ⋀[ℝ]^2 V →L[ℝ] SD(V, o, hkl) :=
  LinearMap.toContinuousLinearMap
    { toFun F := ⟨(√2 / 2 : ℝ) • (F + o.hodgeStar hkl F), Module.End.mem_eigenspace_iff.2 <| by
        simp [o.hodgeStar_hodgeStar_of_even even_two hkl, add_comm]⟩
      map_add' _ _ := Subtype.ext <| by simp only [Submodule.coe_add, map_add]; module
      map_smul' _ _ := Subtype.ext <| by
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]; module }
@[simp] theorem coe_selfDualTwoVector (hkl : 2 + 2 = finrank ℝ V) (F : ⋀[ℝ]^2 V) :
    (selfDualTwoVector o hkl F : ⋀[ℝ]^2 V) = (√2 / 2 : ℝ) • (F + o.hodgeStar hkl F) := (rfl)
variable (o ρ J) in
/-- **Self-dual curvature defect** `(√2 / 2) (F + ⋆F - ω / 8 + q(χ) / 2) ∈ Λ⁺ V`, `F = -db`. -/
def flatCurvatureDefect (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ)) (p : V) : SD(V, o, hkl) :=
  selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm (-extDeriv b p)) -
    (8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃ + (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p)
theorem flatCurvatureDefect_apply (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ)) (p : V) :
    flatCurvatureDefect o ρ J hkl he h₀ h₂₃ b χ p =
      selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm (-extDeriv b p)) -
        (8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃ +
        (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p) := (rfl)
/-- `flatCurvatureDefect` vanishes iff `F + ⋆F = ω / 8 - q(χ) / 2` for `F = -db`. -/
theorem flatCurvatureDefect_eq_zero_iff (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ)) (p : V) :
    flatCurvatureDefect o ρ J hkl he h₀ h₂₃ b χ p = 0 ↔
      let F := (alternatingFormEquiv V 2).symm (-extDeriv b p)
      F + o.hodgeStar hkl F =
        (8⁻¹ : ℝ) • J.kahlerForm - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (χ p) : ⋀[ℝ]^2 V) := by
  set F := (alternatingFormEquiv V 2).symm (-extDeriv b p)
  rw [← Submodule.coe_eq_zero, show (flatCurvatureDefect o ρ J hkl he h₀ h₂₃ b χ p : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • ((F + o.hodgeStar hkl F) - ((8⁻¹ : ℝ) • J.kahlerForm -
        (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (χ p) : ⋀[ℝ]^2 V))) by
    simp only [flatCurvatureDefect, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      coe_selfDualTwoVector, coe_kahlerSelfDual, F]; module,
    smul_eq_zero_iff_right (by positivity), sub_eq_zero]
variable (o ρ) in
/-- **Linearized self-dual curvature operator** `(√2 / 2) (δF + ⋆δF) + (√2 / 4) q'(χ, ζ)`. -/
def linearizedFlatCurvature (hkl : 2 + 2 = finrank ℝ V) (χ : V → PosSpin(o, ρ))
    (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) : SD(V, o, hkl) :=
  selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm (-extDeriv δb p)) +
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (χ p) (ζ p)
theorem linearizedFlatCurvature_apply (hkl : 2 + 2 = finrank ℝ V) (χ : V → PosSpin(o, ρ))
    (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) :
    linearizedFlatCurvature o ρ hkl χ δb ζ p =
      selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm (-extDeriv δb p)) +
        (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (χ p) (ζ p) := (rfl)
omit [FiniteDimensional ℂ W] in variable (o ρ e) in
/-- **Linearized chiral Dirac operator** `D_b ζ + ∑ₖ c(eₖ) (i δb(eₖ) χ)`. -/
def linearizedFlatDirac (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ))
    (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) : NegSpin(Q, o, ρ) :=
  flatDirac o ρ e b ζ p + ∑ k, cMul(o, ρ, e k, δb p (fun _ ↦ e k) • (I • χ p))
omit [FiniteDimensional ℂ W] in theorem linearizedFlatDirac_apply (b : V → OneForm(V))
    (χ : V → PosSpin(o, ρ)) (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) :
    linearizedFlatDirac o ρ e b χ δb ζ p =
      flatDirac o ρ e b ζ p + ∑ k, cMul(o, ρ, e k, δb p (fun _ ↦ e k) • (I • χ p)) := (rfl)
omit [FiniteDimensional ℂ W] in
/-- `linearizedFlatDirac` is independent of the choice of orthonormal basis of `V`. -/
theorem linearizedFlatDirac_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ))
    (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) :
    linearizedFlatDirac o ρ e b χ δb ζ p = linearizedFlatDirac o ρ e' b χ δb ζ p := by
  let T := (((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (δb p)).smulRight
    (I • χ p)).toLinearMap
  exact congrArg₂ (· + ·) (flatDirac_congr_orthonormalBasis e' b ζ p) <| by
    simpa [T, cliffordMulRightBilin, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply] using
      e.sum_apply_self_eq e' (cliffordMulRightBilin T)
/-- `linearizedFlatCurvature` is the directional derivative of `flatCurvatureDefect` along
`(b + t • δb, χ + t • ζ)` at `t = 0`. -/
theorem hasDerivAt_flatCurvatureDefect (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    {b δb : V → OneForm(V)} (χ ζ : V → PosSpin(o, ρ)) {p : V}
    (hb : DifferentiableAt ℝ b p) (hδb : DifferentiableAt ℝ δb p) :
    HasDerivAt (fun t : ℝ ↦ flatCurvatureDefect o ρ J hkl he h₀ h₂₃ (b + t • δb) (χ + t • ζ) p)
      (linearizedFlatCurvature o ρ hkl χ δb ζ p) 0 := by
  let L := (selfDualTwoVector o hkl).comp
    (LinearEquiv.toContinuousLinearEquiv (alternatingFormEquiv V 2).symm).toContinuousLinearMap
  have hcurv (t : ℝ) : selfDualTwoVector o hkl
      ((alternatingFormEquiv V 2).symm (-extDeriv (b + t • δb) p)) =
      L (-extDeriv b p) + t • L (-extDeriv δb p) := by
    change L (-extDeriv (b + t • δb) p) = L (-extDeriv b p) + t • L (-extDeriv δb p)
    rw [show -extDeriv (b + t • δb) p = -extDeriv b p + t • (-extDeriv δb p) by
      rw [extDeriv_add hb (hδb.const_smul t), extDeriv_smul]; module, map_add, map_smul]
  have hF : HasFDerivAt (quadraticTwoForm o ρ hkl) (quadraticTwoFormPolar o ρ hkl (χ p))
      (χ p + (0 : ℝ) • ζ p) := by simpa using hasFDerivAt_quadraticTwoForm o ρ hkl (χ p)
  exact ((((((hasDerivAt_id (0 : ℝ)).smul_const (L (-extDeriv δb p))).const_add
      (L (-extDeriv b p))).sub_const ((8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃)).fun_add
    ((hF.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const (ζ p)).const_add (χ p)))
      |>.const_smul (√2 / 4 : ℝ))).congr_deriv
    (by simp [L, linearizedFlatCurvature])).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun t ↦ by
      simp only [flatCurvatureDefect, Pi.add_apply, Pi.smul_apply, hcurv t, id_eq,
        Function.comp_apply]
/-- `linearizedFlatDirac` is the directional derivative of `flatDirac` along
`(b + t • δb, χ + t • ζ)` at `t = 0`. -/
theorem hasDerivAt_flatDirac (b δb : V → OneForm(V)) {χ ζ : V → PosSpin(o, ρ)} {p : V}
    (hχ : DifferentiableAt ℝ χ p) (hζ : DifferentiableAt ℝ ζ p) :
    HasDerivAt (fun t : ℝ ↦ flatDirac o ρ e (b + t • δb) (χ + t • ζ) p)
      (linearizedFlatDirac o ρ e b χ δb ζ p) 0 := by
  have : FiniteDimensional ℝ PosSpin(o, ρ) := FiniteDimensional.trans ℝ ℂ _
  let C (k : Fin 4) : PosSpin(o, ρ) →L[ℝ] NegSpin(Q, o, ρ) :=
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
  rw [show linearizedFlatDirac o ρ e b χ δb ζ p = ∑ k : Fin 4, C k (d₁ k) by
    simp only [d₁, map_add, Finset.sum_add_distrib]; rfl]
  exact HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) ↦ hterm k

omit [FiniteDimensional ℂ W] in variable (e) in
/-- **Formal adjoint of the 4D infinitesimal gauge action**: `∑ₖ ∂_{eₖ}(δb(eₖ)) + Im⟪χ, ζ⟫ / 4`. -/
def flatGaugeAdjoint (χ : V → PosSpin(o, ρ)) (δb : V → OneForm(V))
    (ζ : V → PosSpin(o, ρ)) (p : V) : ℝ :=
  (∑ k, (fderiv ℝ δb p (e k)) (fun _ ↦ e k)) + (⟪χ p, ζ p⟫_ℂ).im / 4
omit [FiniteDimensional ℂ W] in theorem flatGaugeAdjoint_def (χ : V → PosSpin(o, ρ))
    (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) : flatGaugeAdjoint e χ δb ζ p =
      (∑ k, (fderiv ℝ δb p (e k)) (fun _ ↦ e k)) + (⟪χ p, ζ p⟫_ℂ).im / 4 := (rfl)
omit [FiniteDimensional ℂ W] in
/-- `flatGaugeAdjoint` is independent of the choice of orthonormal basis of `V`. -/
theorem flatGaugeAdjoint_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (χ : V → PosSpin(o, ρ)) (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) :
    flatGaugeAdjoint e χ δb ζ p = flatGaugeAdjoint e' χ δb ζ p := by
  let B := (ContinuousLinearMap.coeLM ℝ).comp
    ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm.toLinearMap.comp
      (fderiv ℝ δb p).toLinearMap)
  exact congrArg (· + _) (e.sum_apply_self_eq e' B)
omit [FiniteDimensional ℂ W] in
/-- Pointwise divergence identity pairing a real gauge generator `f` against `flatGaugeAdjoint`
with the infinitesimal gauge action `(-df, i f χ / 4)`. -/
theorem mul_flatGaugeAdjoint_eq {f : V → ℝ} (χ : V → PosSpin(o, ρ))
    {δb : V → OneForm(V)} (ζ : V → PosSpin(o, ρ)) {p : V}
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
def gaugeFixedFlatOperator (hkl : 2 + 2 = finrank ℝ V) (b : V → OneForm(V))
    (χ : V → PosSpin(o, ρ)) (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) :
    ℝ × SD(V, o, hkl) × NegSpin(Q, o, ρ) :=
  (flatGaugeAdjoint e χ δb ζ p, linearizedFlatCurvature o ρ hkl χ δb ζ p,
   linearizedFlatDirac o ρ e b χ δb ζ p)
theorem gaugeFixedFlatOperator_apply (hkl : 2 + 2 = finrank ℝ V) (b : V → OneForm(V))
    (χ : V → PosSpin(o, ρ)) (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p =
      (flatGaugeAdjoint e χ δb ζ p, linearizedFlatCurvature o ρ hkl χ δb ζ p,
       linearizedFlatDirac o ρ e b χ δb ζ p) := (rfl)
/-- `gaugeFixedFlatOperator` is independent of the choice of orthonormal basis of `V`. -/
theorem gaugeFixedFlatOperator_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (hkl : 2 + 2 = finrank ℝ V) (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ))
    (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) :
    gaugeFixedFlatOperator o ρ e hkl b χ δb ζ p = gaugeFixedFlatOperator o ρ e' hkl b χ δb ζ p := by
  rw [gaugeFixedFlatOperator, gaugeFixedFlatOperator, flatGaugeAdjoint_congr_orthonormalBasis e',
    linearizedFlatDirac_congr_orthonormalBasis e']

end TauCeti.SeibergWitten
