/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.FlatLimit
public import TauCeti.Analysis.PDE.SeibergWitten.Normal.Frame
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# The gauge-fixed flat Seiberg–Witten operator and normal intertwining

On an abstract oriented four-dimensional real inner product space `V` with almost complex structure
`J`, an adapted orthonormal frame `e` splits `V` into tangential and normal complex planes via
`normalCoord e : V → ℂ`. Pulling back `x` gives a canonical-line background solving the flat
Seiberg–Witten equations iff `Vortex.equation x = 0`.

To reduce the linearized four-dimensional Seiberg–Witten problem along the normal plane to the
plane-vortex model, we define the nonlinear flat Dirac and curvature-defect maps alongside the
eight-real-component linearized gauge-fixed operator, and prove that at any background `x` it
intertwines normal perturbations from `(y, η)` with `(L_x y, L_x* η)`.

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

/-! ### The gauge-fixed flat Seiberg–Witten operator and its linearization -/

section FlatOperator

omit [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] in
private def cliffordMulRightBilin (T : V →ₗ[ℝ] PosSpin(o, ρ)) :
    V →ₗ[ℝ] V →ₗ[ℝ] NegSpin(Q, o, ρ) :=
  LinearMap.mk₂ ℝ (fun u v ↦ cMul(o, ρ) u (T v))
    (fun _ _ _ ↦ Subtype.ext <| by simp [coe_positiveHalfSpinCliffordMul_apply, map_add])
    (fun _ _ _ ↦ Subtype.ext <| by simp [coe_positiveHalfSpinCliffordMul_apply, map_smul])
    (fun _ _ _ ↦ by rw [map_add, map_add])
    (fun _ _ _ ↦ by rw [map_smul, ← Complex.coe_smul, map_smul, Complex.coe_smul])
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
/-- Along a constant spinor direction `ψ₀`, `spinorCovariantDeriv` acts via `covariantDeriv b`. -/
theorem spinorCovariantDeriv_smul_const (b : V → OneForm(V)) {α : V → ℂ} {p : V}
    (hα : DifferentiableAt ℝ α p) (ψ₀ : PosSpin(o, ρ)) (v : V) :
    spinorCovariantDeriv b (fun q ↦ α q • ψ₀) p v = covariantDeriv b α p v • ψ₀ := by
  let L : ℂ →L[ℝ] PosSpin(o, ρ) := ((ContinuousLinearMap.id ℂ ℂ).smulRight ψ₀).restrictScalars ℝ
  have hfun : (fun q ↦ α q • ψ₀) = L ∘ α := funext fun _ ↦ by simp [L]
  have hf : fderiv ℝ (fun q ↦ α q • ψ₀) p v = fderiv ℝ α p v • ψ₀ := by
    rw [hfun, (L.hasFDerivAt.comp p hα.hasFDerivAt).fderiv]; simp [L]
  rw [spinorCovariantDeriv_apply, hf, covariantDeriv_apply, add_smul, ← Complex.coe_smul,
    smul_smul, smul_smul]; congr 2; ring
omit [FiniteDimensional ℂ W] in variable (o ρ e) in
/-- **The flat chiral Dirac operator** `D_b χ = ∑ₖ c(eₖ) ∇_{b, eₖ} χ : W⁺ → W⁻`. -/
def flatDirac (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ)) (p : V) : NegSpin(Q, o, ρ) :=
  ∑ k, cMul(o, ρ) (e k) (spinorCovariantDeriv b χ p (e k))
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
/-- Action of `flatDirac` on a scalar multiple `α • ψ₀` of a constant positive half-spinor. -/
theorem coe_flatDirac_smul_const (b : V → OneForm(V)) {α : V → ℂ} {p : V}
    (hα : DifferentiableAt ℝ α p) (ψ₀ : PosSpin(o, ρ)) :
    (flatDirac o ρ e b (fun q ↦ α q • ψ₀) p : W) =
      ∑ k, covariantDeriv b α p (e k) • ρ (ι Q (e k)) ψ₀ := by
  rw [coe_flatDirac]; exact Finset.sum_congr rfl fun k _ ↦ by
    rw [spinorCovariantDeriv_smul_const b hα, Submodule.coe_smul, map_smul]
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
      (√2 / 2 : ℝ) • ((F + o.hodgeStar hkl F) -
        ((8⁻¹ : ℝ) • J.kahlerForm - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (χ p) : ⋀[ℝ]^2 V))) by
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
  flatDirac o ρ e b ζ p + ∑ k, cMul(o, ρ) (e k) (δb p (fun _ ↦ e k) • (I • χ p))
omit [FiniteDimensional ℂ W] in theorem linearizedFlatDirac_apply (b : V → OneForm(V))
    (χ : V → PosSpin(o, ρ)) (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) :
    linearizedFlatDirac o ρ e b χ δb ζ p =
      flatDirac o ρ e b ζ p + ∑ k, cMul(o, ρ) (e k) (δb p (fun _ ↦ e k) • (I • χ p)) := (rfl)
omit [FiniteDimensional ℂ W] in
/-- `linearizedFlatDirac` is independent of the choice of orthonormal basis of `V`. -/
theorem linearizedFlatDirac_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (b : V → OneForm(V)) (χ : V → PosSpin(o, ρ))
    (δb : V → OneForm(V)) (ζ : V → PosSpin(o, ρ)) (p : V) :
    linearizedFlatDirac o ρ e b χ δb ζ p = linearizedFlatDirac o ρ e' b χ δb ζ p := by
  let T : V →ₗ[ℝ] PosSpin(o, ρ) := (((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm
    (δb p)).smulRight (I • χ p)).toLinearMap
  rw [linearizedFlatDirac, linearizedFlatDirac, flatDirac_congr_orthonormalBasis e',
    show (∑ k, cMul(o, ρ) (e k) (δb p (fun _ ↦ e k) • (I • χ p))) =
        ∑ k, cMul(o, ρ) (e' k) (δb p (fun _ ↦ e' k) • (I • χ p)) by
      simpa [T, cliffordMulRightBilin, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply] using
        e.sum_apply_self_eq e' (cliffordMulRightBilin T)]
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
    have hed : -extDeriv (b + t • δb) p = -extDeriv b p + t • (-extDeriv δb p) := by
      rw [extDeriv_add hb (hδb.const_smul t), extDeriv_smul]; module
    have hL (ω : V [⋀^Fin 2]→L[ℝ] ℝ) :
        selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm ω) = L ω := by simp [L]
    rw [hL, hed, map_add, map_smul]
  have hd_curv : HasDerivAt (fun t : ℝ ↦ L (-extDeriv b p) + t • L (-extDeriv δb p) -
      (8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃) (L (-extDeriv δb p)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (L (-extDeriv δb p))).const_add
      (L (-extDeriv b p))).sub_const ((8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃)
  have hd_line : HasDerivAt (fun t : ℝ ↦ χ p + t • ζ p) (ζ p) (0 : ℝ) := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ζ p)).const_add (χ p)
  have hF : HasFDerivAt (quadraticTwoForm o ρ hkl) (quadraticTwoFormPolar o ρ hkl (χ p))
      (χ p + (0 : ℝ) • ζ p) := by simpa using hasFDerivAt_quadraticTwoForm o ρ hkl (χ p)
  have hfun : (fun t : ℝ ↦ flatCurvatureDefect o ρ J hkl he h₀ h₂₃ (b + t • δb) (χ + t • ζ) p) =
      fun t : ℝ ↦ (L (-extDeriv b p) + t • L (-extDeriv δb p) -
        (8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃) +
        (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p + t • ζ p) :=
    funext fun t ↦ by simp only [flatCurvatureDefect, Pi.add_apply, Pi.smul_apply, hcurv t]
  rw [hfun]; exact hd_curv.fun_add ((hF.comp_hasDerivAt (0 : ℝ) hd_line).const_smul (√2 / 4 : ℝ))
/-- `linearizedFlatDirac` is the directional derivative of `flatDirac` along
`(b + t • δb, χ + t • ζ)` at `t = 0`. -/
theorem hasDerivAt_flatDirac (b δb : V → OneForm(V)) {χ ζ : V → PosSpin(o, ρ)} {p : V}
    (hχ : DifferentiableAt ℝ χ p) (hζ : DifferentiableAt ℝ ζ p) :
    HasDerivAt (fun t : ℝ ↦ flatDirac o ρ e (b + t • δb) (χ + t • ζ) p)
      (linearizedFlatDirac o ρ e b χ δb ζ p) 0 := by
  have : FiniteDimensional ℝ PosSpin(o, ρ) := FiniteDimensional.trans ℝ ℂ _
  let C (k : Fin 4) : PosSpin(o, ρ) →L[ℝ] NegSpin(Q, o, ρ) :=
    ((cMul(o, ρ) (e k)).restrictScalars ℝ).toContinuousLinearMap
  have hcov (t : ℝ) (k : Fin 4) :
      spinorCovariantDeriv (b + t • δb) (χ + t • ζ) p (e k) = spinorCovariantDeriv b χ p (e k) +
          t • (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)) +
          (t ^ 2) • (δb p (fun _ ↦ e k) • (I • ζ p)) := by
    have hf : fderiv ℝ (χ + t • ζ) p (e k) = fderiv ℝ χ p (e k) + t • fderiv ℝ ζ p (e k) := by
      rw [(hχ.hasFDerivAt.add (hζ.hasFDerivAt.const_smul t)).fderiv, add_apply, smul_apply]
    simp only [spinorCovariantDeriv_apply, hf, Pi.add_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    simp only [← Complex.coe_smul]; push_cast; module
  have hterm (k : Fin 4) :
      HasDerivAt (fun t : ℝ ↦ C k (spinorCovariantDeriv (b + t • δb) (χ + t • ζ) p (e k)))
        (C k (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p))) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const
      (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p))).const_add
      (spinorCovariantDeriv b χ p (e k))
    have h2 := (hasDerivAt_pow 2 (0 : ℝ)).smul_const (δb p (fun _ ↦ e k) • (I • ζ p))
    have hpoly : HasDerivAt (fun t : ℝ ↦ spinorCovariantDeriv b χ p (e k) +
        t • (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)) +
        (t ^ 2) • (δb p (fun _ ↦ e k) • (I • ζ p)))
        (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)) 0 :=
      (h1.fun_add h2).congr_deriv (by simp)
    have hfn : (fun t : ℝ ↦ C k (spinorCovariantDeriv (b + t • δb) (χ + t • ζ) p (e k))) =
        C k ∘ fun t : ℝ ↦ spinorCovariantDeriv b χ p (e k) +
          t • (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)) +
          (t ^ 2) • (δb p (fun _ ↦ e k) • (I • ζ p)) := funext fun t ↦ congrArg (C k) (hcov t k)
    rw [hfn]; exact (C k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hpoly
  have hgoal_eq : (∑ k : Fin 4, C k (spinorCovariantDeriv b ζ p (e k) +
      δb p (fun _ ↦ e k) • (I • χ p))) = linearizedFlatDirac o ρ e b χ δb ζ p := by
    simp only [map_add, Finset.sum_add_distrib]; rfl
  rw [← hgoal_eq]; exact HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) ↦ hterm k
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
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun u := ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm
        (fderiv ℝ δb p u)).toLinearMap
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  have hdiv : (∑ k, (fderiv ℝ δb p (e k)) (fun _ ↦ e k)) =
      ∑ k, (fderiv ℝ δb p (e' k)) (fun _ ↦ e' k) := e.sum_apply_self_eq e' B
  simp only [flatGaugeAdjoint, hdiv]
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
    let evk := ContinuousAlternatingMap.apply ℝ V ℝ (fun _ : Fin 1 ↦ e k)
    have hδbk : HasFDerivAt (fun q ↦ δb q (fun _ ↦ e k)) (evk.comp (fderiv ℝ δb p)) p :=
      evk.hasFDerivAt.comp p hδb.hasFDerivAt
    rw [(hf.hasFDerivAt.fun_mul hδbk).fderiv]
    simp only [evk, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousAlternatingMap.apply_apply, smul_eq_mul]; ring
  have hspin : (⟪f p • (I • χ p), ζ p⟫_ℂ).re = f p * (⟪χ p, ζ p⟫_ℂ).im := by
    rw [← Complex.coe_smul, inner_smul_left, inner_smul_left]
    simp only [conj_ofReal, conj_I, mul_re, neg_re, neg_im, I_re, I_im, ofReal_re, ofReal_im]; ring
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
end FlatOperator

/-! ### Exact eight-component normal intertwining theorem -/

section NormalIntertwining
omit [FiniteDimensional ℂ W] in variable (o ρ e) in
/-- The canonical-line spinor field `p ↦ α(z(p)) u₀` pulled back along `normalCoord e`. -/
def normalSpinor (u₀ : PosSpin(o, ρ)) (x : ℂ → E4) (p : V) : PosSpin(o, ρ) :=
  Vortex.sectionValue x (normalCoord e p) • u₀
omit [FiniteDimensional ℂ W] in theorem normalSpinor_apply (u₀ : PosSpin(o, ρ)) (x : ℂ → E4)
    (p : V) : normalSpinor o ρ e u₀ x p = Vortex.sectionValue x (normalCoord e p) • u₀ := (rfl)
omit [Fact (finrank ℝ V = 4)] in variable (e) in
/-- The connection perturbation pulled back from `(y, η) : ℂ → ℝ⁴ × ℝ⁴` along `normalCoord e`. -/
def normalPerturbationForm (y η : ℂ → E4) (p : V) : OneForm(V) :=
  normalFrameForm e (y (normalCoord e p)) (η (normalCoord e p))
omit [Fact (finrank ℝ V = 4)] in theorem normalPerturbationForm_apply (y η : ℂ → E4) (p : V) :
    normalPerturbationForm e y η p =
      normalFrameForm e (y (normalCoord e p)) (η (normalCoord e p)) := (rfl)
omit [FiniteDimensional ℂ W] in variable (o ρ e) in
/-- The spinor perturbation pulled back from `(y, η) : ℂ → ℝ⁴ × ℝ⁴` along `normalCoord e`. -/
def normalPerturbationSpinor (u₀ : PosSpin(o, ρ)) (y η : ℂ → E4) (p : V) : PosSpin(o, ρ) :=
  normalFrameSpinor o ρ e u₀ (y (normalCoord e p)) (η (normalCoord e p))
omit [FiniteDimensional ℂ W] in theorem normalPerturbationSpinor_apply (u₀ : PosSpin(o, ρ))
    (y η : ℂ → E4) (p : V) : normalPerturbationSpinor o ρ e u₀ y η p =
      normalFrameSpinor o ρ e u₀ (y (normalCoord e p)) (η (normalCoord e p)) := (rfl)
omit [Fact (finrank ℝ V = 4)] in private theorem normalCoord_basis_zero : normalCoord e (e 0) = 0 :=
  by simp [normalCoord_apply, orthonormal_iff_ite.1 e.orthonormal]
omit [Fact (finrank ℝ V = 4)] in private theorem normalCoord_basis_one : normalCoord e (e 1) = 0 :=
  by simp [normalCoord_apply, orthonormal_iff_ite.1 e.orthonormal]
omit [Fact (finrank ℝ V = 4)] in private theorem normalCoord_basis_three :
    normalCoord e (e 3) = I := by simp [normalCoord_apply, orthonormal_iff_ite.1 e.orthonormal]
omit [Fact (finrank ℝ V = 4)] in private theorem hasFDerivAt_coord_comp_normalCoord {f : ℂ → E4}
    {p : V} (hf : DifferentiableAt ℝ f (normalCoord e p)) (i : Fin 4) :
    HasFDerivAt (fun q ↦ f (normalCoord e q) i)
      ((fderiv ℝ (fun w ↦ f w i) (normalCoord e p)).comp (normalCoord e)) p :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hf).hasFDerivAt.comp p
    (normalCoord e).hasFDerivAt
omit [Fact (finrank ℝ V = 4)] in private theorem differentiableAt_normalPerturbationForm
    {y η : ℂ → E4} {p : V} (hy : DifferentiableAt ℝ y (normalCoord e p))
    (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    DifferentiableAt ℝ (normalPerturbationForm e y η) p := by
  have hyi := hasFDerivAt_coord_comp_normalCoord hy
  have hηi := hasFDerivAt_coord_comp_normalCoord hη
  rw [show normalPerturbationForm e y η = fun q ↦ ContinuousAlternatingMap.ofSubsingletonLIE
    (0 : Fin 1) ((-η (normalCoord e q) 0) • innerSL ℝ (e 0) + η (normalCoord e q) 1 •
      innerSL ℝ (e 1) + y (normalCoord e q) 0 • innerSL ℝ (e 2) + y (normalCoord e q) 1 •
      innerSL ℝ (e 3)) from funext fun q ↦ normalFrameForm_eq e _ _]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
    (0 : Fin 1)).differentiableAt.comp p (((((hηi 0).differentiableAt.neg.smul_const _).add
      ((hηi 1).differentiableAt.smul_const _)).add
      ((hyi 0).differentiableAt.smul_const _)).add ((hyi 1).differentiableAt.smul_const _))
omit [Fact (finrank ℝ V = 4)] in private theorem fderiv_normalPerturbationForm_apply {y η : ℂ → E4}
    {p : V} (hy : DifferentiableAt ℝ y (normalCoord e p))
    (hη : DifferentiableAt ℝ η (normalCoord e p)) (u w : V) :
    fderiv ℝ (fun q ↦ normalPerturbationForm e y η q (fun _ ↦ w)) p u =
      -fderiv ℝ (fun z ↦ η z 0) (normalCoord e p) (normalCoord e u) * ⟪e 0, w⟫ +
        fderiv ℝ (fun z ↦ η z 1) (normalCoord e p) (normalCoord e u) * ⟪e 1, w⟫ +
        fderiv ℝ (fun z ↦ y z 0) (normalCoord e p) (normalCoord e u) * ⟪e 2, w⟫ +
        fderiv ℝ (fun z ↦ y z 1) (normalCoord e p) (normalCoord e u) * ⟪e 3, w⟫ := by
  have hyi := hasFDerivAt_coord_comp_normalCoord hy
  have hηi := hasFDerivAt_coord_comp_normalCoord hη
  have hd : HasFDerivAt (fun q ↦ -η (normalCoord e q) 0 * ⟪e 0, w⟫ +
      η (normalCoord e q) 1 * ⟪e 1, w⟫ + y (normalCoord e q) 0 * ⟪e 2, w⟫ +
      y (normalCoord e q) 1 * ⟪e 3, w⟫) _ p :=
    ((((hηi 0).neg.mul_const ⟪e 0, w⟫).fun_add ((hηi 1).mul_const ⟪e 1, w⟫)).fun_add
      ((hyi 0).mul_const ⟪e 2, w⟫)).fun_add ((hyi 1).mul_const ⟪e 3, w⟫)
  have hfun : (fun q ↦ normalPerturbationForm e y η q (fun _ ↦ w)) =
      fun q ↦ -η (normalCoord e q) 0 * ⟪e 0, w⟫ + η (normalCoord e q) 1 * ⟪e 1, w⟫ +
        y (normalCoord e q) 0 * ⟪e 2, w⟫ + y (normalCoord e q) 1 * ⟪e 3, w⟫ :=
    funext fun q ↦ normalFrameForm_apply e (y (normalCoord e q)) (η (normalCoord e q)) w
  rw [hfun, hd.fderiv]; simp; ring
private theorem alternatingFormEquiv_symm_neg_extDeriv_normalPerturbationForm {y η : ℂ → E4} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p)) (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    let z := normalCoord e p
    (alternatingFormEquiv V 2).symm (-extDeriv (normalPerturbationForm e y η) p) =
      (-fderiv ℝ (fun w ↦ η w 0) z 1) • ιMulti ℝ 2 ![e 0, e 2] +
      (-fderiv ℝ (fun w ↦ η w 0) z I) • ιMulti ℝ 2 ![e 0, e 3] +
      (fderiv ℝ (fun w ↦ η w 1) z 1) • ιMulti ℝ 2 ![e 1, e 2] +
      (fderiv ℝ (fun w ↦ η w 1) z I) • ιMulti ℝ 2 ![e 1, e 3] +
      (fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1) • ιMulti ℝ 2 ![e 2, e 3] := by
  intro z; refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [inner_alternatingFormEquiv_symm_ιMulti, ContinuousAlternatingMap.neg_apply,
    extDeriv_apply_pair_of_differentiableAt (differentiableAt_normalPerturbationForm hy hη),
    fderiv_normalPerturbationForm_apply hy hη, fderiv_normalPerturbationForm_apply hy hη]
  simp only [inner_add_left, real_inner_smul_left, inner_ιMulti_two,
    ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I _ (normalCoord e u),
    ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I _ (normalCoord e w),
    normalCoord_re, normalCoord_im, smul_eq_mul]; ring
private theorem conj_sectionValue_mul_two (x g : ℂ → E4) (z : ℂ) :
    conj (Vortex.sectionValue x z) * ((2 : ℂ) * ((g z 2 : ℂ) + (g z 3 : ℂ) * I)) =
      4 * (((x z 2 * g z 2 + x z 3 * g z 3 : ℝ) : ℂ) +
        ((x z 2 * g z 3 - x z 3 * g z 2 : ℝ) : ℂ) * I) := by
  apply Complex.ext <;> simp [Vortex.sectionValue_apply] <;> ring
omit [FiniteDimensional ℂ W] in private theorem coe_flatDirac_add (b : V → OneForm(V))
    {χ₁ χ₂ : V → PosSpin(o, ρ)} {p : V} (h₁ : DifferentiableAt ℝ χ₁ p)
    (h₂ : DifferentiableAt ℝ χ₂ p) :
    (flatDirac o ρ e b (χ₁ + χ₂) p : W) = flatDirac o ρ e b χ₁ p + flatDirac o ρ e b χ₂ p := by
  rw [coe_flatDirac, coe_flatDirac, coe_flatDirac, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [show spinorCovariantDeriv b (χ₁ + χ₂) p (e k) =
      spinorCovariantDeriv b χ₁ p (e k) + spinorCovariantDeriv b χ₂ p (e k) by
    rw [spinorCovariantDeriv_apply, spinorCovariantDeriv_apply, spinorCovariantDeriv_apply,
      fderiv_add h₁ h₂, add_apply, Pi.add_apply, smul_add, smul_add]; abel,
    Submodule.coe_add, map_add]
omit [FiniteDimensional ℂ W] in private theorem sum_covariantDeriv_normalConnection_smul_ι
    (x : ℂ → E4) {g : ℂ → E4} {p : V} (hg : DifferentiableAt ℝ g (normalCoord e p))
    (ψ₀ : PosSpin(o, ρ)) :
    let z := normalCoord e p
    ∑ k, covariantDeriv (normalConnection e x) (Vortex.sectionValue g ∘ normalCoord e) p (e k) •
        ρ (ι Q (e k)) ψ₀ =
      (fderiv ℝ (Vortex.sectionValue g) z 1 + I * (x z 0 : ℂ) * Vortex.sectionValue g z) •
          ρ (ι Q (e 2)) ψ₀ +
        (fderiv ℝ (Vortex.sectionValue g) z I + I * (x z 1 : ℂ) * Vortex.sectionValue g z) •
          ρ (ι Q (e 3)) ψ₀ := by
  intro z
  have hcov (v : V) :
      covariantDeriv (normalConnection e x) (Vortex.sectionValue g ∘ normalCoord e) p v =
        fderiv ℝ (Vortex.sectionValue g) z (normalCoord e v) +
          I * (x z 0 * (normalCoord e v).re + x z 1 * (normalCoord e v).im) *
            Vortex.sectionValue g z := by
    rw [covariantDeriv_apply, ((Vortex.differentiableAt_sectionValue_of_differentiableAt hg)
      |>.hasFDerivAt.comp p (normalCoord e).hasFDerivAt).fderiv, normalConnection_apply]; simp [z]
  rw [Fin.sum_univ_four, hcov, hcov, hcov, hcov, normalCoord_basis_zero, normalCoord_basis_one,
    normalCoord_apply_two, normalCoord_basis_three]
  simp only [map_zero, zero_re, zero_im, one_re, one_im, I_re, I_im, ofReal_zero, ofReal_one]
  module

section FrameHypotheses

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
  (h₂ : finrank ℂ PosSpin(o, ρ) = 2) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : PosSpin(o, ρ)} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
include hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁

@[simp] theorem normalDomainEquiv_normalPerturbation (y η : ℂ → E4) (p : V) :
    normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (y (normalCoord e p), η (normalCoord e p)) =
      (normalPerturbationForm e y η p, normalPerturbationSpinor o ρ e u₀ y η p) :=
  Prod.ext (normalDomainEquiv_apply_fst o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ _ _)
    (normalDomainEquiv_apply_snd o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ _ _)
/-- At the pulled-back canonical-line background `(normalConnection e x, normalSpinor o ρ e u₀ x)`,
the flat Seiberg–Witten equations hold iff `Vortex.equation x = 0` at `normalCoord e p`. -/
theorem flatDirac_eq_zero_and_flatCurvatureDefect_eq_zero_iff {x : ℂ → E4} {p : V}
    (hx : DifferentiableAt ℝ x (normalCoord e p)) :
    (flatDirac o ρ e (normalConnection e x) (normalSpinor o ρ e u₀ x) p = 0 ∧
      flatCurvatureDefect o ρ J hkl he h₀ h₂₃ (normalConnection e x)
        (normalSpinor o ρ e u₀ x) p = 0) ↔ Vortex.equation x (normalCoord e p) = 0 := by
  have hα := (Vortex.differentiableAt_sectionValue_of_differentiableAt hx).comp p
    (normalCoord e).differentiableAt
  have hns : normalSpinor o ρ e u₀ x = fun q ↦ (Vortex.sectionValue x ∘ normalCoord e) q • u₀ := rfl
  rw [← Submodule.coe_eq_zero, hns, coe_flatDirac_smul_const (normalConnection e x) hα u₀,
    flatCurvatureDefect_eq_zero_iff]
  exact sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff
    hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ hx
/-- Polarization of `quadraticTwoForm` along a unit canonical spinor `u₀`: pairing `α • u₀` with
`δα • u₀` gives `(Re(conj α * δα) / 4) • ω_u`. -/
theorem smul_quadraticTwoFormPolar_smul_smul_of_cliffordProjection_apply_eq_self (α δα : ℂ) :
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (α • u₀) (δα • u₀) =
      ((conj α * δα).re / 4) • kahlerSelfDual o J hkl he h₀ h₂₃ := by
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hq (c : ℂ) : ((√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (c • u₀) : ⋀[ℝ]^2 V) =
      (‖c‖ ^ 2 / 8) • (kahlerSelfDual o J hkl he h₀ h₂₃ : ⋀[ℝ]^2 V) := by
    have hc : cliffordProjection o ρ J.kahlerForm (c • u₀) = c • u₀ := by rw [map_smul, hu₀]
    rw [coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hω h₂ hρ hc,
      norm_smul, hu₀₁, mul_one, coe_kahlerSelfDual, smul_smul, smul_smul]; congr 1; ring
  have hpol : quadraticTwoFormPolar o ρ hkl (α • u₀) (δα • u₀) =
      quadraticTwoForm o ρ hkl ((α + δα) • u₀) -
        quadraticTwoForm o ρ hkl (α • u₀) - quadraticTwoForm o ρ hkl (δα • u₀) := by
    rw [add_smul, quadraticTwoForm_add]; abel
  apply Subtype.ext
  rw [hpol, smul_sub, smul_sub, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_smul, Submodule.coe_smul, hq (α + δα), hq α, hq δα, Submodule.coe_smul,
    ← sub_smul, ← sub_smul]; congr 1
  simp only [← normSq_eq_norm_sq, normSq_apply, add_re, add_im, mul_re, conj_re, conj_im]; ring
omit h₂ in
/-- Intertwining of `flatGaugeAdjoint` on normal perturbations with `Vortex.gaugeAdjoint x y`. -/
theorem flatGaugeAdjoint_normalPerturbation (x : ℂ → E4) {y η : ℂ → E4} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p)) (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    flatGaugeAdjoint e (normalSpinor o ρ e u₀ x) (normalPerturbationForm e y η)
        (normalPerturbationSpinor o ρ e u₀ y η) p = Vortex.gaugeAdjoint x y (normalCoord e p) := by
  have hdiv : (∑ k : Fin 4, (fderiv ℝ (normalPerturbationForm e y η) p (e k)) (fun _ ↦ e k)) =
      fderiv ℝ (fun z ↦ y z 0) (normalCoord e p) 1 +
        fderiv ℝ (fun z ↦ y z 1) (normalCoord e p) I := by
    simp only [← fderiv_continuousAlternatingMap_apply_const_apply
      (differentiableAt_normalPerturbationForm hy hη), fderiv_normalPerturbationForm_apply hy hη,
      Fin.sum_univ_four, normalCoord_basis_zero, normalCoord_basis_one, normalCoord_apply_two,
      normalCoord_basis_three, map_zero, orthonormal_iff_ite.1 e.orthonormal]; norm_num
  have horth := inner_antiCanonicalSpinor_eq_zero hQ hkl he h₀ h₂₃ hρ hu₀
  have hu₀_in : ⟪u₀, u₀⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hu₀₁]; norm_num
  have hspin : (⟪normalSpinor o ρ e u₀ x p, normalPerturbationSpinor o ρ e u₀ y η p⟫_ℂ).im / 4 =
      x (normalCoord e p) 2 * y (normalCoord e p) 3 -
        x (normalCoord e p) 3 * y (normalCoord e p) 2 := by
    rw [normalSpinor_apply, normalPerturbationSpinor_apply, normalFrameSpinor_eq, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right, hu₀_in, horth,
      mul_one, mul_zero, mul_zero, add_zero, conj_sectionValue_mul_two]; simp
  rw [flatGaugeAdjoint, hdiv, hspin, Vortex.gaugeAdjoint_def]; ring
/-- Intertwining of `linearizedFlatCurvature` on normal perturbations along `(ω_u, ρ₁, ρ₂)`. -/
theorem linearizedFlatCurvature_normalPerturbation (x : ℂ → E4) {y η : ℂ → E4} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p)) (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    let z := normalCoord e p
    linearizedFlatCurvature o ρ hkl (normalSpinor o ρ e u₀ x) (normalPerturbationForm e y η)
        (normalPerturbationSpinor o ρ e u₀ y η) p =
      Vortex.linearizedEquation x y z 0 • kahlerSelfDual o J hkl he h₀ h₂₃ +
        Vortex.gaugeFixedAdjoint x η z 0 • antiInvariantSelfDual₁ o e hkl he +
        Vortex.gaugeFixedAdjoint x η z 1 • antiInvariantSelfDual₂ o e hkl he := by
  intro z; have h12 : o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 2]) = ιMulti ℝ 2 ![e 0, e 3] := by
    rw [← o.hodgeStar_ιMulti_zero_three hkl he, o.hodgeStar_hodgeStar_of_even even_two hkl]
  have h13 : o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 3]) = -ιMulti ℝ 2 ![e 0, e 2] := by
    rw [← neg_neg (ιMulti ℝ 2 ![e 1, e 3]), ← o.hodgeStar_ιMulti_zero_two hkl he, map_neg,
      o.hodgeStar_hodgeStar_of_even even_two hkl]
  have hdiff : selfDualTwoVector o hkl
        ((alternatingFormEquiv V 2).symm (-extDeriv (normalPerturbationForm e y η) p)) =
      (fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1) •
          kahlerSelfDual o J hkl he h₀ h₂₃ +
        (-fderiv ℝ (fun w ↦ η w 0) z 1 - fderiv ℝ (fun w ↦ η w 1) z I) •
          antiInvariantSelfDual₁ o e hkl he +
        (-fderiv ℝ (fun w ↦ η w 0) z I + fderiv ℝ (fun w ↦ η w 1) z 1) •
          antiInvariantSelfDual₂ o e hkl he := Subtype.ext <| by
    rw [coe_selfDualTwoVector, alternatingFormEquiv_symm_neg_extDeriv_normalPerturbationForm hy hη]
    simp only [Submodule.coe_add, Submodule.coe_smul, coe_kahlerSelfDual,
      coe_antiInvariantSelfDual₁, coe_antiInvariantSelfDual₂,
      AlmostComplexStructure.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂₃, map_add, map_smul,
      o.hodgeStar_ιMulti_zero_two hkl he, o.hodgeStar_ιMulti_zero_three hkl he,
      o.hodgeStar_ιMulti_two_three hkl he, h12, h13]; module
  have hzeroth : (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (normalSpinor o ρ e u₀ x p)
        (normalPerturbationSpinor o ρ e u₀ y η p) =
      (x z 2 * y z 2 + x z 3 * y z 3) • kahlerSelfDual o J hkl he h₀ h₂₃ +
        (x z 2 * η z 3 - x z 3 * η z 2) • antiInvariantSelfDual₁ o e hkl he +
        (-x z 2 * η z 2 - x z 3 * η z 3) • antiInvariantSelfDual₂ o e hkl he := Subtype.ext <| by
    rw [normalSpinor_apply, normalPerturbationSpinor_apply, normalFrameSpinor_eq, map_add,
      smul_add, smul_quadraticTwoFormPolar_smul_smul_of_cliffordProjection_apply_eq_self
        hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁,
      smul_quadraticTwoFormPolar_smul_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hρ hu₀ hu₀₁]
    simp only [z, conj_sectionValue_mul_two, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_smul, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
      re_ofNat, im_ofNat]; module
  apply Subtype.ext; rw [linearizedFlatCurvature, Submodule.coe_add, congrArg Subtype.val hdiff,
    congrArg Subtype.val hzeroth]
  simp only [Submodule.coe_add, Submodule.coe_smul, Vortex.linearizedEquation_apply_zero,
    Vortex.gaugeFixedAdjoint_apply_zero, Vortex.gaugeFixedAdjoint_apply_one]; module
omit h₂ hρ hu₀₁ in private theorem coe_flatDirac_normalPerturbationSpinor (x : ℂ → E4)
    {y η : ℂ → E4} {p : V} (hy : DifferentiableAt ℝ y (normalCoord e p))
    (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    let z := normalCoord e p
    (flatDirac o ρ e (normalConnection e x) (normalPerturbationSpinor o ρ e u₀ y η) p : W) =
      ((fderiv ℝ (Vortex.sectionValue y) z 1 + I * (x z 0 : ℂ) * Vortex.sectionValue y z) +
          (fderiv ℝ (Vortex.sectionValue y) z I + I * (x z 1 : ℂ) * Vortex.sectionValue y z) * I) •
          ρ (ι Q (e 2)) u₀ +
        ((fderiv ℝ (Vortex.sectionValue η) z 1 + I * (x z 0 : ℂ) * Vortex.sectionValue η z) -
          (fderiv ℝ (Vortex.sectionValue η) z I + I * (x z 1 : ℂ) * Vortex.sectionValue η z) * I) •
          ρ (ι Q (e 0)) u₀ := by
  intro z; set v₀ := antiCanonicalSpinor o ρ e u₀
  have h3u := h₂₃ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 2)
  have hsec {g : ℂ → E4} (hg : DifferentiableAt ℝ g z) :
      DifferentiableAt ℝ (Vortex.sectionValue g ∘ normalCoord e) p :=
    (Vortex.differentiableAt_sectionValue_of_differentiableAt hg).comp p
      (normalCoord e).differentiableAt
  have hsmul_d {g : ℂ → E4} (hg : DifferentiableAt ℝ g z) (ψ : PosSpin(o, ρ)) :
      DifferentiableAt ℝ (fun q ↦ (Vortex.sectionValue g ∘ normalCoord e) q • ψ) p :=
    (((ContinuousLinearMap.id ℂ ℂ).smulRight ψ).restrictScalars ℝ).differentiableAt.comp p (hsec hg)
  -- Split the spinor perturbation along `(u₀, v₀)` and expand `flatDirac` on each component.
  have hsplit : normalPerturbationSpinor o ρ e u₀ y η =
      (fun q ↦ (Vortex.sectionValue y ∘ normalCoord e) q • u₀) +
        (fun q ↦ (Vortex.sectionValue η ∘ normalCoord e) q • v₀) :=
    funext fun q ↦ by simp [normalPerturbationSpinor, normalFrameSpinor_eq,
      Vortex.sectionValue_apply, v₀]
  rw [hsplit, coe_flatDirac_add (normalConnection e x) (hsmul_d hy u₀) (hsmul_d hη v₀),
    coe_flatDirac_smul_const _ (hsec hy), coe_flatDirac_smul_const _ (hsec hη),
    sum_covariantDeriv_normalConnection_smul_ι x hy u₀,
    sum_covariantDeriv_normalConnection_smul_ι x hη v₀, ι_apply_two_antiCanonicalSpinor hQ u₀,
    h3u, ι_apply_three_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀]
  simp only [z, smul_smul, mul_neg]; module
omit h₂ hρ hu₀₁ in private theorem coe_sum_normalPerturbationForm_smul_normalSpinor (x y η : ℂ → E4)
    (p : V) :
    let z := normalCoord e p
    ((∑ k : Fin 4, cMul(o, ρ) (e k) (normalPerturbationForm e y η p (fun _ ↦ e k) •
      (I • normalSpinor o ρ e u₀ x p)) : NegSpin(Q, o, ρ)) : W) =
      (((y z 0 : ℂ) * I + (y z 1 : ℂ) * I * I) * Vortex.sectionValue x z) • ρ (ι Q (e 2)) u₀ +
        (((-(η z 0 : ℂ)) * I + (η z 1 : ℂ) * I * I) * Vortex.sectionValue x z) •
          ρ (ι Q (e 0)) u₀ := by
  intro z
  have h1u := h₀ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 0)
  have h3u := h₂₃ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 2)
  have hδb (k : Fin 4) : (cMul(o, ρ) (e k)
      (normalPerturbationForm e y η p (fun _ ↦ e k) • (I • normalSpinor o ρ e u₀ x p)) : W) =
      ((normalFrameForm e (y z) (η z) (fun _ ↦ e k) : ℂ) * I * Vortex.sectionValue x z) •
        ρ (ι Q (e k)) u₀ := by
    rw [normalPerturbationForm_apply, normalSpinor_apply]; simp only [z, ← Complex.coe_smul,
      smul_smul, map_smul, Submodule.coe_smul, coe_positiveHalfSpinCliffordMul_apply, ← mul_assoc]
  rw [Fin.sum_univ_four, Submodule.coe_add, Submodule.coe_add, Submodule.coe_add, hδb 0, hδb 1,
    hδb 2, hδb 3, h1u, h3u]; simp only [normalFrameForm_apply, orthonormal_iff_ite.1 e.orthonormal,
    smul_smul]; norm_num; module
omit h₂ hρ hu₀₁ in
/-- Intertwining of `linearizedFlatDirac` on normal perturbations along `(c(e₂) u₀, -c(e₀) u₀)`. -/
theorem linearizedFlatDirac_normalPerturbation (x : ℂ → E4) {y η : ℂ → E4} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p)) (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    let z := normalCoord e p
    linearizedFlatDirac o ρ e (normalConnection e x) (normalSpinor o ρ e u₀ x)
        (normalPerturbationForm e y η) (normalPerturbationSpinor o ρ e u₀ y η) p =
      ((2 : ℂ) * ((Vortex.linearizedEquation x y z 1 : ℂ) +
          (Vortex.linearizedEquation x y z 2 : ℂ) * I)) • cMul(o, ρ) (e 2) u₀ -
        ((2 : ℂ) * ((Vortex.gaugeFixedAdjoint x η z 2 : ℂ) +
          (Vortex.gaugeFixedAdjoint x η z 3 : ℂ) * I)) • cMul(o, ρ) (e 0) u₀ := by
  intro z; have hpy (i : Fin 4) := (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy
  have hpη (i : Fin 4) := (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hη
  -- Match the complex coefficients of `c(e₂) u₀` and `c(e₀) u₀` with `L_x y` and `L_x* η`.
  have hc₂ : (fderiv ℝ (Vortex.sectionValue y) z 1 + I * (x z 0 : ℂ) * Vortex.sectionValue y z) +
        (fderiv ℝ (Vortex.sectionValue y) z I + I * (x z 1 : ℂ) * Vortex.sectionValue y z) * I +
        ((y z 0 : ℂ) * I + (y z 1 : ℂ) * I * I) * Vortex.sectionValue x z =
      (2 : ℂ) * ((Vortex.linearizedEquation x y z 1 : ℂ) +
        (Vortex.linearizedEquation x y z 2 : ℂ) * I) := by
    simp_rw [Vortex.fderiv_sectionValue_apply (hpy 2) (hpy 3)]
    apply Complex.ext <;> simp [Vortex.sectionValue_apply] <;> ring
  have hc₀ : (2 : ℂ) * ((Vortex.gaugeFixedAdjoint x η z 2 : ℂ) +
        (Vortex.gaugeFixedAdjoint x η z 3 : ℂ) * I) =
      -((fderiv ℝ (Vortex.sectionValue η) z 1 + I * (x z 0 : ℂ) * Vortex.sectionValue η z) -
        (fderiv ℝ (Vortex.sectionValue η) z I + I * (x z 1 : ℂ) * Vortex.sectionValue η z) * I +
        ((-(η z 0 : ℂ)) * I + (η z 1 : ℂ) * I * I) * Vortex.sectionValue x z) := by
    simp_rw [Vortex.fderiv_sectionValue_apply (hpη 2) (hpη 3)]
    apply Complex.ext <;> simp [Vortex.sectionValue_apply] <;> ring
  -- Combine the chiral Dirac expansion and connection-perturbation sum in `W`.
  apply Subtype.ext; rw [linearizedFlatDirac, Submodule.coe_add,
    coe_flatDirac_normalPerturbationSpinor hQ hkl he h₀ h₂₃ hu₀ x hy hη,
    coe_sum_normalPerturbationForm_smul_normalSpinor hQ hkl he h₀ h₂₃ hu₀ x y η p,
    Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul,
    coe_positiveHalfSpinCliffordMul_apply, coe_positiveHalfSpinCliffordMul_apply, ← hc₂, hc₀]
  module
/-- **Eight-real-component normal intertwining theorem**: for any plane field `x : ℂ → ℝ⁴` (with no
PDE hypothesis on `x`), `gaugeFixedFlatOperator` at the pulled-back background
`(normalConnection e x, normalSpinor o ρ e u₀ x)` applied to the normal perturbation pulled back
from `(y, η)` equals `normalTargetEquiv (L_x y, L_x* η)` at `normalCoord e p`. -/
theorem gaugeFixedFlatOperator_normalPerturbation (x : ℂ → E4) {y η : ℂ → E4} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p)) (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    gaugeFixedFlatOperator o ρ e hkl (normalConnection e x) (normalSpinor o ρ e u₀ x)
        (normalPerturbationForm e y η) (normalPerturbationSpinor o ρ e u₀ y η) p =
      normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (Vortex.gaugeFixedOperator x y (normalCoord e p),
          Vortex.gaugeFixedAdjoint x η (normalCoord e p)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [gaugeFixedFlatOperator, normalTargetEquiv_apply_fst, Vortex.gaugeFixedOperator_apply_zero]
    exact flatGaugeAdjoint_normalPerturbation hQ hkl he h₀ h₂₃ hρ hu₀ hu₀₁ x hy hη
  · rw [gaugeFixedFlatOperator, normalTargetEquiv_apply_snd_fst,
      Vortex.gaugeFixedOperator_apply_one]
    exact linearizedFlatCurvature_normalPerturbation hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ x hy hη
  · rw [gaugeFixedFlatOperator, normalTargetEquiv_apply_snd_snd,
      Vortex.gaugeFixedOperator_apply_two, Vortex.gaugeFixedOperator_apply_three]
    exact linearizedFlatDirac_normalPerturbation hQ hkl he h₀ h₂₃ hu₀ x hy hη

end FrameHypotheses
end NormalIntertwining
end TauCeti.SeibergWitten
