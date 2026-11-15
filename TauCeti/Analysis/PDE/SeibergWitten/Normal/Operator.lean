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

/-!
# The gauge-fixed flat Seiberg–Witten operator and eight-component normal intertwining

Near a pseudoholomorphic curve `C` in a symplectic four-manifold, rescaling the large-parameter
Seiberg–Witten equations along the normal planes `V = ℂ_base × ℂ_normal` produces the flat limiting
equations of `TauCeti.Analysis.PDE.SeibergWitten.FlatLimit`. While base-independent solutions on the
canonical spinor line `χ = α u₀` reduce to plane vortices, genuine four-dimensional perturbations
`(δb, ζ) ∈ Ω¹(V) × W⁺` have **eight** real components: the four normal/canonical components `y`
(normal connection `(y₀, y₁)` and canonical spinor perturbation `2(y₂ + i y₃) u₀`) together with the
four tangential/anti-canonical components `η` (tangential connection `(-η₀, η₁)` and anti-canonical
spinor perturbation `2(η₂ + i η₃) v₀`, where `v₀ = c(e₀) c(e₂) u₀`).

This file constructs the full eight-real-component linearized gauge-fixed flat Seiberg–Witten
operator on `V` and proves its exact off-shell block decomposition along the normal coordinate into
the plane-vortex operator `L_x` and its formal adjoint `L_x*`:

* **Gauge-fixed flat Seiberg–Witten operator.** We define `spinorCovariantDeriv`, the chiral Dirac
  operator `flatDirac`, the unit-symbol self-dual curvature defect `flatCurvatureDefect` (matching
  the `(√2 / 2) (F + ⋆F)` convention of `TauCeti.Analysis.PDE.SeibergWitten.DeformationSymbol`),
  their first variations `linearizedFlatCurvature` and `linearizedFlatDirac`
  (`hasDerivAt_flatCurvatureDefect`, `hasDerivAt_flatDirac`), the formal gauge-fixing adjoint
  `flatGaugeAdjoint` for the metric `‖δb‖² + ‖ζ‖² / 4` (`mul_flatGaugeAdjoint_eq`), and the
  combined eight-component operator `gaugeFixedFlatSW`. All differential operators are independent
  of the orthonormal frame (`flatDirac_congr_orthonormalBasis`,
  `linearizedFlatDirac_congr_orthonormalBasis`, `flatGaugeAdjoint_congr_orthonormalBasis`,
  `gaugeFixedFlatSW_congr_orthonormalBasis`).
* **Exact normal intertwining.** Pulling a plane perturbation `(y, η) : ℂ → ℝ⁴ × ℝ⁴` back along
  `normalCoord e` via `normalDomainEquiv` (`normalPerturbationForm`, `normalPerturbationSpinor`),
  `gaugeFixedFlatSW_normalPerturbation` proves that at *every* background plane field `x`
  (off-shell, with no regularity hypothesis on `x`), `gaugeFixedFlatSW` at
  `(normalConnection e x, α u₀)` intertwines through `normalTargetEquiv` with
  `(Vortex.gaugeFixedOperator x y, Vortex.gaugeFixedAdjoint x η)`.

The planar eight-component normal model operator, its kernel and cokernel identifications at a plane
vortex, the normal slow projections `Π₊, Π₋`, and the complementary weak `L²` inverse `𝒬` are
constructed in `TauCeti.Analysis.PDE.SeibergWitten.Normal.Inverse`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open CliffordAlgebra Complex Module exteriorPower
open scoped RealInnerProductSpace InnerProductSpace ComplexConjugate

namespace TauCeti.SeibergWitten

/-! ### The gauge-fixed flat Seiberg–Witten operator and its linearization -/

section FlatOperator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

omit [Fact (finrank ℝ V = 4)] in
/-- The trace of a real bilinear map over an orthonormal basis is independent of the basis. -/
private theorem sum_bilin_orthonormalBasis_eq {ι : Type*} [Fintype ι]
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] M) (e e' : OrthonormalBasis ι ℝ V) :
    ∑ k, B (e k) (e k) = ∑ i, B (e' i) (e' i) := by
  classical
  have hexp (k : ι) :
      B (e k) (e k) = ∑ i, ∑ j, (⟪e' i, e k⟫ * ⟪e k, e' j⟫) • B (e' i) (e' j) := by
    conv_lhs => rw [← e'.sum_repr' (e k)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_comm, real_inner_comm (e' j) (e k)]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  have hsum (j : ι) :
      (∑ k, (⟪e' i, e k⟫ * ⟪e k, e' j⟫) • B (e' i) (e' j)) =
        ⟪e' i, e' j⟫ • B (e' i) (e' j) := by
    rw [← Finset.sum_smul, e.sum_inner_mul_inner]
  simp only [hsum, orthonormal_iff_ite.1 e'.orthonormal, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [FiniteDimensional ℂ W] in
/-- **Covariant derivative of a positive half-spinor field** `∇_a χ = dχ + i b χ` for the imaginary
connection one-form `a = i b`. -/
def spinorCovariantDeriv (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (p : V) : V →L[ℝ] positiveHalfSpinors o ρ :=
  fderiv ℝ χ p +
    ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (b p)).smulRight (I • χ p)

omit [FiniteDimensional ℂ W] in
@[simp]
theorem spinorCovariantDeriv_apply (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (χ : V → positiveHalfSpinors o ρ) (p v : V) :
    spinorCovariantDeriv b χ p v = fderiv ℝ χ p v + b p (fun _ ↦ v) • (I • χ p) := by
  simp [spinorCovariantDeriv, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply]

omit [FiniteDimensional ℂ W] in
/-- On a section `α • ψ₀` along a constant spinor `ψ₀`, `spinorCovariantDeriv` reduces to the
abelian covariant derivative `covariantDeriv b α`. -/
theorem spinorCovariantDeriv_smul_const (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) {α : V → ℂ} {p : V}
    (hα : DifferentiableAt ℝ α p) (ψ₀ : positiveHalfSpinors o ρ) (v : V) :
    spinorCovariantDeriv b (fun q ↦ α q • ψ₀) p v = covariantDeriv b α p v • ψ₀ := by
  let L : ℂ →L[ℝ] positiveHalfSpinors o ρ :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight ψ₀).restrictScalars ℝ
  have hf : fderiv ℝ (fun q ↦ α q • ψ₀) p v = fderiv ℝ α p v • ψ₀ := by
    change fderiv ℝ (L ∘ α) p v = _
    rw [(L.hasFDerivAt.comp p hα.hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply]
    rfl
  rw [spinorCovariantDeriv_apply, hf, covariantDeriv_apply, add_smul, ← Complex.coe_smul,
    smul_smul, smul_smul]
  congr 2
  ring

omit [FiniteDimensional ℂ W] in
variable (o ρ e) in
/-- **The flat chiral Dirac operator** `D_b χ = ∑ₖ c(eₖ) ∇_{b, eₖ} χ : W⁺ → W⁻`. -/
def flatDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  ∑ k, positiveHalfSpinCliffordMul o ρ (e k) (spinorCovariantDeriv b χ p (e k))

omit [FiniteDimensional ℂ W] in
@[simp]
theorem coe_flatDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    (flatDirac o ρ e b χ p : W) = ∑ k, ρ (ι Q (e k)) (spinorCovariantDeriv b χ p (e k)) := by
  simp [flatDirac]

omit [FiniteDimensional ℂ W] in
/-- `flatDirac` is independent of the choice of orthonormal basis of `V`. -/
theorem flatDirac_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatDirac o ρ e b χ p = flatDirac o ρ e' b χ p := by
  let B : V →ₗ[ℝ] V →ₗ[ℝ] Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
    { toFun u :=
        { toFun v := positiveHalfSpinCliffordMul o ρ u (spinorCovariantDeriv b χ p v)
          map_add' v₁ v₂ := by rw [map_add, map_add]
          map_smul' r v := by
            rw [ContinuousLinearMap.map_smul, RingHom.id_apply, ← Complex.coe_smul,
              LinearMap.map_smul, Complex.coe_smul] }
      map_add' u₁ u₂ := LinearMap.ext fun v ↦ Subtype.ext <| by
        dsimp
        rw [coe_positiveHalfSpinCliffordMul_apply, coe_positiveHalfSpinCliffordMul_apply,
          coe_positiveHalfSpinCliffordMul_apply, map_add, map_add, LinearMap.add_apply]
      map_smul' r u := LinearMap.ext fun v ↦ Subtype.ext <| by
        dsimp
        rw [coe_positiveHalfSpinCliffordMul_apply, coe_positiveHalfSpinCliffordMul_apply,
          map_smul, map_smul, LinearMap.smul_apply] }
  exact sum_bilin_orthonormalBasis_eq B e e'

omit [FiniteDimensional ℂ W] in
/-- On a spinor field `α • ψ₀` with constant `ψ₀`, `flatDirac` coincides with the Dirac sum of
`TauCeti.Analysis.PDE.SeibergWitten.FlatLimit`. -/
theorem coe_flatDirac_smul_const (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) {α : V → ℂ} {p : V}
    (hα : DifferentiableAt ℝ α p) (ψ₀ : positiveHalfSpinors o ρ) :
    (flatDirac o ρ e b (fun q ↦ α q • ψ₀) p : W) =
      ∑ k, covariantDeriv b α p (e k) • ρ (ι Q (e k)) ψ₀ := by
  rw [coe_flatDirac]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [spinorCovariantDeriv_smul_const b hα, Submodule.coe_smul, map_smul]

variable (o) in
/-- **Unit-symbol self-dual projection** `F ↦ (√2 / 2) (F + ⋆F) ∈ Λ⁺ V`, matching the symbol
convention `(√2 d⁺)` of `TauCeti.Analysis.PDE.SeibergWitten.DeformationSymbol`. -/
def selfDualTwoVector (hkl : 2 + 2 = finrank ℝ V) :
    ⋀[ℝ]^2 V →L[ℝ] Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  LinearMap.toContinuousLinearMap
    { toFun F := ⟨(√2 / 2 : ℝ) • (F + o.hodgeStar hkl F), Module.End.mem_eigenspace_iff.2 <| by
        simp only [LinearEquiv.coe_coe, map_smul, map_add,
          o.hodgeStar_hodgeStar_of_even even_two hkl, one_smul, add_comm]⟩
      map_add' F G := Subtype.ext <| by
        simp only [Submodule.coe_add, map_add]
        module
      map_smul' r F := Subtype.ext <| by
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        module }

@[simp]
theorem coe_selfDualTwoVector (hkl : 2 + 2 = finrank ℝ V) (F : ⋀[ℝ]^2 V) :
    (selfDualTwoVector o hkl F : ⋀[ℝ]^2 V) = (√2 / 2 : ℝ) • (F + o.hodgeStar hkl F) :=
  (rfl)

variable (o ρ J) in
/-- **Self-dual curvature defect** of the flat limiting Seiberg–Witten equations in `Λ⁺ V`:
`(√2 / 2) (F + ⋆F - ω / 8 + q(χ) / 2)`, where `F = -db` as a two-vector. -/
def flatCurvatureDefect (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm (-extDeriv b p)) -
    (8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃ +
    (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p)

theorem flatCurvatureDefect_apply (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatCurvatureDefect o ρ J hkl he h₀ h₂₃ b χ p =
      selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm (-extDeriv b p)) -
        (8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃ +
        (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p) :=
  (rfl)

/-- `flatCurvatureDefect` vanishes if and only if the flat limiting curvature equation
`F + ⋆F = ω / 8 - q(χ) / 2` of `TauCeti.Analysis.PDE.SeibergWitten.FlatLimit` holds. -/
theorem flatCurvatureDefect_eq_zero_iff (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ) (p : V) :
    flatCurvatureDefect o ρ J hkl he h₀ h₂₃ b χ p = 0 ↔
      let F := (alternatingFormEquiv V 2).symm (-extDeriv b p)
      F + o.hodgeStar hkl F =
        (8⁻¹ : ℝ) • J.kahlerForm - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (χ p) : ⋀[ℝ]^2 V) := by
  set F := (alternatingFormEquiv V 2).symm (-extDeriv b p)
  have hsqrt : (√2 / 2 : ℝ) ≠ 0 := by positivity
  have hrel : (flatCurvatureDefect o ρ J hkl he h₀ h₂₃ b χ p : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • ((F + o.hodgeStar hkl F) -
        ((8⁻¹ : ℝ) • J.kahlerForm -
          (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (χ p) : ⋀[ℝ]^2 V))) := by
    simp only [flatCurvatureDefect, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      coe_selfDualTwoVector, coe_kahlerSelfDual, F]
    module
  rw [← Submodule.coe_eq_zero, hrel, smul_eq_zero_iff_right hsqrt, sub_eq_zero]

variable (o ρ) in
/-- **Linearized self-dual curvature operator** at `(b, χ)` applied to `(δb, ζ)`:
`(√2 / 2) (δF + ⋆δF) + (√2 / 4) q'(χ, ζ)`, where `δF = -d(δb)`. -/
def linearizedFlatCurvature (hkl : 2 + 2 = finrank ℝ V)
    (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm (-extDeriv δb p)) +
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (χ p) (ζ p)

theorem linearizedFlatCurvature_apply (hkl : 2 + 2 = finrank ℝ V)
    (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatCurvature o ρ hkl χ δb ζ p =
      selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm (-extDeriv δb p)) +
        (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (χ p) (ζ p) :=
  (rfl)

omit [FiniteDimensional ℂ W] in
variable (o ρ e) in
/-- **Linearized chiral Dirac operator** at `(b, χ)` applied to `(δb, ζ)`:
`D_b ζ + ∑ₖ c(eₖ) (i δb(eₖ) χ)`. -/
def linearizedFlatDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  flatDirac o ρ e b ζ p +
    ∑ k, positiveHalfSpinCliffordMul o ρ (e k) (δb p (fun _ ↦ e k) • (I • χ p))

omit [FiniteDimensional ℂ W] in
theorem linearizedFlatDirac_apply (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatDirac o ρ e b χ δb ζ p =
      flatDirac o ρ e b ζ p +
        ∑ k, positiveHalfSpinCliffordMul o ρ (e k) (δb p (fun _ ↦ e k) • (I • χ p)) :=
  (rfl)

omit [FiniteDimensional ℂ W] in
/-- `linearizedFlatDirac` is independent of the choice of orthonormal basis of `V`. -/
theorem linearizedFlatDirac_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    linearizedFlatDirac o ρ e b χ δb ζ p = linearizedFlatDirac o ρ e' b χ δb ζ p := by
  let L : V →ₗ[ℝ] ℝ :=
    ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (δb p)).toLinearMap
  have hL (v : V) : L v = δb p (fun _ ↦ v) := by
    simp [L, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply]
  let B : V →ₗ[ℝ] V →ₗ[ℝ] Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
    { toFun u :=
        { toFun v := positiveHalfSpinCliffordMul o ρ u (L v • (I • χ p))
          map_add' v₁ v₂ := by rw [map_add, add_smul, map_add]
          map_smul' r v := by
            rw [LinearMap.map_smul, RingHom.id_apply, smul_eq_mul, mul_smul,
              ← Complex.coe_smul, LinearMap.map_smul, Complex.coe_smul] }
      map_add' u₁ u₂ := LinearMap.ext fun v ↦ Subtype.ext <| by
        dsimp
        rw [coe_positiveHalfSpinCliffordMul_apply, coe_positiveHalfSpinCliffordMul_apply,
          coe_positiveHalfSpinCliffordMul_apply, map_add, map_add, LinearMap.add_apply]
      map_smul' r u := LinearMap.ext fun v ↦ Subtype.ext <| by
        dsimp
        rw [coe_positiveHalfSpinCliffordMul_apply, coe_positiveHalfSpinCliffordMul_apply,
          map_smul, map_smul, LinearMap.smul_apply] }
  have h0 : (∑ k, positiveHalfSpinCliffordMul o ρ (e k) (δb p (fun _ ↦ e k) • (I • χ p))) =
      ∑ k, positiveHalfSpinCliffordMul o ρ (e' k) (δb p (fun _ ↦ e' k) • (I • χ p)) := by
    simpa only [B, LinearMap.coe_mk, AddHom.coe_mk, hL] using sum_bilin_orthonormalBasis_eq B e e'
  rw [linearizedFlatDirac, linearizedFlatDirac, flatDirac_congr_orthonormalBasis e', h0]

/-- `linearizedFlatCurvature` is the first variation of `flatCurvatureDefect` along `(δb, ζ)`. -/
theorem hasDerivAt_flatCurvatureDefect (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    {b δb : V → V [⋀^Fin 1]→L[ℝ] ℝ} (χ ζ : V → positiveHalfSpinors o ρ) {p : V}
    (hb : DifferentiableAt ℝ b p) (hδb : DifferentiableAt ℝ δb p) :
    HasDerivAt
      (fun t : ℝ ↦ flatCurvatureDefect o ρ J hkl he h₀ h₂₃ (b + t • δb) (χ + t • ζ) p)
      (linearizedFlatCurvature o ρ hkl χ δb ζ p) 0 := by
  let L := (selfDualTwoVector o hkl).comp
    (LinearEquiv.toContinuousLinearEquiv (alternatingFormEquiv V 2).symm).toContinuousLinearMap
  have hcurv (t : ℝ) :
      selfDualTwoVector o hkl ((alternatingFormEquiv V 2).symm (-extDeriv (b + t • δb) p)) =
        L (-extDeriv b p) + t • L (-extDeriv δb p) := by
    have hed : -extDeriv (b + t • δb) p = -extDeriv b p + t • (-extDeriv δb p) := by
      rw [extDeriv_add hb (hδb.const_smul t), extDeriv_smul]
      module
    change L (-extDeriv (b + t • δb) p) = L (-extDeriv b p) + t • L (-extDeriv δb p)
    rw [hed, map_add, map_smul]
  have hd_curv : HasDerivAt
      (fun t : ℝ ↦ L (-extDeriv b p) + t • L (-extDeriv δb p) -
        (8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃)
      (L (-extDeriv δb p)) 0 := by
    refine HasDerivAt.congr_deriv
      ((((hasDerivAt_id (0 : ℝ)).smul_const (L (-extDeriv δb p))).const_add
        (L (-extDeriv b p))).sub_const ((8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃)) ?_
    simp
  have hd_line : HasDerivAt (fun t : ℝ ↦ χ p + t • ζ p) (ζ p) (0 : ℝ) := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_id (0 : ℝ)).smul_const (ζ p)).const_add (χ p)) ?_
    simp
  have hd_q : HasDerivAt
      (fun t : ℝ ↦ (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p + t • ζ p))
      ((√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (χ p) (ζ p)) 0 := by
    have hF : HasFDerivAt (quadraticTwoForm o ρ hkl)
        (quadraticTwoFormPolar o ρ hkl (χ p)) (χ p + (0 : ℝ) • ζ p) := by
      rw [zero_smul, add_zero]
      exact hasFDerivAt_quadraticTwoForm o ρ hkl (χ p)
    exact (hF.comp_hasDerivAt (0 : ℝ) hd_line).const_smul (√2 / 4 : ℝ)
  have hfun : (fun t : ℝ ↦ flatCurvatureDefect o ρ J hkl he h₀ h₂₃ (b + t • δb) (χ + t • ζ) p) =
      fun t : ℝ ↦ (L (-extDeriv b p) + t • L (-extDeriv δb p) -
        (8⁻¹ : ℝ) • kahlerSelfDual o J hkl he h₀ h₂₃) +
        (√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (χ p + t • ζ p) := by
    funext t
    simp only [flatCurvatureDefect, Pi.add_apply, Pi.smul_apply, hcurv t]
  rw [hfun]
  exact hd_curv.fun_add hd_q

/-- `linearizedFlatDirac` is the first variation of `flatDirac` along `(δb, ζ)`. -/
theorem hasDerivAt_flatDirac (b δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    {χ ζ : V → positiveHalfSpinors o ρ} {p : V}
    (hχ : DifferentiableAt ℝ χ p) (hζ : DifferentiableAt ℝ ζ p) :
    HasDerivAt (fun t : ℝ ↦ flatDirac o ρ e (b + t • δb) (χ + t • ζ) p)
      (linearizedFlatDirac o ρ e b χ δb ζ p) 0 := by
  have : FiniteDimensional ℝ (positiveHalfSpinors o ρ) := FiniteDimensional.trans ℝ ℂ _
  let C (k : Fin 4) : positiveHalfSpinors o ρ →L[ℝ]
      Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
    ((positiveHalfSpinCliffordMul o ρ (e k)).restrictScalars ℝ).toContinuousLinearMap
  have hcov (t : ℝ) (k : Fin 4) :
      spinorCovariantDeriv (b + t • δb) (χ + t • ζ) p (e k) =
        spinorCovariantDeriv b χ p (e k) +
          t • (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)) +
          (t ^ 2) • (δb p (fun _ ↦ e k) • (I • ζ p)) := by
    have hf : fderiv ℝ (χ + t • ζ) p (e k) = fderiv ℝ χ p (e k) + t • fderiv ℝ ζ p (e k) := by
      rw [(hχ.hasFDerivAt.add (hζ.hasFDerivAt.const_smul t)).fderiv, add_apply, smul_apply]
    simp only [spinorCovariantDeriv_apply, hf, Pi.add_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [smul_add, smul_comm I t (ζ p), smul_add, add_smul, add_smul,
      mul_smul t (δb p (fun _ ↦ e k)) (I • χ p),
      mul_smul t (δb p (fun _ ↦ e k)) (t • (I • ζ p)),
      smul_comm (b p (fun _ ↦ e k)) t (I • ζ p),
      smul_comm (δb p (fun _ ↦ e k)) t (I • ζ p),
      smul_smul t t, ← sq, smul_add, smul_add]
    abel
  have hterm (k : Fin 4) :
      HasDerivAt
        (fun t : ℝ ↦ C k (spinorCovariantDeriv (b + t • δb) (χ + t • ζ) p (e k)))
        (C k (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p))) 0 := by
    have hpoly : HasDerivAt
        (fun t : ℝ ↦ spinorCovariantDeriv b χ p (e k) +
          t • (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)) +
          (t ^ 2) • (δb p (fun _ ↦ e k) • (I • ζ p)))
        (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)) 0 := by
      have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const
        (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p))).const_add
        (spinorCovariantDeriv b χ p (e k))
      have h2 := (hasDerivAt_pow 2 (0 : ℝ)).smul_const (δb p (fun _ ↦ e k) • (I • ζ p))
      refine HasDerivAt.congr_deriv (h1.fun_add h2) ?_
      simp
    have hfn : (fun t : ℝ ↦ C k (spinorCovariantDeriv (b + t • δb) (χ + t • ζ) p (e k))) =
        (C k ∘ fun t : ℝ ↦ spinorCovariantDeriv b χ p (e k) +
          t • (spinorCovariantDeriv b ζ p (e k) + δb p (fun _ ↦ e k) • (I • χ p)) +
          (t ^ 2) • (δb p (fun _ ↦ e k) • (I • ζ p))) := by
      funext t
      dsimp
      rw [hcov t k]
    rw [hfn]
    exact (C k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hpoly
  have hsum := HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) ↦ hterm k
  have hgoal_eq : (∑ k : Fin 4, C k (spinorCovariantDeriv b ζ p (e k) +
      δb p (fun _ ↦ e k) • (I • χ p))) = linearizedFlatDirac o ρ e b χ δb ζ p := by
    simp only [map_add, Finset.sum_add_distrib]
    rfl
  rw [← hgoal_eq]
  exact hsum

omit [FiniteDimensional ℂ W] in
variable (e) in
/-- **Formal adjoint of the four-dimensional infinitesimal gauge action** `f ↦ (-df, i f χ)` with
respect to the domain metric `‖δb‖² + ‖ζ‖² / 4`:
`d₀* (δb, ζ) = ∑ₖ ∂_{eₖ}(δb(eₖ)) + Im⟪χ, ζ⟫ / 4`. -/
def flatGaugeAdjoint (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) : ℝ :=
  (∑ k, (fderiv ℝ δb p (e k)) (fun _ ↦ e k)) + (⟪χ p, ζ p⟫_ℂ).im / 4

omit [FiniteDimensional ℂ W] in
theorem flatGaugeAdjoint_def (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    flatGaugeAdjoint e χ δb ζ p =
      (∑ k, (fderiv ℝ δb p (e k)) (fun _ ↦ e k)) + (⟪χ p, ζ p⟫_ℂ).im / 4 :=
  (rfl)

omit [FiniteDimensional ℂ W] in
/-- `flatGaugeAdjoint` is independent of the choice of orthonormal basis of `V`. -/
theorem flatGaugeAdjoint_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (χ : V → positiveHalfSpinors o ρ) (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    flatGaugeAdjoint e χ δb ζ p = flatGaugeAdjoint e' χ δb ζ p := by
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun u := ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm
        (fderiv ℝ δb p u)).toLinearMap
      map_add' u₁ u₂ := by ext v; simp
      map_smul' r u := by ext v; simp }
  have hdiv : (∑ k, (fderiv ℝ δb p (e k)) (fun _ ↦ e k)) =
      ∑ k, (fderiv ℝ δb p (e' k)) (fun _ ↦ e' k) :=
    sum_bilin_orthonormalBasis_eq B e e'
  simp only [flatGaugeAdjoint, hdiv]

omit [FiniteDimensional ℂ W] in
/-- **Pointwise Green identity for `flatGaugeAdjoint`**: for `f : V → ℝ` and `δb` differentiable at
`p`, `f · d₀*(δb, ζ)` equals the inner product of the infinitesimal gauge variation
`(-df, i f χ)` with `(δb, ζ)` (in the metric `‖δb‖² + ‖ζ‖² / 4`) plus the divergence
`∑ₖ ∂_{eₖ}(f · δb(eₖ))`. -/
theorem mul_flatGaugeAdjoint_eq {f : V → ℝ} (χ : V → positiveHalfSpinors o ρ)
    {δb : V → V [⋀^Fin 1]→L[ℝ] ℝ} (ζ : V → positiveHalfSpinors o ρ) {p : V}
    (hf : DifferentiableAt ℝ f p) (hδb : DifferentiableAt ℝ δb p) :
    f p * flatGaugeAdjoint e χ δb ζ p =
      (-(∑ k, fderiv ℝ f p (e k) * δb p (fun _ ↦ e k)) +
        (⟪f p • (I • χ p), ζ p⟫_ℂ).re / 4) +
        ∑ k, fderiv ℝ (fun q ↦ f q * δb q (fun _ ↦ e k)) p (e k) := by
  have hprod (k : Fin 4) :
      fderiv ℝ (fun q ↦ f q * δb q (fun _ ↦ e k)) p (e k) =
        fderiv ℝ f p (e k) * δb p (fun _ ↦ e k) +
          f p * (fderiv ℝ δb p (e k)) (fun _ ↦ e k) := by
    let evk : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousAlternatingMap.apply ℝ V ℝ (fun _ ↦ e k)
    have hδbk : HasFDerivAt (fun q ↦ δb q (fun _ ↦ e k)) (evk.comp (fderiv ℝ δb p)) p :=
      evk.hasFDerivAt.comp p hδb.hasFDerivAt
    rw [(hf.hasFDerivAt.fun_mul hδbk).fderiv]
    simp only [evk, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousAlternatingMap.apply_apply, smul_eq_mul]
    ring
  have hspin : (⟪f p • (I • χ p), ζ p⟫_ℂ).re = f p * (⟪χ p, ζ p⟫_ℂ).im := by
    rw [← Complex.coe_smul, inner_smul_left, inner_smul_left]
    simp only [conj_ofReal, conj_I, mul_re, neg_re, neg_im, I_re, I_im, ofReal_re, ofReal_im]
    ring
  simp_rw [hprod, Finset.sum_add_distrib, ← Finset.mul_sum, hspin, flatGaugeAdjoint]
  ring

variable (o ρ e) in
/-- **The full eight-real-component linearized gauge-fixed flat Seiberg–Witten operator**
`Ω¹(V) × W⁺ → ℝ × Λ⁺ V × W⁻` at `(b, χ)`. -/
def gaugeFixedFlatSW (hkl : 2 + 2 = finrank ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    ℝ × Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ×
      Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  (flatGaugeAdjoint e χ δb ζ p,
   linearizedFlatCurvature o ρ hkl χ δb ζ p,
   linearizedFlatDirac o ρ e b χ δb ζ p)

theorem gaugeFixedFlatSW_apply (hkl : 2 + 2 = finrank ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatSW o ρ e hkl b χ δb ζ p =
      (flatGaugeAdjoint e χ δb ζ p,
       linearizedFlatCurvature o ρ hkl χ δb ζ p,
       linearizedFlatDirac o ρ e b χ δb ζ p) :=
  (rfl)

/-- `gaugeFixedFlatSW` is independent of the choice of orthonormal basis of `V`. -/
theorem gaugeFixedFlatSW_congr_orthonormalBasis (e' : OrthonormalBasis (Fin 4) ℝ V)
    (hkl : 2 + 2 = finrank ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (χ : V → positiveHalfSpinors o ρ)
    (δb : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ : V → positiveHalfSpinors o ρ) (p : V) :
    gaugeFixedFlatSW o ρ e hkl b χ δb ζ p = gaugeFixedFlatSW o ρ e' hkl b χ δb ζ p := by
  rw [gaugeFixedFlatSW, gaugeFixedFlatSW, flatGaugeAdjoint_congr_orthonormalBasis e',
    linearizedFlatDirac_congr_orthonormalBasis e']

end FlatOperator

/-! ### Exact eight-component normal intertwining theorem -/

section NormalIntertwining

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

attribute [local instance] finiteDimensional_of_finrank_four

omit [FiniteDimensional ℂ W] in
variable (o ρ e) in
/-- The canonical-line spinor field `p ↦ α(z(p)) u₀` pulled back from a plane field `x` along
`normalCoord e`. -/
def normalSpinor (u₀ : positiveHalfSpinors o ρ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (p : V) :
    positiveHalfSpinors o ρ :=
  Vortex.sectionValue x (normalCoord e p) • u₀

omit [FiniteDimensional ℂ W] in
theorem normalSpinor_apply (u₀ : positiveHalfSpinors o ρ)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (p : V) :
    normalSpinor o ρ e u₀ x p = Vortex.sectionValue x (normalCoord e p) • u₀ :=
  (rfl)

omit [Fact (finrank ℝ V = 4)] in
variable (e) in
/-- The connection perturbation `-η₀(z) e₀* + η₁(z) e₁* + y₀(z) e₂* + y₁(z) e₃*` pulled back from
`(y, η) : ℂ → ℝ⁴ × ℝ⁴` along `normalCoord e`. -/
def normalPerturbationForm (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (p : V) :
    V [⋀^Fin 1]→L[ℝ] ℝ :=
  normalFrameForm e (y (normalCoord e p)) (η (normalCoord e p))

omit [Fact (finrank ℝ V = 4)] in
theorem normalPerturbationForm_apply (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (p : V) :
    normalPerturbationForm e y η p =
      normalFrameForm e (y (normalCoord e p)) (η (normalCoord e p)) :=
  (rfl)

omit [FiniteDimensional ℂ W] in
variable (o ρ e) in
/-- The spinor perturbation `2(y₂(z) + i y₃(z)) u₀ + 2(η₂(z) + i η₃(z)) v₀` pulled back from
`(y, η) : ℂ → ℝ⁴ × ℝ⁴` along `normalCoord e`. -/
def normalPerturbationSpinor (u₀ : positiveHalfSpinors o ρ)
    (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (p : V) : positiveHalfSpinors o ρ :=
  normalFrameSpinor o ρ e u₀ (y (normalCoord e p)) (η (normalCoord e p))

omit [FiniteDimensional ℂ W] in
theorem normalPerturbationSpinor_apply (u₀ : positiveHalfSpinors o ρ)
    (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (p : V) :
    normalPerturbationSpinor o ρ e u₀ y η p =
      normalFrameSpinor o ρ e u₀ (y (normalCoord e p)) (η (normalCoord e p)) :=
  (rfl)

/-- Pointwise, `(normalPerturbationForm, normalPerturbationSpinor)` is the image of
`(y (normalCoord e p), η (normalCoord e p))` under `normalDomainEquiv`. -/
@[simp]
theorem normalDomainEquiv_normalPerturbation (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (p : V) :
    normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (y (normalCoord e p), η (normalCoord e p)) =
      (normalPerturbationForm e y η p, normalPerturbationSpinor o ρ e u₀ y η p) :=
  Prod.ext
    (normalDomainEquiv_apply_fst o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ _ _)
    (normalDomainEquiv_apply_snd o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ _ _)

/-- On `(normalConnection e x, normalSpinor o ρ e u₀ x)`, the nonlinear flat Dirac and curvature
defects vanish at `p` if and only if `x` solves `Vortex.equation` at `normalCoord e p`. -/
theorem flatDirac_eq_zero_and_flatCurvatureDefect_eq_zero_iff
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {p : V}
    (hx : DifferentiableAt ℝ x (normalCoord e p)) :
    (flatDirac o ρ e (normalConnection e x) (normalSpinor o ρ e u₀ x) p = 0 ∧
      flatCurvatureDefect o ρ J hkl he h₀ h₂₃ (normalConnection e x)
        (normalSpinor o ρ e u₀ x) p = 0) ↔
      Vortex.equation x (normalCoord e p) = 0 := by
  have hα : DifferentiableAt ℝ (Vortex.sectionValue x ∘ normalCoord e) p :=
    (Vortex.differentiableAt_sectionValue_of_differentiableAt hx).comp p
      (normalCoord e).differentiableAt
  rw [← Submodule.coe_eq_zero,
    show normalSpinor o ρ e u₀ x = fun q ↦ (Vortex.sectionValue x ∘ normalCoord e) q • u₀ from rfl,
    coe_flatDirac_smul_const (normalConnection e x) hα u₀,
    flatCurvatureDefect_eq_zero_iff]
  exact sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff
    hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ hx

omit [Fact (finrank ℝ V = 4)] in
private theorem normalCoord_basis_zero : normalCoord e (e 0) = 0 := by
  apply Complex.ext <;> simp [orthonormal_iff_ite.1 e.orthonormal]

omit [Fact (finrank ℝ V = 4)] in
private theorem normalCoord_basis_one : normalCoord e (e 1) = 0 := by
  apply Complex.ext <;> simp [orthonormal_iff_ite.1 e.orthonormal]

omit [Fact (finrank ℝ V = 4)] in
private theorem normalCoord_basis_three : normalCoord e (e 3) = I := by
  apply Complex.ext <;> simp [orthonormal_iff_ite.1 e.orthonormal]

/-- Canonical-line diagonal polarization formula:
`(√2 / 4) q'(α u₀, δα u₀) = (Re(conj α · δα) / 4) ω_u`. -/
theorem smul_quadraticTwoFormPolar_smul_self_canonical
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (α δα : ℂ) :
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (α • u₀) (δα • u₀) =
      ((conj α * δα).re / 4) • kahlerSelfDual o J hkl he h₀ h₂₃ := by
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hq (c : ℂ) :
      ((√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (c • u₀) : ⋀[ℝ]^2 V) =
        (‖c‖ ^ 2 / 8) • (kahlerSelfDual o J hkl he h₀ h₂₃ : ⋀[ℝ]^2 V) := by
    have hc : cliffordProjection o ρ J.kahlerForm (c • u₀) = c • u₀ := by rw [map_smul, hu₀]
    rw [coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hω h₂ hρ hc,
      norm_smul, hu₀₁, mul_one, coe_kahlerSelfDual, smul_smul, smul_smul]
    congr 1
    ring
  have hpol : quadraticTwoFormPolar o ρ hkl (α • u₀) (δα • u₀) =
      quadraticTwoForm o ρ hkl ((α + δα) • u₀) -
        quadraticTwoForm o ρ hkl (α • u₀) -
        quadraticTwoForm o ρ hkl (δα • u₀) := by
    rw [add_smul, quadraticTwoForm_add]
    abel
  apply Subtype.ext
  rw [hpol, smul_sub, smul_sub, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_smul, Submodule.coe_smul, hq (α + δα), hq α, hq δα, Submodule.coe_smul,
    ← sub_smul, ← sub_smul]
  congr 1
  simp only [← normSq_eq_norm_sq, normSq_apply, add_re, add_im, mul_re, conj_re, conj_im]
  ring

/-- Exterior derivative of `normalPerturbationForm e y η` expressed in the two-vector basis. -/
private theorem alternatingFormEquiv_symm_neg_extDeriv_normalPerturbationForm
    {y η : ℂ → EuclideanSpace ℝ (Fin 4)} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p))
    (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    let z := normalCoord e p
    (alternatingFormEquiv V 2).symm (-extDeriv (normalPerturbationForm e y η) p) =
      (-fderiv ℝ (fun w ↦ η w 0) z 1) • ιMulti ℝ 2 ![e 0, e 2] +
      (-fderiv ℝ (fun w ↦ η w 0) z I) • ιMulti ℝ 2 ![e 0, e 3] +
      (fderiv ℝ (fun w ↦ η w 1) z 1) • ιMulti ℝ 2 ![e 1, e 2] +
      (fderiv ℝ (fun w ↦ η w 1) z I) • ιMulti ℝ 2 ![e 1, e 3] +
      (fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1) • ιMulti ℝ 2 ![e 2, e 3] := by
  intro z
  have hyi (i : Fin 4) : HasFDerivAt (fun q ↦ y (normalCoord e q) i)
      ((fderiv ℝ (fun w ↦ y w i) z).comp (normalCoord e)) p :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hy).hasFDerivAt.comp p
      (normalCoord e).hasFDerivAt
  have hηi (i : Fin 4) : HasFDerivAt (fun q ↦ η (normalCoord e q) i)
      ((fderiv ℝ (fun w ↦ η w i) z).comp (normalCoord e)) p :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hη).hasFDerivAt.comp p
      (normalCoord e).hasFDerivAt
  have hδb : DifferentiableAt ℝ (normalPerturbationForm e y η) p := by
    have hform : normalPerturbationForm e y η =
        fun q ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
          ((-η (normalCoord e q) 0) • innerSL ℝ (e 0) +
            η (normalCoord e q) 1 • innerSL ℝ (e 1) +
            y (normalCoord e q) 0 • innerSL ℝ (e 2) +
            y (normalCoord e q) 1 • innerSL ℝ (e 3)) :=
      funext fun q ↦ normalFrameForm_eq e (y (normalCoord e q)) (η (normalCoord e q))
    rw [hform]
    have h : DifferentiableAt ℝ
        (fun q ↦ (-η (normalCoord e q) 0) • innerSL ℝ (e 0) +
          η (normalCoord e q) 1 • innerSL ℝ (e 1) +
          y (normalCoord e q) 0 • innerSL ℝ (e 2) +
          y (normalCoord e q) 1 • innerSL ℝ (e 3)) p :=
      ((((hηi 0).differentiableAt.neg.smul_const _).add
        ((hηi 1).differentiableAt.smul_const _)).add
        ((hyi 0).differentiableAt.smul_const _)).add
        ((hyi 1).differentiableAt.smul_const _)
    exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
      (0 : Fin 1)).differentiableAt.comp p h
  have key (u w : V) :
      fderiv ℝ (fun q ↦ normalPerturbationForm e y η q (fun _ ↦ w)) p u =
        -fderiv ℝ (fun z' ↦ η z' 0) z (normalCoord e u) * ⟪e 0, w⟫ +
          fderiv ℝ (fun z' ↦ η z' 1) z (normalCoord e u) * ⟪e 1, w⟫ +
          fderiv ℝ (fun z' ↦ y z' 0) z (normalCoord e u) * ⟪e 2, w⟫ +
          fderiv ℝ (fun z' ↦ y z' 1) z (normalCoord e u) * ⟪e 3, w⟫ := by
    have hd : HasFDerivAt
        (fun q ↦ -η (normalCoord e q) 0 * ⟪e 0, w⟫ + η (normalCoord e q) 1 * ⟪e 1, w⟫ +
          y (normalCoord e q) 0 * ⟪e 2, w⟫ + y (normalCoord e q) 1 * ⟪e 3, w⟫) _ p :=
      ((((hηi 0).neg.mul_const ⟪e 0, w⟫).fun_add
        ((hηi 1).mul_const ⟪e 1, w⟫)).fun_add
        ((hyi 0).mul_const ⟪e 2, w⟫)).fun_add
        ((hyi 1).mul_const ⟪e 3, w⟫)
    have hfun : (fun q ↦ normalPerturbationForm e y η q (fun _ ↦ w)) =
        fun q ↦ -η (normalCoord e q) 0 * ⟪e 0, w⟫ + η (normalCoord e q) 1 * ⟪e 1, w⟫ +
          y (normalCoord e q) 0 * ⟪e 2, w⟫ + y (normalCoord e q) 1 * ⟪e 3, w⟫ := by
      funext q
      exact normalFrameForm_apply e (y (normalCoord e q)) (η (normalCoord e q)) w
    rw [hfun, hd.fderiv]
    simp
    ring
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [inner_alternatingFormEquiv_symm_ιMulti, ContinuousAlternatingMap.neg_apply,
    extDeriv_apply_pair_of_differentiableAt hδb, key, key]
  simp only [inner_add_left, real_inner_smul_left, inner_ιMulti_two]
  simp only [ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I _ (normalCoord e u),
    ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I _ (normalCoord e w),
    normalCoord_re, normalCoord_im, smul_eq_mul]
  ring

/-- **Gauge-fixing row intertwining**: on a normal perturbation `(y, η)` at `(normalConnection e x,
normalSpinor o ρ e u₀ x)`, `flatGaugeAdjoint` equals `Vortex.gaugeAdjoint x y (normalCoord e p)`. -/
theorem flatGaugeAdjoint_normalPerturbation
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) {y η : ℂ → EuclideanSpace ℝ (Fin 4)} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p))
    (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    flatGaugeAdjoint e (normalSpinor o ρ e u₀ x) (normalPerturbationForm e y η)
        (normalPerturbationSpinor o ρ e u₀ y η) p =
      Vortex.gaugeAdjoint x y (normalCoord e p) := by
  have hyi (i : Fin 4) : HasFDerivAt (fun q ↦ y (normalCoord e q) i)
      ((fderiv ℝ (fun w ↦ y w i) (normalCoord e p)).comp (normalCoord e)) p :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hy).hasFDerivAt.comp p
      (normalCoord e).hasFDerivAt
  have hηi (i : Fin 4) : HasFDerivAt (fun q ↦ η (normalCoord e q) i)
      ((fderiv ℝ (fun w ↦ η w i) (normalCoord e p)).comp (normalCoord e)) p :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hη).hasFDerivAt.comp p
      (normalCoord e).hasFDerivAt
  have hδb : DifferentiableAt ℝ (normalPerturbationForm e y η) p := by
    have hform : normalPerturbationForm e y η =
        fun q ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
          ((-η (normalCoord e q) 0) • innerSL ℝ (e 0) +
            η (normalCoord e q) 1 • innerSL ℝ (e 1) +
            y (normalCoord e q) 0 • innerSL ℝ (e 2) +
            y (normalCoord e q) 1 • innerSL ℝ (e 3)) :=
      funext fun q ↦ normalFrameForm_eq e (y (normalCoord e q)) (η (normalCoord e q))
    rw [hform]
    have h : DifferentiableAt ℝ
        (fun q ↦ (-η (normalCoord e q) 0) • innerSL ℝ (e 0) +
          η (normalCoord e q) 1 • innerSL ℝ (e 1) +
          y (normalCoord e q) 0 • innerSL ℝ (e 2) +
          y (normalCoord e q) 1 • innerSL ℝ (e 3)) p :=
      ((((hηi 0).differentiableAt.neg.smul_const _).add
        ((hηi 1).differentiableAt.smul_const _)).add
        ((hyi 0).differentiableAt.smul_const _)).add
        ((hyi 1).differentiableAt.smul_const _)
    exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
      (0 : Fin 1)).differentiableAt.comp p h
  have hterm (k : Fin 4) :
      (fderiv ℝ (normalPerturbationForm e y η) p (e k)) (fun _ ↦ e k) =
        -fderiv ℝ (fun z ↦ η z 0) (normalCoord e p) (normalCoord e (e k)) * ⟪e 0, e k⟫ +
          fderiv ℝ (fun z ↦ η z 1) (normalCoord e p) (normalCoord e (e k)) * ⟪e 1, e k⟫ +
          fderiv ℝ (fun z ↦ y z 0) (normalCoord e p) (normalCoord e (e k)) * ⟪e 2, e k⟫ +
          fderiv ℝ (fun z ↦ y z 1) (normalCoord e p) (normalCoord e (e k)) * ⟪e 3, e k⟫ := by
    rw [← fderiv_continuousAlternatingMap_apply_const_apply hδb]
    have hd : HasFDerivAt
        (fun q ↦ -η (normalCoord e q) 0 * ⟪e 0, e k⟫ + η (normalCoord e q) 1 * ⟪e 1, e k⟫ +
          y (normalCoord e q) 0 * ⟪e 2, e k⟫ + y (normalCoord e q) 1 * ⟪e 3, e k⟫) _ p :=
      ((((hηi 0).neg.mul_const ⟪e 0, e k⟫).fun_add
        ((hηi 1).mul_const ⟪e 1, e k⟫)).fun_add
        ((hyi 0).mul_const ⟪e 2, e k⟫)).fun_add
        ((hyi 1).mul_const ⟪e 3, e k⟫)
    have hfun : (fun q ↦ normalPerturbationForm e y η q (fun _ ↦ e k)) =
        fun q ↦ -η (normalCoord e q) 0 * ⟪e 0, e k⟫ + η (normalCoord e q) 1 * ⟪e 1, e k⟫ +
          y (normalCoord e q) 0 * ⟪e 2, e k⟫ + y (normalCoord e q) 1 * ⟪e 3, e k⟫ := by
      funext q
      exact normalFrameForm_apply e (y (normalCoord e q)) (η (normalCoord e q)) (e k)
    rw [hfun, hd.fderiv]
    simp
    ring
  have hdiv : (∑ k : Fin 4, (fderiv ℝ (normalPerturbationForm e y η) p (e k)) (fun _ ↦ e k)) =
      fderiv ℝ (fun z ↦ y z 0) (normalCoord e p) 1 +
        fderiv ℝ (fun z ↦ y z 1) (normalCoord e p) I := by
    rw [Fin.sum_univ_four]
    simp only [hterm, normalCoord_basis_zero, normalCoord_basis_one, normalCoord_apply_two,
      normalCoord_basis_three, map_zero, orthonormal_iff_ite.1 e.orthonormal]
    norm_num
  have horth := inner_antiCanonicalSpinor_eq_zero hQ hkl he h₀ h₂₃ hρ hu₀
  have hu₀_in : ⟪u₀, u₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hu₀₁]; norm_num
  have hspin : (⟪normalSpinor o ρ e u₀ x p, normalPerturbationSpinor o ρ e u₀ y η p⟫_ℂ).im / 4 =
      x (normalCoord e p) 2 * y (normalCoord e p) 3 -
        x (normalCoord e p) 3 * y (normalCoord e p) 2 := by
    simp only [normalSpinor, normalPerturbationSpinor, normalFrameSpinor_eq,
      Vortex.sectionValue_apply, inner_add_right, inner_smul_left, inner_smul_right, hu₀_in, horth,
      mul_one, mul_zero, add_zero, map_mul, map_add, conj_ofReal, conj_I, map_ofNat]
    simp only [mul_im, add_im, mul_re, add_re, neg_re, neg_im, ofReal_re, ofReal_im, I_re, I_im,
      re_ofNat, im_ofNat]
    ring
  rw [flatGaugeAdjoint, hdiv, hspin, Vortex.gaugeAdjoint_def]
  ring

/-- **Curvature row intertwining**: on a normal perturbation `(y, η)` at `(normalConnection e x,
normalSpinor o ρ e u₀ x)`, `linearizedFlatCurvature` expands in `(ω_u, ρ₁, ρ₂)` as the vortex
curvature linearization `L₁ ω_u` plus the connection components `A₀ ρ₁ + A₁ ρ₂` of `L_x* η`. -/
theorem linearizedFlatCurvature_normalPerturbation
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) {y η : ℂ → EuclideanSpace ℝ (Fin 4)} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p))
    (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    let z := normalCoord e p
    linearizedFlatCurvature o ρ hkl (normalSpinor o ρ e u₀ x) (normalPerturbationForm e y η)
        (normalPerturbationSpinor o ρ e u₀ y η) p =
      Vortex.linearizedEquation x y z 0 • kahlerSelfDual o J hkl he h₀ h₂₃ +
        Vortex.gaugeFixedAdjoint x η z 0 • antiInvariantSelfDual₁ o e hkl he +
        Vortex.gaugeFixedAdjoint x η z 1 • antiInvariantSelfDual₂ o e hkl he := by
  intro z
  have h12 : o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 2]) = ιMulti ℝ 2 ![e 0, e 3] := by
    rw [← o.hodgeStar_ιMulti_zero_three hkl he, o.hodgeStar_hodgeStar_of_even even_two hkl]
  have h13 : o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 3]) = -ιMulti ℝ 2 ![e 0, e 2] := by
    rw [← neg_neg (ιMulti ℝ 2 ![e 1, e 3]), ← o.hodgeStar_ιMulti_zero_two hkl he, map_neg,
      o.hodgeStar_hodgeStar_of_even even_two hkl]
  -- Differential part `(√2 / 2) (δF + ⋆δF)`.
  have hdiff :
      selfDualTwoVector o hkl
          ((alternatingFormEquiv V 2).symm (-extDeriv (normalPerturbationForm e y η) p)) =
        (fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1) •
            kahlerSelfDual o J hkl he h₀ h₂₃ +
          (-fderiv ℝ (fun w ↦ η w 0) z 1 - fderiv ℝ (fun w ↦ η w 1) z I) •
            antiInvariantSelfDual₁ o e hkl he +
          (-fderiv ℝ (fun w ↦ η w 0) z I + fderiv ℝ (fun w ↦ η w 1) z 1) •
            antiInvariantSelfDual₂ o e hkl he := by
    apply Subtype.ext
    rw [coe_selfDualTwoVector,
      alternatingFormEquiv_symm_neg_extDeriv_normalPerturbationForm hy hη]
    simp only [Submodule.coe_add, Submodule.coe_smul, coe_kahlerSelfDual,
      coe_antiInvariantSelfDual₁, coe_antiInvariantSelfDual₂,
      AlmostComplexStructure.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂₃,
      map_add, map_smul, o.hodgeStar_ιMulti_zero_two hkl he,
      o.hodgeStar_ιMulti_zero_three hkl he, o.hodgeStar_ιMulti_two_three hkl he, h12, h13]
    module
  -- Zeroth-order polarization `(√2 / 4) q'(α u₀, δα u₀ + β v₀)`.
  set α := Vortex.sectionValue x z
  set δα : ℂ := 2 * ((y z 2 : ℂ) + (y z 3 : ℂ) * I)
  set β : ℂ := 2 * ((η z 2 : ℂ) + (η z 3 : ℂ) * I)
  have hzeroth :
      (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (normalSpinor o ρ e u₀ x p)
          (normalPerturbationSpinor o ρ e u₀ y η p) =
        (x z 2 * y z 2 + x z 3 * y z 3) • kahlerSelfDual o J hkl he h₀ h₂₃ +
          (x z 2 * η z 3 - x z 3 * η z 2) • antiInvariantSelfDual₁ o e hkl he +
          (-x z 2 * η z 2 - x z 3 * η z 3) • antiInvariantSelfDual₂ o e hkl he := by
    rw [normalSpinor, normalPerturbationSpinor, normalFrameSpinor_eq,
      show Vortex.sectionValue x (normalCoord e p) = α from rfl,
      show ((2 : ℂ) * ((y (normalCoord e p) 2 : ℂ) + (y (normalCoord e p) 3 : ℂ) * I)) = δα
        from rfl,
      show ((2 : ℂ) * ((η (normalCoord e p) 2 : ℂ) + (η (normalCoord e p) 3 : ℂ) * I)) = β
        from rfl,
      map_add, smul_add,
      smul_quadraticTwoFormPolar_smul_self_canonical hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ α δα,
      smul_quadraticTwoFormPolar_smul_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hρ hu₀ hu₀₁ α β]
    have hc1 : (conj α * δα).re / 4 = x z 2 * y z 2 + x z 3 * y z 3 := by
      simp only [α, δα, Vortex.sectionValue_apply, map_mul, map_add, conj_ofReal, conj_I,
        map_ofNat, mul_re, add_re, mul_im, add_im, neg_re, neg_im, ofReal_re, ofReal_im, I_re,
        I_im, re_ofNat, im_ofNat]
      ring
    have hc2 : (conj α * β).im / 4 = x z 2 * η z 3 - x z 3 * η z 2 := by
      simp only [α, β, Vortex.sectionValue_apply, map_mul, map_add, conj_ofReal, conj_I,
        map_ofNat, mul_im, add_im, mul_re, add_re, neg_re, neg_im, ofReal_re, ofReal_im, I_re,
        I_im, re_ofNat, im_ofNat]
      ring
    have hc3 : (conj α * β).re / 4 = x z 2 * η z 2 + x z 3 * η z 3 := by
      simp only [α, β, Vortex.sectionValue_apply, map_mul, map_add, conj_ofReal, conj_I,
        map_ofNat, mul_re, add_re, mul_im, add_im, neg_re, neg_im, ofReal_re, ofReal_im, I_re,
        I_im, re_ofNat, im_ofNat]
      ring
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    rw [hc1, hc2, hc3]
    module
  have hsum :
      linearizedFlatCurvature o ρ hkl (normalSpinor o ρ e u₀ x) (normalPerturbationForm e y η)
          (normalPerturbationSpinor o ρ e u₀ y η) p =
        ((fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1) +
            (x z 2 * y z 2 + x z 3 * y z 3)) • kahlerSelfDual o J hkl he h₀ h₂₃ +
          ((-fderiv ℝ (fun w ↦ η w 0) z 1 - fderiv ℝ (fun w ↦ η w 1) z I) +
            (x z 2 * η z 3 - x z 3 * η z 2)) • antiInvariantSelfDual₁ o e hkl he +
          ((-fderiv ℝ (fun w ↦ η w 0) z I + fderiv ℝ (fun w ↦ η w 1) z 1) +
            (-x z 2 * η z 2 - x z 3 * η z 3)) • antiInvariantSelfDual₂ o e hkl he := by
    refine (congrArg₂ (· + ·) hdiff hzeroth).trans ?_
    simp only [add_smul]
    abel
  have hs0 : (fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1) +
      (x z 2 * y z 2 + x z 3 * y z 3) = Vortex.linearizedEquation x y z 0 := by
    rw [Vortex.linearizedEquation_apply_zero]; ring
  have hs1 : (-fderiv ℝ (fun w ↦ η w 0) z 1 - fderiv ℝ (fun w ↦ η w 1) z I) +
      (x z 2 * η z 3 - x z 3 * η z 2) = Vortex.gaugeFixedAdjoint x η z 0 := by
    rw [Vortex.gaugeFixedAdjoint_apply_zero]; ring
  have hs2 : (-fderiv ℝ (fun w ↦ η w 0) z I + fderiv ℝ (fun w ↦ η w 1) z 1) +
      (-x z 2 * η z 2 - x z 3 * η z 3) = Vortex.gaugeFixedAdjoint x η z 1 := by
    rw [Vortex.gaugeFixedAdjoint_apply_one]; ring
  rw [hsum]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (congrArg (· • _) hs0) (congrArg (· • _) hs1))
    (congrArg (· • _) hs2)

/-- **Dirac row intertwining**: on a normal perturbation `(y, η)` at `(normalConnection e x,
normalSpinor o ρ e u₀ x)`, `linearizedFlatDirac` expands in `(c(e₂) u₀, c(e₀) u₀)` as the
linearized `∂bar_a` rows of `L_x y` along `c(e₂) u₀` minus the spinor rows of `L_x* η` along
`c(e₀) u₀`. -/
theorem linearizedFlatDirac_normalPerturbation
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) {y η : ℂ → EuclideanSpace ℝ (Fin 4)} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p))
    (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    let z := normalCoord e p
    linearizedFlatDirac o ρ e (normalConnection e x) (normalSpinor o ρ e u₀ x)
        (normalPerturbationForm e y η) (normalPerturbationSpinor o ρ e u₀ y η) p =
      ((2 : ℂ) * ((Vortex.linearizedEquation x y z 1 : ℂ) +
          (Vortex.linearizedEquation x y z 2 : ℂ) * I)) •
          positiveHalfSpinCliffordMul o ρ (e 2) u₀ -
        ((2 : ℂ) * ((Vortex.gaugeFixedAdjoint x η z 2 : ℂ) +
          (Vortex.gaugeFixedAdjoint x η z 3 : ℂ) * I)) •
          positiveHalfSpinCliffordMul o ρ (e 0) u₀ := by
  intro z
  set v₀ := antiCanonicalSpinor o ρ e u₀
  set w₂ : W := ρ (ι Q (e 2)) u₀
  set w₀ : W := ρ (ι Q (e 0)) u₀
  have h1u : ρ (ι Q (e 1)) u₀ = I • w₀ := by
    rw [← h₀, ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀]
  have h3u : ρ (ι Q (e 3)) u₀ = I • w₂ := by
    rw [← h₂₃, ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀]
  have h2v : ρ (ι Q (e 2)) v₀ = w₀ :=
    ι_apply_two_antiCanonicalSpinor hQ u₀
  have h3v : ρ (ι Q (e 3)) v₀ = -I • w₀ :=
    ι_apply_three_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀
  -- Split `normalPerturbationSpinor` into `(sectionValue y ∘ normalCoord e) • u₀ + ...`.
  have hsplit : normalPerturbationSpinor o ρ e u₀ y η =
      (fun q ↦ (Vortex.sectionValue y ∘ normalCoord e) q • u₀) +
        (fun q ↦ (Vortex.sectionValue η ∘ normalCoord e) q • v₀) := by
    funext q
    simp [normalPerturbationSpinor, normalFrameSpinor_eq, Vortex.sectionValue_apply, v₀]
  have hy_sec : DifferentiableAt ℝ (Vortex.sectionValue y ∘ normalCoord e) p :=
    (Vortex.differentiableAt_sectionValue_of_differentiableAt hy).comp p
      (normalCoord e).differentiableAt
  have hη_sec : DifferentiableAt ℝ (Vortex.sectionValue η ∘ normalCoord e) p :=
    (Vortex.differentiableAt_sectionValue_of_differentiableAt hη).comp p
      (normalCoord e).differentiableAt
  let Lu : ℂ →L[ℝ] positiveHalfSpinors o ρ :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight u₀).restrictScalars ℝ
  let Lv : ℂ →L[ℝ] positiveHalfSpinors o ρ :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight v₀).restrictScalars ℝ
  have hdu : DifferentiableAt ℝ (fun q ↦ (Vortex.sectionValue y ∘ normalCoord e) q • u₀) p :=
    Lu.differentiableAt.comp p hy_sec
  have hdv : DifferentiableAt ℝ (fun q ↦ (Vortex.sectionValue η ∘ normalCoord e) q • v₀) p :=
    Lv.differentiableAt.comp p hη_sec
  have hcov_add (k : Fin 4) :
      spinorCovariantDeriv (normalConnection e x) (normalPerturbationSpinor o ρ e u₀ y η) p (e k) =
        covariantDeriv (normalConnection e x) (Vortex.sectionValue y ∘ normalCoord e) p (e k) • u₀ +
          covariantDeriv (normalConnection e x)
            (Vortex.sectionValue η ∘ normalCoord e) p (e k) • v₀ := by
    rw [hsplit]
    have hf : fderiv ℝ ((fun q ↦ (Vortex.sectionValue y ∘ normalCoord e) q • u₀) +
          (fun q ↦ (Vortex.sectionValue η ∘ normalCoord e) q • v₀)) p (e k) =
        fderiv ℝ (fun q ↦ (Vortex.sectionValue y ∘ normalCoord e) q • u₀) p (e k) +
          fderiv ℝ (fun q ↦ (Vortex.sectionValue η ∘ normalCoord e) q • v₀) p (e k) := by
      rw [fderiv_add hdu hdv, add_apply]
    have h1 := spinorCovariantDeriv_smul_const (normalConnection e x) hy_sec u₀ (e k)
    have h2 := spinorCovariantDeriv_smul_const (normalConnection e x) hη_sec v₀ (e k)
    simp only [spinorCovariantDeriv_apply] at h1 h2 ⊢
    rw [hf, Pi.add_apply, smul_add, smul_add, ← h1, ← h2]
    abel
  -- Covariant derivatives along `e₀, e₁` vanish, and along `e₂, e₃` give normal derivatives.
  have hcov_plane (g : ℂ → EuclideanSpace ℝ (Fin 4))
      (hg : DifferentiableAt ℝ g (normalCoord e p)) (v : V) :
      covariantDeriv (normalConnection e x) (Vortex.sectionValue g ∘ normalCoord e) p v =
        fderiv ℝ (Vortex.sectionValue g) z (normalCoord e v) +
          I * (x z 0 * (normalCoord e v).re + x z 1 * (normalCoord e v).im) *
            Vortex.sectionValue g z := by
    have hd := ((Vortex.differentiableAt_sectionValue_of_differentiableAt hg).hasFDerivAt.comp p
      (normalCoord e).hasFDerivAt).fderiv
    rw [covariantDeriv_apply, hd, normalConnection_apply]
    simp [z]
  have hcov_term (k : Fin 4) :
      ρ (ι Q (e k))
          (spinorCovariantDeriv (normalConnection e x)
            (normalPerturbationSpinor o ρ e u₀ y η) p (e k)) =
        covariantDeriv (normalConnection e x)
            (Vortex.sectionValue y ∘ normalCoord e) p (e k) • ρ (ι Q (e k)) u₀ +
          covariantDeriv (normalConnection e x)
            (Vortex.sectionValue η ∘ normalCoord e) p (e k) • ρ (ι Q (e k)) v₀ := by
    rw [hcov_add k, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      map_add, map_smul, map_smul]
  have hδb_term (k : Fin 4) :
      (positiveHalfSpinCliffordMul o ρ (e k)
          (normalPerturbationForm e y η p (fun _ ↦ e k) •
            (I • normalSpinor o ρ e u₀ x p)) : W) =
        ((normalFrameForm e (y z) (η z) (fun _ ↦ e k) : ℂ) * I *
          Vortex.sectionValue x z) • ρ (ι Q (e k)) u₀ := by
    simp only [show normalPerturbationForm e y η p = normalFrameForm e (y z) (η z) from rfl,
      show normalSpinor o ρ e u₀ x p = Vortex.sectionValue x z • u₀ from rfl,
      ← Complex.coe_smul, smul_smul, map_smul, Submodule.coe_smul,
      coe_positiveHalfSpinCliffordMul_apply, ← mul_assoc]
  have hy2 : DifferentiableAt ℝ (fun w ↦ y w 2) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 4)).differentiableAt.comp z hy
  have hy3 : DifferentiableAt ℝ (fun w ↦ y w 3) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (3 : Fin 4)).differentiableAt.comp z hy
  have hη2 : DifferentiableAt ℝ (fun w ↦ η w 2) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 4)).differentiableAt.comp z hη
  have hη3 : DifferentiableAt ℝ (fun w ↦ η w 3) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (3 : Fin 4)).differentiableAt.comp z hη
  set cy₂ : ℂ := (2 : ℂ) * ((fderiv ℝ (fun w ↦ y w 2) z 1 : ℂ) +
      (fderiv ℝ (fun w ↦ y w 3) z 1 : ℂ) * I) + I * (x z 0 : ℂ) * Vortex.sectionValue y z
  set cy₃ : ℂ := (2 : ℂ) * ((fderiv ℝ (fun w ↦ y w 2) z I : ℂ) +
      (fderiv ℝ (fun w ↦ y w 3) z I : ℂ) * I) + I * (x z 1 : ℂ) * Vortex.sectionValue y z
  set cη₂ : ℂ := (2 : ℂ) * ((fderiv ℝ (fun w ↦ η w 2) z 1 : ℂ) +
      (fderiv ℝ (fun w ↦ η w 3) z 1 : ℂ) * I) + I * (x z 0 : ℂ) * Vortex.sectionValue η z
  set cη₃ : ℂ := (2 : ℂ) * ((fderiv ℝ (fun w ↦ η w 2) z I : ℂ) +
      (fderiv ℝ (fun w ↦ η w 3) z I : ℂ) * I) + I * (x z 1 : ℂ) * Vortex.sectionValue η z
  have hcov0 : ρ (ι Q (e 0))
      (spinorCovariantDeriv (normalConnection e x)
        (normalPerturbationSpinor o ρ e u₀ y η) p (e 0)) = 0 := by
    rw [hcov_term 0, hcov_plane y hy, hcov_plane η hη, normalCoord_basis_zero]
    simp
  have hcov1 : ρ (ι Q (e 1))
      (spinorCovariantDeriv (normalConnection e x)
        (normalPerturbationSpinor o ρ e u₀ y η) p (e 1)) = 0 := by
    rw [hcov_term 1, hcov_plane y hy, hcov_plane η hη, normalCoord_basis_one]
    simp
  have hcov2 : ρ (ι Q (e 2))
      (spinorCovariantDeriv (normalConnection e x)
        (normalPerturbationSpinor o ρ e u₀ y η) p (e 2)) = cy₂ • w₂ + cη₂ • w₀ := by
    rw [hcov_term 2, hcov_plane y hy, hcov_plane η hη, normalCoord_apply_two,
      Vortex.fderiv_sectionValue_apply hy2 hy3, Vortex.fderiv_sectionValue_apply hη2 hη3, h2v]
    simp [cy₂, cη₂, w₂]
  have hcov3 : ρ (ι Q (e 3))
      (spinorCovariantDeriv (normalConnection e x)
        (normalPerturbationSpinor o ρ e u₀ y η) p (e 3)) =
        (cy₃ * I) • w₂ + (-(cη₃ * I)) • w₀ := by
    rw [hcov_term 3, hcov_plane y hy, hcov_plane η hη, normalCoord_basis_three,
      Vortex.fderiv_sectionValue_apply hy2 hy3, Vortex.fderiv_sectionValue_apply hη2 hη3,
      h3u, h3v, smul_smul, smul_smul, mul_neg]
    simp [cy₃, cη₃]
  have hδb0 : (positiveHalfSpinCliffordMul o ρ (e 0)
      (normalPerturbationForm e y η p (fun _ ↦ e 0) •
        (I • normalSpinor o ρ e u₀ x p)) : W) =
      ((-(η z 0 : ℂ)) * I * Vortex.sectionValue x z) • w₀ := by
    rw [hδb_term 0, normalFrameForm_apply]
    simp [orthonormal_iff_ite.1 e.orthonormal, w₀]
  have hδb1 : (positiveHalfSpinCliffordMul o ρ (e 1)
      (normalPerturbationForm e y η p (fun _ ↦ e 1) •
        (I • normalSpinor o ρ e u₀ x p)) : W) =
      ((η z 1 : ℂ) * I * Vortex.sectionValue x z * I) • w₀ := by
    rw [hδb_term 1, normalFrameForm_apply, h1u, smul_smul]
    simp [orthonormal_iff_ite.1 e.orthonormal]
  have hδb2 : (positiveHalfSpinCliffordMul o ρ (e 2)
      (normalPerturbationForm e y η p (fun _ ↦ e 2) •
        (I • normalSpinor o ρ e u₀ x p)) : W) =
      ((y z 0 : ℂ) * I * Vortex.sectionValue x z) • w₂ := by
    rw [hδb_term 2, normalFrameForm_apply]
    simp [orthonormal_iff_ite.1 e.orthonormal, w₂]
  have hδb3 : (positiveHalfSpinCliffordMul o ρ (e 3)
      (normalPerturbationForm e y η p (fun _ ↦ e 3) •
        (I • normalSpinor o ρ e u₀ x p)) : W) =
      ((y z 1 : ℂ) * I * Vortex.sectionValue x z * I) • w₂ := by
    rw [hδb_term 3, normalFrameForm_apply, h3u, smul_smul]
    simp [orthonormal_iff_ite.1 e.orthonormal]
  apply Subtype.ext
  rw [linearizedFlatDirac, Submodule.coe_add, coe_flatDirac, Fin.sum_univ_four,
    Fin.sum_univ_four, Submodule.coe_add, Submodule.coe_add, Submodule.coe_add,
    hcov0, hcov1, hcov2, hcov3, hδb0, hδb1, hδb2, hδb3, Submodule.coe_sub,
    Submodule.coe_smul, Submodule.coe_smul, coe_positiveHalfSpinCliffordMul_apply,
    coe_positiveHalfSpinCliffordMul_apply,
    show ρ (ι Q (e 2)) u₀ = w₂ from rfl, show ρ (ι Q (e 0)) u₀ = w₀ from rfl]
  have hlhs :
      (0 + 0 + (cy₂ • w₂ + cη₂ • w₀) + ((cy₃ * I) • w₂ + -(cη₃ * I) • w₀)) +
        (((-(η z 0 : ℂ)) * I * Vortex.sectionValue x z) • w₀ +
          ((η z 1 : ℂ) * I * Vortex.sectionValue x z * I) • w₀ +
          ((y z 0 : ℂ) * I * Vortex.sectionValue x z) • w₂ +
          ((y z 1 : ℂ) * I * Vortex.sectionValue x z * I) • w₂) =
        (cy₂ + cy₃ * I + (y z 0 : ℂ) * I * Vortex.sectionValue x z +
            (y z 1 : ℂ) * I * Vortex.sectionValue x z * I) • w₂ +
          (cη₂ + -(cη₃ * I) + (-(η z 0 : ℂ)) * I * Vortex.sectionValue x z +
            (η z 1 : ℂ) * I * Vortex.sectionValue x z * I) • w₀ := by
    simp only [add_smul]
    abel
  rw [hlhs]
  have hc₂ :
      cy₂ + cy₃ * I + (y z 0 : ℂ) * I * Vortex.sectionValue x z +
        (y z 1 : ℂ) * I * Vortex.sectionValue x z * I =
      (2 : ℂ) * ((Vortex.linearizedEquation x y z 1 : ℂ) +
        (Vortex.linearizedEquation x y z 2 : ℂ) * I) := by
    apply Complex.ext <;> simp [cy₂, cy₃, Vortex.sectionValue_apply] <;> ring
  have hc₀ :
      cη₂ + -(cη₃ * I) + (-(η z 0 : ℂ)) * I * Vortex.sectionValue x z +
        (η z 1 : ℂ) * I * Vortex.sectionValue x z * I =
      -((2 : ℂ) * ((Vortex.gaugeFixedAdjoint x η z 2 : ℂ) +
        (Vortex.gaugeFixedAdjoint x η z 3 : ℂ) * I)) := by
    apply Complex.ext <;> simp [cη₂, cη₃, Vortex.sectionValue_apply] <;> ring
  rw [hc₂, hc₀, neg_smul, sub_eq_add_neg]

/-- **Full eight-real-component normal intertwining theorem**: at *every* background plane field `x`
(off-shell, with no regularity hypothesis on `x`), the linearized gauge-fixed flat Seiberg–Witten
operator at `(normalConnection e x, normalSpinor o ρ e u₀ x)` applied to the normal perturbation
`(normalPerturbationForm e y η, normalPerturbationSpinor o ρ e u₀ y η)` equals the image under
`normalTargetEquiv` of `(Vortex.gaugeFixedOperator x y, Vortex.gaugeFixedAdjoint x η)`. -/
theorem gaugeFixedFlatSW_normalPerturbation
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) {y η : ℂ → EuclideanSpace ℝ (Fin 4)} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p))
    (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    gaugeFixedFlatSW o ρ e hkl (normalConnection e x) (normalSpinor o ρ e u₀ x)
        (normalPerturbationForm e y η) (normalPerturbationSpinor o ρ e u₀ y η) p =
      normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (Vortex.gaugeFixedOperator x y (normalCoord e p),
          Vortex.gaugeFixedAdjoint x η (normalCoord e p)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [gaugeFixedFlatSW, normalTargetEquiv_apply_fst, Vortex.gaugeFixedOperator_apply_zero]
    exact flatGaugeAdjoint_normalPerturbation hQ hkl he h₀ h₂₃ hρ hu₀ hu₀₁ x hy hη
  · rw [gaugeFixedFlatSW, normalTargetEquiv_apply_snd_fst, Vortex.gaugeFixedOperator_apply_one]
    exact linearizedFlatCurvature_normalPerturbation hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ x hy hη
  · rw [gaugeFixedFlatSW, normalTargetEquiv_apply_snd_snd, Vortex.gaugeFixedOperator_apply_two,
      Vortex.gaugeFixedOperator_apply_three]
    exact linearizedFlatDirac_normalPerturbation hQ hkl he h₀ h₂₃ hu₀ x hy hη

end NormalIntertwining

end TauCeti.SeibergWitten
