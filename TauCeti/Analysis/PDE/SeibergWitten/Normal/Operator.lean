/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.FlatLimit
public import TauCeti.Analysis.PDE.SeibergWitten.FlatOperator
public import TauCeti.Analysis.PDE.SeibergWitten.Normal.Frame
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Complex.OperatorNorm

/-!
# Normal intertwining for the gauge-fixed flat Seiberg–Witten operator

On an abstract oriented four-dimensional real inner product space `V` with almost complex structure
`J`, an adapted orthonormal frame `e` splits `V` into tangential and normal complex planes via
`normalCoord e : V → ℂ`. Pulling back `x` gives a canonical-line background solving the flat
Seiberg–Witten equations iff `Vortex.equation x = 0`.

To reduce the linearized four-dimensional Seiberg–Witten problem along the normal plane to the
plane-vortex model, we define the pulled-back canonical-line spinor and normal perturbations and
prove that at any background `x`, the eight-real-component linearized gauge-fixed operator
`gaugeFixedFlatOperator` intertwines normal perturbations from `(y, η)` with `(L_x y, L_x* η)`.

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
  let hyi i := (hasFDerivAt_coord_comp_normalCoord hy i).differentiableAt
  let hηi i := (hasFDerivAt_coord_comp_normalCoord hη i).differentiableAt
  exact ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
    (0 : Fin 1)).differentiableAt.comp p (((((hηi 0).neg.smul_const (innerSL ℝ (e 0))).fun_add
      ((hηi 1).smul_const (innerSL ℝ (e 1)))).fun_add
      ((hyi 0).smul_const (innerSL ℝ (e 2)))).fun_add
      ((hyi 1).smul_const (innerSL ℝ (e 3))))).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun q ↦ by simp [normalPerturbationForm_apply, normalFrameForm_eq]
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
  have hd : HasFDerivAt (fun q ↦ normalPerturbationForm e y η q (fun _ ↦ w)) _ p :=
    (((((hηi 0).neg.mul_const ⟪e 0, w⟫).fun_add ((hηi 1).mul_const ⟪e 1, w⟫)).fun_add
      ((hyi 0).mul_const ⟪e 2, w⟫)).fun_add ((hyi 1).mul_const ⟪e 3, w⟫)).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun q ↦ normalFrameForm_apply e _ _ w
  rw [hd.fderiv]; simp; ring
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
  Prod.ext (normalDomainEquiv_apply_fst ..) (normalDomainEquiv_apply_snd ..)
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
    rw [coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hω h₂ hρ
      (by rw [map_smul, hu₀]), norm_smul, hu₀₁, mul_one, coe_kahlerSelfDual, smul_smul, smul_smul]
    congr 1; ring
  apply Subtype.ext
  rw [show quadraticTwoFormPolar o ρ hkl (α • u₀) (δα • u₀) =
      quadraticTwoForm o ρ hkl ((α + δα) • u₀) -
        quadraticTwoForm o ρ hkl (α • u₀) - quadraticTwoForm o ρ hkl (δα • u₀) by
      rw [add_smul, quadraticTwoForm_add]; abel]
  simp only [smul_sub, Submodule.coe_sub, Submodule.coe_smul, hq, ← sub_smul]; congr 1
  simp [← normSq_eq_norm_sq, normSq_apply]; ring
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
  rw [flatGaugeAdjoint_def, hdiv, hspin, Vortex.gaugeAdjoint_def]; ring
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
        (-x z 2 * η z 2 - x z 3 * η z 3) • antiInvariantSelfDual₂ o e hkl he := by
    rw [normalSpinor_apply, normalPerturbationSpinor_apply, normalFrameSpinor_eq, map_add,
      smul_add, smul_quadraticTwoFormPolar_smul_smul_of_cliffordProjection_apply_eq_self
        hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁,
      smul_quadraticTwoFormPolar_smul_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hρ hu₀ hu₀₁]
    simp only [z, conj_sectionValue_mul_two, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im,
      I_re, I_im, re_ofNat, im_ofNat]; module
  rw [linearizedFlatCurvature_apply, hdiff, hzeroth]
  simp only [Vortex.linearizedEquation_apply_zero, Vortex.gaugeFixedAdjoint_apply_zero,
    Vortex.gaugeFixedAdjoint_apply_one]; module
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
  have hsec {g : ℂ → E4} (hg : DifferentiableAt ℝ g z) :
      DifferentiableAt ℝ (Vortex.sectionValue g ∘ normalCoord e) p :=
    (Vortex.differentiableAt_sectionValue_of_differentiableAt hg).comp p
      (normalCoord e).differentiableAt
  have hsmul_d {g : ℂ → E4} (hg : DifferentiableAt ℝ g z) (ψ : PosSpin(o, ρ)) :
      DifferentiableAt ℝ (fun q ↦ (Vortex.sectionValue g ∘ normalCoord e) q • ψ) p :=
    (((ContinuousLinearMap.id ℂ ℂ).smulRight ψ).restrictScalars ℝ).differentiableAt.comp p (hsec hg)
  have h3u := h₂₃ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 2)
  rw [show normalPerturbationSpinor o ρ e u₀ y η =
      (fun q ↦ (Vortex.sectionValue y ∘ normalCoord e) q • u₀) +
        (fun q ↦ (Vortex.sectionValue η ∘ normalCoord e) q • v₀) from funext fun q ↦ by
      simp [normalPerturbationSpinor, normalFrameSpinor_eq, Vortex.sectionValue_apply, v₀],
    flatDirac_add (normalConnection e x) (hsmul_d hy u₀) (hsmul_d hη v₀), Submodule.coe_add,
    coe_flatDirac_smul_const _ (hsec hy), coe_flatDirac_smul_const _ (hsec hη),
    sum_covariantDeriv_normalConnection_smul_ι x hy u₀,
    sum_covariantDeriv_normalConnection_smul_ι x hη v₀, ι_apply_two_antiCanonicalSpinor hQ u₀,
    h3u, ι_apply_three_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀]
  simp only [z, smul_smul, mul_neg]; module
omit h₂ hρ hu₀₁ in private theorem coe_sum_normalPerturbationForm_smul_normalSpinor (x y η : ℂ → E4)
    (p : V) :
    let z := normalCoord e p
    ((∑ k : Fin 4, cMul(o, ρ, e k, normalPerturbationForm e y η p (fun _ ↦ e k) •
      (I • normalSpinor o ρ e u₀ x p)) : NegSpin(Q, o, ρ)) : W) =
      (((y z 0 : ℂ) * I + (y z 1 : ℂ) * I * I) * Vortex.sectionValue x z) • ρ (ι Q (e 2)) u₀ +
        (((-(η z 0 : ℂ)) * I + (η z 1 : ℂ) * I * I) * Vortex.sectionValue x z) •
          ρ (ι Q (e 0)) u₀ := by
  intro z
  have h1u := h₀ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 0)
  have h3u := h₂₃ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 2)
  have hδb (k : Fin 4) : (cMul(o, ρ, e k,
      normalPerturbationForm e y η p (fun _ ↦ e k) • (I • normalSpinor o ρ e u₀ x p)) : W) =
      ((normalFrameForm e (y z) (η z) (fun _ ↦ e k) : ℂ) * I * Vortex.sectionValue x z) •
        ρ (ι Q (e k)) u₀ := by
    rw [normalPerturbationForm_apply, normalSpinor_apply]; simp only [z, ← Complex.coe_smul,
      smul_smul, map_smul, Submodule.coe_smul, coe_halfSpinCliffordMul_apply_apply,
      LinearEquiv.coe_ofEq_apply, ← mul_assoc]
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
          (Vortex.linearizedEquation x y z 2 : ℂ) * I)) • cMul(o, ρ, e 2, u₀) -
        ((2 : ℂ) * ((Vortex.gaugeFixedAdjoint x η z 2 : ℂ) +
          (Vortex.gaugeFixedAdjoint x η z 3 : ℂ) * I)) • cMul(o, ρ, e 0, u₀) := by
  intro z; have hpy (i : Fin 4) := (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy
  have hpη (i : Fin 4) := (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hη
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
  apply Subtype.ext; rw [linearizedFlatDirac_apply, Submodule.coe_add,
    coe_flatDirac_normalPerturbationSpinor hQ hkl he h₀ h₂₃ hu₀ x hy hη,
    coe_sum_normalPerturbationForm_smul_normalSpinor hQ hkl he h₀ h₂₃ hu₀ x y η p,
    Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul,
    coe_halfSpinCliffordMul_apply_apply, coe_halfSpinCliffordMul_apply_apply,
    LinearEquiv.coe_ofEq_apply, ← hc₂, hc₀]
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
  rw [gaugeFixedFlatOperator_apply]
  exact Prod.ext
    (by simp [flatGaugeAdjoint_normalPerturbation hQ hkl he h₀ h₂₃ hρ hu₀ hu₀₁ x hy hη]) <|
    Prod.ext (by simp [linearizedFlatCurvature_normalPerturbation
      hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ x hy hη])
      (by simp [linearizedFlatDirac_normalPerturbation hQ hkl he h₀ h₂₃ hu₀ x hy hη])

end FrameHypotheses
end NormalIntertwining
end TauCeti.SeibergWitten
