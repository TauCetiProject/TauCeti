/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Torus.CauchyRiemannOperator
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial.Basic

/-!
# Conjugate coefficients on the plane, bordered disc, and torus

The coefficient `conj σ • η` gives a real Cauchy–Riemann operator on the native trivial line
bundle whenever `η` is a `(0,1)`-form. These examples specialize all four decomposition laws to
the plane, open planar domains, the closed disc with its bordered Cayley atlas, and the square
torus. The closed-disc coefficient is expressed in the preferred tangent model; its fibrewise
properties require no assertion that this choice of covectors is a smooth section. The torus
coefficient is its native `dzbar`.
-/

public section

open Bundle Complex ComplexConjugate TauCeti TauCeti.SmoothAlmostComplexStructure
open scoped ContDiff Manifold TauCeti.ComplexManifold Complex.UnitDisc

noncomputable section
namespace TauCeti.Examples.ConjugateCoefficient

private def modelDzbar {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ ℂ H}
    [TopologicalSpace M] [ChartedSpace H M] (x : M) : TangentSpace I x →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap

private theorem modelDzbar_apply {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ ℂ H} [TopologicalSpace M] [ChartedSpace H M] (x : M) (v : ℂ) :
    modelDzbar (I := I) x v = conj v := Complex.conjCLE_apply v

private theorem modelDzbar_ne_zero {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ ℂ H} [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    modelDzbar (I := I) x ≠ 0 := by
  intro h
  have h₁ := congrArg (fun L : TangentSpace I x →L[ℝ] ℂ ↦ L (1 : ℂ)) h
  have h₀ : (0 : TangentSpace I x →L[ℝ] ℂ) (1 : ℂ) = 0 := zero_apply _
  exact one_ne_zero (by simpa only [map_one] using
    (modelDzbar_apply x 1).symm.trans (h₁.trans h₀))

private theorem modelDzbar_zeroOne {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (𝓘(ℂ)) ∞ M] (x : M) :
    (ofComplexManifold ℂ M).IsZeroOneForm (V := Trivial M ℂ) (modelDzbar x) := by
  refine isZeroOneForm_iff.2 fun (v : ℂ) ↦ ?_
  rw [ofComplexManifold_apply, modelDzbar_apply, modelDzbar_apply, smul_eq_mul, map_mul,
    Complex.conj_I, smul_eq_mul, neg_mul]

private theorem disc_modelDzbar_zeroOne (x : 𝕔𝔻) :
    (ofBorderedHolomorphic 𝕔𝔻).IsZeroOneForm (V := Trivial 𝕔𝔻 ℂ)
      (modelDzbar (I := closedUpperHalfPlaneModel) x) := by
  refine isZeroOneForm_iff.2 fun (v : ℂ) ↦ ?_
  rw [ofBorderedHolomorphic_apply, modelDzbar_apply, modelDzbar_apply, smul_eq_mul, map_mul,
    Complex.conj_I, smul_eq_mul, neg_mul]

private theorem torus_dzbar_zeroOne (x : UnitAddCircle × UnitAddCircle) :
    (addCircleProd 1 1).IsZeroOneForm (V := Trivial _ ℂ) (TauCeti.UnitAddTorus.dzbar x) := by
  simpa only [one_smul] using TauCeti.UnitAddTorus.isZeroOneForm_smul_dzbar x 1

section Plane

/-- The conjugate-coefficient operator on the plane `ℂ`. -/
def operatorPlane (σ : ℂ → ℂ) (x : ℂ) : TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] ℂ :=
  (ofComplexManifold ℂ ℂ).dbarFunction σ x + conj (σ x) • (modelDzbar (I := 𝓘(ℝ, ℂ))) x

example : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ ℂ) (V := Trivial (ℂ) ℂ)
    operatorPlane :=
  (ofComplexManifold ℂ ℂ).isRealCauchyRiemannOperator_dbarFunction_add_conjSMulForm
    (modelDzbar (I := 𝓘(ℝ, ℂ)))
    modelDzbar_zeroOne

example (σ : ℂ → ℂ) (x : ℂ) :
    sectionComplexLinearPart (V := Trivial (ℂ) ℂ) operatorPlane σ x
    = (ofComplexManifold ℂ ℂ).dbarFunction σ x :=
  (ofComplexManifold ℂ ℂ).sectionComplexLinearPart_dbarFunction_add_conjSMulForm
    (modelDzbar (I := 𝓘(ℝ, ℂ))) σ x

example (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ ℂ) (V := Trivial (ℂ) ℂ)
    operatorPlane)
    (x : ℂ) : hD.antilinearPart x = conjSMulForm (modelDzbar (I := 𝓘(ℝ, ℂ))) x :=
  (ofComplexManifold ℂ ℂ).antilinearPart_dbarFunction_add_conjSMulForm
    (modelDzbar (I := 𝓘(ℝ, ℂ))) hD x

example : ¬IsComplexLinearOperator ℂ (V := Trivial (ℂ) ℂ) operatorPlane := by
  intro hD
  have h := ((ofComplexManifold ℂ ℂ).isComplexLinearOperator_dbarFunction_add_conjSMulForm_iff
    (modelDzbar (I := 𝓘(ℝ, ℂ)))).1 hD
  exact modelDzbar_ne_zero (0 : ℂ) (h _)

end Plane

section OpenDomain

variable {U : TopologicalSpace.Opens ℂ}

/-- The conjugate-coefficient operator on an open subset `U` of `ℂ`. -/
def operatorOpenDomain (σ : U → ℂ) (x : U) : TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] ℂ :=
  (ofComplexManifold ℂ U).dbarFunction σ x + conj (σ x) • (modelDzbar (I := 𝓘(ℝ, ℂ))) x

example : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ U) (V := Trivial (U) ℂ)
    operatorOpenDomain :=
  (ofComplexManifold ℂ U).isRealCauchyRiemannOperator_dbarFunction_add_conjSMulForm
    (modelDzbar (I := 𝓘(ℝ, ℂ)))
    modelDzbar_zeroOne

example (σ : U → ℂ) (x : U) :
    sectionComplexLinearPart (V := Trivial (U) ℂ) operatorOpenDomain σ x
    = (ofComplexManifold ℂ U).dbarFunction σ x :=
  (ofComplexManifold ℂ U).sectionComplexLinearPart_dbarFunction_add_conjSMulForm
    (modelDzbar (I := 𝓘(ℝ, ℂ))) σ x

example (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ U) (V := Trivial (U) ℂ)
    operatorOpenDomain)
    (x : U) : hD.antilinearPart x = conjSMulForm (modelDzbar (I := 𝓘(ℝ, ℂ))) x :=
  (ofComplexManifold ℂ U).antilinearPart_dbarFunction_add_conjSMulForm
    (modelDzbar (I := 𝓘(ℝ, ℂ))) hD x

example [Nonempty U] : ¬IsComplexLinearOperator ℂ (V := Trivial (U) ℂ) operatorOpenDomain := by
  intro hD
  have h := ((ofComplexManifold ℂ U).isComplexLinearOperator_dbarFunction_add_conjSMulForm_iff
    (modelDzbar (I := 𝓘(ℝ, ℂ)))).1 hD
  exact modelDzbar_ne_zero (Classical.choice inferInstance) (h _)

end OpenDomain

section ClosedDisc

/-- The conjugate-coefficient operator on the closed unit disc with its bordered atlas. -/
def operatorClosedDisc (σ : 𝕔𝔻 → ℂ) (x : 𝕔𝔻) : TangentSpace (closedUpperHalfPlaneModel) x →L[ℝ] ℂ :=
  (ofBorderedHolomorphic 𝕔𝔻).dbarFunction σ x +
    conj (σ x) • modelDzbar (I := closedUpperHalfPlaneModel) x

example : IsRealCauchyRiemannOperator ℂ (ofBorderedHolomorphic 𝕔𝔻) (V := Trivial (𝕔𝔻) ℂ)
    operatorClosedDisc :=
  (ofBorderedHolomorphic 𝕔𝔻).isRealCauchyRiemannOperator_dbarFunction_add_conjSMulForm
    (modelDzbar (I := closedUpperHalfPlaneModel))
    disc_modelDzbar_zeroOne

example (σ : 𝕔𝔻 → ℂ) (x : 𝕔𝔻) :
    sectionComplexLinearPart (V := Trivial (𝕔𝔻) ℂ) operatorClosedDisc σ x
    = (ofBorderedHolomorphic 𝕔𝔻).dbarFunction σ x :=
  (ofBorderedHolomorphic 𝕔𝔻).sectionComplexLinearPart_dbarFunction_add_conjSMulForm
    (modelDzbar (I := closedUpperHalfPlaneModel)) σ x

example (hD : IsRealCauchyRiemannOperator ℂ (ofBorderedHolomorphic 𝕔𝔻)
    (V := Trivial (𝕔𝔻) ℂ) operatorClosedDisc)
    (x : 𝕔𝔻) : hD.antilinearPart x = conjSMulForm (modelDzbar (I := closedUpperHalfPlaneModel)) x :=
  (ofBorderedHolomorphic 𝕔𝔻).antilinearPart_dbarFunction_add_conjSMulForm
    (modelDzbar (I := closedUpperHalfPlaneModel)) hD x

example : ¬IsComplexLinearOperator ℂ (V := Trivial (𝕔𝔻) ℂ) operatorClosedDisc := by
  intro hD
  have h := ((ofBorderedHolomorphic 𝕔𝔻).isComplexLinearOperator_dbarFunction_add_conjSMulForm_iff
    (modelDzbar (I := closedUpperHalfPlaneModel))).1 hD
  exact modelDzbar_ne_zero (0 : 𝕔𝔻) (h _)

end ClosedDisc

section Torus

/-- The conjugate-coefficient operator on the square torus. -/
def operatorTorus (σ : UnitAddCircle × UnitAddCircle → ℂ) (x : UnitAddCircle × UnitAddCircle) :
    TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x →L[ℝ] ℂ :=
  (addCircleProd 1 1).dbarFunction σ x + conj (σ x) • (TauCeti.UnitAddTorus.dzbar) x

example : IsRealCauchyRiemannOperator ℂ (addCircleProd 1 1)
    (V := Trivial (UnitAddCircle × UnitAddCircle) ℂ) operatorTorus :=
  (addCircleProd 1 1).isRealCauchyRiemannOperator_dbarFunction_add_conjSMulForm
    TauCeti.UnitAddTorus.dzbar
    torus_dzbar_zeroOne

example (σ : UnitAddCircle × UnitAddCircle → ℂ) (x : UnitAddCircle × UnitAddCircle) :
    sectionComplexLinearPart (V := Trivial (UnitAddCircle × UnitAddCircle) ℂ)
    operatorTorus σ x = (addCircleProd 1 1).dbarFunction σ x :=
  (addCircleProd 1 1).sectionComplexLinearPart_dbarFunction_add_conjSMulForm
    TauCeti.UnitAddTorus.dzbar σ x

example (hD : IsRealCauchyRiemannOperator ℂ (addCircleProd 1 1)
    (V := Trivial (UnitAddCircle × UnitAddCircle) ℂ) operatorTorus)
    (x : UnitAddCircle × UnitAddCircle) : hD.antilinearPart x =
      conjSMulForm TauCeti.UnitAddTorus.dzbar x :=
  (addCircleProd 1 1).antilinearPart_dbarFunction_add_conjSMulForm
    TauCeti.UnitAddTorus.dzbar hD x

example : ¬IsComplexLinearOperator ℂ (V := Trivial (UnitAddCircle × UnitAddCircle) ℂ)
    operatorTorus := by
  intro hD
  have h := ((addCircleProd 1 1).isComplexLinearOperator_dbarFunction_add_conjSMulForm_iff
    (TauCeti.UnitAddTorus.dzbar)).1 hD
  exact TauCeti.UnitAddTorus.dzbar_ne_zero (0, 0) (h _)

end Torus

/-- The preferred-coordinate coefficient is defined at a boundary point of the bordered disc. -/
example : conjSMulForm (modelDzbar (I := closedUpperHalfPlaneModel))
    (1 : 𝕔𝔻) Complex.I (1 : ℂ) = -Complex.I := by
  calc
    _ = conj Complex.I • modelDzbar (I := closedUpperHalfPlaneModel) (1 : 𝕔𝔻) (1 : ℂ) :=
      (congrArg (fun L : TangentSpace closedUpperHalfPlaneModel (1 : 𝕔𝔻) →L[ℝ] ℂ ↦ L (1 : ℂ))
        (conjSMulForm_apply (modelDzbar (I := closedUpperHalfPlaneModel)) 1 Complex.I)).trans
          (smul_apply _ _ _)
    _ = -Complex.I := by rw [modelDzbar_apply, map_one, Complex.conj_I, smul_eq_mul, mul_one]

section DegenerateAndScalar

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (j : SmoothAlmostComplexStructure I M)

example [IsEmpty M] (η : Π x : M, TangentSpace I x →L[ℝ] ℂ) :
    IsComplexLinearOperator ℂ (V := Trivial M ℂ)
      (fun σ x ↦ j.dbarFunction σ x + conj (σ x) • η x) :=
  (j.isComplexLinearOperator_dbarFunction_add_conjSMulForm_iff η).2 (fun x ↦ isEmptyElim x)

example (σ : M → (Fin 0 → ℂ)) (x : M) : j.dbarFunction σ x = 0 := Subsingleton.elim _ _

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (σ : M → F) (x : M) (c : ℝ) :
    j.dbarFunction (c • σ) x = c • j.dbarFunction σ x := j.dbarFunction_const_smul c σ x

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (σ : M → F) (x : M) (c : ℂ) :
    j.delFunction (c • σ) x = c • j.delFunction σ x := j.delFunction_const_smul c σ x

example [Nontrivial E] [Nonempty M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Nontrivial F] : ¬IsRealCauchyRiemannOperator F j (V := Trivial M F) j.delFunction :=
  j.not_isRealCauchyRiemannOperator_delFunction

example [FiniteDimensional ℝ E] [T2Space M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] : ContMDiffCovariantDerivativeOn F 0 (V := Trivial M F)
      j.dbarFunction Set.univ := j.contMDiffCovariantDerivativeOn_dbarFunction (by simp)

example [FiniteDimensional ℝ E] [T2Space M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] : ContMDiffCovariantDerivativeOn F 1 (V := Trivial M F)
      j.dbarFunction Set.univ := j.contMDiffCovariantDerivativeOn_dbarFunction (by simp)

example [FiniteDimensional ℝ E] [T2Space M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] : ContMDiffCovariantDerivativeOn F ∞ (V := Trivial M F)
      j.dbarFunction Set.univ := j.contMDiffCovariantDerivativeOn_dbarFunction (by simp)

end DegenerateAndScalar
end TauCeti.Examples.ConjugateCoefficient
