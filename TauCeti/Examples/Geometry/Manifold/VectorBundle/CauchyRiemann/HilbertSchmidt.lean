/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.HilbertSchmidt
public import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Tactic

/-!
# Intrinsic zero-one pairing examples

These clients use original native tangent and trivial-bundle fibres with Mathlib's standard
Riemannian metric on the complex line. Conjugation is a zero-one form for the standard complex
structure, while a complex-linear form is zero-one for its negative. Their real geometric
Hilbert–Schmidt pairing has factor two, including nonzero coefficients.

A mixed real-linear principal term checks the cancellation of the native half-normalization.
An arbitrary native fibre checks orthogonality of the projected part and the residual. Source
dimension zero, target rank zero, a general empty base and the literal empty native manifold
are included without selecting a unit vector in a degenerate source.
-/

public section

open scoped InnerProductSpace Manifold ContDiff
open Bundle ContinuousLinearMap

noncomputable section

namespace TauCeti.SmoothAlmostComplexStructure.HilbertSchmidtExamples

section NativeBundleClients
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (j : SmoothAlmostComplexStructure I M) (x : M)

/-- The actual projected component is orthogonal to the actual residual in arbitrary fibres. -/
example (hJ : ∀ u v, ⟪j x u, j x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hI : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (A B : TangentSpace I x →L[ℝ] V x) :
    hilbertSchmidtInner (j.zeroOnePart A) (B - j.zeroOnePart B) = 0 := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ (j.zeroOnePart B),
    hilbertSchmidtInner_add_right, hilbertSchmidtInner_smul_right,
    (isZeroOneForm_zeroOnePart A).hilbertSchmidtInner_zeroOnePart_right hJ hI B]
  ring

omit [IsManifold I ∞ M] in
/-- Dimension two supplies a unit vector at the point; no unitary coordinate is assumed. -/
example (hDim : Module.finrank ℝ (TangentSpace I x) = 2) :
    ∃ v : TangentSpace I x, ‖v‖ = 1 := by
  let i : Fin (Module.finrank ℝ (TangentSpace I x)) := ⟨0, by rw [hDim]; decide⟩
  exact ⟨stdOrthonormalBasis ℝ (TangentSpace I x) i,
    (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal.norm_eq_one i⟩

/-- The native pairing formula remains well-formed on an arbitrary empty base. -/
example [IsEmpty M] (A B : ∀ y : M, TangentSpace I y →L[ℝ] V y) :
    ∀ y, hilbertSchmidtInner (j.zeroOnePart (A y)) (B y) =
      hilbertSchmidtInner (A y) (j.zeroOnePart (B y)) := by
  intro y
  exact isEmptyElim y

end NativeBundleClients

section ConcreteClients
open Bundle
private def standardComplexStructure := TauCeti.SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ
private def tangentToComplex :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℂ)).toContinuousLinearMap
private def antilinearForm (a : ℂ) : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ) →L[ℝ] Trivial ℂ ℂ 0 :=
  a • Complex.conjCLE.toContinuousLinearMap.comp tangentToComplex
private def linearForm (a : ℂ) :
    TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ) →L[ℝ] Trivial ℂ ℂ 0 := a • tangentToComplex

private theorem inner_I_smul_I_smul (u v : ℂ) :
    ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ := by
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]

private theorem inner_standardComplexStructure_apply_apply (u v : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) :
    ⟪standardComplexStructure 0 u, standardComplexStructure 0 v⟫_ℝ = ⟪u, v⟫_ℝ := by
  -- Mathlib's actual tangent Riemannian metric on a vector space is `innerSL` of that space.
  -- Its `fromTangentSpace` and the standard complex structure preserve the original vectors.
  dsimp only [standardComplexStructure, tangentToComplex]
  rw [TauCeti.SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  change ⟪Complex.I • (tangentToComplex u), Complex.I • (tangentToComplex v)⟫_ℝ =
    ⟪tangentToComplex u, tangentToComplex v⟫_ℝ
  exact inner_I_smul_I_smul _ _

private theorem antilinearForm_zero_one (a : ℂ) :
    standardComplexStructure.IsZeroOneForm (antilinearForm a) := by
  apply TauCeti.SmoothAlmostComplexStructure.isZeroOneForm_iff.mpr
  intro w
  dsimp only [antilinearForm, tangentToComplex, standardComplexStructure]
  rw [TauCeti.SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  change a * (starRingEnd ℂ) (Complex.I * tangentToComplex w) =
    -(Complex.I * (a * (starRingEnd ℂ) (tangentToComplex w)))
  rw [map_mul, Complex.conj_I]
  ring

private theorem linearForm_negative_zero_one (a : ℂ) :
    (-standardComplexStructure).IsZeroOneForm (linearForm a) := by
  apply TauCeti.SmoothAlmostComplexStructure.isZeroOneForm_iff.mpr
  intro w
  dsimp only [linearForm]
  rw [TauCeti.SmoothAlmostComplexStructure.neg_toEndomorphism]
  simp only [ContMDiffSection.coe_neg, Pi.neg_apply, _root_.neg_apply]
  rw [map_neg]
  dsimp only [standardComplexStructure, tangentToComplex]
  rw [TauCeti.SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  change -(a * (Complex.I * tangentToComplex w)) = -(Complex.I * (a * tangentToComplex w))
  ring

private def unitTangent := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℂ)).symm (1 : ℂ)

private theorem norm_unitTangent : ‖unitTangent‖ = 1 := by
  rw [norm_tangentSpace_vectorSpace]
  simp [unitTangent]

private theorem finrank_tangent_complex :
    Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) = 2 := by
  change Module.finrank ℝ ℂ = 2
  exact Complex.finrank_real_complex

private theorem std_factor_two (a b : ℂ) :
    hilbertSchmidtInner (antilinearForm a) (antilinearForm b) = 2 * ⟪a, b⟫_ℝ := by
  have h := (antilinearForm_zero_one a).hilbertSchmidtInner_eq_two_mul_inner_apply
    (antilinearForm_zero_one b)
    inner_standardComplexStructure_apply_apply inner_I_smul_I_smul
      finrank_tangent_complex unitTangent norm_unitTangent
  simpa [antilinearForm, tangentToComplex, unitTangent] using h

private theorem nonzero_standard_and_negative_clients (a : ℂ) (ha : a ≠ 0) :
    standardComplexStructure.zeroOnePart (antilinearForm a) = antilinearForm a ∧
    (-standardComplexStructure).zeroOnePart (linearForm a) = linearForm a ∧
    hilbertSchmidtInner (antilinearForm a) (antilinearForm a) = 2 * ‖a‖ ^ 2 ∧
    hilbertSchmidtInner (antilinearForm a) (antilinearForm a) ≠ 0 := by
  have hpos : 0 < 2 * ‖a‖ ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr ha))
  refine ⟨(antilinearForm_zero_one a).zeroOnePart_eq,
    (linearForm_negative_zero_one a).zeroOnePart_eq,
    ?_, ?_⟩
  · rw [std_factor_two, real_inner_self_eq_norm_sq]
  · rw [std_factor_two, real_inner_self_eq_norm_sq]
    exact ne_of_gt hpos

private theorem linearForm_project_std (a : ℂ) :
    standardComplexStructure.zeroOnePart (linearForm a) = 0 := by
  ext w
  rw [TauCeti.SmoothAlmostComplexStructure.zeroOnePart_apply]
  dsimp only [linearForm, tangentToComplex, standardComplexStructure]
  rw [TauCeti.SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  change (2⁻¹ : ℝ) •
    (a * tangentToComplex w + Complex.I * (a * (Complex.I * tangentToComplex w))) = 0
  have h : a * tangentToComplex w + Complex.I * (a * (Complex.I * tangentToComplex w)) = 0 := by
    calc _ = (a * tangentToComplex w) * (1 + Complex.I ^ 2) := by ring
         _ = 0 := by simp
  rw [h, smul_zero]

private theorem mixed_projection_pairing (a b c : ℂ) :
    hilbertSchmidtInner (antilinearForm a)
      (standardComplexStructure.zeroOnePart (linearForm b + antilinearForm c)) =
      2 * ⟪a, c⟫_ℝ := by
  rw [TauCeti.SmoothAlmostComplexStructure.zeroOnePart_add, linearForm_project_std,
    (antilinearForm_zero_one c).zeroOnePart_eq, zero_add, std_factor_two]

private theorem negative_factor_two (a b : ℂ) :
    hilbertSchmidtInner (linearForm a) (linearForm b) = 2 * ⟪a, b⟫_ℝ := by
  have hJ (u v : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) :
      ⟪(-standardComplexStructure) 0 u, (-standardComplexStructure) 0 v⟫_ℝ = ⟪u, v⟫_ℝ := by
    simpa only [TauCeti.SmoothAlmostComplexStructure.neg_apply, inner_neg_neg] using
      inner_standardComplexStructure_apply_apply u v
  have h := (linearForm_negative_zero_one a).hilbertSchmidtInner_eq_two_mul_inner_apply
    (linearForm_negative_zero_one b) hJ inner_I_smul_I_smul
      finrank_tangent_complex unitTangent norm_unitTangent
  simpa [linearForm, tangentToComplex, unitTangent] using h

private theorem mixed_principal_pairing (a b c : ℂ) :
    hilbertSchmidtInner (antilinearForm a)
      (standardComplexStructure.zeroOnePart (linearForm b + antilinearForm c)) =
      ⟪a, (2 : ℝ) • c⟫_ℝ := by
  have h := (antilinearForm_zero_one a).hilbertSchmidtInner_zeroOnePart_eq_inner_apply
    inner_standardComplexStructure_apply_apply inner_I_smul_I_smul
      finrank_tangent_complex unitTangent norm_unitTangent
      (linearForm b + antilinearForm c)
  rw [h]
  let u := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℂ)).symm (1 : ℂ)
  have hu : tangentToComplex u = 1 :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℂ)).apply_symm_apply 1
  dsimp only [antilinearForm, linearForm, tangentToComplex, standardComplexStructure]
  rw [TauCeti.SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  change ⟪a * (starRingEnd ℂ) (tangentToComplex u),
    b * tangentToComplex u + c * (starRingEnd ℂ) (tangentToComplex u) +
      Complex.I * (b * (Complex.I * tangentToComplex u) +
        c * (starRingEnd ℂ) (Complex.I * tangentToComplex u))⟫_ℝ = ⟪a, (2 : ℝ) • c⟫_ℝ
  rw [hu]
  simp only [map_one, mul_one, Complex.conj_I]
  congr 1
  change b + c + Complex.I * (b * Complex.I + c * -Complex.I) = 2 * c
  calc _ = 2 * c + b * (1 + Complex.I ^ 2) - c * (1 + Complex.I ^ 2) := by ring
       _ = 2 * c := by simp

private abbrev ZR := EuclideanSpace ℝ (Fin 0)
private def jZero : TauCeti.SmoothAlmostComplexStructure 𝓘(ℝ, ZR) ZR :=
  TauCeti.SmoothAlmostComplexStructure.const 0 (fun _ ↦ Subsingleton.elim _ _)

private theorem source_zero_client (A : TangentSpace 𝓘(ℝ, ZR) (0 : ZR) →L[ℝ] Trivial ZR ℂ 0) :
    hilbertSchmidtInner (jZero.zeroOnePart A) A =
      hilbertSchmidtInner A (jZero.zeroOnePart A) ∧
    jZero.zeroOnePart A = 0 ∧ hilbertSchmidtInner A A = 0 ∧
      Module.finrank ℝ (TangentSpace 𝓘(ℝ, ZR) (0 : ZR)) = 0 := by
  refine ⟨jZero.hilbertSchmidtInner_zeroOnePart_left_eq_right 0 ?_
    inner_I_smul_I_smul A A, ?_⟩
  · intro u v
    have hz (w : TangentSpace 𝓘(ℝ, ZR) (0 : ZR)) : w = 0 := by
      apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ZR)).injective
      exact Subsingleton.elim _ _
    rw [hz u, hz v, hz (jZero 0 0)]
  have hA : A = 0 := by
    ext v
    have hv : v = 0 := by
      apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ZR)).injective
      exact Subsingleton.elim _ _
    rw [hv, map_zero, zero_apply]
  rw [hA]
  refine ⟨by simp, by simp, ?_⟩
  change Module.finrank ℝ ZR = 0
  simp [ZR]

private abbrev ZC := EuclideanSpace ℂ (Fin 0)
/-- The zero-dimensional complex target carries its inherited real metric. -/
local instance zeroTargetMetric : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 0)) :=
  InnerProductSpace.complexToReal

private theorem target_zero_client (A : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ) →L[ℝ] Trivial ℂ ZC 0) :
    hilbertSchmidtInner (standardComplexStructure.zeroOnePart A) A =
      hilbertSchmidtInner A (standardComplexStructure.zeroOnePart A) ∧
    standardComplexStructure.zeroOnePart A = 0 ∧ hilbertSchmidtInner A A = 0 ∧
      Module.finrank ℂ ZC = 0 := by
  refine ⟨standardComplexStructure.hilbertSchmidtInner_zeroOnePart_left_eq_right 0
    inner_standardComplexStructure_apply_apply (fun u v ↦ ?_) A A, ?_⟩
  · rw [Subsingleton.elim u 0, Subsingleton.elim v 0, smul_zero, inner_zero_left]
  have hA : A = 0 := ContinuousLinearMap.ext fun _ ↦ Subsingleton.elim _ _
  rw [hA]
  exact ⟨by simp, by simp, by simp [ZC]⟩

/-- The literal empty native manifold has the canonical empty complex atlas. -/
local instance emptyCharted : ChartedSpace ℂ Empty := ChartedSpace.empty _ _
/-- The tangent metric on the empty manifold has no fibre values to choose. -/
local instance emptyMetric :
    RiemannianBundle (fun y : Empty ↦ TangentSpace 𝓘(ℝ, ℂ) y) where
  g := {
    inner := fun y ↦ Empty.elim y
    symm := fun y ↦ Empty.elim y
    pos := fun y ↦ Empty.elim y
    continuousAt := fun y ↦ Empty.elim y
    isVonNBounded := fun y ↦ Empty.elim y
  }

private theorem literal_empty_client
    (A B : ∀ y : Empty, TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] Trivial Empty ℂ y) :
    ∀ y,
      hilbertSchmidtInner
        ((TauCeti.SmoothAlmostComplexStructure.ofComplexManifold ℂ Empty).zeroOnePart (A y)) (B y) =
      hilbertSchmidtInner (A y)
        ((TauCeti.SmoothAlmostComplexStructure.ofComplexManifold ℂ Empty).zeroOnePart (B y)) := by
  intro y
  exact Empty.elim y

end ConcreteClients

end TauCeti.SmoothAlmostComplexStructure.HilbertSchmidtExamples
