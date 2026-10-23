/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.ModelTransport
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
import TauCeti.Geometry.Manifold.Diffeomorph.Tangent

/-!
# Adapted pseudo-gradients under boundaryless model transport

The native adapted-pseudo-gradient theory is stated for manifolds whose charts take values in
their model vector space. This file transfers vector fields on an arbitrary boundaryless model to
the canonical self-modelled copy `BoundarylessModel I M`. The pushforward and pullback fields are
inverse, smoothness is preserved, and evaluation by the differential of a real function is
unchanged.

This gives `BoundarylessModel.IsAdaptedPseudoGradient`, the intrinsic version of the native
predicate for an arbitrary boundaryless model. Its defining comparison is exposed without
installing a second atlas on `M`. In particular, a Morse function on a compact arbitrary-model
manifold has an adapted pseudo-gradient field.

## Main declarations

* `TauCeti.BoundarylessModel.transportVectorField`: push a vector field to the self-modelled copy.
* `TauCeti.BoundarylessModel.contMDiff_transportVectorField_iff`: smoothness is invariant under
  transport.
* `TauCeti.BoundarylessModel.mvfderiv_transportVectorField`: transport preserves differential
  evaluation.
* `TauCeti.BoundarylessModel.IsAdaptedPseudoGradient`: adapted pseudo-gradients on an arbitrary
  boundaryless model.
* `TauCeti.BoundarylessModel.IsMorse.exists_isAdaptedPseudoGradient`: existence on compact
  arbitrary-model manifolds.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti
namespace BoundarylessModel

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- Push a vector field on an arbitrary boundaryless model forward to its canonical self-modelled
copy. This is the differential of the identity diffeomorphism applied fiberwise. -/
noncomputable def transportVectorField (X : (x : M) → TangentSpace I x) :
    (x : BoundarylessModel I M) → TangentSpace 𝓘(ℝ, E) x :=
  fun x ↦ mfderiv I 𝓘(ℝ, E) (diffeomorph I (M := M) ∞)
    ((homeomorph I M).symm x) (X ((homeomorph I M).symm x))

/-- The transported vector field at the image of `x` is the differential of the model-change
diffeomorphism applied to the original field at `x`. -/
theorem transportVectorField_apply (X : (x : M) → TangentSpace I x) (x : M) :
    transportVectorField I X (homeomorph I M x) =
      mfderiv I 𝓘(ℝ, E) (diffeomorph I (M := M) ∞) x (X x) := by
  rw [transportVectorField, Homeomorph.symm_apply_apply]

/-- The transported field is the original field read through the two tangent-space
identifications with the common model vector space. -/
theorem transportVectorField_eq_cast (X : (x : M) → TangentSpace I x) (x : M) :
    transportVectorField I X (homeomorph I M x) =
      (tangentSpaceCastModel 𝓘(ℝ, E) (homeomorph I M x)).symm
        (tangentSpaceCastModel I x (X x)) := by
  rw [transportVectorField, Homeomorph.symm_apply_apply, coe_diffeomorph]
  have h := mfderiv_target (I := I) I (id : M → M) x
  have h' := congrArg (fun L ↦ L (X x)) h
  simpa only [Function.comp_id, id_eq, Homeomorph.apply_symm_apply, mfderiv_id,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe] using h'

variable [IsManifold I ∞ M]

/-- A vector field is smooth precisely when its pushforward to the self-modelled copy is smooth. -/
theorem contMDiff_transportVectorField_iff (X : (x : M) → TangentSpace I x) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun x ↦ (⟨x, transportVectorField I X x⟩ :
          TangentBundle 𝓘(ℝ, E) (BoundarylessModel I M))) ↔
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) := by
  set h := diffeomorph I (M := M) ∞ with hh
  have heq : (fun x ↦ (⟨x, transportVectorField I X x⟩ :
      TangentBundle 𝓘(ℝ, E) (BoundarylessModel I M))) =
      (h.tangent ∘ fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) ∘ h.symm := by
    funext x
    ext
    · simp only [Function.comp_apply]
      rw [Diffeomorph.coe_tangent, tangentMap_proj, h.apply_symm_apply]
    · simp only [Function.comp_apply]
      rw [Diffeomorph.coe_tangent, tangentMap_snd, transportVectorField, ← hh,
        coe_diffeomorph_symm]
      exact HEq.rfl
  rw [heq]
  rw [h.symm.contMDiff_comp_diffeomorph_iff (by simp)]
  rw [h.tangent.contMDiff_diffeomorph_comp_iff (by simp)]

omit [IsManifold I ∞ M] in
/-- Evaluation of a function's differential on a vector field is unchanged by boundaryless model
transport. -/
theorem mvfderiv_transportVectorField (f : M → ℝ)
    (X : (x : M) → TangentSpace I x) (x : M) :
    mvfderiv 𝓘(ℝ, E) (f ∘ (homeomorph I M).symm) (homeomorph I M x)
        (transportVectorField I X (homeomorph I M x)) = mvfderiv I f x (X x) := by
  rw [mvfderiv, mfderiv_source, transportVectorField_eq_cast]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [Homeomorph.symm_apply_apply]
  rfl

omit [IsManifold I ∞ M] in
/-- Transporting the pullback of a field recovers the field on the self-modelled copy. -/
@[simp]
theorem transportVectorField_mpullback
    (Y : (x : BoundarylessModel I M) → TangentSpace 𝓘(ℝ, E) x) :
    transportVectorField I
        (VectorField.mpullback I 𝓘(ℝ, E) (homeomorph I M) Y) = Y := by
  funext x
  obtain ⟨y, rfl⟩ := (homeomorph I M).surjective x
  rw [transportVectorField_apply]
  rw [← coe_diffeomorph I (M := M) ∞]
  exact (diffeomorph I (M := M) ∞).mfderiv_apply_mpullback (by simp) Y y

omit [IsManifold I ∞ M] in
/-- Pulling back a transported field recovers the field on the original model. -/
@[simp]
theorem mpullback_transportVectorField (X : (x : M) → TangentSpace I x) :
    VectorField.mpullback I 𝓘(ℝ, E) (homeomorph I M)
        (transportVectorField I X) = X := by
  funext x
  rw [VectorField.mpullback, transportVectorField_apply]
  rw [← coe_diffeomorph I (M := M) ∞]
  exact ((diffeomorph I (M := M) ∞).isInvertible_mfderiv (by simp)).inverse_apply_self (X x)

/-- An adapted pseudo-gradient on an arbitrary boundaryless model is a vector field whose
pushforward to the canonical self-modelled copy is adapted to the transported function. -/
def IsAdaptedPseudoGradient (f : M → ℝ) (X : (x : M) → TangentSpace I x) : Prop :=
  TauCeti.IsAdaptedPseudoGradient (f ∘ (homeomorph I M).symm) (transportVectorField I X)

/-- The arbitrary-model adapted-pseudo-gradient predicate is exactly the native predicate after
the canonical model transport. -/
@[simp]
theorem isAdaptedPseudoGradient_iff (f : M → ℝ)
    (X : (x : M) → TangentSpace I x) :
    IsAdaptedPseudoGradient I f X ↔
      TauCeti.IsAdaptedPseudoGradient (f ∘ (homeomorph I M).symm)
        (transportVectorField I X) :=
  Iff.rfl

omit [IsManifold I ∞ M] in
/-- The transported field vanishes exactly when the original field vanishes. -/
theorem transportVectorField_eq_zero_iff (X : (x : M) → TangentSpace I x) (x : M) :
    transportVectorField I X (homeomorph I M x) = 0 ↔ X x = 0 := by
  rw [transportVectorField_eq_cast]
  simp

namespace IsAdaptedPseudoGradient

/-- An adapted pseudo-gradient on an arbitrary model is a smooth vector field. -/
theorem contMDiff {f : M → ℝ} {X : (x : M) → TangentSpace I x}
    (hX : IsAdaptedPseudoGradient I f X) :
    ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) := by
  have hnative := (isAdaptedPseudoGradient_iff I f X).mp hX
  exact (contMDiff_transportVectorField_iff I X).mp hnative.contMDiff

/-- Away from critical points, an adapted pseudo-gradient strictly decreases the function. -/
theorem mvfderiv_apply_lt_zero {f : M → ℝ} {X : (x : M) → TangentSpace I x}
    (hX : IsAdaptedPseudoGradient I f X) (x : M) (hx : mfderiv I 𝓘(ℝ) f x ≠ 0) :
    mvfderiv I f x (X x) < 0 := by
  have hnative := (isAdaptedPseudoGradient_iff I f X).mp hX
  rw [← mvfderiv_transportVectorField I f X x]
  have hx' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ (homeomorph I M).symm)
      (homeomorph I M x) ≠ 0 := by
    apply (mfderiv_source_eq_zero_iff I 𝓘(ℝ) f (homeomorph I M x)).not.mpr
    have hpoint := (homeomorph I M).symm_apply_apply x
    rw [hpoint]
    exact hx
  exact hnative.mvfderiv_apply_lt_zero (homeomorph I M x)
    hx'

/-- At a critical point, the transported field has the native linear normal form in a Morse
chart of the self-modelled copy. -/
theorem exists_morseChart {f : M → ℝ} {X : (x : M) → TangentSpace I x}
    (hX : IsAdaptedPseudoGradient I f X) (x : M) (hx : mfderiv I 𝓘(ℝ) f x = 0) :
    ∃ φ : MorseChart E (f ∘ (homeomorph I M).symm) (homeomorph I M x),
      ∀ y ∈ φ.toChart.source,
        φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y
          (transportVectorField I X y)) =
          fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i) := by
  have hnative := (isAdaptedPseudoGradient_iff I f X).mp hX
  apply hnative.exists_morseChart (homeomorph I M x)
  apply (mfderiv_source_eq_zero_iff I 𝓘(ℝ) f (homeomorph I M x)).mpr
  have hpoint := (homeomorph I M).symm_apply_apply x
  rw [hpoint]
  exact hx

/-- An adapted pseudo-gradient does not increase the function. -/
theorem mvfderiv_apply_nonpos {f : M → ℝ} {X : (x : M) → TangentSpace I x}
    (hX : IsAdaptedPseudoGradient I f X) (x : M) : mvfderiv I f x (X x) ≤ 0 := by
  rw [← mvfderiv_transportVectorField I f X x]
  exact ((isAdaptedPseudoGradient_iff I f X).mp hX).mvfderiv_apply_nonpos
    (homeomorph I M x)

/-- The zeros of an arbitrary-model adapted pseudo-gradient are exactly the critical points. -/
theorem eq_zero_iff {f : M → ℝ} {X : (x : M) → TangentSpace I x}
    (hX : IsAdaptedPseudoGradient I f X) (x : M) :
    X x = 0 ↔ mfderiv I 𝓘(ℝ) f x = 0 := by
  rw [← transportVectorField_eq_zero_iff I X x]
  rw [((isAdaptedPseudoGradient_iff I f X).mp hX).eq_zero_iff]
  rw [mfderiv_source_eq_zero_iff]
  have hpoint := (homeomorph I M).symm_apply_apply x
  rw [hpoint]

end IsAdaptedPseudoGradient

namespace IsMorse

/-- Every Morse function on a compact arbitrary-model manifold has an adapted pseudo-gradient. -/
theorem exists_isAdaptedPseudoGradient [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
    {f : M → ℝ} (hf : TauCeti.IsMorse I f) :
    ∃ X : (x : M) → TangentSpace I x, IsAdaptedPseudoGradient I f X := by
  let _ : CompactSpace (BoundarylessModel I M) := (homeomorph I M).compactSpace
  let _ : T2Space (BoundarylessModel I M) := (homeomorph I M).t2Space
  have hf' : TauCeti.IsMorse 𝓘(ℝ, E) (f ∘ (homeomorph I M).symm) :=
    (isMorse_iff I f).mpr hf
  obtain ⟨Y, hY⟩ := hf'.exists_isAdaptedPseudoGradient
  refine ⟨VectorField.mpullback I 𝓘(ℝ, E) (homeomorph I M) Y, ?_⟩
  rw [isAdaptedPseudoGradient_iff, transportVectorField_mpullback]
  exact hY

end IsMorse

end BoundarylessModel
end TauCeti
