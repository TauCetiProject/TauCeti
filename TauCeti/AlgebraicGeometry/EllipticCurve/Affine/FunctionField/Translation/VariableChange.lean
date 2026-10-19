/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint

/-!
# Changes of variables carry translations to translations

Let `W` be an elliptic curve over a field `F` and `C` a change of variables, and write
`ψ : F(C • W) → F(W)` for the function-field pullback of the isomorphism `W → C • W`. The
isomorphism is a homomorphism of point groups (`WeierstrassCurve.pointEquivVariableChange`), so it
intertwines the translations: `τ_P^* ∘ ψ = ψ ∘ τ_{P'}^*`, where `P'` is the point of `C • W`
corresponding to `P`. Both sides are determined by where they send the generic point of `C • W`,
and this is computed with tautological points
(`TauCeti.Isogeny.tautologicalPoint_variableChangePullback`).

## Main results

* `WeierstrassCurve.Affine.translation_comp_fieldPullback_variableChangeIsogeny`: a change of
  variables carries the translation by `P` to the translation by the corresponding point.
* `WeierstrassCurve.Affine.exists_translation_comp_fieldPullback_variableChangeIsogeny`: the same,
  for any change of variables `C • W₁ = W₂`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3.
-/

public section

open TauCeti TauCeti.Isogeny WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F]

section Conjugation

variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] [DecidableEq F]

/-- **Translations are carried to translations by a change of variables.** For a change of
variables `C`, write `ψ : F(C • W) → F(W)` for the pullback of the isomorphism `W → C • W`. Then
`τ_P^* ∘ ψ = ψ ∘ τ_{P'}^*`, where `P'` is the point of `C • W` corresponding to `P`: the
isomorphism is a homomorphism of point groups. -/
theorem translation_comp_fieldPullback_variableChangeIsogeny (C : VariableChange F)
    (P : (W₁⁄F).toAffine.Point) :
    (translation W₁ P : W₁.FunctionField →ₐ[F] W₁.FunctionField).comp
        (variableChangeIsogeny C (rfl : C • W₁ = C • W₁)).fieldPullback =
      (variableChangeIsogeny C rfl).fieldPullback.comp
        (translation (C • W₁) ((W₁.pointEquivVariableChange F C).symm P) :
          (C • W₁).FunctionField →ₐ[F] (C • W₁).FunctionField) := by
  set ψ := (variableChangeIsogeny C (rfl : C • W₁ = C • W₁)).fieldPullback
  set e := W₁.pointEquivVariableChange W₁.FunctionField C
  -- both sides send the generic point of `C • W` to `e⁻¹ g + P'`, `g` the generic point of `W`
  have hgen : Point.map ψ (genericPoint (C • W₁)) = e.symm (genericPoint W₁) := by
    rw [← tautologicalPoint_eq_map_genericPoint, variableChangeIsogeny_pullback,
      tautologicalPoint_variableChangePullback]
  have htaut : CoordinatePullback.tautologicalPoint
      (((translation W₁ P : W₁.FunctionField →ₐ[F] W₁.FunctionField).comp ψ).comp
        (CoordinatePullback.id (C • W₁))) =
      CoordinatePullback.tautologicalPoint
        ((ψ.comp (translation (C • W₁) ((W₁.pointEquivVariableChange F C).symm P) :
          (C • W₁).FunctionField →ₐ[F] (C • W₁).FunctionField)).comp
            (CoordinatePullback.id (C • W₁))) := by
    rw [CoordinatePullback.tautologicalPoint_comp, CoordinatePullback.tautologicalPoint_comp,
      CoordinatePullback.tautologicalPoint_id, ← Point.map_map, ← Point.map_map, hgen,
      map_pointEquivVariableChange_symm, map_translation_genericPoint, map_translation_genericPoint,
      translatedGenericPoint_def, translatedGenericPoint_def, map_add, map_add,
      Point.map_baseChange, hgen, ← map_pointEquivVariableChange_symm]
  refine AlgHom.toRingHom_injective
    (IsFractionRing.ringHom_ext (A := (C • W₁).CoordinateRing) fun z ↦ ?_)
  simpa using DFunLike.congr_fun (CoordinatePullback.tautologicalPoint_injective htaut) z

/-- **A change of variables carries translations to translations**, for any change of variables
`C • W₁ = W₂`: there is a point `P'` of `W₂` with `τ_P^* ∘ ψ = ψ ∘ τ_{P'}^*`, where `ψ` is the
pullback of the isomorphism `W₁ → W₂`. -/
theorem exists_translation_comp_fieldPullback_variableChangeIsogeny {C : VariableChange F}
    (h : C • W₁ = W₂) (P : (W₁⁄F).toAffine.Point) :
    ∃ P' : (W₂⁄F).toAffine.Point,
      (translation W₁ P : W₁.FunctionField →ₐ[F] W₁.FunctionField).comp
          (variableChangeIsogeny C h).fieldPullback =
        (variableChangeIsogeny C h).fieldPullback.comp
          (translation W₂ P' : W₂.FunctionField →ₐ[F] W₂.FunctionField) := by
  subst h
  exact ⟨_, translation_comp_fieldPullback_variableChangeIsogeny C P⟩

end Conjugation

end WeierstrassCurve.Affine
