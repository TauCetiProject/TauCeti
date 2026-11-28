/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Frobenius
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Composition
import TauCeti.FieldTheory.Finite.SepClosedSubfield

/-!
# Frobenius descent of isogenies

`TauCeti.Isogeny.existsUnique_map_eq_iff_baseChangeFrobenius_comp_eq` gives descent over algebraic
extensions of finite fields. It combines `TauCeti.Isogeny.existsUnique_map_eq_iff_galoisEquivariant`
with `WeierstrassCurve.functionFieldGaloisAction_eq_self_of_frobenius_eq_self`. See
[J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.
-/

public section

open scoped WeierstrassCurve

namespace TauCeti.Isogeny

attribute [local simp] RingHom.comp_apply RingEquiv.toRingHom_eq_coe RingEquiv.coe_toRingHom
  AlgHom.toRingHom_eq_coe AlgHom.coe_toRingHom

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
  [Algebra.IsAlgebraic F K] {W₁ W₂ : WeierstrassCurve F}

/-- Over an algebraic extension of a finite field, an isogeny descends uniquely to the base field
exactly when it commutes with base-field Frobenius (Silverman V.2). -/
theorem existsUnique_map_eq_iff_baseChangeFrobenius_comp_eq
    {φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine} :
    (∃! ψ : Isogeny W₁.toAffine W₂.toAffine, ψ.map (algebraMap F K) = φ) ↔
      (baseChangeFrobenius K W₂.toAffine).comp φ = φ.comp (baseChangeFrobenius K W₁.toAffine) := by
  constructor
  · rintro ⟨ψ, rfl, -⟩
    have h := congrArg (fun f : Isogeny W₁.toAffine W₂.toAffine ↦ f.map (algebraMap F K))
      (frobeniusIsogeny_comp ψ)
    simp only [Isogeny.comp_map] at h
    rw [baseChangeFrobenius_def, baseChangeFrobenius_def]
    exact h
  · intro hφ
    let := Fintype.ofFinite F
    have := TauCeti.FiniteField.isGalois_of_isAlgebraic F K
    let Frob := FiniteField.frobeniusAlgEquivOfAlgebraic F K
    have hFrob : Frob.toAlgHom = FiniteField.frobeniusAlgHom F K :=
      AlgHom.ext (congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic F K))
    have hpow (W : WeierstrassCurve F) (z : (W⁄K).toAffine.FunctionField) :
        (baseChangeFrobenius K W.toAffine).fieldPullback (W.functionFieldGaloisAction Frob z) =
          z ^ Fintype.card F := by
      have hmap' : W.functionFieldMapBaseChange (FiniteField.frobeniusAlgHom F K) z =
          W.functionFieldGaloisAction Frob z := by
        simpa [hFrob] using
          RingHom.congr_fun (W.functionFieldMapBaseChange_eq_galoisAction Frob) z
      rw [← hmap']
      exact fieldPullback_baseChangeFrobenius_mapBaseChange W.toAffine z
    have heq := congrArg fieldPullback hφ
    simp only [comp_fieldPullback] at heq
    have hfix {z : (W₂⁄K).toAffine.FunctionField}
        (hz : W₂.functionFieldGaloisAction Frob z = z)
        (τ : K ≃ₐ[F] K) :
        W₁.functionFieldGaloisAction τ (φ.fieldPullback z) = φ.fieldPullback z := by
      apply W₁.functionFieldGaloisAction_eq_self_of_frobenius_eq_self _ τ
      have hzq : (baseChangeFrobenius K W₂.toAffine).fieldPullback z = z ^ Fintype.card F := by
        simpa only [hz] using hpow W₂ z
      apply (baseChangeFrobenius K W₁.toAffine).fieldPullback.injective
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hpow W₁,
        ← AlgHom.comp_apply, ← heq, AlgHom.comp_apply, hzq, map_pow]
    apply (existsUnique_map_eq_iff_galoisEquivariant W₁ W₂ φ).mpr
    intro τ z
    let left := (W₁.functionFieldGaloisAction τ).toRingHom.comp φ.fieldPullback.toRingHom
    let right := φ.fieldPullback.toRingHom.comp (W₂.functionFieldGaloisAction τ).toRingHom
    have happly (a : (W₂⁄K).toAffine.FunctionField) : left a = right a ↔
        W₁.functionFieldGaloisAction τ (φ.fieldPullback a) =
          φ.fieldPullback (W₂.functionFieldGaloisAction τ a) := by
      simp only [left, right, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have hequiv : left = right := by
      apply WeierstrassCurve.Affine.FunctionField.ringHom_ext
      · intro a
        rw [happly]
        simp only [AlgHom.commutes, WeierstrassCurve.functionFieldGaloisAction_algebraMap]
      · rw [happly, WeierstrassCurve.functionFieldGaloisAction_genericX]
        exact hfix (W₂.functionFieldGaloisAction_genericX _) τ
      · rw [happly, WeierstrassCurve.functionFieldGaloisAction_genericY]
        exact hfix (W₂.functionFieldGaloisAction_genericY _) τ
    exact (happly z).mp (RingHom.congr_fun hequiv z)

end TauCeti.Isogeny

end
