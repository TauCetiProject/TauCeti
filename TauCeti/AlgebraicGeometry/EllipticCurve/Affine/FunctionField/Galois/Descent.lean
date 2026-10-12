/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.FixedField

/-!
# Galois descent of Weierstrass function-field maps

A function-field map between base changes of two Weierstrass curves descends uniquely to the
ground field if and only if it commutes with the coefficient Galois actions. The criterion
applies to arbitrary Galois extensions, including a separable closure over an imperfect field;
neither ellipticity nor finiteness of the extension is needed.

The descended map is characterized by its commuting square with the two function-field
base-change maps. This is the field-map descent step in constructing a dual isogeny over its
field of definition. Pointedness and degree are separate properties of that construction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.6.
-/

public section

open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K]
  (W₁ W₂ : WeierstrassCurve F)

/-- A map between the function fields of two base-changed Weierstrass curves descends uniquely
to the ground field exactly when it commutes with every coefficient automorphism. The equality
in the existence statement is the defining base-change square of the descended map. -/
theorem existsUnique_functionFieldMap_iff_galoisEquivariant
    (g : (W₂⁄K).toAffine.FunctionField →ₐ[K] (W₁⁄K).toAffine.FunctionField) :
    (∃! f : W₂.toAffine.FunctionField →ₐ[F] W₁.toAffine.FunctionField,
      ∀ z, Affine.FunctionField.map W₁.toAffine (algebraMap F K) (f z) =
        g (Affine.FunctionField.map W₂.toAffine (algebraMap F K) z)) ↔
      ∀ (σ : K ≃ₐ[F] K) z,
        W₁.functionFieldGaloisAction σ (g z) = g (W₂.functionFieldGaloisAction σ z) := by
  classical
  constructor
  · rintro ⟨f, hf, -⟩ σ z
    -- Constants and the generic coordinates generate the base-changed function field.
    -- Constants satisfy equivariance by `K`-linearity, and the coordinates come from `F`.
    have h : (W₁.functionFieldGaloisAction σ).toRingHom.comp g.toRingHom =
        g.toRingHom.comp (W₂.functionFieldGaloisAction σ).toRingHom := by
      apply Affine.FunctionField.ringHom_ext
      · intro a
        simp
      · -- Expose evaluation of the bundled ring maps; the target uses base-change notation,
        -- while the coordinate lemmas use the same curve written with `Affine.map`.
        change W₁.functionFieldGaloisAction σ (g (W₂⁄K).toAffine.genericX) =
          g (W₂.functionFieldGaloisAction σ (W₂⁄K).toAffine.genericX)
        have hm : Affine.FunctionField.map W₂.toAffine (algebraMap F K)
            W₂.toAffine.genericX = (W₂⁄K).toAffine.genericX :=
          Affine.FunctionField.map_genericX ..
        have hx := hf W₂.toAffine.genericX
        rw [hm] at hx
        rw [functionFieldGaloisAction_genericX, ← hx,
          functionFieldGaloisAction_map_algebraMap]
      · -- As above, identify pointwise evaluation through the ring-map coercions.
        change W₁.functionFieldGaloisAction σ (g (W₂⁄K).toAffine.genericY) =
          g (W₂.functionFieldGaloisAction σ (W₂⁄K).toAffine.genericY)
        have hm : Affine.FunctionField.map W₂.toAffine (algebraMap F K)
            W₂.toAffine.genericY = (W₂⁄K).toAffine.genericY :=
          Affine.FunctionField.map_genericY ..
        have hy := hf W₂.toAffine.genericY
        rw [hm] at hy
        rw [functionFieldGaloisAction_genericY, ← hy,
          functionFieldGaloisAction_map_algebraMap]
    exact RingHom.congr_fun h z
  · intro hg
    -- Equivariance sends ground-field functions into the fixed field, which is exactly
    -- the ground-field image. Restrict to that image and invert its embedding.
    let b₁ : W₁.toAffine.FunctionField →ₐ[F] (W₁⁄K).toAffine.FunctionField :=
      { toRingHom := Affine.FunctionField.map W₁.toAffine (algebraMap F K)
        commutes' := fun a ↦ (Affine.FunctionField.map_algebraMap ..).trans
          (IsScalarTower.algebraMap_apply F K (W₁⁄K).toAffine.FunctionField a).symm }
    let b₂ : W₂.toAffine.FunctionField →ₐ[F] (W₂⁄K).toAffine.FunctionField :=
      { toRingHom := Affine.FunctionField.map W₂.toAffine (algebraMap F K)
        commutes' := fun a ↦ (Affine.FunctionField.map_algebraMap ..).trans
          (IsScalarTower.algebraMap_apply F K (W₂⁄K).toAffine.FunctionField a).symm }
    let r : W₂.toAffine.FunctionField →ₐ[F] (W₁⁄K).toAffine.FunctionField :=
      (g.restrictScalars F).comp b₂
    -- `WeierstrassCurve.mem_range_functionFieldMap_iff_fixed` identifies the fixed field
    -- of the coefficient action with the ground-field image.
    have hr (z : W₂.toAffine.FunctionField) : r z ∈ b₁.fieldRange.toSubalgebra := by
      apply (W₁.mem_range_functionFieldMap_iff_fixed _).mpr
      intro σ
      -- Evaluate `r` and `b₂` to expose the coefficient-map equality.
      change W₁.functionFieldGaloisAction σ
          (g (Affine.FunctionField.map W₂.toAffine (algebraMap F K) z)) =
        g (Affine.FunctionField.map W₂.toAffine (algebraMap F K) z)
      exact (hg σ _).trans
        (congrArg g (functionFieldGaloisAction_map_algebraMap W₂ σ z))
    -- Mathlib's `AlgEquiv.ofInjectiveField` identifies the ground function field with its image.
    let f : W₂.toAffine.FunctionField →ₐ[F] W₁.toAffine.FunctionField :=
      (AlgEquiv.ofInjectiveField b₁).symm.toAlgHom.comp (r.codRestrict _ hr)
    have hf (z : W₂.toAffine.FunctionField) :
        Affine.FunctionField.map W₁.toAffine (algebraMap F K) (f z) =
          g (Affine.FunctionField.map W₂.toAffine (algebraMap F K) z) := by
      -- Evaluate `f` through its restricted composite, and identify the two base-change maps.
      change b₁ ((AlgEquiv.ofInjectiveField b₁).symm ⟨r z, hr z⟩) = r z
      simpa only [AlgEquiv.ofInjectiveField, AlgEquiv.ofInjective_apply] using
        congrArg Subtype.val ((AlgEquiv.ofInjectiveField b₁).apply_symm_apply ⟨r z, hr z⟩)
    refine ⟨f, hf, ?_⟩
    intro f' hf'
    apply AlgHom.ext
    intro z
    exact (Affine.FunctionField.map W₁.toAffine (algebraMap F K)).injective
      ((hf' z).trans (hf z).symm)

end WeierstrassCurve

end
