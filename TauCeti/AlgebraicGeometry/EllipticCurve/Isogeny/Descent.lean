/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Galois
public import Mathlib.FieldTheory.Galois.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace

/-!
# Galois descent of isogenies

An isogeny between curves defined over `F`, after base change to a Galois extension `K/F`,
descends uniquely to `F` exactly when its function-field pullback is Galois equivariant.
Equivalently, the isogeny is fixed by every coefficient conjugation.

Pointedness is preserved and reflected by change of the coefficient field: a coordinate pullback
satisfies `MapsInfinity` exactly when its base change does. Equivalently, the pulled-back target
`x`-coordinate has a pole at the source's point at infinity before base change exactly when it
does afterwards.

The extension need not be finite. In particular the criterion applies to a separable closure of
an imperfect field, the descent step used in constructing the dual of a separable isogeny over
its field of definition. Neither ellipticity nor separability of the isogeny is needed here.

## Main results

* `TauCeti.Isogeny.existsUnique_map_eq_iff_galoisEquivariant`: the function-field criterion.
* `TauCeti.Isogeny.existsUnique_map_eq_iff_galoisFixed`: the coefficient-conjugation criterion.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.6.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

open scoped WeierstrassCurve

namespace TauCeti

namespace Isogeny

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  (W₁ W₂ : WeierstrassCurve F)

variable [IsGalois F K]

/-- An isogeny after a Galois extension descends uniquely precisely when its function-field
pullback is equivariant. -/
theorem existsUnique_map_eq_iff_galoisEquivariant
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) :
    (∃! ψ : Isogeny W₁.toAffine W₂.toAffine, ψ.map (algebraMap F K) = φ) ↔
      ∀ (σ : K ≃ₐ[F] K) z,
        W₁.functionFieldGaloisAction σ (φ.fieldPullback z) =
          φ.fieldPullback (W₂.functionFieldGaloisAction σ z) := by
  constructor
  · rintro ⟨ψ, hψ, -⟩ σ z
    exact (galoisConj_eq_iff_fieldPullback_equivariant W₁ W₂ φ σ).mp
      (hψ ▸ galoisConj_map_algebraMap W₁ W₂ ψ σ) z
  · intro hφ
    -- First descend the field map, with its defining base-change square and uniqueness.
    obtain ⟨f, hf, hunique⟩ :=
      (W₁.existsUnique_functionFieldMap_iff_galoisEquivariant W₂ φ.fieldPullback).mpr hφ
    let p : CoordinatePullback W₁.toAffine W₂.toAffine :=
      f.comp (IsScalarTower.toAlgHom F W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField)
    -- Constants and the two coordinates determine a coordinate pullback. The field-map square
    -- therefore identifies the base change of the restriction with the original pullback.
    have hmap : p.map (algebraMap F K) = φ.pullback := by
      apply CoordinateRing.algHom_ext
      · rw [CoordinatePullback.map_of_X]
        -- Evaluate the restricted composite on the coordinate-ring image of `X`.
        change Affine.FunctionField.map W₁.toAffine (algebraMap F K)
            (f (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
              (AdjoinRoot.of W₂.toAffine.polynomial Polynomial.X))) =
          φ.pullback (AdjoinRoot.of (W₂⁄K).toAffine.polynomial Polynomial.X)
        rw [hf, Affine.FunctionField.map_algebraMap_coordinateRing,
          CoordinateRing.map_of_X]
        exact φ.fieldPullback_algebraMap _
      · rw [CoordinatePullback.map_root]
        -- Evaluate the restricted composite on the coordinate-ring image of `Y`.
        change Affine.FunctionField.map W₁.toAffine (algebraMap F K)
            (f (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
              (AdjoinRoot.root W₂.toAffine.polynomial))) =
          φ.pullback (AdjoinRoot.root (W₂⁄K).toAffine.polynomial)
        rw [hf, Affine.FunctionField.map_algebraMap_coordinateRing,
          CoordinateRing.map_root]
        exact φ.fieldPullback_algebraMap _
    -- Reflection of pointedness is available before packaging the restriction as an isogeny.
    have hp : p.MapsInfinity := (CoordinatePullback.mapsInfinity_map_iff p _).mp
      (hmap.symm ▸ φ.mapsInfinity)
    let ψ : Isogeny W₁.toAffine W₂.toAffine := ⟨p, hp⟩
    have hψ : ψ.map (algebraMap F K) = φ := by
      apply Isogeny.ext
      rw [map_pullback]
      exact hmap
    refine ⟨ψ, hψ, ?_⟩
    -- Field-map uniqueness identifies every other descended pullback with the same restriction.
    intro ψ' hψ'
    have hfield : ψ'.fieldPullback = f := hunique _ fun z ↦ by
      rw [← map_fieldPullback_map, hψ']
      rfl
    apply Isogeny.ext
    apply AlgHom.ext
    intro z
    rw [← fieldPullback_algebraMap ψ' z, hfield]
    rfl

/-- An isogeny between base-changed ground-field curves descends uniquely exactly when every
coefficient Galois conjugation fixes it. The extension may be infinite, as for a separable
closure; no perfectness hypothesis on the ground field is imposed. -/
theorem existsUnique_map_eq_iff_galoisFixed
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) :
    (∃! ψ : Isogeny W₁.toAffine W₂.toAffine, ψ.map (algebraMap F K) = φ) ↔
      ∀ σ : K ≃ₐ[F] K, φ.galoisConj W₁ W₂ σ = φ := by
  rw [existsUnique_map_eq_iff_galoisEquivariant]
  exact forall_congr' fun σ ↦ (galoisConj_eq_iff_fieldPullback_equivariant W₁ W₂ φ σ).symm

end Isogeny

end TauCeti

end
