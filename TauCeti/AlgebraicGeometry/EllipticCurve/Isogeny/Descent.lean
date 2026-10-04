/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Galois
public import Mathlib.FieldTheory.Galois.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace

/-!
# Galois descent of isogenies

An isogeny between curves defined over `F`, after base change to a Galois extension `K/F`,
descends uniquely to `F` exactly when its function-field pullback is Galois equivariant.
Equivalently, the isogeny is fixed by every coefficient conjugation.

Function-field descent supplies the underlying algebra homomorphism. Its restriction to the
target coordinate ring is pointed because pointedness is reflected by change of the coefficient
field: the pulled-back `x`-coordinate has a pole at infinity before base change exactly when it
does afterwards. This uses the infinity-place criterion and its uniqueness theorem, rather than
any point map of the not-yet-constructed descended isogeny.

The extension need not be finite. In particular the criterion applies to a separable closure of
an imperfect field, the descent step used in constructing the dual of a separable isogeny over
its field of definition. Neither ellipticity nor separability of the isogeny is needed here.

## Main results

* `TauCeti.CoordinatePullback.mapsInfinity_map_iff`: base change reflects pointedness.
* `TauCeti.Isogeny.existsUnique_map_eq_iff_galoisEquivariant`: the function-field criterion.
* `TauCeti.Isogeny.existsUnique_map_eq_iff_galoisFixed`: the coefficient-conjugation criterion.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.6.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

open scoped WeierstrassCurve

namespace TauCeti

namespace CoordinatePullback

variable {F K : Type*} [Field F] [Field K] {W₁ W₂ : Affine F}

/-- Changing the coefficient field reflects pointedness. The pole criterion for `MapsInfinity`
is unchanged because the infinity valuation after base change restricts to the original one. -/
theorem mapsInfinity_map_iff (p : CoordinatePullback W₁ W₂) (f : F →+* K) :
    (p.map f).MapsInfinity ↔ p.MapsInfinity := by
  refine ⟨?_, fun hp ↦ hp.map f⟩
  intro hp
  rw [mapsInfinity_iff_one_lt_infinityPlace] at hp ⊢
  have hequiv := isEquiv_comap_infinityPlace_map W₁ f
  have hcoord := p.map_of_X f
  -- The polynomial algebra map sends `X` to its `AdjoinRoot.of` class, the base-change API's
  -- coordinate spelling.
  change 1 < infinityPlace (W₁.map f)
    ((p.map f) (AdjoinRoot.of (W₂.map f).polynomial Polynomial.X)) at hp
  change 1 < infinityPlace W₁ (p (AdjoinRoot.of W₂.polynomial Polynomial.X))
  rw [hcoord] at hp
  exact not_le.1 fun hle ↦ (not_le.2 hp)
    ((Valuation.isEquiv_iff_val_le_one.1 hequiv).2 hle)

end CoordinatePullback

namespace Isogeny

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  (W₁ W₂ : WeierstrassCurve F)

/-- Galois conjugation fixes an isogeny exactly when its function-field pullback commutes with
the corresponding coefficient automorphism. This compares actual field maps, including their
action on functions with poles. -/
theorem galoisConj_eq_iff_fieldPullback_equivariant
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) (σ : K ≃ₐ[F] K) :
    φ.galoisConj W₁ W₂ σ = φ ↔
      ∀ z, W₁.functionFieldGaloisAction σ (φ.fieldPullback z) =
        φ.fieldPullback (W₂.functionFieldGaloisAction σ z) := by
  constructor
  · intro h z
    rw [← galoisConj_fieldPullback W₁ W₂ φ σ, h]
  · intro h
    have hfield : (φ.galoisConj W₁ W₂ σ).fieldPullback = φ.fieldPullback := by
      apply AlgHom.ext
      intro z
      obtain ⟨z, rfl⟩ := (W₂.functionFieldGaloisAction σ).surjective z
      rw [galoisConj_fieldPullback, h]
    apply Isogeny.ext
    apply AlgHom.ext
    intro z
    exact (fieldPullback_algebraMap _ z).symm.trans
      ((congrArg (fun g ↦ g (algebraMap (W₂⁄K).toAffine.CoordinateRing
        (W₂⁄K).toAffine.FunctionField z)) hfield).trans (fieldPullback_algebraMap _ z))

variable [IsGalois F K]

/-- An isogeny after a Galois extension descends uniquely precisely when its function-field
pullback is equivariant. Pointedness is recovered from the base-changed coordinate pullback,
without using an induced point map before the descended isogeny exists. -/
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
