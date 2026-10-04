/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange

/-!
# Galois conjugation of isogenies

Let `W₁` and `W₂` be Weierstrass curves over `F`, and let `K/F` be a field extension. An
`F`-automorphism `σ` of `K` conjugates an isogeny `φ : (W₁)_K → (W₂)_K`: apply `σ⁻¹` to
the coefficients of a function on the target, pull it back along `φ`, and apply `σ` to the
resulting function on the source. The two semilinearities cancel, so the conjugate pullback is
again a `K`-algebra homomorphism.

Conjugation preserves the condition that infinity maps to infinity. Algebraically, a monic
integral-dependence relation for the source coordinate is transported by the coefficient
automorphisms. The construction therefore gives a genuine Galois action on the type of isogenies,
and it respects identity and composition. These are the equivariance facts needed to descend an
isogeny constructed after extending the base field.

## Main definitions

* `TauCeti.CoordinatePullback.galoisConj`: conjugation of a coordinate pullback.
* `TauCeti.Isogeny.galoisConj`: conjugation of an isogeny.
* `TauCeti.Isogeny.galoisAction`: the resulting action on isogenies between two fixed
  base-changed curves.

## Main results

* `TauCeti.Isogeny.galoisConj_fieldPullback`: conjugation commutes with extension of a pullback
  to the function fields.
* `TauCeti.Isogeny.galoisConj_eq_iff_fieldPullback_equivariant`: conjugation fixes an isogeny
  exactly when its function-field pullback commutes with the coefficient automorphism.
* `TauCeti.Isogeny.galoisConj_id` and `TauCeti.Isogeny.galoisConj_comp`: conjugation preserves
  identity and composition.
* `TauCeti.Isogeny.galoisConj_map_algebraMap`: an isogeny defined over the ground field is fixed.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.6.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable (W₁ W₂ : WeierstrassCurve F)

namespace CoordinatePullback

/-- **Galois conjugation of a coordinate pullback.** Its underlying ring homomorphism is
`σ ∘ φ ∘ σ⁻¹`; the semilinearity of the two outer maps cancels, making the composite
`K`-linear. -/
noncomputable def galoisConj
  (φ : CoordinatePullback (W₁⁄K).toAffine (W₂⁄K).toAffine) (σ : K ≃ₐ[F] K) :
    CoordinatePullback (W₁⁄K).toAffine (W₂⁄K).toAffine where
  toRingHom := (W₁.functionFieldGaloisAction σ).toRingHom.comp
    (φ.toRingHom.comp (W₂.coordinateRingGaloisAction σ.symm).toRingHom)
  commutes' a := by simp

/-- The conjugate pullback is obtained by applying `σ⁻¹` on the target, then `φ`, then `σ`
on the source. -/
@[simp]
theorem galoisConj_apply
    (φ : CoordinatePullback (W₁⁄K).toAffine (W₂⁄K).toAffine) (σ : K ≃ₐ[F] K)
    (z : (W₂⁄K).toAffine.CoordinateRing) :
    φ.galoisConj W₁ W₂ σ z =
      W₁.functionFieldGaloisAction σ
        (φ (W₂.coordinateRingGaloisAction σ.symm z)) :=
  (rfl)

/-- Conjugation by the identity fixes a coordinate pullback. -/
@[simp]
theorem galoisConj_one
    (φ : CoordinatePullback (W₁⁄K).toAffine (W₂⁄K).toAffine) :
    φ.galoisConj W₁ W₂ 1 = φ := by
  apply CoordinateRing.algHom_ext <;> simp

/-- Successive Galois conjugations multiply their automorphisms. -/
@[simp]
theorem galoisConj_galoisConj
    (φ : CoordinatePullback (W₁⁄K).toAffine (W₂⁄K).toAffine) (σ τ : K ≃ₐ[F] K) :
    (φ.galoisConj W₁ W₂ τ).galoisConj W₁ W₂ σ =
      φ.galoisConj W₁ W₂ (σ * τ) := by
  apply CoordinateRing.algHom_ext <;> simp

/-- Galois conjugation preserves the condition that infinity maps to infinity. -/
theorem MapsInfinity.galoisConj
    {φ : CoordinatePullback (W₁⁄K).toAffine (W₂⁄K).toAffine} (hφ : φ.MapsInfinity)
    (σ : K ≃ₐ[F] K) : (φ.galoisConj W₁ W₂ σ).MapsInfinity := by
  rw [mapsInfinity_iff_isIntegralElem_genericX]
  have hX := (mapsInfinity_iff_isIntegralElem_genericX φ).mp hφ
  have hcomm :
      (φ.galoisConj W₁ W₂ σ).toRingHom.comp
          (W₂.coordinateRingGaloisAction σ).toRingHom =
        (W₁.functionFieldGaloisAction σ).toRingHom.comp φ.toRingHom := by
    apply CoordinateRing.ringHom_ext <;> simp
  apply RingHom.IsIntegralElem.of_comp
    (f := (W₂.coordinateRingGaloisAction σ).toRingHom)
  rw [hcomm]
  simpa using hX.map (W₁.functionFieldGaloisAction σ).toRingHom

end CoordinatePullback

namespace Isogeny

/-- **Galois conjugation of an isogeny** between base changes of curves defined over `F`. -/
noncomputable def galoisConj
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) (σ : K ≃ₐ[F] K) :
    Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine where
  pullback := φ.pullback.galoisConj W₁ W₂ σ
  mapsInfinity := φ.mapsInfinity.galoisConj W₁ W₂ σ

/-- The pullback of the conjugate is the conjugate of the pullback. -/
@[simp]
theorem galoisConj_pullback
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) (σ : K ≃ₐ[F] K) :
    (φ.galoisConj W₁ W₂ σ).pullback = φ.pullback.galoisConj W₁ W₂ σ :=
  (rfl)

/-- Conjugating a function-field pullback is the function-field pullback of the conjugate
isogeny. -/
@[simp]
theorem galoisConj_fieldPullback
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) (σ : K ≃ₐ[F] K)
    (z : (W₂⁄K).toAffine.FunctionField) :
    (φ.galoisConj W₁ W₂ σ).fieldPullback
        (W₂.functionFieldGaloisAction σ z) =
      W₁.functionFieldGaloisAction σ (φ.fieldPullback z) := by
  have h :
      (φ.galoisConj W₁ W₂ σ).fieldPullback.toRingHom.comp
          (W₂.functionFieldGaloisAction σ).toRingHom =
        (W₁.functionFieldGaloisAction σ).toRingHom.comp
          φ.fieldPullback.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := (W₂⁄K).toAffine.CoordinateRing)
    intro x
    simp only [RingHom.comp_apply]
    -- Expose the coercions from the bundled ring maps so the function-field action's
    -- coordinate-ring compatibility lemma can rewrite the inner term.
    change (φ.galoisConj W₁ W₂ σ).fieldPullback
        (W₂.functionFieldGaloisAction σ
          (algebraMap (W₂⁄K).toAffine.CoordinateRing (W₂⁄K).toAffine.FunctionField x)) =
      W₁.functionFieldGaloisAction σ
        (φ.fieldPullback
          (algebraMap (W₂⁄K).toAffine.CoordinateRing (W₂⁄K).toAffine.FunctionField x))
    rw [
      W₂.functionFieldGaloisAction_algebraMap_coordinateRing,
      fieldPullback_algebraMap, fieldPullback_algebraMap]
    rw [galoisConj_pullback, CoordinatePullback.galoisConj_apply]
    have hσ : σ.symm * σ = 1 := by
      ext a
      exact σ.symm_apply_apply a
    have hx : W₂.coordinateRingGaloisAction σ.symm
        (W₂.coordinateRingGaloisAction σ x) = x := by
      have hmap := congrArg (fun e : (W₂⁄K).toAffine.CoordinateRing ≃+*
          (W₂⁄K).toAffine.CoordinateRing ↦ e x)
        (map_mul (W₂.coordinateRingGaloisAction) σ.symm σ)
      simpa [hσ] using hmap.symm
    exact congrArg (fun y ↦ W₁.functionFieldGaloisAction σ (φ.pullback y)) hx
  exact RingHom.congr_fun h z

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

/-- Conjugation by the identity fixes an isogeny. -/
@[simp]
theorem galoisConj_one (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) :
    φ.galoisConj W₁ W₂ 1 = φ :=
  Isogeny.ext <| CoordinatePullback.galoisConj_one W₁ W₂ φ.pullback

/-- Successive Galois conjugations multiply their automorphisms. -/
@[simp]
theorem galoisConj_galoisConj
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) (σ τ : K ≃ₐ[F] K) :
    (φ.galoisConj W₁ W₂ τ).galoisConj W₁ W₂ σ =
      φ.galoisConj W₁ W₂ (σ * τ) :=
  Isogeny.ext <| CoordinatePullback.galoisConj_galoisConj W₁ W₂ φ.pullback σ τ

/-- Galois conjugation fixes the identity isogeny. -/
@[simp]
theorem galoisConj_id (σ : K ≃ₐ[F] K) :
    (Isogeny.id (W₁⁄K).toAffine).galoisConj W₁ W₁ σ =
      Isogeny.id (W₁⁄K).toAffine := by
  apply Isogeny.ext
  apply CoordinateRing.algHom_ext <;> simp

/-- Galois conjugation respects composition of isogenies. -/
@[simp]
theorem galoisConj_comp (W₃ : WeierstrassCurve F)
    (ψ : Isogeny (W₂⁄K).toAffine (W₃⁄K).toAffine)
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) (σ : K ≃ₐ[F] K) :
    (ψ.comp φ).galoisConj W₁ W₃ σ =
      (ψ.galoisConj W₂ W₃ σ).comp (φ.galoisConj W₁ W₂ σ) := by
  apply Isogeny.ext
  apply CoordinateRing.algHom_ext <;>
    simp only [galoisConj_pullback, CoordinatePullback.galoisConj_apply, comp_pullback,
      AlgHom.comp_apply, galoisConj_fieldPullback]

/-- **An isogeny defined over the ground field is fixed by Galois conjugation.** -/
@[simp]
theorem galoisConj_map_algebraMap
    (φ : Isogeny W₁.toAffine W₂.toAffine) (σ : K ≃ₐ[F] K) :
    (φ.map (algebraMap F K)).galoisConj W₁ W₂ σ = φ.map (algebraMap F K) := by
  apply Isogeny.ext
  have hconj :
      ((φ.map (algebraMap F K)).galoisConj W₁ W₂ σ).pullback =
        (φ.map (algebraMap F K)).pullback.galoisConj W₁ W₂ σ :=
    galoisConj_pullback W₁ W₂ (φ.map (algebraMap F K)) σ
  rw [hconj, map_pullback]
  have hconj_apply (z : (W₂⁄K).toAffine.CoordinateRing) :
      (φ.pullback.map (algebraMap F K)).galoisConj W₁ W₂ σ z =
        W₁.functionFieldGaloisAction σ
          (φ.pullback.map (algebraMap F K)
            (W₂.coordinateRingGaloisAction σ.symm z)) :=
    CoordinatePullback.galoisConj_apply W₁ W₂ (φ.pullback.map (algebraMap F K)) σ z
  have hmap_x :
      φ.pullback.map (algebraMap F K)
          (AdjoinRoot.of (W₂⁄K).toAffine.polynomial Polynomial.X) =
        Affine.FunctionField.map W₁.toAffine (algebraMap F K)
          (φ.pullback (AdjoinRoot.of W₂.toAffine.polynomial Polynomial.X)) :=
    CoordinatePullback.map_of_X φ.pullback (algebraMap F K)
  have hmap_y :
      φ.pullback.map (algebraMap F K) (AdjoinRoot.root (W₂⁄K).toAffine.polynomial) =
        Affine.FunctionField.map W₁.toAffine (algebraMap F K)
          (φ.pullback (AdjoinRoot.root W₂.toAffine.polynomial)) :=
    CoordinatePullback.map_root φ.pullback (algebraMap F K)
  apply CoordinateRing.algHom_ext
  · rw [hconj_apply, coordinateRingGaloisAction_of, Polynomial.map_X, hmap_x,
      W₁.functionFieldGaloisAction_map_algebraMap]
    exact hmap_x.symm
  · rw [hconj_apply, coordinateRingGaloisAction_root, hmap_y,
      W₁.functionFieldGaloisAction_map_algebraMap]
    exact hmap_y.symm

/-- **The Galois action on isogenies** between two fixed base-changed curves. -/
noncomputable def galoisAction :
    (K ≃ₐ[F] K) →* Equiv.Perm (Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) where
  toFun σ :=
    { toFun := fun φ ↦ φ.galoisConj W₁ W₂ σ
      invFun := fun φ ↦ φ.galoisConj W₁ W₂ σ.symm
      left_inv := fun φ ↦
        (galoisConj_galoisConj W₁ W₂ φ σ.symm σ).trans <| by
          have hσ : σ.symm * σ = 1 := by
            ext a
            exact σ.symm_apply_apply a
          rw [hσ]
          exact galoisConj_one W₁ W₂ φ
      right_inv := fun φ ↦
        (galoisConj_galoisConj W₁ W₂ φ σ σ.symm).trans <| by
          have hσ : σ * σ.symm = 1 := by
            ext a
            exact σ.apply_symm_apply a
          rw [hσ]
          exact galoisConj_one W₁ W₂ φ }
  map_one' := Equiv.ext fun φ ↦ galoisConj_one W₁ W₂ φ
  map_mul' σ τ := Equiv.ext fun φ ↦
    (galoisConj_galoisConj W₁ W₂ φ σ τ).symm

/-- The bundled Galois action is Galois conjugation. -/
@[simp]
theorem galoisAction_apply
    (σ : K ≃ₐ[F] K) (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) :
    galoisAction W₁ W₂ σ φ = φ.galoisConj W₁ W₂ σ :=
  (rfl)

end Isogeny

end TauCeti

end
