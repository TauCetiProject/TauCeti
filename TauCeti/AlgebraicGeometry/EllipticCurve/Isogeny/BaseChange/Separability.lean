/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential

/-!
# Separability of isogenies under base change

An isogeny of elliptic curves is separable if and only if any base change of it is separable.
This file proves that compatibility without first comparing the degrees of the original and
base-changed function-field extensions. Instead it uses the differential criterion: an isogeny is
separable exactly when the pullback of the invariant differential is nonzero.

For a field homomorphism `f : F →+* K`, Mathlib's functorial map on Kähler differentials gives a
semilinear map

```text
  Ω[F(W)/F] ──▸ Ω[K(W.map f)/K].
```

It sends the invariant differential of `W` to that of `W.map f`. Since the invariant differential
is a basis, this map reflects zero. The commuting square
`Isogeny.map_fieldPullback_map` then shows that it intertwines pullback by an isogeny with pullback
by its base change.

## Main definitions

* `WeierstrassCurve.Affine.FunctionField.mapDifferential`: the semilinear map on differentials
  induced by base change of a Weierstrass function field.

## Main results

* `WeierstrassCurve.Affine.FunctionField.mapDifferential_invariantDifferential`: base change carries
  the invariant differential to the invariant differential.
* `TauCeti.Isogeny.mapDifferential_pullback_invariantDifferential`: base change commutes with the
  pullback of the invariant differential.
* `TauCeti.Isogeny.isSeparable_map_iff`: an isogeny is separable if and only if its base change is.

## Roadmap

This completes the separability clause of the first **Layer 0.5** milestone in
`TauCetiRoadmap/EllipticCurves/README.md`: base change of isogenies is compatible with separability.
It is also a prerequisite for the **Layer 1** dual-isogeny milestone, whose separable construction
starts by changing the base field to a separable closure.

No material is copied from an external formalisation.
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.FunctionField

variable {F K : Type*} [Field F] [Field K]

/-- **The map on Kähler differentials induced by field base change.** For `f : F →+* K`, this is
the semilinear map `Ω[F(W)/F] → Ω[K(W.map f)/K]` induced by the commuting square formed by `f`
and `FunctionField.map W f`. -/
noncomputable def mapDifferential (W : WeierstrassCurve.Affine F) (f : F →+* K) :
    KaehlerDifferential F W.FunctionField →ₛₗ[FunctionField.map W f]
      KaehlerDifferential K (W.map f).FunctionField := by
  letI : Algebra F K := f.toAlgebra
  letI : Algebra W.FunctionField (W.map f).FunctionField :=
    (FunctionField.map W f).toAlgebra
  letI : Algebra F (W.map f).FunctionField :=
    ((algebraMap K (W.map f).FunctionField).comp f).toAlgebra
  letI : SMul F (W.map f).FunctionField :=
    (inferInstance : Algebra F (W.map f).FunctionField).toSMul
  letI : IsScalarTower F K (W.map f).FunctionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F W.FunctionField (W.map f).FunctionField :=
    IsScalarTower.of_algebraMap_eq'
      (WeierstrassCurve.Affine.FunctionField.map_comp_algebraMap W f).symm
  letI : SMulCommClass K W.FunctionField (W.map f).FunctionField :=
    SMulCommClass.of_commMonoid K W.FunctionField (W.map f).FunctionField
  exact
    { toFun := KaehlerDifferential.map F K W.FunctionField (W.map f).FunctionField
      map_add' := map_add _
      map_smul' := fun c η ↦ by
        change KaehlerDifferential.map F K W.FunctionField (W.map f).FunctionField (c • η) =
          FunctionField.map W f c •
            KaehlerDifferential.map F K W.FunctionField (W.map f).FunctionField η
        rw [map_smul]
        rfl }

/-- Base change of differentials sends `d z` to the differential of the image of `z`. -/
@[simp]
theorem mapDifferential_D (W : WeierstrassCurve.Affine F) (f : F →+* K)
    (z : W.FunctionField) :
    mapDifferential W f (KaehlerDifferential.D F W.FunctionField z) =
      KaehlerDifferential.D K (W.map f).FunctionField (FunctionField.map W f z) := by
  simp [mapDifferential, KaehlerDifferential.map_D, RingHom.algebraMap_toAlgebra]

/-- Base change carries the denominator `2y + a₁x + a₃` of the invariant differential to the
corresponding denominator on the base-changed curve. -/
@[simp]
theorem map_invariantDifferentialDenom (W : WeierstrassCurve.Affine F) (f : F →+* K) :
    FunctionField.map W f (invariantDifferentialDenom W) =
      invariantDifferentialDenom (W.map f) := by
  simp [invariantDifferentialDenom_def, map_ofNat]

/-- **Base change carries the invariant differential to the invariant differential.** -/
@[simp]
theorem mapDifferential_invariantDifferential (W : WeierstrassCurve.Affine F) (f : F →+* K) :
    mapDifferential W f (invariantDifferential W) =
      invariantDifferential (W.map f) := by
  rw [invariantDifferential_def, invariantDifferential_def]
  rw [(mapDifferential W f).map_smulₛₗ, mapDifferential_D]
  simp

/-- **Base change of differentials reflects zero for an elliptic function field.** The invariant
differential is a basis on both curves, and the coefficient embedding `FunctionField.map W f` is
injective. -/
theorem mapDifferential_eq_zero_iff (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (f : F →+* K) (η : KaehlerDifferential F W.FunctionField) :
    mapDifferential W f η = 0 ↔ η = 0 := by
  obtain ⟨c, hc, -⟩ := existsUnique_smul_invariantDifferential W η
  rw [← hc, (mapDifferential W f).map_smulₛₗ, mapDifferential_invariantDifferential]
  constructor
  · intro h
    have hc₀ : FunctionField.map W f c = 0 :=
      (smul_eq_zero.mp h).resolve_right (invariantDifferential_ne_zero (W.map f))
    rw [map_eq_zero_iff _ (FunctionField.map W f).injective] at hc₀
    rw [hc₀, zero_smul]
  · intro h
    have hc₀ : c = 0 :=
      (smul_eq_zero.mp h).resolve_right (invariantDifferential_ne_zero W)
    rw [hc₀, map_zero, zero_smul]

end WeierstrassCurve.Affine.FunctionField

namespace TauCeti

namespace Isogeny

variable {F K : Type*} [Field F] [Field K]
variable {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **Pulling back the invariant differential commutes with field base change.** This is the
differential counterpart of `map_fieldPullback_map`. -/
theorem mapDifferential_pullback_invariantDifferential (φ : Isogeny W₁ W₂)
    (f : F →+* K) :
    WeierstrassCurve.Affine.FunctionField.mapDifferential W₁ f
        (φ.pullbackDifferential (invariantDifferential W₂)) =
      (φ.map f).pullbackDifferential (invariantDifferential (W₂.map f)) := by
  rw [invariantDifferential_def, invariantDifferential_def]
  simp only [pullbackDifferential_smul, pullbackDifferential_D, map_inv₀,
    (WeierstrassCurve.Affine.FunctionField.mapDifferential W₁ f).map_smulₛₗ,
    WeierstrassCurve.Affine.FunctionField.mapDifferential_D]
  rw [← WeierstrassCurve.Affine.FunctionField.map_invariantDifferentialDenom W₂ f,
    ← WeierstrassCurve.Affine.FunctionField.map_genericX W₂ f,
    map_fieldPullback_map, map_fieldPullback_map]

/-- **Separability is invariant under arbitrary field base change.** An isogeny is separable if
and only if the isogeny obtained by carrying its coefficients along `f : F →+* K` is separable. -/
theorem isSeparable_map_iff [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂)
    (f : F →+* K) :
    Algebra.IsSeparable (φ.map f).fieldPullback.fieldRange (W₁.map f).FunctionField ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField := by
  rw [isSeparable_iff_pullbackDifferential_ne_zero,
    isSeparable_iff_pullbackDifferential_ne_zero,
    ← mapDifferential_pullback_invariantDifferential]
  exact not_congr
    (WeierstrassCurve.Affine.FunctionField.mapDifferential_eq_zero_iff W₁ f _)

/-- A separable isogeny stays separable after field base change. -/
theorem isSeparable_map [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂)
    (f : F →+* K) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    Algebra.IsSeparable (φ.map f).fieldPullback.fieldRange (W₁.map f).FunctionField :=
  (isSeparable_map_iff φ f).2 inferInstance

/-- Separability descends from any field base change. -/
theorem isSeparable_of_map [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂)
    (f : F →+* K)
    [Algebra.IsSeparable (φ.map f).fieldPullback.fieldRange (W₁.map f).FunctionField] :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField :=
  (isSeparable_map_iff φ f).1 inferInstance

end Isogeny

end TauCeti

end
