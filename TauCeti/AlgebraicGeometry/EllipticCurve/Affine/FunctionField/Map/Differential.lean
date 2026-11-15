/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential

/-!
# Kähler differentials of a Weierstrass function field under base change

For a field homomorphism `f : F →+* K`, the embedding `FunctionField.map W f : F(W) → K(W.map f)`
and `f` form a commuting square, so Mathlib's functorial map on Kähler differentials gives a
semilinear map

```text
  Ω[F(W)/F] ──▸ Ω[K(W.map f)/K].
```

It sends the invariant differential of `W` to that of `W.map f`. Since the invariant differential
is a basis, this map reflects zero.

## Main definitions

* `WeierstrassCurve.Affine.FunctionField.mapDifferential`: the semilinear map on differentials
  induced by base change of a Weierstrass function field.

## Main results

* `WeierstrassCurve.Affine.FunctionField.mapDifferential_D`: it sends `d z` to `d` of the image
  of `z`.
* `WeierstrassCurve.Affine.FunctionField.mapDifferential_invariantDifferential`: base change carries
  the invariant differential to the invariant differential.
* `WeierstrassCurve.Affine.FunctionField.mapDifferential_eq_zero_iff`: for an elliptic curve,
  base change of differentials reflects zero.

No material is copied from an external formalisation.
-/

public section

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
        -- `KaehlerDifferential.map` is `F(W)`-linear for the action on the target restricted
        -- along the local algebra structure, whose `algebraMap` is `FunctionField.map W f`.
        rw [LinearMap.map_smul, ← IsScalarTower.algebraMap_smul (W.map f).FunctionField c,
          RingHom.algebraMap_toAlgebra] }

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

end
