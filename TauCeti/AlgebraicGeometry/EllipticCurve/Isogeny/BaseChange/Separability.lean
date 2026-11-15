/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential

/-!
# Separability of isogenies under base change

An isogeny of elliptic curves is separable if and only if any base change of it is separable.
This file proves that compatibility without first comparing the degrees of the original and
base-changed function-field extensions. Instead it uses the differential criterion: an isogeny is
separable exactly when the pullback of the invariant differential is nonzero.

For a field homomorphism `f : F →+* K`, the semilinear map on Kähler differentials
`WeierstrassCurve.Affine.FunctionField.mapDifferential : Ω[F(W)/F] → Ω[K(W.map f)/K]` sends the
invariant differential to the invariant differential and reflects zero. The commuting square
`Isogeny.map_fieldPullback_map` then shows that it intertwines pullback by an isogeny with pullback
by its base change.

## Main results

* `TauCeti.Isogeny.mapDifferential_pullback_invariantDifferential`: base change commutes with the
  pullback of the invariant differential.
* `TauCeti.Isogeny.map_pullbackDifferential_invariantDifferential_eq_smul`: if `φ^*ω₂ = c ω₁`, the
  base change of `φ` along `f` pulls the invariant differential back to `f c` times it.
* `TauCeti.Isogeny.isSeparable_map_iff`: an isogeny is separable if and only if its base change is.
* `TauCeti.Isogeny.isSeparable_baseChange`: the base change `φ.baseChange K` of a separable
  isogeny is separable, as an instance.

No material is copied from an external formalisation.
-/

public section

open WeierstrassCurve.Affine

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

/-- **The constant of an isogeny under field base change**: if `φ^*ω₂ = c ω₁` for a constant
`c ∈ F`, then the base change of `φ` along `f : F →+* K` pulls the invariant differential back to
`f c` times the invariant differential. -/
theorem map_pullbackDifferential_invariantDifferential_eq_smul (φ : Isogeny W₁ W₂)
    (f : F →+* K) {c : F}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    (φ.map f).pullbackDifferential (invariantDifferential (W₂.map f)) =
      f c • invariantDifferential (W₁.map f) := by
  rw [← mapDifferential_pullback_invariantDifferential, hc,
    ← algebraMap_smul W₁.FunctionField c, (FunctionField.mapDifferential W₁ f).map_smulₛₗ,
    FunctionField.mapDifferential_invariantDifferential, FunctionField.map_algebraMap,
    algebraMap_smul]

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

open WeierstrassCurve in
/-- The base change of a separable isogeny is separable. -/
instance isSeparable_baseChange [Algebra F K] {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic]
    [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    Algebra.IsSeparable (φ.baseChange K).fieldPullback.fieldRange (W₁⁄K).toAffine.FunctionField :=
  isSeparable_map φ (algebraMap F K)

end Isogeny

end TauCeti

end
