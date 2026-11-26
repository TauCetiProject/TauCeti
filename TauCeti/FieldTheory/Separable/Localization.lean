/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.Basic

/-!
# Transport of separability across localizations

Let `B` be an `A`-algebra, let `K₁` and `K₂` be field localizations of `A` at the same submonoid
`M`, and let `L₁` and `L₂` be localizations of `B` at the same submonoid `N`, forming compatible
squares `A → Kᵢ → Lᵢ` and `A → B → Lᵢ`. The canonical localization isomorphisms `K₁ ≃ₐ[A] K₂` and
`L₁ ≃ₐ[B] L₂` commute with `algebraMap Kᵢ Lᵢ` by uniqueness of ring homomorphisms out of `K₁`, so
separability of `L₁ / K₁` transports to `L₂ / K₂` (`Algebra.IsSeparable.of_isLocalization`,
`Algebra.IsSeparable.iff_of_isLocalization`).

In particular, taking `M = A⁰` and `N = B⁰` transports separability between any chosen fraction
fields `K` of `A` and `L` of `B` and the canonical fraction fields `FractionRing A` and
`FractionRing B`.

## Main results

* `Algebra.IsSeparable.of_isLocalization`: separability transports between pairs of localizations
  at the same submonoids.
* `Algebra.IsSeparable.iff_of_isLocalization`: separability of `L₁ / K₁` is equivalent to
  separability of `L₂ / K₂`.
-/

public section

namespace Algebra.IsSeparable

variable {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B]

/-- Separability transports between pairs of localizations `(K₁, L₁)` and `(K₂, L₂)` of `A` at `M`
and `B` at `N` whose algebra maps form commuting squares with `A → B`. In particular, for `M = A⁰`
and `N = B⁰`, separability of an extension `L / K` of abstract fraction fields of `A` and `B` gives
`Algebra.IsSeparable (FractionRing A) (FractionRing B)`. -/
theorem of_isLocalization (M : Submonoid A) (N : Submonoid B) (K₁ L₁ : Type*) {K₂ L₂ : Type*}
    [Field K₁] [Field K₂] [CommRing L₁] [CommRing L₂]
    [Algebra A K₁] [Algebra A K₂] [IsLocalization M K₁] [IsLocalization M K₂]
    [Algebra B L₁] [Algebra B L₂] [IsLocalization N L₁] [IsLocalization N L₂]
    [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra A L₁] [Algebra A L₂]
    [IsScalarTower A K₁ L₁] [IsScalarTower A K₂ L₂]
    [IsScalarTower A B L₁] [IsScalarTower A B L₂]
    [Algebra.IsSeparable K₁ L₁] :
    Algebra.IsSeparable K₂ L₂ := by
  refine of_equiv_equiv (IsLocalization.algEquiv M K₁ K₂).toRingEquiv
    (IsLocalization.algEquiv N L₁ L₂).toRingEquiv ?_
  apply IsLocalization.ringHom_ext M
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply A B L₁, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

/-- Separability is invariant between pairs of localizations `(K₁, L₁)` and `(K₂, L₂)` of `A` at
`M` and `B` at `N` whose algebra maps form commuting squares with `A → B`. -/
theorem iff_of_isLocalization (M : Submonoid A) (N : Submonoid B) (K₁ L₁ K₂ L₂ : Type*)
    [Field K₁] [Field K₂] [CommRing L₁] [CommRing L₂]
    [Algebra A K₁] [Algebra A K₂] [IsLocalization M K₁] [IsLocalization M K₂]
    [Algebra B L₁] [Algebra B L₂] [IsLocalization N L₁] [IsLocalization N L₂]
    [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra A L₁] [Algebra A L₂]
    [IsScalarTower A K₁ L₁] [IsScalarTower A K₂ L₂]
    [IsScalarTower A B L₁] [IsScalarTower A B L₂] :
    Algebra.IsSeparable K₁ L₁ ↔ Algebra.IsSeparable K₂ L₂ :=
  ⟨fun _ ↦ of_isLocalization M N K₁ L₁, fun _ ↦ of_isLocalization M N K₂ L₂⟩

end Algebra.IsSeparable

end
