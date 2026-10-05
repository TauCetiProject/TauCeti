/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Syntomic.Localization
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Standard syntomic ring homomorphisms

This file expresses standard syntomic algebras as a property of ring homomorphisms.
Localization on either side and arbitrary base change preserve the relative dimension.
Consequently the property of being locally standard syntomic is local on both source and
base, giving the affine input for syntomic morphisms of schemes.

Use `TauCeti.IsStandardSyntomicOfRelativeDimension n f` for the ring-map predicate;
given a proof `hf`, its consequences are available as `hf.flat` and `hf.finitePresentation`.
The theorem `TauCeti.isStandardSyntomicOfRelativeDimension_iff n f` relates an arbitrary
ring map to its induced algebra structure. With `hf` as above, both conversions use the
public bridge:

```lean
have hAlg := (TauCeti.isStandardSyntomicOfRelativeDimension_iff n f).mp hf
have hRing := (TauCeti.isStandardSyntomicOfRelativeDimension_iff n f).mpr hAlg
```

The relative dimension is the first explicit argument, as in
`RingHom.IsStandardSmoothOfRelativeDimension`.

For example, the proof methods supply both ring-map consequences:

```lean
example (n : ℕ) {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : TauCeti.IsStandardSyntomicOfRelativeDimension n f) :
    f.Flat ∧ f.FinitePresentation := by
  exact ⟨hf.flat, hf.finitePresentation⟩
```

The ring-homomorphism bridge follows Mathlib's `RingHom.IsStandardSmoothOfRelativeDimension`
in `Mathlib/RingTheory/RingHom/StandardSmooth.lean`, by Christian Merten. The underlying
complete-intersection definition follows the Stacks Project, *Syntomic morphisms*.
-/

public section

namespace TauCeti

universe u v

/-- A ring homomorphism is standard syntomic of relative dimension `n` if its target,
with the algebra structure induced by the homomorphism, is such an algebra. -/
def IsStandardSyntomicOfRelativeDimension (n : ℕ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.IsStandardSyntomicOfRelativeDimension n R S _ _ f.toAlgebra

variable {n : ℕ} {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring map is standard syntomic of relative dimension `n` exactly when its target
is standard syntomic for the induced algebra structure. -/
theorem isStandardSyntomicOfRelativeDimension_iff (n : ℕ) (f : R →+* S) :
    IsStandardSyntomicOfRelativeDimension n f ↔
      @Algebra.IsStandardSyntomicOfRelativeDimension n R S _ _ f.toAlgebra := (Iff.rfl)

/-- The ring-homomorphism and algebra formulations agree on an algebra map. -/
@[simp]
theorem isStandardSyntomicOfRelativeDimension_algebraMap [Algebra R S] :
    IsStandardSyntomicOfRelativeDimension n (algebraMap R S) ↔
      Algebra.IsStandardSyntomicOfRelativeDimension n R S := by
  rw [isStandardSyntomicOfRelativeDimension_iff n, toAlgebra_algebraMap]

variable (R) in
/-- The identity ring map is standard syntomic of relative dimension zero. -/
theorem IsStandardSyntomicOfRelativeDimension.id :
    IsStandardSyntomicOfRelativeDimension 0 (RingHom.id R) := by
  rw [isStandardSyntomicOfRelativeDimension_iff 0]
  have : Algebra.IsStandardSyntomicOfRelativeDimension 0 R (MvPolynomial (Fin 0) R) :=
    inferInstance
  exact Algebra.IsStandardSyntomicOfRelativeDimension.of_algEquiv
    (MvPolynomial.isEmptyAlgEquiv R (Fin 0))

/-- Standard syntomic ring maps are flat. -/
theorem IsStandardSyntomicOfRelativeDimension.flat {f : R →+* S}
    (hf : IsStandardSyntomicOfRelativeDimension n f) : f.Flat :=
  Algebra.IsStandardSyntomicOfRelativeDimension.flat
    (self := (isStandardSyntomicOfRelativeDimension_iff n f).mp hf)

/-- Standard syntomic ring maps are finitely presented. -/
theorem IsStandardSyntomicOfRelativeDimension.finitePresentation {f : R →+* S}
    (hf : IsStandardSyntomicOfRelativeDimension n f) : f.FinitePresentation := by
  let := f.toAlgebra
  exact Algebra.IsStandardSyntomicOfRelativeDimension.finitePresentation
    (h := (isStandardSyntomicOfRelativeDimension_iff n f).mp hf)

/-- Localizing either side of a standard syntomic map preserves its relative dimension. -/
theorem isStandardSyntomicOfRelativeDimension_stableUnderCompositionWithLocalizationAway
    (n : ℕ) : RingHom.StableUnderCompositionWithLocalizationAway
      (@IsStandardSyntomicOfRelativeDimension n) where
  left R S T _ _ _ _ r _ f hf := by
    let := f.toAlgebra
    let := (f.comp (algebraMap R S)).toAlgebra
    have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
    exact Algebra.IsStandardSyntomicOfRelativeDimension.localization_away_trans r
      (h := (isStandardSyntomicOfRelativeDimension_iff n f).mp hf)
  right R S T _ _ _ _ s _ f hf := by
    let := f.toAlgebra
    let := ((algebraMap S T).comp f).toAlgebra
    have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
    exact Algebra.IsStandardSyntomicOfRelativeDimension.trans_localization_away s
      (h := (isStandardSyntomicOfRelativeDimension_iff n f).mp hf)

/-- Standard syntomic ring maps are invariant under isomorphisms on either side. -/
theorem isStandardSyntomicOfRelativeDimension_respectsIso (n : ℕ) :
    RingHom.RespectsIso (@IsStandardSyntomicOfRelativeDimension n) :=
  (isStandardSyntomicOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).respectsIso

/-- Arbitrary base change preserves standard syntomic ring maps and their relative dimension. -/
theorem isStandardSyntomicOfRelativeDimension_isStableUnderBaseChange (n : ℕ) :
    RingHom.IsStableUnderBaseChange (@IsStandardSyntomicOfRelativeDimension n) := by
  apply RingHom.IsStableUnderBaseChange.mk
  · exact isStandardSyntomicOfRelativeDimension_respectsIso n
  · intro R S T _ _ _ _ _ h
    have : Algebra.IsStandardSyntomicOfRelativeDimension n R T :=
      isStandardSyntomicOfRelativeDimension_algebraMap.mp h
    exact isStandardSyntomicOfRelativeDimension_algebraMap.mpr inferInstance

/-- Being locally standard syntomic of fixed relative dimension is local on source and base. -/
theorem locally_isStandardSyntomicOfRelativeDimension_propertyIsLocal (n : ℕ) :
    RingHom.PropertyIsLocal
      (RingHom.Locally (@IsStandardSyntomicOfRelativeDimension n)) :=
  RingHom.locally_propertyIsLocal
    (isStandardSyntomicOfRelativeDimension_isStableUnderBaseChange n).localizationPreserves.away
    (isStandardSyntomicOfRelativeDimension_stableUnderCompositionWithLocalizationAway n)

end TauCeti
