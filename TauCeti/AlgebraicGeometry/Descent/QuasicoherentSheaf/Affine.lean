/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Affine
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Basic

/-!
# Faithfully flat descent of quasi-coherent modules on affine schemes

Let `φ : R ⟶ S` be a faithfully flat map of commutative rings. Mathlib shows that extension of
scalars `ModuleCat R ⥤ ModuleCat S` is comonadic (`comonadicExtendScalars`): an `R`-module is
the same as an `S`-module `N` with a coassociative and counital `S`-linear coaction
`N → S ⊗[R] N`. This file transports that statement to quasi-coherent modules: pullback along
`Spec φ : Spec S ⟶ Spec R` is comonadic as a functor
`QuasicoherentSheaf (Spec R) ⥤ QuasicoherentSheaf (Spec S)`, with right adjoint the pushforward
`QuasicoherentSheaf.pushforwardSpecMap φ`.

Comonadicity is the affine case of faithfully flat descent for quasi-coherent modules: a
coalgebra for the comonad `(Spec φ)^* (Spec φ)_*` on quasi-coherent modules on `Spec S` is the
sheaf form of an `S`-module with a coaction as above, and every such coalgebra comes, uniquely
up to unique isomorphism, from a quasi-coherent module on `Spec R`.

The transport goes through Mathlib's equivalence `tildeEquiv` between `R`-modules and
quasi-coherent modules on `Spec R`, under which pullback along `Spec φ` is extension of scalars
along `φ` (`tildeEquivFunctorCompPullbackIso`, the quasi-coherent form of
`TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso`). So pullback along `Spec φ` preserves
finite limits when `φ` is flat and reflects isomorphisms when `φ` is faithfully flat, and Beck's
comonadicity theorem applies.

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.comonadicPullbackSpecMap`: for faithfully flat
  `φ`, pullback of quasi-coherent modules along `Spec φ` is comonadic;
  `isEquivalence_comparison_pullbackPushforwardSpecMapAdjunction` states this for the
  comparison functor of `pullbackPushforwardSpecMapAdjunction φ`.

## References

* The Stacks Project, Section 35.3, descent for modules along faithfully flat ring maps, and
  Proposition 35.5.2 (023T), descent of quasi-coherent modules along fpqc coverings.
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 1.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.QuasicoherentSheaf

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- **Faithfully flat descent for quasi-coherent modules on affine schemes.** For a faithfully
flat ring map `φ : R ⟶ S`, pullback of quasi-coherent modules along `Spec φ` is comonadic, with
right adjoint `pushforwardSpecMap φ`: the comparison functor from quasi-coherent modules on
`Spec R` to coalgebras for the comonad `(Spec φ)^* (Spec φ)_*` is an equivalence. This is
Mathlib's `comonadicExtendScalars` transported along `tildeEquiv`. -/
@[instance_reducible]
def comonadicPullbackSpecMap (hφ : φ.hom.FaithfullyFlat) :
    ComonadicLeftAdjoint (pullback (Spec.map φ)) := by
  -- Pullback along `Spec φ` is extension of scalars, conjugated by `tildeEquiv`.
  let e : (tildeEquiv (R := R)).inverse ⋙ ModuleCat.extendScalars φ.hom ⋙
      (tildeEquiv (R := S)).functor ≅ pullback (Spec.map φ) :=
    Functor.isoWhiskerLeft _ (tildeEquivFunctorCompPullbackIso φ).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (tildeEquiv (R := R)).counitIso _ ≪≫ Functor.leftUnitor _
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ.flat
  have := ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hφ
  have : PreservesFiniteLimits (pullback (Spec.map φ)) := preservesFiniteLimits_of_natIso e
  have : (pullback (Spec.map φ)).ReflectsIsomorphisms := reflectsIsomorphisms_of_iso e
  have : Comonad.HasEqualizerOfIsCosplitPair (pullback (Spec.map φ)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : Comonad.PreservesLimitOfIsCosplitPair (pullback (Spec.map φ)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
    (pullbackPushforwardSpecMapAdjunction φ)

/-- For a faithfully flat ring map `φ`, the comparison functor from quasi-coherent modules on
`Spec R` to coalgebras for the comonad of the adjunction
`pullbackPushforwardSpecMapAdjunction φ` is an equivalence. -/
theorem isEquivalence_comparison_pullbackPushforwardSpecMapAdjunction
    (hφ : φ.hom.FaithfullyFlat) :
    (Comonad.comparison (pullbackPushforwardSpecMapAdjunction φ)).IsEquivalence :=
  (comonadicPullbackSpecMap φ hφ).eqv

end

end TauCeti.AlgebraicGeometry.QuasicoherentSheaf
