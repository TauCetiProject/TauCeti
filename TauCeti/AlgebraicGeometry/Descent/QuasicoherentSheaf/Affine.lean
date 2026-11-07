/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Basic
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
  comparison functor of `pullbackPushforwardSpecMapAdjunction φ`;
* `TauCeti.AlgebraicGeometry.Descent.qcohPseudofunctorMapSpecMapAdjunction` and
  `isEquivalence_comparison_qcohPseudofunctorMapSpecMapAdjunction`: the same adjunction and
  comonadicity for the functor `qcohPseudofunctor.map` along `Spec φ`, the form of pullback in
  which descent data are stated.

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
  have := preservesFiniteLimits_pullback_specMap φ hφ.flat
  have := reflectsIsomorphisms_pullback_specMap φ hφ
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

namespace TauCeti.AlgebraicGeometry.Descent

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The adjunction between pullback along `Spec φ` in the form of the functor
`qcohPseudofunctor.map`, in which descent data are stated, and `pushforwardSpecMap φ`. Its unit and
counit are those of `Scheme.Modules.pullbackPushforwardAdjunction` on underlying modules by
definition. The functor equals `QuasicoherentSheaf.pullback (Spec.map φ)` only propositionally
(`qcohPseudofunctor_map_toFunctor`), so `pullbackPushforwardSpecMapAdjunction` does not apply to it
directly. -/
def qcohPseudofunctorMapSpecMapAdjunction :
    (qcohPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor ⊣
      QuasicoherentSheaf.pushforwardSpecMap φ where
  unit :=
    { app A := ObjectProperty.homMk
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app A.obj)
      naturality _ _ x := ObjectProperty.hom_ext _
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality x.hom) }
  counit :=
    { app B := ObjectProperty.homMk
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app B.obj)
      naturality _ _ x := ObjectProperty.hom_ext _
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.naturality x.hom) }
  left_triangle_components A := ObjectProperty.hom_ext _
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).left_triangle_components A.obj)
  right_triangle_components B := ObjectProperty.hom_ext _
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).right_triangle_components B.obj)

/-- The unit of `qcohPseudofunctorMapSpecMapAdjunction φ` is the unit of the adjunction for
modules. -/
@[simp]
lemma qcohPseudofunctorMapSpecMapAdjunction_unit_app_hom (A : QuasicoherentSheaf (Spec R)) :
    ((qcohPseudofunctorMapSpecMapAdjunction φ).unit.app A).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app A.obj :=
  (rfl)

/-- The counit of `qcohPseudofunctorMapSpecMapAdjunction φ` is the counit of the adjunction for
modules. -/
@[simp]
lemma qcohPseudofunctorMapSpecMapAdjunction_counit_app_hom (B : QuasicoherentSheaf (Spec S)) :
    ((qcohPseudofunctorMapSpecMapAdjunction φ).counit.app B).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app B.obj :=
  (rfl)

/-- For a faithfully flat ring map `φ`, the comparison functor from quasi-coherent modules on
`Spec R` to coalgebras for the comonad of `qcohPseudofunctorMapSpecMapAdjunction φ` is an
equivalence: Beck's comonadicity theorem applies as in
`QuasicoherentSheaf.comonadicPullbackSpecMap`. -/
theorem isEquivalence_comparison_qcohPseudofunctorMapSpecMapAdjunction
    (hφ : φ.hom.FaithfullyFlat) :
    (Comonad.comparison (qcohPseudofunctorMapSpecMapAdjunction φ)).IsEquivalence := by
  have hL := qcohPseudofunctor_map_toFunctor (Spec.map φ).op.toLoc
  -- The categories of `qcohPseudofunctor` are `QuasicoherentSheaf` only up to unfolding, which
  -- instance search does not see.
  have : HasEqualizers (qcohPseudofunctor.obj ⟨.op (Spec R)⟩) :=
    inferInstanceAs (HasEqualizers (QuasicoherentSheaf (Spec R)))
  have : PreservesFiniteLimits (qcohPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor :=
    hL ▸ QuasicoherentSheaf.preservesFiniteLimits_pullback_specMap φ hφ.flat
  have : (qcohPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor.ReflectsIsomorphisms :=
    hL ▸ QuasicoherentSheaf.reflectsIsomorphisms_pullback_specMap φ hφ
  have : Comonad.HasEqualizerOfIsCosplitPair
      (qcohPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : Comonad.PreservesLimitOfIsCosplitPair
      (qcohPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact (Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
    (qcohPseudofunctorMapSpecMapAdjunction φ)).eqv

end

end TauCeti.AlgebraicGeometry.Descent
