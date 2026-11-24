/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Coalgebra
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

Combined with the passage from descent data to coalgebras
(`TauCeti.AlgebraicGeometry.Descent.qcohDescentDataToCoalgebra`, the Bénabou–Roubaud comparison),
this gives effective descent along `Spec φ`. For flat `φ`, the coaction of a descent datum along
`Spec φ` is a morphism of quasi-coherent modules, so descent data are coalgebras for the comonad
`(Spec φ)^* (Spec φ)_*` on `QCoh(Spec S)`, fully faithfully. On the descent datum of a pullback
this is Beck's comparison coalgebra, so for faithfully flat `φ` every coalgebra comes from a descent
datum and descent data along `Spec φ` are equivalent to quasi-coherent modules on `Spec R`.

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.comonadicPullbackSpecMap`: for faithfully flat
  `φ`, pullback of quasi-coherent modules along `Spec φ` is comonadic;
  `isEquivalence_comparison_pullbackPushforwardSpecMapAdjunction` states this for the
  comparison functor of `pullbackPushforwardSpecMapAdjunction φ`;
* `TauCeti.AlgebraicGeometry.Descent.qcohPseudofunctorMapSpecMapAdjunction` and
  `isEquivalence_comparison_qcohPseudofunctorMapSpecMapAdjunction`: the same adjunction and
  comonadicity for the functor `qcohPseudofunctor.map` along `Spec φ`, the form of pullback in
  which descent data are stated;
* `TauCeti.AlgebraicGeometry.Descent.qcohDescentDataToCoalgebraSpecMap`: descent data along
  `Spec φ` as coalgebras for this comonad, an equivalence for faithfully flat `φ`
  (`isEquivalence_qcohDescentDataToCoalgebraSpecMap`);
* `TauCeti.AlgebraicGeometry.Descent.isEquivalence_toDescentData_specMap`: for faithfully flat
  `φ`, quasi-coherent modules on `Spec R` are equivalent to descent data along `Spec φ`, so these
  descent data are effective.

## References

* The Stacks Project, Section 35.3, descent for modules along faithfully flat ring maps, and
  Proposition 35.5.2 (023T), descent of quasi-coherent modules along fpqc coverings.
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 1.1.
* J. Bénabou, J. Roubaud, *Monades et descente*, C. R. Acad. Sci. Paris Sér. A-B 270 (1970),
  A96–A98.
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

section Coalgebra

open _root_.AlgebraicGeometry

variable [Flat (Spec.map φ)]

/-- **Descent data along `Spec φ` as coalgebras of quasi-coherent modules.** For a flat ring map
`φ : R ⟶ S`, the coaction `qcohDescentDataCoaction` of a descent datum for quasi-coherent modules
along `Spec φ : Spec S ⟶ Spec R` is a morphism of quasi-coherent modules, so the descent datum is a
coalgebra for the comonad of `qcohPseudofunctorMapSpecMapAdjunction φ` on `QCoh(Spec S)`, the
comonad of Beck's comparison in `isEquivalence_comparison_qcohPseudofunctorMapSpecMapAdjunction`.
This is `qcohDescentDataToCoalgebra (Spec.map φ)` read in quasi-coherent modules. -/
@[expose, simps]
def qcohDescentDataToCoalgebraSpecMap :
    qcohPseudofunctor.DescentData (fun _ : PUnit ↦ Spec.map φ) ⥤
      (qcohPseudofunctorMapSpecMapAdjunction φ).toComonad.Coalgebra where
  obj D :=
    { A := D.obj PUnit.unit
      a := ObjectProperty.homMk (qcohDescentDataCoaction (Spec.map φ) D)
      counit := ObjectProperty.hom_ext _
        ((congrArg (qcohDescentDataCoaction (Spec.map φ) D ≫ ·)
          (qcohPseudofunctorMapSpecMapAdjunction_counit_app_hom φ _)).trans
            qcohDescentDataCoaction_counit)
      coassoc := ObjectProperty.hom_ext _
        ((congrArg (qcohDescentDataCoaction (Spec.map φ) D ≫ (Scheme.Modules.pullback _).map ·)
          (qcohPseudofunctorMapSpecMapAdjunction_unit_app_hom φ _)).trans
            qcohDescentDataCoaction_coassoc.symm) }
  map ψ :=
    { f := ψ.hom PUnit.unit
      h := ObjectProperty.hom_ext _ (qcohDescentDataCoaction_comp_map ψ) }

/-- The functor `qcohDescentDataToCoalgebraSpecMap φ` is fully faithful, as
`qcohDescentDataToCoalgebra (Spec.map φ)` is (`fullyFaithfulQcohDescentDataToCoalgebra`). -/
def fullyFaithfulQcohDescentDataToCoalgebraSpecMap :
    (qcohDescentDataToCoalgebraSpecMap φ).FullyFaithful where
  preimage g := (fullyFaithfulQcohDescentDataToCoalgebra (Spec.map φ)).preimage
    { f := g.f.hom
      h := congrArg (·.hom) g.h }
  map_preimage _ := Comonad.Coalgebra.Hom.ext (ObjectProperty.hom_ext _
    (congrArg Comonad.Coalgebra.Hom.f
      ((fullyFaithfulQcohDescentDataToCoalgebra (Spec.map φ)).map_preimage _)))
  preimage_map ψ := (fullyFaithfulQcohDescentDataToCoalgebra (Spec.map φ)).preimage_map ψ

/-- On the descent datum of the pullback of a quasi-coherent module `M` on `Spec R`, the coaction
of `qcohDescentDataToCoalgebraSpecMap φ` is the coaction of Beck's comparison coalgebra of `M`, the
pullback of the unit `M ⟶ (Spec φ)_* (Spec φ)^* M` (`qcohDescentDataCoaction_ofObj`). -/
lemma qcohDescentDataToCoalgebraSpecMap_obj_ofObj_a (M : QuasicoherentSheaf (Spec R)) :
    ((qcohDescentDataToCoalgebraSpecMap φ).obj (.ofObj M)).a =
      ((Comonad.comparison (qcohPseudofunctorMapSpecMapAdjunction φ)).obj M).a := by
  have : M.obj.IsQuasicoherent := M.property
  refine ObjectProperty.hom_ext _ ((qcohDescentDataCoaction_ofObj M).trans ?_)
  exact congrArg (Scheme.Modules.pullback (Spec.map φ)).map
    (qcohPseudofunctorMapSpecMapAdjunction_unit_app_hom φ M).symm

/-- On the descent datum of the pullback of a quasi-coherent module `M` on `Spec R`, the coalgebra
`qcohDescentDataToCoalgebraSpecMap φ` is the coalgebra that Beck's comparison functor of
`qcohPseudofunctorMapSpecMapAdjunction φ` attaches to `M`. -/
def toDescentDataCompQcohDescentDataToCoalgebraSpecMapIso :
    qcohPseudofunctor.toDescentData (fun _ : PUnit ↦ Spec.map φ) ⋙
        qcohDescentDataToCoalgebraSpecMap φ ≅
      Comonad.comparison (qcohPseudofunctorMapSpecMapAdjunction φ) :=
  NatIso.ofComponents
    (fun M ↦ Comonad.Coalgebra.isoMk (Iso.refl _) (by
      -- The two coactions agree. As `qcohPseudofunctor.obj T` is `QuasicoherentSheaf T` only up
      -- to unfolding, `simp` removes `T.map (𝟙 _)` only for a general comonad `T`.
      have key {C : Type (u + 1)} [Category.{u} C] (T : Comonad C) {A : C}
          (a b : A ⟶ T.obj A) (h : a = b) : a ≫ T.map (Iso.refl A).hom = (Iso.refl A).hom ≫ b := by
        simp [h]
      exact key _ _ _ (qcohDescentDataToCoalgebraSpecMap_obj_ofObj_a φ M)))
    (fun _ ↦ Comonad.Coalgebra.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

variable [Surjective (Spec.map φ)]

/-- **Faithfully flat descent data are coalgebras.** For a flat ring map `φ : R ⟶ S` with
`Spec φ` surjective, that is, for `φ` faithfully flat, descent data for quasi-coherent modules along
`Spec φ : Spec S ⟶ Spec R` are equivalent to coalgebras for the comonad `(Spec φ)^* (Spec φ)_*` on
`QCoh(Spec S)`. This is the sheaf form of the description of descent data on an `S`-module as a
coassociative and counital coaction `N → S ⊗[R] N`. -/
theorem isEquivalence_qcohDescentDataToCoalgebraSpecMap :
    (qcohDescentDataToCoalgebraSpecMap φ).IsEquivalence := by
  have := isEquivalence_comparison_qcohPseudofunctorMapSpecMapAdjunction φ
    ((flat_and_surjective_SpecMap_iff φ).1 ⟨‹_›, ‹_›⟩)
  have hK := fullyFaithfulQcohDescentDataToCoalgebraSpecMap φ
  have := hK.full
  have := hK.faithful
  -- Every coalgebra is Beck's comparison coalgebra of a quasi-coherent module on `Spec R`, which
  -- is the coalgebra of the descent datum of its pullback.
  have : (qcohDescentDataToCoalgebraSpecMap φ).EssSurj := ⟨fun C ↦
    ⟨_, ⟨(toDescentDataCompQcohDescentDataToCoalgebraSpecMapIso φ).app _ ≪≫
      (Comonad.comparison (qcohPseudofunctorMapSpecMapAdjunction φ)).objObjPreimageIso C⟩⟩⟩
  exact { }

/-- **Faithfully flat descent of quasi-coherent modules on affine schemes.** For a flat ring map
`φ : R ⟶ S` with `Spec φ` surjective, that is, for `φ` faithfully flat, the functor from
quasi-coherent modules on `Spec R` to descent data for quasi-coherent modules along
`Spec φ : Spec S ⟶ Spec R` is an equivalence: descent data along `Spec φ` are effective and
morphisms descend. -/
theorem isEquivalence_toDescentData_specMap :
    (qcohPseudofunctor.toDescentData (fun _ : PUnit ↦ Spec.map φ)).IsEquivalence := by
  have := isEquivalence_comparison_qcohPseudofunctorMapSpecMapAdjunction φ
    ((flat_and_surjective_SpecMap_iff φ).1 ⟨‹_›, ‹_›⟩)
  have := isEquivalence_qcohDescentDataToCoalgebraSpecMap φ
  have :=
    Functor.isEquivalence_of_iso (toDescentDataCompQcohDescentDataToCoalgebraSpecMapIso φ).symm
  exact Functor.isEquivalence_of_comp_right _ (qcohDescentDataToCoalgebraSpecMap φ)

end Coalgebra

end

end TauCeti.AlgebraicGeometry.Descent
