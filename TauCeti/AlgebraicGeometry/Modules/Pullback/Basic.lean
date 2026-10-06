/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Refinement
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.CategoryTheory.Adjunction.Mates

/-!
# Pullback and restriction of modules on schemes

Mathlib packages pullback of modules along scheme morphisms as a pseudofunctor
(`AlgebraicGeometry.Scheme.Modules.pseudofunctor`), whose coherence conditions are equations of
natural transformations. This file records them on components, in the forms used to compare
iterated pullbacks of a single module, and shows that pullback preserves the structure sheaf
`𝒪` compatibly with identities and composition.

For a scheme morphism `f : X ⟶ Y` and an open `V ⊆ Y`, restricting the pullback `f^* M` to
`f⁻¹ V` agrees with pulling back the restriction `M|_V` along `f ∣_ V`. This compatibility lets
local properties of modules, expressed on open covers, be transported along scheme morphisms.
Being an isomorphism is such a local property: a morphism of modules is an isomorphism exactly
when its pullbacks to the members of an open cover are.

Identifying modules on the slice site at an open `U` with modules on the open subscheme `U`, and
pulling back along an isomorphism of schemes, preserve free modules, so trivializations of a
module by free modules can be moved between slices, open subschemes and open immersions.

Pushforward of modules along a scheme morphism is lax symmetric monoidal, so pullback, its left
adjoint, is oplax monoidal, with unit map the identification `f^* 𝒪_Y ≅ 𝒪_X` and tensor comparison
compatible with symmetry (`pullback_map_braiding_hom_comp_δ`). These structures are compatible
with composition: the composition isomorphism of pullbacks carries the comparison maps of
`(f ≫ g)^*` to the composites of those of `g^*` and `f^*`.

Pullback along any scheme morphism preserves quasi-coherence, finite type, finite presentation
and local freeness of modules. Local generators and presentations on an open cover pull back to
local data on the preimage cover.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity_app`,
  `AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality_app` and
  `AlgebraicGeometry.Scheme.Modules.pseudofunctor_right_unitality_app`: the coherence conditions
  of the pullback pseudofunctor, on components;
* `AlgebraicGeometry.Scheme.Modules.pullbackObjUnitIso`: the isomorphism `f^* 𝒪_Y ≅ 𝒪_X`, with
  `pullbackObjUnitIso_id`, `pullbackObjUnitIso_comp`, and `pullbackObjUnitIso_congr` comparing it
  with identity, composition, and equality of scheme morphisms;
* `AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal` and
  `AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal`: the lax monoidal structure of
  pushforward and the oplax monoidal structure of pullback, with unit maps computed by
  `AlgebraicGeometry.Scheme.Modules.pushforward_ε` and
  `AlgebraicGeometry.Scheme.Modules.pullback_η`, and the tensor map of pullback by
  `AlgebraicGeometry.Scheme.Modules.pullback_δ`;
* `AlgebraicGeometry.Scheme.Modules.isMonoidal_pushforwardComp_hom` and
  `AlgebraicGeometry.Scheme.Modules.pullback_comp_δ`: the composition isomorphisms of pushforward
  and pullback respect the lax and oplax monoidal structures;
* `AlgebraicGeometry.Scheme.Modules.restrictPullbackObjIso` identifies these two restricted
  pullbacks;
* `AlgebraicGeometry.Scheme.Modules.isIso_iff_of_isOpenCover`: a morphism of modules is an
  isomorphism exactly when its pullbacks to the members of an open cover are;
* `AlgebraicGeometry.Scheme.Modules.pullbackOver`: pullback read on the slice sites over `V` and
  `f⁻¹ V`, with `pullbackOverUnitIso` and `pullbackOverObjIso` comparing it with the structure
  sheaves and with the pullback of `𝒪_Y`-modules;
* `AlgebraicGeometry.Scheme.Modules.overEquivFunctorObjFreeIso`: the identification of modules on
  the slice at an open `U` with modules on the open subscheme `U` preserves free modules, so
  trivializations of a module pass between the slice and the open subscheme
  (`AlgebraicGeometry.Scheme.Modules.restrictIsoFreeOfOverIsoFree`,
  `AlgebraicGeometry.Scheme.Modules.overIsoFreeOfRestrictIsoFree`), and a trivialization of the
  pullback along an open immersion `f` is one of the restriction to `f.opensRange`
  (`AlgebraicGeometry.Scheme.Modules.restrictOpensRangeIsoFree`);
* `SheafOfModules.LocalGeneratorsData.pullback` and `SheafOfModules.QuasicoherentData.pullback`:
  local generators and quasi-coherent data carried along `f`;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback`,
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pullback` and
  `AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback`: pullback preserves quasi-coherent,
  finite type, finitely presented and locally free modules.

## References

* The Stacks Project, *Sheaves of Modules*, sections *Quasi-coherent modules*, *Modules of finite
  type*, *Modules of finite presentation* and *Locally free sheaves*.
-/

public section

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe w u

noncomputable section

variable {X Y : Scheme.{u}}

section Coherence

variable {Z W : Scheme.{u}}

/-- The associativity condition of the pullback pseudofunctor, on the component at a module. -/
@[reassoc]
lemma pseudofunctor_associativity_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (pullbackComp f (g ≫ h)).inv.app M ≫ (pullback f).map ((pullbackComp g h).inv.app M) ≫
      (pullbackComp f g).hom.app ((pullback h).obj M) ≫ (pullbackComp (f ≫ g) h).hom.app M =
      eqToHom (by simp) := by
  simpa using NatTrans.congr_app (pseudofunctor_associativity f g h) M

/-- The left unitality condition of the pullback pseudofunctor, on the component at a module. -/
@[reassoc]
lemma pseudofunctor_left_unitality_app (f : X ⟶ Y) (M : Y.Modules) :
    (pullbackComp f (𝟙 Y)).inv.app M ≫ (pullback f).map ((pullbackId Y).hom.app M) =
      eqToHom (by simp) := by
  simpa using NatTrans.congr_app (pseudofunctor_left_unitality f) M

/-- The right unitality condition of the pullback pseudofunctor, on the component at a module. -/
@[reassoc]
lemma pseudofunctor_right_unitality_app (f : X ⟶ Y) (M : Y.Modules) :
    (pullbackComp (𝟙 X) f).inv.app M ≫ (pullbackId X).hom.app ((pullback f).obj M) =
      eqToHom (by simp) := by
  simpa using NatTrans.congr_app (pseudofunctor_right_unitality f) M

/-- The two ways of identifying `f^* g^* h^* M` with `(f ≫ g ≫ h)^* M` agree. -/
@[reassoc]
lemma pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (M : W.Modules) :
    (pullback f).map ((pullbackComp g h).hom.app M) ≫ (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp f g).hom.app ((pullback h).obj M) ≫ (pullbackComp (f ≫ g) h).hom.app M ≫
        eqToHom (by simp) := by
  rw [← cancel_epi ((pullbackComp f (g ≫ h)).inv.app M ≫
    (pullback f).map ((pullbackComp g h).inv.app M))]
  simp only [Category.assoc, pseudofunctor_associativity_app_assoc, eqToHom_trans, eqToHom_refl]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app]

/-- Associativity of pullback, rearranged to pass from `(f ≫ g)^* h^* M` to `f^* (g ≫ h)^* M`. -/
@[reassoc]
lemma pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (M : W.Modules) :
    (pullbackComp f g).inv.app ((pullback h).obj M) ≫
        (pullback f).map ((pullbackComp g h).hom.app M) =
      (pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by simp) ≫
        (pullbackComp f (g ≫ h)).inv.app M := by
  rw [← cancel_epi ((pullbackComp f g).hom.app ((pullback h).obj M)),
    ← cancel_mono ((pullbackComp f (g ≫ h)).hom.app M)]
  simp [pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app]

/-- Associativity of pullback, rearranged to pass from `(f ≫ g ≫ h)^* M` to `f^* g^* h^* M`
through `(f ≫ g)^* h^* M`. -/
@[reassoc]
lemma pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (M : W.Modules) :
    (pullbackComp f (g ≫ h)).inv.app M ≫ (pullback f).map ((pullbackComp g h).inv.app M) =
      eqToHom (by simp) ≫ (pullbackComp (f ≫ g) h).inv.app M ≫
        (pullbackComp f g).inv.app ((pullback h).obj M) := by
  rw [← cancel_mono ((pullbackComp f g).hom.app ((pullback h).obj M) ≫
    (pullbackComp (f ≫ g) h).hom.app M)]
  simp [pseudofunctor_associativity_app]

/-- The composition isomorphism of pullback is compatible with replacing the first morphism by an
equal one. -/
@[reassoc]
lemma pullbackCongr_hom_app_comp_pullbackComp_hom_app {a b : X ⟶ Y} (p : a = b) (f : Y ⟶ Z)
    (M : Z.Modules) :
    (pullbackCongr p).hom.app ((pullback f).obj M) ≫ (pullbackComp b f).hom.app M =
      (pullbackComp a f).hom.app M ≫ eqToHom (by rw [p]) := by
  subst p
  simp [pullbackCongr]

/-- The composition isomorphism of pullback is compatible with replacing the second morphism by
an equal one. -/
@[reassoc]
lemma pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app (f : X ⟶ Y) {a b : Y ⟶ Z}
    (p : a = b) (M : Z.Modules) :
    (pullbackComp f a).inv.app M ≫ (pullback f).map ((pullbackCongr p).hom.app M) =
      eqToHom (by rw [p]) ≫ (pullbackComp f b).inv.app M := by
  subst p
  simp [pullbackCongr]

end Coherence

section Unit

variable {Z : Scheme.{u}}

/-- Pullback along a morphism of schemes preserves the structure sheaf: `f^* 𝒪_Y ≅ 𝒪_X`, the
isomorphism being Mathlib's comparison `SheafOfModules.pullbackObjUnitToUnit`. -/
def pullbackObjUnitIso (f : X ⟶ Y) : (pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  -- Mathlib's invertibility of `pullbackObjUnitToUnit` is stated for pushforwards known to be
  -- right adjoints; the adjunction is recorded for `Scheme.Modules.pushforward`. Instance search
  -- does not find the resulting `IsIso` instance, so it is passed explicitly.
  let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) this

/-- The hom of `pullbackObjUnitIso` is Mathlib's structure sheaf comparison map. -/
@[simp]
lemma pullbackObjUnitIso_hom (f : X ⟶ Y) :
    (pullbackObjUnitIso f).hom =
      (letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
        inferInstanceAs (pushforward f).IsRightAdjoint
       SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := by
  rfl

/-- The transpose of `f^* 𝒪_Y ≅ 𝒪_X` is the map `𝒪_Y ⟶ f_* 𝒪_X` given by `f` on sections. -/
lemma pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom (f : X ⟶ Y) :
    (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackObjUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  Equiv.apply_symm_apply _ _

/-- The map `𝒪_Z ⟶ (f ≫ g)_* 𝒪_X` given by `f ≫ g` on sections is the composite of the maps given
by `g` and by `f`. -/
lemma unitToPushforwardObjUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (pushforward g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (pushforwardComp f g).hom.app _ =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
  -- On each open, `pushforwardComp` is the identity map and the map associated to
  -- `(f ≫ g).toRingCatSheafHom` is the composite of the two maps on sections.
  ext U
  rfl

/-- Along the identity, `𝟙^* 𝒪_X ≅ 𝒪_X` is the identity isomorphism of pullback. -/
lemma pullbackObjUnitIso_id (X : Scheme.{u}) :
    (pullbackObjUnitIso (𝟙 X)).hom = (pullbackId X).hom.app _ := by
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom, Adjunction.homEquiv_unit,
    ← unit_conjugateEquiv Adjunction.id, conjugateEquiv_pullbackId_hom]
  -- On each open, `pushforwardId` and `(𝟙 X).toRingCatSheafHom` act as identities.
  ext U
  rfl

/-- The isomorphism `(f ≫ g)^* 𝒪_Z ≅ 𝒪_X` is the composite of `f^* (g^* 𝒪_Z ≅ 𝒪_Y)` and
`f^* 𝒪_Y ≅ 𝒪_X`, through the composition isomorphism of pullback. -/
@[reassoc]
lemma pullbackObjUnitIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackComp f g).inv.app _ ≫ (pullback f).map (pullbackObjUnitIso g).hom ≫
      (pullbackObjUnitIso f).hom = (pullbackObjUnitIso (f ≫ g)).hom := by
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [← Adjunction.homEquiv_conjugateEquiv ((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f)), conjugateEquiv_pullbackComp_inv,
    Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  -- `rw` cannot rewrite `homEquiv_naturality_right` here: its instance of
  -- `SheafOfModules.unitToPushforwardObjUnit` mentions `X.ringCatSheaf` at a type that is not
  -- unfolded at instance transparency, so the step is applied as a term.
  refine (congrArg (· ≫ (pushforwardComp f g).hom.app _)
    ((pullbackPushforwardAdjunction g).homEquiv_naturality_right _ _)).trans ?_
  rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  exact (Category.assoc _ _ _).trans (unitToPushforwardObjUnit_comp f g)

/-- The canonical identification of a pulled-back structure sheaf is unchanged when the
scheme morphism is replaced by an equal morphism. -/
lemma pullbackObjUnitIso_congr {f g : X ⟶ Y} (hf : f = g) :
    (pullbackCongr hf).hom.app (𝟙_ Y.Modules) ≫ (pullbackObjUnitIso g).hom =
      (pullbackObjUnitIso f).hom := by
  subst g
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]

end Unit

section Monoidal

variable (f : X ⟶ Y)

/-- Pushforward of modules along a morphism of schemes is lax monoidal
(`TauCeti.SheafOfModules.pushforwardLaxMonoidal`): its tensor map `f_* M ⊗ f_* N ⟶ f_* (M ⊗ N)`
is induced by `m ⊗ n ↦ m ⊗ n` on sections, and its unit map `𝒪_Y ⟶ f_* 𝒪_X` is given by `f` on
sections (`pushforward_ε`). -/
instance pushforwardLaxMonoidal : (pushforward f).LaxMonoidal :=
  TauCeti.SheafOfModules.pushforwardLaxMonoidal f.toRingCatSheafHom

/-- Pushforward of modules along a scheme morphism respects the symmetry of tensor products. -/
instance pushforwardLaxBraided : (pushforward f).LaxBraided :=
  TauCeti.SheafOfModules.pushforwardLaxBraided f.toRingCatSheafHom

/-- The unit map `𝒪_Y ⟶ f_* 𝒪_X` of the pushforward of modules is given by `f` on sections. -/
@[simp]
lemma pushforward_ε :
    Functor.LaxMonoidal.ε (pushforward f) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  TauCeti.SheafOfModules.pushforward_ε f.toRingCatSheafHom

/-- Pullback of modules along a morphism of schemes is oplax monoidal, as the left adjoint of the
lax monoidal pushforward: it carries comparison maps `f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N`, and its unit
map is `pullbackObjUnitIso f` (`pullback_η`). The comparison maps are the mates of the tensor
map of pushforward (`pullback_δ`). -/
instance pullbackOplaxMonoidal : (pullback f).OplaxMonoidal :=
  (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal

/-- The pullback--pushforward adjunction of modules along a morphism of schemes is compatible with
the oplax monoidal structure of pullback and the lax monoidal structure of pushforward. -/
instance isMonoidal_pullbackPushforwardAdjunction :
    (pullbackPushforwardAdjunction f).IsMonoidal :=
  inferInstanceAs (letI := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
    (pullbackPushforwardAdjunction f).IsMonoidal)

/-- The unit map `f^* 𝒪_Y ⟶ 𝒪_X` of the pullback of modules is the isomorphism
`pullbackObjUnitIso f`. -/
@[simp]
lemma pullback_η : Functor.OplaxMonoidal.η (pullback f) = (pullbackObjUnitIso f).hom := by
  rw [pullbackOplaxMonoidal, Adjunction.leftAdjointOplaxMonoidal_η, pushforward_ε]
  exact (Equiv.symm_apply_eq _).mpr
    (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f).symm

/-- The tensor map `f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` of the pullback of modules is the mate, under the
pullback--pushforward adjunction, of the composite of the units `M ⟶ f_* f^* M` and
`N ⟶ f_* f^* N` with the tensor map `f_* f^* M ⊗ f_* f^* N ⟶ f_* (f^* M ⊗ f^* N)` of
pushforward. -/
lemma pullback_δ (M N : Y.Modules) :
    Functor.OplaxMonoidal.δ (pullback f) M N =
      ((pullbackPushforwardAdjunction f).homEquiv _ _).symm
        (((pullbackPushforwardAdjunction f).unit.app M ⊗ₘ
            (pullbackPushforwardAdjunction f).unit.app N) ≫
          Functor.LaxMonoidal.μ (pushforward f) _ _) :=
  Adjunction.leftAdjointOplaxMonoidal_δ _ _ _

/-- The canonical tensor comparison of module pullback respects symmetry, without any
flatness, finiteness or quasi-coherence hypothesis. -/
@[reassoc]
lemma pullback_map_braiding_hom_comp_δ (M N : Y.Modules) :
    (pullback f).map (β_ M N).hom ≫ Functor.OplaxMonoidal.δ (pullback f) N M =
      Functor.OplaxMonoidal.δ (pullback f) M N ≫
        (β_ ((pullback f).obj M) ((pullback f).obj N)).hom :=
  (pullbackPushforwardAdjunction f).map_braiding_hom_comp_δ M N

instance : IsIso (Functor.OplaxMonoidal.η (pullback f)) := by
  rw [pullback_η]
  infer_instance

variable {Z : Scheme.{u}} (g : Y ⟶ Z)

/-- The identification `pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g)` is an isomorphism of
lax monoidal functors (`TauCeti.SheafOfModules.isMonoidal_pushforwardComp_hom`). -/
instance isMonoidal_pushforwardComp_hom : NatTrans.IsMonoidal (pushforwardComp f g).hom :=
  TauCeti.SheafOfModules.isMonoidal_pushforwardComp_hom g.toRingCatSheafHom f.toRingCatSheafHom

/-- The tensor map `(f ≫ g)^* (M ⊗ N) ⟶ (f ≫ g)^* M ⊗ (f ≫ g)^* N` of the pullback along a
composite is, through the composition isomorphism `pullbackComp f g`, the composite
`f^* g^* (M ⊗ N) ⟶ f^* (g^* M ⊗ g^* N) ⟶ f^* g^* M ⊗ f^* g^* N` of the tensor maps of the two
pullbacks. With `pullbackObjUnitIso_comp` for the unit maps, this says that `pullbackComp f g` is
an isomorphism of oplax monoidal functors. -/
lemma pullback_comp_δ (M N : Z.Modules) :
    Functor.OplaxMonoidal.δ (pullback (f ≫ g)) M N =
      (pullbackComp f g).inv.app (M ⊗ N) ≫
        (pullback f).map (Functor.OplaxMonoidal.δ (pullback g) M N) ≫
        Functor.OplaxMonoidal.δ (pullback f) _ _ ≫
        ((pullbackComp f g).hom.app M ⊗ₘ (pullbackComp f g).hom.app N) :=
  -- The site-level statement asks for the right adjoints by instance; for schemes they are
  -- recorded on `Scheme.Modules.pushforward`.
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward g).IsRightAdjoint
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  TauCeti.SheafOfModules.pullback_comp_δ g.toRingCatSheafHom f.toRingCatSheafHom M N

end Monoidal

section Over

variable (f : X ⟶ Y)

/-- Pullback commutes with restriction to opens: for an open `V ⊆ Y`, the restriction of
`f^* M` to the preimage `f⁻¹ V` is the pullback of `M|_V` along `f ∣_ V : f⁻¹ V ⟶ V`. -/
def restrictPullbackObjIso (V : Y.Opens) (M : Y.Modules) :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ V).ι ≅ (pullback (f ∣_ V)).obj (M.restrict V.ι) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _ ≪≫ (pullbackComp (f ⁻¹ᵁ V).ι f).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f V).symm).app M ≪≫
    ((pullbackComp (f ∣_ V) V.ι).app M).symm ≪≫
    (pullback (f ∣_ V)).mapIso ((restrictFunctorIsoPullback V.ι).app M).symm

variable (V : Y.Opens)

/-- Pullback along `f` read on slice sites: sheaves of modules over the slice of `Y` at an open
`V` are identified with `𝒪_V`-modules, pulled back along `f ∣_ V : f⁻¹ V ⟶ V`, and read as
sheaves of modules over the slice of `X` at `f⁻¹ V`. -/
-- This composite is a left adjoint, hence preserves colimits. The unit and object isomorphisms
-- below identify its effect on the structure sheaf and on restrictions of modules.
def pullbackOver : SheafOfModules (Y.ringCatSheaf.over V) ⥤
    SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ V)) :=
  (overEquiv V).functor ⋙ pullback (f ∣_ V) ⋙ (overEquiv (f ⁻¹ᵁ V)).inverse

instance : (pullbackOver f V).IsLeftAdjoint := by
  unfold pullbackOver
  infer_instance

/-- Pullback read on slice sites preserves the structure sheaf. -/
def pullbackOverUnitIso :
    SheafOfModules.unit _ ≅ (pullbackOver f V).obj (SheafOfModules.unit _) :=
  (overEquiv (f ⁻¹ᵁ V)).unitIso.app _ ≪≫
    (overEquiv (f ⁻¹ᵁ V)).inverse.mapIso (pullbackObjUnitIso (f ∣_ V)).symm

/-- Pullback read on slice sites computes the restriction of the pullback: it sends `M.over V`
to `(f^* M).over (f⁻¹ V)`. -/
def pullbackOverObjIso (M : Y.Modules) :
    (pullbackOver f V).obj (M.over V) ≅ ((pullback f).obj M).over (f ⁻¹ᵁ V) :=
  ((overEquiv (f ⁻¹ᵁ V)).inverse.mapIso
      ((overFunctorEquiv (f ⁻¹ᵁ V)).app _ ≪≫ restrictPullbackObjIso f V M ≪≫
        (pullback (f ∣_ V)).mapIso ((overFunctorEquiv V).app M).symm)).symm ≪≫
    ((overEquiv (f ⁻¹ᵁ V)).unitIso.app _).symm

/-- A morphism of modules is an isomorphism exactly when its pullbacks to the members of an open
cover are isomorphisms. -/
theorem isIso_iff_of_isOpenCover {ι : Type*} {U : ι → X.Opens}
    (hU : TopologicalSpace.IsOpenCover U) {A B : X.Modules} (φ : A ⟶ B) :
    IsIso φ ↔ ∀ i, IsIso ((pullback (U i).ι).map φ) := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩
  refine SheafOfModules.isIso_of_coversTop ((_root_.Opens.coversTop_iff _ U).mpr hU) φ
    fun i ↦ ?_
  -- Pullback along `(U i).ι` is restriction to `U i`, which is restriction to the slice at `U i`
  -- followed by an equivalence of categories.
  have : IsIso ((restrictFunctor (U i).ι).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback (U i).ι) φ).mpr (h i)
  have : IsIso ((overEquiv (U i)).functor.map (φ.over (U i))) :=
    (NatIso.isIso_map_iff (overFunctorEquiv (U i)) φ).mpr this
  exact isIso_of_reflects_iso (φ.over (U i)) (overEquiv (U i)).functor

end Over

section Free

/-- The identification of modules on the slice site over an open `U` with modules on the open
subscheme `U` preserves free modules. -/
def overEquivFunctorObjFreeIso (U : X.Opens) (I : Type u) :
    (overEquiv U).functor.obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  -- The functor is rebound with its type as a functor between categories of sheaves of modules,
  -- where `SheafOfModules.mapFreeIso` seeks its colimit-preservation instance.
  let F : SheafOfModules (X.ringCatSheaf.over U) ⥤ SheafOfModules (U : Scheme).ringCatSheaf :=
    (overEquiv U).functor
  have : PreservesColimitsOfShape (Discrete I) F :=
    (overEquiv U).toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso F I (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).symm

/-- A trivialization of `M` on the slice site over an open `U` gives a trivialization of the
restriction of `M` to the open subscheme `U`. -/
def restrictIsoFreeOfOverIsoFree (M : X.Modules) (U : X.Opens) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) : M.restrict U.ι ≅ SheafOfModules.free I :=
  ((overFunctorEquiv U).app M).symm ≪≫ (overEquiv U).functor.mapIso e ≪≫
    overEquivFunctorObjFreeIso U I

/-- A trivialization of the restriction of `M` to the open subscheme `U` gives a trivialization
of `M` on the slice site over `U`. -/
def overIsoFreeOfRestrictIsoFree (M : X.Modules) (U : X.Opens) {I : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free I) : M.over U ≅ SheafOfModules.free I :=
  (overEquiv U).fullyFaithfulFunctor.preimageIso ((overFunctorEquiv U).app M ≪≫ e ≪≫
    (overEquivFunctorObjFreeIso U I).symm)

/-- A trivialization of the pullback of `M` along an open immersion `f` gives a trivialization of
the restriction of `M` to the open image of `f`. -/
def restrictOpensRangeIsoFree (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] {I : Type u}
    (e : (pullback f).obj M ≅ SheafOfModules.free I) :
    M.restrict f.opensRange.ι ≅ SheafOfModules.free I :=
  letI : (SheafOfModules.pushforward.{u} f.isoOpensRange.inv.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f.isoOpensRange.inv).IsRightAdjoint
  (restrictFunctorIsoPullback f.opensRange.ι).app M ≪≫
    (pullbackCongr f.isoOpensRange_inv_comp).symm.app M ≪≫
    ((pullbackComp f.isoOpensRange.inv f).app M).symm ≪≫
    (pullback f.isoOpensRange.inv).mapIso e ≪≫
    SheafOfModules.pullbackObjFreeIso f.isoOpensRange.inv.toRingCatSheafHom I

end Free

/-- Local generators of an `𝒪_Y`-module `M` on a cover `V i` of `Y`, carried along `f` to local
generators of `f^* M` on the cover `f⁻¹ (V i)` of `X`. -/
@[expose, simps I X generators]
def _root_.SheafOfModules.LocalGeneratorsData.pullback {M : Y.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{w} (R := Y.ringCatSheaf) M) (f : X ⟶ Y) :
    SheafOfModules.LocalGeneratorsData.{w} (R := X.ringCatSheaf) ((pullback f).obj M) where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := by
    have hq := (Opens.coversTop_iff _ _).mp q.coversTop
    rw [Opens.coversTop_iff, IsOpenCover, ← Scheme.Hom.preimage_iSup, hq.iSup_eq_top,
      Scheme.Hom.preimage_top]
  generators i :=
    (q.generators i).mapIso (pullbackOver f (q.X i)) (pullbackOverUnitIso f _)
      (pullbackOverObjIso f _ M)

/-- Carrying local generators along a morphism of schemes preserves finiteness. -/
instance {M : Y.Modules} (q : SheafOfModules.LocalGeneratorsData.{w} (R := Y.ringCatSheaf) M)
    [q.IsFiniteType] (f : X ⟶ Y) : (q.pullback f).IsFiniteType where
  isFiniteType i := SheafOfModules.GeneratingSections.isFiniteType_mapIso (q.generators i)
    (pullbackOver f (q.X i)) (pullbackOverUnitIso f _) (pullbackOverObjIso f _ M)
    (hσ := SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i)

/-- Carrying locally free data along a morphism of schemes gives locally free data. -/
instance {M : Y.Modules} (q : SheafOfModules.LocalGeneratorsData.{w} (R := Y.ringCatSheaf) M)
    [q.IsLocallyFreeData] (f : X ⟶ Y) : (q.pullback f).IsLocallyFreeData where
  isIso i :=
    have := SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i
    SheafOfModules.GeneratingSections.isIso_mapIso_π (q.generators i)
      (pullbackOver f (q.X i)) (pullbackOverUnitIso f _) (pullbackOverObjIso f _ M)

/-- Quasi-coherent data of an `𝒪_Y`-module `M` on a cover `V i` of `Y`, carried along `f` to
quasi-coherent data of `f^* M` on the cover `f⁻¹ (V i)` of `X`. -/
-- As in Mathlib's `SheafOfModules.QuasicoherentData.pushforward`, presentations are transported
-- by `SheafOfModules.Presentation.map` along a colimit-preserving functor.
@[expose, simps I X presentation]
def _root_.SheafOfModules.QuasicoherentData.pullback {M : Y.Modules}
    (q : SheafOfModules.QuasicoherentData.{w} (R := Y.ringCatSheaf) M) (f : X ⟶ Y) :
    SheafOfModules.QuasicoherentData.{w} (R := X.ringCatSheaf) ((pullback f).obj M) where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := (q.localGeneratorsData.pullback f).coversTop
  presentation i :=
    ((q.presentation i).map (pullbackOver f (q.X i)) (pullbackOverUnitIso f _)).ofIsIso
      (pullbackOverObjIso f _ M).hom

/-- Carrying finite quasi-coherent data along a morphism of schemes gives finite quasi-coherent
data. -/
instance {M : Y.Modules} (q : SheafOfModules.QuasicoherentData.{w} (R := Y.ringCatSheaf) M)
    [q.IsFinitePresentation] (f : X ⟶ Y) : (q.pullback f).IsFinitePresentation where
  isFinite_presentation i :=
    have := SheafOfModules.QuasicoherentData.IsFinitePresentation.isFinite_presentation (q := q) i
    SheafOfModules.instIsFiniteOfIsIso (pullbackOverObjIso f _ M).hom _

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
instance isQuasicoherent_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent :=
  ((SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)).some.pullback
    f).isQuasicoherent

/-- The pullback of a module of finite type along a morphism of schemes is of finite type. -/
instance isFiniteType_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  obtain ⟨q, _⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := M)
  exact SheafOfModules.IsFiniteType.mk (R := X.ringCatSheaf) ⟨q.pullback f, inferInstance⟩

/-- The pullback of a finitely presented module along a morphism of schemes is finitely
presented. -/
instance isFinitePresentation_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsFinitePresentation] :
    ((pullback f).obj M).IsFinitePresentation := by
  obtain ⟨q, _⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  exact SheafOfModules.IsFinitePresentation.mk (R := X.ringCatSheaf) ⟨q.pullback f, inferInstance⟩

/-- The pullback of a locally free module along a morphism of schemes is locally free. -/
instance isLocallyFree_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsLocallyFree] :
    ((pullback f).obj M).IsLocallyFree := by
  obtain ⟨q, _⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  exact (q.pullback f).isLocallyFree

end

end AlgebraicGeometry.Scheme.Modules
