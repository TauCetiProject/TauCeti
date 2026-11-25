/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.SmoothSheaf
public import TauCeti.AlgebraicGeometry.Sites.Etale.FiniteLisseSepClosed
public import TauCeti.CategoryTheory.Galois.ModuleSheaf
public import TauCeti.CategoryTheory.Sites.ConstantSheaf
public import TauCeti.RingTheory.Etale.Field

/-!
# Étale sheaves of modules on a field from Galois representations

Let `K` be a field with separable closure `Ω`, and let `ρ` be a representation of `Gal(Ω/K)` on a
`Λ`-module `M`. On finite continuous `Gal(Ω/K)`-sets, `Gal(Ω/K)`-maps into `M` form a sheaf of
`Λ`-modules for the jointly surjective topology (`ContAction.isSheaf_modulePresheaf`). The
equivalence `TauCeti.FiniteEtaleScheme.jointlySurjectiveSheafEquiv` between étale sheaves on
`Spec K` and sheaves for the jointly surjective topology turns `ρ` into an étale sheaf of
`Λ`-modules on `Spec K` (`TauCeti.FiniteEtaleScheme.galoisModuleSheaf`), whose sections over a
finite étale `K`-scheme `X` are the `Gal(Ω/K)`-maps from the `Ω`-points of `X` into `M`, naturally
in `X` (`TauCeti.FiniteEtaleScheme.galoisModuleSheafObjIso`). In particular its sections over
`Spec K` are the invariants of `ρ`
(`TauCeti.FiniteEtaleScheme.galoisModuleSheafObjOfHomIdEquivInvariants`).

When `Ω` is finite over `K`, as `ℂ` is over `ℝ`, the geometric point `Spec Ω ⟶ Spec K` is
surjective and étale, so the sheaf of a finitely generated module over a Noetherian ring is finite
lisse (`TauCeti.FiniteEtaleScheme.isFiniteLisse_galoisModuleSheaf`). The constant sheaf on a
module `N` maps to a sheaf exactly as `N` maps to its sections over the terminal object `Spec K`
(`CategoryTheory.Sheaf.isZero_of_isConstant_of_isZero_obj`), so if `M ≠ 0` has no nonzero
invariants, the sheaf is not constant
(`TauCeti.FiniteEtaleScheme.not_isConstant_galoisModuleSheaf`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.galoisModuleSheaf K Ω ρ`: the étale sheaf of `Λ`-modules on `Spec K`
  attached to a representation `ρ` of `Gal(Ω/K)`.
* `TauCeti.FiniteEtaleScheme.galoisModuleSheafObjIso`,
  `TauCeti.FiniteEtaleScheme.galoisModuleSheafInverseObjIso`: sections over finite étale
  `K`-schemes, and over the finite étale `K`-scheme of a finite Galois set; the latter is a
  component of the natural isomorphism `TauCeti.FiniteEtaleScheme.galoisModuleSheafInverseIso`.
* `TauCeti.FiniteEtaleScheme.galoisModuleSheafObjOfHomIdEquivInvariants`: sections over `Spec K`
  are the invariants.

## Main results

* `TauCeti.FiniteEtaleScheme.galoisModuleSheafObjIso_hom_naturality`,
  `TauCeti.FiniteEtaleScheme.galoisModuleSheafInverseObjIso_hom_naturality`: restriction of
  sections is precomposition of `Gal(Ω/K)`-maps.
* `TauCeti.FiniteEtaleScheme.isFiniteLisse_galoisModuleSheaf`: finite lisse when `Ω` is finite
  over `K`.
* `TauCeti.FiniteEtaleScheme.not_isConstant_galoisModuleSheaf`: not constant when `Ω` is finite
  over `K` and `ρ` is nonzero without nonzero invariants.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry PreGaloisCategory FintypeCatDiscrete

universe u

namespace TauCeti.FiniteEtaleScheme

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]

variable {Λ : Type u} [CommRing Λ] {M : Type u} [AddCommGroup M] [Module Λ M]
  (ρ : Representation Λ Gal(Ω/K) M)

/-- **The étale sheaf of a Galois representation.** For a representation `ρ` of `Gal(Ω/K)` on a
`Λ`-module, the étale sheaf of `Λ`-modules on `Spec K` corresponding under
`jointlySurjectiveSheafEquiv` to the sheaf of `Gal(Ω/K)`-maps into `ρ`. -/
noncomputable def galoisModuleSheaf :
    Sheaf (Scheme.smallEtaleTopology (Spec (.of K))) (ModuleCat.{u} Λ) :=
  (jointlySurjectiveSheafEquiv K Ω (ModuleCat.{u} Λ)).inverse.obj (ContAction.moduleSheaf ρ)

/-- **Sections of the étale sheaf of a Galois representation over Galois sets.** Over the finite
étale `K`-scheme corresponding to a finite continuous `Gal(Ω/K)`-set, the sections of
`galoisModuleSheaf K Ω ρ` are the `Gal(Ω/K)`-maps from it into `ρ`, naturally. -/
noncomputable def galoisModuleSheafInverseIso :
    (galoisEquivalence K Ω).inverse.op ⋙ (toEtale _).op ⋙ (galoisModuleSheaf K Ω ρ).obj ≅
      ContAction.modulePresheaf ρ :=
  -- This is the counit of `jointlySurjectiveSheafEquiv`.
  eqToIso (jointlySurjectiveSheafEquiv_functor_obj_obj K Ω _ _).symm ≪≫
    (sheafToPresheaf _ _).mapIso ((jointlySurjectiveSheafEquiv K Ω (ModuleCat.{u} Λ)).counitIso.app
      (ContAction.moduleSheaf ρ)) ≪≫ eqToIso (ContAction.moduleSheaf_obj ρ)

/-- **Sections of the étale sheaf of a Galois representation over a Galois set.** Over the finite
étale `K`-scheme corresponding to a finite continuous `Gal(Ω/K)`-set `X`, the sections of
`galoisModuleSheaf K Ω ρ` are the `Gal(Ω/K)`-maps from `X` into `ρ`. -/
noncomputable def galoisModuleSheafInverseObjIso (X : ContAction FintypeCat.{u} Gal(Ω/K)) :
    (galoisModuleSheaf K Ω ρ).obj.obj
        (op ((toEtale _).obj ((galoisEquivalence K Ω).inverse.obj X))) ≅
      (ContAction.modulePresheaf ρ).obj (op X) :=
  (galoisModuleSheafInverseIso K Ω ρ).app (op X)

/-- Under `galoisModuleSheafInverseObjIso`, restriction of sections of `galoisModuleSheaf K Ω ρ`
along a map of finite Galois sets is precomposition of `Gal(Ω/K)`-maps. -/
@[reassoc]
theorem galoisModuleSheafInverseObjIso_hom_naturality
    {X Y : ContAction FintypeCat.{u} Gal(Ω/K)} (f : X ⟶ Y) :
    (galoisModuleSheaf K Ω ρ).obj.map ((toEtale _).map ((galoisEquivalence K Ω).inverse.map f)).op ≫
        (galoisModuleSheafInverseObjIso K Ω ρ X).hom =
      (galoisModuleSheafInverseObjIso K Ω ρ Y).hom ≫ (ContAction.modulePresheaf ρ).map f.op :=
  (galoisModuleSheafInverseIso K Ω ρ).hom.naturality f.op

/-- **Sections of the étale sheaf of a Galois representation.** Over a finite étale `K`-scheme
`X`, the sections of `galoisModuleSheaf K Ω ρ` are the `Gal(Ω/K)`-maps from the corresponding
finite Galois set into `ρ`. -/
noncomputable def galoisModuleSheafObjIso (X : FiniteEtaleScheme (Spec (.of K))) :
    (galoisModuleSheaf K Ω ρ).obj.obj (op ((toEtale _).obj X)) ≅
      (ContAction.modulePresheaf ρ).obj (op ((galoisEquivalence K Ω).functor.obj X)) :=
  (galoisModuleSheaf K Ω ρ).obj.mapIso
      ((toEtale _).mapIso ((galoisEquivalence K Ω).unitIso.app X)).symm.op ≪≫
    galoisModuleSheafInverseObjIso K Ω ρ ((galoisEquivalence K Ω).functor.obj X)

/-- Under `galoisModuleSheafObjIso`, restriction of sections of `galoisModuleSheaf K Ω ρ` along a
map of finite étale `K`-schemes is precomposition with the corresponding map of Galois sets. -/
@[reassoc]
theorem galoisModuleSheafObjIso_hom_naturality {X Y : FiniteEtaleScheme (Spec (.of K))}
    (f : X ⟶ Y) :
    (galoisModuleSheaf K Ω ρ).obj.map ((toEtale _).map f).op ≫
        (galoisModuleSheafObjIso K Ω ρ X).hom =
      (galoisModuleSheafObjIso K Ω ρ Y).hom ≫
        (ContAction.modulePresheaf ρ).map ((galoisEquivalence K Ω).functor.map f).op := by
  simp only [galoisModuleSheafObjIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Category.assoc,
    ← galoisModuleSheafInverseObjIso_hom_naturality, ← Functor.map_comp_assoc, ← op_comp,
    ← Functor.map_comp]
  have h := (galoisEquivalence K Ω).unitIso.inv.naturality f
  simp only [Functor.comp_map, Functor.id_map] at h
  rw [h]

/-- Over a finite étale `K`-scheme, the sections of the sheaf of a finitely generated module over
a Noetherian ring are finitely generated. -/
instance instModuleFiniteGaloisModuleSheafObj [IsNoetherianRing Λ] [Module.Finite Λ M]
    (X : FiniteEtaleScheme (Spec (.of K))) :
    Module.Finite Λ ((galoisModuleSheaf K Ω ρ).obj.obj (op ((toEtale _).obj X))) :=
  Module.Finite.equiv (galoisModuleSheafObjIso K Ω ρ X).toLinearEquiv.symm

/-- **The sheaf of a Galois representation is finite lisse when `Ω` is finite over `K`.** For a
representation `ρ` of `Gal(Ω/K)` on a finitely generated module over a Noetherian ring,
`galoisModuleSheaf K Ω ρ` is finite lisse. -/
theorem isFiniteLisse_galoisModuleSheaf [FiniteDimensional K Ω] [IsNoetherianRing Λ]
    [Module.Finite Λ M] : (galoisModuleSheaf K Ω ρ).IsFiniteLisse := by
  let s : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have : Algebra.Etale K Ω := Algebra.Etale.of_isSeparable K Ω
  have : Etale s :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : IsFinite s := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  -- The geometric point `s : Spec Ω ⟶ Spec K` is finite étale and surjective.
  have : Surjective s := ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  -- The stalk at the étale point `s` is the module of sections over `s`.
  have : Module.Finite Λ
      ((TauCeti.AlgebraicGeometry.Scheme.etaleStalk Λ s).obj (galoisModuleSheaf K Ω ρ)) :=
    Module.Finite.equiv (((Scheme.pointSmallEtaleSheafFiberIso s).app _ ≪≫
      (galoisModuleSheaf K Ω ρ).obj.mapIso (toEtaleObjOfHomIso _ s).op).toLinearEquiv.symm)
  exact .of_etale_of_surjective_of_isSepClosed _ s

variable {K Ω} in
/-- **Sections over `Spec K` are the invariants.** The sections of `galoisModuleSheaf K Ω ρ` over
the terminal object `Spec K` are the invariants of `ρ`. -/
noncomputable def galoisModuleSheafObjOfHomIdEquivInvariants :
    (galoisModuleSheaf K Ω ρ).obj.obj (op ((toEtale _).obj (ofHom (𝟙 (Spec (.of K)))))) ≃ₗ[Λ]
      Representation.invariants ρ :=
  -- The corresponding Galois set is a point, and a `Gal(Ω/K)`-map from a point is its value.
  (galoisModuleSheafObjIso K Ω ρ _).toLinearEquiv ≪≫ₗ
    ContAction.modulePresheafObjEquivInvariants ρ
      ((isTerminalOfHomId (Spec (.of K))).isTerminalObj (galoisEquivalence K Ω).functor)

variable {K Ω} in
/-- Under `galoisModuleSheafObjOfHomIdEquivInvariants`, a section over `Spec K` is sent to the
value, at any point, of the `Gal(Ω/K)`-map that `galoisModuleSheafObjIso` assigns to it. -/
theorem coe_galoisModuleSheafObjOfHomIdEquivInvariants_apply
    (φ : (galoisModuleSheaf K Ω ρ).obj.obj (op ((toEtale _).obj (ofHom (𝟙 (Spec (.of K)))))))
    (s : (ContAction.fiberFunctor Gal(Ω/K)).obj
      ((galoisEquivalence K Ω).functor.obj (ofHom (𝟙 (Spec (.of K)))))) :
    (galoisModuleSheafObjOfHomIdEquivInvariants ρ φ : M) =
      (ContAction.modulePresheafObjEquiv ρ _ ((galoisModuleSheafObjIso K Ω ρ _).hom φ)).val s :=
  ContAction.coe_modulePresheafObjEquivInvariants_apply ρ _ _ s

variable {K Ω} in
/-- If `ρ` has no nonzero invariants, the sheaf `galoisModuleSheaf K Ω ρ` has no nonzero sections
over `Spec K`. -/
theorem subsingleton_galoisModuleSheaf_obj_ofHom_id (hρ : Representation.invariants ρ = ⊥) :
    Subsingleton ((galoisModuleSheaf K Ω ρ).obj.obj
      (op ((toEtale _).obj (ofHom (𝟙 (Spec (.of K))))))) := by
  rw [(galoisModuleSheafObjOfHomIdEquivInvariants ρ).subsingleton_congr, hρ]
  infer_instance

variable {K Ω} in
/-- For `Ω` finite over `K` and `M ≠ 0`, the sheaf `galoisModuleSheaf K Ω ρ` has a nonzero
section over the finite étale `K`-scheme of the left regular `Gal(Ω/K)`-set: the orbit map
`g ↦ ρ g m` of a nonzero `m`. -/
theorem nontrivial_galoisModuleSheaf_obj_leftRegular [FiniteDimensional K Ω] [Nontrivial M] :
    Nontrivial ((galoisModuleSheaf K Ω ρ).obj.obj
      (op ((toEtale _).obj
        ((galoisEquivalence K Ω).inverse.obj (ContAction.leftRegular Gal(Ω/K)))))) :=
  have := ContAction.nontrivial_modulePresheaf_obj_leftRegular ρ
  (galoisModuleSheafInverseObjIso K Ω ρ _).toLinearEquiv.nontrivial_congr.2 this

variable {K Ω} in
/-- **Galois representations without invariants give nonconstant étale sheaves.** Let `Ω` be
finite over `K`, and let `ρ` be a nonzero representation of `Gal(Ω/K)` with no nonzero
invariants. Then the étale sheaf `galoisModuleSheaf K Ω ρ` on `Spec K` is not constant. -/
theorem not_isConstant_galoisModuleSheaf [FiniteDimensional K Ω] [Nontrivial M]
    (hρ : Representation.invariants ρ = ⊥) :
    ¬ (galoisModuleSheaf K Ω ρ).IsConstant (Scheme.smallEtaleTopology (Spec (.of K))) := by
  -- A constant such sheaf is zero, since its sections over the terminal object `Spec K` vanish;
  -- but it has a nonzero section over the finite étale `K`-scheme of the left regular Galois set.
  intro _
  have hT : IsTerminal ((toEtale _).obj (ofHom (𝟙 (Spec (.of K))))) :=
    (Scheme.Etale.mkIdTerminal _).ofIso (toEtaleObjOfHomIso _ (𝟙 _)).symm
  have := subsingleton_galoisModuleSheaf_obj_ofHom_id ρ hρ
  have hz := Sheaf.isZero_of_isConstant_of_isZero_obj _ hT (galoisModuleSheaf K Ω ρ)
    (ModuleCat.isZero_of_subsingleton _)
  obtain ⟨a, b, hab⟩ :=
    (nontrivial_galoisModuleSheaf_obj_leftRegular (K := K) (Ω := Ω) ρ).exists_pair_ne
  exact hab (@Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero
    (((sheafSections _ _).obj (op ((toEtale _).obj
      ((galoisEquivalence K Ω).inverse.obj (ContAction.leftRegular Gal(Ω/K)))))).map_isZero hz))
    a b)

end TauCeti.FiniteEtaleScheme
