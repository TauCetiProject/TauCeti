/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Connected
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.FieldSheaf
public import TauCeti.AlgebraicGeometry.Sites.Etale.Localization
public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf
public import TauCeti.CategoryTheory.Galois.ModuleSheaf
public import TauCeti.RingTheory.Etale.Field

/-!
# Étale sheaves of modules on a field from Galois representations

Let `K` be a field with separable closure `Ω`, and let `ρ` be a representation of `Gal(Ω/K)` on a
`Λ`-module `M`. On finite continuous `Gal(Ω/K)`-sets, `Gal(Ω/K)`-maps into `M` form a sheaf of
`Λ`-modules for the jointly surjective topology (`ContAction.isSheaf_modulePresheaf`). The
topology `TauCeti.FiniteEtaleScheme.galoisTopology K Ω` transported from the small étale site of
`Spec K` is coarser (`TauCeti.FiniteEtaleScheme.galoisTopology_le_jointlySurjectiveTopology`): a
covering family of finite étale `K`-schemes is jointly surjective on geometric fibres. Hence the
equivalence `TauCeti.FiniteEtaleScheme.galoisSheafEquiv` turns `ρ` into an étale sheaf of
`Λ`-modules on `Spec K` (`TauCeti.FiniteEtaleScheme.galoisModuleSheaf`), whose sections over a
finite étale `K`-scheme `X` are the `Gal(Ω/K)`-maps from the `Ω`-points of `X` into `M`
(`TauCeti.FiniteEtaleScheme.galoisModuleSheafObjIso`).

When `Ω` is finite over `K`, as `ℂ` is over `ℝ`, the geometric point `Spec Ω ⟶ Spec K` is
surjective and étale, so the sheaf of a finitely generated module over a Noetherian ring is finite
lisse (`TauCeti.FiniteEtaleScheme.isFiniteLisse_galoisModuleSheaf`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.galoisModuleSheaf K Ω ρ`: the étale sheaf of `Λ`-modules on `Spec K`
  attached to a representation `ρ` of `Gal(Ω/K)`.

## Main results

* `TauCeti.FiniteEtaleScheme.nonempty_fiberFunctor_obj_iff`: a finite Galois set is nonempty
  exactly when the corresponding finite étale `K`-scheme is.
* `TauCeti.FiniteEtaleScheme.galoisTopology_le_jointlySurjectiveTopology`: coverings for
  `galoisTopology K Ω` are jointly surjective.
* `TauCeti.FiniteEtaleScheme.galoisModuleSheafObjIso`: sections over finite étale `K`-schemes.
* `TauCeti.FiniteEtaleScheme.isFiniteLisse_galoisModuleSheaf`: finite lisse when `Ω` is finite
  over `K`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry PreGaloisCategory FintypeCatDiscrete

universe u

namespace TauCeti.FiniteEtaleScheme

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]

variable {K Ω} in
/-- A finite continuous `Gal(Ω/K)`-set is nonempty if and only if the corresponding finite étale
`K`-scheme is nonempty: both mean that the object is not initial. -/
theorem nonempty_fiberFunctor_obj_iff (T : ContAction FintypeCat.{u} Gal(Ω/K)) :
    Nonempty ((ContAction.fiberFunctor Gal(Ω/K)).obj T) ↔
      Nonempty ((galoisEquivalence K Ω).inverse.obj T).obj.left := by
  rw [← not_isEmpty_iff, ← not_isEmpty_iff, ← isInitial_iff_isEmpty]
  refine not_congr ((initial_iff_fiber_empty
    (forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u}) T).symm.trans
      ⟨fun ⟨h⟩ ↦ ⟨h.isInitialObj _ _⟩, fun ⟨h⟩ ↦ ⟨?_⟩⟩)
  exact (h.isInitialObj (galoisEquivalence K Ω).functor _).ofIso
    ((galoisEquivalence K Ω).counitIso.app T)

/-- **Galois coverings are jointly surjective.** A covering sieve of a finite continuous
`Gal(Ω/K)`-set for the topology transported from the small étale site of `Spec K` is jointly
surjective on underlying sets. Every point lies in the image of a Galois object `A`; the sieve
pulled back to `A` covers the nonempty scheme corresponding to `A`, so it contains a map from a
nonempty Galois set to the connected `A`, which is surjective. -/
theorem galoisTopology_le_jointlySurjectiveTopology :
    galoisTopology K Ω ≤ ContAction.jointlySurjectiveTopology Gal(Ω/K) := by
  intro X R hR
  rw [ContAction.mem_jointlySurjectiveTopology_iff]
  intro s
  obtain ⟨A, a, a₀, hA, rfl⟩ := exists_hom_from_galois_of_fiber
    (forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u}) X s
  have hRA := (galoisTopology K Ω).pullback_stable a hR
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    Functor.mem_inducedTopology_iff_of_isCoverDense, Scheme.mem_smallEtaleTopology_iff] at hRA
  obtain ⟨x⟩ := (nonempty_fiberFunctor_obj_iff A).1 ⟨a₀⟩
  obtain ⟨Y, f, y, ⟨Z, g, h, ⟨T, t, k, ht, rfl⟩, rfl⟩, -⟩ := hRA x
  obtain ⟨t₀⟩ := (nonempty_fiberFunctor_obj_iff T).2 ⟨k.hom.left (h.left y)⟩
  have : Nonempty ((forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u}).obj T) := ⟨t₀⟩
  obtain ⟨t₁, ht₁⟩ := surjective_of_nonempty_fiber_of_isConnected
    (forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u}) t a₀
  exact ⟨T, t ≫ a, ht, t₁, by simp [ht₁]⟩

variable {Λ : Type u} [CommRing Λ] {M : Type u} [AddCommGroup M] [Module Λ M]
  (ρ : Representation Λ Gal(Ω/K) M)

/-- The `Gal(Ω/K)`-maps into a representation `ρ`, as a sheaf on finite continuous
`Gal(Ω/K)`-sets for `galoisTopology K Ω`. -/
noncomputable def galoisSetModuleSheaf : Sheaf (galoisTopology K Ω) (ModuleCat.{u} Λ) :=
  ⟨ContAction.modulePresheaf ρ, fun E ↦ Presieve.isSheaf_of_le _
    (galoisTopology_le_jointlySurjectiveTopology K Ω) (ContAction.isSheaf_modulePresheaf ρ E)⟩

/-- **The étale sheaf of a Galois representation.** For a representation `ρ` of `Gal(Ω/K)` on a
`Λ`-module, the étale sheaf of `Λ`-modules on `Spec K` corresponding under `galoisSheafEquiv` to
the sheaf of `Gal(Ω/K)`-maps into `ρ`. -/
noncomputable def galoisModuleSheaf :
    Sheaf (Scheme.smallEtaleTopology (Spec (.of K))) (ModuleCat.{u} Λ) :=
  (galoisSheafEquiv K (ModuleCat.{u} Λ) Ω).inverse.obj (galoisSetModuleSheaf K Ω ρ)

/-- **Sections of the étale sheaf of a Galois representation.** Over a finite étale `K`-scheme
`X`, the sections of `galoisModuleSheaf K Ω ρ` are the `Gal(Ω/K)`-maps from the corresponding
finite Galois set into `ρ`. -/
noncomputable def galoisModuleSheafObjIso (X : FiniteEtaleScheme (Spec (.of K))) :
    (galoisModuleSheaf K Ω ρ).obj.obj (op ((toEtale _).obj X)) ≅
      (ContAction.modulePresheaf ρ).obj (op ((galoisEquivalence K Ω).functor.obj X)) :=
  (galoisModuleSheaf K Ω ρ).obj.mapIso
      ((toEtale _).mapIso ((galoisEquivalence K Ω).unitIso.app X)).symm.op ≪≫
    eqToIso (by rw [galoisSheafEquiv_functor, fieldSheafEquiv_functor]; rfl) ≪≫
    ((sheafToPresheaf _ _).mapIso ((galoisSheafEquiv K (ModuleCat.{u} Λ) Ω).counitIso.app
      (galoisSetModuleSheaf K Ω ρ))).app (op ((galoisEquivalence K Ω).functor.obj X))

/-- Over a finite étale `K`-scheme, the sections of the sheaf of a finitely generated module over
a Noetherian ring are finitely generated. -/
instance instModuleFiniteGaloisModuleSheafObj [IsNoetherianRing Λ] [Module.Finite Λ M]
    (X : FiniteEtaleScheme (Spec (.of K))) :
    Module.Finite Λ ((galoisModuleSheaf K Ω ρ).obj.obj (op ((toEtale _).obj X))) :=
  Module.Finite.equiv (galoisModuleSheafObjIso K Ω ρ X).toLinearEquiv.symm

/-- **The sheaf of a Galois representation is finite lisse when `Ω` is finite over `K`.** Then the
geometric point `Spec Ω ⟶ Spec K` is finite étale and surjective, and the stalk there is the
module of sections over it, finitely generated for a finitely generated module over a Noetherian
ring. -/
theorem isFiniteLisse_galoisModuleSheaf [FiniteDimensional K Ω] [IsNoetherianRing Λ]
    [Module.Finite Λ M] : (galoisModuleSheaf K Ω ρ).IsFiniteLisse := by
  let s : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have : Algebra.Etale K Ω := Algebra.Etale.of_isSeparable K Ω
  have : Etale s :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : IsFinite s := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Surjective s := ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  -- The stalk at the étale point `s` is the module of sections over `s`.
  have : Module.Finite Λ
      ((TauCeti.AlgebraicGeometry.Scheme.etaleStalk Λ s).obj (galoisModuleSheaf K Ω ρ)) :=
    Module.Finite.equiv (((Scheme.pointSmallEtaleSheafFiberIso s).app _ ≪≫
      (galoisModuleSheaf K Ω ρ).obj.mapIso ((Scheme.Etale.forgetFullyFaithful _).preimageIso
        (eqToIso (by rw [forget_obj_toEtale_obj, ofHom_obj]; rfl)) :
          Scheme.Etale.mk s ≅ (toEtale _).obj (ofHom s)).symm.op).toLinearEquiv.symm)
  exact .of_etale_of_surjective_of_isSepClosed _ s

end TauCeti.FiniteEtaleScheme
