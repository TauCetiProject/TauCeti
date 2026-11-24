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
public import TauCeti.AlgebraicGeometry.Sites.Etale.Subcanonical
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
(`TauCeti.FiniteEtaleScheme.galoisModuleSheafObjIso`). The topology `galoisTopology K Ω` is also
subcanonical (`TauCeti.FiniteEtaleScheme.subcanonical_galoisTopology`), being induced from the
subcanonical small étale topology of `Spec K`.

When `Ω` is finite over `K`, as `ℂ` is over `ℝ`, the geometric point `Spec Ω ⟶ Spec K` is
surjective and étale, so the sheaf of a finitely generated module over a Noetherian ring is finite
lisse (`TauCeti.FiniteEtaleScheme.isFiniteLisse_galoisModuleSheaf`). Its sections over `Spec K`
are the invariants of `ρ`. The constant sheaf on a module `N` maps to a sheaf exactly as `N` maps
to its sections over the terminal object `Spec K`, so if `M ≠ 0` has no nonzero invariants, the
sheaf is not constant (`TauCeti.FiniteEtaleScheme.not_isConstant_galoisModuleSheaf`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.galoisModuleSheaf K Ω ρ`: the étale sheaf of `Λ`-modules on `Spec K`
  attached to a representation `ρ` of `Gal(Ω/K)`.
* `TauCeti.FiniteEtaleScheme.regularGaloisSet K Ω`: the regular `Gal(Ω/K)`-set, for `Ω` finite
  over `K`.

## Main results

* `TauCeti.FiniteEtaleScheme.nonempty_fiberFunctor_obj_iff`: a finite Galois set is nonempty
  exactly when the corresponding finite étale `K`-scheme is.
* `TauCeti.FiniteEtaleScheme.galoisTopology_le_jointlySurjectiveTopology`: coverings for
  `galoisTopology K Ω` are jointly surjective.
* `TauCeti.FiniteEtaleScheme.subcanonical_fieldTopology`,
  `TauCeti.FiniteEtaleScheme.subcanonical_galoisTopology`: these topologies are subcanonical.
* `TauCeti.FiniteEtaleScheme.galoisModuleSheafObjIso`,
  `TauCeti.FiniteEtaleScheme.galoisModuleSheafInverseObjIso`: sections over finite étale
  `K`-schemes, and over the finite étale `K`-scheme of a finite Galois set.
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

/-- The topology on finite étale `K`-schemes induced from the small étale site of `Spec K` is
subcanonical, as the small étale topology is. -/
instance subcanonical_fieldTopology : (fieldTopology K).Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful (toEtale _) _
    (Scheme.smallEtaleTopology _)

/-- The topology on finite continuous `Gal(Ω/K)`-sets transported from the small étale site of
`Spec K` is subcanonical. -/
instance subcanonical_galoisTopology : (galoisTopology K Ω).Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful (galoisEquivalence K Ω).inverse _
    (fieldTopology K)

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

/-- **Sections of the étale sheaf of a Galois representation over Galois sets.** Over the finite
étale `K`-scheme corresponding to a finite continuous `Gal(Ω/K)`-set `X`, the sections of
`galoisModuleSheaf K Ω ρ` are the `Gal(Ω/K)`-maps from `X` into `ρ`. -/
noncomputable def galoisModuleSheafInverseObjIso (X : ContAction FintypeCat.{u} Gal(Ω/K)) :
    (galoisModuleSheaf K Ω ρ).obj.obj
        (op ((toEtale _).obj ((galoisEquivalence K Ω).inverse.obj X))) ≅
      (ContAction.modulePresheaf ρ).obj (op X) :=
  eqToIso (by rw [galoisSheafEquiv_functor, fieldSheafEquiv_functor]; rfl) ≪≫
    ((sheafToPresheaf _ _).mapIso ((galoisSheafEquiv K (ModuleCat.{u} Λ) Ω).counitIso.app
      (galoisSetModuleSheaf K Ω ρ))).app (op X)

/-- **Sections of the étale sheaf of a Galois representation.** Over a finite étale `K`-scheme
`X`, the sections of `galoisModuleSheaf K Ω ρ` are the `Gal(Ω/K)`-maps from the corresponding
finite Galois set into `ρ`. -/
noncomputable def galoisModuleSheafObjIso (X : FiniteEtaleScheme (Spec (.of K))) :
    (galoisModuleSheaf K Ω ρ).obj.obj (op ((toEtale _).obj X)) ≅
      (ContAction.modulePresheaf ρ).obj (op ((galoisEquivalence K Ω).functor.obj X)) :=
  (galoisModuleSheaf K Ω ρ).obj.mapIso
      ((toEtale _).mapIso ((galoisEquivalence K Ω).unitIso.app X)).symm.op ≪≫
    galoisModuleSheafInverseObjIso K Ω ρ ((galoisEquivalence K Ω).functor.obj X)

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

variable {K Ω} in
/-- **Sections over `Spec K` are the invariants.** If no nonzero vector of `ρ` is fixed by
`Gal(Ω/K)`, the sheaf `galoisModuleSheaf K Ω ρ` has no nonzero sections over `Spec K`: the
corresponding Galois set is a point, so a section is a fixed vector. -/
theorem subsingleton_galoisModuleSheaf_obj_ofHom_id (hfix : ∀ m, (∀ g, ρ g m = m) → m = 0) :
    Subsingleton ((galoisModuleSheaf K Ω ρ).obj.obj
      (op ((toEtale _).obj (ofHom (𝟙 (Spec (.of K))))))) := by
  have hT := (isTerminalOfHomId (Spec (.of K))).isTerminalObj (galoisEquivalence K Ω).functor
  have : Subsingleton ((ContAction.fiberFunctor Gal(Ω/K)).obj
      ((galoisEquivalence K Ω).functor.obj (ofHom (𝟙 (Spec (.of K)))))) :=
    (Types.isTerminalEquivUnique _
      (hT.isTerminalObj (ContAction.fiberFunctor Gal(Ω/K)))).instSubsingleton
  have key (φ : (ContAction.modulePresheaf ρ).obj
      (op ((galoisEquivalence K Ω).functor.obj (ofHom (𝟙 (Spec (.of K))))))) y : φ.val y = 0 :=
    hfix _ fun g ↦ by rw [← φ.property g y, Subsingleton.elim (g • y) y]
  exact ⟨fun a b ↦ (galoisModuleSheafObjIso K Ω ρ _).toLinearEquiv.injective
    (Subtype.ext (funext fun y ↦ (key _ y).trans (key _ y).symm))⟩

/-- The regular `Gal(Ω/K)`-set, for `Ω` finite over `K`; it is continuous since `Gal(Ω/K)` is
then discrete. -/
noncomputable abbrev regularGaloisSet [FiniteDimensional K Ω] :
    ContAction FintypeCat.{u} Gal(Ω/K) :=
  ⟨Action.FintypeCat.ofMulAction Gal(Ω/K) (FintypeCat.of Gal(Ω/K)),
    (Action.isContinuous_iff_isOpen_stabilizer _).2 fun _ ↦ isOpen_discrete _⟩

variable {K Ω} in
/-- For `Ω` finite over `K` and `M ≠ 0`, the sheaf `galoisModuleSheaf K Ω ρ` has a nonzero
section over the finite étale `K`-scheme of the regular `Gal(Ω/K)`-set: the orbit map
`g ↦ ρ g m` of a nonzero `m`. -/
theorem nontrivial_galoisModuleSheaf_obj_regularGaloisSet [FiniteDimensional K Ω]
    [Nontrivial M] :
    Nontrivial ((galoisModuleSheaf K Ω ρ).obj.obj
      (op ((toEtale _).obj ((galoisEquivalence K Ω).inverse.obj (regularGaloisSet K Ω))))) := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let φ : (ContAction.modulePresheaf ρ).obj (op (regularGaloisSet K Ω)) :=
    ⟨fun (g : Gal(Ω/K)) ↦ ρ g m, fun g (h : Gal(Ω/K)) ↦ by
      change ρ (g * h) m = _
      rw [map_mul]; rfl⟩
  have : φ ≠ 0 := fun h ↦ by
    have h1 : φ.val (show (ContAction.fiberFunctor _).obj (regularGaloisSet K Ω) from
        (1 : Gal(Ω/K))) = m := by
      simp [φ]
    rw [h] at h1
    exact hm h1.symm
  exact (galoisModuleSheafInverseObjIso K Ω ρ _).toLinearEquiv.nontrivial_congr.2 ⟨φ, 0, this⟩

variable {K Ω} in
/-- **Galois representations without invariants give nonconstant étale sheaves.** Let `Ω` be
finite over `K`, and let `ρ` be a nonzero representation of `Gal(Ω/K)` with no nonzero fixed
vector. Then the étale sheaf `galoisModuleSheaf K Ω ρ` on `Spec K` is not constant: morphisms
from a constant sheaf on `N` correspond to maps from `N` to the sections over the terminal object
`Spec K`, which vanish, so a constant such sheaf is zero; but it has a nonzero section over the
finite étale `K`-scheme of the regular Galois set. -/
theorem not_isConstant_galoisModuleSheaf [FiniteDimensional K Ω] [Nontrivial M]
    (hfix : ∀ m, (∀ g, ρ g m = m) → m = 0) :
    ¬ (galoisModuleSheaf K Ω ρ).IsConstant (Scheme.smallEtaleTopology (Spec (.of K))) := by
  rintro ⟨N, ⟨e⟩⟩
  let F := galoisModuleSheaf K Ω ρ
  have hT : IsTerminal ((toEtale _).obj (ofHom (𝟙 (Spec (.of K))))) :=
    (Scheme.Etale.mkIdTerminal _).ofIso ((Scheme.Etale.forgetFullyFaithful _).preimageIso
      (eqToIso (by rw [forget_obj_toEtale_obj, ofHom_obj]; rfl)))
  have hΓ := subsingleton_galoisModuleSheaf_obj_ofHom_id ρ hfix
  -- Morphisms from the constant sheaf on `N` correspond to maps from `N` to the zero module.
  have hF : Subsingleton (F ⟶ F) := ⟨fun a b ↦ by
    have h := ((constantSheafAdj _ (ModuleCat.{u} Λ) hT).homEquiv N F).injective
      (a₁ := e.hom ≫ a) (a₂ := e.hom ≫ b)
      (ModuleCat.hom_ext (LinearMap.ext fun _ ↦ hΓ.elim _ _))
    simpa using congr(e.inv ≫ $h)⟩
  have hz : IsZero F := (IsZero.iff_id_eq_zero F).2 (Subsingleton.elim _ _)
  obtain ⟨a, b, hab⟩ := (nontrivial_galoisModuleSheaf_obj_regularGaloisSet ρ).exists_pair_ne
  exact hab (@Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero
    (((sheafSections _ _).obj (op ((toEtale _).obj
      ((galoisEquivalence K Ω).inverse.obj (regularGaloisSet K Ω))))).map_isZero hz)) a b)

end TauCeti.FiniteEtaleScheme
