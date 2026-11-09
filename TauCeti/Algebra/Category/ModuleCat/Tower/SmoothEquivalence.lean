/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Ring

/-!
# Smooth modules are the discrete modules over the completion

Let `A` be a ring and `J₀ ⊇ J₁ ⊇ J₂ ⊇ ⋯` a decreasing family of left ideals of `A` satisfying the
right-shift estimate `∀ b n, ∃ m, Jₘ b ⊆ Jₙ`, so that the completion `Â = lim A ⧸ Jₙ` is a
topological ring (`TauCeti.ModuleTower.limRing`). This file proves that the category of
`A`-modules which are smooth for `J` (`TauCeti.smoothModules`) is equivalent to the category of
discrete `Â`-modules (`TauCeti.discreteModules`), the `Â`-modules all of whose orbit maps
`x ↦ x • m` are continuous for the discrete topology on the module
(`TauCeti.ModuleTower.smoothModulesEquivalence`).

The two functors do not change the underlying abelian groups or linear maps.

* A smooth `A`-module is an `Â`-module through the action `TauCeti.ModuleTower.limSmul`, under which
  `x` acts on a vector killed by `Jₙ` as any representative of the `n`-th coordinate of `x`
  (`TauCeti.ModuleTower.limModule`). Its orbit maps are locally constant, so it is discrete.
* A discrete `Â`-module restricts along the canonical ring homomorphism `A → Â`
  (`TauCeti.ModuleTower.toLimRingHom`) to a smooth `A`-module: the annihilator of a vector is an
  open neighbourhood of zero, so it contains the kernel of some projection `Â → A ⧸ Jₙ`, whose
  preimage in `A` is `Jₙ`.

Extending and then restricting gives back the action of `A`, since `limSmul` extends it. Restricting
and then extending gives back the action of `Â`, by the uniqueness of an extension of the action
of `A` with locally constant orbit maps (`TauCeti.ModuleTower.eq_limSmul_of_isLocallyConstant`),
which rests on the density of `A` in `Â`.

## Implementation notes

The functors and the equivalence are exposed, so that the image of a module definitionally has the
same carrier; the formulas for the actions (`TauCeti.ModuleTower.smoothModulesToDiscrete_obj_smul`,
`TauCeti.ModuleTower.discreteModulesToSmooth_obj_smul`) are stated on that carrier. The unit and
counit of the equivalence are identity maps on carriers
(`TauCeti.ModuleTower.smoothModulesEquivalence_unitIso_hom_app_hom_apply` and its companions).

## Main definitions

* `TauCeti.ModuleTower.smoothModulesToDiscrete`: smooth `A`-modules as discrete `Â`-modules.
* `TauCeti.ModuleTower.discreteModulesToSmooth`: restriction of discrete `Â`-modules to `A`.
* `TauCeti.ModuleTower.smoothModulesEquivalence`: the equivalence of categories they form.

## Main results

* `TauCeti.ModuleTower.discreteModules_limModule`: a smooth module is a discrete module over the
  completion.
* `TauCeti.ModuleTower.smoothModules_restrictScalars_toLimRingHom`: a discrete module over the
  completion restricts to a smooth module.
* `TauCeti.ModuleTower.limSmul_restrictScalars_toLimRingHom`: the action of the completion on a
  discrete module is recovered from its restriction to `A`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.1.2 and §3.2.1, for the identification
  of smooth modules over an affine Kac--Moody algebra with discrete modules over its completed
  enveloping algebra.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory

universe u w

variable {A : Type u} [Ring A] {J : ℕ → Submodule A A} {hJ : Antitone J}
  (hJr : ∀ (b : A) (n : ℕ), ∃ m, ∀ c ∈ J m, c * b ∈ J n)

/-- **A smooth module is a discrete module over the completion**: for the action
`TauCeti.ModuleTower.limSmul`, every orbit map `x ↦ x • m` is locally constant. -/
theorem discreteModules_limModule {M : ModuleCat.{w} A} (hM : smoothModules J M) :
    letI := limRing (hJ := hJ) hJr
    letI := limModule hJr hM
    discreteModules (quotients J hJ).lim (ModuleCat.of (quotients J hJ).lim M) :=
  letI := limRing (hJ := hJ) hJr
  letI := limModule hJr hM
  discreteModules_iff.2 fun m ↦ by
    let _ : TopologicalSpace M := ⊥
    exact (isLocallyConstant_limSmul hM m).continuous

/-- **A discrete module over the completion restricts to a smooth module**: the annihilator of a
vector is open, so it contains the kernel of a projection `lim A ⧸ Jₙ → A ⧸ Jₙ`, and the image of
`Jₙ` lies in that kernel. -/
theorem smoothModules_restrictScalars_toLimRingHom :
    letI := limRing (hJ := hJ) hJr
    ∀ {M : ModuleCat.{w} (quotients J hJ).lim}, discreteModules (quotients J hJ).lim M →
      smoothModules J ((ModuleCat.restrictScalars (toLimRingHom hJr)).obj M) := by
  let := limRing (hJ := hJ) hJr
  intro M hM
  refine smoothModules_iff.2 fun m ↦ ?_
  obtain ⟨n, -, hn⟩ := (quotients J hJ).hasBasis_nhds_zero.mem_iff.1
    ((discreteModules_iff_isOpen.1 hM m 0).mem_nhds (zero_smul _ m))
  refine ⟨n, fun a ha ↦ (ModuleCat.restrictScalars.smul_def _ a m).trans (hn ?_)⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, coe_toLimRingHom, ← LinearMap.comp_apply,
    limπ_comp_toLimQuotients, quotientsπ_eq_zero_iff]
  exact ha

/-- **The action of the completion on a discrete module is determined by the action of `A`**: it
is the action `TauCeti.ModuleTower.limSmul` on the restriction of the module to `A`. -/
theorem limSmul_restrictScalars_toLimRingHom :
    letI := limRing (hJ := hJ) hJr
    ∀ {M : ModuleCat.{w} (quotients J hJ).lim} (hM : discreteModules (quotients J hJ).lim M)
      (x : (quotients J hJ).lim) (m : M),
      limSmul (smoothModules_restrictScalars_toLimRingHom hJr hM) x m = x • m := by
  let := limRing (hJ := hJ) hJr
  intro M hM x m
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hg : IsLocallyConstant fun x : (quotients J hJ).lim ↦ x • m :=
    (IsLocallyConstant.iff_continuous _).2 (discreteModules_iff.1 hM m)
  exact (congrFun (eq_limSmul_of_isLocallyConstant
    (smoothModules_restrictScalars_toLimRingHom hJr hM) hg
    fun a ↦ ((ModuleCat.restrictScalars.smul_def (toLimRingHom hJr) a m).trans
      (by rw [coe_toLimRingHom])).symm) x).symm

/-- **Smooth `A`-modules are discrete modules over the completion** `lim A ⧸ Jₙ`, through the
action `TauCeti.ModuleTower.limSmul`, with the same underlying linear maps. -/
@[expose]
def smoothModulesToDiscrete :
    letI := limRing (hJ := hJ) hJr
    (smoothModules.{w} J).FullSubcategory ⥤
      (discreteModules.{w} (quotients J hJ).lim).FullSubcategory :=
  letI := limRing (hJ := hJ) hJr
  { obj M :=
      letI := limModule hJr M.property
      ⟨ModuleCat.of _ M.obj, discreteModules_limModule hJr M.property⟩
    map {M N} f :=
      letI := limModule hJr M.property
      letI := limModule hJr N.property
      ObjectProperty.homMk <| ModuleCat.ofHom
        { toFun := f.hom.hom
          map_add' := map_add f.hom.hom
          map_smul' x m := map_limSmul M.property N.property f.hom.hom x m } }

/-- The completion acts on the image of a smooth module through
`TauCeti.ModuleTower.limSmul`. -/
theorem smoothModulesToDiscrete_obj_smul (M : (smoothModules.{w} J).FullSubcategory)
    (x : (quotients J hJ).lim) (m : ((smoothModulesToDiscrete hJr).obj M).obj) :
    letI := limRing (hJ := hJ) hJr
    x • m = limSmul M.property x m :=
  (rfl)

/-- The image of a linear map of smooth modules is the same map. -/
@[simp]
theorem smoothModulesToDiscrete_map_hom_apply {M N : (smoothModules.{w} J).FullSubcategory}
    (f : M ⟶ N) (m : ((smoothModulesToDiscrete (hJ := hJ) hJr).obj M).obj) :
    letI := limRing (hJ := hJ) hJr
    ((smoothModulesToDiscrete hJr).map f).hom m = f.hom m :=
  (rfl)

/-- **Restriction of discrete modules over the completion** `lim A ⧸ Jₙ` along the canonical ring
homomorphism `A → lim A ⧸ Jₙ`, which lands in smooth `A`-modules. -/
@[expose]
def discreteModulesToSmooth :
    letI := limRing (hJ := hJ) hJr
    (discreteModules.{w} (quotients J hJ).lim).FullSubcategory ⥤
      (smoothModules.{w} J).FullSubcategory :=
  letI := limRing (hJ := hJ) hJr
  (smoothModules J).lift ((discreteModules _).ι ⋙ ModuleCat.restrictScalars (toLimRingHom hJr))
    fun M ↦ smoothModules_restrictScalars_toLimRingHom hJr M.property

/-- An element of `A` acts on the restriction of a discrete module over the completion through its
image in the completion. -/
theorem discreteModulesToSmooth_obj_smul :
    letI := limRing (hJ := hJ) hJr
    ∀ (M : (discreteModules.{w} (quotients J hJ).lim).FullSubcategory) (a : A)
      (m : ((discreteModulesToSmooth hJr).obj M).obj),
      a • m = toLimQuotients J hJ a • show M.obj from m :=
  let := limRing (hJ := hJ) hJr
  fun _ a m ↦ (ModuleCat.restrictScalars.smul_def (toLimRingHom hJr) a m).trans
    (by rw [coe_toLimRingHom])

/-- The restriction of a linear map of discrete modules over the completion is the same map. -/
@[simp]
theorem discreteModulesToSmooth_map_hom_apply :
    letI := limRing (hJ := hJ) hJr
    ∀ {M N : (discreteModules.{w} (quotients J hJ).lim).FullSubcategory} (f : M ⟶ N)
      (m : ((discreteModulesToSmooth hJr).obj M).obj),
      ((discreteModulesToSmooth hJr).map f).hom m = f.hom m :=
  fun _ _ ↦ (rfl)

/-- **Smooth modules are the discrete modules over the completion.** For a decreasing family of
left ideals `Jₙ` of `A` with the right-shift estimate, extending the action of `A` to
`lim A ⧸ Jₙ` (`TauCeti.ModuleTower.smoothModulesToDiscrete`) is an equivalence from the category of
`A`-modules smooth for `J` to the category of discrete `lim A ⧸ Jₙ`-modules, with inverse the
restriction of scalars `TauCeti.ModuleTower.discreteModulesToSmooth`. -/
@[expose]
def smoothModulesEquivalence :
    letI := limRing (hJ := hJ) hJr
    (smoothModules.{w} J).FullSubcategory ≌
      (discreteModules.{w} (quotients J hJ).lim).FullSubcategory :=
  letI := limRing (hJ := hJ) hJr
  -- Both composites have the same underlying abelian groups as the identity, so the unit and
  -- counit are identity maps; the explicit instances name the two module structures compared.
  CategoryTheory.Equivalence.mk (smoothModulesToDiscrete hJr) (discreteModulesToSmooth hJr)
    (NatIso.ofComponents
      (fun M ↦ ObjectProperty.isoMk _ <| LinearEquiv.toModuleIso <|
        @AddEquiv.toLinearEquiv _ _ _ _ _ _ M.obj.isModule
          ((discreteModulesToSmooth hJr).obj ((smoothModulesToDiscrete hJr).obj M)).obj.isModule
          (AddEquiv.refl M.obj) fun a m ↦
            ((discreteModulesToSmooth_obj_smul hJr ((smoothModulesToDiscrete hJr).obj M) a m).trans
              ((smoothModulesToDiscrete_obj_smul hJr M _ m).trans
                (limSmul_toLimQuotients M.property a m))).symm)
      fun _ ↦ rfl)
    (NatIso.ofComponents
      (fun M ↦ ObjectProperty.isoMk _ <| LinearEquiv.toModuleIso <|
        @AddEquiv.toLinearEquiv _ _ _ _ _ _
          ((smoothModulesToDiscrete hJr).obj ((discreteModulesToSmooth hJr).obj M)).obj.isModule
          M.obj.isModule (AddEquiv.refl M.obj)
          fun x m ↦ (smoothModulesToDiscrete_obj_smul hJr _ x m).trans
            (limSmul_restrictScalars_toLimRingHom hJr M.property x m))
      fun _ ↦ rfl)

/-- The functor of the equivalence extends the action of `A` to the completion. -/
@[simp]
theorem smoothModulesEquivalence_functor :
    (smoothModulesEquivalence (hJ := hJ) hJr).functor = smoothModulesToDiscrete hJr :=
  (rfl)

/-- The inverse of the equivalence restricts the action of the completion to `A`. -/
@[simp]
theorem smoothModulesEquivalence_inverse :
    (smoothModulesEquivalence (hJ := hJ) hJr).inverse = discreteModulesToSmooth hJr :=
  (rfl)

/-- The unit of the equivalence is the identity on the underlying abelian group. -/
@[simp]
theorem smoothModulesEquivalence_unitIso_hom_app_hom_apply
    (M : (smoothModules.{w} J).FullSubcategory) (m : M.obj) :
    dsimp% ((smoothModulesEquivalence (hJ := hJ) hJr).unitIso.hom.app M).hom m = m :=
  (rfl)

/-- The inverse of the unit of the equivalence is the identity on the underlying abelian group. -/
@[simp]
theorem smoothModulesEquivalence_unitIso_inv_app_hom_apply
    (M : (smoothModules.{w} J).FullSubcategory)
    (m : ((smoothModulesEquivalence (hJ := hJ) hJr).inverse.obj
      ((smoothModulesEquivalence hJr).functor.obj M)).obj) :
    dsimp% ((smoothModulesEquivalence hJr).unitIso.inv.app M).hom m = show M.obj from m :=
  (rfl)

/-- The counit of the equivalence is the identity on the underlying abelian group. -/
@[simp]
theorem smoothModulesEquivalence_counitIso_hom_app_hom_apply :
    letI := limRing (hJ := hJ) hJr
    ∀ (M : (discreteModules.{w} (quotients J hJ).lim).FullSubcategory)
      (m : ((smoothModulesEquivalence hJr).functor.obj
        ((smoothModulesEquivalence hJr).inverse.obj M)).obj),
      dsimp% ((smoothModulesEquivalence hJr).counitIso.hom.app M).hom m = show M.obj from m :=
  fun _ _ ↦ (rfl)

/-- The inverse of the counit of the equivalence is the identity on the underlying abelian
group. -/
@[simp]
theorem smoothModulesEquivalence_counitIso_inv_app_hom_apply :
    letI := limRing (hJ := hJ) hJr
    ∀ (M : (discreteModules.{w} (quotients J hJ).lim).FullSubcategory) (m : M.obj),
      dsimp% ((smoothModulesEquivalence hJr).counitIso.inv.app M).hom m = m :=
  fun _ _ ↦ (rfl)

end TauCeti.ModuleTower
