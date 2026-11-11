/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Basic
public import TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.Modules.Localization

/-!
# The ideal sheaf of an effective Cartier divisor

Let `D` be an effective Cartier divisor on an integral scheme `X`, given by local equations which
are regular functions. Then `𝒪_X(-D) ⊆ 𝒦_X` lies inside `𝒪_X`, and over an open subset `U` its
sections are the regular functions `a` with `a / f` regular at every point `x` of `U`, for `f` a
local equation of `D` at `x`. These sections form an ideal sheaf `I_D ⊆ 𝒪_X`, quasi-coherent
because `𝒪_X(-D)` is: over a basic open `D(g)` of an affine open `U`, the sections of `𝒪_X(-D)`
are the localization at `g` of those over `U`. Near each point `I_D` is generated on an affine
open by a regular local equation `a` of `D`, a nonzerodivisor since `X` is integral, so `I_D` is
an effective Cartier ideal sheaf in the sense of `Scheme.IdealSheafData.IsEffectiveCartier`, and
`I_D ≅ 𝒪_X(-D)`.

This identifies the two notions of effective Cartier divisor on an integral scheme, by local
equations in the function field and by locally principal ideal sheaves, and with it their line
bundles: the class of the ideal sheaf `I_D` is the inverse of the class of `𝒪_X(D)`. The degree
and intersection-number formulas proved for effective Cartier ideal sheaves, such as
`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf`, therefore apply
to the line bundles `𝒪_X(D)` of effective Cartier divisors.

## Main definitions

* `Scheme.CartierDivisor.IsEffective.sectionsIdealSheaf`: the ideal sheaf `I_D` of an effective
  Cartier divisor `D`, defined through its sections.
* `Scheme.CartierDivisor.IsEffective.sectionsIdealSheafIso`: the isomorphism `I_D ≅ 𝒪_X(-D)`,
  compatible with the inclusions into the sheaf `𝒦_X` of rational functions.

## Main results

* `Scheme.CartierDivisor.IsEffective.mem_sections_sectionsIdealSheaf_iff`: the sections of `I_D`
  over an open subset `U` are the regular functions which are sections of `𝒪_X(-D)`.
* `Scheme.CartierDivisor.IsEffective.isEffectiveCartier_sectionsIdealSheaf`: `I_D` is an effective
  Cartier ideal sheaf.
* `Scheme.CartierDivisor.IsEffective.mk_toInvertibleSheaf_sectionsIdealSheaf`: the line-bundle
  class of `I_D` is the inverse of that of `𝒪_X(D)`.

## References

* The Stacks Project, *Divisors*, Section *Effective Cartier divisors* (Tag 01WQ), where an
  effective Cartier divisor is a closed subscheme whose ideal sheaf is invertible, and Section
  *Meromorphic functions and sections*, where it corresponds to a Cartier divisor with regular
  local equations.
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Remark 6.17.1 and Proposition 6.18: on an
  integral scheme, Cartier divisors with regular local equations correspond to locally principal
  closed subschemes, and `𝒪_X(-D)` is the ideal sheaf of `D`.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X] {D : CartierDivisor X}

/-- **Sections of `𝒪_X(-D)` are regular.** If `D` is effective, every section of `𝒪_X(-D)` over
an open subset `U` is a regular function on `U`. -/
theorem IsEffective.exists_toRationalFunctions_app_eq (hD : D.IsEffective) {U : X.Opens}
    {s : Γ(rationalFunctions X, U)} (hs : s ∈ (-D).sections U) :
    ∃ a : Γ(X, U), Scheme.Modules.Hom.app (toRationalFunctions X) U a = s := by
  rcases isEmpty_or_nonempty U with hU | hU
  · -- Over the empty set there are no nonzero rational functions.
    have hbot : U = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU)
    have := subsingleton_rationalFunctions U hbot
    exact ⟨0, Subsingleton.elim _ _⟩
  · -- At `y ∈ U`, with `f` a regular local equation of `D`, `s = f · (f⁻¹ s)` is regular.
    obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_mem_range
      (f := rationalFunctionsEquiv U s) fun y hy ↦ by
        obtain ⟨f, hf, hfy⟩ := isEffective_iff_exists.mp hD y
        have h := Subring.mul_mem _ hfy (mem_sections.mp hs y hy f⁻¹ hf.inv)
        rwa [← mul_assoc, Units.mul_inv, one_mul] at h
    exact ⟨a, (rationalFunctionsEquiv U).injective
      (by rw [rationalFunctionsEquiv_toRationalFunctions_app, ha])⟩

/-- The ideal of the regular functions on `U` which are sections of `𝒪_X(-D)`. -/
private def sectionsIdeal (D : CartierDivisor X) (U : X.Opens) : Ideal Γ(X, U) where
  carrier := {a | Scheme.Modules.Hom.app (toRationalFunctions X) U a ∈ (-D).sections U}
  -- `rw [map_add]` fails here: the structure sheaf `𝒪_X` appears as `SheafOfModules.unit`, which
  -- `rw` does not see to be an object of `X.Modules`, so the equations are transported by hand.
  add_mem' {a b} ha hb := (congrArg (· ∈ (-D).sections U)
    (map_add (Scheme.Modules.Hom.app (toRationalFunctions X) U).hom a b)).mpr (add_mem ha hb)
  zero_mem' := (congrArg (· ∈ (-D).sections U)
    (map_zero (Scheme.Modules.Hom.app (toRationalFunctions X) U).hom)).mpr (zero_mem _)
  smul_mem' r a ha := (congrArg (· ∈ (-D).sections U)
    (Scheme.Modules.Hom.app_smul (M := SheafOfModules.unit X.ringCatSheaf) _ r a)).mpr
      (Submodule.smul_mem _ r ha)

private lemma mem_sectionsIdeal_iff {U : X.Opens} {a : Γ(X, U)} :
    a ∈ sectionsIdeal D U ↔
      Scheme.Modules.Hom.app (toRationalFunctions X) U a ∈ (-D).sections U :=
  Iff.rfl

private lemma map_mem_sectionsIdeal {U V : X.Opens} (i : V ⟶ U) {a : Γ(X, U)}
    (ha : a ∈ sectionsIdeal D U) : X.presheaf.map i.op a ∈ sectionsIdeal D V := by
  rw [mem_sectionsIdeal_iff, toRationalFunctions_app_map]
  exact sections_map i ha

/-- Over a basic open `D(g)` of an affine open `U`, the regular sections of `𝒪_X(-D)` are the
localization at `g` of those over `U`, because `𝒪_X(-D)` is quasi-coherent. -/
private lemma map_sectionsIdeal_basicOpen (hD : D.IsEffective) (U : X.affineOpens)
    (g : Γ(X, U)) :
    (sectionsIdeal D U).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom =
      sectionsIdeal D (X.basicOpen g) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ map_mem_sectionsIdeal _ ha) ?_
  intro b hb
  set ρ := X.presheaf.map (homOfLE (X.basicOpen_le g)).op
  have : (-D).sheaf.IsQuasicoherent :=
    (-D).toInvertibleSheaf_obj ▸ InvertibleSheaf.isQuasicoherent_obj (-D).toInvertibleSheaf
  -- Rewriting inside images under `𝒪_X ⟶ 𝒦_X` fails for the reason recorded at `sectionsIdeal`,
  -- so the equations between them are chained with `Eq.trans` below.
  obtain ⟨tb, htb⟩ : ∃ tb, Scheme.Modules.Hom.app (-D).sheafι (X.basicOpen g) tb =
      Scheme.Modules.Hom.app (toRationalFunctions X) (X.basicOpen g) b :=
    (Set.ext_iff.mp ((-D).range_sheafι_app (X.basicOpen g)) _).mpr hb
  -- Some `gⁿ b` extends to a section `t₀` of `𝒪_X(-D)` over `U`, by quasi-coherence.
  obtain ⟨n, t₀, ht⟩ := (-D).sheaf.exists_pow_smul_eq_map U.2 g rfl (X.basicOpen_le g) tb
  obtain ⟨a₀, ha₀⟩ := hD.exists_toRationalFunctions_app_eq ((-D).sheafι_app_mem U t₀)
  have ha₀I : a₀ ∈ sectionsIdeal D U :=
    (congrArg (· ∈ (-D).sections U) ha₀).mpr ((-D).sheafι_app_mem U t₀)
  -- Then `gⁿ b` is the restriction of `a₀`, as one checks inside `𝒦_X`.
  have hgb : ρ g ^ n * b = ρ a₀ := by
    refine toRationalFunctions_app_injective _ ?_
    -- `ht` says `gⁿ • b = t₀|_{D(g)}` in `𝒪_X(-D)`; its image in `𝒦_X` is the claim.
    have h := congrArg (Scheme.Modules.Hom.app (-D).sheafι (X.basicOpen g)) ht
    rw [Scheme.Modules.Hom.app_smul, ← Scheme.Modules.mapPresheaf_app,
      (-D).sheafι.mapPresheaf.naturality_apply, Scheme.Modules.mapPresheaf_app] at h
    exact (Scheme.Modules.Hom.app_smul (M := SheafOfModules.unit X.ringCatSheaf) _ _ b).trans
      ((congrArg (ρ g ^ n • ·) htb.symm).trans (h.trans
        ((congrArg ((rationalFunctions X).presheaf.map _) ha₀.symm).trans
          (toRationalFunctions_app_map _ a₀).symm)))
  have hu : IsUnit (ρ g ^ n) := (X.toRingedSpace.isUnit_res_basicOpen g).pow n
  rw [← Ideal.unit_mul_mem_iff_mem _ hu, hgb]
  exact Ideal.mem_map_of_mem _ ha₀I

/-- **The ideal sheaf of an effective Cartier divisor.** For an effective Cartier divisor `D` on an
integral scheme, the ideal sheaf `I_D ⊆ 𝒪_X` whose sections over an affine open `U` are the regular
functions on `U` which are sections of `𝒪_X(-D) ⊆ 𝒦_X`: near a point with regular local equation
`f`, the multiples of `f`. -/
def IsEffective.sectionsIdealSheaf (hD : D.IsEffective) : X.IdealSheafData where
  ideal U := sectionsIdeal D U
  map_ideal_basicOpen U g := map_sectionsIdeal_basicOpen hD U g

/-- Over an affine open `U`, a regular function lies in the ideal sheaf of `D` exactly when it is a
section of `𝒪_X(-D)`. -/
@[simp]
theorem IsEffective.mem_sectionsIdealSheaf_ideal_iff (hD : D.IsEffective) {U : X.affineOpens}
    {a : Γ(X, U)} :
    a ∈ hD.sectionsIdealSheaf.ideal U ↔
      Scheme.Modules.Hom.app (toRationalFunctions X) U a ∈ (-D).sections U :=
  Iff.rfl

/-- **The sections of the ideal sheaf of `D`.** Over every open subset `U`, a regular function lies
in the ideal sheaf of `D` exactly when it is a section of `𝒪_X(-D)`. -/
@[simp]
theorem IsEffective.mem_sections_sectionsIdealSheaf_iff (hD : D.IsEffective) {U : X.Opens}
    {a : Γ(X, U)} :
    a ∈ hD.sectionsIdealSheaf.sections U ↔
      Scheme.Modules.Hom.app (toRationalFunctions X) U a ∈ (-D).sections U := by
  constructor
  · -- Both conditions are local: test the one for `𝒪_X(-D)` on affine neighbourhoods.
    refine fun ha ↦ mem_sections.mpr fun x hx f hf ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    have haV := hD.sectionsIdealSheaf.map_mem_sections (homOfLE hVU) ha
    rw [Scheme.IdealSheafData.sections_eq_ideal (U := ⟨V, hV⟩), mem_sectionsIdealSheaf_ideal_iff,
      toRationalFunctions_app_map] at haV
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    have h := mem_sections.mp haV x hxV f hf
    rwa [rationalFunctionsEquiv_map] at h
  · intro ha
    refine hD.sectionsIdealSheaf.mem_sections_of_forall_exists fun x hx ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    refine ⟨V, homOfLE hVU, hxV, ?_⟩
    rw [Scheme.IdealSheafData.sections_eq_ideal (U := ⟨V, hV⟩)]
    exact map_mem_sectionsIdeal (homOfLE hVU) ha

/-- **The ideal sheaf of an effective Cartier divisor is effective Cartier.** Near every point it
is generated, on an affine open, by a regular local equation of `D`, a nonzerodivisor since `X` is
integral. -/
theorem IsEffective.isEffectiveCartier_sectionsIdealSheaf (hD : D.IsEffective) :
    hD.sectionsIdealSheaf.IsEffectiveCartier := by
  refine (Scheme.IdealSheafData.isEffectiveCartier_iff _).mpr fun x ↦ ?_
  -- A regular local equation `f` of `D` at `x` is the germ of a regular function `c'` on `W`.
  obtain ⟨f, hf, c, hc⟩ := isEffective_iff_exists.mp hD x
  obtain ⟨W, hxW, c', rfl⟩ := X.presheaf.exists_germ_eq c
  obtain ⟨V, hxV, hV⟩ := isLocalEquationAt_iff.mp hf.inv
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (⟨hxV, hxW⟩ : x ∈ V ⊓ W) (V ⊓ W).isOpen
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  set a := X.presheaf.map (homOfLE (hUVW.trans inf_le_right)).op c'
  have ha : X.germToFunctionField U a = f := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hxU, ← hc]
    exact congrArg _ (X.presheaf.germ_res_apply _ x hxU c')
  have ha0 : a ≠ 0 := fun h ↦ f.ne_zero (by rw [← ha, h, map_zero])
  refine ⟨⟨U, hU⟩, hxU, a, IsSMulRegular.of_ne_zero ha0, ?_⟩
  -- Over `U ⊆ V`, `f⁻¹` is an equation of `-D`, so `b` lies in the ideal iff `f⁻¹ b` is regular.
  ext b
  rw [mem_sectionsIdealSheaf_ideal_iff, mem_sections_iff_of_rationalUnitClass_eq
    (hUVW.trans inf_le_left) hV, rationalFunctionsEquiv_toRationalFunctions_app,
    Ideal.mem_span_singleton']
  refine exists_congr fun d ↦ ?_
  rw [← (X.germToFunctionField_injective U).eq_iff, map_mul, ha, Units.val_inv_eq_inv_val,
    eq_inv_mul_iff_mul_eq₀ f.ne_zero, mul_comm]

/-- The inclusion `I_D ⟶ 𝒦_X` of the ideal sheaf of `D`, through `𝒪_X`, takes values in
`𝒪_X(-D)`. -/
private lemma sheafι_comp_toRationalFunctions_app_mem (hD : D.IsEffective) (U : X.Opens)
    (t : Γ(hD.sectionsIdealSheaf.sheaf, U)) :
    Scheme.Modules.Hom.app (hD.sectionsIdealSheaf.sheafι ≫ toRationalFunctions X) U t ∈
      (-D).sections U := by
  rw [Scheme.Modules.Hom.comp_app (N := SheafOfModules.unit X.ringCatSheaf),
    ConcreteCategory.comp_apply]
  exact hD.mem_sections_sectionsIdealSheaf_iff.mp (hD.sectionsIdealSheaf.sheafι_app_mem U t)

/-- **The ideal sheaf of `D` is `𝒪_X(-D)`.** For an effective Cartier divisor `D` on an integral
scheme, the inclusion of the ideal sheaf `I_D ⊆ 𝒪_X ⊆ 𝒦_X` is an isomorphism onto `𝒪_X(-D)`
(`IsEffective.sectionsIdealSheafIso_hom_sheafι`). -/
def IsEffective.sectionsIdealSheafIso (hD : D.IsEffective) :
    hD.sectionsIdealSheaf.sheaf ≅ (-D).sheaf :=
  haveI : IsIso ((-D).sheafLift (hD.sectionsIdealSheaf.sheafι ≫ toRationalFunctions X)
      (sheafι_comp_toRationalFunctions_app_mem hD)) := by
    refine isIso_sheafLift _ _ _ (fun U ↦ ?_) fun U s hs ↦ ?_
    · rw [Scheme.Modules.Hom.comp_app (N := SheafOfModules.unit X.ringCatSheaf),
        ConcreteCategory.coe_comp]
      exact (toRationalFunctions_app_injective U).comp
        (hD.sectionsIdealSheaf.sheafι_app_injective U)
    · obtain ⟨a, rfl⟩ := hD.exists_toRationalFunctions_app_eq hs
      refine ⟨hD.sectionsIdealSheaf.sectionMk a (hD.mem_sections_sectionsIdealSheaf_iff.mpr hs), ?_⟩
      rw [Scheme.Modules.Hom.comp_app (N := SheafOfModules.unit X.ringCatSheaf),
        ConcreteCategory.comp_apply, Scheme.IdealSheafData.sheafι_app_sectionMk]
  asIso ((-D).sheafLift (hD.sectionsIdealSheaf.sheafι ≫ toRationalFunctions X)
    (sheafι_comp_toRationalFunctions_app_mem hD))

/-- The isomorphism `I_D ≅ 𝒪_X(-D)` is compatible with the inclusions into `𝒦_X`: the ideal sheaf
includes into `𝒦_X` through `𝒪_X`. -/
@[reassoc (attr := simp)]
lemma IsEffective.sectionsIdealSheafIso_hom_sheafι (hD : D.IsEffective) :
    hD.sectionsIdealSheafIso.hom ≫ (-D).sheafι =
      hD.sectionsIdealSheaf.sheafι ≫ toRationalFunctions X :=
  sheafLift_ι _ _ _

/-- **The line bundle of the ideal sheaf of `D`.** The class of the invertible ideal sheaf
`I_D = 𝒪_X(-D)` of an effective Cartier divisor `D` is the inverse of the class of `𝒪_X(D)`. -/
@[simp]
theorem IsEffective.mk_toInvertibleSheaf_sectionsIdealSheaf (hD : D.IsEffective) :
    LineBundleClass.mk hD.isEffectiveCartier_sectionsIdealSheaf.toInvertibleSheaf =
      D.toLineBundleClass⁻¹ := by
  rw [← toLineBundleClass_neg, eq_comm, toLineBundleClass_eq_mk_iff,
    Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]
  exact ⟨hD.sectionsIdealSheafIso.symm⟩

end Scheme.CartierDivisor

end

end AlgebraicGeometry

end TauCeti
