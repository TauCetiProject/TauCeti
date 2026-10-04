/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Hilbert90
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic

/-!
# The formation of the units of a separable closure

For a field `K` with separable closure `Kˢ` and absolute Galois group `G_K = Gal(Kˢ/K)`, this file
builds the **formation** `unitsFormation K` whose coefficient module is the multiplicative group
`(Kˢ)ˣ`, written additively. Its level at an open subgroup `U` is the unit group of the fixed field
of `U` (`mem_level_unitsFormation_iff`), presented as `Eˣ` when that fixed field is the image of a
`K`-embedding of `E` (`unitsLevelEquiv`), and its finite normal layers are the finite Galois
extensions `E/F` inside `Kˢ`. It is the formation on which the local class formation is to be
built.

For a finite extension `L/K` embedded in `Kˢ`, restriction of this formation from `G_K` to the
open subgroup identified with `G_L` is canonically isomorphic to `unitsFormation L`
(`localFormationRestrict`). On coefficients this isomorphism is induced by the identification
`Lˢ ≃ Kˢ` extending the chosen embedding.

The first input of the class-formation axioms is proved here, for every field `K`: **Hilbert 90 on
every finite normal layer** (`subsingleton_h1_unitsFormation`), `H¹(U ⧸ V, ((Kˢ)ˣ)^V) = 0` for
open subgroups `V ◁ U`. The finite-layer description of the Brauer group through this formation is
in `TauCeti.NumberTheory.ClassFieldTheory.Brauer.Formation`.

## Implementation notes

The body of `unitsFormation` is not exposed; its coefficient module is read through the dictionary
`unitsCoeffEquivUnitsFormation`, as `TauCeti.ClassFieldTheory.unitsRep` is read through
`TauCeti.ClassFieldTheory.unitsCoeffEquivUnitsRep`.

## Main definitions

* `TauCeti.ClassFieldTheory.unitsFormation K`: the formation of `(Kˢ)ˣ` over `G_K`.
* `TauCeti.ClassFieldTheory.unitsCoeffEquivUnitsFormation K`: its coefficient module as
  `TauCeti.UnitsCoeff K`.
* `TauCeti.ClassFieldTheory.localFormationRestrict K L σ`: restriction from `G_K` to `G_L` as
  an isomorphism of topological representations.
* `TauCeti.ClassFieldTheory.unitsLevelEquiv ι hU`: the level of an open subgroup `U` whose fixed
  field is the image of `ι : E →ₐ[K] Kˢ` is `Eˣ`.
* `TauCeti.ClassFieldTheory.layerCoeffEquiv L`: the coefficient module of a finite normal layer
  `V ◁ U` is the subgroup `((Kˢ)ˣ)^V` of `(Kˢ)ˣ`.

## Main results

* `TauCeti.ClassFieldTheory.mem_level_unitsFormation_iff`: the level of an open subgroup is the
  unit group of its fixed field.
* `TauCeti.ClassFieldTheory.subsingleton_h1_unitsFormation`: `H¹` of every finite normal layer
  vanishes.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J.-P. Serre, *Local Fields*, Chapter X, §1, and Chapter XI, §1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open groupCohomology ContCohomology

variable (K : Type) [Field K]

/-- **The formation of the units of a separable closure**: the discrete module `(Kˢ)ˣ`, written
additively as `TauCeti.UnitsCoeff K`, over the absolute Galois group `G_K = Gal(Kˢ/K)`. Its
elements are read through `unitsCoeffEquivUnitsFormation`, and its level at an open subgroup is
the unit group of the fixed field of that subgroup (`mem_level_unitsFormation_iff`). -/
def unitsFormation : Formation (AbsoluteGaloisGroup K) :=
  ⟨ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K),
    ofDiscreteModule_isSmoothDiscrete ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)⟩

/-- **The coefficient dictionary** between `TauCeti.UnitsCoeff K` and the coefficient module of
`unitsFormation K`. It is equivariant by `unitsCoeffEquivUnitsFormation_smul`. -/
def unitsCoeffEquivUnitsFormation : UnitsCoeff K ≃+ (unitsFormation K).toRep.V :=
  AddEquiv.refl _

/-- **The coefficient dictionary is equivariant**: `G_K` acts on the coefficient module of
`unitsFormation K` as it acts on `(Kˢ)ˣ`. -/
@[simp]
theorem unitsCoeffEquivUnitsFormation_smul (g : AbsoluteGaloisGroup K) (x : UnitsCoeff K) :
    unitsCoeffEquivUnitsFormation K (g • x) =
      (unitsFormation K).toRep.ρ g (unitsCoeffEquivUnitsFormation K x) :=
  (rfl)

/-! ### Restriction to a finite extension -/

section Restriction

open CategoryTheory

variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- The homomorphism `G_L → G_K` obtained by identifying `G_L` with the subgroup fixing `σ(L)`
and including that subgroup in `G_K`. -/
def localFormationHom : AbsoluteGaloisGroup L →* AbsoluteGaloisGroup K :=
  (TauCeti.galoisSubgroup K L σ).toSubgroup.subtype.comp
    (TauCeti.galoisSubgroupEquiv K L σ).toMulEquiv.toMonoidHom

/-- The additive equivalence on the coefficient modules underlying restriction of the units
formation along `L/K`. It sends a unit of `Kˢ` to its image in `Lˢ` under the inverse of the
chosen identification `Lˢ ≃ Kˢ`. -/
def localFormationCoeffEquiv : UnitsCoeff K ≃+ UnitsCoeff L :=
  (Units.mapEquiv (separableClosureRingEquiv K L σ).symm.toMulEquiv).toAdditive

/-- The coefficient equivalence underlying `localFormationRestrict` is equivariant for the
embedding `G_L → G_K`. -/
@[simp]
theorem localFormationCoeffEquiv_smul (g : AbsoluteGaloisGroup L) (x : UnitsCoeff K) :
    localFormationCoeffEquiv K L σ ((localFormationHom K L σ g) • x) =
      g • localFormationCoeffEquiv K L σ x := by
  refine Additive.toMul.injective (Units.ext ?_)
  simp [localFormationCoeffEquiv, localFormationHom, AlgEquiv.smul_units_def,
    TauCeti.galoisSubgroupEquiv_apply]

/-- **Restriction of the units formation to a finite extension.** A `K`-embedding
`σ : L →ₐ[K] Kˢ` identifies `G_L` with the open subgroup of `G_K` fixing `σ(L)`. After restricting
the `G_K`-representation `(Kˢ)ˣ` along this embedding, the inverse of
`separableClosureRingEquiv K L σ : Lˢ ≃+* Kˢ` identifies it with the `G_L`-representation
`(Lˢ)ˣ`. This is the coefficient comparison used to regard a finite layer over `L` as a layer of
the formation over `K`. -/
def localFormationRestrict :
    TopRep.res (localFormationHom K L σ) (unitsFormation K).module ≅
      (unitsFormation L).module := by
  let e : UnitsCoeff K ≃ₗ[ℤ] UnitsCoeff L :=
    (localFormationCoeffEquiv K L σ).toIntLinearEquiv
  let ec : UnitsCoeff K ≃L[ℤ] UnitsCoeff L :=
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  let er :
      (TopRep.res (localFormationHom K L σ) (unitsFormation K).module).ρ.Equiv
        (unitsFormation L).module.ρ :=
    ContRepresentation.Equiv.mk ec fun g => ContinuousLinearMap.ext fun x =>
      localFormationCoeffEquiv_smul K L σ g x
  exact
    { hom := TopRep.ofHom er.toContIntertwiningMap
      inv := TopRep.ofHom er.symm.toContIntertwiningMap
      hom_inv_id := by
        apply TopRep.hom_ext
        ext x
        exact er.symm_apply_apply x
      inv_hom_id := by
        apply TopRep.hom_ext
        ext x
        exact er.apply_symm_apply x }

/-- `localFormationRestrict` sends a coefficient `x ∈ (Kˢ)ˣ` to its image in `(Lˢ)ˣ` under the
inverse identification of separable closures. -/
@[simp]
theorem localFormationRestrict_hom_apply (x : UnitsCoeff K) :
    (dsimp% only
      ((localFormationRestrict K L σ).hom (unitsCoeffEquivUnitsFormation K x) :
        (unitsFormation L).module.V)) =
      unitsCoeffEquivUnitsFormation L (localFormationCoeffEquiv K L σ x) :=
  (rfl)

/-- The inverse of `localFormationRestrict` sends a coefficient `y ∈ (Lˢ)ˣ` along the chosen
identification `Lˢ ≃ Kˢ`. -/
@[simp]
theorem localFormationRestrict_inv_apply (y : UnitsCoeff L) :
    (dsimp% only
      ((localFormationRestrict K L σ).inv (unitsCoeffEquivUnitsFormation L y) :
        (unitsFormation K).module.V)) =
      unitsCoeffEquivUnitsFormation K ((localFormationCoeffEquiv K L σ).symm y) :=
  (rfl)

end Restriction

variable {K}

/-- The inverse of the coefficient dictionary is equivariant. -/
private theorem unitsCoeffEquivUnitsFormation_symm_ρ (g : AbsoluteGaloisGroup K)
    (x : (unitsFormation K).toRep.V) :
    (unitsCoeffEquivUnitsFormation K).symm ((unitsFormation K).toRep.ρ g x) =
      g • (unitsCoeffEquivUnitsFormation K).symm x :=
  (rfl)

/-- **The level of an open subgroup `U` is the unit group of its fixed field**: a unit of `Kˢ`
lies in the level `((Kˢ)ˣ)^U` exactly when it lies in the fixed field of `U`. Its `simp` priority
is high so that `simp` uses it in preference to the generic `Formation.mem_level`. -/
@[simp high]
theorem mem_level_unitsFormation_iff {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    {x : UnitsCoeff K} :
    (dsimp% only (unitsCoeffEquivUnitsFormation K x ∈ (unitsFormation K).level U)) ↔
      ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) ∈
        IntermediateField.fixedField U.toSubgroup := by
  rw [Formation.mem_level, IntermediateField.mem_fixedField_iff]
  refine forall₂_congr fun u _ => ?_
  rw [← unitsCoeffEquivUnitsFormation_smul, (unitsCoeffEquivUnitsFormation K).injective.eq_iff,
    ← Additive.toMul.injective.eq_iff, Units.ext_iff]
  rfl

/-! ### Levels as unit groups of embedded fields -/

section Level

open IntermediateField

variable {E : Type*} [Field E] [Algebra K E]

/-- The image of a `K`-embedding of a unit of `E` lies in the level of an open subgroup whose
fixed field is the image of the embedding. -/
private theorem unitsCoeffEquivUnitsFormation_map_mem_level (ι : E →ₐ[K] SeparableClosure K)
    {U : OpenSubgroup (AbsoluteGaloisGroup K)} (hU : fixedField U.toSubgroup = ι.fieldRange)
    (x : Eˣ) :
    unitsCoeffEquivUnitsFormation K (Additive.ofMul (Units.map (ι : E →* SeparableClosure K) x))
      ∈ (unitsFormation K).level U := by
  rw [mem_level_unitsFormation_iff, hU]
  exact ⟨x, rfl⟩

/-- The additive map `Eˣ → ((Kˢ)ˣ)^U` underlying `unitsLevelEquiv`. -/
private def unitsLevelHom (ι : E →ₐ[K] SeparableClosure K)
    {U : OpenSubgroup (AbsoluteGaloisGroup K)} (hU : fixedField U.toSubgroup = ι.fieldRange) :
    Additive Eˣ →+ (unitsFormation K).level U :=
  AddMonoidHom.codRestrict ((unitsCoeffEquivUnitsFormation K).toAddMonoidHom.comp
      (Units.map (ι : E →* SeparableClosure K)).toAdditive) _
    (unitsCoeffEquivUnitsFormation_map_mem_level ι hU)

private theorem coe_unitsLevelHom (ι : E →ₐ[K] SeparableClosure K)
    {U : OpenSubgroup (AbsoluteGaloisGroup K)} (hU : fixedField U.toSubgroup = ι.fieldRange)
    (x : Additive Eˣ) :
    ((unitsLevelHom ι hU x : (unitsFormation K).level U) : (unitsFormation K).toRep.V) =
      unitsCoeffEquivUnitsFormation K
        (Additive.ofMul (Units.map (ι : E →* SeparableClosure K) x.toMul)) :=
  (rfl)

private theorem bijective_unitsLevelHom (ι : E →ₐ[K] SeparableClosure K)
    {U : OpenSubgroup (AbsoluteGaloisGroup K)} (hU : fixedField U.toSubgroup = ι.fieldRange) :
    Function.Bijective (unitsLevelHom ι hU) := by
  refine ⟨fun x y h => ?_, fun z => ?_⟩
  · have h := congrArg Subtype.val h
    rw [coe_unitsLevelHom, coe_unitsLevelHom] at h
    exact Additive.toMul.injective <| Units.map_injective ι.injective <|
      Additive.ofMul.injective ((unitsCoeffEquivUnitsFormation K).injective h)
  · -- The unit underlying `z` lies in the fixed field of `U`, the image of `ι`.
    obtain ⟨z, hz⟩ := z
    obtain ⟨w, rfl⟩ := (unitsCoeffEquivUnitsFormation K).surjective z
    obtain ⟨e, he⟩ : ((w.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) ∈ ι.fieldRange := by
      rw [← hU, ← mem_level_unitsFormation_iff]
      exact hz
    have he0 : e ≠ 0 := fun h0 => w.toMul.ne_zero (by rw [← he, h0, map_zero])
    refine ⟨Additive.ofMul (Units.mk0 e he0), Subtype.ext ?_⟩
    rw [coe_unitsLevelHom]
    exact congrArg _ (Additive.toMul.injective (Units.ext he))

/-- **The level of an open subgroup is the unit group of its fixed field**, presented as `Eˣ`:
if the fixed field of `U` is the image of a `K`-embedding `ι : E →ₐ[K] Kˢ`, then `ι` identifies
`Eˣ` with the level `((Kˢ)ˣ)^U` of `unitsFormation K`. Applied to `K` itself and to a finite
Galois extension `L`, it identifies the ground and top levels of the layer of `L` with `Kˣ` and
`Lˣ`. -/
def unitsLevelEquiv (ι : E →ₐ[K] SeparableClosure K) {U : OpenSubgroup (AbsoluteGaloisGroup K)}
    (hU : fixedField U.toSubgroup = ι.fieldRange) :
    Additive Eˣ ≃+ (unitsFormation K).level U :=
  AddEquiv.ofBijective (unitsLevelHom ι hU) (bijective_unitsLevelHom ι hU)

/-- `unitsLevelEquiv ι hU` sends a unit `x` of `E` to the unit `ι x` of `Kˢ`. -/
@[simp]
theorem unitsLevelEquiv_apply_coe (ι : E →ₐ[K] SeparableClosure K)
    {U : OpenSubgroup (AbsoluteGaloisGroup K)} (hU : fixedField U.toSubgroup = ι.fieldRange)
    (x : Additive Eˣ) :
    (dsimp% only
      ((unitsLevelEquiv ι hU x : (unitsFormation K).level U) : (unitsFormation K).toRep.V)) =
      unitsCoeffEquivUnitsFormation K
        (Additive.ofMul (Units.map (ι : E →* SeparableClosure K) x.toMul)) :=
  (rfl)

end Level

/-! ### The coefficients of a finite normal layer -/

section LayerCoeff

variable (L : NormalLayer (AbsoluteGaloisGroup K))

/-- **The coefficient module of a layer** `V ◁ U` of the formation of units is the subgroup
`((Kˢ)ˣ)^V` of fixed points of its top subgroup, read as a subgroup of the ground subgroup `U`.
It moves no element of `(Kˢ)ˣ` (`layerCoeffEquiv_apply_coe`) and is equivariant for the Galois
group of the layer (`layerCoeffEquiv_ρ`). -/
def layerCoeffEquiv :
    (L.rep (unitsFormation K)).V ≃+
      FixedPoints.addSubgroup (L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
        (UnitsCoeff K) where
  toFun x := ⟨(unitsCoeffEquivUnitsFormation K).symm (x : (unitsFormation K).level L.top),
    (FixedPoints.mem_addSubgroup _ _ _).2 fun v =>
      (Formation.mem_level _).1 x.2 _ (Subgroup.mem_subgroupOf.1 v.2)⟩
  invFun m := ⟨unitsCoeffEquivUnitsFormation K m, (Formation.mem_level _).2 fun v hv =>
    (unitsCoeffEquivUnitsFormation_smul K v m).symm.trans <| congrArg _ <|
      (FixedPoints.mem_addSubgroup _ _ _).1 m.2 ⟨⟨v, L.top_le_ground hv⟩, hv⟩⟩
  left_inv _ := Subtype.ext ((unitsCoeffEquivUnitsFormation K).apply_symm_apply _)
  right_inv _ := Subtype.ext ((unitsCoeffEquivUnitsFormation K).symm_apply_apply _)
  map_add' _ _ := Subtype.ext (map_add (unitsCoeffEquivUnitsFormation K).symm _ _)

/-- `layerCoeffEquiv` moves no element of `(Kˢ)ˣ`: it only changes the coefficient dictionary. -/
@[simp]
theorem layerCoeffEquiv_apply_coe (x : (L.rep (unitsFormation K)).V) :
    (layerCoeffEquiv L x : UnitsCoeff K) =
      (unitsCoeffEquivUnitsFormation K).symm (x : (unitsFormation K).level L.top) :=
  (rfl)

/-- `layerCoeffEquiv` is equivariant for the Galois group of the layer. -/
@[simp]
theorem layerCoeffEquiv_ρ
    (g : L.ground.toSubgroup ⧸ L.top.toSubgroup.subgroupOf L.ground.toSubgroup)
    (x : (L.rep (unitsFormation K)).V) :
    layerCoeffEquiv L ((L.rep (unitsFormation K)).ρ g x) = g • layerCoeffEquiv L x := by
  induction g using QuotientGroup.induction_on with
  | H u =>
    refine Subtype.ext ?_
    rw [layerCoeffEquiv_apply_coe, coe_quotient_smul_fixedPoints_addSubgroup,
      coe_smul_fixedPoints_addSubgroup, layerCoeffEquiv_apply_coe, AddEquiv.symm_apply_eq,
      Subgroup.smul_def, unitsCoeffEquivUnitsFormation_smul, AddEquiv.apply_symm_apply]
    exact L.rep_ρ_mk_apply_coe _ u x

end LayerCoeff

/-! ### Hilbert 90 on the finite normal layers -/

/-- Read a cocycle on a formation layer as a function valued in the corresponding fixed points
of `(Kˢ)ˣ`. -/
private def unitsCocycle (L : NormalLayer (AbsoluteGaloisGroup K))
    (f : L.Gal → (L.rep (unitsFormation K)).V) :
    L.Gal → FixedPoints.addSubgroup L.relativeTop (UnitsCoeff K) := fun q =>
  layerCoeffEquiv L (f q)

/-- Reading a layer cocycle through the coefficient dictionary preserves the cocycle identity. -/
private theorem isCocycle₁_unitsCocycle (L : NormalLayer (AbsoluteGaloisGroup K))
    {f : L.Gal → (L.rep (unitsFormation K)).V}
    (hf : ∀ σ τ, f (σ * τ) = (L.rep (unitsFormation K)).ρ σ (f τ) + f σ) :
    IsCocycle₁ (unitsCocycle L f) := fun σ τ => by
  have h := congrArg (layerCoeffEquiv L) (hf σ τ)
  rw [map_add] at h
  exact h.trans (congrArg (· + _) (layerCoeffEquiv_ρ L σ (f τ)))

/-- Hilbert 90 on a finite layer `U ⧸ N` of a closed subgroup `U` of `G_K`, in the explicit form
used by inflation. -/
private theorem isCoboundary₁_of_isCocycle₁_quotient (U : Subgroup (AbsoluteGaloisGroup K))
    (hU : IsClosed (U : Set (AbsoluteGaloisGroup K))) (N : Subgroup U) [N.Normal]
    (hN : IsOpen (N : Set U)) {f : U ⧸ N → FixedPoints.addSubgroup N (UnitsCoeff K)}
    (hf : IsCocycle₁ f) : IsCoboundary₁ f := by
  -- Inflation `H¹(U ⧸ N, ((Kˢ)ˣ)^N) → H¹(U, (Kˢ)ˣ)` is injective, and its target vanishes by
  -- Hilbert 90 for the closed subgroup `U`.
  have : DiscreteTopology (U ⧸ N) := QuotientGroup.discreteTopology hN
  have := subsingleton_H1_unitsCoeff_of_isClosed K U hU
  have hz : f ∈ Z1 (U ⧸ N) (FixedPoints.addSubgroup N (UnitsCoeff K)) :=
    mem_Z1_iff.2 ⟨continuous_of_discreteTopology, hf⟩
  exact mem_B1_iff.1 (H1pi_eq_zero_iff.1 (explicitInfl1_injective U (UnitsCoeff K) N
    (a₁ := ((⟨f, hz⟩ : Z1 _ _) : H1 _ _)) (a₂ := 0) (Subsingleton.elim _ _)))

/-- **Hilbert 90 on a finite normal layer** of the formation of units: for open subgroups
`V ◁ U` of `G_K`, `H¹(U ⧸ V, ((Kˢ)ˣ)^V) = 0`. In field notation, `H¹(Gal(E/F), Eˣ) = 0` for the
finite Galois extension `E/F` of fixed fields of `V` and `U`; this is the first axiom of a class
formation. -/
theorem subsingleton_h1_unitsFormation (L : NormalLayer (AbsoluteGaloisGroup K)) :
    Subsingleton (L.H (unitsFormation K) 1) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  induction c using H1_induction_on with
  | h f => ?_
  rw [H1π_eq_zero_iff]
  -- The cocycle `f`, read with values in the fixed points of `V` in `(Kˢ)ˣ`, is a coboundary.
  have : (L.top.toSubgroup.subgroupOf L.ground.toSubgroup).Normal := L.normal
  obtain ⟨m, hm⟩ := isCoboundary₁_of_isCocycle₁_quotient L.ground.toSubgroup L.ground.isClosed
    (L.top.toSubgroup.subgroupOf L.ground.toSubgroup) (L.top.isOpen.preimage continuous_subtype_val)
    (f := unitsCocycle L f) (isCocycle₁_unitsCocycle L ((mem_cocycles₁_iff f).1 f.2))
  refine ⟨(layerCoeffEquiv L).symm m, funext fun σ => (layerCoeffEquiv L).injective ?_⟩
  rw [d₀₁_hom_apply, map_sub, layerCoeffEquiv_ρ, AddEquiv.apply_symm_apply]
  exact hm σ

end TauCeti.ClassFieldTheory
