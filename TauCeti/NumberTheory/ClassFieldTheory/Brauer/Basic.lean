/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.GaloisCohomology.Hilbert90
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent
public import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso

/-!
# The Brauer group as continuous cohomology, and its finite layers

For a field `F` with absolute Galois group `G_F = Field.absoluteGaloisGroup F`, this file defines
the coefficient object `unitsRep F` of the units `(Fˢ)ˣ` of a separable closure, written
additively, and the **Brauer group**

`Br F = H²(G_F, (Fˢ)ˣ)`

on Mathlib's continuous cohomology `continuousCohomology`, the carrier on which the local
invariant is to be defined. The group `G_F` acts on `(Fˢ)ˣ` through the restriction isomorphism
`TauCeti.absoluteGaloisGroupRestrictEquiv : G_F ≃ₜ* Gal(Fˢ/F)`, exactly as for the roots of unity
`TauCeti.ClassFieldTheory.muNRep`, and `unitsRepH2Equiv` identifies `Br F` with the explicit
`H²(Gal(Fˢ/F), (Fˢ)ˣ)` of `TauCeti.UnitsCoeff F`, the group whose `n`-torsion is described by
`TauCeti.h2KummerToUnits_range`.

The Brauer group is the union of its finite layers. For an open normal subgroup `U` of
`Gal(Fˢ/F)`, `brLevelInfl U` is inflation `H²(Gal(Fˢ/F) ⧸ U, ((Fˢ)ˣ)^U) → Br F`. Every Brauer
class is inflated from some level (`exists_brLevelInfl_eq`), and, by Hilbert 90 for `U`, each
inflation is injective (`brLevelInfl_injective`). For a finite normal extension `L/K` embedded in
`Kˢ` by `σ`, the level of `Gal(Kˢ/σ(L))` is identified with Mathlib's group cohomology
`H²(Gal(L/K), Lˣ)` of the relative Brauer group (`relBrLevelEquiv`), which gives the injection
`relBrInfl K L σ : H²(Gal(L/K), Lˣ) → Br K`; every Brauer class comes from a finite Galois
subextension of `Kˢ` (`exists_relBrInfl_eq`). This finite-layer description is what an invariant
defined on the finite layers, such as the unramified invariant
`TauCeti.ClassFieldTheory.unramifiedInv` on `H²(Gal(L/K), Lˣ)`, has to be carried along to reach
`Br K`.

`Br F` is the cohomological Brauer group. Its comparison with the Brauer group `BrauerGroup F` of
central simple algebras is not made here.

## Implementation notes

`relBrLevelEquiv` compares with Mathlib's `groupCohomology`, whose comparison with the explicit
model, `TauCeti.ContCohomology.explicitH2IsoGroupCohomology`, asks for the group and the module in
`Type`; the fields `K` and `L` of the relative statements therefore live in `Type`, as do those of
`TauCeti.ClassFieldTheory.unramifiedInv`. The level `galoisOpenNormalSubgroup K L σ` is defined in
this file so that its underlying subgroup is the fixing subgroup of `σ(L)` by definition, which is
what lets `relBrLevelEquiv` pass between the two descriptions of the same quotient and invariants.

## Main definitions

* `TauCeti.ClassFieldTheory.unitsRep F`: the units `(Fˢ)ˣ` as a coefficient object for `G_F`.
* `TauCeti.ClassFieldTheory.Br F`: the Brauer group `H²(G_F, (Fˢ)ˣ)`.
* `TauCeti.ClassFieldTheory.unitsRepH2Equiv`: `H²(Gal(Fˢ/F), (Fˢ)ˣ) ≃+ Br F`.
* `TauCeti.ClassFieldTheory.brLevelInfl`: inflation from the level of an open normal subgroup.
* `TauCeti.ClassFieldTheory.relBrLevelEquiv`: `H²(Gal(L/K), Lˣ)` as the level of the subgroup
  fixing `σ(L)`.
* `TauCeti.ClassFieldTheory.relBrInfl`: inflation `H²(Gal(L/K), Lˣ) → Br K`.

## Main results

* `TauCeti.ClassFieldTheory.brLevelInfl_injective`, `TauCeti.ClassFieldTheory.relBrInfl_injective`:
  inflation into the Brauer group is injective.
* `TauCeti.ClassFieldTheory.exists_brLevelInfl_eq`, `TauCeti.ClassFieldTheory.exists_relBrInfl_eq`:
  every Brauer class is inflated from a finite layer.
* `TauCeti.ClassFieldTheory.brLevelInfl_explicitFiniteQuotientTransition2`: inflations from
  different levels are compatible.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §4 and §5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.3.4).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

universe u

variable (F : Type u) [Field F]

/-! ### The coefficient object `(Fˢ)ˣ` and the Brauer group -/

/-- **The units `(Fˢ)ˣ` of a separable closure, written additively, as a coefficient object.**
An automorphism of the algebraic closure acts through its restriction to the separable closure,
`TauCeti.absoluteGaloisGroupRestrictEquiv`; `unitsCoeffEquivUnitsRep` identifies the underlying
module with `TauCeti.UnitsCoeff F`. -/
def unitsRep : TopRep ℤ (Field.absoluteGaloisGroup F) :=
  TopRep.res
    (absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
    (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (UnitsCoeff F))

/-- `(Fˢ)ˣ` carries the discrete topology. -/
instance : DiscreteTopology (unitsRep F).V :=
  inferInstanceAs (DiscreteTopology (UnitsCoeff F))

/-- **The coefficient dictionary** between `TauCeti.UnitsCoeff F`, a module for `Gal(Fˢ/F)`, and
the underlying module of `unitsRep F`. It is equivariant along the restriction isomorphism by
`unitsCoeffEquivUnitsRep_smul`. -/
def unitsCoeffEquivUnitsRep : UnitsCoeff F ≃+ (unitsRep F).V :=
  AddEquiv.refl _

/-- **The coefficient dictionary is equivariant**: `σ ∈ G_F` acts on `unitsRep F` as its
restriction to the separable closure acts on `TauCeti.UnitsCoeff F`. -/
@[simp]
theorem unitsCoeffEquivUnitsRep_smul (g : Field.absoluteGaloisGroup F) (x : UnitsCoeff F) :
    unitsCoeffEquivUnitsRep F (absoluteGaloisGroupRestrictEquiv F g • x) =
      (unitsRep F).ρ g (unitsCoeffEquivUnitsRep F x) :=
  (ofDiscreteModule_ρ_apply_apply (R := ℤ) (absoluteGaloisGroupRestrictEquiv F g) x).symm.trans
    (ContRepresentation.restrict_apply_apply
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (UnitsCoeff F)).ρ
      (absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
      g x).symm

/-- **`(Fˢ)ˣ` is a smooth discrete coefficient object**: the stabilizer of a unit is the preimage,
under the restriction isomorphism, of its open stabilizer in `Gal(Fˢ/F)`. -/
theorem isSmoothDiscrete_unitsRep : IsSmoothDiscrete ℤ (unitsRep F) :=
  (ofDiscreteModule_isSmoothDiscrete ℤ (AbsoluteGaloisGroup F) (UnitsCoeff F)).res
    (absoluteGaloisGroupRestrictEquiv F).continuous

attribute [local instance] TopRep.distribMulAction

/-- The action of `G_F` on `(Fˢ)ˣ` is continuous, `(Fˢ)ˣ` being smooth discrete. -/
instance : ContinuousSMul (Field.absoluteGaloisGroup F) (unitsRep F).V :=
  (isSmoothDiscrete_unitsRep F).continuousSMul

/-- **The Brauer group** `Br F = H²(G_F, (Fˢ)ˣ)`, on Mathlib's continuous cohomology. -/
abbrev Br : Type _ :=
  continuousCohomology 2 (unitsRep F)

/-- **`H²` of `(Fˢ)ˣ` over `Gal(Fˢ/F)` is the Brauer group**: pullback along the restriction
isomorphism `G_F ≃ Gal(Fˢ/F)` and the coefficient dictionary, followed by the degree-two
comparison of explicit and canonical continuous cohomology for the discrete object
`unitsRep F`. -/
def unitsRepH2Equiv : H2 (AbsoluteGaloisGroup F) (UnitsCoeff F) ≃+ Br F :=
  (explicitMap2Equiv (AbsoluteGaloisGroup F) (UnitsCoeff F) (Field.absoluteGaloisGroup F)
      (unitsRep F).V (absoluteGaloisGroupRestrictEquiv F) (unitsCoeffEquivUnitsRep F)
      continuous_of_discreteTopology continuous_of_discreteTopology
      fun g x => (unitsCoeffEquivUnitsRep_smul F g x).trans
        (TopRep.distribMulAction_smul _ g _).symm).trans <|
    (unitsRep F).explicitH2AddEquivContinuousCohomologyOfDiscrete

/-- `unitsRepH2Equiv` is the pullback along the restriction isomorphism and the coefficient
dictionary, followed by the degree-two comparison for the discrete object `unitsRep F`. -/
theorem unitsRepH2Equiv_apply (x : H2 (AbsoluteGaloisGroup F) (UnitsCoeff F)) :
    unitsRepH2Equiv F x =
      (unitsRep F).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 (AbsoluteGaloisGroup F) (UnitsCoeff F) (Field.absoluteGaloisGroup F)
          (unitsRep F).V (absoluteGaloisGroupRestrictEquiv F)
          (unitsCoeffEquivUnitsRep F).toAddMonoidHom continuous_of_discreteTopology
          (fun g x => (unitsCoeffEquivUnitsRep_smul F g x).trans
            (TopRep.distribMulAction_smul _ g _).symm) x) := by
  rw [unitsRepH2Equiv, AddEquiv.trans_apply, explicitMap2Equiv_apply]

/-! ### Inflation from the finite levels -/

variable {F}

/-- **Inflation from a finite level into the Brauer group**: for an open normal subgroup `U` of
`Gal(Fˢ/F)`, inflation `H²(Gal(Fˢ/F) ⧸ U, ((Fˢ)ˣ)^U) → H²(Gal(Fˢ/F), (Fˢ)ˣ)` followed by
`unitsRepH2Equiv`. It is injective (`brLevelInfl_injective`) and every Brauer class lies in the
image of some level (`exists_brLevelInfl_eq`). -/
def brLevelInfl (U : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    H2 (AbsoluteGaloisGroup F ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup (UnitsCoeff F))
      →+ Br F :=
  (unitsRepH2Equiv F).toAddMonoidHom.comp (explicitInfl2 _ _ U.toSubgroup)

/-- `brLevelInfl U` is explicit inflation followed by `unitsRepH2Equiv`. -/
theorem brLevelInfl_apply (U : OpenNormalSubgroup (AbsoluteGaloisGroup F))
    (y : H2 (AbsoluteGaloisGroup F ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup (UnitsCoeff F))) :
    brLevelInfl U y = unitsRepH2Equiv F (explicitInfl2 _ (UnitsCoeff F) U.toSubgroup y) :=
  (rfl)

/-- **Inflation from a finite level into the Brauer group is injective**, by Hilbert 90 for the
open subgroup `U` (`TauCeti.explicitInfl2_unitsCoeff_injective`). -/
theorem brLevelInfl_injective (U : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    Function.Injective (brLevelInfl U) :=
  (unitsRepH2Equiv F).injective.comp
    (explicitInfl2_unitsCoeff_injective F U.toSubgroup U.isClosed)

/-- **Every Brauer class is inflated from a finite level**, by strict descent of continuous
`2`-cocycles to a finite quotient (`TauCeti.ContCohomology.exists_explicitInfl2_eq`). -/
theorem exists_brLevelInfl_eq (x : Br F) :
    ∃ (U : OpenNormalSubgroup (AbsoluteGaloisGroup F))
      (y : H2 (AbsoluteGaloisGroup F ⧸ U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup (UnitsCoeff F))),
      brLevelInfl U y = x := by
  obtain ⟨U, y, hy⟩ := exists_explicitInfl2_eq ((unitsRepH2Equiv F).symm x)
  exact ⟨U, y, by rw [brLevelInfl_apply, hy, AddEquiv.apply_symm_apply]⟩

/-- **Inflations from different levels are compatible**: for open normal subgroups `V ≤ U`,
inflating from the `U`-level through the `V`-level is inflating from the `U`-level directly. -/
theorem brLevelInfl_explicitFiniteQuotientTransition2
    {U V : OpenNormalSubgroup (AbsoluteGaloisGroup F)} (hVU : V ≤ U)
    (y : H2 (AbsoluteGaloisGroup F ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup (UnitsCoeff F))) :
    brLevelInfl V (explicitFiniteQuotientTransition2 _ (UnitsCoeff F) U V hVU y) =
      brLevelInfl U y := by
  rw [brLevelInfl_apply, brLevelInfl_apply, explicitInfl2_explicitFiniteQuotientTransition2]

/-! ### The relative Brauer group of a finite normal extension -/

section Relative

variable (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Normal K L] (σ : L →ₐ[K] SeparableClosure K)

/-- **The level of a finite normal extension**: the subgroup `Gal(Kˢ/σ(L))` of automorphisms of
`Kˢ` fixing `σ(L)`, an open normal subgroup of `Gal(Kˢ/K)` because `L/K` is finite and normal. -/
def galoisOpenNormalSubgroup : OpenNormalSubgroup (AbsoluteGaloisGroup K) where
  toSubgroup := σ.fieldRange.fixingSubgroup
  isOpen' := isOpen_fixingSubgroup_fieldRange K L σ
  isNormal' := inferInstance

/-- The subgroup underlying `galoisOpenNormalSubgroup K L σ` is the fixing subgroup of `σ(L)`. -/
@[simp]
theorem galoisOpenNormalSubgroup_toSubgroup :
    (galoisOpenNormalSubgroup K L σ).toSubgroup = σ.fieldRange.fixingSubgroup :=
  (rfl)

omit [FiniteDimensional K L] in
/-- Embedding units of `L` by `σ` turns the action of the restriction of `g` into the action
of `g`. -/
private theorem embeddedUnitsEquivInvariants_restrictNormalHom_smul
    (g : AbsoluteGaloisGroup K) (b : Additive Lˣ) :
    (embeddedUnitsEquivInvariants K L σ (Additive.ofMul (σ.restrictNormalHom g • b.toMul)) :
        UnitsCoeff K) =
      g • (embeddedUnitsEquivInvariants K L σ b : UnitsCoeff K) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [embeddedUnitsEquivInvariants_apply, embeddedUnitsEquivInvariants_apply, Additive.toMul_smul,
    toMul_coe_embeddedUnitsInvariants, toMul_coe_embeddedUnitsInvariants, toMul_ofMul,
    AlgEquiv.smul_units_def, AlgEquiv.smul_units_def]
  simp only [Units.coe_map]
  exact σ.restrictNormalHom_commutes g b.toMul

/-- `quotientFixingSubgroupFieldRangeEquiv`, read at the level `galoisOpenNormalSubgroup K L σ`,
whose underlying subgroup is by definition the fixing subgroup of `σ(L)`. -/
private def levelQuotientEquiv :
    AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L σ).toSubgroup ≃* Gal(L/K) :=
  quotientFixingSubgroupFieldRangeEquiv K L σ

/-- `levelQuotientEquiv` sends the class of `g` to its restriction to `L`. -/
private theorem levelQuotientEquiv_mk (g : AbsoluteGaloisGroup K) :
    levelQuotientEquiv K L σ g = σ.restrictNormalHom g :=
  quotientFixingSubgroupFieldRangeEquiv_mk K L σ g

/-- **The relative Brauer group `H²(Gal(L/K), Lˣ)` is the level of `Gal(Kˢ/σ(L))`**: Mathlib's
group cohomology of `Lˣ` is carried by `quotientFixingSubgroupFieldRangeEquiv` and
`TauCeti.embeddedUnitsEquivInvariants` to that of `((Kˢ)ˣ)^U` over `Gal(Kˢ/K) ⧸ U`, for
`U = galoisOpenNormalSubgroup K L σ`, which is the explicit `H²` of this discrete finite level by
`TauCeti.ContCohomology.explicitH2IsoGroupCohomology`. -/
def relBrLevelEquiv :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2 ≃+
      H2 (AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L σ).toSubgroup)
        (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L σ).toSubgroup (UnitsCoeff K)) :=
  (groupCohomology.mapIso (levelQuotientEquiv K L σ).symm
    (embeddedUnitsEquivInvariants K L σ).toIntLinearEquiv (fun τ => by
      obtain ⟨g, rfl⟩ := σ.restrictNormalHom_surjective τ
      refine LinearMap.ext fun b => Subtype.ext ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        (MulEquiv.symm_apply_eq _).2 (levelQuotientEquiv_mk K L σ g).symm]
      -- Both sides are the action on the image of `b` in `(Kˢ)ˣ`, the representations acting by
      -- `Rep.ofMulDistribMulAction_ρ_apply_apply` and `Rep.ofDistribMulAction_ρ_apply_apply`, and
      -- `G_K ⧸ U` acting on `((Kˢ)ˣ)^U` through representatives, all of which hold by `rfl`.
      exact embeddedUnitsEquivInvariants_restrictNormalHom_smul K L σ g b)
    2).toLinearEquiv.toAddEquiv.trans (explicitH2IsoGroupCohomology _ _).symm

/-- **Inflation from the relative Brauer group** `H²(Gal(L/K), Lˣ) → Br K` of a finite normal
extension `L/K` embedded in `Kˢ` by `σ`: the identification `relBrLevelEquiv` of
`H²(Gal(L/K), Lˣ)` with the level of `Gal(Kˢ/σ(L))`, followed by `brLevelInfl`. -/
def relBrInfl : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2 →+ Br K :=
  (brLevelInfl (galoisOpenNormalSubgroup K L σ)).comp (relBrLevelEquiv K L σ).toAddMonoidHom

/-- `relBrInfl K L σ` is `brLevelInfl` after the identification `relBrLevelEquiv`. -/
theorem relBrInfl_apply (x : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) :
    relBrInfl K L σ x = brLevelInfl (galoisOpenNormalSubgroup K L σ) (relBrLevelEquiv K L σ x) :=
  (rfl)

/-- **`H²(Gal(L/K), Lˣ)` injects into the Brauer group of `K`.** -/
theorem relBrInfl_injective : Function.Injective (relBrInfl K L σ) :=
  (brLevelInfl_injective _).comp (relBrLevelEquiv K L σ).injective

/-- `relBrInfl K L σ` takes the class corresponding to a level class `y` to its inflation. -/
private theorem relBrInfl_relBrLevelEquiv_symm
    (y : H2 (AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L σ).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L σ).toSubgroup (UnitsCoeff K))) :
    relBrInfl K L σ ((relBrLevelEquiv K L σ).symm y) =
      brLevelInfl (galoisOpenNormalSubgroup K L σ) y := by
  rw [relBrInfl_apply, AddEquiv.apply_symm_apply]

variable {K} in
/-- **Every Brauer class splits over a finite Galois subextension of `Kˢ`**: it is inflated from
`H²(Gal(E/K), Eˣ)` for some intermediate field `E` of `Kˢ/K`, finite and normal over `K`. -/
theorem exists_relBrInfl_eq (x : Br K) :
    ∃ (E : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K E) (_ : Normal K E)
      (y : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) Eˣ) 2),
      relBrInfl K E E.val y = x := by
  obtain ⟨U, y, rfl⟩ := exists_brLevelInfl_eq x
  -- The fixed field `E` of `U` is finite Galois over `K`, and `U` is the subgroup fixing it.
  obtain ⟨E, hE⟩ : ∃ E : IntermediateField K (SeparableClosure K),
      E.fixingSubgroup = U.toSubgroup :=
    ⟨_, InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩⟩
  have : FiniteDimensional K E := by
    rw [← InfiniteGalois.isOpen_iff_finite, hE]
    exact U.isOpen
  have : IsGalois K E := by
    rw [← InfiniteGalois.normal_iff_isGalois, hE]
    infer_instance
  have hU : galoisOpenNormalSubgroup K E E.val = U := by
    refine OpenNormalSubgroup.toSubgroup_injective ?_
    dsimp only
    rw [galoisOpenNormalSubgroup_toSubgroup, IntermediateField.fieldRange_val, hE]
  subst hU
  exact ⟨E, inferInstance, inferInstance, _, relBrInfl_relBrLevelEquiv_symm K E E.val y⟩

end Relative

end TauCeti.ClassFieldTheory
