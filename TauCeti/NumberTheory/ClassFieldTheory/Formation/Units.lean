/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Hilbert90
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic

/-!
# The formation of the units of a separable closure

For a field `K` with separable closure `Kˢ` and absolute Galois group `G_K = Gal(Kˢ/K)`, this file
builds the **formation** `unitsFormation K` whose coefficient module is the multiplicative group
`(Kˢ)ˣ`, written additively. Its level at an open subgroup `U` is the unit group of the fixed field
of `U`, and its finite normal layers are the finite Galois extensions `E/F` inside `Kˢ`. It is the
formation on which the local class formation is to be built.

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

/-! ### Hilbert 90 on the finite normal layers -/

/-- Read a cocycle on a formation layer as a function valued in the corresponding fixed points
of `(Kˢ)ˣ`. -/
private def unitsCocycle (L : NormalLayer (AbsoluteGaloisGroup K))
    (f : L.Gal → (L.rep (unitsFormation K)).V) :
    L.Gal → FixedPoints.addSubgroup L.relativeTop (UnitsCoeff K) := fun q =>
  ⟨(unitsCoeffEquivUnitsFormation K).symm (f q : (unitsFormation K).level L.top),
    (FixedPoints.mem_addSubgroup _ _ _).2 fun v =>
      (Formation.mem_level _).1 (f q).2 _ (Subgroup.mem_subgroupOf.1 v.2)⟩

/-- `unitsCocycle` changes only the coefficient dictionary, not the underlying element. -/
private theorem unitsCocycle_apply_coe (L : NormalLayer (AbsoluteGaloisGroup K))
    (f : L.Gal → (L.rep (unitsFormation K)).V) (q : L.Gal) :
    (unitsCocycle L f q : UnitsCoeff K) =
      (unitsCoeffEquivUnitsFormation K).symm
        (f q : (unitsFormation K).level L.top) :=
  (rfl)

/-- Reading a layer cocycle through the coefficient dictionary preserves the cocycle identity. -/
private theorem isCocycle₁_unitsCocycle (L : NormalLayer (AbsoluteGaloisGroup K))
    {f : L.Gal → (L.rep (unitsFormation K)).V}
    (hf : ∀ σ τ, f (σ * τ) = (L.rep (unitsFormation K)).ρ σ (f τ) + f σ) :
    IsCocycle₁ (unitsCocycle L f) := by
  intro σ τ
  induction σ using QuotientGroup.induction_on with
  | H u =>
    apply Subtype.ext
    have hsmul :
        (((u : L.Gal) • unitsCocycle L f τ :
            FixedPoints.addSubgroup L.relativeTop (UnitsCoeff K)) : UnitsCoeff K) =
          (u : AbsoluteGaloisGroup K) • (unitsCocycle L f τ : UnitsCoeff K) :=
      subtype_mk'_smul L.ground (UnitsCoeff K) L.relativeTop u (unitsCocycle L f τ)
    rw [unitsCocycle_apply_coe, AddSubgroup.coe_add, hsmul,
      unitsCocycle_apply_coe, unitsCocycle_apply_coe, hf u τ, Submodule.coe_add, map_add,
      NormalLayer.rep_ρ_mk_apply_coe, unitsCoeffEquivUnitsFormation_symm_ρ]

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
  refine ⟨⟨unitsCoeffEquivUnitsFormation K m, (Formation.mem_level _).2 fun v hv =>
    (FixedPoints.mem_addSubgroup _ _ _).1 m.2 ⟨⟨v, L.top_le_ground hv⟩, hv⟩⟩, funext fun σ => ?_⟩
  induction σ using QuotientGroup.induction_on with
  | H u =>
    have h : (u : AbsoluteGaloisGroup K) • (m : UnitsCoeff K) - m =
        (unitsCoeffEquivUnitsFormation K).symm (f u : (unitsFormation K).level L.top) :=
      congrArg Subtype.val (hm u)
    refine Subtype.ext ?_
    rw [d₀₁_hom_apply, Submodule.coe_sub, NormalLayer.rep_ρ_mk_apply_coe,
      ← unitsCoeffEquivUnitsFormation_smul, ← map_sub, h, AddEquiv.apply_symm_apply]

end TauCeti.ClassFieldTheory
