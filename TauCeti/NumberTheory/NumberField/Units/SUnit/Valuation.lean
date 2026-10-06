/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.SUnit.Basic
public import TauCeti.RingTheory.DedekindDomain.Action
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup

/-!
# The equivariant S-unit valuation sequence

For a stable finite set `S` of finite places of a number field `L`, the valuation map from
S-units to the permutation module `ℤ[S]` is equivariant under automorphisms of `L`. Its kernel
is the ordinary unit group and its image has finite index. Thus the finite-place contribution
to the S-unit representation is a full sublattice of the permutation module, rather than only
a group of the same rank.

The valuation uses Mathlib's multiplicative normalization: its integer coordinate is the
negative of the prime's exponent in the principal fractional ideal. This sign has no effect
on exactness or equivariance.

The arithmetic finite-index input is `TauCeti.finiteIndex_range_unitValuation`; the permutation
module and its action are Mathlib's `Rep.ofMulAction`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4 (the S-unit Herbrand calculation).
-/

public section
noncomputable section

open IsDedekindDomain NumberField CategoryTheory MonoidAlgebra
open scoped Pointwise

namespace SubMulAction

attribute [local instance] Units.mulDistribMulActionRight

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Automorphisms preserve the S-units when the set of allowed finite primes is stable. -/
theorem smul_mem_sUnits (S : SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)))
    (g : L ≃ₐ[K] L) {u : Lˣ} (hu : u ∈ (S : Set (HeightOneSpectrum (𝓞 L))).unit L) :
    g • u ∈ (S : Set (HeightOneSpectrum (𝓞 L))).unit L := by
  apply (Set.mem_unit_iff _ _).mpr
  intro v hv
  have hnot : g⁻¹ • v ∉ S := by
    intro h
    exact hv (by simpa using S.smul_mem g h)
  have hval := HeightOneSpectrum.valuation_apply_eq_of_asIdeal_eq_smul g
    (w := g⁻¹ • v) (w' := v) (by simp) (u : L)
  simpa only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass] using
    hval.trans ((Set.mem_unit_iff _ _).mp hu _ hnot)

/-- The natural automorphism action on the group of S-units. -/
abbrev sUnitAction (S : SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L))) :
    MulDistribMulAction (L ≃ₐ[K] L) ((S : Set (HeightOneSpectrum (𝓞 L))).unit L) where
  smul g u := ⟨g • u.val, smul_mem_sUnits S g u.property⟩
  one_smul u := Subtype.ext (one_smul (L ≃ₐ[K] L) u.val)
  mul_smul g h u := Subtype.ext (mul_smul g h u.val)
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g u v := Subtype.ext (smul_mul' g u.val v.val)

/-- The integral representation of the automorphism group on S-units. Its carrier is the
additive version of Mathlib's `Set.unit`, not a new S-unit group. -/
abbrev sUnitRep (S : SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L))) :
    Rep ℤ (L ≃ₐ[K] L) :=
  letI := sUnitAction S
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)

/-- The action on an S-unit is the restriction of the field automorphism. -/
@[simp]
theorem sUnitAction_smul_val
    (S : SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L))) (g : L ≃ₐ[K] L)
    (u : (S : Set (HeightOneSpectrum (𝓞 L))).unit L) :
    letI := sUnitAction S
    (g • u).val = g • u.val :=
  (rfl)

variable (S : SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L))) [Finite S]

private def valuationCoordinates : Additive (S → Multiplicative ℤ) ≃ₗ[ℤ] ℤ[S] :=
  (MulEquiv.funMultiplicative S ℤ).symm.toAdditiveLeft.toIntLinearEquiv.trans
    ((Finsupp.linearEquivFunOnFinite ℤ ℤ S).symm.trans (coeffLinearEquiv ℤ).symm)

private def valuationVector :
    Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L) →ₗ[ℤ] ℤ[S] :=
  (valuationCoordinates S).toLinearMap ∘ₗ
    (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L))) L).toAdditive.toIntLinearMap

private theorem valuationVector_coeff
    (u : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) (v : S) :
    (valuationVector S u).coeff v =
      Multiplicative.toAdd (v.val.valuationOfNeZero u.toMul.val) := by
  -- The coordinate equivalences and type-tag combinators compute to the valuation tuple.
  change Multiplicative.toAdd
    (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L))) L u.toMul v) = _
  rw [Set.unitValuation_apply]

/-- The S-unit valuation homomorphism into the finite-prime permutation module. -/
def sUnitValuation : sUnitRep S ⟶ Rep.ofMulAction ℤ (L ≃ₐ[K] L) S :=
  Rep.ofHom
    { toLinearMap := valuationVector S
      isIntertwining' g := by
        let := sUnitAction S
        apply LinearMap.ext
        intro u
        apply MonoidAlgebra.ext
        apply Finsupp.ext
        intro v
        -- Unpack composition and the S-unit representation's local action instance.
        change (valuationVector S (Additive.ofMul (g • u.toMul))).coeff v =
          ((Representation.ofMulAction ℤ (L ≃ₐ[K] L) S g) (valuationVector S u)).coeff v
        rw [Representation.coeff_ofMulAction, valuationVector_coeff, valuationVector_coeff]
        -- The subtype action has the same underlying unit as the ambient action.
        change Multiplicative.toAdd (v.val.valuationOfNeZero (g • u.toMul.val)) = _
        apply congrArg Multiplicative.toAdd
        rw [HeightOneSpectrum.valuationOfNeZero_eq_iff,
          HeightOneSpectrum.valuationOfNeZero_eq]
        exact HeightOneSpectrum.valuation_apply_eq_of_asIdeal_eq_smul g
          (w := (g⁻¹ • v).val) (w' := v.val) (by simp) _ }

/-- The coefficient of the valuation vector is the integer attached to the prime valuation. -/
@[simp]
theorem sUnitValuation_coeff
    (u : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) (v : S) :
    ((sUnitValuation S).hom u).coeff v =
      Multiplicative.toAdd (v.val.valuationOfNeZero u.toMul.val) :=
  valuationVector_coeff S u v

omit [Finite S] in
private def unitInclusion : (𝓞 L)ˣ →* (S : Set (HeightOneSpectrum (𝓞 L))).unit L :=
  (Subgroup.inclusion (Set.unit_mono L (Set.empty_subset _))).comp
    (Set.unitEmptyEquivUnits (R := 𝓞 L) L).symm.toMonoidHom

omit [Finite S] in
private theorem unitInclusion_val (u : (𝓞 L)ˣ) :
    (unitInclusion S u).val = Units.map (algebraMap (𝓞 L) L) u := by
  apply Units.ext
  exact (Set.algebraMap_unitEmptyEquivUnits_apply L
    ((Set.unitEmptyEquivUnits (R := 𝓞 L) L).symm u)).symm.trans
      (by simp)

omit [Finite S] in
/-- The inclusion of ordinary units into S-units, as a morphism of integral representations. -/
def sUnitInclusion : Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ ⟶ sUnitRep S :=
  Rep.ofHom
    { toLinearMap := (unitInclusion S).toAdditive.toIntLinearMap
      isIntertwining' g := by
        let := sUnitAction S
        apply LinearMap.ext
        intro u
        -- Both representations are additive versions of multiplicative unit groups.
        change Additive.ofMul (unitInclusion S (g • u.toMul)) =
          Additive.ofMul (g • unitInclusion S u.toMul)
        apply congrArg Additive.ofMul
        apply Subtype.ext
        rw [unitInclusion_val]
        -- Reduce equivariance of units to equivariance of the ring-of-integers embedding.
        apply Units.ext
        change algebraMap (𝓞 L) L (g • (u.toMul : 𝓞 L)) =
          g ((unitInclusion S u.toMul).val : L)
        rw [unitInclusion_val, Units.coe_map]
        exact algebraMap_smul_eq_apply g (u.toMul : 𝓞 L) }

omit [Finite S] in
/-- The inclusion has the same underlying field element as the ring-of-integers embedding. -/
@[simp]
theorem sUnitInclusion_val (u : Additive (𝓞 L)ˣ) :
    ((sUnitInclusion S).hom u).toMul.val = Units.map (algebraMap (𝓞 L) L) u.toMul :=
  unitInclusion_val S u.toMul

omit [Finite S] in
/-- Ordinary units embed injectively into the S-unit representation. -/
theorem sUnitInclusion_injective : Function.Injective (sUnitInclusion S).hom := by
  -- The source carrier is the additive version of the ordinary unit group.
  change Function.Injective (fun u : Additive (𝓞 L)ˣ => (sUnitInclusion S).hom u)
  intro u v h
  apply Additive.toMul.injective
  apply (Set.unitEmptyEquivUnits (R := 𝓞 L) L).symm.injective
  apply Subtype.ext
  exact congrArg (fun x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L) =>
    x.toMul.val) h

/-- The kernel of the S-unit valuation map is exactly the image of the ordinary units. -/
theorem range_sUnitInclusion_eq_ker_sUnitValuation :
    (sUnitInclusion S).hom.toLinearMap.range = (sUnitValuation S).hom.toLinearMap.ker := by
  ext u
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  -- `Rep.Hom` and its underlying linear map have the same evaluation.
  change (∃ y : Additive (𝓞 L)ˣ, (sUnitInclusion S).hom y = u) ↔
    (sUnitValuation S).hom u = 0
  have hzero : (sUnitValuation S).hom u = 0 ↔
      u.toMul ∈ (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L))) L).ker := by
    -- The coordinate equivalence is injective; only the valuation tuple can vanish.
    change valuationCoordinates S
      ((Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L))) L).toAdditive u) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    rfl
  rw [hzero, Set.unitValuation_ker]
  -- Membership in a subgroup of S-units is membership of the underlying field unit.
  change (∃ y : Additive (𝓞 L)ˣ, (sUnitInclusion S).hom y = u) ↔ u.toMul.val ∈
    (∅ : Set (HeightOneSpectrum (𝓞 L))).unit L
  constructor
  · rintro ⟨v, rfl⟩
    exact ((Set.unitEmptyEquivUnits (R := 𝓞 L) L).symm v.toMul).property
  · intro hu
    refine ⟨Additive.ofMul (Set.unitEmptyEquivUnits L ⟨u.toMul.val, hu⟩), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg
      (fun x : (∅ : Set (HeightOneSpectrum (𝓞 L))).unit L => x.val)
      ((Set.unitEmptyEquivUnits L).symm_apply_apply ⟨u.toMul.val, hu⟩)

/-- The finite-prime valuation image has finite index in the permutation module. -/
theorem finiteIndex_range_sUnitValuation :
    (sUnitValuation S).hom.toLinearMap.range.toAddSubgroup.FiniteIndex := by
  have : (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L)))
      L).range.toAddSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_toAddSubgroup_iff.mpr
      (TauCeti.finiteIndex_range_unitValuation (𝓞 L) L _)
  have hrange : (sUnitValuation S).hom.toLinearMap.range.toAddSubgroup =
      (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L))) L).range.toAddSubgroup.map
        (valuationCoordinates S).toAddMonoidHom := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨_, ⟨u.toMul, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      exact ⟨Additive.ofMul u, rfl⟩
  rw [hrange]
  exact AddSubgroup.FiniteIndex.map_of_surjective _ (valuationCoordinates S).surjective

end SubMulAction
