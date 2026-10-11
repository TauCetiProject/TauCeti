/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.SUnit.Basic
public import TauCeti.RingTheory.DedekindDomain.Action
public import TauCeti.Algebra.MonoidAlgebra.Basis
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
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

`TauCeti.ordinaryUnitRep` is the integral representation on the ordinary units, using
Mathlib's `Units.mulDistribMulActionRight` for the induced action on units.
`TauCeti.sUnitShortComplex` packages the ordinary-unit inclusion and valuation onto
Mathlib's categorical image as a short exact sequence. The image inclusion has finite categorical
cokernel, so it can be used with Herbrand-quotient invariance under finite cokernels.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4 (the S-unit Herbrand calculation).
-/

public section
noncomputable section

open IsDedekindDomain NumberField CategoryTheory MonoidAlgebra
open scoped Pointwise

namespace TauCeti

attribute [local instance] Units.mulDistribMulActionRight

/-- The integral representation of field automorphisms on the ordinary units of the ring of
integers. Its carrier is `Additive (𝓞 L)ˣ`. -/
abbrev ordinaryUnitRep (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ

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
instance sUnitAction (S : SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L))) :
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
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)

/-- The action on an S-unit is the restriction of the field automorphism. -/
@[simp]
theorem sUnitAction_smul_val
    (S : SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L))) (g : L ≃ₐ[K] L)
    (u : (S : Set (HeightOneSpectrum (𝓞 L))).unit L) :
    (g • u).val = g • u.val :=
  (rfl)

variable (S : SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L))) [Finite S]

private def valuationVector :
    Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L) →ₗ[ℤ] ℤ[S] :=
  (TauCeti.funMultiplicativeIntLinearEquiv S).toLinearMap ∘ₗ
    (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L))) L).toAdditive.toIntLinearMap

private theorem valuationVector_coeff
    (u : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) (v : S) :
    (valuationVector S u).coeff v =
      Multiplicative.toAdd (v.val.valuationOfNeZero u.toMul.val) := by
  rw [valuationVector, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TauCeti.funMultiplicativeIntLinearEquiv_coeff]
  simp only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul, Set.unitValuation_apply]

/-- The S-unit valuation homomorphism into the finite-prime permutation module. -/
def sUnitValuation : sUnitRep S ⟶ Rep.ofMulAction ℤ (L ≃ₐ[K] L) S :=
  Rep.ofHom
    { toLinearMap := valuationVector S
      isIntertwining' g := by
        apply LinearMap.ext
        intro u
        apply MonoidAlgebra.ext
        apply Finsupp.ext
        intro v
        simp only [LinearMap.comp_apply, Representation.ofMulDistribMulAction_apply_apply]
        rw [Representation.coeff_ofMulAction, valuationVector_coeff, valuationVector_coeff]
        rw [toMul_ofMul, sUnitAction_smul_val]
        apply congrArg Multiplicative.toAdd
        rw [HeightOneSpectrum.valuationOfNeZero_eq_iff,
          HeightOneSpectrum.valuationOfNeZero_eq]
        exact HeightOneSpectrum.valuation_apply_eq_of_asIdeal_eq_smul g
          (w := (g⁻¹ • v).val) (w' := v.val) (by simp) _ }

/-- The underlying valuation map is the S-unit valuation transported to the permutation module. -/
theorem sUnitValuation_hom_apply
    (u : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    (sUnitValuation S).hom u = TauCeti.funMultiplicativeIntLinearEquiv S
      (Additive.ofMul (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L))) L u.toMul)) :=
  (rfl)

/-- The coefficient of the valuation vector is the integer attached to the prime valuation. -/
@[simp]
theorem sUnitValuation_coeff
    (u : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) (v : S) :
    ((sUnitValuation S).hom u).coeff v =
      Multiplicative.toAdd (v.val.valuationOfNeZero u.toMul.val) :=
  valuationVector_coeff S u v

omit [Finite S] in
/-- The inclusion of ordinary units into S-units, as a morphism of integral representations. -/
def sUnitInclusion : ordinaryUnitRep K L ⟶ sUnitRep S :=
  Rep.ofHom
    { toLinearMap := (unitsToUnit (S : Set (HeightOneSpectrum (𝓞 L))) L).toAdditive.toIntLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro u
        simp only [LinearMap.comp_apply, Representation.ofMulDistribMulAction_apply_apply,
          AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive, Function.comp_apply,
          toMul_ofMul]
        apply congrArg Additive.ofMul
        apply Subtype.ext
        rw [unitsToUnit_val]
        -- Reduce equivariance of units to equivariance of the ring-of-integers embedding.
        apply Units.ext
        simp only [sUnitAction_smul_val, Units.coe_smul, unitsToUnit_val, AlgEquiv.smul_units_def,
          Units.coe_map, MonoidHom.coe_ofClass, algebraMap_smul_eq_apply] }

omit [Finite S] in
/-- The underlying inclusion is the ordinary-unit inclusion transported to additive groups. -/
theorem sUnitInclusion_hom_apply (u : Additive (𝓞 L)ˣ) :
    (sUnitInclusion S).hom u =
      Additive.ofMul (unitsToUnit (S : Set (HeightOneSpectrum (𝓞 L))) L u.toMul) :=
  (rfl)

omit [Finite S] in
/-- The inclusion has the same underlying field element as the ring-of-integers embedding. -/
@[simp]
theorem sUnitInclusion_val (u : Additive (𝓞 L)ˣ) :
    ((sUnitInclusion S).hom u).toMul.val = Units.map (algebraMap (𝓞 L) L) u.toMul :=
  unitsToUnit_val (S : Set (HeightOneSpectrum (𝓞 L))) L u.toMul

omit [Finite S] in
/-- Ordinary units embed injectively into the S-unit representation. -/
theorem sUnitInclusion_injective : Function.Injective (sUnitInclusion S).hom := by
  intro u v h
  apply Additive.toMul.injective
  exact unitsToUnit_injective (S : Set (HeightOneSpectrum (𝓞 L))) L
    (congrArg Additive.toMul
      ((sUnitInclusion_hom_apply S u).symm.trans (h.trans (sUnitInclusion_hom_apply S v))))

/-- The kernel of the S-unit valuation map is exactly the image of the ordinary units. -/
theorem range_sUnitInclusion_eq_ker_sUnitValuation :
    (sUnitInclusion S).hom.toLinearMap.range = (sUnitValuation S).hom.toLinearMap.ker := by
  ext u
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  simp only [Representation.IntertwiningMap.toLinearMap_apply]
  have hzero : (sUnitValuation S).hom u = 0 ↔
      u.toMul ∈ (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L))) L).ker := by
    exact (congrArg (· = 0) (sUnitValuation_hom_apply S u)).to_iff.trans
      ((LinearEquiv.map_eq_zero_iff _).trans
        (toMul_eq_one.symm.trans MonoidHom.mem_ker.symm))
  rw [hzero, ← range_unitsToUnit]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.toMul, congrArg Additive.toMul (sUnitInclusion_hom_apply S v).symm⟩
  · rintro ⟨v, hv⟩
    exact ⟨Additive.ofMul v,
      (sUnitInclusion_hom_apply S (Additive.ofMul v)).trans (Additive.toMul.injective hv)⟩

/-- The finite-prime valuation image has finite index in the permutation module. -/
theorem finiteIndex_range_sUnitValuation :
    (sUnitValuation S).hom.toLinearMap.range.toAddSubgroup.FiniteIndex := by
  have : (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L)))
      L).range.toAddSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_toAddSubgroup_iff.mpr
      (TauCeti.finiteIndex_range_unitValuation (𝓞 L) L _)
  have hrange : (sUnitValuation S).hom.toLinearMap.range.toAddSubgroup =
      (Set.unitValuation (S : Set (HeightOneSpectrum (𝓞 L))) L).range.toAddSubgroup.map
        (TauCeti.funMultiplicativeIntLinearEquiv S).toAddMonoidHom := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨_, ⟨u.toMul, rfl⟩, (sUnitValuation_hom_apply S u).symm⟩
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      exact ⟨Additive.ofMul u, sUnitValuation_hom_apply S (Additive.ofMul u)⟩
  rw [hrange]
  exact AddSubgroup.FiniteIndex.map_of_surjective _
    (TauCeti.funMultiplicativeIntLinearEquiv S).surjective

end TauCeti

namespace TauCeti

open CategoryTheory.Limits

attribute [local instance] Units.mulDistribMulActionRight

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L))) [Finite S]

/-- Ordinary units have zero finite-prime valuation, as a composite in `Rep`. -/
@[reassoc (attr := simp)]
theorem sUnitInclusion_comp_sUnitValuation : sUnitInclusion S ≫ sUnitValuation S = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    LinearMap.comp_apply, Rep.zero_hom, Representation.IntertwiningMap.zero_toLinearMap,
    LinearMap.zero_apply]
  exact (LinearMap.mem_ker.mp <| range_sUnitInclusion_eq_ker_sUnitValuation S ▸
    LinearMap.mem_range_self (sUnitInclusion S).hom.toLinearMap u)

/-- The ordinary-unit inclusion followed by the valuation onto its categorical image.
Mathlib's `image.ι` embeds the last term into the finite-prime permutation representation. -/
def sUnitShortComplex : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) where
  X₁ := ordinaryUnitRep K L
  X₂ := sUnitRep S
  X₃ := image (sUnitValuation S)
  f := sUnitInclusion S
  g := factorThruImage (sUnitValuation S)
  zero := comp_factorThruImage_eq_zero (sUnitInclusion_comp_sUnitValuation S)

/-- The S-unit sequence consists of the ordinary-unit inclusion and the canonical valuation
image factorization. This equality also identifies its objects and arrows. -/
@[simp]
theorem sUnitShortComplex_eq_mk :
    sUnitShortComplex S = ShortComplex.mk (sUnitInclusion S)
      (factorThruImage (sUnitValuation S))
      (comp_factorThruImage_eq_zero (sUnitInclusion_comp_sUnitValuation S)) := (rfl)

/-- Ordinary units, S-units, and the valuation image form a short exact sequence. -/
theorem shortExact_sUnitShortComplex : (sUnitShortComplex S).ShortExact := by
  have h : (ShortComplex.mk (sUnitInclusion S) (sUnitValuation S)
      (sUnitInclusion_comp_sUnitValuation S)).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _
      (forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact range_sUnitInclusion_eq_ker_sUnitValuation S
  exact
    { exact := ShortComplex.exact_of_g_is_cokernel _ h.isColimitImage
      mono_f := (Rep.mono_iff_injective _).mpr (sUnitInclusion_injective S)
      epi_g := inferInstanceAs (Epi (factorThruImage (sUnitValuation S))) }

/-- The valuation image has finite categorical cokernel in the permutation representation. -/
instance finite_cokernel_sUnitValuation_image_ι :
    Finite ↑(cokernel (image.ι (sUnitValuation S))) := by
  let F := forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)
  let := finiteIndex_range_sUnitValuation S
  have : Finite ↑(cokernel (sUnitValuation S)) :=
    Finite.of_equiv (ℤ[S] ⧸ (sUnitValuation S).hom.toLinearMap.range.toAddSubgroup)
      ((PreservesCokernel.iso F (sUnitValuation S) ≪≫
        ModuleCat.cokernelIsoRangeQuotient (F.map (sUnitValuation S))).toLinearEquiv.toEquiv.symm)
  exact Finite.of_equiv _ (F.mapIso
    (cokernelImageι (sUnitValuation S))).toLinearEquiv.toEquiv.symm

end TauCeti
