/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Orientation
public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RingTheory.RootsOfUnity.ZMod
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Inflation
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The prescription property of the cyclotomic character

Let `K` be a field in which the prime `p` is invertible and `χ = χ_cyc` the `p`-adic cyclotomic
character of its absolute Galois group `G_K`. This file proves that `χ` has Labute's prescription
property: every reduction `H¹(G_K, I(χ)/pⁱ) → H¹(G_K, I(χ)/p)` of the twisted coefficients is
surjective. When `K` contains a primitive `p`-th root of unity, the same holds for the cyclotomic
orientation of the maximal pro-`p` Galois group `G_K(p)`, the character through which `χ`
factors. The proof is Kummer theory, with no input from local duality or reciprocity.

A primitive `pʲ`-th root of unity `ζ` of the separable closure identifies `I(χ)/pʲ` with the
roots of unity `μ_{pʲ}`, by `x ↦ ζ ^ x`. This is equivariant because `G_K` acts on `μ_{pʲ}`
through `χ` modulo `pʲ` (`TauCeti.smul_kummerCoeff_eq_nsmul_localCyclotomicCharacter`), which is
how `χ` is defined. If the root used at level `j ≤ i` is the `p ^ (i - j)`-th power of the root
used at level `i`, the reduction `I(χ)/pⁱ → I(χ)/pʲ` becomes the power map `μ_{pⁱ} → μ_{pʲ}`. On
Kummer classes that power map only changes the level, so it is surjective on `H¹` because every
class at level `pʲ` is a Kummer class (`TauCeti.explicitCoeff1_kummerCoeffPow_surjective`).

The prescription property is the hypothesis under which a character of a Demushkin group is its
canonical character. It descends from `G_K` to the maximal pro-`p` quotient `G_K(p)`
(`TauCeti.hasPrescriptionProperty_comp_quotientMk_proPKernel_iff`), because twisted inflation
along `G_K → G_K(p)` is bijective and compatible with the reductions. The cyclotomic orientation
pulls back to `χ` along this map, so it has the property as well.

## Main definitions

* `TauCeti.zModTwistEquivKummerCoeff`: the identification `I(χ_cyc)/pʲ ≃ μ_{pʲ}`, `x ↦ ζ ^ x`, of a
  primitive `pʲ`-th root of unity `ζ`.

## Main results

* `TauCeti.smul_kummerCoeff_eq_nsmul_localCyclotomicCharacter`: the Galois action on `μ_{pʲ}` is
  multiplication by the cyclotomic character modulo `pʲ`.
* `TauCeti.zModTwistEquivKummerCoeff_smul`: the identification is equivariant.
* `TauCeti.kummerCoeffPow_zModTwistEquivKummerCoeff`: it turns the reductions into power maps.
* `TauCeti.continuousLocalCyclotomicCharacter_hasPrescriptionProperty`: the cyclotomic character
  has the prescription property.
* `TauCeti.cyclotomicOrientation_hasPrescriptionProperty`: if `μ_p ⊆ K`, the cyclotomic
  orientation of `G_K(p)` has the prescription property.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section

namespace TauCeti

open ContCohomology

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]

/-- **The Galois action on `μ_{pʲ}` is the cyclotomic character modulo `pʲ`**: an element `τ` of
`Gal(Kˢ/K)` raises every `pʲ`-th root of unity of `Kˢ` to the power `χ(τ) mod pʲ`, where `χ` is
read on `τ` through the comparison with `Field.absoluteGaloisGroup K`. -/
theorem smul_kummerCoeff_eq_nsmul_localCyclotomicCharacter [NeZero (p : K)] {j : ℕ}
    (τ : AbsoluteGaloisGroup K) (x : KummerCoeff K (p ^ j)) :
    τ • x = (PadicInt.toZModPow j (localCyclotomicCharacter p K
      ((absoluteGaloisGroupRestrictEquiv K).symm τ) : ℤ_[p])).val • x := by
  set σ := (absoluteGaloisGroupRestrictEquiv K).symm τ
  set u : (SeparableClosure K)ˣ := x.toMul.1
  -- the defining equation of the cyclotomic character, in the algebraic closure
  have hu : ((u : SeparableClosure K) : AlgebraicClosure K) ^ p ^ j = 1 := by
    rw [← IntermediateField.coe_pow, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2,
      Units.val_one, IntermediateField.coe_one]
  have hspec := cyclotomicCharacter.spec p σ.toRingEquiv _ hu
  refine Additive.toMul.injective (Subtype.ext (Units.ext (Subtype.ext ?_)))
  simp only [toMul_nsmul, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, Additive.toMul_smul,
    rootsOfUnity.coe_smul, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass]
  rw [localCyclotomicCharacter_apply, ← hspec, ← absoluteGaloisGroupRestrictEquiv_symm_apply_coe]
  -- `σ.toRingEquiv` and `σ` have the same coercion to functions (`AlgEquiv.coe_ringEquiv`), which
  -- `rw` does not see through the type synonym `Field.absoluteGaloisGroup K`
  rfl

variable (p K) in
/-- **The identification `I(χ_cyc)/pʲ ≃ μ_{pʲ}`** of a primitive `pʲ`-th root of unity `ζ` of
`Kˢ`: the residue class of `x` goes to `ζ ^ x`. It is equivariant for the comparison of
`Field.absoluteGaloisGroup K` with `Gal(Kˢ/K)` (`TauCeti.zModTwistEquivKummerCoeff_smul`). -/
noncomputable def zModTwistEquivKummerCoeff {j : ℕ} {ζ : (SeparableClosure K)ˣ}
    (hζ : IsPrimitiveRoot ζ (p ^ j)) :
    ZModTwist (continuousLocalCyclotomicCharacter p K) j ≃+ KummerCoeff K (p ^ j) :=
  (ZModTwist.equiv _ j).trans hζ.zmodEquivRootsOfUnity

/-- The identification `I(χ_cyc)/pʲ ≃ μ_{pʲ}` sends the residue class of `x` to `ζ ^ x`. -/
@[simp]
theorem coe_toMul_zModTwistEquivKummerCoeff {j : ℕ} {ζ : (SeparableClosure K)ˣ}
    (hζ : IsPrimitiveRoot ζ (p ^ j)) (x : ZModTwist (continuousLocalCyclotomicCharacter p K) j) :
    ((zModTwistEquivKummerCoeff p K hζ x).toMul : (SeparableClosure K)ˣ) = ζ ^ x.val.val := by
  rw [zModTwistEquivKummerCoeff, AddEquiv.trans_apply, ZModTwist.equiv_apply,
    ← ZMod.natCast_zmod_val x.val, IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_apply_natCast,
    ZMod.natCast_zmod_val]

/-- **The identification `I(χ_cyc)/pʲ ≃ μ_{pʲ}` is equivariant**: the action of `σ` on the twisted
module, multiplication by `χ(σ) mod pʲ`, corresponds to the action of the restriction of `σ` to
`Kˢ` on the roots of unity. -/
@[simp]
theorem zModTwistEquivKummerCoeff_smul [NeZero (p : K)] {j : ℕ} {ζ : (SeparableClosure K)ˣ}
    (hζ : IsPrimitiveRoot ζ (p ^ j)) (τ : AbsoluteGaloisGroup K)
    (x : ZModTwist (continuousLocalCyclotomicCharacter p K) j) :
    zModTwistEquivKummerCoeff p K hζ ((absoluteGaloisGroupRestrictEquiv K).symm τ • x) =
      τ • zModTwistEquivKummerCoeff p K hζ x := by
  rw [smul_kummerCoeff_eq_nsmul_localCyclotomicCharacter, ← map_nsmul]
  congr 1
  refine ZModTwist.ext ?_
  rw [ZModTwist.val_smul, ZModTwist.val_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val,
    charScalar_apply, continuousLocalCyclotomicCharacter_apply]

/-- **The identifications turn reductions into power maps**: if the root used at level `j ≤ i`
is the `pⁱ / pʲ`-th power of the root `ζ` used at level `i`, the reduction
`I(χ_cyc)/pⁱ → I(χ_cyc)/pʲ` corresponds to the power map `μ_{pⁱ} → μ_{pʲ}`. -/
theorem kummerCoeffPow_zModTwistEquivKummerCoeff {i j : ℕ} (h : j ≤ i)
    {ζ : (SeparableClosure K)ˣ} (hζ : IsPrimitiveRoot ζ (p ^ i))
    (x : ZModTwist (continuousLocalCyclotomicCharacter p K) i) :
    kummerCoeffPow K (pow_dvd_pow p h) (zModTwistEquivKummerCoeff p K hζ x) =
      zModTwistEquivKummerCoeff p K
        (hζ.pow (pow_pos (Fact.out : p.Prime).pos i) (Nat.div_mul_cancel (pow_dvd_pow p h)).symm)
        (ZModTwist.reduce _ h x) := by
  have hζ' : IsPrimitiveRoot (ζ ^ (p ^ i / p ^ j)) (p ^ j) :=
    hζ.pow (pow_pos (Fact.out : p.Prime).pos i) (Nat.div_mul_cancel (pow_dvd_pow p h)).symm
  refine Additive.toMul.injective (Subtype.ext ?_)
  rw [coe_toMul_kummerCoeffPow, coe_toMul_zModTwistEquivKummerCoeff,
    coe_toMul_zModTwistEquivKummerCoeff, ← pow_mul, mul_comm, pow_mul]
  generalize ζ ^ (p ^ i / p ^ j) = ζ' at hζ' ⊢
  rw [ZModTwist.val_reduce, ← ZMod.natCast_zmod_val x.val, map_natCast, ZMod.val_natCast,
    ZMod.val_natCast, ← Nat.mod_mod_of_dvd _ (pow_dvd_pow p h), hζ'.eq_orderOf, pow_mod_orderOf]

variable (p K) in
/-- **The cyclotomic character has the prescription property**: for a field `K` in
which `p` is invertible, every reduction `H¹(G_K, I(χ_cyc)/pⁱ) → H¹(G_K, I(χ_cyc)/p)` is
surjective. Through a compatible choice of primitive roots of unity the reduction is the power map
`H¹(G_K, μ_{pⁱ}) → H¹(G_K, μ_p)`, which is onto because every class at level `p` is the Kummer
class of a unit of `K`, and so the image of the Kummer class of that unit at level `pⁱ`. -/
theorem continuousLocalCyclotomicCharacter_hasPrescriptionProperty [NeZero (p : K)] :
    HasPrescriptionProperty (continuousLocalCyclotomicCharacter p K) := by
  rw [hasPrescriptionProperty_iff]
  intro i hi y
  have hpi : IsUnit ((p ^ i : ℕ) : K) := by
    rw [Nat.cast_pow]
    exact (NeZero.ne (p : K)).isUnit.pow i
  -- compatible primitive roots of unity `ζ` of order `pⁱ` and `ζ'` of order `p`
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (SeparableClosure K) (p ^ i)
  have hζ := hξ.isUnit_unit (pow_ne_zero i (Fact.out : p.Prime).ne_zero)
  have hζ' := hζ.pow (Nat.pos_of_ne_zero (pow_ne_zero i (Fact.out : p.Prime).ne_zero))
    (Nat.div_mul_cancel (pow_dvd_pow p hi)).symm
  -- the identifications `H¹(G_K, I(χ_cyc)/pʲ) ≃ H¹(Gal(Kˢ/K), μ_{pʲ})` at the two levels
  let E {j : ℕ} {η : (SeparableClosure K)ˣ} (hη : IsPrimitiveRoot η (p ^ j)) :=
    explicitMap1Equiv (Field.absoluteGaloisGroup K)
      (ZModTwist (continuousLocalCyclotomicCharacter p K) j) (AbsoluteGaloisGroup K)
      (KummerCoeff K (p ^ j)) (absoluteGaloisGroupRestrictEquiv K).symm
      (zModTwistEquivKummerCoeff p K hη) continuous_of_discreteTopology
      continuous_of_discreteTopology (zModTwistEquivKummerCoeff_smul hη)
  -- they carry the reduction to the power map
  have hsq (w) :
      E hζ' (explicitCoeff1 _ _ (ZModTwist.reduce _ hi) continuous_of_discreteTopology w) =
        explicitCoeff1 _ _ (kummerCoeffPow K (pow_dvd_pow p hi)) continuous_of_discreteTopology
          (E hζ w) := by
    simp only [E, explicitMap1Equiv_apply, explicitCoeff1_eq_explicitMap1]
    refine explicitMap1_explicitMap1_of_comp_eq (hφ := ?_) (hqf := ?_) ..
    · exact ContinuousMonoidHom.ext fun _ => rfl
    · exact AddMonoidHom.ext fun x =>
        (kummerCoeffPow_zModTwistEquivKummerCoeff hi hζ x).symm
  obtain ⟨z, hz⟩ := explicitCoeff1_kummerCoeffPow_surjective hpi (pow_dvd_pow p hi) (E hζ' y)
  obtain ⟨w, rfl⟩ := (E hζ).surjective z
  exact ⟨w, (E hζ').injective ((hsq w).trans hz)⟩

variable (p K) in
/-- **The cyclotomic orientation has the prescription property**: if `K` contains a primitive
`p`-th root of unity, then for the cyclotomic orientation `χ` of the maximal pro-`p` Galois group
`G_K(p)`, every reduction `H¹(G_K(p), I(χ)/pⁱ) → H¹(G_K(p), I(χ)/p)` is surjective. The
orientation pulls back to the cyclotomic character of `G_K`, which has the property, and the
property descends along `G_K → G_K(p)`. -/
theorem cyclotomicOrientation_hasPrescriptionProperty (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    HasPrescriptionProperty (cyclotomicOrientation p K hmu) := by
  have : NeZero (p : K) := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact hζ.neZero'
  -- `absoluteGaloisGroupProPQuotientMap` is by definition (an `abbrev`) the quotient map by the
  -- pro-`p` kernel, so the pullback lemma rewrites the descended statement
  rw [← hasPrescriptionProperty_comp_quotientMk_proPKernel_iff,
    cyclotomicOrientation_comp_absoluteGaloisGroupProPQuotientMap]
  exact continuousLocalCyclotomicCharacter_hasPrescriptionProperty p K

end TauCeti
