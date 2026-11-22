/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Inverse
import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
import TauCeti.NumberTheory.LFunctions.Grossencharacter.Conductor
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
import TauCeti.RingTheory.DedekindDomain.Ideal.Basic
import TauCeti.RingTheory.RootsOfUnity.Complex
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Descent

/-!
# Hecke's angular Größencharaktere of `ℚ(i)`

Let `F` be a fourth cyclotomic extension of `ℚ`, so that `F ≅ ℚ(i)` has ring of integers `ℤ[i]`,
class number `1`, unit group `{±1, ±i}` of order `4`, no real places, and a unique complex place
`w`. For each integer `k`, Hecke attached to `F` an unramified unitary Größencharakter sending a
nonzero principal ideal `(α)` to

`(τ α / conj (τ α)) ^ (2 * k) = (τ α / ‖τ α‖) ^ (4 * k)`,

where `τ = w.embedding : F →+* ℂ` is the chosen complex embedding of `w`. Modifying the generator
`α` by a unit `u ∈ (𝓞 F)ˣ` multiplies `τ α` by a fourth root of unity, on which
`z ↦ (z / conj z) ^ (2 * k) = z ^ (4 * k)` is trivial, so the ideal value depends only on `(α)`.

On the idele class group `C_F = 𝔸_F^× / F^×`, every class has a representative in the open
everywhere-unramified subgroup `U = ∏_v 𝒪_v^× × F_∞^×` because `𝓞 F` is a principal ideal domain,
and `U ∩ F^× = (𝓞 F)ˣ` consists of the fourth roots of unity. Sending `y ∈ U` to
`(z / ‖z‖) ^ (-4 * k)` at the complex coordinate `z` of `y` therefore descends to a continuous
unramified character of `C_F`, which `Grossencharacter.mkOfFiniteConductor` presents at
`Modulus.one F`.

Because the idelic archimedean component is the **inverse** of the ideal-side monomial,
`angularGrossencharacter F k` has algebraic exponent `-2 * k` at `w.embedding` and `2 * k` at
`conj w.embedding`. The two conjugate exponents sum to `0` (the character is unitary, with
`idealShift = 0`) and differ by `-4 * k` (the complex angular frequency); Hecke's unit relation
(`Grossencharacter.compatibility_inv`) reads off the principal-ideal value
`(τ α / conj (τ α)) ^ (2 * k)` from these exponents. For `k ≠ 0`, `angularGrossencharacter F k`
has infinite order and admits no ray-class presentation at any modulus. The explicit evaluation at
`(2 + i)` and absence of pure imaginary norm twists are developed in
`TauCeti.NumberTheory.LFunctions.Grossencharacter.Angular.NormTwist`.

## Main definitions

* `TauCeti.LFunctions.angularGrossencharacter`: Hecke's unramified angular Größencharakter of `F`
  of index `k : ℤ`, presented at `Modulus.one F`.

## Main results

* `TauCeti.LFunctions.exists_angularGrossencharacter`: existence of the presentation with exponent
  `-2 * k` at an embedding `τ` and principal-ideal values `(τ α / conj (τ α)) ^ (2 * k)`.
* `TauCeti.LFunctions.toHeckeCharacter_angularGrossencharacter_ideleCongruenceToClassHom`: explicit
  evaluation of the presented Hecke character on everywhere-unramified congruence representatives.
* `TauCeti.LFunctions.unitaryWeight_angularGrossencharacter_span_singleton`: explicit value on
  nonzero principal ideals `(α)`.
* `TauCeti.LFunctions.angularGrossencharacter_infinityType`: vanishing complex modulus exponent,
  complex angular frequency `± 4 * k`, and vanishing ideal-side shift.
* `TauCeti.LFunctions.angularGrossencharacter_zero`,
  `TauCeti.LFunctions.angularGrossencharacter_neg`,
  `TauCeti.LFunctions.toHeckeCharacter_angularGrossencharacter_add`,
  `TauCeti.LFunctions.unitaryWeight_angularGrossencharacter_add`: group laws in `k : ℤ`.
* `TauCeti.LFunctions.angularGrossencharacter_injective`,
  `TauCeti.LFunctions.isFiniteOrder_toHeckeCharacter_angularGrossencharacter_iff`,
  `TauCeti.LFunctions.not_mem_range_ofRayClassCharacter_toHeckeCharacter_angularGrossencharacter`:
  injectivity in `k`, infinite order for `k ≠ 0`, and absence of ray-class presentations.

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen*,
  Math. Z. **1** (1918), 357–376, and **6** (1920), 11–51.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField

namespace TauCeti.LFunctions

open GlobalNumberFields TauCeti.NumberField

section CyclotomicFourHelpers

private theorem embedding_coe_ne_zero {F : Type*} [Field F] {w : InfinitePlace F} {α : 𝓞 F}
    (hα : α ≠ 0) : w.embedding (α : F) ≠ 0 :=
  (map_ne_zero _).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hα)

variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F]

private theorem raySubgroup_one_eq_top : raySubgroup (Modulus.one F) = ⊤ := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ F
  exact (raySubgroup_one_eq_top_iff F).mpr
    (GaussianRationals.classNumber_eq_one hζ.minpoly_toInteger_eq_X_sq_add_one
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ))

private theorem embedding_unit_pow_four_eq_one (u : (𝓞 F)ˣ) :
    ((complexPlaceFour F).val.embedding ((u : 𝓞 F) : F)) ^ 4 = 1 := by
  have h := congrArg
    (((complexPlaceFour F).val.embedding.toMonoidHom.comp
      (algebraMap (𝓞 F) F).toMonoidHom).comp (Units.coeHom (𝓞 F)))
    (TauCeti.units_pow_four_eq_one_four u)
  simpa using h

end CyclotomicFourHelpers

/-! ### The angular Hecke character and its archimedean and local components -/

section HeckeConstruction

variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F]

open Classical in
/-- The algebraic infinity type of Hecke's `k`-th angular character: `-2 * k` at the chosen
embedding of the unique complex place and `2 * k` at its complex conjugate. -/
private def angularAlgebraicInfinityType (k : ℤ) : AlgebraicInfinityType F :=
  fun σ ↦ if σ = (complexPlaceFour F).val.embedding then -(2 * k) else 2 * k

private theorem angularAlgebraicInfinityType_embedding (k : ℤ) :
    angularAlgebraicInfinityType F k (complexPlaceFour F).val.embedding = -(2 * k) := by
  simp [angularAlgebraicInfinityType]

private theorem angularAlgebraicInfinityType_conjugate (k : ℤ) :
    angularAlgebraicInfinityType F k
        (ComplexEmbedding.conjugate (complexPlaceFour F).val.embedding) = 2 * k := by
  have hne : ComplexEmbedding.conjugate (complexPlaceFour F).val.embedding ≠
      (complexPlaceFour F).val.embedding := by
    intro h
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (complexPlaceFour F).property
      (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
  simp [angularAlgebraicInfinityType, hne]

/-- The continuous homomorphism extracting the complex coordinate at `complexPlaceFour F` as a
unit in `ℂˣ`. -/
private def angularCoordHom : IdeleGroup (𝓞 F) F →ₜ* ℂˣ :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (Units.mapContinuousMulEquiv
      (continuousMulEquivComplexOfIsComplex (complexPlaceFour F).property))).comp
    ⟨(complexPlaceFour F).val.ideleInfiniteCoord,
      (complexPlaceFour F).val.continuous_ideleInfiniteCoord⟩

private theorem coe_angularCoordHom_apply (y : IdeleGroup (𝓞 F) F) :
    (angularCoordHom F y : ℂ) =
      continuousMulEquivComplexOfIsComplex (complexPlaceFour F).property
        ((complexPlaceFour F).val.ideleInfiniteCoord y :
          (complexPlaceFour F).val.Completion) :=
  rfl

private theorem coe_angularCoordHom_unitEmbedding_units (u : (𝓞 F)ˣ) :
    (angularCoordHom F (IdeleGroup.unitEmbedding (𝓞 F) F
        (Units.map (algebraMap (𝓞 F) F).toMonoidHom u)) : ℂ) =
      (complexPlaceFour F).val.embedding ((u : 𝓞 F) : F) := by
  simp [coe_angularCoordHom_apply, InfinitePlace.ideleInfiniteCoord_unitEmbedding,
    NumberField.InfinitePlace.Completion.algebraMap_apply_eq_coe,
    continuousMulEquivComplexOfIsComplex_apply]

private theorem angularCoordHom_ofCompletion (z : ℂˣ) :
    angularCoordHom F (IdeleGroup.ofCompletion (𝓞 F) F (complexPlaceFour F).val
      ((Units.mapContinuousMulEquiv
        (continuousMulEquivComplexOfIsComplex (complexPlaceFour F).property)).symm z)) = z := by
  simp only [angularCoordHom, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    ContinuousMonoidHom.coe_mk, ContinuousMonoidHom.coe_coe,
    InfinitePlace.ideleInfiniteCoord_ofCompletion_self]
  exact (Units.mapContinuousMulEquiv
    (continuousMulEquivComplexOfIsComplex (complexPlaceFour F).property)).apply_symm_apply z

private theorem angularCoordHom_ofAdicCompletion (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    angularCoordHom F (IdeleGroup.ofAdicCompletion (𝓞 F) F v u) = 1 := by
  simp [angularCoordHom]

/-- The continuous character on `IdeleGroup (𝓞 F) F` reading the angular character of frequency
`-4 * k` at the unique complex place `complexPlaceFour F`. Its restriction to
`ideleCongruenceSubgroup (Modulus.one F)` kills `U ∩ F^× = (𝓞 F)ˣ`. -/
private def angularIdeleArchChar (k : ℤ) : IdeleGroup (𝓞 F) F →ₜ* ℂˣ :=
  (complexAngularCharacter ^ (-(4 * k))).comp (angularCoordHom F)

private theorem coe_angularIdeleArchChar_apply (k : ℤ) (y : IdeleGroup (𝓞 F) F) :
    (angularIdeleArchChar F k y : ℂ) =
      ((angularCoordHom F y : ℂ) / (‖(angularCoordHom F y : ℂ)‖ : ℂ)) ^ (-(4 * k)) := by
  simp [angularIdeleArchChar, ContinuousMonoidHom.zpow_apply, coe_complexAngularCharacter_apply]

/-- Principal ideles in `ideleCongruenceSubgroup (Modulus.one F)` come from `(𝓞 F)ˣ`, which are
fourth roots of unity and therefore lie in the kernel of `angularIdeleArchChar F k`. -/
private theorem ideleCongruenceToClassHom_ker_le (k : ℤ) :
    (ideleCongruenceToClassHom (Modulus.one F) :
        ideleCongruenceSubgroup (Modulus.one F) →* IdeleClassGroup (𝓞 F) F).ker ≤
      (((angularIdeleArchChar F k).comp
        (TauCeti.ContinuousMonoidHom.subgroupSubtype
          (ideleCongruenceSubgroup (Modulus.one F)))) :
          ideleCongruenceSubgroup (Modulus.one F) →* ℂˣ).ker := by
  intro y hy
  obtain ⟨u, -, hyu⟩ := mem_ker_ideleCongruenceToClassHom_iff.mp hy
  rw [MonoidHom.mem_ker, MonoidHom.coe_ofClass, ContinuousMonoidHom.coe_comp,
    Function.comp_apply, TauCeti.ContinuousMonoidHom.subgroupSubtype_apply, hyu]
  apply Units.ext
  rw [coe_angularIdeleArchChar_apply, coe_angularCoordHom_unitEmbedding_units, Units.val_one,
    ← mul_neg]
  exact Complex.div_norm_zpow_mul_eq_one_of_pow_eq_one
    (embedding_unit_pow_four_eq_one F u) (by decide) (-k)

/-- Hecke's `k`-th angular idele class character on `F`. -/
private def angularHeckeCharacter (k : ℤ) : HeckeCharacter F :=
  ContinuousMonoidHom.liftOfIsQuotientMap (ideleCongruenceToClassHom (Modulus.one F))
    ((isQuotientMap_ideleCongruenceToClassHom_iff (Modulus.one F)).mpr
      (raySubgroup_one_eq_top F))
    ((angularIdeleArchChar F k).comp
      (TauCeti.ContinuousMonoidHom.subgroupSubtype (ideleCongruenceSubgroup (Modulus.one F))))
    (ideleCongruenceToClassHom_ker_le F k)

private theorem angularHeckeCharacter_ideleCongruenceToClassHom (k : ℤ)
    (y : ideleCongruenceSubgroup (Modulus.one F)) :
    angularHeckeCharacter F k (ideleCongruenceToClassHom (Modulus.one F) y) =
      angularIdeleArchChar F k y := by
  rw [angularHeckeCharacter, ContinuousMonoidHom.liftOfIsQuotientMap_comp_apply,
    ContinuousMonoidHom.coe_comp, Function.comp_apply,
    TauCeti.ContinuousMonoidHom.subgroupSubtype_apply]

private theorem coe_angularHeckeCharacter_ideleCongruenceToClassHom (k : ℤ)
    (y : ideleCongruenceSubgroup (Modulus.one F)) :
    ((angularHeckeCharacter F k (ideleCongruenceToClassHom (Modulus.one F) y) : ℂˣ) : ℂ) =
      ((angularCoordHom F (y : IdeleGroup (𝓞 F) F) : ℂ) /
        (‖(angularCoordHom F (y : IdeleGroup (𝓞 F) F) : ℂ)‖ : ℂ)) ^ (-(4 * k)) := by
  rw [angularHeckeCharacter_ideleCongruenceToClassHom, coe_angularIdeleArchChar_apply]

/-- Every value of `angularHeckeCharacter F k` has norm `1`, so its idelic shift vanishes. -/
private theorem shift_angularHeckeCharacter (k : ℤ) :
    (angularHeckeCharacter F k).shift = 0 := by
  refine (HeckeCharacter.shift_eq_zero_iff _).mpr fun c ↦ ?_
  obtain ⟨y, rfl⟩ :=
    (ideleCongruenceToClassHom_surjective_iff (Modulus.one F)).mpr (raySubgroup_one_eq_top F) c
  rw [coe_angularHeckeCharacter_ideleCongruenceToClassHom]
  have hz : (angularCoordHom F (y : IdeleGroup (𝓞 F) F) : ℂ) ≠ 0 := Units.ne_zero _
  rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hz),
    one_zpow]

private theorem unitaryPart_angularHeckeCharacter (k : ℤ) :
    (angularHeckeCharacter F k).unitaryPart = angularHeckeCharacter F k :=
  (HeckeCharacter.unitaryPart_eq_self_iff _).mpr (shift_angularHeckeCharacter F k)

/-- At the complex place `w`, the archimedean component of `angularHeckeCharacter F k` is
`complexUnitsCharacter 0 (-(4 * k))`. -/
private theorem complexComponent_angularHeckeCharacter (k : ℤ)
    (w : {w : InfinitePlace F // w.IsComplex}) :
    (angularHeckeCharacter F k).complexComponent w = complexUnitsCharacter 0 (-(4 * k)) := by
  obtain rfl : w = complexPlaceFour F := Subsingleton.elim w _
  refine ContinuousMonoidHom.ext fun z ↦ ?_
  let e := Units.mapContinuousMulEquiv
    (continuousMulEquivComplexOfIsComplex (complexPlaceFour F).property)
  have hmem : IdeleGroup.ofCompletion (𝓞 F) F (complexPlaceFour F).val (e.symm z) ∈
      ideleCongruenceSubgroup (Modulus.one F) :=
    mem_ideleCongruenceSubgroup_one_iff.mpr fun v ↦ by simp
  rw [HeckeCharacter.complexComponent_apply, HeckeCharacter.infiniteComponent_apply,
    IdeleClassGroup.ofCompletion_apply, ← ideleCongruenceToClassHom_apply (Modulus.one F) ⟨_, hmem⟩,
    angularHeckeCharacter_ideleCongruenceToClassHom, complexUnitsCharacter_zero_left,
    angularIdeleArchChar, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    angularCoordHom_ofCompletion]

/-- The continuous infinity type of `angularHeckeCharacter F k` equals the continuous image of
`angularAlgebraicInfinityType F k`. -/
private theorem infinityType_angularHeckeCharacter (k : ℤ) :
    (angularHeckeCharacter F k).infinityType =
      AlgebraicInfinityType.toContinuous (angularAlgebraicInfinityType F k) := by
  refine HeckeCharacter.infinityType_eq_iff.mpr ⟨fun w ↦ IsEmpty.elim inferInstance w, fun w ↦ ?_⟩
  obtain rfl : w = complexPlaceFour F := Subsingleton.elim w _
  rw [complexComponent_angularHeckeCharacter,
    AlgebraicInfinityType.toContinuous_complexExponent,
    AlgebraicInfinityType.toContinuous_complexAngularFrequency,
    angularAlgebraicInfinityType_embedding, angularAlgebraicInfinityType_conjugate]
  have hsum : ((-(2 * k) : ℤ) : ℂ) + ((2 * k : ℤ) : ℂ) = 0 := by push_cast; ring
  have hdiff : -(2 * k) - 2 * k = -(4 * k) := by ring
  rw [hsum, hdiff]

/-- `angularHeckeCharacter F k` is unramified at every finite place, so its finite conductor is
`⊤`. -/
private theorem finiteConductor_angularHeckeCharacter (k : ℤ) :
    (angularHeckeCharacter F k).finiteConductor = ⊤ := by
  refine (HeckeCharacter.finiteConductor_eq_top_iff _).mpr fun v ↦
    (HeckeCharacter.conductorExponent_eq_zero_iff _ v).mpr fun u hu ↦ ?_
  have hmem : IdeleGroup.ofAdicCompletion (𝓞 F) F v u ∈
      ideleCongruenceSubgroup (Modulus.one F) :=
    mem_ideleCongruenceSubgroup_one_iff.mpr fun v' ↦ by
      rcases eq_or_ne v' v with rfl | hne
      · simpa using (HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff v').mp hu
      · simp [hne]
  rw [HeckeCharacter.finiteComponent_apply, IdeleClassGroup.ofAdicCompletion_apply,
    ← ideleCongruenceToClassHom_apply (Modulus.one F) ⟨_, hmem⟩,
    angularHeckeCharacter_ideleCongruenceToClassHom, angularIdeleArchChar,
    ContinuousMonoidHom.coe_comp, Function.comp_apply, angularCoordHom_ofAdicCompletion, map_one]

end HeckeConstruction

/-! ### Construction of `angularGrossencharacter` -/

section AngularGrossencharacter

/-- **Hecke's angular Größencharaktere of `ℚ(i)`**: for `[IsCyclotomicExtension {4} ℚ F]` and
`k : ℤ`, the unramified unitary presentation at `Modulus.one F` sending `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)` for `τ = w.embedding` at the unique complex place `w` of `F`, with
algebraic infinity type `-2 * k` at `τ` and `2 * k` at `conj τ`. -/
def angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    Grossencharacter F (Modulus.one F) :=
  Grossencharacter.mkOfFiniteConductor (angularHeckeCharacter F k)
    (angularAlgebraicInfinityType F k)
    (by
      rw [infinityType_angularHeckeCharacter]
      exact (ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mpr ⟨rfl, rfl, rfl⟩)
    (Modulus.one_finitePart.trans (finiteConductor_angularHeckeCharacter F k).symm)
    (fun w _ ↦ IsEmpty.elim inferInstance w)

private theorem toHeckeCharacter_angularGrossencharacter_def (F : Type*) [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).toHeckeCharacter = angularHeckeCharacter F k :=
  Grossencharacter.toHeckeCharacter_mkOfFiniteConductor _ _ _ _ _

end AngularGrossencharacter

/-! ### Specification, projections, and group laws in `k` -/

section SpecificationAndGroupLaws

/-- **Evaluation of `angularGrossencharacter F k` on congruence representatives**: on the class of
an everywhere-unramified idele `y ∈ ideleCongruenceSubgroup (Modulus.one F)`, the presented Hecke
character evaluates at the complex place `w` to `(z / ‖z‖) ^ (-(4 * k))`, where `z` is the
complex coordinate of `y` at `w` under `continuousMulEquivComplexOfIsComplex w.property`. -/
theorem toHeckeCharacter_angularGrossencharacter_ideleCongruenceToClassHom {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ)
    (w : {w : InfinitePlace F // w.IsComplex})
    (y : ideleCongruenceSubgroup (Modulus.one F)) :
    (((angularGrossencharacter F k).toHeckeCharacter
      (ideleCongruenceToClassHom (Modulus.one F) y) : ℂˣ) : ℂ) =
      (continuousMulEquivComplexOfIsComplex w.property
          (w.val.ideleInfiniteCoord (y : IdeleGroup (𝓞 F) F) : w.val.Completion) /
        (‖continuousMulEquivComplexOfIsComplex w.property
          (w.val.ideleInfiniteCoord (y : IdeleGroup (𝓞 F) F) : w.val.Completion)‖ : ℂ)) ^
        (-(4 * k)) := by
  obtain rfl : w = complexPlaceFour F := Subsingleton.elim w _
  rw [toHeckeCharacter_angularGrossencharacter_def,
    coe_angularHeckeCharacter_ideleCongruenceToClassHom]
  rfl

/-- At the chosen embedding `w.val.embedding` of the complex place `w` of `F`, the algebraic
infinity type of `angularGrossencharacter F k` has exponent `-(2 * k)`. -/
@[simp]
theorem infinityType_angularGrossencharacter_embedding {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (angularGrossencharacter F k).infinityType w.val.embedding = -(2 * k) := by
  obtain rfl : w = complexPlaceFour F := Subsingleton.elim w _
  rw [angularGrossencharacter, Grossencharacter.infinityType_mkOfFiniteConductor,
    angularAlgebraicInfinityType_embedding]

/-- At the conjugate embedding `conj w.val.embedding` of the complex place `w` of `F`, the algebraic
infinity type of `angularGrossencharacter F k` has exponent `2 * k`. -/
@[simp]
theorem infinityType_angularGrossencharacter_conjugate {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (angularGrossencharacter F k).infinityType (ComplexEmbedding.conjugate w.val.embedding) =
      2 * k := by
  obtain rfl : w = complexPlaceFour F := Subsingleton.elim w _
  rw [angularGrossencharacter, Grossencharacter.infinityType_mkOfFiniteConductor,
    angularAlgebraicInfinityType_conjugate]

open Classical in
/-- **Ideal-side value on principal ideals**: for any nonzero `α ∈ 𝓞 F` and the complex place `w`
of `F` with chosen embedding `τ = w.val.embedding`, `angularGrossencharacter F k` sends `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)`. -/
theorem unitaryWeight_angularGrossencharacter_span_singleton {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex})
    {α : 𝓞 F} (hα : α ≠ 0) :
    (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {α}) =
      (w.val.embedding (α : F) / starRingEnd ℂ (w.val.embedding (α : F))) ^ (2 * k) := by
  obtain rfl : w = complexPlaceFour F := Subsingleton.elim w _
  set w4 := complexPlaceFour F
  have hαF : (algebraMap (𝓞 F) F α) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hα
  let x : Fˣ := Units.mk0 (algebraMap (𝓞 F) F α) hαF
  have hcompat := (angularGrossencharacter F k).compatibility_inv x (isCongrOne_one x) α rfl
  have hidealShift : (angularGrossencharacter F k).idealShift = 0 := by
    rw [Grossencharacter.idealShift_def, toHeckeCharacter_angularGrossencharacter_def,
      shift_angularHeckeCharacter, neg_zero]
  rw [hidealShift, Complex.ofReal_zero, Complex.cpow_zero, mul_one] at hcompat
  have hne : w4.val.embedding ≠ ComplexEmbedding.conjugate w4.val.embedding := by
    intro h
    exact InfinitePlace.not_isReal_iff_isComplex.mpr w4.property
      (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
  have huniv : (Finset.univ : Finset (F →+* ℂ)) =
      {w4.val.embedding, ComplexEmbedding.conjugate w4.val.embedding} := by
    ext τ
    simpa using w4.val.embedding_eq_or_eq_conjugate τ
  rw [hcompat, huniv, Finset.prod_pair hne, infinityType_angularGrossencharacter_embedding,
    infinityType_angularGrossencharacter_conjugate]
  have hxval : (x : F) = (α : F) := rfl
  rw [hxval, ComplexEmbedding.conjugate_coe_eq, mul_inv, ← zpow_neg, neg_neg, ← zpow_neg,
    div_eq_mul_inv, mul_zpow, inv_zpow, zpow_neg]

/-- **Hecke's angular characters of `ℚ(i)` exist**: for each `k : ℤ` there is an unramified
presentation whose algebraic infinity type has exponent `-(2 * k)` at an embedding `τ : F →+* ℂ`
and whose unitary ideal weight sends every nonzero principal ideal `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)`. -/
theorem exists_angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    ∃ χ : Grossencharacter F (Modulus.one F), ∃ τ : F →+* ℂ, χ.infinityType τ = -(2 * k) ∧
      ∀ α : 𝓞 F, α ≠ 0 →
        χ.unitaryWeight.val (Ideal.span {α}) = (τ (α : F) / starRingEnd ℂ (τ (α : F))) ^ (2 * k) :=
  ⟨angularGrossencharacter F k, (complexPlaceFour F).val.embedding,
    infinityType_angularGrossencharacter_embedding k (complexPlaceFour F),
    fun _ hα ↦ unitaryWeight_angularGrossencharacter_span_singleton k (complexPlaceFour F) hα⟩

/-- Because `angularGrossencharacter F k` is unramified everywhere, its unitary ideal weight has no
bad primes. -/
@[simp]
theorem badPrimes_unitaryWeight_angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).unitaryWeight.val.badPrimes = ∅ := by
  rw [(angularGrossencharacter F k).badPrimes_unitaryWeight]
  simp

/-- `angularGrossencharacter F k` has idelic shift `0` (it is unitary). -/
@[simp]
theorem shift_toHeckeCharacter_angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).toHeckeCharacter.shift = 0 := by
  rw [toHeckeCharacter_angularGrossencharacter_def]
  exact shift_angularHeckeCharacter F k

/-- `angularGrossencharacter F k` is its own unitary part. -/
@[simp]
theorem unitaryPart_toHeckeCharacter_angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).toHeckeCharacter.unitaryPart =
      (angularGrossencharacter F k).toHeckeCharacter := by
  rw [toHeckeCharacter_angularGrossencharacter_def]
  exact unitaryPart_angularHeckeCharacter F k

/-- `angularGrossencharacter F k` has ideal-side shift `0`. -/
@[simp]
theorem idealShift_angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).idealShift = 0 := by
  rw [Grossencharacter.idealShift_def, shift_toHeckeCharacter_angularGrossencharacter, neg_zero]

/-- `angularGrossencharacter F k` is everywhere unramified at finite places: its finite conductor is
the unit ideal `⊤`. -/
@[simp]
theorem finiteConductor_toHeckeCharacter_angularGrossencharacter (F : Type*) [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).toHeckeCharacter.finiteConductor = ⊤ :=
  (angularGrossencharacter F k).finiteConductor_eq_top_of_finitePart_eq_top
    Modulus.one_finitePart

/-- At the complex place `w` of `F`, the archimedean component of `angularGrossencharacter F k` is
`complexUnitsCharacter 0 (-(4 * k))`. -/
@[simp]
theorem complexComponent_toHeckeCharacter_angularGrossencharacter {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ)
    (w : {w : InfinitePlace F // w.IsComplex}) :
    (angularGrossencharacter F k).toHeckeCharacter.complexComponent w =
      complexUnitsCharacter 0 (-(4 * k)) := by
  rw [toHeckeCharacter_angularGrossencharacter_def]
  exact complexComponent_angularHeckeCharacter F k w

/-- At the complex place `w` of `F`, the continuous infinity type of `angularGrossencharacter F k`
has complex modulus exponent `0`. -/
@[simp high]
theorem complexExponent_angularGrossencharacter {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (AlgebraicInfinityType.toContinuous
      (angularGrossencharacter F k).infinityType).complexExponent w = 0 := by
  rw [AlgebraicInfinityType.toContinuous_complexExponent,
    infinityType_angularGrossencharacter_embedding,
    infinityType_angularGrossencharacter_conjugate]
  push_cast
  ring

/-- At the complex place `w` of `F`, the continuous infinity type of `angularGrossencharacter F k`
has angular frequency `-(4 * k)` (with respect to `w.val.embedding`). -/
@[simp high]
theorem complexAngularFrequency_angularGrossencharacter {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (AlgebraicInfinityType.toContinuous
      (angularGrossencharacter F k).infinityType).complexAngularFrequency w = -(4 * k) := by
  rw [AlgebraicInfinityType.toContinuous_complexAngularFrequency,
    infinityType_angularGrossencharacter_embedding,
    infinityType_angularGrossencharacter_conjugate]
  ring

/-- **Infinity-type summary for `angularGrossencharacter F k`**: the two conjugate algebraic
exponents sum to `0` (`complexExponent = 0` and `idealShift = 0`) and differ by `± (4 * k)`. -/
theorem angularGrossencharacter_infinityType
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ)
    (w : {w : InfinitePlace F // w.IsComplex}) :
    (AlgebraicInfinityType.toContinuous
        (angularGrossencharacter F k).infinityType).complexExponent w = 0 ∧
      ((AlgebraicInfinityType.toContinuous
          (angularGrossencharacter F k).infinityType).complexAngularFrequency w = 4 * k ∨
        (AlgebraicInfinityType.toContinuous
          (angularGrossencharacter F k).infinityType).complexAngularFrequency w = -(4 * k)) ∧
      (angularGrossencharacter F k).idealShift = 0 :=
  ⟨complexExponent_angularGrossencharacter k w,
    Or.inr (complexAngularFrequency_angularGrossencharacter k w),
    idealShift_angularGrossencharacter F k⟩

/-- At `k = 0`, `angularGrossencharacter F 0` is the presentation of the trivial ray-class
character at `Modulus.one F`. -/
@[simp]
theorem angularGrossencharacter_zero (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] :
    angularGrossencharacter F 0 = Grossencharacter.ofRayClassCharacter 1 := by
  apply Grossencharacter.ext_of_infinityType_eq (raySubgroup_one_eq_top F)
  ext σ
  rcases (complexPlaceFour F).val.embedding_eq_or_eq_conjugate σ with rfl | rfl
  · simp [infinityType_angularGrossencharacter_embedding 0 (complexPlaceFour F)]
  · simp [infinityType_angularGrossencharacter_conjugate 0 (complexPlaceFour F)]

/-- At `k = 0`, the Hecke character of `angularGrossencharacter F 0` is trivial. -/
theorem toHeckeCharacter_angularGrossencharacter_zero (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] :
    (angularGrossencharacter F 0).toHeckeCharacter = 1 := by
  rw [angularGrossencharacter_zero, Grossencharacter.toHeckeCharacter_ofRayClassCharacter, map_one]

/-- At `k = 0`, the unitary ideal weight of `angularGrossencharacter F 0` is `1`. -/
theorem unitaryWeight_angularGrossencharacter_zero (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] :
    (angularGrossencharacter F 0).unitaryWeight = 1 := by
  simp

/-- Negating the angular index `k` inverts the presentation (`Grossencharacter.inverse`). -/
theorem angularGrossencharacter_neg (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    angularGrossencharacter F (-k) = (angularGrossencharacter F k).inverse := by
  apply Grossencharacter.ext_of_infinityType_eq (raySubgroup_one_eq_top F)
  ext σ
  rcases (complexPlaceFour F).val.embedding_eq_or_eq_conjugate σ with rfl | rfl
  · simp [infinityType_angularGrossencharacter_embedding _ (complexPlaceFour F)]
  · simp [infinityType_angularGrossencharacter_conjugate _ (complexPlaceFour F)]

/-- Adding angular indices adds the algebraic infinity types. -/
theorem infinityType_angularGrossencharacter_add (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (j k : ℤ) :
    (angularGrossencharacter F (j + k)).infinityType =
      (angularGrossencharacter F j).infinityType +
        (angularGrossencharacter F k).infinityType := by
  ext σ
  rcases (complexPlaceFour F).val.embedding_eq_or_eq_conjugate σ with rfl | rfl
  · simp only [Pi.add_apply, infinityType_angularGrossencharacter_embedding _ (complexPlaceFour F)]
    ring
  · simp only [Pi.add_apply, infinityType_angularGrossencharacter_conjugate _ (complexPlaceFour F)]
    ring

/-- Adding angular indices multiplies the underlying Hecke characters. -/
theorem toHeckeCharacter_angularGrossencharacter_add (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (j k : ℤ) :
    (angularGrossencharacter F (j + k)).toHeckeCharacter =
      (angularGrossencharacter F j).toHeckeCharacter *
        (angularGrossencharacter F k).toHeckeCharacter := by
  refine ContinuousMonoidHom.ext fun c ↦ Units.ext ?_
  obtain ⟨y, rfl⟩ :=
    (ideleCongruenceToClassHom_surjective_iff (Modulus.one F)).mpr (raySubgroup_one_eq_top F) c
  simp only [ContinuousMonoidHom.mul_apply, Units.val_mul,
    toHeckeCharacter_angularGrossencharacter_def,
    coe_angularHeckeCharacter_ideleCongruenceToClassHom]
  have hz : (angularCoordHom F (y : IdeleGroup (𝓞 F) F) : ℂ) ≠ 0 := Units.ne_zero _
  have hdiv :
      (angularCoordHom F (y : IdeleGroup (𝓞 F) F) : ℂ) /
          (‖(angularCoordHom F (y : IdeleGroup (𝓞 F) F) : ℂ)‖ : ℂ) ≠ 0 :=
    div_ne_zero hz (by simp [hz])
  have hexp : -(4 * (j + k)) = -(4 * j) + -(4 * k) := by ring
  rw [hexp, zpow_add₀ hdiv]

/-- Adding angular indices multiplies the unitary ideal weights. -/
theorem unitaryWeight_angularGrossencharacter_add (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (j k : ℤ) :
    (angularGrossencharacter F (j + k)).unitaryWeight =
      (angularGrossencharacter F j).unitaryWeight *
        (angularGrossencharacter F k).unitaryWeight := by
  have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  apply Subtype.ext
  refine MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_
  obtain ⟨π, hπ0, hspan⟩ := v.exists_span_singleton_eq_asIdeal
  rw [UnitaryIdealWeight.val_mul, MultiplicativeIdealWeight.mul_apply, ← hspan,
    unitaryWeight_angularGrossencharacter_span_singleton (j + k) (complexPlaceFour F) hπ0,
    unitaryWeight_angularGrossencharacter_span_singleton j (complexPlaceFour F) hπ0,
    unitaryWeight_angularGrossencharacter_span_singleton k (complexPlaceFour F) hπ0]
  have hz := embedding_coe_ne_zero (w := (complexPlaceFour F).val) hπ0
  have hexp : 2 * (j + k) = 2 * j + 2 * k := by ring
  rw [hexp, zpow_add₀ (div_ne_zero hz ((map_ne_zero _).mpr hz))]

/-- Taking the `n`-th power of the unitary ideal weight of `angularGrossencharacter F k` multiplies
the angular index by `n`. In particular, for `n = 2`, the companion weight `χ_u ^ 2` of the
`3-4-1` nonvanishing argument is the weight of `angularGrossencharacter F (2 * k)`. -/
@[simp]
theorem unitaryWeight_angularGrossencharacter_pow (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (n : ℕ) :
    (angularGrossencharacter F k).unitaryWeight ^ n =
      (angularGrossencharacter F (n * k)).unitaryWeight := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, (unitaryWeight_angularGrossencharacter_zero F).symm]
  | succ n ih =>
    rw [pow_succ, ih, ← unitaryWeight_angularGrossencharacter_add]
    exact congrArg (fun m ↦ (angularGrossencharacter F m).unitaryWeight) (by push_cast; ring)

end SpecificationAndGroupLaws

/-! ### Injectivity, infinite order, and absence of ray-class presentations -/

section InfiniteOrder

/-- Distinct integers `k` give distinct angular Größencharaktere. -/
theorem angularGrossencharacter_injective (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] :
    Function.Injective (angularGrossencharacter F) := by
  intro j k h
  have hinj :=
    congrFun (congrArg Grossencharacter.infinityType h) (complexPlaceFour F).val.embedding
  rw [infinityType_angularGrossencharacter_embedding j (complexPlaceFour F),
    infinityType_angularGrossencharacter_embedding k (complexPlaceFour F)] at hinj
  omega

/-- Two angular Größencharaktere of `F` are equal if and only if their indices are equal. -/
@[simp]
theorem angularGrossencharacter_eq_iff {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] {j k : ℤ} :
    angularGrossencharacter F j = angularGrossencharacter F k ↔ j = k :=
  (angularGrossencharacter_injective F).eq_iff

/-- **An angular Größencharakter has finite order if and only if `k = 0`.** For `k ≠ 0`, its
nonzero algebraic infinity type prevents it from agreeing on the identity component with the zero
algebraic infinity type of any finite-order character. -/
@[simp]
theorem isFiniteOrder_toHeckeCharacter_angularGrossencharacter_iff {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {k : ℤ} :
    (angularGrossencharacter F k).toHeckeCharacter.IsFiniteOrder ↔ k = 0 := by
  refine ⟨fun hfin ↦ ?_, ?_⟩
  · have hn := (angularGrossencharacter F k).infinityType_eq_zero_of_isFiniteOrder hfin
    have hk0 := congrFun hn (complexPlaceFour F).val.embedding
    rw [infinityType_angularGrossencharacter_embedding k (complexPlaceFour F), Pi.zero_apply]
      at hk0
    omega
  · rintro rfl
    rw [angularGrossencharacter_zero, Grossencharacter.toHeckeCharacter_ofRayClassCharacter]
    exact HeckeCharacter.isFiniteOrder_ofRayClassCharacter 1

/-- For `k ≠ 0`, `angularGrossencharacter F k` does not arise from a ray class character at **any**
modulus `𝔪 : Modulus F`. -/
theorem not_mem_range_ofRayClassCharacter_toHeckeCharacter_angularGrossencharacter {F : Type*}
    [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] {k : ℤ} (hk : k ≠ 0)
    (𝔪 : Modulus F) :
    (angularGrossencharacter F k).toHeckeCharacter ∉
      (HeckeCharacter.ofRayClassCharacter 𝔪).range := by
  rintro ⟨η, hη⟩
  apply hk
  rw [← isFiniteOrder_toHeckeCharacter_angularGrossencharacter_iff (F := F), ← hη]
  exact HeckeCharacter.isFiniteOrder_ofRayClassCharacter η

/-- For `k ≠ 0`, `angularGrossencharacter F k` is not in the range of
`Grossencharacter.ofRayClassCharacter` at `Modulus.one F`. -/
theorem not_mem_range_ofRayClassCharacter_angularGrossencharacter (F : Type*) [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {k : ℤ} (hk : k ≠ 0) :
    angularGrossencharacter F k ∉
      Set.range (Grossencharacter.ofRayClassCharacter (K := F) (𝔪 := Modulus.one F)) := by
  rintro ⟨η, hη⟩
  exact not_mem_range_ofRayClassCharacter_toHeckeCharacter_angularGrossencharacter hk
    (Modulus.one F)
    ⟨η, (Grossencharacter.toHeckeCharacter_ofRayClassCharacter η).symm.trans
      (congrArg Grossencharacter.toHeckeCharacter hη)⟩

end InfiniteOrder

end TauCeti.LFunctions
