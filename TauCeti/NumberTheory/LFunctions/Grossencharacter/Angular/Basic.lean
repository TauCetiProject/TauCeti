/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Inverse
import TauCeti.Analysis.RCLike.Basic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
import TauCeti.RingTheory.DedekindDomain.Ideal.Basic
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
unramified character of `C_F`.

Because the idelic archimedean component is the **inverse** of the ideal-side monomial,
`angularGrossencharacter F k` has algebraic exponent `-2 * k` at `w.embedding` and `2 * k` at
`conj w.embedding`. The two conjugate exponents sum to `0` (the character is unitary, with
`idealShift = 0`) and differ by `-4 * k` (the complex angular frequency). For `k ≠ 0`,
`angularGrossencharacter F k` has infinite order and admits no ray-class presentation at any
modulus. The explicit evaluation at `(2 + i)` and absence of pure imaginary norm twists are
developed in `TauCeti.NumberTheory.LFunctions.Grossencharacter.Angular.NormTwist`.

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

variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F]

/-- The unique complex infinite place of `F`. -/
private def angularPlace : {w : InfinitePlace F // w.IsComplex} :=
  let w := Classical.arbitrary (InfinitePlace F)
  ⟨w, (IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) F (by norm_num)).isComplex w⟩

private theorem infinitePlace_eq_angularPlace (w : InfinitePlace F) :
    w = (angularPlace F).val :=
  letI : IsTotallyComplex F := IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) F (by norm_num)
  letI : Subsingleton (InfinitePlace F) :=
    InfinitePlace.subsingleton_of_finrank_eq_two
      (TauCeti.finrank_eq_two_of_isCyclotomicExtension_four (K := F))
  Subsingleton.elim _ _

private theorem complexPlace_eq_angularPlace (w : {w : InfinitePlace F // w.IsComplex}) :
    w = angularPlace F :=
  Subtype.ext (infinitePlace_eq_angularPlace F w.val)

private theorem raySubgroup_one_eq_top : raySubgroup (Modulus.one F) = ⊤ := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ F
  exact (raySubgroup_one_eq_top_iff F).mpr
    (GaussianRationals.classNumber_eq_one hζ.minpoly_toInteger_eq_X_sq_add_one
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ))

end CyclotomicFourHelpers

/-! ### The angular unitary ideal weight -/

section IdealWeight

variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F]

open Classical in
/-- The value `(τ α / conj (τ α)) ^ (2 * k)` at `α : 𝓞 F`, extended by `0` at `α = 0`, where `τ`
is the complex embedding of the unique infinite place of `F`. -/
private def angularGenVal (k : ℤ) (α : 𝓞 F) : ℂ :=
  if α = 0 then 0
  else
    let τ := (angularPlace F).val.embedding
    (τ (α : F) / starRingEnd ℂ (τ (α : F))) ^ (2 * k)

private theorem angularGenVal_zero (k : ℤ) : angularGenVal F k 0 = 0 := by
  simp [angularGenVal]

private theorem angularGenVal_of_ne_zero (k : ℤ) {α : 𝓞 F} (hα : α ≠ 0) :
    angularGenVal F k α =
      ((angularPlace F).val.embedding (α : F) /
        starRingEnd ℂ ((angularPlace F).val.embedding (α : F))) ^ (2 * k) := by
  simp [angularGenVal, hα]

private theorem angularGenVal_one (k : ℤ) : angularGenVal F k 1 = 1 := by
  rw [angularGenVal_of_ne_zero F k one_ne_zero]
  simp

private theorem angularGenVal_mul (k : ℤ) (α β : 𝓞 F) :
    angularGenVal F k (α * β) = angularGenVal F k α * angularGenVal F k β := by
  by_cases hα : α = 0
  · simp [hα, angularGenVal_zero]
  by_cases hβ : β = 0
  · simp [hβ, angularGenVal_zero]
  rw [angularGenVal_of_ne_zero F k (mul_ne_zero hα hβ), angularGenVal_of_ne_zero F k hα,
    angularGenVal_of_ne_zero F k hβ]
  push_cast
  rw [map_mul, map_mul, mul_div_mul_comm, mul_zpow]

/-- On a unit `u ∈ (𝓞 F)ˣ`, `(τ u) ^ 4 = 1`, so `conj (τ u) = (τ u)⁻¹` and
`(τ u / conj (τ u)) ^ (2 * k) = ((τ u) ^ 4) ^ k = 1`. -/
private theorem angularGenVal_unit (k : ℤ) (u : (𝓞 F)ˣ) : angularGenVal F k (u : 𝓞 F) = 1 := by
  rw [angularGenVal_of_ne_zero F k u.ne_zero]
  set z : ℂ := (angularPlace F).val.embedding ((u : 𝓞 F) : F)
  have hz4 : z ^ 4 = 1 :=
    TauCeti.apply_unit_pow_four_eq_one_of_four (angularPlace F).val.embedding u
  have hconj : starRingEnd ℂ z = z⁻¹ :=
    (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz4 (by decide))).symm
  have hexp : ((2 : ℕ) : ℤ) * (2 * k) = (4 : ℕ) * k := by ring
  rw [hconj, div_inv_eq_mul, ← sq, ← zpow_natCast, ← zpow_mul, hexp, zpow_mul, zpow_natCast, hz4,
    one_zpow]

/-- Associated elements of `𝓞 F` have the same `angularGenVal`. -/
private theorem angularGenVal_eq_of_associated (k : ℤ) {α β : 𝓞 F} (h : Associated α β) :
    angularGenVal F k α = angularGenVal F k β := by
  obtain ⟨u, rfl⟩ := h
  rw [angularGenVal_mul, angularGenVal_unit, mul_one]

private theorem angularGenVal_ne_zero (k : ℤ) {α : 𝓞 F} (hα : α ≠ 0) :
    angularGenVal F k α ≠ 0 := by
  rw [angularGenVal_of_ne_zero F k hα]
  have hαF : (α : F) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective (𝓞 F) F)).mpr hα
  have hz : (angularPlace F).val.embedding (α : F) ≠ 0 := (map_ne_zero _).mpr hαF
  exact zpow_ne_zero _ (div_ne_zero hz ((map_ne_zero _).mpr hz))

private theorem norm_angularGenVal_of_ne_zero (k : ℤ) {α : 𝓞 F} (hα : α ≠ 0) :
    ‖angularGenVal F k α‖ = 1 := by
  rw [angularGenVal_of_ne_zero F k hα, norm_zpow, norm_div, RCLike.norm_conj]
  have hαF : (α : F) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective (𝓞 F) F)).mpr hα
  have hz : ‖(angularPlace F).val.embedding (α : F)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hαF)
  rw [div_self hz, one_zpow]

/-- The completely multiplicative ideal weight on `Ideal (𝓞 F)` sending `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)`. -/
private def angularIdealWeight (k : ℤ) : MultiplicativeIdealWeight F :=
  letI : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  { toMonoidWithZeroHom :=
      { toFun I := angularGenVal F k (Submodule.IsPrincipal.generator I)
        map_zero' := by
          rw [(Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mp Ideal.zero_eq_bot,
            angularGenVal_zero]
        map_one' := by
          have h1 : Ideal.span {Submodule.IsPrincipal.generator (1 : Ideal (𝓞 F))} =
              Ideal.span {1} := by
            rw [Ideal.span_singleton_generator, Ideal.one_eq_top, Ideal.span_singleton_one]
          rw [angularGenVal_eq_of_associated F k
            (Ideal.span_singleton_eq_span_singleton.mp h1), angularGenVal_one]
        map_mul' I J := by
          have hIJ : Ideal.span {Submodule.IsPrincipal.generator (I * J)} =
              Ideal.span {Submodule.IsPrincipal.generator I *
                Submodule.IsPrincipal.generator J} := by
            simp only [← Ideal.span_singleton_mul_span_singleton,
              Ideal.span_singleton_generator]
          rw [angularGenVal_eq_of_associated F k
            (Ideal.span_singleton_eq_span_singleton.mp hIJ), angularGenVal_mul] }
    finite_setOf_apply_eq_zero := by
      refine Set.Finite.subset Set.finite_empty fun v hv ↦ ?_
      exact absurd hv (angularGenVal_ne_zero F k
        (mt (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr v.ne_bot)) }

private theorem angularIdealWeight_apply (k : ℤ) (I : Ideal (𝓞 F)) :
    letI : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
    angularIdealWeight F k I = angularGenVal F k (Submodule.IsPrincipal.generator I) :=
  rfl

private theorem angularIdealWeight_span_singleton (k : ℤ) (α : 𝓞 F) :
    angularIdealWeight F k (Ideal.span {α}) = angularGenVal F k α := by
  have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  rw [angularIdealWeight_apply]
  exact angularGenVal_eq_of_associated F k
    (Ideal.span_singleton_eq_span_singleton.mp (Ideal.span_singleton_generator (Ideal.span {α})))

private theorem angularIdealWeight_ne_zero (k : ℤ) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    angularIdealWeight F k I ≠ 0 := by
  have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  rw [← Ideal.span_singleton_generator I, angularIdealWeight_span_singleton]
  exact angularGenVal_ne_zero F k
    (mt (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hI)

/-- The bundled `UnitaryIdealWeight F` of Hecke's `k`-th angular character. -/
private def angularUnitaryWeight (k : ℤ) : UnitaryIdealWeight F :=
  ⟨angularIdealWeight F k, fun 𝔭 _ ↦ by
    have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
    rw [← Ideal.span_singleton_generator 𝔭.asIdeal, angularIdealWeight_span_singleton]
    exact norm_angularGenVal_of_ne_zero F k
      (mt (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero 𝔭.asIdeal).mpr 𝔭.ne_bot)⟩

private theorem val_angularUnitaryWeight (k : ℤ) :
    (angularUnitaryWeight F k).val = angularIdealWeight F k :=
  rfl

end IdealWeight

/-! ### The angular Hecke character and its archimedean and local components -/

section HeckeConstruction

variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F]

open Classical in
/-- The algebraic infinity type of Hecke's `k`-th angular character: `-2 * k` at the chosen
embedding of the unique complex place and `2 * k` at its complex conjugate. -/
private def angularAlgebraicInfinityType (k : ℤ) : AlgebraicInfinityType F :=
  fun σ ↦ if σ = (angularPlace F).val.embedding then -(2 * k) else 2 * k

private theorem angularAlgebraicInfinityType_embedding (k : ℤ) :
    angularAlgebraicInfinityType F k (angularPlace F).val.embedding = -(2 * k) := by
  simp [angularAlgebraicInfinityType]

private theorem angularAlgebraicInfinityType_conjugate (k : ℤ) :
    angularAlgebraicInfinityType F k (ComplexEmbedding.conjugate (angularPlace F).val.embedding) =
      2 * k := by
  have hne : ComplexEmbedding.conjugate (angularPlace F).val.embedding ≠
      (angularPlace F).val.embedding := by
    intro h
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (angularPlace F).property
      (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
  simp [angularAlgebraicInfinityType, hne]

/-- Every embedding `σ : F →+* ℂ` is either `(angularPlace F).val.embedding` or its conjugate. -/
private theorem embedding_eq_or_eq_conjugate_four (σ : F →+* ℂ) :
    σ = (angularPlace F).val.embedding ∨
      σ = ComplexEmbedding.conjugate (angularPlace F).val.embedding := by
  have hmk : InfinitePlace.mk σ = (angularPlace F).val :=
    infinitePlace_eq_angularPlace F (InfinitePlace.mk σ)
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · left
    exact (congrArg InfinitePlace.embedding hmk).symm.trans h |>.symm
  · right
    have h' := congrArg ComplexEmbedding.conjugate
      ((congrArg InfinitePlace.embedding hmk).symm.trans h)
    have hconj_inv : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      RingHom.ext fun z ↦ by simp
    rwa [hconj_inv, eq_comm] at h'

/-- The continuous character on `IdeleGroup (𝓞 F) F` reading the angular character of frequency
`-4 * k` at the unique complex place `angularPlace F`. Its restriction to
`ideleCongruenceSubgroup (Modulus.one F)` kills `U ∩ F^× = (𝓞 F)ˣ`. -/
private def angularIdeleArchChar (k : ℤ) : IdeleGroup (𝓞 F) F →ₜ* ℂˣ :=
  ((complexAngularCharacter ^ (-(4 * k))).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (Units.mapContinuousMulEquiv
        (continuousMulEquivComplexOfIsComplex (angularPlace F).property)))).comp
    ⟨(angularPlace F).val.ideleInfiniteCoord, (angularPlace F).val.continuous_ideleInfiniteCoord⟩

private theorem coe_angularIdeleArchChar_apply (k : ℤ) (y : IdeleGroup (𝓞 F) F) :
    (angularIdeleArchChar F k y : ℂ) =
      (continuousMulEquivComplexOfIsComplex (angularPlace F).property
          ((angularPlace F).val.ideleInfiniteCoord y : (angularPlace F).val.Completion) /
        (‖continuousMulEquivComplexOfIsComplex (angularPlace F).property
          ((angularPlace F).val.ideleInfiniteCoord y : (angularPlace F).val.Completion)‖ : ℂ)) ^
        (-(4 * k)) := by
  simp only [angularIdeleArchChar, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    ContinuousMonoidHom.coe_mk, ContinuousMonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val,
    coe_complexAngularCharacter_apply, ContinuousMonoidHom.coe_coe,
    Units.mapContinuousMulEquiv_apply, Units.coe_map, ContinuousMulEquiv.coe_toMulEquiv,
    MonoidHom.coe_ofClass]

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
  rw [MonoidHom.mem_ker] at hy ⊢
  have hmk : QuotientGroup.mk (y : IdeleGroup (𝓞 F) F) = (1 : IdeleClassGroup (𝓞 F) F) := by
    simpa only [MonoidHom.coe_ofClass, ideleCongruenceToClassHom_apply] using hy
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff (y : IdeleGroup (𝓞 F) F)).mp hmk
  have hxmem : IdeleGroup.unitEmbedding (𝓞 F) F x ∈ ideleCongruenceSubgroup (Modulus.one F) :=
    hx.symm ▸ y.property
  obtain ⟨u, -, rfl⟩ :=
    Subgroup.mem_map.mp (unitEmbedding_mem_ideleCongruenceSubgroup_iff.mp hxmem)
  apply Units.ext
  rw [MonoidHom.coe_ofClass, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    TauCeti.ContinuousMonoidHom.subgroupSubtype_apply, ← hx, Units.val_one,
    coe_angularIdeleArchChar_apply, InfinitePlace.ideleInfiniteCoord_unitEmbedding]
  have hval : continuousMulEquivComplexOfIsComplex (angularPlace F).property
      ((Units.map (algebraMap F (angularPlace F).val.Completion).toMonoidHom
        (Units.map (algebraMap (𝓞 F) F).toMonoidHom u) : (angularPlace F).val.Completionˣ) :
          (angularPlace F).val.Completion) =
      (angularPlace F).val.embedding ((u : 𝓞 F) : F) := by
    simp [NumberField.InfinitePlace.Completion.algebraMap_apply_eq_coe,
      continuousMulEquivComplexOfIsComplex_apply]
  rw [hval]
  have hz4 : ((angularPlace F).val.embedding ((u : 𝓞 F) : F)) ^ 4 = 1 :=
    TauCeti.apply_unit_pow_four_eq_one_of_four (angularPlace F).val.embedding u
  have hexp : -(4 * k) = (4 : ℕ) * (-k) := by ring
  rw [Complex.norm_eq_one_of_pow_eq_one hz4 (by decide), Complex.ofReal_one, div_one,
    hexp, zpow_mul, zpow_natCast, hz4, one_zpow]

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
      (continuousMulEquivComplexOfIsComplex (angularPlace F).property
          ((angularPlace F).val.ideleInfiniteCoord (y : IdeleGroup (𝓞 F) F) :
            (angularPlace F).val.Completion) /
        (‖continuousMulEquivComplexOfIsComplex (angularPlace F).property
          ((angularPlace F).val.ideleInfiniteCoord (y : IdeleGroup (𝓞 F) F) :
            (angularPlace F).val.Completion)‖ : ℂ)) ^ (-(4 * k)) := by
  rw [angularHeckeCharacter_ideleCongruenceToClassHom, coe_angularIdeleArchChar_apply]

/-- Every value of `angularHeckeCharacter F k` has norm `1`, so its idelic shift vanishes. -/
private theorem shift_angularHeckeCharacter (k : ℤ) :
    (angularHeckeCharacter F k).shift = 0 := by
  refine (HeckeCharacter.shift_eq_zero_iff _).mpr fun c ↦ ?_
  obtain ⟨y, rfl⟩ :=
    (ideleCongruenceToClassHom_surjective_iff (Modulus.one F)).mpr (raySubgroup_one_eq_top F) c
  rw [coe_angularHeckeCharacter_ideleCongruenceToClassHom]
  set z : ℂ := continuousMulEquivComplexOfIsComplex (angularPlace F).property
    ((angularPlace F).val.ideleInfiniteCoord (y : IdeleGroup (𝓞 F) F) :
      (angularPlace F).val.Completion)
  have hz : z ≠ 0 :=
    (map_ne_zero _).mpr ((angularPlace F).val.ideleInfiniteCoord (y : IdeleGroup (𝓞 F) F)).ne_zero
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
  obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
  refine ContinuousMonoidHom.ext fun z ↦ ?_
  let e := Units.mapContinuousMulEquiv
    (continuousMulEquivComplexOfIsComplex (angularPlace F).property)
  have hmem : IdeleGroup.ofCompletion (𝓞 F) F (angularPlace F).val (e.symm z) ∈
      ideleCongruenceSubgroup (Modulus.one F) :=
    mem_ideleCongruenceSubgroup_one_iff.mpr fun v ↦ by simp
  rw [HeckeCharacter.complexComponent_apply, HeckeCharacter.infiniteComponent_apply,
    IdeleClassGroup.ofCompletion_apply, ← ideleCongruenceToClassHom_apply (Modulus.one F) ⟨_, hmem⟩,
    angularHeckeCharacter_ideleCongruenceToClassHom, complexUnitsCharacter_zero_left]
  simp only [angularIdeleArchChar, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    ContinuousMonoidHom.coe_mk, ContinuousMonoidHom.coe_coe,
    InfinitePlace.ideleInfiniteCoord_ofCompletion_self]
  exact congrArg (complexAngularCharacter ^ (-(4 * k))) (e.apply_symm_apply z)

/-- The continuous infinity type of `angularHeckeCharacter F k` equals the continuous image of
`angularAlgebraicInfinityType F k`. -/
private theorem infinityType_angularHeckeCharacter (k : ℤ) :
    (angularHeckeCharacter F k).infinityType =
      AlgebraicInfinityType.toContinuous (angularAlgebraicInfinityType F k) := by
  refine HeckeCharacter.infinityType_eq_iff.mpr ⟨fun w ↦ ?_, fun w ↦ ?_⟩
  · have : IsTotallyComplex F :=
      IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) F (by norm_num)
    exact IsEmpty.elim inferInstance w
  · obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
    rw [complexComponent_angularHeckeCharacter,
      AlgebraicInfinityType.toContinuous_complexExponent,
      AlgebraicInfinityType.toContinuous_complexAngularFrequency,
      angularAlgebraicInfinityType_embedding, angularAlgebraicInfinityType_conjugate]
    have hsum : ((-(2 * k) : ℤ) : ℂ) + ((2 * k : ℤ) : ℂ) = 0 := by push_cast; ring
    have hdiff : -(2 * k) - 2 * k = -(4 * k) := by ring
    rw [hsum, hdiff]

/-- Evaluating `angularHeckeCharacter F k` at a uniformizer `u` of `v` gives the principal-ideal
weight at `v.asIdeal`: multiplying `ofAdicCompletion v u` by `(unitEmbedding π)⁻¹` for a generator
`π` of `v.asIdeal` produces an everywhere-integral unit idele with infinite coordinate `(τ π)⁻¹`,
on which `z ↦ (z / ‖z‖) ^ (-4 * k)` evaluates to `(τ π / conj (τ π)) ^ (2 * k)`. -/
private theorem finiteComponent_angularHeckeCharacter_of_valued_eq_exp_neg_one (k : ℤ)
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = WithZero.exp (-1)) :
    ((angularHeckeCharacter F k).finiteComponent v u : ℂ) =
      angularIdealWeight F k v.asIdeal := by
  have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  obtain ⟨π, hπ0, hspan⟩ := v.exists_span_singleton_eq_asIdeal
  have hspan1 : Ideal.span {π} = v.asIdeal ^ 1 := by rw [pow_one, hspan]
  have hπF : (algebraMap (𝓞 F) F π) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective (𝓞 F) F)).mpr hπ0
  set x : Fˣ := Units.mk0 (algebraMap (𝓞 F) F π) hπF
  set y : IdeleGroup (𝓞 F) F :=
    IdeleGroup.ofAdicCompletion (𝓞 F) F v u * (IdeleGroup.unitEmbedding (𝓞 F) F x)⁻¹
  have hy_mem : y ∈ ideleCongruenceSubgroup (Modulus.one F) := by
    refine mem_ideleCongruenceSubgroup_one_iff.mpr fun v' ↦ ?_
    have hval_x : Valued.v ((v'.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 F) F x) :
        (v'.adicCompletion F)ˣ) : v'.adicCompletion F) = v'.intValuation π :=
      v'.valued_ideleFiniteCoord_unitEmbedding_of_eq_algebraMap rfl
    simp only [y, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, map_inv₀, hval_x]
    rcases eq_or_ne v' v with rfl | hne
    · rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self, hu,
        v'.intValuation_eq_exp_neg_of_span_singleton_eq_pow hspan1, Nat.cast_one,
        mul_inv_cancel₀ WithZero.exp_ne_zero]
    · rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ hne, Units.val_one,
        map_one, v'.intValuation_eq_one_of_span_singleton_eq_pow hne hspan1, inv_one, mul_one]
  have hy_class : ideleCongruenceToClassHom (Modulus.one F) ⟨y, hy_mem⟩ =
      IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u := by
    rw [ideleCongruenceToClassHom_apply, IdeleClassGroup.ofAdicCompletion_apply, QuotientGroup.eq]
    exact ⟨x, by simp [y, mul_assoc]⟩
  rw [HeckeCharacter.finiteComponent_apply, ← hy_class,
    coe_angularHeckeCharacter_ideleCongruenceToClassHom, ← hspan,
    angularIdealWeight_span_singleton, angularGenVal_of_ne_zero F k hπ0]
  have hinf : continuousMulEquivComplexOfIsComplex (angularPlace F).property
      ((angularPlace F).val.ideleInfiniteCoord y : (angularPlace F).val.Completion) =
      ((angularPlace F).val.embedding (π : F))⁻¹ := by
    simp [y, x, InfinitePlace.ideleInfiniteCoord_ofAdicCompletion,
      InfinitePlace.ideleInfiniteCoord_unitEmbedding,
      NumberField.InfinitePlace.Completion.algebraMap_apply_eq_coe,
      continuousMulEquivComplexOfIsComplex_apply]
  have hexp : -(4 * k) = -(2 * (2 * k)) := by ring
  rw [hinf, hexp]
  exact RCLike.inv_div_norm_inv_zpow_neg_two_mul _ (2 * k)

end HeckeConstruction

/-! ### Construction of `angularGrossencharacter` -/

section AngularGrossencharacter

/-- **Hecke's angular Größencharaktere of `ℚ(i)`**: for `[IsCyclotomicExtension {4} ℚ F]` and
`k : ℤ`, the unramified unitary presentation at `Modulus.one F` sending `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)` for `τ = w.embedding` at the unique complex place `w` of `F`, with
algebraic infinity type `-2 * k` at `τ` and `2 * k` at `conj τ`. -/
def angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    Grossencharacter F (Modulus.one F) where
  toHeckeCharacter := angularHeckeCharacter F k
  unitaryWeight := angularUnitaryWeight F k
  infinityType := angularAlgebraicInfinityType F k
  eq_one_of_mem y hy hw := by
    rw [← ideleCongruenceToClassHom_apply (Modulus.one F) ⟨y, hy⟩, Units.ext_iff,
      coe_angularHeckeCharacter_ideleCongruenceToClassHom, hw (angularPlace F).val, Units.val_one,
      map_one]
    simp
  agreesOnIdentityComponent := by
    rw [infinityType_angularHeckeCharacter]
    exact (ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mpr ⟨rfl, rfl, rfl⟩
  realParity_eq w _ := by
    have : IsTotallyComplex F :=
      IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) F (by norm_num)
    exact IsEmpty.elim inferInstance w
  unitaryWeight_eq_zero I hI := by
    by_cases hbot : I = ⊥
    · simp [hbot]
    · exact absurd (Modulus.isCoprimeTo_iff.mpr ⟨hbot, fun v hv ↦ by simp at hv⟩) hI
  unitaryWeight_apply v _ u hu := by
    rw [val_angularUnitaryWeight, unitaryPart_angularHeckeCharacter,
      finiteComponent_angularHeckeCharacter_of_valued_eq_exp_neg_one F k v u hu]

private theorem toHeckeCharacter_angularGrossencharacter_def (F : Type*) [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).toHeckeCharacter = angularHeckeCharacter F k :=
  rfl

private theorem unitaryWeight_angularGrossencharacter_def (F : Type*) [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).unitaryWeight = angularUnitaryWeight F k :=
  rfl

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
  obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
  exact coe_angularHeckeCharacter_ideleCongruenceToClassHom F k y

/-- At the chosen embedding `w.val.embedding` of the complex place `w` of `F`, the algebraic
infinity type of `angularGrossencharacter F k` has exponent `-(2 * k)`. -/
@[simp]
theorem infinityType_angularGrossencharacter_embedding {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (angularGrossencharacter F k).infinityType w.val.embedding = -(2 * k) := by
  obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
  exact angularAlgebraicInfinityType_embedding F k

/-- At the conjugate embedding `conj w.val.embedding` of the complex place `w` of `F`, the algebraic
infinity type of `angularGrossencharacter F k` has exponent `2 * k`. -/
@[simp]
theorem infinityType_angularGrossencharacter_conjugate {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (angularGrossencharacter F k).infinityType (ComplexEmbedding.conjugate w.val.embedding) =
      2 * k := by
  obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
  exact angularAlgebraicInfinityType_conjugate F k

/-- **Ideal-side value on principal ideals**: for any nonzero `α ∈ 𝓞 F` and the complex place `w`
of `F` with chosen embedding `τ = w.val.embedding`, `angularGrossencharacter F k` sends `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)`. -/
theorem unitaryWeight_angularGrossencharacter_span_singleton {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex})
    {α : 𝓞 F} (hα : α ≠ 0) :
    (angularGrossencharacter F k).unitaryWeight.val (Ideal.span {α}) =
      (w.val.embedding (α : F) / starRingEnd ℂ (w.val.embedding (α : F))) ^ (2 * k) := by
  obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
  rw [unitaryWeight_angularGrossencharacter_def, val_angularUnitaryWeight,
    angularIdealWeight_span_singleton, angularGenVal_of_ne_zero F k hα]

/-- **Hecke's angular characters of `ℚ(i)` exist**: for each `k : ℤ` there is an unramified
presentation whose algebraic infinity type has exponent `-(2 * k)` at an embedding `τ : F →+* ℂ`
and whose unitary ideal weight sends every nonzero principal ideal `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)`. -/
theorem exists_angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    ∃ χ : Grossencharacter F (Modulus.one F), ∃ τ : F →+* ℂ, χ.infinityType τ = -(2 * k) ∧
      ∀ α : 𝓞 F, α ≠ 0 →
        χ.unitaryWeight.val (Ideal.span {α}) = (τ (α : F) / starRingEnd ℂ (τ (α : F))) ^ (2 * k) :=
  ⟨angularGrossencharacter F k, (angularPlace F).val.embedding,
    infinityType_angularGrossencharacter_embedding k (angularPlace F),
    fun _ hα ↦ unitaryWeight_angularGrossencharacter_span_singleton k (angularPlace F) hα⟩

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
    (angularGrossencharacter F k).toHeckeCharacter.shift = 0 :=
  shift_angularHeckeCharacter F k

/-- `angularGrossencharacter F k` is its own unitary part. -/
@[simp]
theorem unitaryPart_toHeckeCharacter_angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).toHeckeCharacter.unitaryPart =
      (angularGrossencharacter F k).toHeckeCharacter :=
  unitaryPart_angularHeckeCharacter F k

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
      complexUnitsCharacter 0 (-(4 * k)) :=
  complexComponent_angularHeckeCharacter F k w

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
  rcases embedding_eq_or_eq_conjugate_four F σ with rfl | rfl
  · simp [infinityType_angularGrossencharacter_embedding 0 (angularPlace F)]
  · simp [infinityType_angularGrossencharacter_conjugate 0 (angularPlace F)]

/-- At `k = 0`, the Hecke character of `angularGrossencharacter F 0` is trivial. -/
theorem toHeckeCharacter_angularGrossencharacter_zero (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] :
    (angularGrossencharacter F 0).toHeckeCharacter = 1 := by
  rw [angularGrossencharacter_zero, Grossencharacter.toHeckeCharacter_ofRayClassCharacter, map_one]

/-- At `k = 0`, the unitary ideal weight of `angularGrossencharacter F 0` is `1`. -/
theorem unitaryWeight_angularGrossencharacter_zero (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] :
    (angularGrossencharacter F 0).unitaryWeight = 1 := by
  have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  apply Subtype.ext
  refine MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_
  obtain ⟨π, hπ0, hspan⟩ := v.exists_span_singleton_eq_asIdeal
  rw [← hspan, unitaryWeight_angularGrossencharacter_span_singleton 0 (angularPlace F) hπ0,
    hspan, UnitaryIdealWeight.val_one, MultiplicativeIdealWeight.one_apply]
  simp [v.ne_bot]

/-- Negating the angular index `k` inverts the presentation (`Grossencharacter.inverse`). -/
theorem angularGrossencharacter_neg (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    angularGrossencharacter F (-k) = (angularGrossencharacter F k).inverse := by
  apply Grossencharacter.ext_of_infinityType_eq (raySubgroup_one_eq_top F)
  ext σ
  rcases embedding_eq_or_eq_conjugate_four F σ with rfl | rfl
  · simp [infinityType_angularGrossencharacter_embedding _ (angularPlace F)]
  · simp [infinityType_angularGrossencharacter_conjugate _ (angularPlace F)]

/-- Adding angular indices adds the algebraic infinity types. -/
theorem infinityType_angularGrossencharacter_add (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (j k : ℤ) :
    (angularGrossencharacter F (j + k)).infinityType =
      (angularGrossencharacter F j).infinityType +
        (angularGrossencharacter F k).infinityType := by
  ext σ
  rcases embedding_eq_or_eq_conjugate_four F σ with rfl | rfl
  · simp only [Pi.add_apply, infinityType_angularGrossencharacter_embedding _ (angularPlace F)]
    ring
  · simp only [Pi.add_apply, infinityType_angularGrossencharacter_conjugate _ (angularPlace F)]
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
  set z : ℂ := continuousMulEquivComplexOfIsComplex (angularPlace F).property
    ((angularPlace F).val.ideleInfiniteCoord (y : IdeleGroup (𝓞 F) F) :
      (angularPlace F).val.Completion)
  have hz : z / (‖z‖ : ℂ) ≠ 0 := by
    have hz0 : z ≠ 0 :=
      (map_ne_zero _).mpr ((angularPlace F).val.ideleInfiniteCoord (y : IdeleGroup (𝓞 F) F)).ne_zero
    exact div_ne_zero hz0 (by simp [hz0])
  have hexp : -(4 * (j + k)) = -(4 * j) + -(4 * k) := by ring
  rw [hexp, zpow_add₀ hz]

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
    unitaryWeight_angularGrossencharacter_span_singleton (j + k) (angularPlace F) hπ0,
    unitaryWeight_angularGrossencharacter_span_singleton j (angularPlace F) hπ0,
    unitaryWeight_angularGrossencharacter_span_singleton k (angularPlace F) hπ0]
  have hπF : (π : F) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective (𝓞 F) F)).mpr hπ0
  have hz : (angularPlace F).val.embedding (π : F) ≠ 0 := (map_ne_zero _).mpr hπF
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
  have hinj := congrFun (congrArg Grossencharacter.infinityType h) (angularPlace F).val.embedding
  rw [infinityType_angularGrossencharacter_embedding j (angularPlace F),
    infinityType_angularGrossencharacter_embedding k (angularPlace F)] at hinj
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
    have hk0 := congrFun hn (angularPlace F).val.embedding
    rw [infinityType_angularGrossencharacter_embedding k (angularPlace F), Pi.zero_apply] at hk0
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
