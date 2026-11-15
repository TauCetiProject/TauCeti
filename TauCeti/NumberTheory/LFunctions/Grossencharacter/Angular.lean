/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Inverse
import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

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

By Hecke's unit relation (`Grossencharacter.compatibility`), the idelic archimedean component is
the **inverse** of the ideal-side monomial: `angularGrossencharacter F k` has algebraic exponent
`-2 * k` at `w.embedding` and `2 * k` at `conj w.embedding`. The two conjugate exponents sum to `0`
(the character is unitary, with `idealShift = 0`) and differ by `-4 * k` (the complex angular
frequency). At `α = 2 + i`, the ideal value is `((3 ± 4i) / 5) ^ (2 * k)`, which for `k ≠ 0` is
nonreal and equals the inverse — not the value — of the archimedean monomial.

For `k ≠ 0`, `angularGrossencharacter F k` has infinite order, admits no ray-class presentation at
any modulus, and its unitary ideal weight is not an imaginary norm twist on good ideals because the
conjugate ideals `(2 + i)` and `(2 - i)` share absolute norm `5` while taking non-real inverse
values.

## Main definitions

* `TauCeti.LFunctions.angularGrossencharacter`: Hecke's unramified angular Größencharakter of `F`
  of index `k : ℤ`, presented at `Modulus.one F`.

## Main results

* `TauCeti.LFunctions.exists_angularGrossencharacter`: existence of the presentation with exponent
  `-2 * k` at an embedding `τ` and principal-ideal values `(τ α / conj (τ α)) ^ (2 * k)`.
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
* `TauCeti.LFunctions.im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero`,
  `TauCeti.LFunctions.unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_prod`: the nonreal
  sign check at `2 + i`.
* `TauCeti.LFunctions.angularGrossencharacter_not_isNormTwist`: for `k ≠ 0`, the unitary ideal
  weight is not a pure imaginary norm twist on its good ideals.

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

/-- Every infinite place of a fourth cyclotomic field is complex. -/
private theorem isTotallyComplex_four : IsTotallyComplex F :=
  GaussianRationals.isTotallyComplex
    (IsCyclotomicExtension.zeta_spec 4 ℚ F).minpoly_toInteger_eq_X_sq_add_one

/-- A fourth cyclotomic field has no real infinite places. -/
private theorem isEmpty_realInfinitePlace_four : IsEmpty {w : InfinitePlace F // w.IsReal} :=
  ⟨fun w ↦ InfinitePlace.not_isReal_iff_isComplex.mpr ((isTotallyComplex_four F).isComplex w.1) w.2⟩

/-- A fourth cyclotomic field has a unique infinite place, since `[F : ℚ] = 2` and `r₁ = 0`. -/
private theorem subsingleton_infinitePlace_four : Subsingleton (InfinitePlace F) := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ F
  have hmin := hζ.minpoly_toInteger_eq_X_sq_add_one
  have hgen : Algebra.adjoin ℚ {(hζ.toInteger : F)} = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  apply Fintype.card_le_one_iff_subsingleton.mp
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    GaussianRationals.nrRealPlaces_eq_zero hmin,
    GaussianRationals.nrComplexPlaces_eq_one hmin hgen]

/-- The unique complex infinite place of `F`. -/
private def angularPlace : {w : InfinitePlace F // w.IsComplex} :=
  let w := Classical.arbitrary (InfinitePlace F)
  ⟨w, (isTotallyComplex_four F).isComplex w⟩

private theorem infinitePlace_eq_angularPlace (w : InfinitePlace F) :
    w = (angularPlace F).1 :=
  @Subsingleton.elim _ (subsingleton_infinitePlace_four F) _ _

private theorem complexPlace_eq_angularPlace (w : {w : InfinitePlace F // w.IsComplex}) :
    w = angularPlace F :=
  Subtype.ext (infinitePlace_eq_angularPlace F w.1)

/-- Every unit of `𝓞 F = ℤ[i]` is a fourth root of unity (`±1` or `±i`). -/
private theorem units_pow_four_eq_one_four (u : (𝓞 F)ˣ) : u ^ 4 = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ F
  obtain ⟨a, b, hu⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) (u : 𝓞 F)
  have hab : a ^ 2 + b ^ 2 = 1 :=
    (hζ.isUnit_intCast_add_intCast_mul_toInteger_iff_of_four).mp (hu ▸ u.isUnit)
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg b]
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg b]
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg a]
  have hb2 : b ≤ 1 := by nlinarith [sq_nonneg a]
  have hpow4 : ((u : 𝓞 F)) ^ 4 = 1 := by
    have h4 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
    rw [← hu]
    interval_cases a <;> interval_cases b <;> first
      | omega
      | (norm_num; done)
      | (push_cast; linear_combination h4)
  exact Units.ext (by simpa using hpow4)

/-- Over `F`, every idele class lies in the ray subgroup of the trivial modulus, since `𝓞 F` has
class number `1`. -/
private theorem raySubgroup_one_eq_top_four : raySubgroup (Modulus.one F) = ⊤ := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ F
  have : Subsingleton (ClassGroup (𝓞 F)) :=
    Fintype.card_le_one_iff_subsingleton.mp
      (GaussianRationals.classNumber_eq_one hζ.minpoly_toInteger_eq_X_sq_add_one
        (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)).le
  have : Subsingleton (RayClassGroup (Modulus.one F)) :=
    (oneEquivClassGroup (K := F)).toEquiv.subsingleton
  rw [← ker_rayClassQuotient, eq_top_iff]
  exact fun _ _ ↦ MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)

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
    let τ := (angularPlace F).1.embedding
    (τ (α : F) / starRingEnd ℂ (τ (α : F))) ^ (2 * k)

private theorem angularGenVal_zero (k : ℤ) : angularGenVal F k 0 = 0 := by
  simp [angularGenVal]

private theorem angularGenVal_of_ne_zero (k : ℤ) {α : 𝓞 F} (hα : α ≠ 0) :
    angularGenVal F k α =
      ((angularPlace F).1.embedding (α : F) /
        starRingEnd ℂ ((angularPlace F).1.embedding (α : F))) ^ (2 * k) := by
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

private theorem embedding_unit_pow_four_eq_one (u : (𝓞 F)ˣ) (τ : F →+* ℂ) :
    (τ ((u : 𝓞 F) : F)) ^ 4 = 1 := by
  rw [← map_pow, RingOfIntegers.coe_eq_algebraMap, ← map_pow,
    show (u : 𝓞 F) ^ 4 = 1 from congrArg Units.val (units_pow_four_eq_one_four F u), map_one,
    map_one]

/-- On a unit `u ∈ (𝓞 F)ˣ`, `(τ u) ^ 4 = 1`, so `conj (τ u) = (τ u)⁻¹` and
`(τ u / conj (τ u)) ^ (2 * k) = ((τ u) ^ 4) ^ k = 1`. -/
private theorem angularGenVal_unit (k : ℤ) (u : (𝓞 F)ˣ) : angularGenVal F k (u : 𝓞 F) = 1 := by
  rw [angularGenVal_of_ne_zero F k u.ne_zero]
  set z : ℂ := (angularPlace F).1.embedding ((u : 𝓞 F) : F)
  have hz4 : z ^ 4 = 1 := embedding_unit_pow_four_eq_one F u (angularPlace F).1.embedding
  have hconj : starRingEnd ℂ z = z⁻¹ :=
    (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz4 (by decide))).symm
  rw [hconj, div_inv_eq_mul, ← sq, ← zpow_natCast, ← zpow_mul,
    show ((2 : ℕ) : ℤ) * (2 * k) = (4 : ℕ) * k by ring, zpow_mul, zpow_natCast, hz4, one_zpow]

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
  have hz : (angularPlace F).1.embedding (α : F) ≠ 0 := (map_ne_zero _).mpr hαF
  exact zpow_ne_zero _ (div_ne_zero hz ((map_ne_zero _).mpr hz))

private theorem norm_angularGenVal_of_ne_zero (k : ℤ) {α : 𝓞 F} (hα : α ≠ 0) :
    ‖angularGenVal F k α‖ = 1 := by
  rw [angularGenVal_of_ne_zero F k hα, norm_zpow, norm_div, RCLike.norm_conj]
  have hαF : (α : F) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective (𝓞 F) F)).mpr hα
  have hz : ‖(angularPlace F).1.embedding (α : F)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hαF)
  rw [div_self hz, one_zpow]

omit [NumberField F] [IsCyclotomicExtension {4} ℚ F] in
private theorem span_generator_four [IsPrincipalIdealRing (𝓞 F)] (I : Ideal (𝓞 F)) :
    Ideal.span {Submodule.IsPrincipal.generator I} = I :=
  Submodule.IsPrincipal.span_singleton_generator I

/-- The completely multiplicative ideal weight on `Ideal (𝓞 F)` sending `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)`. -/
private def angularIdealWeight (k : ℤ) : MultiplicativeIdealWeight F := by
  haveI : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  refine
    { toMonoidWithZeroHom :=
        { toFun I := angularGenVal F k (Submodule.IsPrincipal.generator I)
          map_zero' := by
            have h0 : Submodule.IsPrincipal.generator (0 : Ideal (𝓞 F)) = 0 :=
              Ideal.span_singleton_eq_bot.mp ((span_generator_four F _).trans Ideal.zero_eq_bot)
            rw [h0, angularGenVal_zero]
          map_one' := by
            have h1 : Ideal.span {Submodule.IsPrincipal.generator (1 : Ideal (𝓞 F))} =
                Ideal.span {1} := by
              rw [span_generator_four, Ideal.one_eq_top, Ideal.span_singleton_one]
            rw [angularGenVal_eq_of_associated F k
              (Ideal.span_singleton_eq_span_singleton.mp h1), angularGenVal_one]
          map_mul' I J := by
            have hIJ : Ideal.span {Submodule.IsPrincipal.generator (I * J)} =
                Ideal.span {Submodule.IsPrincipal.generator I *
                  Submodule.IsPrincipal.generator J} := by
              simp only [← Ideal.span_singleton_mul_span_singleton, span_generator_four]
            rw [angularGenVal_eq_of_associated F k
              (Ideal.span_singleton_eq_span_singleton.mp hIJ), angularGenVal_mul] }
      finite_setOf_apply_eq_zero := by
        refine Set.Finite.subset Set.finite_empty fun v hv ↦ ?_
        have hgen0 : Submodule.IsPrincipal.generator v.asIdeal ≠ 0 := by
          intro h0
          apply v.ne_bot
          rw [← span_generator_four F v.asIdeal, h0, Ideal.span_singleton_eq_bot]
        exact absurd hv (angularGenVal_ne_zero F k hgen0) }

private theorem angularIdealWeight_span_singleton (k : ℤ) (α : 𝓞 F) :
    angularIdealWeight F k (Ideal.span {α}) = angularGenVal F k α := by
  have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  change angularGenVal F k (Submodule.IsPrincipal.generator (Ideal.span {α})) =
    angularGenVal F k α
  exact angularGenVal_eq_of_associated F k
    (Ideal.span_singleton_eq_span_singleton.mp (span_generator_four F (Ideal.span {α})))

private theorem angularIdealWeight_ne_zero (k : ℤ) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    angularIdealWeight F k I ≠ 0 := by
  have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  rw [← span_generator_four F I, angularIdealWeight_span_singleton]
  refine angularGenVal_ne_zero F k fun h0 ↦ hI ?_
  rw [← span_generator_four F I, h0, Ideal.span_singleton_eq_bot]

/-- The bundled `UnitaryIdealWeight F` of Hecke's `k`-th angular character. -/
private def angularUnitaryWeight (k : ℤ) : UnitaryIdealWeight F :=
  ⟨angularIdealWeight F k, fun 𝔭 _ ↦ by
    have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
    rw [← span_generator_four F 𝔭.asIdeal, angularIdealWeight_span_singleton]
    refine norm_angularGenVal_of_ne_zero F k fun h0 ↦ 𝔭.ne_bot ?_
    rw [← span_generator_four F 𝔭.asIdeal, h0, Ideal.span_singleton_eq_bot]⟩

end IdealWeight

/-! ### The angular Hecke character and its archimedean and local components -/

section HeckeConstruction

variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F]

open Classical in
/-- The algebraic infinity type of Hecke's `k`-th angular character: `-2 * k` at the chosen
embedding of the unique complex place and `2 * k` at its complex conjugate. -/
private def angularAlgebraicInfinityType (k : ℤ) : AlgebraicInfinityType F :=
  fun σ ↦ if σ = (angularPlace F).1.embedding then -(2 * k) else 2 * k

private theorem angularAlgebraicInfinityType_embedding (k : ℤ) :
    angularAlgebraicInfinityType F k (angularPlace F).1.embedding = -(2 * k) := by
  simp [angularAlgebraicInfinityType]

private theorem angularAlgebraicInfinityType_conjugate (k : ℤ) :
    angularAlgebraicInfinityType F k (ComplexEmbedding.conjugate (angularPlace F).1.embedding) =
      2 * k := by
  have hne : ComplexEmbedding.conjugate (angularPlace F).1.embedding ≠
      (angularPlace F).1.embedding := by
    intro h
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (angularPlace F).2
      (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
  simp [angularAlgebraicInfinityType, hne]

/-- Every embedding `σ : F →+* ℂ` is either `(angularPlace F).1.embedding` or its conjugate. -/
private theorem embedding_eq_or_eq_conjugate_four (σ : F →+* ℂ) :
    σ = (angularPlace F).1.embedding ∨
      σ = ComplexEmbedding.conjugate (angularPlace F).1.embedding := by
  have hmk : InfinitePlace.mk σ = (angularPlace F).1 :=
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

omit [IsCyclotomicExtension {4} ℚ F] in
/-- The coordinate map `ideleInfiniteCoord` at an infinite place is continuous on the idele
group. -/
private theorem continuous_ideleInfiniteCoord_four (w : InfinitePlace F) :
    Continuous (w.ideleInfiniteCoord : IdeleGroup (𝓞 F) F → w.Completionˣ) := by
  have h : (w.ideleInfiniteCoord : IdeleGroup (𝓞 F) F → w.Completionˣ) =
      fun x ↦ (IdeleGroup.localUnitsEquiv (𝓞 F) F x).1 w :=
    funext fun x ↦ (IdeleGroup.localUnitsEquiv_apply_fst x w).symm
  rw [h]
  exact ((continuous_apply w).comp continuous_fst).comp
    (IdeleGroup.localUnitsEquiv (𝓞 F) F).continuous

/-- The continuous character on `IdeleGroup (𝓞 F) F` reading the angular character of frequency
`-4 * k` at the unique complex place `angularPlace F`. Its restriction to
`ideleCongruenceSubgroup (Modulus.one F)` kills `U ∩ F^× = (𝓞 F)ˣ`. -/
private def angularIdeleArchChar (k : ℤ) : IdeleGroup (𝓞 F) F →ₜ* ℂˣ :=
  ((complexAngularCharacter ^ (-(4 * k))).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex (angularPlace F).2)))).comp
    ⟨(angularPlace F).1.ideleInfiniteCoord, continuous_ideleInfiniteCoord_four F (angularPlace F).1⟩

private theorem coe_angularIdeleArchChar_apply (k : ℤ) (y : IdeleGroup (𝓞 F) F) :
    (angularIdeleArchChar F k y : ℂ) =
      (continuousMulEquivComplexOfIsComplex (angularPlace F).2
          ((angularPlace F).1.ideleInfiniteCoord y : (angularPlace F).1.Completion) /
        (‖continuousMulEquivComplexOfIsComplex (angularPlace F).2
          ((angularPlace F).1.ideleInfiniteCoord y : (angularPlace F).1.Completion)‖ : ℂ)) ^
        (-(4 * k)) := by
  change (((complexAngularCharacter ^ (-(4 * k)))
    ((Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex (angularPlace F).2))
      ((angularPlace F).1.ideleInfiniteCoord y))) : ℂ) = _
  rw [ContinuousMonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val, coe_complexAngularCharacter_apply]
  rfl

/-- The surjection from the everywhere-unramified ideles `ideleCongruenceSubgroup (Modulus.one F)`
onto `IdeleClassGroup (𝓞 F) F`. -/
private def congruenceOneToClassHom :
    ideleCongruenceSubgroup (Modulus.one F) →* IdeleClassGroup (𝓞 F) F :=
  (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp
    (ideleCongruenceSubgroup (Modulus.one F)).subtype

private theorem congruenceOneToClassHom_surjective :
    Function.Surjective (congruenceOneToClassHom F) := by
  intro c
  have hc : c ∈ raySubgroup (Modulus.one F) := by
    rw [raySubgroup_one_eq_top_four]
    trivial
  obtain ⟨y, hy, rfl⟩ := mem_raySubgroup_iff.mp hc
  exact ⟨⟨y, hy⟩, rfl⟩

private theorem isQuotientMap_congruenceOneToClassHom :
    Topology.IsQuotientMap (congruenceOneToClassHom F) := by
  have hcont : Continuous (congruenceOneToClassHom F) :=
    continuous_quot_mk.comp continuous_subtype_val
  have hopen : IsOpenMap (congruenceOneToClassHom F) :=
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap.comp
      (isOpen_ideleCongruenceSubgroup (Modulus.one F)).isOpenEmbedding_subtypeVal.isOpenMap
  exact hopen.isQuotientMap hcont (congruenceOneToClassHom_surjective F)

/-- Principal ideles in `ideleCongruenceSubgroup (Modulus.one F)` come from `(𝓞 F)ˣ`, which are
fourth roots of unity and therefore lie in the kernel of `angularIdeleArchChar F k`. -/
private theorem congruenceOneToClassHom_ker_le (k : ℤ) :
    (congruenceOneToClassHom F).ker ≤
      ((angularIdeleArchChar F k).toMonoidHom.comp
        (ideleCongruenceSubgroup (Modulus.one F)).subtype).ker := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy ⊢
  have hmk : QuotientGroup.mk (y : IdeleGroup (𝓞 F) F) = (1 : IdeleClassGroup (𝓞 F) F) := hy
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff (y : IdeleGroup (𝓞 F) F)).mp hmk
  have hxmem : IdeleGroup.unitEmbedding (𝓞 F) F x ∈ ideleCongruenceSubgroup (Modulus.one F) :=
    hx.symm ▸ y.2
  obtain ⟨u, -, rfl⟩ :=
    Subgroup.mem_map.mp (unitEmbedding_mem_ideleCongruenceSubgroup_iff.mp hxmem)
  apply Units.ext
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← hx]
  change (angularIdeleArchChar F k
    (IdeleGroup.unitEmbedding (𝓞 F) F (Units.map (algebraMap (𝓞 F) F).toMonoidHom u)) : ℂ) = 1
  rw [coe_angularIdeleArchChar_apply, InfinitePlace.ideleInfiniteCoord_unitEmbedding]
  have hval : continuousMulEquivComplexOfIsComplex (angularPlace F).2
      ((Units.map (algebraMap F (angularPlace F).1.Completion).toMonoidHom
        (Units.map (algebraMap (𝓞 F) F).toMonoidHom u) : (angularPlace F).1.Completionˣ) :
          (angularPlace F).1.Completion) =
      (angularPlace F).1.embedding ((u : 𝓞 F) : F) := by
    simp [NumberField.InfinitePlace.Completion.algebraMap_apply_eq_coe,
      continuousMulEquivComplexOfIsComplex_apply]
  rw [hval]
  have hz4 : ((angularPlace F).1.embedding ((u : 𝓞 F) : F)) ^ 4 = 1 :=
    embedding_unit_pow_four_eq_one F u (angularPlace F).1.embedding
  rw [Complex.norm_eq_one_of_pow_eq_one hz4 (by decide), Complex.ofReal_one, div_one,
    show -(4 * k) = (4 : ℕ) * (-k) by ring, zpow_mul, zpow_natCast, hz4, one_zpow]

/-- Underlying group homomorphism of Hecke's `k`-th angular idele class character on `F`. -/
private def angularHeckeCharacterAux (k : ℤ) : IdeleClassGroup (𝓞 F) F →* ℂˣ :=
  (congruenceOneToClassHom F).liftOfSurjective (congruenceOneToClassHom_surjective F)
    ⟨(angularIdeleArchChar F k).toMonoidHom.comp
        (ideleCongruenceSubgroup (Modulus.one F)).subtype,
      congruenceOneToClassHom_ker_le F k⟩

/-- Hecke's `k`-th angular idele class character on `F`. -/
private def angularHeckeCharacter (k : ℤ) : HeckeCharacter F where
  toMonoidHom := angularHeckeCharacterAux F k
  continuous_toFun := by
    change Continuous ⇑(angularHeckeCharacterAux F k)
    rw [(isQuotientMap_congruenceOneToClassHom F).continuous_iff]
    have hcomp :
        ⇑(angularHeckeCharacterAux F k) ∘ ⇑(congruenceOneToClassHom F) =
        fun y : ideleCongruenceSubgroup (Modulus.one F) ↦
          angularIdeleArchChar F k (y : IdeleGroup (𝓞 F) F) :=
      funext fun y ↦ MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ y
    rw [hcomp]
    exact (angularIdeleArchChar F k).continuous.comp continuous_subtype_val

/-- On an idele `y ∈ ideleCongruenceSubgroup (Modulus.one F)`, `angularHeckeCharacter F k`
evaluates `angularIdeleArchChar F k` directly. -/
private theorem angularHeckeCharacter_mk_of_mem (k : ℤ) {y : IdeleGroup (𝓞 F) F}
    (hy : y ∈ ideleCongruenceSubgroup (Modulus.one F)) :
    angularHeckeCharacter F k (y : IdeleClassGroup (𝓞 F) F) = angularIdeleArchChar F k y :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _
    (⟨y, hy⟩ : ideleCongruenceSubgroup (Modulus.one F))

/-- Every value of `angularHeckeCharacter F k` has norm `1`, so its idelic shift vanishes. -/
private theorem shift_angularHeckeCharacter (k : ℤ) :
    (angularHeckeCharacter F k).shift = 0 := by
  refine (HeckeCharacter.shift_eq_zero_iff _).mpr fun c ↦ ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := congruenceOneToClassHom_surjective F c
  change ‖(angularHeckeCharacter F k (y : IdeleClassGroup (𝓞 F) F) : ℂ)‖ = 1
  rw [angularHeckeCharacter_mk_of_mem F k hy, coe_angularIdeleArchChar_apply]
  set z : ℂ := continuousMulEquivComplexOfIsComplex (angularPlace F).2
    ((angularPlace F).1.ideleInfiniteCoord y : (angularPlace F).1.Completion)
  have hz : z ≠ 0 :=
    (map_ne_zero _).mpr ((angularPlace F).1.ideleInfiniteCoord y).ne_zero
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
  ext z
  let e := Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex (angularPlace F).2)
  have hmem : IdeleGroup.ofCompletion (𝓞 F) F (angularPlace F).1 (e.symm z) ∈
      ideleCongruenceSubgroup (Modulus.one F) :=
    mem_ideleCongruenceSubgroup_one_iff.mpr fun v ↦ by simp
  rw [HeckeCharacter.complexComponent_apply, HeckeCharacter.infiniteComponent_apply,
    IdeleClassGroup.ofCompletion_apply]
  change (angularHeckeCharacter F k
    ((IdeleGroup.ofCompletion (𝓞 F) F (angularPlace F).1 (e.symm z) : IdeleGroup (𝓞 F) F) :
      IdeleClassGroup (𝓞 F) F) : ℂ) =
    (complexUnitsCharacter 0 (-(4 * k)) z : ℂ)
  rw [angularHeckeCharacter_mk_of_mem F k hmem, complexUnitsCharacter_zero_left]
  simp [angularIdeleArchChar, e, InfinitePlace.ideleInfiniteCoord_ofCompletion_self]

/-- The continuous infinity type of `angularHeckeCharacter F k` equals the continuous image of
`angularAlgebraicInfinityType F k`. -/
private theorem infinityType_angularHeckeCharacter (k : ℤ) :
    (angularHeckeCharacter F k).infinityType =
      AlgebraicInfinityType.toContinuous (angularAlgebraicInfinityType F k) := by
  refine HeckeCharacter.infinityType_eq_iff.mpr ⟨fun w ↦ ?_, fun w ↦ ?_⟩
  · exact (isEmpty_realInfinitePlace_four F).elim w
  · obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
    rw [complexComponent_angularHeckeCharacter,
      AlgebraicInfinityType.toContinuous_complexExponent,
      AlgebraicInfinityType.toContinuous_complexAngularFrequency,
      angularAlgebraicInfinityType_embedding, angularAlgebraicInfinityType_conjugate]
    have hsum : ((-(2 * k) : ℤ) : ℂ) + ((2 * k : ℤ) : ℂ) = 0 := by push_cast; ring
    have hdiff : -(2 * k) - 2 * k = -(4 * k) := by ring
    rw [hsum, hdiff]

/-- For any nonzero `z : ℂ`, `(z⁻¹ / ‖z⁻¹‖) ^ (-(4 * k)) = (z / conj z) ^ (2 * k)`, since
`z * conj z = ‖z‖ ^ 2`. -/
private theorem inv_div_norm_inv_zpow_neg_four_mul (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    (z⁻¹ / (‖z⁻¹‖ : ℂ)) ^ (-(4 * k)) = (z / starRingEnd ℂ z) ^ (2 * k) := by
  have hinv_ang : z⁻¹ / (‖z⁻¹‖ : ℂ) = (z / (‖z‖ : ℂ))⁻¹ := by
    rw [norm_inv, Complex.ofReal_inv, inv_div_inv, inv_div]
  have hmul : z * starRingEnd ℂ z = (‖z‖ : ℂ) ^ (2 : ℕ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hsq_ang : (z / (‖z‖ : ℂ)) ^ (2 : ℕ) = z / starRingEnd ℂ z := by
    rw [div_pow, ← hmul, sq, mul_div_mul_left z (starRingEnd ℂ z) hz]
  rw [hinv_ang, inv_zpow, ← zpow_neg, neg_neg, show (4 * k : ℤ) = (2 : ℕ) * (2 * k) by ring,
    zpow_mul, zpow_natCast, hsq_ang]

private theorem exists_span_singleton_eq_asIdeal_four (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : 𝓞 F, π ≠ 0 ∧ Ideal.span {π} = v.asIdeal := by
  have : IsPrincipalIdealRing (𝓞 F) := isPrincipalIdealRing_ringOfIntegers_four F
  refine ⟨Submodule.IsPrincipal.generator v.asIdeal, ?_, span_generator_four F v.asIdeal⟩
  exact v.ne_zero_of_span_singleton_eq_pow (by rw [pow_one, span_generator_four F v.asIdeal])

/-- Evaluating `angularHeckeCharacter F k` at a uniformizer `u` of `v` gives the principal-ideal
weight at `v.asIdeal`: multiplying `ofAdicCompletion v u` by `(unitEmbedding π)⁻¹` for a generator
`π` of `v.asIdeal` produces an everywhere-integral unit idele with infinite coordinate `(τ π)⁻¹`,
on which `z ↦ (z / ‖z‖) ^ (-4 * k)` evaluates to `(τ π / conj (τ π)) ^ (2 * k)`. -/
private theorem finiteComponent_angularHeckeCharacter_of_valued_eq_exp_neg_one (k : ℤ)
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = WithZero.exp (-1)) :
    ((angularHeckeCharacter F k).finiteComponent v u : ℂ) =
      angularIdealWeight F k v.asIdeal := by
  obtain ⟨π, hπ0, hspan⟩ := exists_span_singleton_eq_asIdeal_four F v
  have hspan1 : Ideal.span {π} = v.asIdeal ^ 1 := by rw [pow_one, hspan]
  have hπF : (algebraMap (𝓞 F) F π) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective (𝓞 F) F)).mpr hπ0
  set x : Fˣ := Units.mk0 (algebraMap (𝓞 F) F π) hπF
  set y : IdeleGroup (𝓞 F) F :=
    IdeleGroup.ofAdicCompletion (𝓞 F) F v u * (IdeleGroup.unitEmbedding (𝓞 F) F x)⁻¹
  have hy_mem : y ∈ ideleCongruenceSubgroup (Modulus.one F) := by
    refine mem_ideleCongruenceSubgroup_one_iff.mpr fun v' ↦ ?_
    have hval_x : Valued.v ((v'.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 F) F x) :
        (v'.adicCompletion F)ˣ) : v'.adicCompletion F) = v'.intValuation π := by
      rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Units.val_mk0,
        HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self_apply, v'.valuedAdicCompletion_eq_valuation',
        v'.valuation_of_algebraMap]
    simp only [y, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, map_inv₀, hval_x]
    rcases eq_or_ne v' v with rfl | hne
    · rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self, hu,
        v'.intValuation_eq_exp_neg_of_span_singleton_eq_pow hspan1, Nat.cast_one,
        mul_inv_cancel₀ WithZero.exp_ne_zero]
    · rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ hne, Units.val_one,
        map_one, v'.intValuation_eq_one_of_span_singleton_eq_pow hne hspan1, inv_one, mul_one]
  have hy_class : (y : IdeleClassGroup (𝓞 F) F) = IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u := by
    rw [IdeleClassGroup.ofAdicCompletion_apply]
    change QuotientGroup.mk y = QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 F) F v u)
    rw [QuotientGroup.eq]
    exact ⟨x, by simp [y, mul_assoc]⟩
  rw [HeckeCharacter.finiteComponent_apply, ← hy_class, angularHeckeCharacter_mk_of_mem F k hy_mem,
    coe_angularIdeleArchChar_apply, ← hspan, angularIdealWeight_span_singleton,
    angularGenVal_of_ne_zero F k hπ0]
  have hinf : continuousMulEquivComplexOfIsComplex (angularPlace F).2
      ((angularPlace F).1.ideleInfiniteCoord y : (angularPlace F).1.Completion) =
      ((angularPlace F).1.embedding (π : F))⁻¹ := by
    simp [y, x, InfinitePlace.ideleInfiniteCoord_ofAdicCompletion,
      InfinitePlace.ideleInfiniteCoord_unitEmbedding,
      NumberField.InfinitePlace.Completion.algebraMap_apply_eq_coe,
      continuousMulEquivComplexOfIsComplex_apply]
  rw [hinf]
  exact inv_div_norm_inv_zpow_neg_four_mul k ((map_ne_zero _).mpr hπF)

end HeckeConstruction

/-! ### Construction of `angularGrossencharacter` -/

section AngularGrossencharacter

private theorem infiniteComponent_eq_of_infinityType_eq_four {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] {𝔪 : Modulus F} {χ ψ : Grossencharacter F 𝔪}
    (h : χ.infinityType = ψ.infinityType) (w : InfinitePlace F) :
    χ.toHeckeCharacter.infiniteComponent w = ψ.toHeckeCharacter.infiniteComponent w := by
  have hcont : χ.toHeckeCharacter.infinityType = ψ.toHeckeCharacter.infinityType := by
    have hagree := χ.agreesOnIdentityComponent.trans
      (h ▸ ψ.agreesOnIdentityComponent.symm)
    obtain ⟨_, hc, hk⟩ := (ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mp hagree
    ext w'
    · exact (isEmpty_realInfinitePlace_four F).elim w'
    · exact (isEmpty_realInfinitePlace_four F).elim w'
    · exact congrFun hc w'
    · exact congrFun hk w'
  have hw : w.IsComplex := (isTotallyComplex_four F).isComplex w
  have hc : χ.toHeckeCharacter.complexComponent ⟨w, hw⟩ =
      ψ.toHeckeCharacter.complexComponent ⟨w, hw⟩ := by
    rw [HeckeCharacter.complexComponent_eq, HeckeCharacter.complexComponent_eq, hcont]
  let e := Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex hw)
  ext u
  have hu := DFunLike.congr_fun hc (e u)
  rw [HeckeCharacter.complexComponent_apply, HeckeCharacter.complexComponent_apply,
    e.symm_apply_apply] at hu
  exact congrArg Units.val hu

/-- Over a fourth cyclotomic field, unramified presentations at `Modulus.one F` are determined by
their algebraic infinity type: every idele class has a representative in
`ideleCongruenceSubgroup (Modulus.one F)` whose finite part is killed by `eq_one_of_mem`. -/
private theorem ext_of_infinityType_one_four {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] {χ ψ : Grossencharacter F (Modulus.one F)}
    (h : χ.infinityType = ψ.infinityType) : χ = ψ := by
  apply Grossencharacter.ext
  ext c
  obtain ⟨⟨y, hy⟩, rfl⟩ := congruenceOneToClassHom_surjective F c
  change (χ.toHeckeCharacter (y : IdeleClassGroup (𝓞 F) F) : ℂ) =
    (ψ.toHeckeCharacter (y : IdeleClassGroup (𝓞 F) F) : ℂ)
  have hfin_mem : IdeleGroup.ofFiniteIdele (𝓞 F) F (IdeleGroup.toFiniteIdele (𝓞 F) F y) ∈
      ideleCongruenceSubgroup (Modulus.one F) := by
    refine mem_ideleCongruenceSubgroup_one_iff.mpr fun v ↦ ?_
    have hv : (v.ideleFiniteCoord (IdeleGroup.ofFiniteIdele (𝓞 F) F
        (IdeleGroup.toFiniteIdele (𝓞 F) F y)) : v.adicCompletion F) =
        (v.ideleFiniteCoord y : v.adicCompletion F) := by
      simp only [HeightOneSpectrum.coe_ideleFiniteCoord, IdeleGroup.coe_ofFiniteIdele,
        IdeleGroup.coe_toFiniteIdele]
    rw [hv]
    exact (mem_ideleCongruenceSubgroup_one_iff.mp hy) v
  have hfin_inf (w : InfinitePlace F) :
      w.ideleInfiniteCoord
        (IdeleGroup.ofFiniteIdele (𝓞 F) F (IdeleGroup.toFiniteIdele (𝓞 F) F y)) = 1 :=
    InfinitePlace.ideleInfiniteCoord_ofFiniteIdele w _
  rw [← IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele y, QuotientGroup.mk_mul, map_mul, map_mul,
    χ.eq_one_of_mem _ hfin_mem hfin_inf, ψ.eq_one_of_mem _ hfin_mem hfin_inf,
    mul_one, mul_one, QuotientGroup.mk_prod, map_prod, map_prod]
  simp only [Units.coe_prod]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  have hw := DFunLike.congr_fun (infiniteComponent_eq_of_infinityType_eq_four h w)
    (w.ideleInfiniteCoord y)
  simpa only [HeckeCharacter.infiniteComponent_apply, IdeleClassGroup.ofCompletion_apply] using
    congrArg Units.val hw

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
    rw [angularHeckeCharacter_mk_of_mem F k hy, Units.ext_iff, coe_angularIdeleArchChar_apply,
      hw (angularPlace F).1, Units.val_one, map_one]
    simp
  agreesOnIdentityComponent := by
    rw [infinityType_angularHeckeCharacter]
    exact (ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mpr ⟨rfl, rfl, rfl⟩
  realParity_eq w _ := (isEmpty_realInfinitePlace_four F).elim w
  unitaryWeight_eq_zero I hI := by
    by_cases hbot : I = ⊥
    · simp [hbot]
    · exact absurd (Modulus.isCoprimeTo_iff.mpr ⟨hbot, fun v hv ↦ by simp at hv⟩) hI
  unitaryWeight_apply v _ u hu := by
    rw [unitaryPart_angularHeckeCharacter,
      finiteComponent_angularHeckeCharacter_of_valued_eq_exp_neg_one F k v u hu]
    rfl

end AngularGrossencharacter

/-! ### Specification, projections, and group laws in `k` -/

section SpecificationAndGroupLaws

/-- At the chosen embedding `w.1.embedding` of the complex place `w` of `F`, the algebraic infinity
type of `angularGrossencharacter F k` has exponent `-(2 * k)`. -/
@[simp]
theorem infinityType_angularGrossencharacter_embedding {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (angularGrossencharacter F k).infinityType w.1.embedding = -(2 * k) := by
  obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
  exact angularAlgebraicInfinityType_embedding F k

/-- At the conjugate embedding `conj w.1.embedding` of the complex place `w` of `F`, the algebraic
infinity type of `angularGrossencharacter F k` has exponent `2 * k`. -/
@[simp]
theorem infinityType_angularGrossencharacter_conjugate {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (angularGrossencharacter F k).infinityType (ComplexEmbedding.conjugate w.1.embedding) =
      2 * k := by
  obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
  exact angularAlgebraicInfinityType_conjugate F k

/-- **Ideal-side value on principal ideals**: for any nonzero `α ∈ 𝓞 F` and the complex place `w`
of `F` with chosen embedding `τ = w.1.embedding`, `angularGrossencharacter F k` sends `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)`. -/
theorem unitaryWeight_angularGrossencharacter_span_singleton {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex})
    {α : 𝓞 F} (hα : α ≠ 0) :
    (angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {α}) =
      (w.1.embedding (α : F) / starRingEnd ℂ (w.1.embedding (α : F))) ^ (2 * k) := by
  obtain rfl : w = angularPlace F := complexPlace_eq_angularPlace F w
  change angularIdealWeight F k (Ideal.span {α}) = _
  rw [angularIdealWeight_span_singleton, angularGenVal_of_ne_zero F k hα]

/-- **Hecke's angular characters of `ℚ(i)` exist**: for each `k : ℤ` there is an unramified
presentation whose algebraic infinity type has exponent `-(2 * k)` at an embedding `τ : F →+* ℂ`
and whose unitary ideal weight sends every nonzero principal ideal `(α)` to
`(τ α / conj (τ α)) ^ (2 * k)`. -/
theorem exists_angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    ∃ χ : Grossencharacter F (Modulus.one F), ∃ τ : F →+* ℂ, χ.infinityType τ = -(2 * k) ∧
      ∀ α : 𝓞 F, α ≠ 0 →
        χ.unitaryWeight.1 (Ideal.span {α}) = (τ (α : F) / starRingEnd ℂ (τ (α : F))) ^ (2 * k) :=
  ⟨angularGrossencharacter F k, (angularPlace F).1.embedding,
    infinityType_angularGrossencharacter_embedding k (angularPlace F),
    fun _ hα ↦ unitaryWeight_angularGrossencharacter_span_singleton k (angularPlace F) hα⟩

/-- Because `angularGrossencharacter F k` is unramified everywhere, its unitary ideal weight has no
bad primes. -/
@[simp]
theorem badPrimes_unitaryWeight_angularGrossencharacter (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    (angularGrossencharacter F k).unitaryWeight.1.badPrimes = ∅ := by
  ext v
  simp only [MultiplicativeIdealWeight.mem_badPrimes, Set.mem_empty_iff_false, iff_false]
  exact angularIdealWeight_ne_zero F k v.ne_bot

/-- An integral ideal `I` of `𝓞 F` is good for `angularGrossencharacter F k` if and only if `I` is
nonzero. -/
@[simp]
theorem isGood_unitaryWeight_angularGrossencharacter_iff {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) {I : Ideal (𝓞 F)} :
    (angularGrossencharacter F k).unitaryWeight.1.IsGood I ↔ I ≠ ⊥ := by
  rw [MultiplicativeIdealWeight.IsGood, badPrimes_unitaryWeight_angularGrossencharacter,
    Ideal.isPrimeTo_iff]
  simp

/-- The unitary ideal weight of `angularGrossencharacter F k` is nonzero on every nonzero ideal. -/
theorem unitaryWeight_angularGrossencharacter_ne_zero {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    (angularGrossencharacter F k).unitaryWeight.1 I ≠ 0 :=
  ((angularGrossencharacter F k).unitaryWeight.1.apply_ne_zero_iff_isGood I).mpr
    ((isGood_unitaryWeight_angularGrossencharacter_iff k).mpr hI)

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
    (angularGrossencharacter F k).toHeckeCharacter.finiteConductor = ⊤ := by
  have hdvd := (angularGrossencharacter F k).finiteConductor_dvd_finitePart
  rwa [Modulus.one_finitePart, Ideal.dvd_iff_le, top_le_iff] at hdvd

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
theorem complexExponent_angularGrossencharacter {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (AlgebraicInfinityType.toContinuous
      (angularGrossencharacter F k).infinityType).complexExponent w = 0 := by
  simp

/-- At the complex place `w` of `F`, the continuous infinity type of `angularGrossencharacter F k`
has angular frequency `-(4 * k)` (with respect to `w.1.embedding`). -/
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
  apply ext_of_infinityType_one_four
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
  apply Subtype.ext
  refine MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_
  obtain ⟨π, hπ0, hspan⟩ := exists_span_singleton_eq_asIdeal_four F v
  rw [← hspan, unitaryWeight_angularGrossencharacter_span_singleton 0 (angularPlace F) hπ0,
    hspan, UnitaryIdealWeight.val_one, MultiplicativeIdealWeight.one_apply]
  simp [v.ne_bot]

/-- Negating the angular index `k` inverts the presentation (`Grossencharacter.inverse`). -/
theorem angularGrossencharacter_neg (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (k : ℤ) :
    angularGrossencharacter F (-k) = (angularGrossencharacter F k).inverse := by
  apply ext_of_infinityType_one_four
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
  ext c
  obtain ⟨⟨y, hy⟩, rfl⟩ := congruenceOneToClassHom_surjective F c
  change (angularHeckeCharacter F (j + k) (y : IdeleClassGroup (𝓞 F) F) : ℂ) =
    (angularHeckeCharacter F j (y : IdeleClassGroup (𝓞 F) F) : ℂ) *
      (angularHeckeCharacter F k (y : IdeleClassGroup (𝓞 F) F) : ℂ)
  rw [angularHeckeCharacter_mk_of_mem F (j + k) hy, angularHeckeCharacter_mk_of_mem F j hy,
    angularHeckeCharacter_mk_of_mem F k hy, coe_angularIdeleArchChar_apply,
    coe_angularIdeleArchChar_apply, coe_angularIdeleArchChar_apply]
  set z : ℂ := continuousMulEquivComplexOfIsComplex (angularPlace F).2
    ((angularPlace F).1.ideleInfiniteCoord y : (angularPlace F).1.Completion)
  have hz : z / (‖z‖ : ℂ) ≠ 0 := by
    have hz0 : z ≠ 0 := (map_ne_zero _).mpr ((angularPlace F).1.ideleInfiniteCoord y).ne_zero
    exact div_ne_zero hz0 (by simp [hz0])
  rw [show -(4 * (j + k)) = -(4 * j) + -(4 * k) by ring, zpow_add₀ hz]

/-- Adding angular indices multiplies the unitary ideal weights. -/
theorem unitaryWeight_angularGrossencharacter_add (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] (j k : ℤ) :
    (angularGrossencharacter F (j + k)).unitaryWeight =
      (angularGrossencharacter F j).unitaryWeight *
        (angularGrossencharacter F k).unitaryWeight := by
  apply Subtype.ext
  refine MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_
  obtain ⟨π, hπ0, hspan⟩ := exists_span_singleton_eq_asIdeal_four F v
  rw [UnitaryIdealWeight.val_mul, MultiplicativeIdealWeight.mul_apply, ← hspan,
    unitaryWeight_angularGrossencharacter_span_singleton (j + k) (angularPlace F) hπ0,
    unitaryWeight_angularGrossencharacter_span_singleton j (angularPlace F) hπ0,
    unitaryWeight_angularGrossencharacter_span_singleton k (angularPlace F) hπ0]
  have hπF : (π : F) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective (𝓞 F) F)).mpr hπ0
  have hz : (angularPlace F).1.embedding (π : F) ≠ 0 := (map_ne_zero _).mpr hπF
  rw [show 2 * (j + k) = 2 * j + 2 * k by ring,
    zpow_add₀ (div_ne_zero hz ((map_ne_zero _).mpr hz))]

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
  have hinj := congrFun (congrArg Grossencharacter.infinityType h) (angularPlace F).1.embedding
  rw [infinityType_angularGrossencharacter_embedding j (angularPlace F),
    infinityType_angularGrossencharacter_embedding k (angularPlace F)] at hinj
  omega

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
  · obtain ⟨ε, hε⟩ := HeckeCharacter.exists_finiteOrderInfinityType hfin
    have h0 : ContinuousInfinityType.AgreesOnIdentityComponent
        (angularGrossencharacter F k).toHeckeCharacter.infinityType
        (AlgebraicInfinityType.toContinuous 0) := by
      rw [hε, map_zero,
        ContinuousInfinityType.agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType]
      exact ⟨ε, (zero_add _).symm⟩
    have hn : (angularGrossencharacter F k).infinityType = 0 :=
      AlgebraicInfinityType.agreesOnIdentityComponent_toContinuous_iff.mp
        ((angularGrossencharacter F k).agreesOnIdentityComponent.symm.trans h0)
    have hk0 := congrFun hn (angularPlace F).1.embedding
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

/-! ### The `2 + i` nonreal sign check and absence of pure norm twists -/

section TwoAddZetaAndNormTwist

/-- Every positive integer power of `3 + 4i` has Gaussian integer coordinates congruent to `(3, 4)`
modulo `5`, because `(3 + 4i) ^ 2 = -7 + 24i ≡ 3 + 4i (mod 5)`. -/
private theorem exists_int_pow_three_add_four_I {n : ℕ} (hn : n ≠ 0) :
    ∃ a b : ℤ, ((3 : ℂ) + 4 * Complex.I) ^ n = (a : ℂ) + (b : ℂ) * Complex.I ∧
      a % 5 = 3 ∧ b % 5 = 4 := by
  induction n with
  | zero => exact absurd rfl hn
  | succ m ih =>
    rcases eq_or_ne m 0 with rfl | hm
    · exact ⟨3, 4, by simp, by decide, by decide⟩
    · obtain ⟨a, b, hpow, ha, hb⟩ := ih hm
      refine ⟨3 * a - 4 * b, 4 * a + 3 * b, ?_, by omega, by omega⟩
      rw [pow_succ, hpow]
      push_cast
      linear_combination (4 * (b : ℂ)) * Complex.I_sq

/-- No nonzero integer power of `(3 + 4i) / 5` is real: its imaginary part is nonzero. -/
private theorem im_three_add_four_I_div_five_zpow_ne_zero {m : ℤ} (hm : m ≠ 0) :
    ((((3 : ℂ) + 4 * Complex.I) / 5) ^ m).im ≠ 0 := by
  have hnat {n : ℕ} (hn : n ≠ 0) : ((((3 : ℂ) + 4 * Complex.I) / 5) ^ n).im ≠ 0 := by
    obtain ⟨a, b, hpow, -, hb⟩ := exists_int_pow_three_add_four_I hn
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have h5 : (5 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hrew : (((3 : ℂ) + 4 * Complex.I) / 5) ^ n =
        ((a : ℝ) / (5 : ℝ) ^ n : ℝ) + (((b : ℝ) / (5 : ℝ) ^ n : ℝ) : ℂ) * Complex.I := by
      rw [div_pow, hpow]
      push_cast
      ring
    have him : ((((3 : ℂ) + 4 * Complex.I) / 5) ^ n).im = (b : ℝ) / (5 : ℝ) ^ n := by
      rw [hrew, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
    rw [him]
    exact div_ne_zero hb0 h5
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · have hn : n ≠ 0 := by omega
    simpa only [zpow_natCast] using hnat hn
  · have hn : n ≠ 0 := by omega
    rw [zpow_neg, zpow_natCast, Complex.inv_im]
    intro him
    rcases div_eq_zero_iff.mp him with hneg | hnsq
    · exact hnat hn (neg_eq_zero.mp hneg)
    · have hz0 : (((3 : ℂ) + 4 * Complex.I) / 5) ^ n = 0 := Complex.normSq_eq_zero.mp hnsq
      exact hnat hn (by simp [hz0])

/-- Under any embedding `τ : F →+* ℂ`, a primitive fourth root of unity `ζ ∈ F` maps to `i` or
`-i`. -/
private theorem embedding_toInteger_eq_I_or_neg_I {F : Type*} [Field F] [NumberField F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ 4) (τ : F →+* ℂ) :
    τ (hζ.toInteger : F) = Complex.I ∨ τ (hζ.toInteger : F) = -Complex.I := by
  have hz : algebraMap (𝓞 F) F hζ.toInteger = ζ := hζ.coe_toInteger
  have hsq : (τ (hζ.toInteger : F)) ^ 2 = Complex.I ^ 2 := by
    rw [Complex.I_sq, RingOfIntegers.coe_eq_algebraMap, hz, ← map_pow,
      hζ.sq_eq_neg_one, map_neg, map_one]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

private theorem norm_two_add_toInteger_of_four {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4) :
    Algebra.norm ℤ ((2 : 𝓞 F) + hζ.toInteger) = 5 := by
  simpa using hζ.norm_intCast_add_intCast_mul_toInteger_of_four 2 1

private theorem two_add_toInteger_ne_zero_of_four {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4) :
    (2 : 𝓞 F) + hζ.toInteger ≠ 0 := by
  intro h0
  have hnorm := norm_two_add_toInteger_of_four hζ
  rw [h0, Algebra.norm_zero] at hnorm
  omega

private theorem unitaryWeight_angularGrossencharacter_apply_sq {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] (k : ℤ) (I : Ideal (𝓞 F)) :
    ((angularGrossencharacter F k).unitaryWeight.1 I) ^ 2 =
      (angularGrossencharacter F (2 * k)).unitaryWeight.1 I := by
  have hp := congrArg Subtype.val (unitaryWeight_angularGrossencharacter_add F k k)
  rw [UnitaryIdealWeight.val_mul, ← two_mul] at hp
  simpa only [MultiplicativeIdealWeight.mul_apply, sq] using (DFunLike.congr_fun hp I).symm

/-- **Value of `angularGrossencharacter F k` at `(2 + i)`**: for a primitive fourth root of unity
`ζ ∈ F`, the unitary weight at `Ideal.span {2 + hζ.toInteger}` is `((3 + 4i) / 5) ^ (2 * k)` or
`((3 + 4i) / 5) ^ (-(2 * k))` according to which square root of `-1` the chosen embedding
selects. -/
theorem unitaryWeight_angularGrossencharacter_two_add_toInteger {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4) (k : ℤ) :
    (angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) =
        (((3 : ℂ) + 4 * Complex.I) / 5) ^ (2 * k) ∨
      (angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) =
        (((3 : ℂ) + 4 * Complex.I) / 5) ^ (-(2 * k)) := by
  rw [unitaryWeight_angularGrossencharacter_span_singleton k (angularPlace F)
    (two_add_toInteger_ne_zero_of_four hζ)]
  set τ := (angularPlace F).1.embedding
  have h2I : (2 + Complex.I) / (2 - Complex.I) = ((3 : ℂ) + 4 * Complex.I) / 5 := by
    have hne : (2 : ℂ) - Complex.I ≠ 0 := fun h ↦ by simpa using congrArg Complex.im h
    rw [div_eq_div_iff hne (by norm_num)]
    linear_combination 4 * Complex.I_sq
  rcases embedding_toInteger_eq_I_or_neg_I hζ τ with hI | hnegI
  · left
    have hτα : τ (((2 : 𝓞 F) + hζ.toInteger : 𝓞 F) : F) = 2 + Complex.I := by
      change τ (algebraMap (𝓞 F) F ((2 : 𝓞 F) + hζ.toInteger)) = 2 + Complex.I
      rw [map_add, map_ofNat, map_add, map_ofNat, ← RingOfIntegers.coe_eq_algebraMap, hI]
    have hconj : starRingEnd ℂ (2 + Complex.I) = 2 - Complex.I := by
      rw [map_add, map_ofNat, Complex.conj_I, sub_eq_add_neg]
    rw [hτα, hconj, h2I]
  · right
    have hτα : τ (((2 : 𝓞 F) + hζ.toInteger : 𝓞 F) : F) = 2 - Complex.I := by
      change τ (algebraMap (𝓞 F) F ((2 : 𝓞 F) + hζ.toInteger)) = 2 - Complex.I
      rw [map_add, map_ofNat, map_add, map_ofNat, ← RingOfIntegers.coe_eq_algebraMap, hnegI,
        sub_eq_add_neg]
    have hconj : starRingEnd ℂ (2 - Complex.I) = 2 + Complex.I := by
      rw [map_sub, map_ofNat, Complex.conj_I, sub_neg_eq_add]
    rw [hτα, hconj, show (2 - Complex.I) / (2 + Complex.I) = (((3 : ℂ) + 4 * Complex.I) / 5)⁻¹ by
      rw [← h2I, inv_div], inv_zpow, ← zpow_neg]

/-- **Nonreal value at `(2 + i)`**: for `k ≠ 0`, `angularGrossencharacter F k` takes a nonreal
value at `(2 + hζ.toInteger)`. -/
theorem im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4)
    {k : ℤ} (hk : k ≠ 0) :
    ((angularGrossencharacter F k).unitaryWeight.1
      (Ideal.span {(2 : 𝓞 F) + hζ.toInteger})).im ≠ 0 := by
  rcases unitaryWeight_angularGrossencharacter_two_add_toInteger hζ k with h | h <;> rw [h]
  · exact im_three_add_four_I_div_five_zpow_ne_zero (mul_ne_zero two_ne_zero hk)
  · exact im_three_add_four_I_div_five_zpow_ne_zero (neg_ne_zero.mpr (mul_ne_zero two_ne_zero hk))

/-- **Sign check at `2 + i` (positive half)**: by Hecke's unit relation, the ideal value of
`angularGrossencharacter F k` at `(2 + ζ)` equals the **inverse** of the archimedean monomial
`∏ τ, τ(2 + ζ) ^ n_τ`. -/
theorem unitaryWeight_angularGrossencharacter_two_add_toInteger_eq_inv_prod {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4) (k : ℤ) :
    (angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) =
      (∏ τ : F →+* ℂ, τ (2 + ζ) ^ (angularGrossencharacter F k).infinityType τ)⁻¹ := by
  set α : 𝓞 F := (2 : 𝓞 F) + hζ.toInteger
  have hαF : (algebraMap (𝓞 F) F α) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 F) F) (IsFractionRing.injective (𝓞 F) F)).mpr
      (two_add_toInteger_ne_zero_of_four hζ)
  let x : Fˣ := Units.mk0 (algebraMap (𝓞 F) F α) hαF
  have hcompat := (angularGrossencharacter F k).compatibility_inv x (isCongrOne_one x) α rfl
  have hz : algebraMap (𝓞 F) F hζ.toInteger = ζ := hζ.coe_toInteger
  have hxval : (x : F) = 2 + ζ := by
    change algebraMap (𝓞 F) F ((2 : 𝓞 F) + hζ.toInteger) = 2 + ζ
    rw [map_add, map_ofNat, hz]
  simpa [idealShift_angularGrossencharacter, hxval] using hcompat

/-- **Sign check at `2 + i` (negative half)**: for `k ≠ 0`, the ideal value of
`angularGrossencharacter F k` at `(2 + ζ)` is **not** equal to the uninverted archimedean monomial
`∏ τ, τ(2 + ζ) ^ n_τ`. -/
theorem unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_prod {F : Type*} [Field F]
    [NumberField F] [IsCyclotomicExtension {4} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ 4)
    {k : ℤ} (hk : k ≠ 0) :
    (angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) ≠
      ∏ τ : F →+* ℂ, τ (2 + ζ) ^ (angularGrossencharacter F k).infinityType τ := by
  intro heq
  have hinv := unitaryWeight_angularGrossencharacter_two_add_toInteger_eq_inv_prod hζ k
  set wval :=
    (angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {(2 : 𝓞 F) + hζ.toInteger}) with hwval
  have hw0 : wval ≠ 0 := fun h0 ↦
    im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero hζ hk
      (by simpa [hwval] using congrArg Complex.im h0)
  have hsq1 : wval ^ 2 = 1 := by
    rw [sq, ← mul_inv_cancel₀ hw0]
    exact congrArg (wval * ·) (hinv.trans (congrArg Inv.inv heq.symm))
  have him2 : (wval ^ 2).im ≠ 0 := by
    rw [hwval, unitaryWeight_angularGrossencharacter_apply_sq]
    exact im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero hζ
      (mul_ne_zero two_ne_zero hk)
  exact him2 (by rw [hsq1, Complex.one_im])

/-- **For `k ≠ 0`, `angularGrossencharacter F k` is not an imaginary norm twist on good ideals.**
The conjugate Gaussian primes `(2 + i)` and `(2 - i)` both have absolute norm `5` and multiply to
`(5)`, on which the angular weight is `1`; a norm twist `N(I) ^ (u * i)` would assign them the same
value `w`, forcing `w ^ 2 = 1`, whereas `w ^ 2 = ((3 ± 4i) / 5) ^ (4 * k)` is nonreal. -/
theorem angularGrossencharacter_not_isNormTwist
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] {k : ℤ} (hk : k ≠ 0)
    (u : ℝ) :
    ¬ TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood
      (angularGrossencharacter F k).unitaryWeight.1 u := by
  intro htwist
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ F
  set α : 𝓞 F := (2 : 𝓞 F) + hζ.toInteger
  set β : 𝓞 F := (2 : 𝓞 F) - hζ.toInteger
  have hNα : Ideal.absNorm (Ideal.span {α}) = 5 := by
    exact_mod_cast (RingOfIntegers.natCast_absNorm_span_singleton_of_four α).trans
      (norm_two_add_toInteger_of_four hζ)
  have hNβ : Ideal.absNorm (Ideal.span {β}) = 5 := by
    have hβ' : β = (2 : ℤ) + (-1 : ℤ) * hζ.toInteger := by simp [β, sub_eq_add_neg]
    have hn : Algebra.norm ℤ β = 5 := by
      rw [hβ', hζ.norm_intCast_add_intCast_mul_toInteger_of_four]; norm_num
    exact_mod_cast (RingOfIntegers.natCast_absNorm_span_singleton_of_four β).trans hn
  have hnormTwist := htwist.eq_normTwist (badPrimes_unitaryWeight_angularGrossencharacter F k)
  have hαprime : Ideal.IsPrimeTo (Ideal.span {α}) ∅ :=
    Ideal.isPrimeTo_iff.mpr ⟨Ideal.absNorm_eq_zero_iff.not.mp (by omega), fun _ hv ↦ hv.elim⟩
  have hβprime : Ideal.IsPrimeTo (Ideal.span {β}) ∅ :=
    Ideal.isPrimeTo_iff.mpr ⟨Ideal.absNorm_eq_zero_iff.not.mp (by omega), fun _ hv ↦ hv.elim⟩
  have heqαβ : (angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {α}) =
      (angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {β}) := by
    rw [DFunLike.congr_fun hnormTwist (Ideal.span {α}),
      DFunLike.congr_fun hnormTwist (Ideal.span {β}),
      MultiplicativeIdealWeight.normTwist_apply, MultiplicativeIdealWeight.normTwist_apply,
      MultiplicativeIdealWeight.ofBadPrimes_apply, MultiplicativeIdealWeight.ofBadPrimes_apply,
      hNα, hNβ]
    simp [hαprime, hβprime]
  have hmul5 : α * β = (5 : 𝓞 F) := by
    simp only [α, β]; linear_combination -hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hval5 : (angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {(5 : 𝓞 F)}) = 1 := by
    rw [unitaryWeight_angularGrossencharacter_span_singleton k (angularPlace F) (by norm_num),
      RingOfIntegers.coe_eq_algebraMap, map_ofNat, map_ofNat, map_ofNat, div_self (by norm_num),
      one_zpow]
  have hsq1 : ((angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {α})) ^ 2 = 1 := by
    rw [sq, ← hval5, ← hmul5, ← Ideal.span_singleton_mul_span_singleton, map_mul, heqαβ]
  have him2 : (((angularGrossencharacter F k).unitaryWeight.1 (Ideal.span {α})) ^ 2).im ≠ 0 := by
    rw [unitaryWeight_angularGrossencharacter_apply_sq]
    exact im_unitaryWeight_angularGrossencharacter_two_add_toInteger_ne_zero hζ
      (mul_ne_zero two_ne_zero hk)
  exact him2 (by rw [hsq1, Complex.one_im])

end TwoAddZetaAndNormTwist

end TauCeti.LFunctions
