/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.DirichletCharacter.Even
import Mathlib.Analysis.Complex.Basic
import TauCeti.FieldTheory.Galois.FixedField

/-!
# The maximal real subfield of a rational cyclotomic field

Let `K` be the `n`-th cyclotomic field over `ℚ`. Under Mathlib's identification
`IsCyclotomicExtension.Rat.galEquivZMod` of `Gal(K/ℚ)` with `(ℤ/nℤ)ˣ`, the class `-1` is the
automorphism `ζ ↦ ζ⁻¹`, and every complex embedding of `K` turns it into complex conjugation.
Its fixed field is therefore the maximal real subfield `K⁺`. (That an element of `K` lies in `K⁺`
as soon as it is real under one complex embedding holds for every abelian extension of `ℚ`:
`IsAbelianGalois.mem_maximalRealSubfield_iff_star_eq`.)

For `n > 2`, `K` is a CM field of degree `φ(n)`, so `K⁺` has degree `φ(n) / 2` over `ℚ`. For every
primitive `n`-th root of unity `ζ`, the sum `ζ + ζ⁻¹` is real under every complex embedding and
generates `K⁺` over `ℚ`: `K = ℚ(ζ + ζ⁻¹)(ζ)` has degree at most `2` over `ℚ(ζ + ζ⁻¹)`, since `ζ` is
a root of `X² - (ζ + ζ⁻¹) X + 1`.

Under the correspondence `IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar` between
intermediate fields of `K / ℚ` and groups of Dirichlet characters of level `n`, the maximal real
subfield corresponds to the even characters: a character is trivial on the fixing subgroup
`{1, τ}` of `K⁺` exactly when `χ (-1) = 1`. This is the classical description of `K⁺` as the
field cut out by the even characters.

## Main results

* `IsOfFinOrder.add_inv_mem_maximalRealSubfield`, `IsPrimitiveRoot.add_inv_mem_maximalRealSubfield`:
  for an element `ζ` of finite order in a field `K`, `ζ + ζ⁻¹` lies in `maximalRealSubfield K`.
* `IsPrimitiveRoot.addInvMaximalRealInteger`: `ζ + ζ⁻¹` in `𝓞 (maximalRealSubfield K)`.
* `IsPrimitiveRoot.toSubfield_adjoin_add_inv_eq_maximalRealSubfield` and
  `IsPrimitiveRoot.adjoin_rat_addInvMaximalRealInteger_eq_top`: `ζ + ζ⁻¹` generates `K⁺` over `ℚ`.
* `TauCeti.IsCyclotomicExtension.Rat.complexEmbedding_galEquivZMod_symm_neg_one_apply`: the
  automorphism attached to `-1` is complex conjugation under every complex embedding.
* `TauCeti.IsCyclotomicExtension.Rat.galEquivZMod_symm_neg_one_apply_eq_self_iff`: its fixed points
  are the maximal real subfield.
* `TauCeti.IsCyclotomicExtension.Rat.finrank_maximalRealSubfield`: for `n > 2`,
  `[K⁺ : ℚ] = φ(n) / 2`.
* The even characters cut out the maximal real subfield:
`TauCeti.IsCyclotomicExtension.Rat.toSubfield_intermediateFieldEquivSubgroupChar_symm_evenSubgroup`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapters 2 and 3.
-/

public section

open NumberField ComplexConjugate IntermediateField _root_.IsCyclotomicExtension.Rat
  DirichletCharacter Polynomial

/-- **The sum of a root of unity and its inverse is totally real**: for any element `ζ` of finite
multiplicative order in `K`, `ζ + ζ⁻¹` lies in `maximalRealSubfield K`. -/
theorem IsOfFinOrder.add_inv_mem_maximalRealSubfield {K : Type*} [Field K] {ζ : K}
    (hζ : IsOfFinOrder ζ) : ζ + ζ⁻¹ ∈ maximalRealSubfield K := by
  -- Under any complex embedding `φ`, `ζ` maps to the unit circle, where conjugation is inversion.
  intro φ
  obtain ⟨m, hm0, hm⟩ := isOfFinOrder_iff_pow_eq_one.mp hζ
  have hz : φ ζ ^ m = 1 := by rw [← map_pow, hm, map_one]
  have hnorm : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hm0.ne'
  rw [map_add, map_inv₀, star_add, star_inv₀, Complex.star_def, ← Complex.inv_eq_conj hnorm,
    inv_inv, add_comm]

namespace TauCeti.IsCyclotomicExtension.Rat

open TauCeti.DirichletCharacter

section GalEquivZMod

variable (n : ℕ) [NeZero n] {K : Type*} [Field K] [NumberField K]
  [_root_.IsCyclotomicExtension {n} ℚ K]

/-- **The automorphism of `ℚ(ζₙ)` attached to `-1` is complex conjugation.** Under every complex
embedding `φ`, the automorphism `ζ ↦ ζ⁻¹` corresponds to complex conjugation. -/
theorem complexEmbedding_galEquivZMod_symm_neg_one_apply (φ : K →+* ℂ) (x : K) :
    φ ((galEquivZMod n K).symm (-1) x) = conj (φ x) := by
  set τ := (galEquivZMod n K).symm (-1)
  have hζ := _root_.IsCyclotomicExtension.zeta_spec n ℚ K
  -- Both sides are `ℚ`-algebra maps `K → ℂ`, so they agree once they agree on the generator `ζ`.
  have hext : (φ.comp (τ : K →+* K)).toRatAlgHom = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top
      (_root_.IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) ?_
    rintro _ rfl
    set z := φ (_root_.IsCyclotomicExtension.zeta n ℚ K)
    have hz : z ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    -- `τ` raises `ζ` to the representative `k` of `-1`, and `z ^ k = z⁻¹` since `n ∣ k + 1`.
    set k := ((-1 : (ZMod n)ˣ) : ZMod n).val
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff (k + 1) n).1 (by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, Units.val_neg, Units.val_one, Nat.cast_one,
        neg_add_cancel])
    have hk : z ^ k = z⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hm, pow_mul, hz, one_pow])
    simp only [RingHom.toRatAlgHom_apply, RingHom.comp_apply, RingHom.coe_coe]
    rw [galEquivZMod_apply_of_pow_eq n K τ hζ.pow_eq_one, MulEquiv.apply_symm_apply, map_pow, hk,
      Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz (NeZero.ne n))]
  simpa using congr($hext x)

/-- **The fixed field of `ζ ↦ ζ⁻¹` is the maximal real subfield.** An element of `ℚ(ζₙ)` is fixed
by the automorphism attached to `-1` exactly when it is real under every complex embedding. -/
theorem galEquivZMod_symm_neg_one_apply_eq_self_iff (x : K) :
    (galEquivZMod n K).symm (-1) x = x ↔ x ∈ maximalRealSubfield K := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  refine ⟨fun hx ψ ↦ ?_, fun hx ↦ φ.injective ?_⟩
  · rw [Complex.star_def, ← complexEmbedding_galEquivZMod_symm_neg_one_apply n, hx]
  · rw [complexEmbedding_galEquivZMod_symm_neg_one_apply n, ← Complex.star_def]
    exact hx φ

variable (K)

/-- The fixed field of the cyclic subgroup generated by `ζ ↦ ζ⁻¹` is the maximal real
subfield of the cyclotomic field. -/
theorem toSubfield_fixedField_zpowers_galEquivZMod_symm_neg_one :
    (fixedField (Subgroup.zpowers ((galEquivZMod n K).symm (-1)))).toSubfield =
      maximalRealSubfield K := by
  ext x
  rw [mem_toSubfield, mem_fixedField_zpowers_iff,
    galEquivZMod_symm_neg_one_apply_eq_self_iff]

variable (R : Type*) [CommRing R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
  [IsAbelianGalois ℚ K]

/-- A character belongs to the character group of a cyclic fixed field exactly when it is
trivial on the chosen generator. -/
theorem mem_intermediateFieldEquivSubgroupChar_fixedField_zpowers_iff
    (σ : Gal(K/ℚ)) (χ : DirichletCharacter R n) :
    χ ∈ intermediateFieldEquivSubgroupChar n K R (fixedField (Subgroup.zpowers σ)) ↔
      χ (galEquivZMod n K σ) = 1 := by
  have hker (τ : Gal(K/ℚ)) : χ (galEquivZMod n K τ) = 1 ↔
      τ ∈ (χ.toUnitHom.comp (galEquivZMod n K).toMonoidHom).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← Units.val_eq_one,
      MulChar.coe_toUnitHom]
  rw [mem_intermediateFieldEquivSubgroupChar_iff, fixingSubgroup_fixedField]
  simp_rw [hker]
  exact Subgroup.zpowers_le

/-- **The even characters cut out the maximal real subfield.** Under the correspondence between
intermediate fields of `ℚ(ζₙ) / ℚ` and groups of Dirichlet characters of level `n`, the group of
even characters corresponds to the maximal real subfield of `ℚ(ζₙ)`. -/
theorem toSubfield_intermediateFieldEquivSubgroupChar_symm_evenSubgroup :
    ((intermediateFieldEquivSubgroupChar n K R).symm (evenSubgroup R n)).toSubfield =
      maximalRealSubfield K := by
  rw [← toSubfield_fixedField_zpowers_galEquivZMod_symm_neg_one n K]
  suffices intermediateFieldEquivSubgroupChar n K R
      (fixedField (Subgroup.zpowers ((galEquivZMod n K).symm (-1)))) = evenSubgroup R n by
    rw [← this, OrderIso.symm_apply_apply]
  ext χ
  simp only [mem_intermediateFieldEquivSubgroupChar_fixedField_zpowers_iff,
    MulEquiv.apply_symm_apply, Units.val_neg, Units.val_one,
    _root_.DirichletCharacter.mem_evenSubgroup_iff, _root_.DirichletCharacter.Even]

end GalEquivZMod

/-- **The degree of the maximal real subfield of `ℚ(ζₙ)` is `φ(n) / 2`** when `n > 2`. -/
theorem finrank_maximalRealSubfield (n : ℕ) (K : Type*) [Field K] [CharZero K]
    [_root_.IsCyclotomicExtension {n} ℚ K] (hn : 2 < n) :
    Module.finrank ℚ (maximalRealSubfield K) = n.totient / 2 := by
  have : NeZero n := ⟨by omega⟩
  have : NumberField K := _root_.IsCyclotomicExtension.numberField {n} ℚ K
  have : IsCMField K :=
    _root_.IsCyclotomicExtension.Rat.isCMField K ⟨n, Set.mem_singleton n, hn⟩
  have htower := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K,
    _root_.IsCyclotomicExtension.Rat.finrank n K] at htower
  omega

end TauCeti.IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] {n : ℕ} {ζ : K}

/-- For a primitive `n`-th root of unity `ζ`, the real combination `ζ + ζ⁻¹` lies in
`maximalRealSubfield K`. -/
theorem add_inv_mem_maximalRealSubfield [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    ζ + ζ⁻¹ ∈ maximalRealSubfield K :=
  (hζ.isOfFinOrder (NeZero.ne n)).add_inv_mem_maximalRealSubfield

/-- **The real cyclotomic integer `ζ + ζ⁻¹`** as an element of the ring of integers
`𝓞 (maximalRealSubfield K)`. -/
noncomputable def addInvMaximalRealInteger [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    𝓞 (maximalRealSubfield K) :=
  ⟨⟨ζ + ζ⁻¹, hζ.add_inv_mem_maximalRealSubfield⟩, by
    rw [mem_integralClosure_iff, ← isIntegral_algebraMap_iff (B := K)]
    exact (hζ.isIntegral (NeZero.pos n)).add (hζ.inv.isIntegral (NeZero.pos n))⟩

/-- Coercing `hζ.addInvMaximalRealInteger` to `maximalRealSubfield K` gives `ζ + ζ⁻¹`. -/
@[simp]
theorem coe_addInvMaximalRealInteger [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    (hζ.addInvMaximalRealInteger : maximalRealSubfield K) =
      ⟨ζ + ζ⁻¹, hζ.add_inv_mem_maximalRealSubfield⟩ :=
  (rfl)

/-- Coercing `hζ.addInvMaximalRealInteger` all the way to `K` gives `ζ + ζ⁻¹`. -/
theorem coe_coe_addInvMaximalRealInteger [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    ((hζ.addInvMaximalRealInteger : maximalRealSubfield K) : K) = ζ + ζ⁻¹ :=
  (rfl)

/-- Over `ℚ(ζ + ζ⁻¹)`, `ℚ(ζₙ)` has degree at most `2`. -/
private theorem finrank_adjoin_add_inv_le_two [NeZero n] [CharZero K]
    [_root_.IsCyclotomicExtension {n} ℚ K] (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank (IntermediateField.adjoin ℚ ({ζ + ζ⁻¹} : Set K)) K ≤ 2 := by
  have : NumberField K := _root_.IsCyclotomicExtension.numberField {n} ℚ K
  set E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {ζ + ζ⁻¹}
  have hle : Algebra.adjoin ℚ ({ζ} : Set K) ≤ E⟮ζ⟯.toSubalgebra.restrictScalars ℚ := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Subalgebra.mem_restrictScalars, IntermediateField.mem_toSubalgebra]
    exact IntermediateField.mem_adjoin_simple_self E ζ
  have htop : E⟮ζ⟯ = ⊤ := eq_top_iff.2 fun x _ ↦ by
    rw [← IntermediateField.mem_toSubalgebra, ← Subalgebra.mem_restrictScalars (R := ℚ)]
    apply hle
    rw [_root_.IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
    exact Algebra.mem_top
  -- `ζ` is a root of the monic quadratic `X² - (ζ + ζ⁻¹) X + 1` over `E`.
  let p : E[X] := X ^ 2 - C ⟨ζ + ζ⁻¹, IntermediateField.mem_adjoin_simple_self ℚ _⟩ * X + 1
  have hp_deg : p.natDegree ≤ 2 := by dsimp [p]; compute_degree!
  have hp_monic : p.Monic :=
    monic_of_natDegree_le_of_coeff_eq_one 2 hp_deg (by simp [p, coeff_one])
  have hp_aeval : aeval ζ p = 0 := by
    have hmul : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ (hζ.ne_zero (NeZero.ne n))
    simp only [p, map_add, map_sub, map_mul, map_pow, map_one, aeval_X, aeval_C,
      IntermediateField.algebraMap_apply]
    linear_combination -hmul
  have h1 : Module.finrank E K = (minpoly E ζ).natDegree := by
    rw [← IntermediateField.finrank_top', ← htop]
    exact IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ)
  have h2 : (minpoly E ζ).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd (minpoly.dvd E ζ hp_aeval) hp_monic.ne_zero
  omega

/-- **`ζ + ζ⁻¹` generates the maximal real subfield of `ℚ(ζₙ)` over `ℚ`.** -/
theorem toSubfield_adjoin_add_inv_eq_maximalRealSubfield [NeZero n] [CharZero K]
    [_root_.IsCyclotomicExtension {n} ℚ K] (hζ : IsPrimitiveRoot ζ n) :
    (IntermediateField.adjoin ℚ {ζ + ζ⁻¹}).toSubfield = maximalRealSubfield K := by
  have : NumberField K := _root_.IsCyclotomicExtension.numberField {n} ℚ K
  set E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {ζ + ζ⁻¹}
  set M : IntermediateField ℚ K :=
    fixedField (Subgroup.zpowers ((galEquivZMod n K).symm (-1)))
  have hM : M.toSubfield = maximalRealSubfield K :=
    TauCeti.IsCyclotomicExtension.Rat.toSubfield_fixedField_zpowers_galEquivZMod_symm_neg_one n K
  suffices E = M by rw [this, hM]
  have hEM : E ≤ M := IntermediateField.adjoin_le_iff.2 <| Set.singleton_subset_iff.2 <| by
    rw [SetLike.mem_coe, ← mem_toSubfield, hM]
    exact hζ.add_inv_mem_maximalRealSubfield
  by_cases hn : 2 < n
  · have : Fact (1 < n) := ⟨by omega⟩
    have hcard : Module.finrank M K = 2 := by
      rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, MulEquiv.orderOf_eq,
        Units.orderOf_neg_one, ZMod.ringChar_zmod_n,
        ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)]
    exact IntermediateField.eq_of_le_of_finrank_le' hEM
      (hζ.finrank_adjoin_add_inv_le_two.trans_eq hcard.symm)
  · have hn0 : 0 < n := NeZero.pos n
    have hfin1 : Module.finrank ℚ K = 1 := by
      rw [_root_.IsCyclotomicExtension.Rat.finrank n K]
      interval_cases n <;> decide
    have hEtop : E = ⊤ := IntermediateField.eq_of_le_of_finrank_le le_top <| by
      rw [IntermediateField.finrank_top', hfin1]
      exact Module.finrank_pos
    exact le_antisymm hEM (hEtop.symm ▸ le_top)

/-- **`ζ + ζ⁻¹` generates `maximalRealSubfield K` as a `ℚ`-algebra.** -/
theorem adjoin_rat_addInvMaximalRealInteger_eq_top [NeZero n] [CharZero K]
    [_root_.IsCyclotomicExtension {n} ℚ K] (hζ : IsPrimitiveRoot ζ n) :
    Algebra.adjoin ℚ {(hζ.addInvMaximalRealInteger : maximalRealSubfield K)} = ⊤ := by
  have : NumberField K := _root_.IsCyclotomicExtension.numberField {n} ℚ K
  rw [eq_top_iff]
  intro x _
  -- Since `K / ℚ` is algebraic, `Algebra.adjoin ℚ {ζ + ζ⁻¹}` agrees with `ℚ(ζ + ζ⁻¹)`.
  have : Algebra.IsAlgebraic ℚ K := NumberField.isAlgebraic K
  have heq : Algebra.adjoin ℚ ({ζ + ζ⁻¹} : Set K) =
      (IntermediateField.adjoin ℚ {ζ + ζ⁻¹}).toSubalgebra :=
    (IntermediateField.adjoin_toSubalgebra {ζ + ζ⁻¹}).symm
  have hxK : (x : K) ∈ (IntermediateField.adjoin ℚ {ζ + ζ⁻¹}).toSubfield := by
    rw [hζ.toSubfield_adjoin_add_inv_eq_maximalRealSubfield]
    exact x.2
  have hxA : (x : K) ∈ Algebra.adjoin ℚ ({ζ + ζ⁻¹} : Set K) := by
    rwa [heq, mem_toSubalgebra, ← mem_toSubfield]
  have hf : ∀ z : maximalRealSubfield K,
      IsScalarTower.toAlgHom ℚ (maximalRealSubfield K) K z = (z : K) := fun z ↦ by
    rw [IsScalarTower.toAlgHom_apply, Subfield.algebraMap_ofSubfield, Subfield.coe_subtype]
  have hmap := Algebra.adjoin_image (R := ℚ) (A := maximalRealSubfield K) (B := K)
    (IsScalarTower.toAlgHom ℚ (maximalRealSubfield K) K)
    {(hζ.addInvMaximalRealInteger : maximalRealSubfield K)}
  rw [Set.image_singleton, hf, hζ.coe_coe_addInvMaximalRealInteger] at hmap
  have hxmap : (x : K) ∈ (Algebra.adjoin ℚ
      {(hζ.addInvMaximalRealInteger : maximalRealSubfield K)}).map
      (IsScalarTower.toAlgHom ℚ (maximalRealSubfield K) K) := by
    rw [← hmap]
    exact hxA
  obtain ⟨y, hy, hyx⟩ := Subalgebra.mem_map.mp hxmap
  rw [hf] at hyx
  obtain rfl : y = x := Subtype.ext hyx
  exact hy

end IsPrimitiveRoot
