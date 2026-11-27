/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.DirichletCharacter.Even
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.Analysis.Complex.Basic
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealSubfield

/-!
# The maximal real subfield of a cyclotomic field

Let `K` be the `n`-th cyclotomic field over `ℚ`. Under Mathlib's identification
`IsCyclotomicExtension.Rat.galEquivZMod` of `Gal(K/ℚ)` with `(ℤ/nℤ)ˣ`, the class `-1` is the
automorphism `ζ ↦ ζ⁻¹`, and every complex embedding of `K` turns it into complex conjugation.
Its fixed field is therefore the maximal real subfield `K⁺`. (That an element of `K` lies in `K⁺`
as soon as it is real under one complex embedding holds for every abelian extension of `ℚ`:
`IsAbelianGalois.mem_maximalRealSubfield_iff_star_eq`.)

Under the correspondence `IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar` between
intermediate fields of `K / ℚ` and groups of Dirichlet characters of level `n`, the maximal real
subfield corresponds to the even characters: a character is trivial on the fixing subgroup
`{1, τ}` of `K⁺` exactly when `χ (-1) = 1`. This is the classical description of `K⁺` as the
field cut out by the even characters.

The field `ℚ(ζ + ζ⁻¹)` is the fixed field of `ζ ↦ ζ⁻¹` for any primitive `n`-th root of unity
`ζ`: an automorphism fixing `ζ + ζ⁻¹` sends `ζ` to a root of `X² - (ζ + ζ⁻¹) X + 1`, that is to
`ζ` or `ζ⁻¹`. The extension `K / K⁺` has degree `2` for `n > 2` and degree `1` for `n ≤ 2`, where
`K = ℚ`. Accordingly the relative norm from `K` to `K⁺` sends `x` to `x` times its image under
`ζ ↦ ζ⁻¹` for `n > 2`, and is the identity for `n ≤ 2`. These are the norms that turn the
cyclotomic numbers of `K` into the real cyclotomic numbers of `K⁺`.

More generally, let `k` be a totally real field and `K = k(μₙ)`. For every primitive `n`-th root
of unity `ζ`, the maximal real subfield of `K` is `k(ζ + ζ⁻¹)`, and for `n > 2` the field `K` is a
CM field, quadratic over `k(ζ + ζ⁻¹)`. The image of `k` and `ζ + ζ⁻¹` are real under every complex
embedding, so `k(ζ + ζ⁻¹) ⊆ K⁺`. Since `ζ` is a root of `X² - (ζ + ζ⁻¹) X + 1` and generates `K`,
the degree of `K` over `k(ζ + ζ⁻¹)` is at most `2`, with equality for `n > 2` because `ζ` is not
real unless `ζ = ±1`. For `n > 2` the field `K` is also totally complex, so Mathlib's
`NumberField.CMExtension.eq_maximalRealSubfield` identifies `k(ζ + ζ⁻¹)` with `K⁺`, and
`NumberField.IsCMField.ofCMExtension` shows that `K` is CM. For `n ≤ 2`, `ζ = ±1` and
`k(ζ + ζ⁻¹) = K`.
Consequently every root of unity of order `m > 2` in `K` generates `K` over `k(ζ + ζ⁻¹)`; in
particular, so do the `ℓ`-th roots of unity for an odd prime `ℓ` dividing `n`.

## Main results

Except for the `IsPrimitiveRoot` lemmas and `IsCyclotomicExtension.isCMField`, all results are in
the namespace `TauCeti.IsCyclotomicExtension.Rat`.

* `complexEmbedding_galEquivZMod_symm_neg_one_apply`: the automorphism attached to `-1` is
  complex conjugation under every complex embedding.
* `galEquivZMod_symm_neg_one_apply_eq_self_iff`: its fixed points are the maximal real subfield.
* `IsPrimitiveRoot.adjoin_add_inv_eq_fixedField`: `ℚ(ζ + ζ⁻¹)` is the fixed field of `ζ ↦ ζ⁻¹`.
* `maximalRealSubfield_eq_top_iff` and `finrank_maximalRealSubfield`: `K⁺ = K` exactly when
  `n ≤ 2`, and `[K : K⁺]` is `2` for `n > 2` and `1` otherwise.
* `algebraMap_norm_maximalRealSubfield_of_two_lt` and
  `algebraMap_norm_maximalRealSubfield_of_le_two`: the relative norm from `K` to `K⁺`.
* `toSubfield_intermediateFieldEquivSubgroupChar_symm_evenSubgroup`: the even characters cut out
  the maximal real subfield.
* `finrank_rat_maximalRealSubfield`: for `n > 2` the maximal real subfield has degree `φ(n) / 2`
  over `ℚ`.

Over a totally real base `k`, for `K = k(μₙ)` and a primitive `n`-th root of unity `ζ`:

* `IsPrimitiveRoot.toSubfield_adjoin_add_inv_eq_maximalRealSubfield`: `K⁺ = k(ζ + ζ⁻¹)`.
* `IsPrimitiveRoot.finrank_adjoin_add_inv_eq_two`: for `n > 2`, `[K : k(ζ + ζ⁻¹)] = 2`.
* `IsCyclotomicExtension.isCMField`: for `n > 2`, `K` is a CM field.
* `IsPrimitiveRoot.adjoin_adjoin_add_inv_eq_top`: every root of unity of order `m > 2` in `K`
  generates `K` over `k(ζ + ζ⁻¹)`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 3.
-/

public section

open NumberField ComplexConjugate IntermediateField _root_.IsCyclotomicExtension.Rat
  DirichletCharacter

namespace TauCeti.IsCyclotomicExtension.Rat

open TauCeti.DirichletCharacter

variable (n : ℕ) [NeZero n] {K : Type*} [Field K] [NumberField K]
  [_root_.IsCyclotomicExtension {n} ℚ K]

/-- The automorphism of `ℚ(ζₙ)` attached to `-1` inverts every `n`-th root of unity. -/
theorem galEquivZMod_symm_neg_one_apply_of_pow_eq_one {x : K} (hx : x ^ n = 1) :
    (galEquivZMod n K).symm (-1) x = x⁻¹ := by
  rw [galEquivZMod_apply_of_pow_eq n K _ hx, MulEquiv.apply_symm_apply]
  -- The representative `k` of `-1` satisfies `n ∣ k + 1`, so `x ^ k * x = 1`.
  obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff (((-1 : (ZMod n)ˣ) : ZMod n).val + 1) n).1 (by
    rw [Nat.cast_add, ZMod.natCast_zmod_val, Units.val_neg, Units.val_one, Nat.cast_one,
      neg_add_cancel])
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hm, pow_mul, hx, one_pow])

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
    have hz : φ (_root_.IsCyclotomicExtension.zeta n ℚ K) ^ n = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    simp only [RingHom.toRatAlgHom_apply, RingHom.comp_apply, RingHom.coe_coe]
    rw [galEquivZMod_symm_neg_one_apply_of_pow_eq_one n hζ.pow_eq_one, map_inv₀,
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

/-- The automorphism `ζ ↦ ζ⁻¹` of `ℚ(ζₙ)` is trivial exactly when `n ≤ 2`. -/
theorem galEquivZMod_symm_neg_one_eq_one_iff : (galEquivZMod n K).symm (-1) = 1 ↔ n ≤ 2 := by
  rw [MulEquiv.symm_apply_eq, map_one, Units.ext_iff, Units.val_neg, Units.val_one,
    ZMod.neg_one_eq_one_iff]
  have := NeZero.ne n
  omega

/-- **`ℚ(ζₙ)` is its own maximal real subfield exactly when `n ≤ 2`.** -/
theorem maximalRealSubfield_eq_top_iff : maximalRealSubfield K = ⊤ ↔ n ≤ 2 := by
  rw [← galEquivZMod_symm_neg_one_eq_one_iff n (K := K), eq_top_iff]
  refine ⟨fun h ↦ AlgEquiv.ext fun x ↦ ?_, fun h x _ ↦ ?_⟩
  · exact (galEquivZMod_symm_neg_one_apply_eq_self_iff n x).2 (h trivial)
  · rw [← galEquivZMod_symm_neg_one_apply_eq_self_iff n, h, AlgEquiv.one_apply]

variable {K} in
/-- For `n ≤ 2` every element of `ℚ(ζₙ) = ℚ` lies in its maximal real subfield. -/
theorem mem_maximalRealSubfield_of_le_two (hn : n ≤ 2) (x : K) : x ∈ maximalRealSubfield K := by
  rw [(maximalRealSubfield_eq_top_iff n K).2 hn]
  trivial

/-- For `n ≤ 2` the extension of `ℚ(ζₙ) = ℚ` over its maximal real subfield is trivial. -/
theorem finrank_maximalRealSubfield_of_le_two (hn : n ≤ 2) :
    Module.finrank (maximalRealSubfield K) K = 1 := by
  refine (finrank_eq_one_iff_of_ne_zero' (1 : K) one_ne_zero).2 fun y ↦
    ⟨⟨y, mem_maximalRealSubfield_of_le_two n hn y⟩, ?_⟩
  simp [Algebra.smul_def, Subfield.algebraMap_ofSubfield]

/-- **The degree of `ℚ(ζₙ)` over its maximal real subfield** is `2` for `n > 2` and `1` for
`n ≤ 2`. -/
theorem finrank_maximalRealSubfield :
    Module.finrank (maximalRealSubfield K) K = if 2 < n then 2 else 1 := by
  split_ifs with hn
  · have := _root_.IsCyclotomicExtension.Rat.isCMField K ⟨n, Set.mem_singleton n, hn⟩
    exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · exact finrank_maximalRealSubfield_of_le_two n K (not_lt.1 hn)

/-- On a CM cyclotomic field, Mathlib's `IsCMField.complexConj` is the automorphism attached to
`-1`. -/
theorem restrictScalars_complexConj [IsCMField K] :
    (IsCMField.complexConj K).restrictScalars ℚ = (galEquivZMod n K).symm (-1) := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  ext x
  apply φ.injective
  rw [AlgEquiv.restrictScalars_apply, IsCMField.complexEmbedding_complexConj,
    complexEmbedding_galEquivZMod_symm_neg_one_apply]

variable {K} in
/-- **The norm to the maximal real subfield for `n > 2`.** The relative norm from `ℚ(ζₙ)` to its
maximal real subfield sends `x` to `x` times its image under `ζ ↦ ζ⁻¹`. -/
theorem algebraMap_norm_maximalRealSubfield_of_two_lt (hn : 2 < n) (x : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) x) =
      x * (galEquivZMod n K).symm (-1) x := by
  have := _root_.IsCyclotomicExtension.Rat.isCMField K ⟨n, Set.mem_singleton n, hn⟩
  rw [IsCMField.algebraMap_norm_eq_mul_complexConj, ← restrictScalars_complexConj n,
    AlgEquiv.restrictScalars_apply]

variable {K} in
/-- **The norm to the maximal real subfield for `n ≤ 2`.** Then `ℚ(ζₙ)` is its own maximal real
subfield and the relative norm is the identity. -/
theorem algebraMap_norm_maximalRealSubfield_of_le_two (hn : n ≤ 2) (x : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) x) = x := by
  have hx' : algebraMap (maximalRealSubfield K) K ⟨x, mem_maximalRealSubfield_of_le_two n hn x⟩ =
      x := by
    simp [Subfield.algebraMap_ofSubfield]
  rw [← hx', Algebra.norm_algebraMap, finrank_maximalRealSubfield_of_le_two n K hn, pow_one]

/-- **The degree of the maximal real subfield.** For `n > 2`, the maximal real subfield of the
`n`-th cyclotomic field has degree `φ(n) / 2` over `ℚ`, since the cyclotomic field is quadratic
over it. -/
theorem finrank_rat_maximalRealSubfield (hn : 2 < n) :
    Module.finrank ℚ (maximalRealSubfield K) = n.totient / 2 := by
  have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
  rw [finrank_maximalRealSubfield n K, ite_eq_left hn,
    _root_.IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))]
    at h
  omega

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

end TauCeti.IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

open TauCeti.IsCyclotomicExtension.Rat

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [_root_.IsCyclotomicExtension {n} ℚ K] {ζ : K}

/-- **`ζ + ζ⁻¹` generates the fixed field of `ζ ↦ ζ⁻¹`.** For a primitive `n`-th root of unity
`ζ` in `ℚ(ζₙ)`, the field `ℚ(ζ + ζ⁻¹)` is the fixed field of the automorphism attached to
`-1`. -/
theorem adjoin_add_inv_eq_fixedField (hζ : IsPrimitiveRoot ζ n) :
    ℚ⟮ζ + ζ⁻¹⟯ = fixedField (Subgroup.zpowers ((galEquivZMod n K).symm (-1))) := by
  set τ := (galEquivZMod n K).symm (-1)
  have hτζ : τ ζ = ζ⁻¹ := galEquivZMod_symm_neg_one_apply_of_pow_eq_one n hζ.pow_eq_one
  refine le_antisymm ?_ ?_
  · rw [adjoin_simple_le_iff, mem_fixedField_zpowers_iff, map_add, map_inv₀, hτζ, inv_inv,
      add_comm]
  -- Conversely, every automorphism fixing `ζ + ζ⁻¹` is `1` or `τ`.
  have := _root_.IsCyclotomicExtension.isGalois {n} ℚ K
  rw [← IsGalois.fixedField_fixingSubgroup ℚ⟮ζ + ζ⁻¹⟯]
  refine fixedField_le fun σ hσ ↦ ?_
  have hext {σ₁ σ₂ : Gal(K/ℚ)} (h : σ₁ ζ = σ₂ ζ) : σ₁ = σ₂ :=
    TauCeti.IntermediateField.algEquiv_ext_of_adjoin_eq_top (adjoin_eq_top_of_algebra _ _
      (_root_.IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)) (by rintro _ rfl; exact h)
  have hs : σ ζ + (σ ζ)⁻¹ = ζ + ζ⁻¹ := by
    rw [← map_inv₀, ← map_add]
    exact hσ ⟨_, mem_adjoin_simple_self ℚ _⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  have hσζ0 : σ ζ ≠ 0 := (map_ne_zero σ).2 hζ0
  -- `w = σ ζ` satisfies `w + w⁻¹ = ζ + ζ⁻¹`, so `(w - ζ) * (w * ζ - 1) = 0`.
  have hprod : (σ ζ - ζ) * (σ ζ * ζ - 1) = σ ζ * ζ * ((σ ζ + (σ ζ)⁻¹) - (ζ + ζ⁻¹)) := by
    field_simp
    ring
  rw [hs, sub_self, mul_zero] at hprod
  rcases mul_eq_zero.1 hprod with h | h
  · rw [hext (σ₂ := 1) (sub_eq_zero.1 h)]
    exact Subgroup.one_mem _
  · rw [hext (σ₂ := τ) ((eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h)).trans hτζ.symm)]
    exact Subgroup.mem_zpowers τ

end IsPrimitiveRoot

/-! ### Cyclotomic extensions of a totally real field -/

namespace IsPrimitiveRoot

open Module

variable {n : ℕ} {k K : Type*} [Field k] [Field K] [Algebra k K]
  [_root_.IsCyclotomicExtension {n} k K] {ζ : K}

/-- If `k(ζ + ζ⁻¹)` contains the generator `ζ` of `K = k(μₙ)`, it is all of `K`. -/
private theorem adjoin_add_inv_eq_top_of_mem [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (h : ζ ∈ k⟮ζ + ζ⁻¹⟯) : k⟮ζ + ζ⁻¹⟯ = ⊤ := by
  rw [eq_top_iff, ← adjoin_eq_top_of_algebra _ _
    (_root_.IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ), adjoin_simple_le_iff]
  exact h

variable [NumberField K]

/-- If `ζ` generates `K = k(μₙ)` and does not lie in `k(ζ + ζ⁻¹)`, then `K` is quadratic over
`k(ζ + ζ⁻¹)`. -/
private theorem finrank_adjoin_add_inv_eq_two_of_notMem [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (h : ζ ∉ k⟮ζ + ζ⁻¹⟯) : finrank k⟮ζ + ζ⁻¹⟯ K = 2 := by
  have hgen : k⟮ζ⟯ = ⊤ := adjoin_eq_top_of_algebra _ _
    (_root_.IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
  refine le_antisymm (TauCeti.IntermediateField.finrank_adjoin_add_inv_le_two hgen) ?_
  have : Module.Finite k⟮ζ + ζ⁻¹⟯ K := .of_restrictScalars_finite ℚ _ K
  have hpos : 0 < finrank k⟮ζ + ζ⁻¹⟯ K := finrank_pos
  have hne : finrank k⟮ζ + ζ⁻¹⟯ K ≠ 1 := fun h1 ↦ h <| by
    refine TauCeti.IntermediateField.mem_bot_iff_mem.1 ?_
    rw [bot_eq_top_iff_finrank_eq_one.2 h1]
    exact mem_top
  omega

variable [IsTotallyReal k]

/-- **`k(ζₙ)` is quadratic over `k(ζ + ζ⁻¹)`** for `n > 2`, over a totally real base `k`. -/
theorem finrank_adjoin_add_inv_eq_two (hn : 2 < n) (hζ : IsPrimitiveRoot ζ n) :
    finrank k⟮ζ + ζ⁻¹⟯ K = 2 := by
  have : NeZero n := ⟨by omega⟩
  exact finrank_adjoin_add_inv_eq_two_of_notMem hζ fun h ↦ hζ.notMem_maximalRealSubfield hn
    (toSubfield_adjoin_add_inv_le_maximalRealSubfield (NeZero.ne n) hζ.pow_eq_one
      ((mem_toSubfield _ _).2 h))

/-- For `n > 2`, `K = k(ζₙ)` is a CM extension of `k(ζ + ζ⁻¹)`: `K` is totally complex, and
`k(ζ + ζ⁻¹)` is a totally real subfield over which `K` is quadratic. -/
private theorem isCMExtension_adjoin_add_inv (hn : 2 < n) (hζ : IsPrimitiveRoot ζ n) :
    IsTotallyComplex K ∧ IsTotallyReal k⟮ζ + ζ⁻¹⟯.toSubfield ∧
      Algebra.IsQuadraticExtension k⟮ζ + ζ⁻¹⟯.toSubfield K :=
  ⟨nrRealPlaces_eq_zero_iff.1 (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hn hζ),
    isTotallyReal_iff_le_maximalRealSubfield.2
      (toSubfield_adjoin_add_inv_le_maximalRealSubfield (by omega) hζ.pow_eq_one),
    ⟨finrank_adjoin_add_inv_eq_two hn hζ⟩⟩

/-- **The maximal real subfield of `k(ζₙ)` is `k(ζ + ζ⁻¹)`** over a totally real base `k`, for
every primitive `n`-th root of unity `ζ`. -/
theorem toSubfield_adjoin_add_inv_eq_maximalRealSubfield [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    k⟮ζ + ζ⁻¹⟯.toSubfield = maximalRealSubfield K := by
  by_cases hn : 2 < n
  · obtain ⟨_, _, _⟩ := isCMExtension_adjoin_add_inv (k := k) hn hζ
    exact CMExtension.eq_maximalRealSubfield K _
  -- For `n ≤ 2`, `ζ = ±1` lies in `k(ζ + ζ⁻¹)`, which is therefore all of `K`.
  refine le_antisymm
    (toSubfield_adjoin_add_inv_le_maximalRealSubfield (NeZero.ne n) hζ.pow_eq_one) ?_
  rw [adjoin_add_inv_eq_top_of_mem hζ ?_, top_toSubfield]
  · exact le_top
  have := NeZero.pos n
  interval_cases n
  · rw [one_right_iff.1 hζ]
    exact one_mem _
  · rw [hζ.eq_neg_one_of_two_right]
    exact neg_mem (one_mem _)

variable (k K) in
include k in
/-- **Cyclotomic extensions of totally real fields are CM.** For a totally real field `k` and
`n > 2`, the cyclotomic extension `k(μₙ)` is a CM field; its maximal real subfield is
`k(ζ + ζ⁻¹)` by `IsPrimitiveRoot.toSubfield_adjoin_add_inv_eq_maximalRealSubfield`. -/
theorem _root_.IsCyclotomicExtension.isCMField (hn : 2 < n) : IsCMField K := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : K, IsPrimitiveRoot ζ n :=
    ⟨_, _root_.IsCyclotomicExtension.zeta_spec n k K⟩
  obtain ⟨_, _, _⟩ := isCMExtension_adjoin_add_inv (k := k) hn hζ
  exact IsCMField.ofCMExtension k⟮ζ + ζ⁻¹⟯.toSubfield K

/-- **`k(ζ + ζ⁻¹)(η) = k(ζₙ)` for every root of unity `η` of order `m > 2`** in `k(ζₙ)`, over a
totally real base `k`. For instance, for an odd prime `ℓ` dividing `n`, adjoining the `ℓ`-th roots
of unity to `k(ζ + ζ⁻¹)` gives all of `k(ζₙ)`. -/
theorem adjoin_adjoin_add_inv_eq_top [NeZero n] (hζ : IsPrimitiveRoot ζ n) {m : ℕ} (hm : 2 < m)
    {η : K} (hη : IsPrimitiveRoot η m) : adjoin k⟮ζ + ζ⁻¹⟯ {η} = ⊤ := by
  have hle := toSubfield_adjoin_add_inv_le_maximalRealSubfield (k := k) (NeZero.ne n)
    hζ.pow_eq_one
  have hη : η ∉ k⟮ζ + ζ⁻¹⟯ := fun h ↦
    hη.notMem_maximalRealSubfield hm (hle ((mem_toSubfield _ _).2 h))
  -- Hence `k(ζ + ζ⁻¹) ≠ K`, so `ζ ∉ k(ζ + ζ⁻¹)` and `K` is quadratic over `k(ζ + ζ⁻¹)`.
  have hζ' : ζ ∉ k⟮ζ + ζ⁻¹⟯ := fun h ↦ hη <| by
    rw [adjoin_add_inv_eq_top_of_mem hζ h]
    exact mem_top
  have := isSimpleOrder_of_finrank_prime k⟮ζ + ζ⁻¹⟯ K
    (finrank_adjoin_add_inv_eq_two_of_notMem hζ hζ' ▸ Nat.prime_two)
  refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun hbot ↦
    hη (TauCeti.IntermediateField.mem_bot_iff_mem.1 ?_)
  rw [← hbot]
  exact mem_adjoin_simple_self _ η

end IsPrimitiveRoot
