/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
Its fixed field is therefore the maximal real subfield `K⁺`, and an element of `K` lies in `K⁺` as
soon as it is real under one complex embedding.

Under the correspondence `IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar` between
intermediate fields of `K / ℚ` and groups of Dirichlet characters of level `n`, the maximal real
subfield corresponds to the even characters: a character is trivial on the fixing subgroup
`{1, τ}` of `K⁺` exactly when `χ (-1) = 1`. This is the classical description of `K⁺` as the
field cut out by the even characters.

## Main results

All results are in the namespace `TauCeti.IsCyclotomicExtension.Rat`.

* `complexEmbedding_galEquivZMod_symm_neg_one_apply`: the automorphism attached to `-1` is
  complex conjugation under every complex embedding.
* `galEquivZMod_symm_neg_one_apply_eq_self_iff`: its fixed points are the maximal real subfield.
* `mem_maximalRealSubfield_iff_star_eq`: one complex embedding suffices to test membership in the
  maximal real subfield.
* `toSubfield_intermediateFieldEquivSubgroupChar_symm_evenSubgroup`: the even characters cut out
  the maximal real subfield.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 3.
-/

public section

open NumberField ComplexConjugate IntermediateField _root_.IsCyclotomicExtension.Rat
  DirichletCharacter

namespace TauCeti.IsCyclotomicExtension.Rat

variable (n : ℕ) [NeZero n] {K : Type*} [Field K] [NumberField K]
  [hK : _root_.IsCyclotomicExtension {n} ℚ K]

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

include hK in
/-- **One complex embedding detects the maximal real subfield of `ℚ(ζₙ)`.** An element lies in
the maximal real subfield as soon as its image under a single complex embedding is real. -/
theorem mem_maximalRealSubfield_iff_star_eq (φ : K →+* ℂ) (x : K) :
    x ∈ maximalRealSubfield K ↔ star (φ x) = φ x := by
  rw [← galEquivZMod_symm_neg_one_apply_eq_self_iff n, ← φ.injective.eq_iff,
    complexEmbedding_galEquivZMod_symm_neg_one_apply n, Complex.star_def]

variable (K) (R : Type*) [CommRing R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
  [IsAbelianGalois ℚ K]

/-- **The even characters cut out the maximal real subfield.** Under the correspondence between
intermediate fields of `ℚ(ζₙ) / ℚ` and groups of Dirichlet characters of level `n`, the group of
even characters corresponds to the maximal real subfield of `ℚ(ζₙ)`. -/
theorem toSubfield_intermediateFieldEquivSubgroupChar_symm_evenSubgroup :
    ((intermediateFieldEquivSubgroupChar n K R).symm (evenSubgroup R n)).toSubfield =
      maximalRealSubfield K := by
  set τ := (galEquivZMod n K).symm (-1)
  let F : IntermediateField ℚ K := (maximalRealSubfield K).toIntermediateField fun q ↦
    (galEquivZMod_symm_neg_one_apply_eq_self_iff n _).1 (τ.commutes q)
  have hF : F = fixedField (Subgroup.zpowers τ) := by
    ext x
    rw [mem_fixedField_zpowers_iff, galEquivZMod_symm_neg_one_apply_eq_self_iff, ← SetLike.mem_coe,
      Subfield.coe_toIntermediateField, SetLike.mem_coe]
  suffices intermediateFieldEquivSubgroupChar n K R F = evenSubgroup R n by
    rw [← this, OrderIso.symm_apply_apply, Subfield.toIntermediateField_toSubfield]
  ext χ
  -- The character `χ` is trivial on a group of automorphisms exactly when that group lies in the
  -- kernel of `χ ∘ galEquivZMod`; for the cyclic group `{1, τ}` this is the value `χ (-1)`.
  have hker (σ : Gal(K/ℚ)) : χ (galEquivZMod n K σ) = 1 ↔
      σ ∈ (χ.toUnitHom.comp (galEquivZMod n K).toMonoidHom).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← Units.val_eq_one,
      MulChar.coe_toUnitHom]
  simp_rw [mem_intermediateFieldEquivSubgroupChar_iff, hF, fixingSubgroup_fixedField, hker,
    ← IsConcreteLE.le_iff, Subgroup.zpowers_le, ← hker, τ, MulEquiv.apply_symm_apply, Units.val_neg,
    Units.val_one, mem_evenSubgroup_iff, _root_.DirichletCharacter.Even]

end TauCeti.IsCyclotomicExtension.Rat
