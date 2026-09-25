/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Basic
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Analysis.Normed.Field.CompactGroup
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Compact
import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# The shift and the unitary part of a Hecke character

For a Hecke character `χ` of a number field `K`, the absolute value `|χ|` is a continuous
homomorphism from the idele class group `C_K` to `ℝ>0`.  It is trivial on the compact norm-one
subgroup `C_K¹`, so it factors through the idele class norm `‖·‖ : C_K → ℝ>0`, and a continuous
endomorphism of `ℝ>0` is a real power.  Hence there is a unique **real** number `σ`, the **shift**
of `χ`, with `|χ(c)| = ‖c‖ ^ σ` for every idele class `c`.  The shift is real by construction: a
complex exponent `s` would only be determined up to the imaginary part, since `‖·‖ ^ (i t)` is
unitary for every real `t`.

Twisting `χ` by `‖·‖ ^ (-σ)` gives the **unitary part** of `χ`, a Hecke character with values of
absolute value `1`, and `χ` is its unitary part times `‖·‖ ^ σ`.  Characters of finite order, in
particular those coming from ray class characters, have shift `0`.

## Main definitions

* `TauCeti.GlobalNumberFields.HeckeCharacter.normPow`: the Hecke character `c ↦ ‖c‖ ^ s` for a
  complex exponent `s`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.shift`: the real exponent `σ` with `|χ| = ‖·‖ ^ σ`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.unitaryPart`: the unitary Hecke character
  `χ · ‖·‖ ^ (-σ)`.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.norm_apply_eq_rpow_shift`: `|χ(c)| = ‖c‖ ^ σ`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.shift_eq_of_norm_apply_eq_rpow`: the shift is the
  only real exponent with this property.
* `TauCeti.GlobalNumberFields.HeckeCharacter.shift_eq_zero_iff`: the shift vanishes exactly for
  unitary characters.
* `TauCeti.GlobalNumberFields.HeckeCharacter.norm_unitaryPart`: the unitary part takes values of
  absolute value `1`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.unitaryPart_mul_normPow_shift`: a Hecke character is
  its unitary part times `‖·‖ ^ σ`, and `unitaryPart_mul_normPow` shows this decomposition is
  unique.
* `TauCeti.GlobalNumberFields.HeckeCharacter.shift_ofRayClassCharacter`: characters coming from
  ray class characters have shift `0`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.mixedEmbedding Module
open scoped NNReal

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

/-! ### The norm characters `‖·‖ ^ s` -/

/-- The complex power `‖c‖ ^ s` of the idele class norm, as a homomorphism to `ℂ`. -/
private def normPowAux (s : ℂ) : IdeleClassGroup (𝓞 K) K →* ℂ where
  toFun c := (((ideleClassNorm c : ℝ≥0) : ℝ) : ℂ) ^ s
  map_one' := by simp
  map_mul' c d := by
    simp only [map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (coe_ideleClassNorm_pos c).le
      (coe_ideleClassNorm_pos d).le s

variable (K) in
/-- **The norm character** `c ↦ ‖c‖ ^ s` of the idele class group, for a complex exponent `s`.
It is unitary exactly when `s` is purely imaginary. -/
def normPow (s : ℂ) : HeckeCharacter K where
  toMonoidHom := (normPowAux s).toHomUnits
  continuous_toFun := by
    refine Units.isEmbedding_val₀.continuous_iff.mpr ?_
    exact (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (Units.continuous_val.comp continuous_ideleClassNorm))).cpow continuous_const
      fun c ↦ Complex.ofReal_mem_slitPlane.mpr (coe_ideleClassNorm_pos c)

/-- The value of the norm character `‖·‖ ^ s` at an idele class `c` is `‖c‖ ^ s`. -/
@[simp]
theorem normPow_apply (s : ℂ) (c : IdeleClassGroup (𝓞 K) K) :
    ((normPow K s c : ℂˣ) : ℂ) = (((ideleClassNorm c : ℝ≥0) : ℝ) : ℂ) ^ s :=
  by
    -- Expose the monoid homomorphism stored in the continuous homomorphism.
    change ((normPowAux s).toHomUnits c : ℂ) = normPowAux s c
    exact MonoidHom.coe_toHomUnits (normPowAux s) c

/-- The absolute value of `‖c‖ ^ s` is `‖c‖ ^ Re s`. -/
theorem norm_normPow_apply (s : ℂ) (c : IdeleClassGroup (𝓞 K) K) :
    ‖((normPow K s c : ℂˣ) : ℂ)‖ = ((ideleClassNorm c : ℝ≥0) : ℝ) ^ s.re := by
  rw [normPow_apply, Complex.norm_cpow_eq_rpow_re_of_pos (coe_ideleClassNorm_pos c)]

/-- The zeroth power of the idele class norm is the trivial character. -/
@[simp]
theorem normPow_zero : normPow K 0 = 1 :=
  ContinuousMonoidHom.ext fun c ↦ Units.ext <| by simp

/-- Norm characters multiply by adding exponents. -/
theorem normPow_add (s t : ℂ) : normPow K (s + t) = normPow K s * normPow K t := by
  refine ContinuousMonoidHom.ext fun c ↦ Units.ext ?_
  simp only [ContinuousMonoidHom.mul_apply, Units.val_mul, normPow_apply]
  exact Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (coe_ideleClassNorm_pos c).ne')

/-- The norm character with the negated exponent is the inverse character. -/
theorem normPow_neg (s : ℂ) : normPow K (-s) = (normPow K s)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by rw [← normPow_add, neg_add_cancel, normPow_zero]

/-! ### The shift -/

/-- The idele with infinite component `exp t` at every infinite place and finite component `1`;
its idele norm is `exp t ^ [K : ℚ]`. -/
private def diagonalIdele (t : ℝ) : IdeleGroup (𝓞 K) K :=
  Units.map ((MonoidHom.inl _ _).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toMonoidHom.comp
      (algebraMap ℝ (mixedSpace K)).toMonoidHom)) (Units.mk0 (Real.exp t) (Real.exp_pos t).ne')

private lemma coe_diagonalIdele (t : ℝ) :
    ((diagonalIdele (K := K) t : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) =
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
        (algebraMap ℝ (mixedSpace K) (Real.exp t)), 1) :=
  by
    unfold diagonalIdele
    -- An idele is a unit of the adele product; expose that product to simplify `Units.map`.
    change ((Units.map _ _ : (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)ˣ) :
      InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) = _
    simp only [Units.coe_map, MonoidHom.comp_apply, MonoidHom.inl_apply, Units.val_mk0]
    -- The remaining coercion of the mixed-space ring equivalence is definitional.
    rfl

private lemma diagonalIdele_add (t u : ℝ) :
    diagonalIdele (K := K) (t + u) = diagonalIdele t * diagonalIdele u := by
  rw [diagonalIdele, diagonalIdele, diagonalIdele, ← map_mul]
  congr 1
  exact Units.ext (by simp [Real.exp_add])

private lemma diagonalIdele_zero : diagonalIdele (K := K) 0 = 1 := by
  ext1
  simp [diagonalIdele]

private lemma continuous_diagonalIdele : Continuous (diagonalIdele (K := K)) := by
  have hc : Continuous fun t : ℝ ↦
      ((diagonalIdele (K := K) t : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) := by
    simp only [coe_diagonalIdele]
    exact ((InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K).comp
      ((continuous_algebraMap ℝ (mixedSpace K)).comp Real.continuous_exp)).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hc, ?_⟩
  have hinv (t : ℝ) : (diagonalIdele (K := K) t)⁻¹ = diagonalIdele (-t) :=
    (eq_inv_of_mul_eq_one_left <| by
      rw [← diagonalIdele_add, neg_add_cancel, diagonalIdele_zero]).symm
  simp only [hinv]
  exact hc.comp continuous_neg

private lemma coe_ideleNorm_diagonalIdele (t : ℝ) :
    ((ideleNorm (diagonalIdele (K := K) t) : ℝ≥0) : ℝ) = Real.exp (finrank ℚ K * t) := by
  have h1 : IdeleGroup.toFiniteIdele (𝓞 K) K (diagonalIdele t) = 1 :=
    Units.ext (by simp [IdeleGroup.coe_toFiniteIdele, coe_diagonalIdele])
  rw [← mixedEmbedding_norm_eq_ideleNorm (h1 ▸ one_mem _), coe_diagonalIdele,
    RingEquiv.apply_symm_apply, Algebra.algebraMap_eq_smul_one, mixedEmbedding.norm_smul,
    map_one, mul_one, abs_of_pos (Real.exp_pos t), ← Real.exp_nat_mul]

/-- The absolute value of a Hecke character is a real power of the idele class norm. -/
private theorem exists_norm_apply_eq_rpow (χ : HeckeCharacter K) :
    ∃ σ : ℝ, ∀ c, ‖(χ c : ℂ)‖ = ((ideleClassNorm c : ℝ≥0) : ℝ) ^ σ := by
  -- `|χ|` is trivial on the compact norm-one subgroup.
  have hone (c : IdeleClassGroup (𝓞 K) K) (hc : c ∈ IdeleClassGroup.normOne K) :
      ‖(χ c : ℂ)‖ = 1 :=
    (χ.comp (ContinuousMonoidHom.subgroupSubtype
      (IdeleClassGroup.normOne K))).norm_apply_eq_one_of_compactSpace ⟨c, hc⟩
  -- Along the diagonal section `t ↦ diagonalIdele t`, `log |χ|` is a continuous additive map
  -- `ℝ → ℝ`, hence linear.
  let e : ℝ → IdeleClassGroup (𝓞 K) K := fun t ↦ ((diagonalIdele t : IdeleGroup (𝓞 K) K) :
    IdeleClassGroup (𝓞 K) K)
  have hχe (t : ℝ) : (χ (e t) : ℂ) ≠ 0 := (χ (e t)).ne_zero
  let ψ : ℝ →+ ℝ :=
    { toFun t := Real.log ‖(χ (e t) : ℂ)‖
      map_zero' := by
        simp [e, diagonalIdele_zero]
      map_add' t u := by
        simp only [e, diagonalIdele_add, QuotientGroup.mk_mul, map_mul, Units.val_mul, norm_mul]
        exact Real.log_mul (norm_ne_zero_iff.mpr (hχe t)) (norm_ne_zero_iff.mpr (hχe u)) }
  have hψ : Continuous ψ :=
    Real.continuous_log.comp ((continuous_norm.comp (Units.continuous_val.comp
      (χ.continuous.comp ((QuotientGroup.continuous_mk).comp continuous_diagonalIdele)))).subtype_mk
      fun t ↦ norm_ne_zero_iff.mpr (hχe t))
  have hψ_apply (t : ℝ) : ψ t = Real.log ‖(χ (e t) : ℂ)‖ := rfl
  have hlin (t : ℝ) : ψ t = t * ψ 1 := by
    simpa using map_real_smul ψ hψ t 1
  have hn : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  refine ⟨ψ 1 / finrank ℚ K, fun c ↦ ?_⟩
  -- Compare `c` with the point of the diagonal section of the same norm.
  set t := Real.log ((ideleClassNorm c : ℝ≥0) : ℝ) / finrank ℚ K
  have hnorm : ((ideleClassNorm (e t) : ℝ≥0) : ℝ) = ((ideleClassNorm c : ℝ≥0) : ℝ) := by
    rw [ideleClassNorm_mk, coe_ideleNorm_diagonalIdele, mul_div_cancel₀ _ hn.ne',
      Real.exp_log (coe_ideleClassNorm_pos c)]
  have hmem : c * (e t)⁻¹ ∈ IdeleClassGroup.normOne K := by
    rw [IdeleClassGroup.mem_normOne_iff, map_mul, map_inv, mul_inv_eq_one]
    exact Units.ext (NNReal.eq hnorm.symm)
  have hc : ‖(χ c : ℂ)‖ = ‖(χ (e t) : ℂ)‖ := by
    have := hone _ hmem
    rwa [map_mul, map_inv, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
      mul_inv_eq_one₀ (norm_ne_zero_iff.mpr (hχe t))] at this
  rw [hc, ← Real.exp_log (norm_pos_iff.mpr (hχe t)),
    Real.rpow_def_of_pos (coe_ideleClassNorm_pos c)]
  rw [← hψ_apply, hlin t]
  congr 1
  simp only [t]
  field_simp

/-- **The shift of a Hecke character**: the unique real number `σ` with `|χ(c)| = ‖c‖ ^ σ` for
every idele class `c`. -/
def shift (χ : HeckeCharacter K) : ℝ :=
  (exists_norm_apply_eq_rpow χ).choose

/-- **The absolute value of a Hecke character is the shift-th power of the idele class norm.** -/
@[simp]
theorem norm_apply_eq_rpow_shift (χ : HeckeCharacter K) (c : IdeleClassGroup (𝓞 K) K) :
    ‖(χ c : ℂ)‖ = ((ideleClassNorm c : ℝ≥0) : ℝ) ^ χ.shift :=
  (exists_norm_apply_eq_rpow χ).choose_spec c

/-- **Uniqueness of the shift**: if `|χ| = ‖·‖ ^ σ` for a real number `σ`, then `σ` is the shift
of `χ`. -/
theorem shift_eq_of_norm_apply_eq_rpow {χ : HeckeCharacter K} {σ : ℝ}
    (h : ∀ c, ‖(χ c : ℂ)‖ = ((ideleClassNorm c : ℝ≥0) : ℝ) ^ σ) : χ.shift = σ := by
  obtain ⟨c, hc⟩ := ideleClassNorm_surjective (K := K) (Units.mk0 2 two_ne_zero)
  have h2 : ((ideleClassNorm c : ℝ≥0) : ℝ) = 2 := by simp [hc]
  have := (norm_apply_eq_rpow_shift χ c).symm.trans (h c)
  rwa [h2, Real.rpow_right_inj two_pos (by norm_num)] at this

/-- The shift of the norm character `‖·‖ ^ s` is the real part of `s`. -/
@[simp]
theorem shift_normPow (s : ℂ) : (normPow K s).shift = s.re :=
  shift_eq_of_norm_apply_eq_rpow (norm_normPow_apply s)

/-- The trivial character has shift `0`. -/
@[simp]
theorem shift_one : (1 : HeckeCharacter K).shift = 0 :=
  shift_eq_of_norm_apply_eq_rpow fun c ↦ by simp

/-- Shifts add under multiplication of Hecke characters. -/
@[simp]
theorem shift_mul (χ ψ : HeckeCharacter K) : (χ * ψ).shift = χ.shift + ψ.shift :=
  shift_eq_of_norm_apply_eq_rpow fun c ↦ by
    rw [ContinuousMonoidHom.mul_apply, Units.val_mul, norm_mul, norm_apply_eq_rpow_shift,
      norm_apply_eq_rpow_shift, ← Real.rpow_add (coe_ideleClassNorm_pos c)]

/-- The inverse of a Hecke character has the negated shift. -/
@[simp]
theorem shift_inv (χ : HeckeCharacter K) : χ⁻¹.shift = -χ.shift := by
  rw [eq_neg_iff_add_eq_zero, ← shift_mul, inv_mul_cancel, shift_one]

/-- **The shift vanishes exactly for unitary Hecke characters.** -/
theorem shift_eq_zero_iff (χ : HeckeCharacter K) :
    χ.shift = 0 ↔ ∀ c, ‖(χ c : ℂ)‖ = 1 := by
  refine ⟨fun h c ↦ by rw [norm_apply_eq_rpow_shift, h, Real.rpow_zero], fun h ↦ ?_⟩
  exact shift_eq_of_norm_apply_eq_rpow fun c ↦ by rw [h, Real.rpow_zero]

/-- **A Hecke character of finite order has shift `0`**: its values are roots of unity. -/
theorem shift_eq_zero_of_isOfFinOrder {χ : HeckeCharacter K} (hχ : IsOfFinOrder χ) :
    χ.shift = 0 := by
  obtain ⟨n, hn, hχn⟩ := hχ.exists_pow_eq_one
  refine (shift_eq_zero_iff χ).mpr fun c ↦ Complex.norm_eq_one_of_pow_eq_one ?_ hn.ne'
  rw [← Units.val_pow_eq_pow_val, ← ContinuousMonoidHom.pow_apply, hχn,
    ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one]

/-- **Hecke characters coming from ray class characters have shift `0`.** -/
@[simp]
theorem shift_ofRayClassCharacter {𝔪 : Modulus K} (η : RayClassCharacter 𝔪) :
    (ofRayClassCharacter 𝔪 η).shift = 0 :=
  shift_eq_zero_of_isOfFinOrder (isOfFinOrder_ofRayClassCharacter η)

/-! ### The unitary part -/

/-- **The unitary part of a Hecke character** `χ`: the twist `χ · ‖·‖ ^ (-σ)` by the inverse power
of the idele class norm, where `σ` is the shift of `χ`.  It takes values of absolute value `1`. -/
def unitaryPart (χ : HeckeCharacter K) : HeckeCharacter K :=
  χ * normPow K (-χ.shift)

/-- The unitary part of `χ` is `χ` times the norm character with exponent `-σ`. -/
theorem unitaryPart_def (χ : HeckeCharacter K) :
    χ.unitaryPart = χ * normPow K (-χ.shift) :=
  (rfl)

/-- The value of the unitary part of `χ` at `c` is `χ(c) · ‖c‖ ^ (-σ)`. -/
@[simp]
theorem unitaryPart_apply (χ : HeckeCharacter K) (c : IdeleClassGroup (𝓞 K) K) :
    ((χ.unitaryPart c : ℂˣ) : ℂ) =
      (χ c : ℂ) * (((ideleClassNorm c : ℝ≥0) : ℝ) : ℂ) ^ (-(χ.shift : ℂ)) := by
  rw [unitaryPart_def, ContinuousMonoidHom.mul_apply, Units.val_mul, normPow_apply]

/-- The unitary part of a Hecke character has shift `0`. -/
@[simp]
theorem shift_unitaryPart (χ : HeckeCharacter K) : χ.unitaryPart.shift = 0 := by
  simp [unitaryPart_def]

/-- **The unitary part of a Hecke character takes values of absolute value `1`.** -/
theorem norm_unitaryPart (χ : HeckeCharacter K) (c : IdeleClassGroup (𝓞 K) K) :
    ‖((χ.unitaryPart c : ℂˣ) : ℂ)‖ = 1 :=
  (shift_eq_zero_iff _).mp (shift_unitaryPart χ) c

/-- **The unitary decomposition**: a Hecke character is its unitary part times the shift-th power
of the idele class norm. -/
@[simp]
theorem unitaryPart_mul_normPow_shift (χ : HeckeCharacter K) :
    χ.unitaryPart * normPow K χ.shift = χ := by
  rw [unitaryPart_def, mul_assoc χ, ← normPow_add, neg_add_cancel, normPow_zero, mul_one χ]

/-- The unitary part of a product is the product of the unitary parts. -/
@[simp]
theorem unitaryPart_mul (χ ψ : HeckeCharacter K) :
    (χ * ψ).unitaryPart = χ.unitaryPart * ψ.unitaryPart := by
  simp only [unitaryPart_def, shift_mul, Complex.ofReal_add, neg_add_rev, normPow_add]
  rw [mul_comm (normPow K (-ψ.shift)) (normPow K (-χ.shift))]
  exact mul_mul_mul_comm χ ψ (normPow K (-χ.shift)) (normPow K (-ψ.shift))

/-- The unitary part of the trivial character is trivial. -/
@[simp]
theorem unitaryPart_one : (1 : HeckeCharacter K).unitaryPart = 1 := by
  rw [unitaryPart_def, shift_one, Complex.ofReal_zero, neg_zero, normPow_zero]
  exact mul_one (1 : HeckeCharacter K)

/-- The unitary part of an inverse is the inverse of the unitary part. -/
@[simp]
theorem unitaryPart_inv (χ : HeckeCharacter K) : χ⁻¹.unitaryPart = χ.unitaryPart⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← unitaryPart_mul, inv_mul_cancel, unitaryPart_one]

/-- Taking the unitary part twice has the same result as taking it once. -/
@[simp]
theorem unitaryPart_unitaryPart (χ : HeckeCharacter K) : χ.unitaryPart.unitaryPart =
    χ.unitaryPart := by
  rw [unitaryPart_def, shift_unitaryPart, Complex.ofReal_zero, neg_zero, normPow_zero]
  exact mul_one (χ.unitaryPart)

/-- **Uniqueness of the unitary decomposition**: the unitary part of `ψ · ‖·‖ ^ σ`, for a unitary
Hecke character `ψ` and a real number `σ`, is `ψ`. -/
theorem unitaryPart_mul_normPow {ψ : HeckeCharacter K} (hψ : ψ.shift = 0) (σ : ℝ) :
    (ψ * normPow K σ).unitaryPart = ψ := by
  rw [unitaryPart_def, shift_mul, shift_normPow, hψ, zero_add, Complex.ofReal_re, mul_assoc ψ,
    ← normPow_add, add_neg_cancel, normPow_zero, mul_one ψ]

/-- A Hecke character is its own unitary part exactly when its shift vanishes. -/
theorem unitaryPart_eq_self_iff (χ : HeckeCharacter K) : χ.unitaryPart = χ ↔ χ.shift = 0 := by
  refine ⟨fun h ↦ h ▸ shift_unitaryPart χ, fun h ↦ ?_⟩
  have := unitaryPart_mul_normPow h 0
  rwa [Complex.ofReal_zero, normPow_zero, mul_one χ] at this

end HeckeCharacter

end TauCeti.GlobalNumberFields
