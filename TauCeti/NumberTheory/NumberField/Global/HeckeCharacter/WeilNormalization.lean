/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Splitting
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.PrincipalFinite
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Principal values of norm-normalized splitting characters

For a splitting character `υ` of a CM field, the normalization `υ |·|⁻¹/²` has
archimedean components `z ↦ 1 / conj z` in the coordinates of the CM type. On the finite
part of a diagonal idele it therefore evaluates to the product of the conjugate embeddings.
This supplies the principal-value formula used to compute powers of its values on finite ideles.

The normalization and exponent convention are those of `New.WeilData.chiFinAlgebraic` in
lsernau/grh-lean, `grh/src/Lib/ClassField/HeckeCharacter/AlgebraicValues.lean` (`72fead1`).
-/

public section

open IsDedekindDomain NumberField NumberField.IsCMField NumberField.InfinitePlace
open scoped NumberField ComplexConjugate

namespace TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {υ : HeckeCharacter E} {Φ : CMType E}

/-- Dividing a splitting character by the square root of the idele norm gives the inverse
conjugate of the CM-type coordinate at each infinite place. -/
theorem infiniteComponent_mul_normPow_neg_half (hυ : υ.IsSplitting Φ)
    (w : InfinitePlace E) (u : w.Completionˣ) :
    ((υ * normPow E (-(2⁻¹ : ℂ))).infiniteComponent w u : ℂ) =
      (conj (Φ.completionEmbedding w u))⁻¹ := by
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  rw [infiniteComponent_mul, ContinuousMonoidHom.mul_apply, Units.val_mul,
    hυ.infiniteComponent_apply, coe_infiniteComponent_normPow_apply,
    completionNormalizedAbsValue_of_isComplex _ hw, Complex.ofReal_pow,
    ofReal_pow_cpow (norm_nonneg _)]
  norm_num only [Nat.cast_ofNat, mul_neg, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_neg_one]
  rw [← Φ.norm_completionEmbedding w (u : w.Completion), ← div_eq_mul_inv, div_div, ← sq,
    ← Complex.mul_conj']
  exact div_mul_cancel_left₀ ((map_ne_zero _).mpr u.ne_zero) _

/-- The normalized splitting character on a principal finite idele is the product of the CM
embeddings evaluated at the conjugate of its generator. -/
theorem mul_normPow_neg_half_apply_ofFiniteIdele_unitEmbedding
    (hυ : υ.IsSplitting Φ) (x : Eˣ) :
    ((υ * normPow E (-(2⁻¹ : ℂ)))
      (IdeleGroup.ofFiniteIdele (𝓞 E) E (FiniteAdeleRing.unitEmbedding (𝓞 E) E x)) : ℂ) =
      ∏ w : InfinitePlace E, Φ.embedding w (complexConj E (x : E)) := by
  rw [apply_ofFiniteIdele_unitEmbedding, Units.val_inv_eq_inv_val, Units.coe_prod]
  simp only [← Finset.prod_inv_distrib, hυ.infiniteComponent_mul_normPow_neg_half, inv_inv,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    CMType.completionEmbedding_algebraMap, complexEmbedding_complexConj]

end TauCeti.GlobalNumberFields.HeckeCharacter.IsSplitting
