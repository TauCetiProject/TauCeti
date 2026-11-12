/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.DiscriminantCharacter
public import TauCeti.Algebra.Module.ZLattice.RootLattice
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Reciprocity
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Milgram's formula for a positive definite even lattice

Let `L` be an even full lattice in a real inner product space `E` of even dimension `n = 2k`, with
discriminant group `A_L = L^∨ / L` and quadratic phase `e(q_L(γ)) = exp (π i ‖γ‖²)` on `A_L`
(`ZLattice.IsEven.discriminantQuadraticChar`). **Milgram's formula** evaluates the Gauss sum of
the discriminant form:

`∑_{γ ∈ A_L} e(q_L(γ)) = √|A_L| · e(n/8)`,

where `e(n/8) = i^k`. It is the case `a = c = 1` of the reciprocity law for the Gauss sums of `L`
(`ZLattice.IsEven.gaussSum_eq_mul_dualGaussSum`), whose left side is then `1`: the law reads
`1 = (covol L)⁻¹ i^k ∑_{γ ∈ A_L} e(-q_L(γ))`, and complex conjugation, together with
`covol L = √|A_L|`, turns it into the formula. The formula thus comes from the asymptotics of theta
series near the cusps, as in Milnor–Husemoller, and is independent of the finite arithmetic of the
rational model behind
`TauCeti.IntegralLattice.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg`.

Since `√|A_L| > 0`, the formula determines `n` modulo `8` from the discriminant form: `8 ∣ n`
exactly when the Gauss sum is the positive real number `√|A_L|`. For an even unimodular lattice of
even rank the group `A_L` is trivial and the sum is `1`, so `8 ∣ n`; the general statement for even
unimodular lattices of any rank is `ZLattice.IsEven.eight_dvd_finrank`. The root lattice `A₂`, of
rank `2` with `|A_L| = 3`, has Gauss sum `i √3`.

## Main statements

* `ZLattice.IsEven.sum_discriminantQuadraticChar`: Milgram's formula
  `∑_{γ ∈ A_L} e(q_L(γ)) = √|A_L| · i^k` for an even lattice of rank `2k`.
* `ZLattice.IsEven.eight_dvd_finrank_iff_sum_discriminantQuadraticChar_eq`: for an even lattice of
  even rank `n`, `8 ∣ n` if and only if `∑_{γ ∈ A_L} e(q_L(γ)) = √|A_L|`.
* `TauCeti.IntegralLattice.finsum_discriminantQuadraticChar_realModel_typeARootLattice_two`: the
  Gauss sum of the discriminant form of the root lattice `A₂` is `i √3`.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Springer, 1973, Appendix 4.
* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
-/

public section

open Complex Module
open scoped Pointwise Real

namespace ZLattice

namespace IsEven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ} (hL : IsEven L)
include hL

/-- **Milgram's formula.** If `L` is an even lattice and `dim E = 2k`, then
`∑_{γ ∈ L^∨/L} e(q_L(γ)) = √|L^∨/L| · i^k`, where `i^k = e(n/8)` for `n = 2k`. -/
theorem sum_discriminantQuadraticChar (hk : finrank ℝ E = 2 * k)
    [Fintype (DiscriminantGroup L)] :
    ∑ γ, hL.discriminantQuadraticChar γ = √(Nat.card (DiscriminantGroup L) : ℝ) * I ^ k := by
  -- The statement involves no measure; the reciprocity law uses the Borel volume.
  borelize E
  have := hL.isIntegral.finite_quotient_smul_submoduleOf_dual 1
  let _ : Fintype (dual L ⧸ (((1 : ℕ) : ℝ) • L).submoduleOf (dual L)) := Fintype.ofFinite _
  have h := gaussSum_eq_mul_dualGaussSum hL hk 1 1
  rw [gaussSum_one] at h
  -- At `a = c = 1` the law reads `1 = (covol L)⁻¹ i^k ∑_γ e(-q_L(γ))`; conjugate it.
  have h' : dualGaussSum L hL (-1) 1 = covolume L * (-I) ^ k := by
    rw [Nat.cast_one, div_one, one_pow, one_mul] at h
    have hcov : (covolume L : ℂ) ≠ 0 := ofReal_ne_zero.mpr (covolume_pos L).ne'
    have hI : I ^ k * (-I) ^ k = 1 := by rw [← mul_pow]; simp
    calc _ = (covolume L : ℂ) * (-I) ^ k * ((covolume L : ℂ)⁻¹ * I ^ k *
          dualGaussSum L hL (-1) 1) := by
          field_simp
          linear_combination (-(dualGaussSum L hL (-1) 1)) * hI
      _ = _ := by push_cast at h; rw [← h, mul_one]
  have hconj := conj_dualGaussSum hL (-1) 1
  rw [neg_neg, h', map_mul, conj_ofReal, map_pow, map_neg, conj_I, neg_neg] at hconj
  -- On a representative `v ∈ L^∨`, `e(q_L(v)) = exp (π i ‖v‖²)` is the summand of `G_{L^∨}(1, 1)`.
  have hq (v : dual L) : hL.discriminantQuadraticChar (Submodule.Quotient.mk v) =
      cexp (2 * π * I * (((1 : ℤ) * ‖(v : E)‖ ^ 2 / 2 : ℝ) : ℂ)) := by
    rw [discriminantQuadraticChar_mk]
    congr 1
    push_cast
    ring
  rw [← dualGaussSum_one hL 1 _ hq, ← hconj, hL.isIntegral.covolume_eq_sqrt_card_discriminantGroup]

/-- **The rank modulo `8` from Milgram's formula.** For an even lattice of even rank `n`, `8 ∣ n`
if and only if the Gauss sum `∑_{γ ∈ L^∨/L} e(q_L(γ))` is the positive real number `√|L^∨/L|`. -/
theorem eight_dvd_finrank_iff_sum_discriminantQuadraticChar_eq (hn : Even (finrank ℝ E))
    [Fintype (DiscriminantGroup L)] :
    8 ∣ finrank ℝ E ↔
      ∑ γ, hL.discriminantQuadraticChar γ = √(Nat.card (DiscriminantGroup L) : ℝ) := by
  obtain ⟨k, hk⟩ := hn
  rw [hL.sum_discriminantQuadraticChar (k := k) (by omega)]
  have hA : (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)).ne'
  rw [mul_eq_left₀ hA, isPrimitiveRoot_I.pow_eq_one_iff_dvd, hk]
  omega

end IsEven

end ZLattice

namespace TauCeti.IntegralLattice

/-- **Milgram's formula for `A₂`.** The Gauss sum of the discriminant form of the real model of
the root lattice `A₂`, of rank `2` and determinant `3`, is `i √3`. The discriminant group is
finite, so the `finsum` is its finite sum. -/
theorem finsum_discriminantQuadraticChar_realModel_typeARootLattice_two :
    ∑ᶠ γ, ((isEven_realModel_iff _ (isPosDef_typeARootLattice 2)).mpr
      (isEven_typeARootLattice 2)).discriminantQuadraticChar γ = √3 * I := by
  -- Finiteness of the discriminant group is proved through the covolume, for the Borel volume.
  borelize ((typeARootLattice 2).RealModelSpace (isPosDef_typeARootLattice 2))
  have := (isIntegral_realModel _ (isPosDef_typeARootLattice 2)).finite_discriminantGroup
  let _ := Fintype.ofFinite
    (ZLattice.DiscriminantGroup ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)))
  rw [finsum_eq_sum_of_fintype, ZLattice.IsEven.sum_discriminantQuadraticChar _ (k := 1)
      (by simp [RealModelSpace.finrank_eq, finrank_carrier]),
    natCard_discriminantGroup_realModel_typeARootLattice_two, pow_one]
  norm_num

end TauCeti.IntegralLattice
