/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.LocalRing.HilbertSamuel

/-!
# Examples of local quotient Hilbert–Samuel functions

At a non-rational closed point such as `(X ^ 2 + 1)` in `ℚ[X]`, measuring length over the local
ring `A = Localization.AtPrime (Ideal.span {X ^ 2 + 1})` normalizes
`TauCeti.localQuotientHilbertSamuel A ⊥ 0` to `1`, whereas the `ℚ`-vector space length of
`A ⧸ IsLocalRing.maximalIdeal A` equals the residue-field degree `2`.
-/

open Polynomial TauCeti

/-- At the degree-two closed point `(X ^ 2 + 1)` of `ℚ[X]`, the local Hilbert–Samuel value `H(0)` is
`1` by local length, even though the quotient `A ⧸ 𝔪` has `ℚ`-dimension `2`. -/
example : ∃ (p : ℚ[X]) (hmax : (Ideal.span {p}).IsMaximal),
    letI : (Ideal.span {p}).IsMaximal := hmax
    let A := Localization.AtPrime (Ideal.span {p})
    localQuotientHilbertSamuel A ⊥ 0 = 1 ∧
      Module.length ℚ (A ⧸ IsLocalRing.maximalIdeal A) = 2 := by
  let p : ℚ[X] := X ^ 2 + 1
  have hp_monic : p.Monic := monic_X_pow_add_C 1 two_ne_zero
  have hp_deg : p.natDegree = 2 := by simp [p]
  have hp_irr : Irreducible p := by
    rw [hp_monic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_iff_forall_notMem.mpr fun q hq ↦ ?_
    have hroot : q ^ 2 + 1 = 0 := by simpa [p, IsRoot.def] using isRoot_of_mem_roots hq
    linarith [sq_nonneg q]
  have hmax : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp_irr
  refine ⟨p, hmax, localQuotientHilbertSamuel_bot_zero, ?_⟩
  let A := Localization.AtPrime (Ideal.span {p})
  have : Module.Finite ℚ (ℚ[X] ⧸ Ideal.span {p}) := (AdjoinRoot.powerBasis hp_irr.ne_zero).finite
  have hres : Module.length ℚ (IsLocalRing.ResidueField A) = 2 := by
    rw [MaximalSpectrum.length_residueField_localization_eq ⟨Ideal.span {p}, hmax⟩,
      Module.length_eq_finrank, finrank_quotient_span_eq_natDegree, hp_deg]
    norm_num
  have hquot : (A ⧸ ((⊥ : Ideal A) ⊔ IsLocalRing.maximalIdeal A ^ (0 + 1))) ≃ₐ[ℚ]
      (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.quotientEquivAlgOfEq ℚ (by simp)
  rw [← hquot.toLinearEquiv.length_eq,
    length_quotient_sup_maximalIdeal_pow_eq_mul_length_residueField ℚ A ⊥ 0,
    localQuotientHilbertSamuel_bot_zero, one_mul, hres]
