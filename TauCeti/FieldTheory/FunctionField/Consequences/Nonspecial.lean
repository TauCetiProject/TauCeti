/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor

/-!
# Nonspecial divisors of degree `g` on prescribed rational places

A divisor `B` of a function field `F / k` of genus `g` is *nonspecial* when its index of
specialty `i(B) = ℓ(B) - deg B - 1 + g` vanishes.  Every divisor of degree at least `2g - 1` is
nonspecial, and an effective nonspecial divisor has degree at least `g`.  This file shows that
this smallest degree is attained on any prescribed set of at least `g` rational places:

if `T` is a set of places of degree one with at least `g` elements, then some effective divisor
`B` with support in `T` has `deg B = g` and `ℓ(B) = 1`, equivalently `i(B) = 0`.

This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Proposition 1.6.12, over an
arbitrary exact constant field.

## Main results

* `TauCeti.Divisor.exists_degree_eq_genus_dim_eq_one`: **nonspecial divisors of degree `g`**
  supported on any prescribed set of at least `g` rational places (Stichtenoth,
  Proposition 1.6.12).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 1.6.10 and Proposition 1.6.12.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-- The inductive construction behind `exists_degree_eq_genus_dim_eq_one`: for a Riemann–Roch
divisor `W` and every `j ≤ g`, some effective `B` supported on `T` has degree `j` and
`ℓ(W - B) = g - j`. -/
private theorem exists_degree_eq_dim_sub_add_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {W : Divisor k F}
    (hW : W.IsRiemannRochDivisor (genus k F)) {T : Finset (Place k F)}
    (hT : ∀ P ∈ T, P.degree = 1) (hcard : genus k F ≤ T.card) :
    ∀ j ≤ genus k F, ∃ B : Divisor k F, 0 ≤ B ∧ B.support ⊆ T ∧ degree B = j ∧
      dim (W - B) + j = genus k F := by
  intro j
  induction j with
  | zero => exact fun _ ↦ ⟨0, le_rfl, by simp, by simp, by simpa using hW.dim_eq hF hex⟩
  | succ j ih =>
    classical
    intro hj
    obtain ⟨B, hB0, hBT, hBdeg, hBdim⟩ := ih (by omega)
    have hdegW := hW.degree_eq hF hex
    have hsum : ∑ P ∈ T, (P.degree : ℤ) = T.card := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      exact Finset.sum_congr rfl fun P hP ↦ by simp [hT P hP]
    obtain ⟨P, hPT, hlt⟩ := exists_mem_dim_sub_ofPoint_lt hF (D := W - B) (T := T)
      (by omega) (by
        rw [hsum, degree_sub, hdegW, hBdeg,
          isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one.mp hex]
        omega)
    have hP0 : 0 ≤ (WeilDivisor.ofPoint P : Divisor k F) :=
      WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)
    have hle := dim_le_dim_add_degree_sub hF (sub_le_self (W - B) hP0)
    simp only [degree_sub, degree_ofPoint, hT P hPT] at hle
    refine ⟨B + WeilDivisor.ofPoint P, add_nonneg hB0 hP0, ?_, ?_, ?_⟩
    · refine Finsupp.support_add.trans (Finset.union_subset hBT ?_)
      simpa using hPT
    · simp [hBdeg, hT P hPT]
    · rw [← sub_sub]
      push_cast at hle ⊢
      omega

/-- **Nonspecial divisors of degree `g` on prescribed rational places** (Stichtenoth,
Proposition 1.6.12).  Let `F / k` be a function field of genus `g` with exact constant field, and
let `T` be a set of places of degree one with at least `g` elements.  Then there is an effective
divisor `B` supported in `T` with `deg B = g` and `ℓ(B) = 1`; equivalently, `B` is nonspecial,
`i(B) = 0`. -/
theorem exists_degree_eq_genus_dim_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {T : Set (Place k F)} (hT : ∀ P ∈ T, P.degree = 1)
    (hcard : (genus k F : ℕ∞) ≤ T.encard) :
    ∃ B : Divisor k F, 0 ≤ B ∧ ↑B.support ⊆ T ∧ degree B = genus k F ∧ dim B = 1 ∧
      indexOfSpecialty B = 0 := by
  obtain ⟨S, hST, hS⟩ := Set.exists_subset_encard_eq hcard
  have hSfin : S.Finite := Set.finite_of_encard_eq_coe hS
  have hScard : genus k F ≤ hSfin.toFinset.card := by
    rw [hSfin.encard_eq_coe_toFinset_card, Nat.cast_inj] at hS
    exact hS.ge
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  obtain ⟨B, hB0, hBS, hBdeg, hBdim⟩ := exists_degree_eq_dim_sub_add_eq hF hex hW
    (fun P hP ↦ hT P (hST (hSfin.mem_toFinset.mp hP))) hScard _ le_rfl
  have hRR := isRiemannRochDivisor_iff.mp hW B
  have hdim : dim B = 1 := by omega
  refine ⟨B, hB0, fun P hP ↦ hST (hSfin.mem_toFinset.mp (hBS hP)), hBdeg, hdim, ?_⟩
  rw [indexOfSpecialty_def, hdim, hBdeg]
  omega

end Divisor

end TauCeti
