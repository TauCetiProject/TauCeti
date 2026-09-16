/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree

/-!
# Nonspecial divisors of degree `g` on prescribed rational places

A divisor `B` of a function field `F / k` of genus `g` is *nonspecial* when its index of
specialty `i(B) = ℓ(B) - deg B - 1 + g` vanishes.  Every divisor of degree at least `2g - 1` is
nonspecial, but nonspecial divisors also exist in the smallest degree the definition allows,
namely `g`, and they may be supported on any prescribed set of at least `g` rational places:

if `T` is a set of places of degree one with at least `g` elements, then some effective divisor
`B` with support in `T` has `deg B = g` and `ℓ(B) = 1`, equivalently `i(B) = 0`.

This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Proposition 1.6.12, over an
arbitrary exact constant field.

The divisor is built one place at a time from a canonical divisor `W`: at each stage the space
`L(W - B)` loses exactly one dimension when a suitable place of `T` is added to `B`.  Such a place
exists by `TauCeti.Divisor.exists_mem_dim_sub_ofPoint_lt`: if removing no single place of a finite
set `T` shrinks a nonzero space `L(D)`, then neither does removing all of `T`, and this is
impossible once `∑_{P ∈ T} deg P` exceeds `deg D + 1 - ℓ(D)`, because a nonzero Riemann–Roch space
has `ℓ ≤ deg + 1`.  After `g` steps `ℓ(W - B) = 0`, and Riemann–Roch gives `ℓ(B) = 1`.

## Main results

* `TauCeti.riemannRochSpace_sub_ofFinsetWithMultiplicity_eq`: if removing any single place of `T`
  leaves `L(D)` unchanged, so does removing all of `T` at once.
* `TauCeti.Divisor.exists_mem_dim_sub_ofPoint_lt`: a nonzero Riemann–Roch space drops when some
  place of a set of sufficiently large total degree is removed.
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

/-- If removing any single place of a finite set `T` leaves `L(D)` unchanged, then so does
removing all of `T` at once: `L(D - ∑_{P ∈ T} P) = L(D)`. -/
theorem riemannRochSpace_sub_ofFinsetWithMultiplicity_eq {D : Divisor k F} {T : Finset (Place k F)}
    (hT : ∀ P ∈ T, riemannRochSpace (D - WeilDivisor.ofPoint P) = riemannRochSpace D) :
    riemannRochSpace (D - WeilDivisor.ofFinsetWithMultiplicity T fun _ ↦ 1) =
      riemannRochSpace D := by
  classical
  refine le_antisymm (riemannRochSpace_mono (sub_le_self _ (WeilDivisor.isEffective_iff_zero_le.mp
    (WeilDivisor.isEffective_ofFinsetWithMultiplicity _ _)))) fun f hf ↦ ?_
  refine mem_riemannRochSpace_iff.mpr fun Q ↦ ?_
  by_cases hQ : Q ∈ T
  · rw [← hT Q hQ, mem_riemannRochSpace_iff] at hf
    simpa [hQ] using hf Q
  · simpa [hQ] using mem_riemannRochSpace_iff.mp hf Q

namespace Divisor

/-- **A nonzero Riemann–Roch space drops along a set of large degree.**  Over an exact constant
field, if `ℓ(D) > 0` and the places of a finite set `T` have total degree exceeding
`deg D + 1 - ℓ(D)`, then removing some place of `T` strictly shrinks `L(D)`. -/
theorem exists_mem_dim_sub_ofPoint_lt (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {D : Divisor k F} {T : Finset (Place k F)}
    (hD : 0 < dim D) (hdeg : degree D + 1 < dim D + ∑ P ∈ T, (P.degree : ℤ)) :
    ∃ P ∈ T, dim (D - WeilDivisor.ofPoint P) < dim D := by
  by_contra! h
  have := finiteDimensional_riemannRochSpace hF D
  set E : Divisor k F := D - WeilDivisor.ofFinsetWithMultiplicity T fun _ ↦ 1 with hE
  have heq : riemannRochSpace E = riemannRochSpace D :=
    riemannRochSpace_sub_ofFinsetWithMultiplicity_eq fun P hP ↦
      Submodule.eq_of_le_of_finrank_le
        (riemannRochSpace_mono (sub_le_self _ (WeilDivisor.isEffective_iff_zero_le.mp
          (WeilDivisor.isEffective_ofPoint P))))
        (by rw [← dim_def, ← dim_def]; exact h P hP)
  have hne : riemannRochSpace E ≠ ⊥ := by
    rw [heq, ← one_le_dim_iff_riemannRochSpace_ne_bot hF]
    exact hD
  have hle := dim_le_degree_add_one_of_riemannRochSpace_ne_bot hF hex hne
  rw [dim_def, heq, ← dim_def, hE, degree_sub,
    degree_eq_weightedDegree (WeilDivisor.ofFinsetWithMultiplicity T fun _ ↦ 1),
    WeilDivisor.weightedDegree_ofFinsetWithMultiplicity] at hle
  simp only [Nat.cast_one, one_mul] at hle
  omega

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
    obtain ⟨P, hPT, hlt⟩ := exists_mem_dim_sub_ofPoint_lt hF hex (D := W - B) (T := T)
      (by omega) (by rw [hsum, degree_sub, hdegW, hBdeg]; omega)
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
