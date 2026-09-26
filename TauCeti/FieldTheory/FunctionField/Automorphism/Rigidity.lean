/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Automorphism

/-!
# Rigidity of automorphisms of a function field

Let `F / k` be a function field of genus `g` with exact constant field `k`. An automorphism
`σ ∈ Aut(F / k)` that fixes `2g + 3` distinct rational places is the identity. This is the
rigidity statement behind the finiteness of `Aut(F / k)` in genus at least two: an automorphism
group acting on a finite set of at least `2g + 3` rational places embeds into the permutations
of that set.

## Main results

* `TauCeti.eq_one_of_two_mul_genus_add_three_le_card`: an automorphism of `F / k` fixing at
  least `2g + 3` rational places is the identity.
* `TauCeti.eq_of_forall_smul_eq_of_two_mul_genus_add_three_le_card`: two automorphisms agreeing
  on at least `2g + 3` rational places are equal.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.6.6 and Exercise 3.17.
* G. D. Villa Salvador, *Topics in the Theory of Algebraic Function Fields*, Birkhäuser, 2006,
  Chapter 9.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

section Aut

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- If `σ ∈ Aut(F / k)` fixes a function `z` whose pole divisor is `n P` for a rational place `P`
and `n ≥ 1`, then the degree of `F` over the fixed field of `σ` divides `n = [F : k(z)]`. -/
private theorem finrank_fixedField_dvd_of_poles_eq (hF : IsFunctionField k F) {σ : F ≃ₐ[k] F}
    {P : Place k F} (hP : P.degree = 1) {n : ℕ} (hn : 0 < n) {z : Fˣ}
    (hz : Divisor.poles hF z = (n : ℤ) • WeilDivisor.ofPoint P) (hσz : σ z = z) :
    Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) F ∣ n := by
  have hPz : P.ord (z : F) = -(n : ℤ) := by
    have h := congrArg (fun D : Divisor k F ↦ D.coeff P) hz
    simp only [Divisor.coeff_poles, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self,
      mul_one] at h
    omega
  have htrans : ¬IsAlgebraic k (z : F) := fun halg ↦ by
    rw [P.ord_eq_zero_of_isAlgebraic halg] at hPz
    omega
  have hfinrank : Module.finrank k⟮(z : F)⟯ F = n := by
    have h := Divisor.degree_poles hF z htrans
    rw [hz, Divisor.degree_zsmul, Divisor.degree_ofPoint, hP] at h
    omega
  have hmem : (z : F) ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (F ≃ₐ[k] F) (z : F) :=
      Subgroup.zpowers_le.mpr (by rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def])
    simpa only [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] using hle hτ
  rw [← hfinrank]
  exact IntermediateField.finrank_dvd_of_le_left
    (IntermediateField.adjoin_simple_le_iff.mpr hmem)

/-- **Rigidity of automorphisms of a function field** (Stichtenoth, Exercise 3.17): over an exact
constant field, an automorphism of `F / k` fixing at least `2g + 3` distinct rational places is
the identity. -/
theorem eq_one_of_two_mul_genus_add_three_le_card (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {σ : F ≃ₐ[k] F} {S : Finset (Place k F)}
    (hS : ∀ P ∈ S, P.degree = 1 ∧ σ • P = P) (hcard : 2 * genus k F + 3 ≤ S.card) :
    σ = 1 := by
  classical
  obtain ⟨P, hPS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hPdeg, hPσ⟩ := hS P hPS
  -- `σ` fixes `L((2g + 1)P)` pointwise, using the `2g + 2` other places of `S`.
  have hfix : ∀ z ∈ riemannRochSpace (((2 * genus k F + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P),
      σ z = z := by
    refine fun z hz ↦ apply_eq_self_of_mem_riemannRochSpace_of_degree_lt_card hF
      (T := S.erase P) ?_ (fun Q hQ ↦ ?_) ?_ hz
    · rw [smul_comm, WeilDivisor.smul_ofPoint, hPσ]
    · obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
      exact ⟨(hS Q hQS).1, (hS Q hQS).2, by simp [WeilDivisor.coeff_ofPoint_of_ne hQP]⟩
    · rw [Finset.card_erase_of_mem hPS, Divisor.degree_zsmul, Divisor.degree_ofPoint, hPdeg]
      push_cast
      omega
  -- A function whose only pole is at `P`, of order at most `2g + 1`, is fixed by `σ`.
  have hfix_poles : ∀ {n : ℕ}, 0 < n → n ≤ 2 * genus k F + 1 → ∀ z : Fˣ,
      Divisor.poles hF z = (n : ℤ) • WeilDivisor.ofPoint P →
      Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) F ∣ n := by
    intro n hn hle z hz
    refine finrank_fixedField_dvd_of_poles_eq hF hPdeg hn hz (hfix _ ?_)
    refine (mem_riemannRochSpace_iff_neg_le_ord (Units.ne_zero z)).mpr fun Q ↦ ?_
    have h := congrArg (fun D : Divisor k F ↦ D.coeff Q) hz
    rcases eq_or_ne Q P with rfl | hQP
    · simp only [Divisor.coeff_poles, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self,
        mul_one] at h ⊢
      omega
    · simp only [Divisor.coeff_poles, WeilDivisor.coeff_zsmul,
        WeilDivisor.coeff_ofPoint_of_ne hQP, mul_zero] at h ⊢
      omega
  -- Functions with a single pole at `P` of orders `2g + 1` and `2g` exist; their degrees are
  -- coprime, so the fixed field of `σ` is all of `F`.
  obtain ⟨x, hx⟩ := P.exists_poles_eq_natCast_zsmul_ofPoint hF hex
    (n := 2 * genus k F + 1) (by omega)
  have hdvd_x := hfix_poles (by omega) le_rfl x hx
  have hdvd_one :
      Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) F ∣ 1 := by
    rcases Nat.eq_zero_or_pos (genus k F) with hg | hg
    · simpa [hg] using hdvd_x
    · obtain ⟨y, hy⟩ := P.exists_poles_eq_natCast_zsmul_ofPoint hF hex
        (n := 2 * genus k F) le_rfl
      have hdvd_y := hfix_poles (by omega) (by omega) y hy
      simpa using Nat.dvd_sub hdvd_x hdvd_y
  have htop : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊤ :=
    IntermediateField.finrank_eq_one_iff_eq_top.mp (Nat.dvd_one.mp hdvd_one)
  ext z
  have hz : z ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := htop ▸ trivial
  exact (IntermediateField.mem_fixedField_iff _ z).mp hz σ (Subgroup.mem_zpowers σ)

/-- **Automorphisms are determined by their action on `2g + 3` rational places**: over an exact
constant field, two automorphisms of `F / k` that move each place of a set of at least `2g + 3`
rational places to the same place are equal. Hence `Aut(F / k)` acts faithfully on every invariant
set of at least `2g + 3` rational places. -/
theorem eq_of_forall_smul_eq_of_two_mul_genus_add_three_le_card (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {σ τ : F ≃ₐ[k] F} {S : Finset (Place k F)}
    (hS : ∀ P ∈ S, P.degree = 1 ∧ σ • P = τ • P) (hcard : 2 * genus k F + 3 ≤ S.card) :
    σ = τ := by
  refine (inv_mul_eq_one.mp (eq_one_of_two_mul_genus_add_three_le_card hF hex
    (fun P hP ↦ ⟨(hS P hP).1, ?_⟩) hcard)).symm
  rw [mul_smul, (hS P hP).2, inv_smul_smul]

end Aut

end TauCeti
