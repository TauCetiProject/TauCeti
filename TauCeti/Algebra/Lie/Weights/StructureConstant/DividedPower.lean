/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Root.KostantStability

/-!
# Integral divided root-string coefficients

For a Chevalley system `x`, the coefficient of `x γ` in
`(ad (x α)) ^ n (x β) / n!`, where `γ = β + n α`, is an integer. These are the
coefficients usually denoted `M_{α,β,n}` in the Chevalley commutator formula. Keeping
the coefficient in `ℤ` permits reduction in characteristics dividing `n!`; division
in the value field would lose precisely that information.

This file defines `IsChevalleySystem.intDividedStructureConstant`, characterizes it
by its action on root vectors, and proves the recurrence
`(n + 1) M_{α,β,n+1} = M_{α,β,n} N_{α,β+nα}`. The finite-string product theorem
identifies `n! M_{α,β,n}` with the product of its successive bracket coefficients.
Degree zero gives `1`, and degree one recovers `IsChevalleySystem.intStructureConstant`.
The source roots are nonopposite;
the exceptional string through `-α`, which passes through the Cartan subalgebra,
is not part of this interface.

The construction uses the rising-factorial computation
`IsChevalleySystem.ad_pow_rootVector_eq_zero_or_exists` from
`TauCeti.Algebra.Lie.Weights.Root.KostantStability`, rather than a new proof of
factorial cancellation. Uniqueness makes the resulting integer independent of the
existence witness used in the definition.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.5.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4 and Theorem 5.2.2.
-/

public section

namespace TauCeti.IsChevalleySystem

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)
  (α β : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero)
  (hab : (α : H → K) + β ≠ 0)

/-- The integer coefficient `M_{α,β,n}` of the divided iterated bracket at the root
`γ = β + n α`. The source weights are nonopposite; the lemmas characterising the coefficient
assume that both are nonzero, and otherwise it is a junk integer. -/
noncomputable def intDividedStructureConstant
    (γ : Weight K H L) (n : ℕ) (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K)) : ℤ :=
  Classical.choose (hx.exists_int_inv_factorial_smul_ad_pow_eq_zsmul α β hab γ n hγ)

/-- The divided iterated bracket is the integer coefficient times its root vector. -/
theorem inv_factorial_smul_ad_pow_eq_intDividedStructureConstant_zsmul
    (γ : Weight K H L) (n : ℕ) (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K)) :
    (n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) (x β) =
      hx.intDividedStructureConstant α β hab γ n hγ • x γ :=
  Classical.choose_spec (hx.exists_int_inv_factorial_smul_ad_pow_eq_zsmul α β hab γ n hγ)

include hα hβ in
/-- The coefficient is uniquely determined by the divided iterated bracket equation. -/
@[simp]
theorem eq_intDividedStructureConstant_iff
    (γ : Weight K H L) (n : ℕ) (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K))
    (z : ℤ) :
    z = hx.intDividedStructureConstant α β hab γ n hγ ↔
      (n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) (x β) = z • x γ := by
  have hγnz := γ.isNonZero_of_coe_eq_add_natCast_smul hα hβ hab hγ
  rw [hx.inv_factorial_smul_ad_pow_eq_intDividedStructureConstant_zsmul α β hab γ n hγ]
  constructor
  · rintro rfl
    rfl
  · intro hz
    apply Int.cast_injective (α := K)
    apply smul_left_injective K (hx.toIsSl2System.ne_zero γ hγnz)
    simpa only [Int.cast_smul_eq_zsmul] using hz.symm

include hα hβ in
/-- Degree zero has coefficient one. -/
@[simp]
theorem intDividedStructureConstant_zero :
    hx.intDividedStructureConstant α β hab β 0 (by simp) = 1 := by
  symm
  apply (hx.eq_intDividedStructureConstant_iff α β hα hβ hab β 0 _ 1).2
  simp

/-- Degree one recovers the ordinary integer structure constant. -/
@[simp]
theorem intDividedStructureConstant_one
    (γ : Weight K H L) (hγ : (γ : H → K) = (α : H → K) + β) :
    hx.intDividedStructureConstant α β hab γ 1 (by simpa [add_comm] using hγ) =
      hx.intStructureConstant α β γ
        (γ.isNonZero_of_coe_eq_add_natCast_smul hα hβ hab (n := 1)
          (by simpa [add_comm] using hγ)) hγ := by
  symm
  apply (hx.eq_intDividedStructureConstant_iff α β hα hβ hab γ 1 _ _).2
  simpa only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one, ad_apply] using
    hx.lie_eq_intStructureConstant_zsmul α β γ
      (γ.isNonZero_of_coe_eq_add_natCast_smul hα hβ hab (n := 1)
        (by simpa [add_comm] using hγ)) hγ

/-- Consecutive divided root-string coefficients satisfy
`(n + 1) M_{α,β,n+1} = M_{α,β,n} N_{α,γ}`, with `γ = β + n α`.
This equation takes place in `ℤ`, before any reduction of the coefficients. -/
theorem succ_mul_intDividedStructureConstant
    (γ δ : Weight K H L) (n : ℕ)
    (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K))
    (hδ : (δ : H → K) = (β : H → K) + ((n + 1 : ℕ) : K) • (α : H → K)) :
    (n + 1 : ℤ) * hx.intDividedStructureConstant α β hab δ (n + 1) hδ =
      hx.intDividedStructureConstant α β hab γ n hγ *
        hx.intStructureConstant α γ δ
          (δ.isNonZero_of_coe_eq_add_natCast_smul hα hβ hab hδ)
          (δ.coe_eq_add_of_coe_eq_add_natCast_smul_succ hγ hδ) := by
  have hδnz := δ.isNonZero_of_coe_eq_add_natCast_smul hα hβ hab hδ
  have hstep := δ.coe_eq_add_of_coe_eq_add_natCast_smul_succ hγ hδ
  have hpow : ((ad K L (x α)) ^ (n + 1)) (x β) =
      ⁅x α, ((ad K L (x α)) ^ n) (x β)⁆ := by
    simp [pow_succ', mul_apply_eq_comp, ad_apply]
  apply Int.cast_injective (α := K)
  apply smul_left_injective K (hx.toIsSl2System.ne_zero δ hδnz)
  simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, mul_smul,
    Int.cast_smul_eq_zsmul]
  rw [← hx.inv_factorial_smul_ad_pow_eq_intDividedStructureConstant_zsmul
      α β hab δ (n + 1) hδ,
    ← hx.lie_eq_intStructureConstant_zsmul α γ δ hδnz hstep, ← lie_zsmul,
    ← hx.inv_factorial_smul_ad_pow_eq_intDividedStructureConstant_zsmul α β hab γ n hγ]
  simp only [hpow, lie_smul, smul_smul, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  congr 1
  field_simp

include hα hβ in
/-- Along a finite root string, the product of the successive integral bracket
coefficients is `n!` times the divided coefficient. Only the portion `0, …, n` of
`γ` is required to be a root string. In particular, this does not assert the
existence of an infinite string of roots. -/
theorem factorial_mul_intDividedStructureConstant_eq_prod
    (γ : ℕ → Weight K H L) (N : ℕ → ℤ) (n : ℕ)
    (hγ : ∀ k ≤ n, (γ k : H → K) = (β : H → K) + (k : K) • (α : H → K))
    (hN : ∀ k < n, ⁅x α, x (γ k)⁆ = N k • x (γ (k + 1))) :
    (n.factorial : ℤ) * hx.intDividedStructureConstant α β hab (γ n) n (hγ n le_rfl) =
      ∏ k ∈ Finset.range n, N k := by
  induction n with
  | zero =>
    have hzero : γ 0 = β := DFunLike.coe_injective (by simpa using hγ 0 le_rfl)
    subst_vars
    simpa using hx.intDividedStructureConstant_zero α (γ 0) hα hβ hab
  | succ n ih =>
    have hγn := hγ n (by omega)
    have hγs := hγ (n + 1) le_rfl
    have hnz := (γ (n + 1)).isNonZero_of_coe_eq_add_natCast_smul hα hβ hab hγs
    have hstep := (γ (n + 1)).coe_eq_add_of_coe_eq_add_natCast_smul_succ hγn hγs
    have hconst := (hx.eq_intStructureConstant_iff α (γ n) (γ (n + 1)) hnz hstep (N n)).2
      (hN n (by omega))
    have hrec := hx.succ_mul_intDividedStructureConstant α β hα hβ hab
      (γ n) (γ (n + 1)) n hγn hγs
    rw [← hconst] at hrec
    have hprod := ih (fun k hk => hγ k (by omega)) (fun k hk => hN k (by omega))
    rw [Finset.prod_range_succ, Nat.factorial_succ]
    push_cast
    linear_combination (n.factorial : ℤ) * hrec + N n * hprod

end TauCeti.IsChevalleySystem
