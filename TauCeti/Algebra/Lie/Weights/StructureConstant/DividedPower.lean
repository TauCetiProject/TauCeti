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

include hx hα hβ hab in
/-- Every divided iterated bracket at a root of a nonopposite root string has an
integer coefficient. -/
theorem exists_int_inv_factorial_smul_ad_pow_eq_zsmul
    (γ : Weight K H L) (n : ℕ) (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K)) :
    ∃ z : ℤ, (n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) (x β) = z • x γ := by
  rcases hx.ad_pow_rootVector_eq_zero_or_exists hα hβ hab n with
    hzero | ⟨δ, hδ, -, z, hz, hpow⟩
  · exact ⟨0, by simp [hzero]⟩
  have hδγ : δ = γ := by
    apply DFunLike.coe_injective
    exact hδ.trans hγ.symm
  subst δ
  obtain ⟨w, hw⟩ : (n.factorial : ℤ) ∣ z := by
    apply Int.dvd_natAbs.1
    rw [hz]
    exact Int.natCast_dvd_natCast.2 (Nat.factorial_dvd_ascFactorial _ _)
  refine ⟨w, ?_⟩
  rw [hpow, hw, smul_smul, ← Int.cast_smul_eq_zsmul K]
  congr 1
  push_cast
  exact inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 n.factorial_ne_zero) _

/-- The integer coefficient `M_{α,β,n}` of the divided iterated bracket at the root
`γ = β + n α`. The source roots are nonzero and nonopposite. -/
noncomputable def intDividedStructureConstant
    (γ : Weight K H L) (n : ℕ) (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K)) : ℤ :=
  Classical.choose (hx.exists_int_inv_factorial_smul_ad_pow_eq_zsmul α β hα hβ hab γ n hγ)

/-- The divided iterated bracket is the integer coefficient times its root vector. -/
theorem inv_factorial_smul_ad_pow_eq_intDividedStructureConstant_zsmul
    (γ : Weight K H L) (n : ℕ) (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K)) :
    (n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) (x β) =
      hx.intDividedStructureConstant α β hα hβ hab γ n hγ • x γ :=
  Classical.choose_spec (hx.exists_int_inv_factorial_smul_ad_pow_eq_zsmul α β hα hβ hab γ n hγ)

/-- The coefficient is uniquely determined by the divided iterated bracket equation. -/
@[simp]
theorem eq_intDividedStructureConstant_iff
    (γ : Weight K H L) (n : ℕ) (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K))
    (z : ℤ) :
    z = hx.intDividedStructureConstant α β hα hβ hab γ n hγ ↔
      (n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) (x β) = z • x γ := by
  have hγnz : γ.IsNonZero := by
    rw [Weight.IsNonZero, Weight.IsZero, hγ]
    exact coe_add_natCast_smul_ne_zero hα hβ hab n
  rw [hx.inv_factorial_smul_ad_pow_eq_intDividedStructureConstant_zsmul α β hα hβ hab γ n hγ]
  constructor
  · rintro rfl
    rfl
  · intro hz
    apply Int.cast_injective (α := K)
    apply smul_left_injective K (hx.toIsSl2System.ne_zero γ hγnz)
    simpa only [Int.cast_smul_eq_zsmul] using hz.symm

/-- Degree zero has coefficient one. -/
@[simp]
theorem intDividedStructureConstant_zero :
    hx.intDividedStructureConstant α β hα hβ hab β 0 (by simp) = 1 := by
  symm
  apply (hx.eq_intDividedStructureConstant_iff α β hα hβ hab β 0 _ 1).2
  simp

/-- Degree one recovers the ordinary integer structure constant. -/
@[simp]
theorem intDividedStructureConstant_one
    (γ : Weight K H L) (hγ : (γ : H → K) = (α : H → K) + β) :
    hx.intDividedStructureConstant α β hα hβ hab γ 1 (by simpa [add_comm] using hγ) =
      hx.intStructureConstant α β γ
        (by rw [Weight.IsNonZero, Weight.IsZero, hγ]; exact hab) hγ := by
  symm
  apply (hx.eq_intDividedStructureConstant_iff α β hα hβ hab γ 1 _ _).2
  simpa only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one, ad_apply] using
    hx.lie_eq_intStructureConstant_zsmul α β γ
      (by rw [Weight.IsNonZero, Weight.IsZero, hγ]; exact hab) hγ

/-- Consecutive divided root-string coefficients satisfy
`(n + 1) M_{α,β,n+1} = M_{α,β,n} N_{α,γ}`, with `γ = β + n α`.
This equation takes place in `ℤ`, before any reduction of the coefficients. -/
theorem succ_mul_intDividedStructureConstant
    (γ δ : Weight K H L) (n : ℕ)
    (hγ : (γ : H → K) = (β : H → K) + (n : K) • (α : H → K))
    (hδ : (δ : H → K) = (β : H → K) + ((n + 1 : ℕ) : K) • (α : H → K)) :
    (n + 1 : ℤ) * hx.intDividedStructureConstant α β hα hβ hab δ (n + 1) hδ =
      hx.intDividedStructureConstant α β hα hβ hab γ n hγ *
        hx.intStructureConstant α γ δ
          (by rw [Weight.IsNonZero, Weight.IsZero, hδ]
              exact coe_add_natCast_smul_ne_zero hα hβ hab (n + 1))
          (by rw [hδ, hγ]; push_cast; module) := by
  have hδnz : δ.IsNonZero := by
    rw [Weight.IsNonZero, Weight.IsZero, hδ]
    exact coe_add_natCast_smul_ne_zero hα hβ hab (n + 1)
  have hstep : (δ : H → K) = (α : H → K) + γ := by
    rw [hδ, hγ]
    push_cast
    module
  apply Int.cast_injective (α := K)
  apply smul_left_injective K (hx.toIsSl2System.ne_zero δ hδnz)
  simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, mul_smul,
    Int.cast_smul_eq_zsmul]
  rw [← hx.inv_factorial_smul_ad_pow_eq_intDividedStructureConstant_zsmul
      α β hα hβ hab δ (n + 1) hδ,
    ← hx.lie_eq_intStructureConstant_zsmul α γ δ hδnz hstep, ← lie_zsmul,
    ← hx.inv_factorial_smul_ad_pow_eq_intDividedStructureConstant_zsmul α β hα hβ hab γ n hγ]
  rw [lie_smul, ← ad_apply (R := K), pow_succ', mul_apply_eq_comp, smul_smul,
    Nat.factorial_succ]
  congr 1
  push_cast
  field_simp

/-- Along a finite root string, the product of the successive integral bracket
coefficients is `n!` times the divided coefficient. Only the portion `0, …, n` of
`γ` is required to be a root string. In particular, this does not assert the
existence of an infinite string of roots. -/
theorem factorial_mul_intDividedStructureConstant_eq_prod
    (γ : ℕ → Weight K H L) (N : ℕ → ℤ) (n : ℕ)
    (hγ : ∀ k ≤ n, (γ k : H → K) = (β : H → K) + (k : K) • (α : H → K))
    (hN : ∀ k < n, ⁅x α, x (γ k)⁆ = N k • x (γ (k + 1))) :
    (n.factorial : ℤ) * hx.intDividedStructureConstant α β hα hβ hab (γ n) n (hγ n le_rfl) =
      ∏ k ∈ Finset.range n, N k := by
  induction n with
  | zero =>
    have hzero : γ 0 = β := DFunLike.coe_injective (by simpa using hγ 0 le_rfl)
    subst_vars
    simp
  | succ n ih =>
    have hγn := hγ n (by omega)
    have hγs := hγ (n + 1) le_rfl
    have hnz : (γ (n + 1)).IsNonZero := by
      rw [Weight.IsNonZero, Weight.IsZero, hγs]
      exact coe_add_natCast_smul_ne_zero hα hβ hab (n + 1)
    have hstep : (γ (n + 1) : H → K) = (α : H → K) + γ n := by
      rw [hγs, hγn]
      push_cast
      module
    have hconst := (hx.eq_intStructureConstant_iff α (γ n) (γ (n + 1)) hnz hstep (N n)).2
      (hN n (by omega))
    have hrec := hx.succ_mul_intDividedStructureConstant α β hα hβ hab
      (γ n) (γ (n + 1)) n hγn hγs
    rw [← hconst] at hrec
    have hprod := ih (fun k hk => hγ k (by omega)) (fun k hk => hN k (by omega))
    rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      (↑n + 1) * ↑n.factorial *
          hx.intDividedStructureConstant α β hα hβ hab (γ (n + 1)) (n + 1) hγs =
          ↑n.factorial * ((↑n + 1) *
            hx.intDividedStructureConstant α β hα hβ hab (γ (n + 1)) (n + 1) hγs) := by ring
      _ = (↑n.factorial * hx.intDividedStructureConstant α β hα hβ hab (γ n) n hγn) * N n := by
        rw [hrec]
        ring
      _ = (∏ k ∈ Finset.range n, N k) * N n := by rw [hprod]

end TauCeti.IsChevalleySystem
