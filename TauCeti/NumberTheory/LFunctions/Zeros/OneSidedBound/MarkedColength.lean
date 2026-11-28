/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Algebra.Module.Submodule.ColengthDvd

/-!
# Colength budget for marked Hecke operators

At an exceptional prime, the individual operator costs count the infinite places inducing the
marked primes, plus one common rounding allowance per mark. Their total is still within the local
loss budget after taking the power corresponding to the length of the theta-lift chain.

The costs and ceiling are those of `New.Data.IsMarked.mul_sum_heckeScalingExponent_le_loss` in
`grh/src/New/UpperBound/Divisibility/LocalDivisibility.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Finset

namespace TauCeti.OneSidedBound

/-- Sum the individual marked-prime colength allowances over `Λ` and pay for `m` copies of the
sum. Here `w` sends a place to its induced prime, `S` consists of the long places, and `f` bounds
both the number of long places and the number of marks. The collision cutoff is `⌈2mfa/p⌉₊`.
The estimate uses the base loss `fa(log b)²/p`, without any exceptional multiplier. -/
theorem mul_sum_heckeScalingExponent_le_loss {Φ W : Type*} [DecidableEq W]
    {S : Finset Φ} {Λ : Finset W} (w : Φ → W) {m f a p : ℕ} {b : ℝ}
    (hS : #S ≤ f) (hΛ : #Λ ≤ f) (hp : p ≤ m * f * a) (hb : 15 ≤ (Real.log b) ^ 2) :
    (m : ℝ) * ∑ P ∈ Λ,
      (12 * a * #{σ ∈ S | w σ = P} / ((m : ℝ) * p) +
        (⌈2 * (m : ℝ) * f * a / p⌉₊ : ℝ) / ((m : ℝ) ^ 2 * f)) ≤
      (f : ℝ) * a * (Real.log b) ^ 2 / p := by
  obtain rfl | hp₀ := Nat.eq_zero_or_pos p
  · simp
  have hprod : 0 < m * f * a := hp₀.trans_le hp
  have hmf : 0 < m * f := Nat.pos_of_mul_pos_right hprod
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_mul_pos_right hmf)
  have hf : (0 : ℝ) < f := Nat.cast_pos.2 (Nat.pos_of_mul_pos_left hmf)
  have hpR : (0 : ℝ) < p := Nat.cast_pos.2 hp₀
  have hratio : 1 ≤ (m : ℝ) * f * a / p := (le_div_iff₀ hpR).2
    (by simpa using (Nat.cast_le (α := ℝ)).2 hp)
  -- Each long place contributes to at most one marked prime.
  have hcount : ∑ P ∈ Λ, (#{σ ∈ S | w σ = P} : ℝ) ≤ f := by
    exact_mod_cast (sum_card_fiberwise_eq_card_filter S Λ w).trans_le
      ((card_filter_le _ _).trans hS)
  -- The rounding loss of at most one fits inside a third copy of `mfa/p`.
  set j : ℝ := (⌈2 * (m : ℝ) * f * a / p⌉₊ : ℝ)
  have hj : j ≤ 3 * ((m : ℝ) * f * a / p) := by
    have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * (m : ℝ) * f * a / p)).le
    have heq : 2 * (m : ℝ) * f * a / p = 2 * ((m : ℝ) * f * a / p) := by ring
    dsimp only [j]
    rw [heq] at hceil ⊢
    linarith only [hceil, hratio]
  have hmfa : 0 ≤ (f : ℝ) * a / p := by positivity
  calc
    _ = 12 * a / p * (∑ P ∈ Λ, (#{σ ∈ S | w σ = P} : ℝ)) +
        (#Λ : ℝ) * (j / ((m : ℝ) * f)) := by
      rw [sum_add_distrib, mul_add, sum_const, nsmul_eq_mul, mul_sum, mul_sum]
      congr 1
      · apply sum_congr rfl
        intro P _
        field_simp
      · field_simp
    _ ≤ 12 * a / p * f + f * (j / ((m : ℝ) * f)) := by
      gcongr
    _ = 12 * ((f : ℝ) * a / p) + j / m := by field_simp
    _ ≤ 15 * ((f : ℝ) * a / p) := by
      have hj' := (div_le_div_of_nonneg_right hj hm.le)
      have heq : 3 * ((m : ℝ) * f * a / p) / m = 3 * ((f : ℝ) * a / p) := by
        field_simp
      rw [heq] at hj'
      linarith only [hj']
    _ ≤ _ := by
      calc
        _ ≤ (Real.log b) ^ 2 * ((f : ℝ) * a / p) := mul_le_mul_of_nonneg_right hb hmfa
        _ = _ := by ring

/-- If each marked Hecke operator has its individual colength bound at the collision cutoff,
then the `m`-th power of their product is onto up to colength `loss * D`, where `D` is the
common dimension factor in the individual bounds. The product uses the list order of `Λ`;
no commutation hypothesis is needed for this bound. The element `π` specifies the modulus
in the coefficient ring, while `p` specifies the numerical scale in the budget. -/
theorem isOntoUpToColength_marked_prod_pow {Φ W O V : Type*} [DecidableEq W]
    [CommRing O] [AddCommMonoid V] [Module O V] {S : Finset Φ} {Λ : Finset W}
    (w : Φ → W) {M : Submodule O V} {π : O} {m f a p D : ℕ} {b : ℝ}
    (hS : #S ≤ f) (hΛ : #Λ ≤ f) (hp : p ≤ m * f * a) (hb : 15 ≤ (Real.log b) ^ 2)
    (Y : W → Module.End O V) :
    let j := ⌈2 * (m : ℝ) * f * a / p⌉₊
    (∀ P ∈ Λ, (Y P).IsOntoUpToColength M π j
      ((12 * a * #{σ ∈ S | w σ = P} / ((m : ℝ) * p) +
        (j : ℝ) / ((m : ℝ) ^ 2 * f)) * D)) →
    ((Λ.toList.map Y).prod ^ m).IsOntoUpToColength M π j
      (((f : ℝ) * a * (Real.log b) ^ 2 / p) * D) := by
  intro j hY
  let c (P : W) : ℝ := 12 * a * #{σ ∈ S | w σ = P} / ((m : ℝ) * p) +
    (j : ℝ) / ((m : ℝ) ^ 2 * f)
  have h := Module.End.isOntoUpToColength_list_prod Λ.toList (c := fun P ↦ c P * D)
    (fun P hP ↦ hY P (Finset.mem_toList.mp hP))
  refine (h.pow m).mono ?_
  rw [Finset.sum_map_toList, ← Finset.sum_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_sum_heckeScalingExponent_le_loss w hS hΛ hp hb)
    (Nat.cast_nonneg D)

end TauCeti.OneSidedBound
