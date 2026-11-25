/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Circle.RotationNumber.Displacement
public import TauCeti.Dynamics.Rotation.Orbit

/-!
# Strict comparison of translation numbers at irrational values

For two lifts `f`, `g` of degree-one circle maps with `f ≤ g`, the translation numbers satisfy
`τ f ≤ τ g` (`CircleDeg1Lift.translationNumber_mono`). A strict inequality `f x < g x` at every
point does not make the translation numbers differ in general: two lifts with fixed points both
have translation number `0`. It does when one of the two translation numbers is irrational and
both lifts are continuous:

* `CircleDeg1Lift.translationNumber_lt_of_forall_lt_of_irrational_left`: if `τ f` is irrational,
  then `τ f < τ g`;
* `CircleDeg1Lift.translationNumber_lt_of_forall_lt_of_irrational_right`: if `τ g` is
  irrational, then `τ f < τ g`.

The proof for `α = τ f` irrational: the continuous `1`-periodic function `g - f` is at least some
`ε > 0`. Choose `q ≥ 1` and an integer `p` with `0 < p - q α < ε`
(`Irrational.exists_int_sub_nat_mul_mem_Ioo`, from the density of the forward multiples of an
irrational rotation). Since `τ (f ^ q) = q α > p - ε`, some `x` has `f^q x > x + p - ε`; along
the iterates the margin `ε` survives, `g^q x ≥ f^q x + ε > x + p`, so `τ g ≥ p / q > α`. The
case `τ g` irrational is symmetric.

## References

* Michael-R. Herman, *Sur les courbes invariantes par les difféomorphismes de l'anneau*, Vol. 1,
  Astérisque 103–104, 1983, Chapitre I, 2.4.3.
-/

public section

open Function Set

namespace CircleDeg1Lift

local notation "τ" => translationNumber

/-- **Uniform margin between continuous lifts.** Two continuous lifts with `f x < g x` for every
`x` satisfy `f x + ε ≤ g x` for a single `ε > 0`. -/
theorem exists_pos_forall_add_le_of_forall_lt {f g : CircleDeg1Lift} (hf : Continuous f)
    (hg : Continuous g) (hfg : ∀ x, f x < g x) : ∃ ε > 0, ∀ x, f x + ε ≤ g x := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one)
    (hg.sub hf).continuousOn
  refine ⟨g x₀ - f x₀, by linarith [hfg x₀], fun x ↦ ?_⟩
  have h : g x₀ - f x₀ ≤ g (Int.fract x) - f (Int.fract x) :=
    hx₀ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  linarith [f.map_fract_sub_fract_eq x, g.map_fract_sub_fract_eq x]

/-- A uniform margin `f + ε ≤ g` between two lifts, with `0 ≤ ε`, persists for every iterate:
`f^[n] + ε ≤ g^[n]` for `n ≠ 0`. -/
theorem iterate_add_le_iterate {f g : CircleDeg1Lift} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x, f x + ε ≤ g x) {n : ℕ} (hn : n ≠ 0) (x : ℝ) : f^[n] x + ε ≤ g^[n] x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [iterate_succ_apply', iterate_succ_apply']
  have hle : f^[n] x ≤ g^[n] x :=
    Monotone.iterate_le_of_le f.monotone (fun y ↦ by linarith [h y]) n x
  linarith [h (f^[n] x), g.monotone hle]

/-- **Strict comparison at an irrational value, left form.** Let `f`, `g` be continuous lifts
with `f x < g x` for every `x`. If the translation number of `f` is irrational, then it is
smaller than the translation number of `g`. -/
theorem translationNumber_lt_of_forall_lt_of_irrational_left {f g : CircleDeg1Lift}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x < g x) (hα : Irrational (τ f)) :
    τ f < τ g := by
  obtain ⟨ε, hε, hεfg⟩ := exists_pos_forall_add_le_of_forall_lt hf hg hfg
  obtain ⟨q, hq, p, hp₁, hp₂⟩ := hα.exists_int_sub_nat_mul_mem_Ioo hε
  have hq' : (0 : ℝ) < q := Nat.cast_pos.2 hq
  obtain ⟨x, hx⟩ : ∃ x, x + (p - ε) < (f ^ q) x := by
    by_contra! H
    have := (f ^ q).translationNumber_le_of_le_add H
    rw [translationNumber_pow] at this
    linarith
  have hgx : x + p ≤ (g ^ q) x := by
    rw [coe_pow] at hx ⊢
    linarith [iterate_add_le_iterate hε.le hεfg hq.ne' x]
  have := (g ^ q).le_translationNumber_of_add_int_le hgx
  rw [translationNumber_pow] at this
  nlinarith [hq']

/-- **Strict comparison at an irrational value, right form.** Let `f`, `g` be continuous lifts
with `f x < g x` for every `x`. If the translation number of `g` is irrational, then it is
larger than the translation number of `f`. -/
theorem translationNumber_lt_of_forall_lt_of_irrational_right {f g : CircleDeg1Lift}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x < g x) (hβ : Irrational (τ g)) :
    τ f < τ g := by
  obtain ⟨ε, hε, hεfg⟩ := exists_pos_forall_add_le_of_forall_lt hf hg hfg
  obtain ⟨q, hq, p, hp₁, hp₂⟩ := hβ.neg.exists_int_sub_nat_mul_mem_Ioo hε
  have hq' : (0 : ℝ) < q := Nat.cast_pos.2 hq
  obtain ⟨x, hx⟩ : ∃ x, (g ^ q) x < x + (-p + ε) := by
    by_contra! H
    have := (g ^ q).le_translationNumber_of_add_le H
    rw [translationNumber_pow] at this
    linarith
  have hfx : (f ^ q) x ≤ x + ((-p : ℤ) : ℝ) := by
    rw [coe_pow] at hx ⊢
    push_cast
    linarith [iterate_add_le_iterate hε.le hεfg hq.ne' x]
  have := (f ^ q).translationNumber_le_of_le_add_int hfx
  rw [translationNumber_pow] at this
  push_cast at hp₁ hp₂ this
  nlinarith [hq']

end CircleDeg1Lift
