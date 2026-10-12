/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Algebra.Ring.SubOnePow

/-!
# Monoid algebras over the `p`-adic integers: powers of `g - 1`

In the monoid algebra `ℤ_[p][Q]` of a monoid `Q`, let `g` be an element with `g ^ p ^ k = 1`.
Then `(g - 1) ^ p ^ k` is divisible by `p`
(`Nat.Prime.dvd_sub_one_pow_of_pow_eq_one`), so `(g - 1) ^ n` lies in `p ^ m • ℤ_[p][Q]` as
soon as `n ≥ p ^ k * m`, and every coefficient of `(g - 1) ^ n` tends to `0` in `ℤ_[p]` as
`n → ∞`. This is the finite-level input for the topological nilpotence of `γ - 1` in the completed
group algebra `ℤ_p[[Γ]]` of a pro-`p` group `Γ`, the fact that lets power series over `ℤ_[p]` be
evaluated at `γ - 1` there.

## Main result

* `TauCeti.PadicInt.tendsto_coeff_single_sub_one_pow`: for `g ^ p ^ k = 1` in a monoid `Q`,
  every coefficient of `(single g 1 - 1) ^ n` in `ℤ_[p][Q]` tends to `0` as `n → ∞`.
-/

public section

open Filter Topology

namespace TauCeti.PadicInt

variable {p : ℕ} [Fact p.Prime] {Q : Type*} [Monoid Q]

/-- For `n ≥ p ^ k * m`, the power `(single g 1 - 1) ^ n` in `ℤ_[p][Q]`, for `g` with
`g ^ p ^ k = 1`, is `p ^ m` times an element of the monoid algebra. -/
theorem exists_single_sub_one_pow_eq_pow_smul {g : Q} {k : ℕ} (hg : g ^ p ^ k = 1) {m n : ℕ}
    (hn : p ^ k * m ≤ n) : ∃ w : MonoidAlgebra ℤ_[p] Q,
      (MonoidAlgebra.single g (1 : ℤ_[p]) - 1) ^ n = (p : ℤ_[p]) ^ m • w := by
  obtain ⟨z, hz⟩ : (p : MonoidAlgebra ℤ_[p] Q) ∣ (MonoidAlgebra.single g (1 : ℤ_[p]) - 1) ^ p ^ k :=
    (Fact.out : p.Prime).dvd_sub_one_pow_of_pow_eq_one <| by
      rw [MonoidAlgebra.single_pow, one_pow, hg, ← MonoidAlgebra.one_def]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨z ^ m * (MonoidAlgebra.single g (1 : ℤ_[p]) - 1) ^ r, ?_⟩
  -- `(g - 1) ^ (p ^ k * m + r) = (p * z) ^ m * (g - 1) ^ r`, and multiplication by the natural
  -- number `p ^ m` is scalar multiplication by `p ^ m ∈ ℤ_[p]`.
  rw [pow_add, pow_mul, hz, (Nat.cast_commute p z).mul_pow, mul_assoc]
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

/-- **Powers of `g - 1` tend to zero coefficientwise.** For `g` with `g ^ p ^ k = 1` in a monoid
`Q`, every coefficient of `(single g 1 - 1) ^ n` in `ℤ_[p][Q]` tends to `0` as `n → ∞`. -/
theorem tendsto_coeff_single_sub_one_pow {g : Q} {k : ℕ} (hg : g ^ p ^ k = 1) (q : Q) :
    Tendsto (fun n ↦ ((MonoidAlgebra.single g (1 : ℤ_[p]) - 1) ^ n).coeff q) atTop (𝓝 0) := by
  have hp : p.Prime := Fact.out
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt : (1 : ℝ) < p))
  refine ⟨p ^ k * m, fun n hn ↦ ?_⟩
  obtain ⟨w, hw⟩ := exists_single_sub_one_pow_eq_pow_smul hg hn
  rw [hw, MonoidAlgebra.coeff_smul_apply, smul_eq_mul, dist_zero_right]
  calc ‖(p : ℤ_[p]) ^ m * w.coeff q‖ ≤ ‖(p : ℤ_[p]) ^ m‖ * ‖w.coeff q‖ := norm_mul_le _ _
    _ ≤ ‖(p : ℤ_[p]) ^ m‖ * 1 := by gcongr; exact _root_.PadicInt.norm_le_one _
    _ = (p : ℝ)⁻¹ ^ m := by
      rw [mul_one, _root_.PadicInt.norm_p_pow, zpow_neg, zpow_natCast, inv_pow]
    _ < ε := hm

end TauCeti.PadicInt
