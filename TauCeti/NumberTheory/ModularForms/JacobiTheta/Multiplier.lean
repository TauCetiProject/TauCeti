/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.JacobiTripleProduct
import TauCeti.Analysis.SpecialFunctions.QPochhammer
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic
import TauCeti.NumberTheory.ModularForms.DedekindEta.Kronecker
import TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient
import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Nonvanishing of `jacobiTheta`, its eta-quotient identity, and the `Γ₀(4)` theta multiplier

Using Jacobi's product specialization (`TauCeti.hasSum_pow_sq`), this file expresses
`jacobiTheta` on the upper half-plane as a convergent nonvanishing infinite product, identifies
`θ(2 τ)` with the level-`4` eta quotient `η(2 τ)⁵ / (η(τ)² η(4 τ)²)`, and derives Shimura's
weight-`1/2` automorphy factor `j(γ, z) = θ(2 · γ z) / θ(2 z)` for `γ ∈ Γ₀(4)`.

## Main definitions

* `TauCeti.thetaMultiplierPhase`: Shimura's fourth-root-of-unity phase `ε_d`, equal to `1` for
  `d ≡ 1 (mod 4)`, `I` for `d ≡ 3 (mod 4)`, and `0` for even `d`.
* `TauCeti.thetaAutomorphyFactor`: the theta automorphy factor
  `j(γ, z) = jacobiTheta (2 * (γ • z)) / jacobiTheta (2 * z)` for `γ ∈ SL(2, ℤ)` and `z ∈ ℍ`.

## Main results

* `TauCeti.jacobiTheta_eq_tprod`: on `0 < τ.im`,
  `jacobiTheta τ = (∏' n, (1 + e^{π i (2n+1) τ})) ^ 2 * ∏' n, (1 - e^{2π i (n+1) τ})`.
* `TauCeti.jacobiTheta_ne_zero`: `jacobiTheta τ ≠ 0` whenever `0 < τ.im`.
* `TauCeti.jacobiTheta_two_mul_eq_eta`:
  `jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2)` on `0 < τ.im`.
* `TauCeti.thetaMultiplierPhase_sq`:
  `thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ d : ℂ)` for every `d : ℤ`.
* `TauCeti.thetaAutomorphyFactor_mul`: the cocycle law
  `j(γ₁ * γ₂, z) = j(γ₁, γ₂ • z) * j(γ₂, z)` for all `γ₁, γ₂ ∈ SL(2, ℤ)`.
* `TauCeti.thetaAutomorphyFactor_of_mem_Gamma0`: Shimura's formula for `γ ∈ Γ₀(4)`,
  `thetaAutomorphyFactor γ z = (ε_d)⁻¹ * (c / d) * √(c * z + d)`.
* `TauCeti.thetaAutomorphyFactor_sq_of_mem_Gamma0`: for `γ ∈ Γ₀(4)`,
  `thetaAutomorphyFactor γ z ^ 2 = (ZMod.χ₄ (γ 1 1) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1)`.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. (2) **97** (1973),
  440–481, (1.10)–(1.11).
* H. Iwaniec, *Fourier coefficients of modular forms of half-integral weight*, Invent. Math. **87**
  (1987), 385–401, §2.
-/

public section

open Complex CongruenceSubgroup ModularGroup TauCeti.ModularForm
open scoped ModularForm MatrixGroups Real UpperHalfPlane

namespace TauCeti

/-! ### Product formula, nonvanishing, and eta quotient for `jacobiTheta` -/

/-- **Infinite-product formula for `jacobiTheta`**: for `0 < τ.im`,
`jacobiTheta τ = (∏_{n ≥ 0} (1 + e^{π i (2n+1) τ}))² ∏_{n ≥ 1} (1 - e^{2π i n τ})`. -/
theorem jacobiTheta_eq_tprod {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ = (∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 2 *
      ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) := by
  have hs := UpperHalfPlane.norm_exp_pi_I_lt_one hτ
  have hθ : jacobiTheta τ = ∑' k : ℤ, cexp (π * I * τ) ^ (k ^ 2) := by
    refine tsum_congr fun k ↦ ?_
    rw [← Complex.exp_intCast_mul]
    congr 1
    push_cast
    ring
  rw [hθ, tsum_pow_sq hs, ← UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq]

/-- **`jacobiTheta` never vanishes on the upper half-plane**. -/
theorem jacobiTheta_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiTheta τ ≠ 0 := by
  rw [jacobiTheta_eq_tprod hτ]
  have h1 : ∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1)) ≠ 0 := by
    have h := tprod_one_sub_pow_odd_ne_zero (q := -cexp (π * I * τ))
      (by simpa [norm_neg] using UpperHalfPlane.norm_exp_pi_I_lt_one hτ)
    rwa [tprod_congr (one_sub_neg_pow_odd (cexp (π * I * τ)))] at h
  have h2 : ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) ≠ 0 :=
    tprod_one_sub_pow_ne_zero (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩)
  exact mul_ne_zero (pow_ne_zero 2 h1) h2

/-- **Eta-quotient identity for `jacobiTheta (2 * τ)`**: on `0 < τ.im`,
`jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2)`. -/
theorem jacobiTheta_two_mul_eq_eta {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2) := by
  have h2τ : 0 < (2 * τ).im := by simpa using mul_pos two_pos hτ
  have h4τ : 0 < (4 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 4) hτ
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have hη4 : η (4 * τ) ≠ 0 := _root_.ModularForm.eta_ne_zero h4τ
  refine (eq_div_iff (mul_ne_zero (pow_ne_zero 2 hη) (pow_ne_zero 2 hη4))).mpr ?_
  set q : ℂ := cexp (2 * π * I * τ)
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have hq2 : ‖q ^ 2‖ < 1 := norm_pow_lt_one hq two_ne_zero
  have h2π : cexp (π * I * (2 * τ)) = q := by congr 1; ring
  have h4π : cexp (2 * π * I * (2 * τ)) = q ^ 2 := by
    rw [← Complex.exp_natCast_mul]
    congr 1
    push_cast
    ring
  have hA : (∏' n : ℕ, (1 + q ^ (2 * n + 1))) * (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) =
      ∏' n : ℕ, (1 + q ^ (n + 1)) := by
    have hE : Multipliable fun k : ℕ ↦ 1 + q ^ (2 * k + 1 + 1) := by
      simpa [← pow_mul, mul_add] using multipliable_one_add_pow hq2
    rw [← tprod_even_mul_odd (f := fun n ↦ 1 + q ^ (n + 1)) (multipliable_one_add_pow_odd hq) hE]
    simp [← pow_mul, mul_add]
  have hη2_prod : η (2 * τ) = cexp (π * I * τ / 6) * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
    rw [eta_eq_exp_mul_tprod, h4π]
    congr 2
    ring
  have hη2_tau : η (2 * τ) = cexp (π * I * τ / 12) * η τ * ∏' n : ℕ, (1 + q ^ (n + 1)) :=
    eta_two_mul hτ
  have hη4_tau : η (4 * τ) = cexp (π * I * (2 * τ) / 12) * η (2 * τ) *
      ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)) := by
    simpa [show 2 * (2 * τ) = 4 * τ by ring, h4π] using eta_two_mul h2τ
  have hexp : cexp (π * I * (2 * τ) / 12) ^ 2 =
      cexp (π * I * τ / 6) * cexp (π * I * τ / 12) ^ 2 := by
    rw [← Complex.exp_natCast_mul, ← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hθ : jacobiTheta (2 * τ) = (∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 *
      ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
    rw [jacobiTheta_eq_tprod h2τ, h2π, h4π]
  calc jacobiTheta (2 * τ) * (η τ ^ 2 * η (4 * τ) ^ 2)
      = ((∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
          (η τ ^ 2 * (cexp (π * I * (2 * τ) / 12) * η (2 * τ) *
            ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) ^ 2) := by rw [hθ, hη4_tau]
    _ = (cexp (π * I * τ / 6) * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
          (cexp (π * I * τ / 12) * η τ * ((∏' n : ℕ, (1 + q ^ (2 * n + 1))) *
            ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)))) ^ 2 * η (2 * τ) ^ 2 := by
          rw [mul_pow, mul_pow, hexp]
          ring
    _ = η (2 * τ) * η (2 * τ) ^ 2 * η (2 * τ) ^ 2 := by
          rw [hA, ← hη2_prod, ← hη2_tau]
    _ = η (2 * τ) ^ 5 := by ring

/-- The exponent vector of the level-`4` eta quotient representing `τ ↦ θ(2 τ)`. -/
private def thetaExpVec : ℕ → ℤ :=
  fun δ ↦ if δ = 2 then 5 else if δ = 1 ∨ δ = 4 then -2 else 0

private lemma sum_divisors_four_thetaExpVec : ∑ δ ∈ (4 : ℕ).divisors, thetaExpVec δ = 1 := by
  decide

private lemma jacobiTheta_two_mul_eq_etaQuotient {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (2 * τ) = etaQuotient 4 thetaExpVec τ := by
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [jacobiTheta_two_mul_eq_eta hτ, etaQuotient_apply, hdiv]
  simp only [Finset.mem_insert, Finset.mem_singleton, OfNat.one_ne_ofNat, OfNat.ofNat_ne_one,
    or_self, not_false_eq_true, Finset.prod_insert, Nat.cast_one, one_mul,
    Nat.reduceEqDiff, Finset.prod_singleton, Nat.cast_ofNat, thetaExpVec]
  norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, zpow_neg, zpow_ofNat]

/-! ### Shimura's phase factor `ε_d` -/

/-- Shimura's phase factor `ε_d` (`1` for `d ≡ 1 (mod 4)`, `I` for `d ≡ 3 (mod 4)`, `0` for even
`d`), appearing in the transformation law of `θ(2 τ)` under `Γ₀(4)`. -/
noncomputable def thetaMultiplierPhase (d : ℤ) : ℂ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0

/-- Defining formula for `thetaMultiplierPhase`. -/
theorem thetaMultiplierPhase_def (d : ℤ) :
    thetaMultiplierPhase d = if d % 4 = 1 then 1 else if d % 4 = 3 then I else 0 := (rfl)

/-- For `d ≡ 1 (mod 4)`, `thetaMultiplierPhase d = 1`. -/
theorem thetaMultiplierPhase_one_mod_four {d : ℤ} (hd : d % 4 = 1) :
    thetaMultiplierPhase d = 1 := by
  rw [thetaMultiplierPhase_def, ite_eq_left hd]

/-- For `d ≡ 3 (mod 4)`, `thetaMultiplierPhase d = I`. -/
theorem thetaMultiplierPhase_three_mod_four {d : ℤ} (hd : d % 4 = 3) :
    thetaMultiplierPhase d = I := by
  rw [thetaMultiplierPhase_def, ite_eq_right (by omega), ite_eq_left hd]

/-- For even `d`, `thetaMultiplierPhase d = 0`. -/
theorem thetaMultiplierPhase_of_even {d : ℤ} (hd : Even d) : thetaMultiplierPhase d = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [thetaMultiplierPhase_def, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- `thetaMultiplierPhase d = 0` if and only if `d` is even. -/
theorem thetaMultiplierPhase_eq_zero_iff (d : ℤ) : thetaMultiplierPhase d = 0 ↔ Even d := by
  refine ⟨fun h ↦ ?_, thetaMultiplierPhase_of_even⟩
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  obtain ⟨k, rfl⟩ := hodd
  rcases show (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 by omega with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm] at h
    exact one_ne_zero h
  · rw [thetaMultiplierPhase_three_mod_four hm] at h
    exact I_ne_zero h

/-- For odd `d`, `thetaMultiplierPhase d ≠ 0`. -/
theorem thetaMultiplierPhase_ne_zero {d : ℤ} (hd : Odd d) : thetaMultiplierPhase d ≠ 0 := by
  rw [ne_eq, thetaMultiplierPhase_eq_zero_iff]
  exact Int.not_even_iff_odd.mpr hd

@[simp]
theorem thetaMultiplierPhase_zero : thetaMultiplierPhase 0 = 0 :=
  thetaMultiplierPhase_of_even ⟨0, rfl⟩

@[simp]
theorem thetaMultiplierPhase_one : thetaMultiplierPhase 1 = 1 :=
  thetaMultiplierPhase_one_mod_four (by norm_num)

@[simp]
theorem thetaMultiplierPhase_neg_one : thetaMultiplierPhase (-1) = I :=
  thetaMultiplierPhase_three_mod_four (by norm_num)

/-- `thetaMultiplierPhase` depends only on the residue class modulo `4`. -/
theorem thetaMultiplierPhase_congr {d d' : ℤ} (h : d ≡ d' [ZMOD 4]) :
    thetaMultiplierPhase d = thetaMultiplierPhase d' := by
  simp only [thetaMultiplierPhase_def, Int.ModEq] at h ⊢
  rw [h]

/-- `thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ d : ℂ)` for every integer `d`. -/
theorem thetaMultiplierPhase_sq (d : ℤ) : thetaMultiplierPhase d ^ 2 = (ZMod.χ₄ d : ℂ) := by
  rw [ZMod.χ₄_int_eq_if_mod_four]
  rcases Int.even_or_odd d with hd | hd
  · rw [thetaMultiplierPhase_of_even hd, zero_pow two_ne_zero,
      ite_eq_left (by obtain ⟨k, rfl⟩ := hd; omega), Int.cast_zero]
  · obtain ⟨k, rfl⟩ := hd
    rw [ite_eq_right (by omega)]
    rcases show (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 by omega with hm | hm
    · rw [thetaMultiplierPhase_one_mod_four hm, ite_eq_left hm]
      norm_num
    · rw [thetaMultiplierPhase_three_mod_four hm, ite_eq_right (by omega)]
      norm_num

/-- For odd `d`, `‖thetaMultiplierPhase d‖ = 1`. -/
theorem norm_thetaMultiplierPhase {d : ℤ} (hd : Odd d) : ‖thetaMultiplierPhase d‖ = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rcases show (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 by omega with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm, norm_one]
  · rw [thetaMultiplierPhase_three_mod_four hm, norm_I]

/-- For odd `d`, `(thetaMultiplierPhase d)⁻¹ = if d % 4 = 1 then 1 else -I`. -/
theorem thetaMultiplierPhase_inv {d : ℤ} (hd : Odd d) :
    (thetaMultiplierPhase d)⁻¹ = if d % 4 = 1 then 1 else -I := by
  obtain ⟨k, rfl⟩ := hd
  rcases show (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 by omega with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm, ite_eq_left hm, inv_one]
  · rw [thetaMultiplierPhase_three_mod_four hm, ite_eq_right (by omega), inv_I]

/-- For odd `d`, `thetaMultiplierPhase (-d) = if d % 4 = 1 then I else 1`. -/
theorem thetaMultiplierPhase_neg {d : ℤ} (hd : Odd d) :
    thetaMultiplierPhase (-d) = if d % 4 = 1 then I else 1 := by
  obtain ⟨k, rfl⟩ := hd
  rcases show (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 by omega with hm | hm
  · rw [thetaMultiplierPhase_three_mod_four (by omega), ite_eq_left hm]
  · rw [thetaMultiplierPhase_one_mod_four (by omega), ite_eq_right (by omega)]

/-- For odd `d`, `thetaMultiplierPhase d * thetaMultiplierPhase (-d) = I`. -/
theorem thetaMultiplierPhase_mul_neg {d : ℤ} (hd : Odd d) :
    thetaMultiplierPhase d * thetaMultiplierPhase (-d) = I := by
  obtain ⟨k, rfl⟩ := hd
  rcases show (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 by omega with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm, thetaMultiplierPhase_three_mod_four (by omega),
      one_mul]
  · rw [thetaMultiplierPhase_three_mod_four hm, thetaMultiplierPhase_one_mod_four (by omega),
      mul_one]

/-- For odd `d`, `star (thetaMultiplierPhase d) = (thetaMultiplierPhase d)⁻¹`. -/
theorem star_thetaMultiplierPhase {d : ℤ} (hd : Odd d) :
    star (thetaMultiplierPhase d) = (thetaMultiplierPhase d)⁻¹ := by
  obtain ⟨k, rfl⟩ := hd
  rcases show (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 by omega with hm | hm
  · rw [thetaMultiplierPhase_one_mod_four hm, star_one, inv_one]
  · rw [thetaMultiplierPhase_three_mod_four hm, Complex.star_def, conj_I, inv_I]

/-! ### Evaluation of the level-`4` theta eta-quotient multiplier on `Γ₀(4)` -/

private lemma kroneckerSym_two_left_of_odd {d : ℤ} (hd : Odd d) :
    kroneckerSym 2 d = ZMod.χ₈ d := by
  rw [kroneckerSym_of_odd 2 hd, ite_eq_right (by omega), one_mul,
    jacobiSym.at_two (Int.natAbs_odd.mpr hd)]
  rcases le_or_gt 0 d with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr h.le)
    have hd' : d = -(n : ℤ) := by omega
    rw [hd', Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast, ZMod.χ₈_neg]

private lemma kroneckerSym_two_mul_e24_three_mul_sub_three {d : ℤ} (hd : Odd d) :
    (kroneckerSym 2 d : ℂ) * e24 (3 * d - 3) = (thetaMultiplierPhase d)⁻¹ := by
  rw [kroneckerSym_two_left_of_odd hd, thetaMultiplierPhase_inv hd]
  obtain ⟨m, r, hr0, hr8, rfl⟩ : ∃ m r : ℤ, 0 ≤ r ∧ r < 8 ∧ d = 8 * m + r :=
    ⟨d / 8, d % 8, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num), by omega⟩
  have hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
    obtain ⟨t, ht⟩ := hd
    omega
  have hχ₈ (a : ℤ) : ZMod.χ₈ ((8 * m + a : ℤ) : ZMod 8) = ZMod.χ₈ a := by
    rw [Int.cast_add, Int.cast_mul, show ((8 : ℤ) : ZMod 8) = 0 by decide, zero_mul, zero_add]
  have hcongr (a : ℤ) : e24 (3 * (8 * m + a) - 3) = e24 (3 * a - 3) :=
    e24_congr (Int.modEq_iff_dvd.mpr ⟨-m, by ring⟩)
  rw [hχ₈, hcongr]
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ite_eq_left (by omega), ZMod.χ₈_int_eq_if_mod_eight, show (3 * (1 : ℤ) - 3) = 0 by norm_num,
      e24_zero]
    norm_num
  · rw [ite_eq_right (by omega), ZMod.χ₈_int_eq_if_mod_eight, e24_def]
    norm_num
    rw [show (2 * π * I * 6 / 24 : ℂ) = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]
  · rw [ite_eq_left (by omega), ZMod.χ₈_int_eq_if_mod_eight, e24_def]
    norm_num
    rw [show (2 * π * I * 12 / 24 : ℂ) = π * I by ring, Complex.exp_pi_mul_I]
    ring
  · rw [ite_eq_right (by omega), ZMod.χ₈_int_eq_if_mod_eight, e24_def]
    norm_num
    rw [show (2 * π * I * 18 / 24 : ℂ) = π * I + π / 2 * I by ring, Complex.exp_add,
      Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
    ring

private lemma etaQuotientMultiplier_thetaExpVec_of_c_nonneg {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4)
    (hc : 0 ≤ γ 1 0) :
    etaQuotientMultiplier 4 thetaExpVec ⟨γ, hγ⟩ =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * kroneckerSym (γ 1 0) (γ 1 1) := by
  have h4c : (4 : ℤ) ∣ γ 1 0 := mem_Gamma0_iff_dvd.mp hγ
  obtain ⟨t, ht⟩ := h4c
  have ht0 : 0 ≤ t := by omega
  have heven : Even (γ 1 0) := ⟨2 * t, by omega⟩
  have hdo : Odd (γ 1 1) := γ.odd_apply_one_of_even_apply_zero heven
  have hcop : (γ 1 0).gcd (γ 1 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp
    ⟨-(γ 0 1), γ 0 0, by linear_combination γ.fin_two_mul_sub_mul_eq_one⟩
  have hcop_t : t.gcd (γ 1 1) = 1 := by
    have hdvd : t.gcd (γ 1 1) ∣ (γ 1 0).gcd (γ 1 1) :=
      Int.gcd_dvd_gcd_of_dvd_left _ ⟨4, by omega⟩
    rw [hcop] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  have hcop_2t : (2 * t).gcd (γ 1 1) = 1 := by
    have hdvd : (2 * t).gcd (γ 1 1) ∣ (γ 1 0).gcd (γ 1 1) :=
      Int.gcd_dvd_gcd_of_dvd_left _ ⟨2, by omega⟩
    rw [hcop] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  have hcop_2 : (2 : ℤ).gcd (γ 1 1) = 1 := by
    have hdvd : (2 : ℤ).gcd (γ 1 1) ∣ (γ 1 0).gcd (γ 1 1) :=
      Int.gcd_dvd_gcd_of_dvd_left _ ⟨2 * t, by omega⟩
    rw [hcop] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  have hfac (δ : (4 : ℕ).divisors) :
      etaMultiplier (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) ⟨γ, hγ⟩) ^
          thetaExpVec δ =
        ((kroneckerSym (γ 1 0 / δ) (γ 1 1) : ℂ) *
          e24 ((γ 0 0 + γ 1 1) * (γ 1 0 / δ) -
            (δ : ℤ) * γ 0 1 * γ 1 1 * ((γ 1 0 / δ) ^ 2 - 1) +
            3 * γ 1 1 - 3 - 3 * (γ 1 0 / δ) * γ 1 1)) ^ thetaExpVec δ := by
    have hcoe := coe_conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) ⟨γ, hγ⟩
    have hconj_c : 0 ≤ (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) ⟨γ, hγ⟩) 1 0 := by
      rw [hcoe]
      exact Int.ediv_nonneg hc (Int.natCast_nonneg δ)
    have hconj_d :
        Odd ((conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) ⟨γ, hγ⟩) 1 1) := by
      rw [hcoe]
      exact hdo
    rw [etaMultiplier_eq_kroneckerSym_mul_of_c_nonneg_of_odd_d _ hconj_c hconj_d]
    have h00 : (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) ⟨γ, hγ⟩) 0 0 = γ 0 0 := by
      rw [hcoe]; rfl
    have h01 : (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) ⟨γ, hγ⟩) 0 1 =
        (δ : ℤ) * γ 0 1 := by
      rw [hcoe]; rfl
    have h10 : (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) ⟨γ, hγ⟩) 1 0 =
        γ 1 0 / δ := by
      rw [hcoe]; rfl
    have h11 : (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) ⟨γ, hγ⟩) 1 1 = γ 1 1 := by
      rw [hcoe]; rfl
    rw [h00, h01, h10, h11, ← e24_def]
  rw [etaQuotientMultiplier_def, Finset.prod_congr rfl fun δ _ ↦ hfac δ,
    Finset.prod_attach (4 : ℕ).divisors fun δ : ℕ ↦ ((kroneckerSym (γ 1 0 / δ) (γ 1 1) : ℂ) *
      e24 ((γ 0 0 + γ 1 1) * (γ 1 0 / δ) - (δ : ℤ) * γ 0 1 * γ 1 1 * ((γ 1 0 / δ) ^ 2 - 1) +
        3 * γ 1 1 - 3 - 3 * (γ 1 0 / δ) * γ 1 1)) ^ thetaExpVec δ]
  rw [hdiv, Finset.prod_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)),
    Finset.prod_insert (by decide : (2 : ℕ) ∉ ({4} : Finset ℕ)), Finset.prod_singleton]
  have hr1 : thetaExpVec 1 = -2 := by decide
  have hr2 : thetaExpVec 2 = 5 := by decide
  have hr4 : thetaExpVec 4 = -2 := by decide
  rw [hr1, hr2, hr4, ht]
  norm_num only [Int.cast_one, one_mul, Int.cast_ofNat]
  rw [show (4 * t) / 1 = 4 * t by omega, show (4 * t) / 2 = 2 * t by omega,
    show (4 * t) / 4 = t by omega]
  have hcollect :
      (((kroneckerSym (4 * t) (γ 1 1) : ℂ) * e24 (((γ 0 0 + γ 1 1) * (4 * t) -
          γ 0 1 * γ 1 1 * ((4 * t) ^ 2 - 1) + 3 * γ 1 1 - 3 - 3 * (4 * t) * γ 1 1))) ^
          (-2 : ℤ) *
        (((kroneckerSym (2 * t) (γ 1 1) : ℂ) * e24 (((γ 0 0 + γ 1 1) * (2 * t) -
          2 * γ 0 1 * γ 1 1 * ((2 * t) ^ 2 - 1) + 3 * γ 1 1 - 3 - 3 * (2 * t) * γ 1 1))) ^
          (5 : ℤ) *
        ((kroneckerSym t (γ 1 1) : ℂ) * e24 (((γ 0 0 + γ 1 1) * t -
          4 * γ 0 1 * γ 1 1 * (t ^ 2 - 1) + 3 * γ 1 1 - 3 - 3 * t * γ 1 1))) ^ (-2 : ℤ))) =
      ((kroneckerSym (4 * t) (γ 1 1) : ℂ) ^ (-2 : ℤ) *
        (kroneckerSym (2 * t) (γ 1 1) : ℂ) ^ (5 : ℤ) *
        (kroneckerSym t (γ 1 1) : ℂ) ^ (-2 : ℤ)) *
        e24 (3 * γ 1 1 - 3) := by
    simp only [mul_zpow, ← e24_mul]
    rw [show ∀ a b c x y z : ℂ, (a * x) * ((b * y) * (c * z)) = (a * b * c) * (x * (y * z))
        by intros; ring,
      ← e24_add, ← e24_add]
    have hsum :
        (-2 : ℤ) * ((γ 0 0 + γ 1 1) * (4 * t) - γ 0 1 * γ 1 1 * ((4 * t) ^ 2 - 1) +
            3 * γ 1 1 - 3 - 3 * (4 * t) * γ 1 1) +
          ((5 : ℤ) * ((γ 0 0 + γ 1 1) * (2 * t) - 2 * γ 0 1 * γ 1 1 * ((2 * t) ^ 2 - 1) +
            3 * γ 1 1 - 3 - 3 * (2 * t) * γ 1 1) +
          (-2 : ℤ) * ((γ 0 0 + γ 1 1) * t - 4 * γ 0 1 * γ 1 1 * (t ^ 2 - 1) +
            3 * γ 1 1 - 3 - 3 * t * γ 1 1)) = 3 * γ 1 1 - 3 := by ring
    rw [hsum]
  rw [hcollect]
  have hcop_4t : (4 * t).gcd (γ 1 1) = 1 := by rwa [← ht]
  have hk_4t : ((kroneckerSym (4 * t) (γ 1 1) : ℤ) : ℂ) ^ (-2 : ℤ) = 1 := by
    rw [show (-2 : ℤ) = -(2 : ℕ) by rfl, zpow_neg, zpow_natCast,
      sq_intCast_kroneckerSym_eq_one hcop_4t, inv_one]
  have hk_t : ((kroneckerSym t (γ 1 1) : ℤ) : ℂ) ^ (-2 : ℤ) = 1 := by
    rw [show (-2 : ℤ) = -(2 : ℕ) by rfl, zpow_neg, zpow_natCast,
      sq_intCast_kroneckerSym_eq_one hcop_t, inv_one]
  have hk_2t : ((kroneckerSym (2 * t) (γ 1 1) : ℤ) : ℂ) ^ (5 : ℤ) =
      kroneckerSym (2 * t) (γ 1 1) := by
    rw [show (5 : ℤ) = (5 : ℕ) by rfl, zpow_natCast, show (5 : ℕ) = 2 * 2 + 1 by rfl,
      pow_add, pow_mul, sq_intCast_kroneckerSym_eq_one hcop_2t]
    simp
  have hk_eq : kroneckerSym (2 * t) (γ 1 1) =
      kroneckerSym 2 (γ 1 1) * kroneckerSym (4 * t) (γ 1 1) := by
    rcases eq_or_ne t 0 with rfl | ht_ne
    · have hd1 : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
        have hdet := γ.fin_two_mul_sub_mul_eq_one
        rw [ht, mul_zero, mul_zero, sub_zero] at hdet
        exact Int.eq_one_or_neg_one_of_mul_eq_one' hdet |>.elim (fun h ↦ .inl h.2)
          (fun h ↦ .inr h.2)
      rcases hd1 with h | h <;> simp [h]
    · rw [kroneckerSym_mul_left two_ne_zero ht_ne,
        show (4 * t : ℤ) = t * 2 ^ 2 by ring, kroneckerSym_mul_sq two_ne_zero hcop_2]
  rw [hk_4t, hk_t, hk_2t, hk_eq, one_mul, mul_one, Int.cast_mul, mul_right_comm,
    kroneckerSym_two_mul_e24_three_mul_sub_three hdo]

private lemma etaQuotientMultiplier_thetaExpVec (γ : Gamma0 4) :
    etaQuotientMultiplier 4 thetaExpVec γ =
      (thetaMultiplierPhase ((γ : SL(2, ℤ)) 1 1))⁻¹ *
        kroneckerSym ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := by
  rcases le_or_gt 0 ((γ : SL(2, ℤ)) 1 0) with hc | hc
  · exact etaQuotientMultiplier_thetaExpVec_of_c_nonneg γ.property hc
  have hc_pos : 0 ≤ (-(γ : SL(2, ℤ))) 1 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
    omega
  have hneg_mem : -(γ : SL(2, ℤ)) ∈ Gamma0 4 := by
    simpa using (Gamma0 4).mul_mem neg_one_mem_Gamma0 γ.property
  have h4c : (4 : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := mem_Gamma0_iff_dvd.mp γ.property
  have hdo : Odd ((γ : SL(2, ℤ)) 1 1) :=
    (γ : SL(2, ℤ)).odd_apply_one_of_even_apply_zero
      (even_iff_two_dvd.mpr (dvd_trans (by decide) h4c))
  have hrel : etaQuotientMultiplier 4 thetaExpVec γ =
      I * etaQuotientMultiplier 4 thetaExpVec ⟨-(γ : SL(2, ℤ)), hneg_mem⟩ := by
    rw [etaQuotientMultiplier_def, etaQuotientMultiplier_def]
    have hfac : ∀ δ : (4 : ℕ).divisors,
        etaMultiplier (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) γ) ^ thetaExpVec δ =
          I ^ thetaExpVec δ *
            etaMultiplier (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property)
              ⟨-(γ : SL(2, ℤ)), hneg_mem⟩) ^ thetaExpVec δ := by
      intro δ
      have hδ_pos : (0 : ℤ) < δ := Int.natCast_pos.mpr (Nat.pos_of_mem_divisors δ.property)
      have hδ_dvd : (δ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_divisors δ.property)) h4c
      have hneg_c_pos : 0 < (conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property)
          ⟨-(γ : SL(2, ℤ)), hneg_mem⟩) 1 0 := by
        rw [coe_conjScaleGamma0]
        exact Int.ediv_pos_of_pos_of_dvd (by simpa using hc) hδ_pos.le (dvd_neg.mpr hδ_dvd)
      have hconj_neg :
          -(conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) ⟨-(γ : SL(2, ℤ)), hneg_mem⟩) =
            conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) γ := by
        ext i j
        change (-((conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property)
          ⟨-(γ : SL(2, ℤ)), hneg_mem⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) i j =
          ((conjScaleGamma0 (Nat.dvd_of_mem_divisors δ.property) γ : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ) i j
        rw [Matrix.neg_apply, coe_conjScaleGamma0, coe_conjScaleGamma0]
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.SpecialLinearGroup.coe_neg, Int.neg_ediv_of_dvd hδ_dvd]
      rw [← hconj_neg, etaMultiplier_neg_of_c_pos _ hneg_c_pos, mul_zpow]
    rw [Finset.prod_congr rfl fun δ _ ↦ hfac δ, Finset.prod_mul_distrib,
      Finset.prod_zpow_eq_zpow_sum_of_isUnit _ I_ne_zero.isUnit,
      Finset.sum_attach (4 : ℕ).divisors thetaExpVec, sum_divisors_four_thetaExpVec, zpow_one]
  rw [hrel, etaQuotientMultiplier_thetaExpVec_of_c_nonneg hneg_mem hc_pos]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  have hd_ne : (γ : SL(2, ℤ)) 1 1 ≠ 0 := by
    rintro h0
    simp [h0] at hdo
  have hkron : kroneckerSym (-((γ : SL(2, ℤ)) 1 0)) (-((γ : SL(2, ℤ)) 1 1)) =
      (ZMod.χ₄ ((γ : SL(2, ℤ)) 1 1) : ℤ) *
        kroneckerSym ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := by
    rw [show -((γ : SL(2, ℤ)) 1 0) = (-1) * (γ : SL(2, ℤ)) 1 0 by ring,
      kroneckerSym_mul_left (by decide) hc.ne,
      show -((γ : SL(2, ℤ)) 1 1) = (-1) * (γ : SL(2, ℤ)) 1 1 by ring,
      kroneckerSym_mul_right ((γ : SL(2, ℤ)) 1 0) (by decide) hd_ne,
      show (-1 : ℤ) * (γ : SL(2, ℤ)) 1 1 = -((γ : SL(2, ℤ)) 1 1) by ring,
      kroneckerSym_neg_one_left_of_odd hdo.neg, Int.cast_neg, ZMod.χ₄_neg,
      kroneckerSym_neg_one_right, ite_eq_left hc]
    ring
  rw [hkron]
  have hphase : I * (thetaMultiplierPhase (-((γ : SL(2, ℤ)) 1 1)))⁻¹ *
      ((ZMod.χ₄ ((γ : SL(2, ℤ)) 1 1) : ℤ) : ℂ) =
      (thetaMultiplierPhase ((γ : SL(2, ℤ)) 1 1))⁻¹ := by
    rw [thetaMultiplierPhase_neg hdo, thetaMultiplierPhase_inv hdo]
    obtain ⟨k, hk⟩ := hdo
    rcases show (γ : SL(2, ℤ)) 1 1 % 4 = 1 ∨ (γ : SL(2, ℤ)) 1 1 % 4 = 3 by omega with hm | hm
    · rw [ite_eq_left hm, ite_eq_left hm, ZMod.χ₄_int_one_mod_four hm]
      norm_num
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ZMod.χ₄_int_three_mod_four hm]
      norm_num
  push_cast
  linear_combination (kroneckerSym ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) : ℂ) * hphase

/-! ### The theta automorphy factor `j(γ, z)` on `SL(2, ℤ)` and `Γ₀(4)` -/

/-- **The theta automorphy factor** `j(γ, z) = θ(2 · γ z) / θ(2 z)` for `γ ∈ SL(2, ℤ)` and
`z ∈ ℍ`. On `Γ₀(4)`, it equals Shimura's weight-`1/2` factor
`(thetaMultiplierPhase d)⁻¹ * kroneckerSym c d * Complex.sqrt (c z + d)`
(`thetaAutomorphyFactor_of_mem_Gamma0`). -/
noncomputable def thetaAutomorphyFactor (γ : SL(2, ℤ)) (z : ℍ) : ℂ :=
  jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / jacobiTheta (2 * (z : ℂ))

/-- Defining formula for `thetaAutomorphyFactor`. -/
theorem thetaAutomorphyFactor_def (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor γ z = jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / jacobiTheta (2 * (z : ℂ)) :=
  (rfl)

/-- The theta automorphy factor never vanishes on the upper half-plane. -/
@[simp]
theorem thetaAutomorphyFactor_ne_zero (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor γ z ≠ 0 :=
  div_ne_zero (jacobiTheta_ne_zero (by simpa using mul_pos two_pos (γ • z).im_pos))
    (jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos))

/-- Rewriting `θ(2 · γ z)` in terms of `thetaAutomorphyFactor γ z` and `θ(2 z)`. -/
theorem jacobiTheta_two_mul_smul_eq (γ : SL(2, ℤ)) (z : ℍ) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) =
      thetaAutomorphyFactor γ z * jacobiTheta (2 * (z : ℂ)) :=
  (div_mul_cancel₀ _ (jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos))).symm

/-- **Cocycle law** for `thetaAutomorphyFactor` on all of `SL(2, ℤ)`:
`j(γ₁ * γ₂, z) = j(γ₁, γ₂ • z) * j(γ₂, z)`. -/
theorem thetaAutomorphyFactor_mul (γ₁ γ₂ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor (γ₁ * γ₂) z =
      thetaAutomorphyFactor γ₁ (γ₂ • z) * thetaAutomorphyFactor γ₂ z := by
  have h₂ : jacobiTheta (2 * ((γ₂ • z : ℍ) : ℂ)) ≠ 0 :=
    jacobiTheta_ne_zero (by simpa using mul_pos two_pos (γ₂ • z).im_pos)
  rw [thetaAutomorphyFactor_def, thetaAutomorphyFactor_def, thetaAutomorphyFactor_def,
    mul_smul, div_mul_div_cancel₀ h₂]

@[simp]
theorem thetaAutomorphyFactor_one (z : ℍ) : thetaAutomorphyFactor 1 z = 1 := by
  rw [thetaAutomorphyFactor_def, one_smul,
    div_self (jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos))]

@[simp]
theorem thetaAutomorphyFactor_neg (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor (-γ) z = thetaAutomorphyFactor γ z := by
  have hsmul : (-γ) • z = γ • z :=
    ModularGroup.smul_eq_smul_of_eq_or_eq_neg (Or.inr rfl)
  rw [thetaAutomorphyFactor_def, hsmul, thetaAutomorphyFactor_def]

theorem thetaAutomorphyFactor_neg_one (z : ℍ) : thetaAutomorphyFactor (-1) z = 1 := by
  rw [thetaAutomorphyFactor_neg, thetaAutomorphyFactor_one]

/-- Inversion formula for the theta automorphy factor:
`thetaAutomorphyFactor γ⁻¹ (γ • z) = (thetaAutomorphyFactor γ z)⁻¹`. -/
theorem thetaAutomorphyFactor_inv (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor γ⁻¹ (γ • z) = (thetaAutomorphyFactor γ z)⁻¹ := by
  have h := thetaAutomorphyFactor_mul γ⁻¹ γ z
  rw [inv_mul_cancel, thetaAutomorphyFactor_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- `jacobiTheta` at `2 * z` is invariant under shifts by `2 * n` (`n : ℤ`). -/
private theorem jacobiTheta_two_mul_intCast_add (n : ℤ) (τ : ℂ) :
    jacobiTheta (2 * n + τ) = jacobiTheta τ := by
  simp only [jacobiTheta]
  refine tsum_congr fun k ↦ ?_
  rw [show π * I * (k : ℂ) ^ 2 * (2 * n + τ) =
      π * I * (k : ℂ) ^ 2 * τ + ((k ^ 2 * n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

@[simp]
theorem thetaAutomorphyFactor_T_zpow (n : ℤ) (z : ℍ) :
    thetaAutomorphyFactor (ModularGroup.T ^ n) z = 1 := by
  rw [thetaAutomorphyFactor_def, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd,
    ofReal_intCast, mul_add, jacobiTheta_two_mul_intCast_add,
    div_self (jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos))]

@[simp]
theorem thetaAutomorphyFactor_T (z : ℍ) : thetaAutomorphyFactor ModularGroup.T z = 1 := by
  simpa using thetaAutomorphyFactor_T_zpow 1 z

/-- **Shimura's theta transformation law** for `γ ∈ Γ₀(4)`:
`θ(2 · γ z) = ε_d⁻¹ · (c / d) · √(c z + d) · θ(2 z)`. -/
theorem jacobiTheta_two_mul_smul_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * kroneckerSym (γ 1 0) (γ 1 1) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) * jacobiTheta (2 * (z : ℂ)) := by
  rw [jacobiTheta_two_mul_eq_etaQuotient (γ • z).im_pos,
    jacobiTheta_two_mul_eq_etaQuotient z.im_pos,
    etaQuotient_smul 4 thetaExpVec ⟨γ, hγ⟩ z,
    sum_divisors_four_thetaExpVec, zpow_one,
    etaQuotientMultiplier_thetaExpVec ⟨γ, hγ⟩]

/-- **Shimura's formula for the theta automorphy factor on `Γ₀(4)`**:
`thetaAutomorphyFactor γ z = ε_d⁻¹ · (c / d) · √(c z + d)`. -/
theorem thetaAutomorphyFactor_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphyFactor γ z =
      (thetaMultiplierPhase (γ 1 1))⁻¹ * kroneckerSym (γ 1 0) (γ 1 1) *
        Complex.sqrt ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rw [thetaAutomorphyFactor_def, jacobiTheta_two_mul_smul_of_mem_Gamma0 hγ z,
    mul_div_cancel_right₀ _ (jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos))]

/-- **Square of the theta automorphy factor on `Γ₀(4)`**:
`thetaAutomorphyFactor γ z ^ 2 = χ₄(d) · (c z + d)`. -/
theorem thetaAutomorphyFactor_sq_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    thetaAutomorphyFactor γ z ^ 2 = (ZMod.χ₄ (γ 1 1) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  have h4c : (4 : ℤ) ∣ γ 1 0 := mem_Gamma0_iff_dvd.mp hγ
  have hdo : Odd (γ 1 1) :=
    γ.odd_apply_one_of_even_apply_zero (even_iff_two_dvd.mpr (dvd_trans (by decide) h4c))
  have hcop : (γ 1 0).gcd (γ 1 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp
    ⟨-(γ 0 1), γ 0 0, by linear_combination γ.fin_two_mul_sub_mul_eq_one⟩
  have hχ_inv : ((ZMod.χ₄ (γ 1 1) : ℤ) : ℂ)⁻¹ = ZMod.χ₄ (γ 1 1) := by
    obtain ⟨k, hk⟩ := hdo
    rcases show γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3 by omega with hm | hm
    · rw [ZMod.χ₄_int_one_mod_four hm]; norm_num
    · rw [ZMod.χ₄_int_three_mod_four hm]; norm_num
  rw [thetaAutomorphyFactor_of_mem_Gamma0 hγ z, mul_pow, mul_pow, inv_pow,
    thetaMultiplierPhase_sq, hχ_inv, sq_intCast_kroneckerSym_eq_one hcop, mul_one,
    Complex.sq_sqrt]

/-- On `Γ₁(4)`, the square of the theta automorphy factor simplifies to `c z + d`. -/
theorem thetaAutomorphyFactor_sq_of_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 4) (z : ℍ) :
    thetaAutomorphyFactor γ z ^ 2 = (γ 1 0 : ℂ) * z + γ 1 1 := by
  have h := thetaAutomorphyFactor_sq_of_mem_Gamma0 (Gamma1_le_Gamma0 4 hγ) z
  have hd : (4 : ℤ) ∣ γ 1 1 - 1 := (mem_Gamma1_iff_dvd_lowerRow.mp hγ).2
  have hχ : ZMod.χ₄ (γ 1 1) = 1 :=
    ZMod.χ₄_int_one_mod_four (by obtain ⟨k, hk⟩ := hd; omega)
  rwa [hχ, Int.cast_one, one_mul] at h

end TauCeti
