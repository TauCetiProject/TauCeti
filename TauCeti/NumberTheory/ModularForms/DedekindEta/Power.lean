/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.NumberTheory.ModularForms.DedekindEta.Kronecker
import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Even powers of the eta function on principal congruence subgroups

The eta multiplier `ε(γ) = TauCeti.ModularForm.etaMultiplier γ` is the 24th root of unity with
`η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the upper half-plane. Squaring removes the square root:
`η(γ τ) ^ (2 k) = ε(γ) ^ (2 k) (c τ + d) ^ k η(τ) ^ (2 k)` for every integer `k`, so `η ^ (2 k)`
transforms in weight `k` with the character `ε ^ (2 k)` of `SL(2, ℤ)`.

This file determines principal congruence subgroups on which that character is trivial: for an
even integer `r` and `γ ∈ Γ(N)` with `24 ∣ r N`, `ε(γ) ^ r = 1`. Hence `η ^ (2 k)` is invariant
under the weight-`k` slash action of `Γ(N)` whenever `12 ∣ k N`, and `τ ↦ η(τ / m) ^ (2 k)` is
invariant under that of `Γ(m N)`. Two cases occur in the unbounded denominators theorem of
Calegari, Dimitrov and Tang: `η(τ / 2)²`, of weight `1` on `Γ(24)`, in its reduction to weight
zero, and `η⁸`, of weight `4` on `Γ(3)`, as the denominator of the cube root `E₄ / η⁸` of `j`.

Both hypotheses of the multiplier statement are needed. Since `ε(T) = e^{π i / 12}`,
`ε(T⁶)² = -1` with `T⁶ ∈ Γ(6)`, so `η²` is not invariant under `Γ(6)` and `η(τ / 2)²` not under
`Γ(12)`. For odd `r` the Kronecker symbol in `ε` survives: `γ = (113 80; 24 17) ∈ Γ(8)` has
`ε(γ)³ = -1`, although `24 ∣ 3 · 8`.

The proof reads `ε` off its Kronecker-symbol form (`etaMultiplier_eq_kroneckerSym_mul_of_even_c`,
`etaMultiplier_eq_kroneckerSym_mul_of_c_pos_of_odd_c`). The symbol is `±1` because the entries
`c` and `d` are coprime, so an even power removes it, and the exponential factor is
`e(r n / 24)` for an integer `n` divisible by `N`.

## Main results

* `TauCeti.ModularForm.eta_smul_zpow_two_mul`:
  `η(γ τ) ^ (2 k) = ε(γ) ^ (2 k) (c τ + d) ^ k η(τ) ^ (2 k)`.
* `TauCeti.ModularForm.eta_zpow_two_mul_slash`: `η ^ (2 k) ∣[k] γ = ε(γ) ^ (2 k) • η ^ (2 k)`.
* `TauCeti.ModularForm.etaMultiplier_mul_sq`: `ε(γ δ)² = ε(γ)² ε(δ)²`, so `ε²` is a character.
* `TauCeti.ModularForm.etaMultiplier_zpow_eq_one_of_mem_Gamma`: `ε(γ) ^ r = 1` for `γ ∈ Γ(N)`,
  `r` even and `24 ∣ r N`.
* `TauCeti.ModularForm.eta_zpow_two_mul_slash_of_mem_Gamma`: `η ^ (2 k)` is invariant under the
  weight-`k` slash action of `Γ(N)` when `12 ∣ k N`.
* `TauCeti.ModularForm.eta_div_zpow_two_mul_slash_of_mem_Gamma_of_dvd`,
  `TauCeti.ModularForm.eta_div_zpow_two_mul_slash_of_mem_Gamma`: `τ ↦ η(τ / m) ^ (2 k)` is
  invariant under the weight-`k` slash action of `γ = (a b; c d) ∈ Γ(N)` with `m N ∣ b`, in
  particular of `Γ(m N)`, when `12 ∣ k N`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), reduction to weight zero following (1.0.2), p.628, and (1.0.3).
* F. Strömberg, *Computation of Maass waveforms with non-trivial multiplier systems*,
  arXiv:math/0611146, Remark 2.5, for the Kronecker-symbol form of the multiplier.
-/

public section

open Complex ModularGroup
open CongruenceSubgroup (mem_Gamma_iff_dvd Gamma_zero_bot)
open scoped Real ModularForm MatrixGroups UpperHalfPlane

namespace TauCeti.ModularForm

/-! ### The transformation law of even powers -/

/-- **The transformation law of `η ^ (2 k)`**: for `γ = (a b; c d) ∈ SL(2, ℤ)` and an integer
`k`, `η(γ τ) ^ (2 k) = ε(γ) ^ (2 k) (c τ + d) ^ k η(τ) ^ (2 k)` on the upper half-plane. -/
theorem eta_smul_zpow_two_mul (γ : SL(2, ℤ)) (τ : ℍ) (k : ℤ) :
    η (γ • τ : ℍ) ^ (2 * k) =
      etaMultiplier γ ^ (2 * k) * ((γ 1 0 : ℂ) * τ + γ 1 1) ^ k * η τ ^ (2 * k) := by
  rw [eta_smul, mul_zpow, mul_zpow, zpow_mul (Complex.sqrt _), zpow_two, ← sq, Complex.sq_sqrt]

/-- `η ^ (2 k)` transforms in weight `k` with the character `ε ^ (2 k)`:
`η ^ (2 k) ∣[k] γ = ε(γ) ^ (2 k) • η ^ (2 k)` for every `γ ∈ SL(2, ℤ)`. -/
theorem eta_zpow_two_mul_slash (k : ℤ) (γ : SL(2, ℤ)) :
    (fun τ : ℍ ↦ η τ ^ (2 * k)) ∣[k] γ =
      etaMultiplier γ ^ (2 * k) • fun τ : ℍ ↦ η τ ^ (2 * k) := by
  ext τ
  have hden : ((γ 1 0 : ℂ) * τ + γ 1 1) ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
  rw [ModularForm.SL_slash_apply, eta_smul_zpow_two_mul, ModularGroup.denom_apply,
    Pi.smul_apply, smul_eq_mul, zpow_neg, mul_right_comm,
    mul_inv_cancel_right₀ (zpow_ne_zero _ hden)]

/-- **The square of the eta multiplier is a character**: `ε(γ δ)² = ε(γ)² ε(δ)²`, because `η²`
transforms in weight one with the multiplier `ε²`. -/
theorem etaMultiplier_mul_sq (γ δ : SL(2, ℤ)) :
    etaMultiplier (γ * δ) ^ 2 = etaMultiplier γ ^ 2 * etaMultiplier δ ^ 2 := by
  have h := eta_zpow_two_mul_slash 1 (γ * δ)
  rw [SlashAction.slash_mul, eta_zpow_two_mul_slash, _root_.ModularForm.SL_smul_slash,
    eta_zpow_two_mul_slash, smul_smul] at h
  have hI := congrFun h UpperHalfPlane.I
  simp only [Pi.smul_apply, smul_eq_mul, mul_one] at hI
  have hη : (η (UpperHalfPlane.I : ℂ)) ^ (2 : ℤ) ≠ 0 :=
    zpow_ne_zero _ (_root_.ModularForm.eta_ne_zero UpperHalfPlane.I.im_pos)
  have := mul_right_cancel₀ hη hI
  norm_num at this
  exact_mod_cast this.symm

/-! ### The multiplier on principal congruence subgroups -/

/-- The multiplier statement for even `c`, from the divisibilities of the entries. -/
private theorem etaMultiplier_zpow_eq_one_of_even_c {N r : ℤ} {γ : SL(2, ℤ)}
    (heven : Even (γ 1 0)) (hr : Even r) (hrN : 24 ∣ r * N) (hb : N ∣ γ 0 1) (hc : N ∣ γ 1 0)
    (hd : N ∣ γ 1 1 - 1) : etaMultiplier γ ^ r = 1 := by
  obtain ⟨m, rfl⟩ := hr.two_dvd
  rw [etaMultiplier_eq_kroneckerSym_mul_of_even_c γ heven, mul_zpow, zpow_mul, zpow_ofNat,
    sq_intCast_kroneckerSym_eq_one (Int.isCoprime_iff_gcd_eq_one.1 (γ.isCoprime_row 1)),
    one_zpow, one_mul, ← e24_def, ← e24_mul, e24_congr (Int.modEq_zero_iff_dvd.2
      (hrN.trans (mul_dvd_mul_left _ ?_))), e24_zero]
  have : N ∣ (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * (γ 1 1 * (γ 1 0 ^ 2 - 1)) +
      3 * (γ 1 1 - 1) - 3 * γ 1 1 * γ 1 0 :=
    (((hc.mul_left _).sub (hb.mul_right _)).add (hd.mul_left _)).sub (hc.mul_left _)
  convert this using 1
  ring

/-- The multiplier statement for odd `c > 0`, from the divisibilities of the entries. -/
private theorem etaMultiplier_zpow_eq_one_of_c_pos_of_odd_c {N r : ℤ} {γ : SL(2, ℤ)}
    (hpos : 0 < γ 1 0) (hodd : Odd (γ 1 0)) (hr : Even r) (hrN : 24 ∣ r * N) (hb : N ∣ γ 0 1)
    (hc : N ∣ γ 1 0) : etaMultiplier γ ^ r = 1 := by
  obtain ⟨m, rfl⟩ := hr.two_dvd
  rw [etaMultiplier_eq_kroneckerSym_mul_of_c_pos_of_odd_c γ hpos hodd, mul_zpow, zpow_mul,
    zpow_ofNat,
    sq_intCast_kroneckerSym_eq_one (Int.isCoprime_iff_gcd_eq_one.1 (γ.isCoprime_row 1).symm),
    one_zpow, one_mul, ← e24_def, ← e24_mul, e24_congr (Int.modEq_zero_iff_dvd.2
      (hrN.trans (mul_dvd_mul_left _ ?_))), e24_zero]
  have : N ∣ (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * (γ 1 1 * (γ 1 0 ^ 2 - 1)) - 3 * γ 1 0 :=
    ((hc.mul_left _).sub (hb.mul_right _)).sub (hc.mul_left _)
  convert this using 1
  ring

/-- **The eta multiplier on a principal congruence subgroup**: for an even integer `r` and
`γ ∈ Γ(N)` with `24 ∣ r N`, `ε(γ) ^ r = 1`. In particular `ε²` is trivial on `Γ(12)` and `ε⁸` on
`Γ(3)`. Neither hypothesis can be dropped: `ε(T⁶)² = -1` with `T⁶ ∈ Γ(6)`, and
`γ = (113 80; 24 17) ∈ Γ(8)` has `ε(γ)³ = -1`. -/
theorem etaMultiplier_zpow_eq_one_of_mem_Gamma {N : ℕ} {r : ℤ} (hr : Even r)
    (hrN : 24 ∣ r * N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    etaMultiplier γ ^ r = 1 := by
  obtain ⟨-, hb, hc, hd⟩ := mem_Gamma_iff_dvd.1 hγ
  rcases Int.even_or_odd (γ 1 0) with heven | hodd
  · exact etaMultiplier_zpow_eq_one_of_even_c heven hr hrN hb hc hd
  rcases lt_or_gt_of_ne (fun h ↦ by simp [h] at hodd : γ 1 0 ≠ 0) with hneg | hpos
  swap
  · exact etaMultiplier_zpow_eq_one_of_c_pos_of_odd_c hpos hodd hr hrN hb hc
  -- For `c < 0` pass to `-γ`, with `ε(γ) = i ε(-γ)`; here `N` is odd, so `4 ∣ r`.
  have hpos' : 0 < (-γ) 1 0 := by simpa using hneg
  have hodd' : Odd ((-γ) 1 0) := by simpa using hodd
  have h := etaMultiplier_neg_of_c_pos (-γ) hpos'
  rw [neg_neg] at h
  obtain ⟨s, rfl⟩ := hr
  have hN : Odd (N : ℤ) := Int.not_even_iff_odd.1 fun hN ↦
    Int.not_even_iff_odd.2 hodd (hN.two_dvd.trans hc |> even_iff_two_dvd.2)
  have hs : Even s := by
    have h2 : 2 ∣ s * N := by
      obtain ⟨t, ht⟩ := hrN
      exact ⟨6 * t, by linarith⟩
    rcases Int.even_mul.1 (even_iff_two_dvd.2 h2) with hs | hN'
    · exact hs
    · exact absurd hN' (Int.not_even_iff_odd.2 hN)
  rw [h, mul_zpow, etaMultiplier_zpow_eq_one_of_c_pos_of_odd_c hpos' hodd' ⟨s, rfl⟩ hrN
    (by simpa using hb) (by simpa using hc), mul_one]
  obtain ⟨u, rfl⟩ := hs
  rw [show u + u + (u + u) = 4 * u by ring, zpow_mul, show I ^ (4 : ℤ) = 1 by norm_num,
    one_zpow]

/-! ### Invariance of even powers of `η` -/

/-- **`η ^ (2 k)` on a principal congruence subgroup**: when `12 ∣ k N`, `η ^ (2 k)` is invariant
under the weight-`k` slash action of `Γ(N)`. For example `η²` has weight `1` on `Γ(12)` and `η⁸`
weight `4` on `Γ(3)`. -/
theorem eta_zpow_two_mul_slash_of_mem_Gamma {N : ℕ} {k : ℤ} (hkN : 12 ∣ k * N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    (fun τ : ℍ ↦ η τ ^ (2 * k)) ∣[k] γ = fun τ : ℍ ↦ η τ ^ (2 * k) := by
  rw [eta_zpow_two_mul_slash, etaMultiplier_zpow_eq_one_of_mem_Gamma (even_two_mul k)
    (by rw [mul_assoc]; exact mul_dvd_mul_left 2 hkN) hγ, one_smul]

/-- **`η(τ / m) ^ (2 k)` in weight `k`**: when `12 ∣ k N`, the function `τ ↦ η(τ / m) ^ (2 k)` is
invariant under the weight-`k` slash action of every `γ = (a b; c d) ∈ Γ(N)` with `m N ∣ b`. -/
theorem eta_div_zpow_two_mul_slash_of_mem_Gamma_of_dvd {m N : ℕ} [NeZero m] {k : ℤ}
    (hkN : 12 ∣ k * N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N)
    (hb : (m * N : ℤ) ∣ γ 0 1) :
    (fun τ : ℍ ↦ η (τ / m) ^ (2 * k)) ∣[k] γ = fun τ : ℍ ↦ η (τ / m) ^ (2 * k) := by
  obtain ⟨ha, -, hc, hd⟩ := mem_Gamma_iff_dvd.1 hγ
  obtain ⟨b', hb'⟩ := (dvd_mul_right (m : ℤ) N).trans hb
  -- `γ` is the `diag(m, 1)`-conjugate of `δ = (a b'; m c d)`, which again lies in `Γ(N)`.
  have hδ : conjInvScale m γ b' hb' ∈ CongruenceSubgroup.Gamma N := by
    refine mem_Gamma_iff_dvd.2 ⟨by simpa using ha, ?_, by simpa using hc.mul_left _,
      by simpa using hd⟩
    have : (m : ℤ) * N ∣ m * b' := hb' ▸ hb
    simpa using (mul_dvd_mul_iff_left (Int.natCast_ne_zero.2 (NeZero.ne m))).1 this
  -- Slashing by `diag(m, 1)` turns `τ ↦ η(τ / m) ^ (2 k)` into `m ^ (k - 1) η ^ (2 k)`.
  have hscale : (fun τ : ℍ ↦ η (τ / m) ^ (2 * k)) ∣[k] scaleGL m =
      (m : ℂ) ^ (k - 1) • fun τ : ℍ ↦ η τ ^ (2 * k) := by
    ext τ
    rw [slash_scaleGL_apply, coe_scaleGL_smul,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (NeZero.ne m)), Pi.smul_apply, smul_eq_mul]
  have h := slash_conjScale_eq_smul_of_slash_scaleGL _ _ (conjInvScale_apply_one_zero m γ b' hb')
    (z := 1) (by
      rw [hscale, one_smul]
      exact (ModularForm.SL_smul_slash k _ _ _).trans
        (congrArg _ (eta_zpow_two_mul_slash_of_mem_Gamma hkN hδ)))
  rw [conjScale_conjInvScale, one_smul] at h
  exact (ModularForm.SL_slash _ γ).trans h

/-- **`η(τ / m) ^ (2 k)` on a principal congruence subgroup**: when `12 ∣ k N`, the function
`τ ↦ η(τ / m) ^ (2 k)` is invariant under the weight-`k` slash action of `Γ(m N)`. For example
`η(τ / 2)²` has weight `1` on `Γ(24)`. -/
theorem eta_div_zpow_two_mul_slash_of_mem_Gamma {m N : ℕ} {k : ℤ} (hkN : 12 ∣ k * N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma (m * N)) :
    (fun τ : ℍ ↦ η (τ / m) ^ (2 * k)) ∣[k] γ = fun τ : ℍ ↦ η (τ / m) ^ (2 * k) := by
  rcases eq_or_ne m 0 with rfl | hm
  · -- `Γ(0)` is trivial.
    rw [zero_mul, Gamma_zero_bot, Subgroup.mem_bot] at hγ
    rw [hγ, SlashAction.slash_one]
  have : NeZero m := ⟨hm⟩
  exact eta_div_zpow_two_mul_slash_of_mem_Gamma_of_dvd hkN
    (CongruenceSubgroup.Gamma_le_Gamma_of_dvd (dvd_mul_left N m) hγ)
    (by exact_mod_cast (mem_Gamma_iff_dvd.1 hγ).2.1)

/-! ### Checks -/

/-- `ε²` is not trivial on `Γ(6)`: `ε(T⁶)² = -1`. -/
example : etaMultiplier (T ^ (6 : ℤ)) ^ 2 = -1 := by
  rw [etaMultiplier_T_zpow, ← Complex.exp_natCast_mul]
  convert Complex.exp_pi_mul_I using 2
  push_cast
  ring

/-- `ε³` is not trivial on `Γ(8)`, although `24 ∣ 3 · 8`: the Kronecker symbol `(24 / 17) = -1`
survives an odd power. -/
example :
    etaMultiplier (.mk !![113, 80; 24, 17] (by norm_num [Matrix.det_fin_two_of])) ^ 3 = -1 := by
  rw [etaMultiplier_eq_kroneckerSym_mul_of_even_c _ (by decide)]
  simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  have hk : kroneckerSym 24 17 = -1 := by
    rw [show (17 : ℤ) = ((17 : ℕ) : ℤ) by norm_num, kroneckerSym_eq_jacobiSym _ (by decide)]
    norm_num
  rw [hk, mul_pow, ← Complex.exp_natCast_mul]
  have : ((3 : ℕ) : ℂ) * (2 * π * I * (((113 + 17) * 24 - 80 * 17 * (24 ^ 2 - 1) + 3 * 17 - 3 -
      3 * 24 * 17 : ℤ) : ℂ) / 24) = (-97507 : ℤ) * (2 * π * I) := by
    push_cast
    ring
  rw [this, exp_int_mul_two_pi_mul_I]
  norm_num

end TauCeti.ModularForm
