/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LValues
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.QExpansion
import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Normalized weight-two Eisenstein series with character

For a Dirichlet character `ψ` modulo `u` and a primitive character `φ` modulo `v`, not both
trivial, with `ψ(-1) φ(-1) = 1`, this file normalizes the weight-two Eisenstein series with
character `G₂^{ψ,φ}` (`TauCeti.EisensteinSeries.charG2MF`) so that its first Fourier coefficient
is `1`. The normalized series `E₂^{ψ,φ}` lies in `M₂(N, ψφ)` and has the full `q`-expansion

`E₂^{ψ,φ} = δ_{u = 1} · (-B₂,φ / 4) + ∑_{n ≥ 1} σ₁^{ψ,φ}(n) qⁿ`,

where `B₂,φ` is the generalized Bernoulli number and `σ₁^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d` is
the twisted divisor sum. This is the weight-two case of the formula for
`TauCeti.EisensteinSeries.normalizedCharEisensteinSeriesMF` in weight `k ≥ 3`, whose constant
coefficient is `δ_{u = 1} · (-Bₖ,φ / (2k))`.

The raised series `E₂^{ψ,φ,t}(z) = E₂^{ψ,φ}(t z)`, at any level `N` with `t u v ∣ N`, lies in
`M₂(N, ψφ)`; it has the same constant coefficient, and at `n = t m > 0` its coefficient is
`σ₁^{ψ,φ}(m)`, the other positive coefficients being zero. For the trivial pair the weight-two
series is not modular, and `TauCeti.EisensteinSeries.correctedE2` takes its place.

## Main definitions

* `TauCeti.EisensteinSeries.normalizedCharG2MF`: `E₂^{ψ,φ}`, the series normalized to have first
  Fourier coefficient `1`.
* `TauCeti.EisensteinSeries.normalizedCharG2MFRaise`: its level raise `E₂^{ψ,φ,t}`.

## Main results

* `TauCeti.EisensteinSeries.qExpansion_normalizedCharG2MF_coeff`: the positive coefficients are
  the twisted divisor sums `σ₁^{ψ,φ}`.
* `TauCeti.EisensteinSeries.qExpansion_normalizedCharG2MF_coeff_zero`: the constant coefficient is
  `-B₂,φ / 4` when `u = 1`, and `0` otherwise.
* `TauCeti.EisensteinSeries.normalizedCharG2MFRaise_mem_modFormCharSpace`:
  `E₂^{ψ,φ,t} ∈ M₂(N, ψφ)`.
* `TauCeti.EisensteinSeries.qExpansion_normalizedCharG2MFRaise_coeff` and
  `TauCeti.EisensteinSeries.qExpansion_normalizedCharG2MFRaise_coeff_zero`: the coefficients of
  the raised series.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.6.
* [T. Miyake, *Modular forms*][miyake1989], §7.1, §7.2.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4, equation (4.1).
-/

public section

noncomputable section

open Complex AddChar ZMod ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup
open UpperHalfPlane hiding I

open scoped Real

namespace TauCeti.EisensteinSeries

variable {u v N t : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The normalized weight-two Eisenstein series with character `E₂^{ψ,φ}`: the series
`G₂^{ψ,φ}` scaled by the inverse of its expected first coefficient `-8 π² g(φ⁻¹) / v²`. When the
Gauss sum `g(φ⁻¹)` is nonzero (for instance when `φ` is primitive), `ψ` and `φ` are not both
trivial and `ψ(-1) φ(-1) = 1`, the result has first Fourier coefficient `1`. -/
def normalizedCharG2MF (huv : u * v ∣ N) : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2 :=
  haveI : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
  (-8 * π ^ 2 / v ^ 2 * gaussSum φ⁻¹ stdAddChar)⁻¹ • charG2MF ψ φ huv

/-- The normalized series is `G₂^{ψ,φ}` multiplied by the inverse of its expected first
coefficient. -/
theorem normalizedCharG2MF_def (huv : u * v ∣ N) :
    haveI : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
    normalizedCharG2MF ψ φ huv =
      (-8 * π ^ 2 / v ^ 2 * gaussSum φ⁻¹ stdAddChar)⁻¹ • charG2MF ψ φ huv := (rfl)

/-- The Gauss sum `g(φ⁻¹)` in the normalization is nonzero for primitive `φ`. -/
private lemma gaussSum_inv_ne_zero [NeZero v] (hφ : φ.IsPrimitive) :
    gaussSum φ⁻¹ stdAddChar ≠ 0 := by
  have hφinv : (φ⁻¹).IsPrimitive := by
    rwa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact DirichletCharacter.gaussSum_ne_zero_of_isPrimitive (Nat.cast_ne_zero.mpr (NeZero.ne v))
    hφinv (isPrimitive_stdAddChar v)

/-- The expected first coefficient `-8 π² g(φ⁻¹) / v²` of `G₂^{ψ,φ}` is nonzero when the Gauss
sum `g(φ⁻¹)` is. -/
private lemma normalizedCharG2_scale_ne_zero [NeZero v] (hg : gaussSum φ⁻¹ stdAddChar ≠ 0) :
    (-8 * π ^ 2 / v ^ 2 * gaussSum φ⁻¹ stdAddChar : ℂ) ≠ 0 := by
  refine mul_ne_zero (div_ne_zero ?_ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne v)))) hg
  simp [Real.pi_ne_zero]

/-- The generalized Bernoulli number `B₂,φ` of an odd primitive character vanishes: the integer
row sum `∑ φ⁻¹(n) n⁻²` is odd in `n`, so it vanishes, and it is a nonzero multiple of `B₂,φ`. -/
private lemma generalizedBernoulli_two_eq_zero_of_odd [NeZero v] (hφ : φ.IsPrimitive)
    (hodd : φ (-1) = -1) : φ.generalizedBernoulli 2 = 0 := by
  have hS : ∑' n : ℤ, φ⁻¹ (n : ZMod v) * (n : ℂ) ^ (-((2 : ℕ) : ℤ)) = 0 := by
    set f : ℤ → ℂ := fun n ↦ φ⁻¹ (n : ZMod v) * (n : ℂ) ^ (-((2 : ℕ) : ℤ))
    have hinv : φ⁻¹ (-1) = -1 := by
      rw [MulChar.inv_apply_eq_inv', hodd, inv_neg, inv_one]
    have hneg (n : ℤ) : f (-n) = -f n := by
      simp only [f, Int.cast_neg]
      rw [neg_eq_neg_one_mul (n : ZMod v), map_mul, hinv, neg_eq_neg_one_mul (n : ℂ), mul_zpow]
      norm_num
    have := (Equiv.neg ℤ).tsum_eq f
    simp only [Equiv.neg_apply, hneg, tsum_neg] at this
    linear_combination -this / 2
  have hB := φ.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli hφ le_rfl
  rw [hS, mul_zero, eq_comm, mul_eq_zero] at hB
  refine hB.resolve_left ?_
  simp [Real.pi_ne_zero, NeZero.ne v, Nat.factorial]

/-- **The positive coefficients of `E₂^{ψ,φ}`** are the twisted divisor sums
`σ₁^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d`. -/
theorem qExpansion_normalizedCharG2MF_coeff (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1)
    (hpar : ψ (-1) * φ (-1) = 1) (hφ : φ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (normalizedCharG2MF ψ φ huv)).coeff n =
      DirichletCharacter.twistedDivisorSum 1 ψ φ n := by
  let _ : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
  rw [normalizedCharG2MF_def, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, qExpansion_charG2MF_coeff_of_isPrimitive ψ φ huv h hpar hφ hn,
    smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (normalizedCharG2_scale_ne_zero φ (gaussSum_inv_ne_zero φ hφ)), one_mul]

/-- The normalized weight-two Eisenstein series with character has first Fourier coefficient `1`
as soon as the Gauss sum `g(φ⁻¹)` in its normalization is nonzero; `φ` need not be primitive. -/
theorem qExpansion_normalizedCharG2MF_coeff_one_of_gaussSum_ne_zero [NeZero v]
    (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1) (hpar : ψ (-1) * φ (-1) = 1)
    (hg : gaussSum φ⁻¹ stdAddChar ≠ 0) :
    (qExpansion 1 (normalizedCharG2MF ψ φ huv)).coeff 1 = 1 := by
  rw [normalizedCharG2MF_def, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, qExpansion_charG2MF_coeff ψ φ huv h hpar, ite_eq_right one_ne_zero,
    Nat.divisorsAntidiagonal_one, Finset.sum_singleton]
  simp only [Nat.cast_one, map_one, one_mul, mul_one, smul_eq_mul, neg_neg,
    DirichletCharacter.fourierTransform_eq_gaussSum_mulShift, AddChar.mulShift_one]
  exact inv_mul_cancel₀ (normalizedCharG2_scale_ne_zero φ hg)

/-- The normalized weight-two Eisenstein series with character has first Fourier
coefficient `1`. -/
@[simp]
theorem qExpansion_normalizedCharG2MF_coeff_one (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1)
    (hpar : ψ (-1) * φ (-1) = 1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharG2MF ψ φ huv)).coeff 1 = 1 :=
  haveI : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
  qExpansion_normalizedCharG2MF_coeff_one_of_gaussSum_ne_zero ψ φ huv h hpar
    (gaussSum_inv_ne_zero φ hφ)

/-- **The constant coefficient of `E₂^{ψ,φ}`** is `-B₂,φ / 4` when the first modulus is one, and
zero otherwise. Primitivity is needed only for the second character, and no parity condition is
needed: for the wrong parity both sides vanish. -/
-- Rewrite before simplification turns the zeroth coefficient into a constant coefficient.
@[simp↓]
theorem qExpansion_normalizedCharG2MF_coeff_zero (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1)
    (hφ : φ.IsPrimitive) :
    haveI : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
    (qExpansion 1 (normalizedCharG2MF ψ φ huv)).coeff 0 =
      if u = 1 then -φ.generalizedBernoulli 2 / 4 else 0 := by
  let _ : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
  obtain hpar | hpar := ne_or_eq (ψ (-1) * φ (-1)) 1
  · -- for the wrong parity the series is zero, and `u = 1` forces `φ` odd, so `B₂,φ = 0`
    rw [normalizedCharG2MF_def, charG2MF_eq_zero ψ φ huv hpar, smul_zero, FunLike.coe_zero,
      UpperHalfPlane.qExpansion_zero, map_zero]
    split_ifs with hu
    · subst u
      rw [Subsingleton.elim (-1 : ZMod 1) 1, map_one, one_mul] at hpar
      rw [generalizedBernoulli_two_eq_zero_of_odd φ hφ
        (φ.even_or_odd.resolve_left hpar), neg_zero, zero_div]
    · rfl
  rw [normalizedCharG2MF_def, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, qExpansion_charG2MF_coeff ψ φ huv h hpar, smul_eq_mul]
  simp only [↓reduceIte]
  split_ifs with hu
  · subst u
    have hψ (a : ZMod 1) : ψ a = 1 := by
      rw [Subsingleton.elim a 1, map_one]
    have hφpar : φ (-1) = 1 := by
      simpa only [hψ, one_mul] using hpar
    rw [hψ, one_mul,
      inv_mul_eq_iff_eq_mul₀ (normalizedCharG2_scale_ne_zero φ (gaussSum_inv_ne_zero φ hφ))]
    have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
    have hτ : gaussSum φ stdAddChar ≠ 0 :=
      DirichletCharacter.gaussSum_ne_zero_of_isPrimitive hv hφ (isPrimitive_stdAddChar v)
    apply mul_left_cancel₀ hτ
    -- the row sum is a generalized Bernoulli number, and `g(φ) g(φ⁻¹) = φ(-1) v = v`
    have hB := φ.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli hφ le_rfl
    have hprod :=
      DirichletCharacter.gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive hφ
        (isPrimitive_stdAddChar v)
    rw [ZMod.card, hφpar, one_mul] at hprod
    push_cast [Nat.factorial_two] at hB
    rw [hB]
    calc
      _ = (2 * π * I) ^ 2 * -φ.generalizedBernoulli 2 / (2 * v) := by
        field_simp
      _ = -8 * π ^ 2 / v ^ 2 * (gaussSum φ stdAddChar * gaussSum φ⁻¹ stdAddChar) *
          (-φ.generalizedBernoulli 2 / 4) := by
        rw [hprod, mul_pow, mul_pow, I_sq]
        field_simp
        ring
      _ = _ := by ring
  · rw [ψ.map_zero' hu, zero_mul, mul_zero]

/-- A normalized weight-two Eisenstein series with character is nonzero as soon as the Gauss sum
`g(φ⁻¹)` in its normalization is nonzero. -/
theorem normalizedCharG2MF_ne_zero_of_gaussSum_ne_zero [NeZero v] (huv : u * v ∣ N)
    (h : ψ ≠ 1 ∨ φ ≠ 1) (hpar : ψ (-1) * φ (-1) = 1) (hg : gaussSum φ⁻¹ stdAddChar ≠ 0) :
    normalizedCharG2MF ψ φ huv ≠ 0 := by
  intro hzero
  have hcoeff := qExpansion_normalizedCharG2MF_coeff_one_of_gaussSum_ne_zero ψ φ huv h hpar hg
  rw [hzero] at hcoeff
  simp only [FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero, zero_ne_one] at hcoeff

/-- A normalized weight-two Eisenstein series with character is nonzero. -/
theorem normalizedCharG2MF_ne_zero (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1)
    (hpar : ψ (-1) * φ (-1) = 1) (hφ : φ.IsPrimitive) : normalizedCharG2MF ψ φ huv ≠ 0 :=
  haveI : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
  normalizedCharG2MF_ne_zero_of_gaussSum_ne_zero ψ φ huv h hpar (gaussSum_inv_ne_zero φ hφ)

/-- **The nebentypus of `E₂^{ψ,φ}`**: `E₂^{ψ,φ} ∈ M₂(N, ψφ)`, the characters being raised to
level `N`. -/
theorem normalizedCharG2MF_mem_modFormCharSpace (huv : u * v ∣ N) :
    normalizedCharG2MF ψ φ huv ∈ modFormCharSpace 2
      (ψ.changeLevel (dvd_of_mul_right_dvd huv) *
        φ.changeLevel (dvd_of_mul_left_dvd huv)).toUnitHom := by
  rw [normalizedCharG2MF_def]
  exact (modFormCharSpace 2 _).smul_mem _ (charG2MF_mem_modFormCharSpace ψ φ huv)

/-! ### Raising the level -/

/-- The normalized weight-two Eisenstein series with character and raising parameter `t`:
`E₂^{ψ,φ,t} = V_t E₂^{ψ,φ}`, viewed at any level `N` divisible by `t u v`. The series is formed at
its natural level `u v` and raised directly to level `N`. -/
def normalizedCharG2MFRaise (t : ℕ) (htuv : t * (u * v) ∣ N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) 2 :=
  haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  ModularForm.levelRaise t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)
    (normalizedCharG2MF ψ φ dvd_rfl)

/-- The raised normalized series is the degeneracy image of the normalized series at its
natural level. -/
theorem normalizedCharG2MFRaise_eq_levelRaise (t : ℕ) (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    normalizedCharG2MFRaise ψ φ t htuv =
      ModularForm.levelRaise t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)
        (normalizedCharG2MF ψ φ dvd_rfl) := (rfl)

/-- The raised normalized series is `G₂^{ψ,φ,t}` multiplied by the inverse of the expected first
coefficient of `G₂^{ψ,φ}`. -/
theorem normalizedCharG2MFRaise_eq_smul (htuv : t * (u * v) ∣ N) :
    haveI : NeZero v :=
      NeZero.of_dvd ((dvd_mul_left v u).trans ((dvd_mul_left (u * v) t).trans htuv))
    normalizedCharG2MFRaise ψ φ t htuv =
      (-8 * π ^ 2 / v ^ 2 * gaussSum φ⁻¹ stdAddChar)⁻¹ • charG2MFRaise ψ φ t htuv := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharG2MFRaise_eq_levelRaise, normalizedCharG2MF_def, charG2MFRaise_eq_levelRaise,
    ← ModularForm.levelRaiseₗ_apply, ← ModularForm.levelRaiseₗ_apply, _root_.map_smul]

/-- The raised normalized series is the normalized series at its natural level evaluated at
`t z`. -/
@[simp]
theorem normalizedCharG2MFRaise_apply (htuv : t * (u * v) ∣ N) (z : ℍ) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    normalizedCharG2MFRaise ψ φ t htuv z = normalizedCharG2MF ψ φ dvd_rfl (scaleGL t • z) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharG2MFRaise_eq_levelRaise, ModularForm.levelRaise_apply]

/-- At `t = 1`, the raised normalized series is the normalized series at its natural level `u v`
restricted to level `N`. -/
@[simp]
theorem normalizedCharG2MFRaise_one (huv : u * v ∣ N) :
    haveI : NeZero (u * v) := NeZero.of_dvd huv
    normalizedCharG2MFRaise ψ φ 1 (by simpa using huv) =
      ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd huv)
        (normalizedCharG2MF ψ φ dvd_rfl) := by
  rw [normalizedCharG2MFRaise_eq_levelRaise, ModularForm.levelRaise_one]

/-- **The nebentypus of `E₂^{ψ,φ,t}`**: at every level `N` divisible by `t u v`,
`E₂^{ψ,φ,t} ∈ M₂(N, ψφ)`, with both characters raised directly to level `N`. -/
theorem normalizedCharG2MFRaise_mem_modFormCharSpace (htuv : t * (u * v) ∣ N) :
    normalizedCharG2MFRaise ψ φ t htuv ∈ modFormCharSpace 2
      (ψ.changeLevel ((dvd_mul_right u v).trans ((dvd_mul_left (u * v) t).trans htuv)) *
        φ.changeLevel
          ((dvd_mul_left v u).trans ((dvd_mul_left (u * v) t).trans htuv))).toUnitHom := by
  rw [normalizedCharG2MFRaise_eq_smul]
  exact (modFormCharSpace 2 _).smul_mem _ (charG2MFRaise_mem_modFormCharSpace ψ φ htuv)

/-- The `q`-expansion of `E₂^{ψ,φ,t}` is that of `E₂^{ψ,φ}` with `q ↦ q^t`. -/
@[simp]
theorem qExpansion_normalizedCharG2MFRaise (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    qExpansion 1 (normalizedCharG2MFRaise ψ φ t htuv) =
      (qExpansion 1 (normalizedCharG2MF ψ φ (N := u * v) dvd_rfl)).expand t (NeZero.ne t) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharG2MFRaise_eq_levelRaise]
  exact ModularForm.qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _

/-- The `q`-expansion of `E₂^{ψ,φ,t}` is supported on the multiples of `t`. -/
theorem isSupportedOnDvd_qExpansion_normalizedCharG2MFRaise (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    PowerSeries.IsSupportedOnDvd t (qExpansion 1 (normalizedCharG2MFRaise ψ φ t htuv)) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharG2MFRaise_eq_levelRaise]
  exact ModularForm.isSupportedOnDvd_qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _

/-- **The positive coefficients of `E₂^{ψ,φ,t}`** are the twisted divisor sums `σ₁^{ψ,φ}(n / t)`
on the indices divisible by `t`, and zero on the other positive indices. -/
theorem qExpansion_normalizedCharG2MFRaise_coeff (htuv : t * (u * v) ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1)
    (hpar : ψ (-1) * φ (-1) = 1) (hφ : φ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (normalizedCharG2MFRaise ψ φ t htuv)).coeff n =
      if t ∣ n then DirichletCharacter.twistedDivisorSum 1 ψ φ (n / t) else 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharG2MFRaise_eq_levelRaise, ModularForm.qExpansion_levelRaise_coeff
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)]
  split_ifs with htn
  · exact qExpansion_normalizedCharG2MF_coeff ψ φ dvd_rfl h hpar hφ
      (Nat.div_ne_zero_iff.mpr ⟨NeZero.ne t, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) htn⟩)
  · rfl

/-- The coefficient of `E₂^{ψ,φ,t}` at `t` is `1` as soon as the Gauss sum `g(φ⁻¹)` in its
normalization is nonzero. -/
theorem qExpansion_normalizedCharG2MFRaise_coeff_self_of_gaussSum_ne_zero [NeZero v]
    (htuv : t * (u * v) ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1) (hpar : ψ (-1) * φ (-1) = 1)
    (hg : gaussSum φ⁻¹ stdAddChar ≠ 0) :
    (qExpansion 1 (normalizedCharG2MFRaise ψ φ t htuv)).coeff t = 1 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [qExpansion_normalizedCharG2MFRaise, PowerSeries.coeff_expand, ite_eq_left dvd_rfl,
    Nat.div_self (NeZero.pos t)]
  exact qExpansion_normalizedCharG2MF_coeff_one_of_gaussSum_ne_zero ψ φ dvd_rfl h hpar hg

/-- The coefficient of `E₂^{ψ,φ,t}` at `t` is `1`. -/
theorem qExpansion_normalizedCharG2MFRaise_coeff_self (htuv : t * (u * v) ∣ N)
    (h : ψ ≠ 1 ∨ φ ≠ 1) (hpar : ψ (-1) * φ (-1) = 1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharG2MFRaise ψ φ t htuv)).coeff t = 1 :=
  haveI : NeZero v :=
    NeZero.of_dvd ((dvd_mul_left v u).trans ((dvd_mul_left (u * v) t).trans htuv))
  qExpansion_normalizedCharG2MFRaise_coeff_self_of_gaussSum_ne_zero ψ φ htuv h hpar
    (gaussSum_inv_ne_zero φ hφ)

/-- **The constant coefficient of `E₂^{ψ,φ,t}`** is that of `E₂^{ψ,φ}`: `-B₂,φ / 4` when the
first modulus is one, and zero otherwise, with no parity condition. -/
-- Rewrite before the level-raise q-expansion is expanded.
@[simp↓]
theorem qExpansion_normalizedCharG2MFRaise_coeff_zero (htuv : t * (u * v) ∣ N)
    (h : ψ ≠ 1 ∨ φ ≠ 1) (hφ : φ.IsPrimitive) :
    haveI : NeZero v :=
      NeZero.of_dvd ((dvd_mul_left v u).trans ((dvd_mul_left (u * v) t).trans htuv))
    (qExpansion 1 (normalizedCharG2MFRaise ψ φ t htuv)).coeff 0 =
      if u = 1 then -φ.generalizedBernoulli 2 / 4 else 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [qExpansion_normalizedCharG2MFRaise, PowerSeries.coeff_expand]
  simp only [dvd_zero, ↓reduceIte, Nat.zero_div]
  exact qExpansion_normalizedCharG2MF_coeff_zero ψ φ dvd_rfl h hφ

/-- A raised normalized weight-two Eisenstein series with character is nonzero as soon as the
Gauss sum `g(φ⁻¹)` in its normalization is nonzero. -/
theorem normalizedCharG2MFRaise_ne_zero_of_gaussSum_ne_zero [NeZero v] (htuv : t * (u * v) ∣ N)
    (h : ψ ≠ 1 ∨ φ ≠ 1) (hpar : ψ (-1) * φ (-1) = 1) (hg : gaussSum φ⁻¹ stdAddChar ≠ 0) :
    normalizedCharG2MFRaise ψ φ t htuv ≠ 0 := by
  intro hzero
  have hcoeff :=
    qExpansion_normalizedCharG2MFRaise_coeff_self_of_gaussSum_ne_zero ψ φ htuv h hpar hg
  rw [hzero] at hcoeff
  simp only [FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero, zero_ne_one] at hcoeff

/-- A raised normalized weight-two Eisenstein series with character is nonzero. -/
theorem normalizedCharG2MFRaise_ne_zero (htuv : t * (u * v) ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1)
    (hpar : ψ (-1) * φ (-1) = 1) (hφ : φ.IsPrimitive) :
    normalizedCharG2MFRaise ψ φ t htuv ≠ 0 :=
  haveI : NeZero v :=
    NeZero.of_dvd ((dvd_mul_left v u).trans ((dvd_mul_left (u * v) t).trans htuv))
  normalizedCharG2MFRaise_ne_zero_of_gaussSum_ne_zero ψ φ htuv h hpar (gaussSum_inv_ne_zero φ hφ)

end TauCeti.EisensteinSeries
