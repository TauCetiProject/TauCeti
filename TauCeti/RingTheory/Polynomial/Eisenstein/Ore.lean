/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Polynomial.DiscreteValuationRing
import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly

/-!
# Ore's conditions for Eisenstein polynomials over a discrete valuation ring

Let `R` be a discrete valuation ring with additive valuation
`v_R = IsDiscreteValuationRing.addVal R`.
For a degree `n` and wild exponent `j = a * n + b` with `a = j / n` and `b = j % n`, the pair
`(n, j)` is *Ore-admissible* (`TauCeti.IsOreAdmissible R n j`) when `0 < n` and either `b = 0` with
`a = v_R(n)`, or `0 < b` with `v_R(b) ≤ a` and `a + 1 ≤ v_R(n)` (reading `v_R(0) = ⊤`).

For a monic Eisenstein polynomial `f : R[X]` of positive degree `n` with uniformizer `ϖ`,
the derivative valuation infimum `⨅ i : Fin n, (n • v_R(f_{i+1} * (i+1)) + (i+1))` equals `j + n`
if and only if `IsOreAdmissible R n j` holds, `v_R(f_h) ≥ oreCoefficientDepth R n j h` for
`1 ≤ h < n`, and equality holds at `h = b` when `0 < b`
(`TauCeti.iInf_addVal_derivative_add_one_eq_iff`). Conversely, for every Ore-admissible `(n, j)`,
`monicOfCoeff` realizes these conditions (`X ^ n + ϖ` when `b = 0`, and
`X ^ n + ϖ ^ ν_b * X ^ b + ϖ` when `0 < b`), giving a separable Eisenstein polynomial over the
fraction field; in equal characteristic with `(n : R) = 0`, taking `j = n * (m - 1) + 1` for
`m ≥ 1` gives `j % n = 1` and `ν_1 = m`, recovering Serre's explicit family `X ^ n + ϖ ^ m * X + ϖ`
(Serre 1978, Remarque 1°).

## Main definitions

* `TauCeti.IsOreAdmissible R n j`: Ore's admissibility predicate for degree `n` and wild
  exponent `j` over a discrete valuation ring `R`.
* `TauCeti.oreCoefficientDepth R n j h`: the valuation lower bound
  `max(1, ⌊j / n⌋ + 1 + [h < j % n] - v_R(h))` imposed on the degree-`h` Eisenstein coefficient.

## Main results

* `TauCeti.isOreAdmissible_one_iff`, `TauCeti.isOreAdmissible_iff_eq_zero_of_isUnit`,
  `TauCeti.isOreAdmissible_iff_eq_zero_of_not_dvd`,
  `TauCeti.isOreAdmissible_iff_of_natCast_eq_zero`: specializations to degree `1`, the tame case,
  and equal characteristic `p ∣ n`.
* `TauCeti.iInf_addVal_derivative_add_one_eq_iff`: valuation criterion on Eisenstein coefficients
  for the shifted derivative valuation infimum to equal `j + n`.
* `TauCeti.IsOreAdmissible.derivative_ne_zero_of_isEisensteinAt`,
  `TauCeti.IsOreAdmissible.separable_map_of_isEisensteinAt`: separability over the fraction field.
* `TauCeti.IsOreAdmissible.exists_monic_isEisensteinAt`: coefficient-level realization of every
  Ore-admissible pair `(n, j)`.

## References

* Ø. Ore, *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. **99** (1928),
  84–117.
* M. Krasner, *Nombre des extensions d'un degré donné d'un corps p-adique*, Colloques
  Internationaux du CNRS **143**, Paris, 1966, 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Remarque 1°.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter III, §6, Proposition 13.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1.
-/

public section
noncomputable section

open Polynomial IsDiscreteValuationRing IsLocalRing

namespace TauCeti

open TauCeti.Polynomial (monicOfCoeff monic_monicOfCoeff natDegree_monicOfCoeff
  coeff_monicOfCoeff)

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable (R) in
/-- **Ore's admissibility conditions** on a degree `n` and wild exponent `j = a * n + b`
(`a = j / n`, `b = j % n`) over a discrete valuation ring `R`: `0 < n`, and either `b = 0` with
`a = v_R(n)`, or `0 < b` with `v_R(b) ≤ a` and `a + 1 ≤ v_R(n)`, where `v_R(m) = addVal R (m : R)`
takes the value `⊤` when `(m : R) = 0`. -/
def IsOreAdmissible (n j : ℕ) : Prop :=
  0 < n ∧
    ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal R (n : R)) ∨
      (0 < j % n ∧ addVal R ((j % n : ℕ) : R) ≤ (j / n : ℕ) ∧
        ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal R (n : R)))

/-- Unfolding `TauCeti.IsOreAdmissible`. -/
theorem isOreAdmissible_iff {n j : ℕ} :
    IsOreAdmissible R n j ↔
      0 < n ∧
        ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal R (n : R)) ∨
          (0 < j % n ∧ addVal R ((j % n : ℕ) : R) ≤ (j / n : ℕ) ∧
            ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal R (n : R))) := by
  rw [IsOreAdmissible]

namespace IsOreAdmissible

/-- An Ore-admissible pair has positive degree. -/
theorem pos {n j : ℕ} (h : IsOreAdmissible R n j) : 0 < n :=
  h.1

/-- An Ore-admissible pair satisfies `⌊j / n⌋ ≤ v_R(n)` in `ℕ∞`. -/
theorem div_le_addVal {n j : ℕ} (h : IsOreAdmissible R n j) :
    ((j / n : ℕ) : ℕ∞) ≤ addVal R (n : R) :=
  h.2.elim (fun ⟨_, heq⟩ ↦ heq.le) fun ⟨_, _, hle⟩ ↦ le_self_add.trans hle

end IsOreAdmissible

/-- Degree zero has no Ore-admissible wild exponents. -/
@[simp]
theorem not_isOreAdmissible_zero_left (j : ℕ) : ¬ IsOreAdmissible R 0 j :=
  fun h ↦ Nat.lt_irrefl 0 h.pos

/-- When `n ∣ j`, Ore admissibility reduces to `0 < n` and `j / n = v_R(n)`. -/
theorem isOreAdmissible_iff_of_mod_eq_zero {n j : ℕ} (hmod : j % n = 0) :
    IsOreAdmissible R n j ↔ 0 < n ∧ ((j / n : ℕ) : ℕ∞) = addVal R (n : R) := by
  simp [IsOreAdmissible, hmod]

/-- When `n ∤ j`, Ore admissibility reduces to `0 < n`, `v_R(j % n) ≤ j / n`, and
`j / n + 1 ≤ v_R(n)`. -/
theorem isOreAdmissible_iff_of_mod_pos {n j : ℕ} (hmod : 0 < j % n) :
    IsOreAdmissible R n j ↔
      0 < n ∧ addVal R ((j % n : ℕ) : R) ≤ (j / n : ℕ) ∧
        ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal R (n : R) := by
  simp [IsOreAdmissible, hmod, hmod.ne']

/-- In degree `1`, only `j = 0` is Ore-admissible. -/
@[simp]
theorem isOreAdmissible_one_iff {j : ℕ} : IsOreAdmissible R 1 j ↔ j = 0 := by
  rcases j with _ | j <;> simp [IsOreAdmissible]

/-- Wild exponent `0` is Ore-admissible for degree `n` exactly when `0 < n` and `n` is a unit of
`R`. -/
theorem isOreAdmissible_zero_right_iff {n : ℕ} :
    IsOreAdmissible R n 0 ↔ 0 < n ∧ IsUnit (n : R) := by
  simp [IsOreAdmissible, eq_comm (a := (0 : ℕ∞)), addVal_eq_zero_iff]

/-- When `n` is a unit of `R`, the only Ore-admissible wild exponent is `0`. -/
theorem isOreAdmissible_iff_eq_zero_of_isUnit {n j : ℕ} (hu : IsUnit (n : R)) :
    IsOreAdmissible R n j ↔ j = 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hu
  rw [IsOreAdmissible, addVal_eq_zero_iff.mpr hu]
  refine ⟨fun ⟨_, h⟩ ↦ ?_, ?_⟩
  · rcases h with ⟨hmod, hdiv⟩ | ⟨-, -, hle⟩
    · have hdiv0 : j / n = 0 := by exact_mod_cast hdiv
      have := Nat.div_add_mod j n
      rw [hdiv0, hmod, Nat.mul_zero] at this
      omega
    · simp at hle
  · rintro rfl; simp [hn]

/-- **The tame case of Ore's conditions**: when the residue characteristic of `R` does not divide
`n`, the unique Ore-admissible wild exponent is `0`. -/
theorem isOreAdmissible_iff_eq_zero_of_not_dvd {n j : ℕ}
    (hp : ¬ ringChar (ResidueField R) ∣ n) : IsOreAdmissible R n j ↔ j = 0 :=
  isOreAdmissible_iff_eq_zero_of_isUnit (isUnit_natCast_iff_not_dvd.mpr hp)

/-- **The equal-characteristic wild case of Ore's conditions**: when `(n : R) = 0`, `(n, j)` is
Ore-admissible if and only if `0 < n` and `(j % n : R) ≠ 0` (equivalently, `ringChar R ∤ j`). -/
theorem isOreAdmissible_iff_of_natCast_eq_zero {n j : ℕ} (hnR : (n : R) = 0) :
    IsOreAdmissible R n j ↔ 0 < n ∧ ((j % n : ℕ) : R) ≠ 0 := by
  rw [IsOreAdmissible, hnR, addVal_zero]
  refine and_congr_right fun hn ↦ ⟨?_, fun hbR ↦ ?_⟩
  · rintro (⟨-, htop⟩ | ⟨-, hvb, -⟩)
    · simp at htop
    · intro hb0
      exact ENat.natCast_ne_top _ (top_le_iff.mp (by rwa [hb0, addVal_zero] at hvb))
  · have hchar : ringChar R ≠ 0 := fun h0 ↦
      hn.ne' (zero_dvd_iff.mp (h0 ▸ (ringChar.spec R n).mp hnR))
    have hp : (ringChar R).Prime := CharP.char_prime_of_ne_zero R hchar
    have hcop : IsCoprime ((ringChar R : ℕ) : R) ((j % n : ℕ) : R) := by
      have hcopNat : Nat.Coprime (ringChar R) (j % n) :=
        hp.coprime_iff_not_dvd.mpr fun h ↦ hbR ((ringChar.spec R (j % n)).mpr h)
      simpa only [eq_intCast, Int.cast_natCast] using
        (Nat.isCoprime_iff_coprime.mpr hcopNat).map (Int.castRingHom R)
    rw [ringChar.Nat.cast_ringChar] at hcop
    refine .inr ⟨Nat.pos_of_ne_zero fun h ↦ hbR (by simp [h]), ?_, le_top⟩
    rw [addVal_eq_zero_iff.mpr (isCoprime_zero_left.mp hcop)]
    simp

variable (R) in
/-- The valuation lower bound `ν_h = max(1, ⌊j / n⌋ + 1 + [h < j % n] - v_R(h))` imposed on the
degree-`h` Eisenstein coefficient by wild exponent `j` in degree `n`. -/
def oreCoefficientDepth (n j h : ℕ) : ℕ :=
  max 1 ((((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) - addVal R (h : R)).toNat)

variable (R) in
/-- Unfolding `TauCeti.oreCoefficientDepth`. -/
theorem oreCoefficientDepth_def (n j h : ℕ) :
    oreCoefficientDepth R n j h =
      max 1 ((((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) - addVal R (h : R)).toNat) := by
  rw [oreCoefficientDepth]

variable (R) in
/-- Every Ore coefficient depth is at least `1`, so coefficients satisfying the depth bound lie in
`maximalIdeal R`. -/
theorem one_le_oreCoefficientDepth (n j h : ℕ) : 1 ≤ oreCoefficientDepth R n j h :=
  le_max_left _ _

variable (R) in
/-- At wild exponent `0`, every Ore coefficient depth is `1`. -/
@[simp]
theorem oreCoefficientDepth_zero_right (n h : ℕ) : oreCoefficientDepth R n 0 h = 1 :=
  (oreCoefficientDepth_def R n 0 h).trans (max_eq_left (ENat.toNat_le_of_le_natCast (by simp)))

variable (R) in
/-- Reading `oreCoefficientDepth` in `ℕ∞`: the truncation to `ℕ` is lossless because the numerator
is finite. -/
theorem natCast_oreCoefficientDepth (n j h : ℕ) :
    ((oreCoefficientDepth R n j h : ℕ) : ℕ∞) =
      max 1 (((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) - addVal R (h : R)) := by
  rw [oreCoefficientDepth, Nat.mono_cast.map_max, Nat.cast_one, ENat.natCast_toNat]
  exact ne_of_lt (tsub_le_self.trans_lt (ENat.natCast_lt_top _))

variable (R) in
/-- When `(h : R) = 0`, the `h`-th derivative term vanishes identically and the Ore coefficient
depth is `1`. -/
@[simp]
theorem oreCoefficientDepth_of_natCast_eq_zero (n j : ℕ) {h : ℕ} (hh : (h : R) = 0) :
    oreCoefficientDepth R n j h = 1 := by
  simp [oreCoefficientDepth, hh]

/-- Auxiliary arithmetic comparison at a lower Eisenstein index `1 ≤ h < n`: when `1 ≤ m`,
`(j / n + 1) * n + j % n ≤ n • (m + w) + h` in `ℕ∞` holds if and only if
`oreCoefficientDepth R n j h ≤ m` (where `w = addVal R (h : R)`). -/
private theorem le_nsmul_add_iff_oreCoefficientDepth_le {n j h : ℕ} (hn : 0 < n)
    (hhn : h < n) {m : ℕ∞} (hm1 : 1 ≤ m) :
    (((j / n + 1) * n + j % n : ℕ) : ℕ∞) ≤ n • (m + addVal R (h : R)) + (h : ℕ∞) ↔
      ((oreCoefficientDepth R n j h : ℕ) : ℕ∞) ≤ m := by
  have hb : j % n < n := Nat.mod_lt j hn
  rw [natCast_oreCoefficientDepth, max_le_iff]
  rcases eq_or_ne m ⊤ with rfl | hmt
  · cases n with | zero => omega | succ _ => simp
  rcases eq_or_ne (addVal R (h : R)) ⊤ with hwt | hwt
  · rw [hwt]
    cases n with | zero => omega | succ _ => simp [hm1]
  lift m to ℕ using hmt
  lift addVal R (h : R) to ℕ using hwt with w hw'
  rw [← ENat.natCast_sub, nsmul_eq_mul]
  norm_cast at hm1 ⊢
  simp only [hm1, true_and, Nat.mul_comm (j / n + 1) n]
  split_ifs with hhb <;> refine ⟨fun hle ↦ ?_, fun hle ↦ ?_⟩
  · by_contra hlt
    have := Nat.mul_le_mul_left n (by omega : m + w ≤ j / n + 1)
    omega
  · have := Nat.mul_le_mul_left n (by omega : j / n + 2 ≤ m + w)
    have : n * (j / n + 2) = n * (j / n + 1) + n := by ring
    omega
  · by_contra hlt
    have := Nat.mul_le_mul_left n (by omega : m + w + 1 ≤ j / n + 1)
    have : n * (m + w + 1) = n * (m + w) + n := by ring
    omega
  · have := Nat.mul_le_mul_left n (by omega : j / n + 1 ≤ m + w)
    omega

/-- Auxiliary arithmetic equality at a lower Eisenstein index `1 ≤ h < n`: when `1 ≤ m`,
`n • (m + w) + h = (j / n + 1) * n + j % n` holds if and only if `h = j % n`, `w ≤ j / n`, and
`m = oreCoefficientDepth R n j h` (where `w = addVal R (h : R)`). -/
private theorem nsmul_add_eq_iff {n j h : ℕ} (hn : 0 < n) (hhn : h < n)
    {m : ℕ∞} (hm1 : 1 ≤ m) :
    n • (m + addVal R (h : R)) + (h : ℕ∞) = (((j / n + 1) * n + j % n : ℕ) : ℕ∞) ↔
      h = j % n ∧ addVal R (h : R) ≤ (j / n : ℕ) ∧
        m = ((oreCoefficientDepth R n j h : ℕ) : ℕ∞) := by
  have hb : j % n < n := Nat.mod_lt j hn
  constructor
  · intro heq
    have hmt : m ≠ ⊤ := by
      rintro rfl
      cases n with
      | zero => omega
      | succ _ => exact ENat.natCast_ne_top _ (by rw [← heq]; simp)
    have hwt : addVal R (h : R) ≠ ⊤ := fun htop ↦ by
      rw [htop] at heq
      cases n with
      | zero => omega
      | succ _ => exact ENat.natCast_ne_top _ (by rw [← heq]; simp)
    lift m to ℕ using hmt
    lift addVal R (h : R) to ℕ using hwt with w hw'
    rw [nsmul_eq_mul] at heq
    norm_cast at hm1 heq
    have h1 := (Nat.div_mod_unique (a := (j / n + 1) * n + j % n) hn).mpr
      ⟨by rw [add_comm, heq], hhn⟩
    have h2 := (Nat.div_mod_unique (a := (j / n + 1) * n + j % n) hn).mpr
      ⟨by rw [add_comm, Nat.mul_comm], hb⟩
    obtain rfl : h = j % n := h1.2.symm.trans h2.2
    have := h1.1.symm.trans h2.1
    refine ⟨rfl, by exact_mod_cast (by omega : w ≤ j / n), ?_⟩
    rw [natCast_oreCoefficientDepth, ← hw', ite_eq_right (lt_irrefl _), ← ENat.natCast_sub,
      max_eq_right (by exact_mod_cast (by omega : 1 ≤ j / n + 1 + 0 - w))]
    norm_cast
    omega
  · rintro ⟨rfl, hw, rfl⟩
    rw [natCast_oreCoefficientDepth, ite_eq_right (lt_irrefl _)]
    have hwt : addVal R ((j % n : ℕ) : R) ≠ ⊤ :=
      ne_of_lt (hw.trans_lt (ENat.natCast_lt_top _))
    lift addVal R ((j % n : ℕ) : R) to ℕ using hwt with w hw'
    have hwle : w ≤ j / n := by exact_mod_cast hw
    rw [← ENat.natCast_sub, max_eq_right (by exact_mod_cast (by omega : 1 ≤ j / n + 1 + 0 - w)),
      nsmul_eq_mul]
    norm_cast
    have : j / n + 1 + 0 - w + w = j / n + 1 := by omega
    rw [this, Nat.mul_comm]

/-- Top-index simplification for the Eisenstein derivative valuation term at `i = n - 1`. -/
private theorem addVal_Eisenstein_top {n : ℕ} (hn : 0 < n) {f : R[X]}
    (hf : f.IsEisensteinAt (maximalIdeal R)) (hdeg : f.natDegree = n) :
    n • (addVal R (f.coeff ((n - 1) + 1)) +
        addVal R (((n - 1 : ℕ) + 1 : ℕ) : R)) + (((n - 1) + 1 : ℕ) : ℕ∞) =
      n • (addVal R (n : R) + 1) := by
  have hsub : n - 1 + 1 = n := by omega
  have hderiv : f.coeff ((n - 1) + 1) * (((n - 1 : ℕ) : R) + 1) =
      (derivative f).coeff (f.natDegree - 1) := by
    simp [hdeg, coeff_derivative]
  rw [Nat.cast_add_one, ← addVal_mul, hderiv,
    f.addVal_coeff_derivative_natDegree_sub_one_of_isUnit_leadingCoeff hf.isUnit_leadingCoeff,
    hdeg, hsub, nsmul_eq_mul, nsmul_eq_mul, mul_add, mul_one]

/-- Top-index equality condition for the Eisenstein derivative valuation term at `i = n - 1`. -/
private theorem addVal_Eisenstein_top_eq_iff {n j : ℕ} (hn : 0 < n) {f : R[X]}
    (hf : f.IsEisensteinAt (maximalIdeal R)) (hdeg : f.natDegree = n) :
    n • (addVal R (f.coeff ((n - 1) + 1)) +
        addVal R (((n - 1 : ℕ) + 1 : ℕ) : R)) + (((n - 1) + 1 : ℕ) : ℕ∞) =
        (((j / n + 1) * n + j % n : ℕ) : ℕ∞) ↔
      j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal R (n : R) := by
  have hb_lt : j % n < n := Nat.mod_lt j hn
  rw [addVal_Eisenstein_top hn hf hdeg]
  rcases eq_or_ne (addVal R (n : R)) ⊤ with hv | hv
  · rw [hv]
    cases n with
    | zero => omega
    | succ _ =>
      exact ⟨fun h ↦ absurd (by rw [← h]; simp) (ENat.natCast_ne_top _),
        fun ⟨_, h⟩ ↦ absurd h (ENat.natCast_ne_top _)⟩
  · lift addVal R (n : R) to ℕ using hv with v hv'
    rw [nsmul_eq_mul]
    norm_cast
    refine ⟨fun heq ↦ ?_, fun ⟨h0, heq⟩ ↦ by rw [heq, h0, add_zero, Nat.mul_comm]⟩
    have h1 := (Nat.div_mod_unique (a := (j / n + 1) * n + j % n) hn).mpr
      ⟨by rw [zero_add, heq], hn⟩
    have h2 := (Nat.div_mod_unique (a := (j / n + 1) * n + j % n) hn).mpr
      ⟨by rw [add_comm, Nat.mul_comm], hb_lt⟩
    exact ⟨h2.2.symm.trans h1.2, by have := h1.1.symm.trans h2.1; omega⟩

/-- Top-index inequality condition for the Eisenstein derivative valuation term at `i = n - 1`. -/
private theorem le_addVal_Eisenstein_top_iff {n j : ℕ} (hn : 0 < n) {f : R[X]}
    (hf : f.IsEisensteinAt (maximalIdeal R)) (hdeg : f.natDegree = n) :
    (((j / n + 1) * n + j % n : ℕ) : ℕ∞) ≤
        n • (addVal R (f.coeff ((n - 1) + 1)) +
            addVal R (((n - 1 : ℕ) + 1 : ℕ) : R)) + (((n - 1) + 1 : ℕ) : ℕ∞) ↔
      (j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) ≤ addVal R (n : R)) ∨
        (0 < j % n ∧ ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal R (n : R)) := by
  have hb_lt : j % n < n := Nat.mod_lt j hn
  rw [addVal_Eisenstein_top hn hf hdeg]
  rcases eq_or_ne (addVal R (n : R)) ⊤ with hv | hv
  · rw [hv]
    cases n with | zero => omega | succ _ => simp [Nat.eq_zero_or_pos (j % _)]
  · lift addVal R (n : R) to ℕ using hv with v hv'
    rw [nsmul_eq_mul]
    norm_cast
    rw [Nat.mul_comm (j / n + 1) n]
    rcases Nat.eq_zero_or_pos (j % n) with h0 | hpos
    · simp only [h0, add_zero, true_and, lt_self_iff_false, false_and, or_false,
        Nat.mul_le_mul_left_iff hn]
      omega
    · simp only [hpos.ne', false_and, hpos, true_and, false_or]
      refine ⟨fun hle ↦ ?_, fun hle ↦ ?_⟩
      · by_contra hgt
        have := Nat.mul_le_mul_left n (by omega : v + 1 ≤ j / n + 1)
        omega
      · have := Nat.mul_le_mul_left n (by omega : j / n + 2 ≤ v + 1)
        have : n * (j / n + 2) = n * (j / n + 1) + n := by ring
        omega

/-- Core algebraic equivalence: for an Eisenstein polynomial `f : R[X]` of positive degree `n`,
the shifted derivative infimum `⨅ i : Fin n, (n • v_R(f_{i+1} * (i+1)) + (i+1))` equals `j + n`
if and only if `IsOreAdmissible R n j` holds and the coefficients of `f` satisfy the Ore depth
bounds (with equality at `j % n` when `0 < j % n`). -/
theorem iInf_addVal_derivative_add_one_eq_iff {n j : ℕ} (hn : 0 < n) {f : R[X]}
    (hf : f.IsEisensteinAt (maximalIdeal R)) (hdeg : f.natDegree = n) :
    (⨅ i : Fin n, n • addVal R (f.coeff (i + 1) * (i + 1)) + ((i : ℕ) + 1 : ℕ∞)) =
        ((j + n : ℕ) : ℕ∞) ↔
      IsOreAdmissible R n j ∧
        (∀ h, 1 ≤ h → h < n → (oreCoefficientDepth R n j h : ℕ∞) ≤ addVal R (f.coeff h)) ∧
        (0 < j % n → addVal R (f.coeff (j % n)) = oreCoefficientDepth R n j (j % n)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hlt_b := Nat.mod_lt j hn
  have hj_decomp : j + n = (j / n + 1) * n + j % n := by
    have := Nat.div_add_mod j n; rw [Nat.mul_comm (j / n + 1) n, Nat.mul_add_one]; omega
  let T (i : Fin n) : ℕ∞ :=
    n • (addVal R (f.coeff ((i : ℕ) + 1)) + addVal R (((i : ℕ) + 1 : ℕ) : R)) +
      ((i : ℕ) + 1 : ℕ∞)
  let iTop : Fin n := ⟨n - 1, by omega⟩
  have hinf :
      (⨅ i : Fin n, n • addVal R (f.coeff (i + 1) * (i + 1)) + ((i : ℕ) + 1 : ℕ∞)) =
        ⨅ i : Fin n, T i := by
    refine iInf_congr fun i ↦ ?_
    dsimp only [T]
    rw [addVal_mul]
    norm_cast
  have hTop_eq := addVal_Eisenstein_top_eq_iff (j := j) hn hf hdeg
  have hTop_le := le_addVal_Eisenstein_top_iff (j := j) hn hf hdeg
  rw [hinf, hj_decomp]
  refine (ciInf_eq_iff T _).trans
    ⟨fun ⟨⟨i, hi⟩, hle⟩ ↦ ?_, fun ⟨hadm, hcoeff, hcrit⟩ ↦ ?_⟩
  · have hcoeff : ∀ h, 1 ≤ h → h < n →
        (oreCoefficientDepth R n j h : ℕ∞) ≤ addVal R (f.coeff h) := fun h hh1 hhn ↦ by
      let k : Fin n := ⟨h - 1, by omega⟩
      have hk : (k : ℕ) + 1 = h := by dsimp [k]; omega
      have hm1 : 1 ≤ addVal R (f.coeff h) := hf.one_le_addVal_coeff (by omega)
      exact (le_nsmul_add_iff_oreCoefficientDepth_le (j := j) hn hhn hm1).mp
        (by simpa only [T, ← Nat.cast_add_one (k : ℕ), hk] using hle k)
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.isLt) with hiTop | hiLow
    · rw [(Fin.ext (by dsimp [iTop]; omega) : i = iTop)] at hi
      have hi' := hTop_eq.mp (by simpa only [T, iTop, Nat.cast_add, Nat.cast_one] using hi)
      exact ⟨⟨hn, .inl hi'⟩, hcoeff, fun hb ↦ absurd hi'.1 hb.ne'⟩
    · have hm1 : 1 ≤ addVal R (f.coeff ((i : ℕ) + 1)) :=
        hf.one_le_addVal_coeff (hdeg ▸ hiLow)
      obtain ⟨hmod, hvb, heq_m⟩ := (nsmul_add_eq_iff (j := j) hn hiLow hm1).mp hi
      have hb_pos : 0 < j % n := by omega
      rcases hTop_le.mp (by simpa only [T, iTop, Nat.cast_add, Nat.cast_one] using hle iTop) with
        ⟨h0, -⟩ | ⟨-, hvn⟩
      · exact absurd h0 hb_pos.ne'
      · exact ⟨⟨hn, .inr ⟨hb_pos, hmod ▸ hvb, hvn⟩⟩, hcoeff, fun _ ↦ hmod ▸ heq_m⟩
  · refine ⟨?_, fun i ↦ ?_⟩
    · rcases hadm.2 with ⟨h0, heq⟩ | ⟨hb_pos, hvb, -⟩
      · exact ⟨iTop,
          by simpa only [T, iTop, Nat.cast_add, Nat.cast_one] using hTop_eq.mpr ⟨h0, heq⟩⟩
      · let ib : Fin n := ⟨j % n - 1, by omega⟩
        have hib : (ib : ℕ) + 1 = j % n := by dsimp [ib]; omega
        have hm1 : 1 ≤ addVal R (f.coeff (j % n)) := hf.one_le_addVal_coeff (by omega)
        refine ⟨ib, ?_⟩
        dsimp only [T]
        rw [← Nat.cast_add_one (ib : ℕ), hib]
        exact (nsmul_add_eq_iff (j := j) hn hlt_b hm1).mpr ⟨rfl, hvb, hcrit hb_pos⟩
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.isLt) with hiTop | hiLow
      · rw [(Fin.ext (by dsimp [iTop]; omega) : i = iTop)]
        simpa only [T, iTop, Nat.cast_add, Nat.cast_one] using hTop_le.mpr
          (hadm.2.imp (fun ⟨h0, heq⟩ ↦ ⟨h0, heq.le⟩) fun ⟨hp, _, hvn⟩ ↦ ⟨hp, hvn⟩)
      · have hm1 : 1 ≤ addVal R (f.coeff ((i : ℕ) + 1)) :=
          hf.one_le_addVal_coeff (hdeg ▸ hiLow)
        exact (le_nsmul_add_iff_oreCoefficientDepth_le (j := j) hn hiLow hm1).mpr
          (hcoeff ((i : ℕ) + 1) (Nat.succ_pos _) hiLow)

/-- Any Eisenstein polynomial `f : R[X]` of degree `n` witnessing an Ore-admissible wild
exponent `j` has nonzero derivative. -/
theorem IsOreAdmissible.derivative_ne_zero_of_isEisensteinAt {n j : ℕ}
    (hadm : IsOreAdmissible R n j) {f : R[X]} (hf : f.IsEisensteinAt (maximalIdeal R))
    (hdeg : f.natDegree = n)
    (hcoeff : ∀ h, 1 ≤ h → h < n → (oreCoefficientDepth R n j h : ℕ∞) ≤ addVal R (f.coeff h))
    (hcrit : 0 < j % n → addVal R (f.coeff (j % n)) = oreCoefficientDepth R n j (j % n)) :
    f.derivative ≠ 0 := by
  rw [← iInf_addVal_derivative_add_one_lt_top_iff hadm.pos hdeg,
    (iInf_addVal_derivative_add_one_eq_iff hadm.pos hf hdeg).mpr ⟨hadm, hcoeff, hcrit⟩]
  exact ENat.natCast_lt_top _

/-- Any Eisenstein polynomial `f : R[X]` of degree `n` whose coefficients satisfy the
Ore-admissibility criterion at `j` has separable image over any fraction field `K` of `R`,
including in positive characteristic. -/
theorem IsOreAdmissible.separable_map_of_isEisensteinAt {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {n j : ℕ} (hadm : IsOreAdmissible R n j) {f : R[X]}
    (hf : f.IsEisensteinAt (maximalIdeal R)) (hdeg : f.natDegree = n)
    (hcoeff : ∀ h, 1 ≤ h → h < n → (oreCoefficientDepth R n j h : ℕ∞) ≤ addVal R (f.coeff h))
    (hcrit : 0 < j % n → addVal R (f.coeff (j % n)) = oreCoefficientDepth R n j (j % n)) :
    (f.map (algebraMap R K)).Separable := by
  have hprim : f.IsPrimitive := isPrimitive_iff_isUnit_of_C_dvd.mpr fun r hr ↦
    isUnit_of_dvd_unit (by simpa using (C_dvd_iff_dvd_coeff r f).mp hr f.natDegree)
      hf.isUnit_leadingCoeff
  have hfirr : Irreducible f := hf.irreducible inferInstance hprim (hdeg ▸ hadm.pos)
  have hirr : Irreducible (f.map (algebraMap R K)) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hfirr
  refine (separable_iff_derivative_ne_zero hirr).mpr ?_
  rw [derivative_map, Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)]
  exact hadm.derivative_ne_zero_of_isEisensteinAt hf hdeg hcoeff hcrit

/-- Over any discrete valuation ring `R`, every Ore-admissible pair `(n, j)` admits a coefficient
tuple `c : Fin n → R` such that `monicOfCoeff c` is Eisenstein at `maximalIdeal R` and satisfies
the Ore depth bounds `oreCoefficientDepth R n j h ≤ addVal R ((monicOfCoeff c).coeff h)` for
`1 ≤ h < n`, with equality at `j % n` when `0 < j % n`. -/
theorem IsOreAdmissible.exists_monic_isEisensteinAt {n j : ℕ} (hadm : IsOreAdmissible R n j) :
    ∃ c : Fin n → R,
      (monicOfCoeff c).IsEisensteinAt (maximalIdeal R) ∧
      (∀ h, 1 ≤ h → h < n →
        (oreCoefficientDepth R n j h : ℕ∞) ≤ addVal R ((monicOfCoeff c).coeff h)) ∧
      (0 < j % n →
        addVal R ((monicOfCoeff c).coeff (j % n)) = oreCoefficientDepth R n j (j % n)) := by
  have hn : 0 < n := hadm.pos
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  have hϖ_mem : ϖ ∈ maximalIdeal R := hϖ.not_isUnit
  have hϖ_notMem : ϖ ∉ maximalIdeal R ^ 2 := by
    rw [TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, addVal_uniformizer hϖ]
    decide
  let ν := oreCoefficientDepth R n j (j % n)
  let c : Fin n → R := fun i ↦
    if (i : ℕ) = 0 then ϖ else if (i : ℕ) = j % n then ϖ ^ ν else 0
  refine ⟨c, ?_, fun h hh1 hhn ↦ ?_, fun hb_pos ↦ ?_⟩
  · refine (monic_monicOfCoeff c).isEisensteinAt_of_mem_of_notMem
      (maximalIdeal.isMaximal R).ne_top (fun {k} hk ↦ ?_) ?_
    · rw [natDegree_monicOfCoeff] at hk
      rw [coeff_monicOfCoeff c ⟨k, hk⟩]
      dsimp [c]
      split_ifs
      · exact hϖ_mem
      · exact Ideal.pow_mem_of_mem _ hϖ_mem ν (one_le_oreCoefficientDepth R n j (j % n))
      · exact (maximalIdeal R).zero_mem
    · rw [coeff_monicOfCoeff c ⟨0, hn⟩]
      simpa [c] using hϖ_notMem
  · rw [coeff_monicOfCoeff c ⟨h, hhn⟩]
    dsimp [c]
    rw [ite_eq_right (by omega : h ≠ 0)]
    split_ifs with hhb
    · subst hhb; rw [hϖ.addVal_pow]
    · simp
  · rw [coeff_monicOfCoeff c ⟨j % n, Nat.mod_lt j hn⟩]
    simp [c, hb_pos.ne', hϖ.addVal_pow, ν]

end TauCeti
