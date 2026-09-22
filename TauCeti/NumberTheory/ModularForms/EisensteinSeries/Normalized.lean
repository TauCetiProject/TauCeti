/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Raising
import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Normalized Eisenstein series with character

For a Dirichlet character `psi` modulo `u` and a primitive character `phi` modulo `v`, with the
parity required in weight `k`, this file normalizes the character Eisenstein series so that its
first Fourier coefficient is `1`. Thus its positive Fourier coefficients are exactly the twisted
divisor sums

`sigma_(k-1)^(psi,phi)(n) = sum_(d | n) psi(n / d) phi(d) d^(k-1)`.

The raised series `E_k^(psi,phi,t)(z) = E_k^(psi,phi)(t z)` has coefficients supported on the
multiples of `t`; at `n = t m > 0`, its coefficient is `sigma_(k-1)^(psi,phi)(m)`. These are the
canonical generators used for the Eisenstein subspace of a fixed nebentypus space.

The constant coefficient is intentionally left in terms of the raw lattice sum. Identifying it
with a generalized Bernoulli number is a separate special-value theorem for Dirichlet L-series.

## Main definitions

* `TauCeti.EisensteinSeries.normalizedCharEisensteinSeriesMF`: the series normalized to have
  first Fourier coefficient `1`.
* `TauCeti.EisensteinSeries.normalizedCharEisensteinSeriesMFRaise`: its level raise by `t`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 4.5, Theorem 4.5.1.
* [T. Miyake, *Modular forms*][miyake1989], Section 7.1.
-/

public section

noncomputable section

open AddChar Complex ZMod ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup
open UpperHalfPlane hiding I

open scoped MatrixGroups Real

namespace TauCeti.EisensteinSeries

variable {u v N t k : ℕ} [NeZero N]
  (psi : DirichletCharacter ℂ u) (phi : DirichletCharacter ℂ v)

/-- The character Eisenstein series scaled by the inverse of its expected first coefficient.

The scalar is the inverse of the first coefficient of `charEisensteinSeriesMF`; its Gauss-sum
factor is nonzero when `phi` is primitive, in which case the parity condition implies that the
result has first Fourier coefficient `1`. -/
def normalizedCharEisensteinSeriesMF (hk : 3 ≤ (k : ℤ)) (huv : u * v ∣ N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ) := by
  let _ : NeZero v := NeZero.of_dvd ((dvd_mul_left v u).trans huv)
  exact
    (2 * (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * gaussSum phi⁻¹ stdAddChar)⁻¹ •
      charEisensteinSeriesMF psi phi hk huv

/-- The positive Fourier coefficients of the normalized character Eisenstein series are the
twisted divisor sums `sigma_(k-1)^(psi,phi)`. -/
theorem qExpansion_normalizedCharEisensteinSeriesMF_coeff (hk : 3 ≤ (k : ℤ))
    (huv : u * v ∣ N) (hpar : psi (-1) * phi (-1) = (-1) ^ (k : ℤ))
    (hphi : phi.IsPrimitive)
    {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (normalizedCharEisensteinSeriesMF psi phi hk huv)).coeff n =
      DirichletCharacter.twistedDivisorSum (k - 1) psi phi n := by
  let _ : NeZero v := NeZero.of_dvd ((dvd_mul_left v u).trans huv)
  have hphiInv : (phi⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hphi
  have hgauss : gaussSum phi⁻¹ stdAddChar ≠ 0 := by
    intro hzero
    have hprod := DirichletCharacter.gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive
      hphiInv (isPrimitive_stdAddChar v)
    rw [hzero, zero_mul, ZMod.card] at hprod
    exact Nat.cast_ne_zero.mpr (NeZero.ne v) hprod.symm
  have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  have hfactorial : ((k - 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpi : (-2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hscale :
      2 * (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * gaussSum phi⁻¹ stdAddChar ≠
        0 := by
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero k hpi))
        (mul_ne_zero hfactorial (pow_ne_zero k hv))) hgauss
  rw [normalizedCharEisensteinSeriesMF, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul,
    qExpansion_charEisensteinSeriesMF_coeff_of_isPrimitive psi phi hk huv hpar hphi hn]
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hscale, one_mul]

/-- The normalized character Eisenstein series has first Fourier coefficient `1`. -/
@[simp]
theorem qExpansion_normalizedCharEisensteinSeriesMF_coeff_one (hk : 3 ≤ (k : ℤ))
    (huv : u * v ∣ N) (hpar : psi (-1) * phi (-1) = (-1) ^ (k : ℤ))
    (hphi : phi.IsPrimitive) :
    (qExpansion 1 (normalizedCharEisensteinSeriesMF psi phi hk huv)).coeff 1 = 1 := by
  rw [qExpansion_normalizedCharEisensteinSeriesMF_coeff psi phi hk huv hpar hphi one_ne_zero,
    DirichletCharacter.twistedDivisorSum_one]

/-- A normalized character Eisenstein series is nonzero. -/
theorem normalizedCharEisensteinSeriesMF_ne_zero (hk : 3 ≤ (k : ℤ))
    (huv : u * v ∣ N) (hpar : psi (-1) * phi (-1) = (-1) ^ (k : ℤ))
    (hphi : phi.IsPrimitive) :
    normalizedCharEisensteinSeriesMF psi phi hk huv ≠ 0 := by
  intro hzero
  have hcoeff := qExpansion_normalizedCharEisensteinSeriesMF_coeff_one
    psi phi hk huv hpar hphi
  rw [hzero] at hcoeff
  have : (0 : ℂ) = 1 := by
    simpa only [FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero] using hcoeff
  exact zero_ne_one this

/-- The normalized series has the same nebentypus as the raw character Eisenstein series. -/
theorem normalizedCharEisensteinSeriesMF_mem_modFormCharSpace (hk : 3 ≤ (k : ℤ))
    (huv : u * v ∣ N) :
    normalizedCharEisensteinSeriesMF psi phi hk huv ∈ modFormCharSpace k
      (psi.changeLevel ((dvd_mul_right u v).trans huv) *
        phi.changeLevel ((dvd_mul_left v u).trans huv)).toUnitHom := by
  rw [normalizedCharEisensteinSeriesMF]
  exact (modFormCharSpace k _).smul_mem _
    (charEisensteinSeriesMF_mem_modFormCharSpace psi phi hk huv)

/-- The level raise by `t` of the character Eisenstein series scaled by the inverse of its
expected first coefficient: `E_k^(psi,phi,t) = V_t E_k^(psi,phi)`. Under the parity and
primitivity hypotheses, its coefficient at index `t` is `1`. -/
def normalizedCharEisensteinSeriesMFRaise (t : ℕ) (hk : 3 ≤ (k : ℤ))
    (htuv : t * (u * v) ∣ N) : ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  exact ModularForm.levelRaise t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)
    (normalizedCharEisensteinSeriesMF psi phi hk dvd_rfl)

/-- The raised normalized character Eisenstein series is the base series evaluated at `t z`. -/
@[simp]
theorem normalizedCharEisensteinSeriesMFRaise_apply (hk : 3 ≤ (k : ℤ))
    (htuv : t * (u * v) ∣ N) (z : ℍ) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    normalizedCharEisensteinSeriesMFRaise psi phi t hk htuv z =
      normalizedCharEisensteinSeriesMF psi phi hk dvd_rfl (scaleGL t • z) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharEisensteinSeriesMFRaise, ModularForm.levelRaise_apply]

/-- The `q`-expansion of a raised normalized character Eisenstein series is obtained by
substituting `q ↦ q^t` in the `q`-expansion of the base series. -/
@[simp]
theorem qExpansion_normalizedCharEisensteinSeriesMFRaise (hk : 3 ≤ (k : ℤ))
    (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    qExpansion 1 (normalizedCharEisensteinSeriesMFRaise psi phi t hk htuv) =
      (qExpansion 1
        (normalizedCharEisensteinSeriesMF psi phi hk dvd_rfl)).expand t
          (NeZero.ne t) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharEisensteinSeriesMFRaise]
  exact ModularForm.qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _

/-- The Fourier coefficients of a raised normalized Eisenstein series are the twisted divisor
sums on indices divisible by `t`, and zero on the other positive indices. -/
theorem qExpansion_normalizedCharEisensteinSeriesMFRaise_coeff (hk : 3 ≤ (k : ℤ))
    (htuv : t * (u * v) ∣ N) (hpar : psi (-1) * phi (-1) = (-1) ^ (k : ℤ))
    (hphi : phi.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1
      (normalizedCharEisensteinSeriesMFRaise psi phi t hk htuv)).coeff n =
      if t ∣ n then DirichletCharacter.twistedDivisorSum (k - 1) psi phi (n / t) else 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharEisensteinSeriesMFRaise]
  rw [ModularForm.qExpansion_levelRaise_coeff
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)]
  split_ifs with htn
  · rw [qExpansion_normalizedCharEisensteinSeriesMF_coeff psi phi hk dvd_rfl hpar hphi]
    exact Nat.div_ne_zero_iff.mpr
      ⟨NeZero.ne t, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) htn⟩
  · rfl

/-- The first positive supported coefficient of a raised normalized Eisenstein series is `1`. -/
theorem qExpansion_normalizedCharEisensteinSeriesMFRaise_coeff_self (hk : 3 ≤ (k : ℤ))
    (htuv : t * (u * v) ∣ N) (hpar : psi (-1) * phi (-1) = (-1) ^ (k : ℤ))
    (hphi : phi.IsPrimitive) :
    (qExpansion 1
      (normalizedCharEisensteinSeriesMFRaise psi phi t hk htuv)).coeff t = 1 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  rw [qExpansion_normalizedCharEisensteinSeriesMFRaise_coeff psi phi hk htuv hpar hphi
      (NeZero.ne t)]
  simp [NeZero.pos t, DirichletCharacter.twistedDivisorSum_one]

/-- A raised normalized character Eisenstein series is nonzero. -/
theorem normalizedCharEisensteinSeriesMFRaise_ne_zero (hk : 3 ≤ (k : ℤ))
    (htuv : t * (u * v) ∣ N) (hpar : psi (-1) * phi (-1) = (-1) ^ (k : ℤ))
    (hphi : phi.IsPrimitive) :
    normalizedCharEisensteinSeriesMFRaise psi phi t hk htuv ≠ 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  intro hzero
  have hcoeff := qExpansion_normalizedCharEisensteinSeriesMFRaise_coeff_self
    psi phi hk htuv hpar hphi
  rw [hzero] at hcoeff
  have : (0 : ℂ) = 1 := by
    simpa only [FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero] using hcoeff
  exact zero_ne_one this

/-- The raised normalized Eisenstein series belongs to the target nebentypus space. -/
theorem normalizedCharEisensteinSeriesMFRaise_mem_modFormCharSpace (hk : 3 ≤ (k : ℤ))
    (htuv : t * (u * v) ∣ N) :
    normalizedCharEisensteinSeriesMFRaise psi phi t hk htuv ∈ modFormCharSpace k
      (psi.changeLevel ((dvd_mul_right u v).trans
          ((dvd_mul_left (u * v) t).trans htuv)) *
        phi.changeLevel ((dvd_mul_left v u).trans
          ((dvd_mul_left (u * v) t).trans htuv))).toUnitHom := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  have hbase := normalizedCharEisensteinSeriesMF_mem_modFormCharSpace
    (N := u * v) psi phi hk dvd_rfl
  have hraise := ModularForm.levelRaise_mem_modFormCharSpace_of_dvd htuv _ hbase
  rw [normalizedCharEisensteinSeriesMFRaise]
  have hpsi := DirichletCharacter.changeLevel_trans psi (dvd_mul_right u v)
    ((dvd_mul_left (u * v) t).trans htuv)
  have hphi := DirichletCharacter.changeLevel_trans phi (dvd_mul_left v u)
    ((dvd_mul_left (u * v) t).trans htuv)
  have hchar :
      (psi.changeLevel ((dvd_mul_right u v).trans
            ((dvd_mul_left (u * v) t).trans htuv)) *
          phi.changeLevel ((dvd_mul_left v u).trans
            ((dvd_mul_left (u * v) t).trans htuv))).toUnitHom =
        ((psi.changeLevel (dvd_mul_right u v) *
          phi.changeLevel (dvd_mul_left v u)).toUnitHom).comp
            (ZMod.unitsMap ((dvd_mul_left (u * v) t).trans htuv)) := by
    rw [hpsi, hphi, ← map_mul, DirichletCharacter.changeLevel_toUnitHom]
  rw [hchar]
  exact hraise

end TauCeti.EisensteinSeries
