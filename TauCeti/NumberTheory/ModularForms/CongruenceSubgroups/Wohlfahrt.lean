/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.StrictLevel

import Mathlib.Tactic.LinearCombination
import TauCeti.Data.ZMod.Units

/-!
# Wohlfahrt's theorem (strict form)

Wohlfahrt's theorem characterizes congruence subgroups of `SL(2, ℤ)` in terms of their level: a
subgroup `Γ ≤ SL(2, ℤ)` with positive strict level (in particular, any finite-index subgroup) is a
congruence subgroup if and only if it contains the principal congruence subgroup `Γ(Γ.strictLevel)`.

The core step is the normal-closure reduction
`CongruenceSubgroup.Gamma_le_normalClosure_T_pow_sup_Gamma`: for every `N : ℕ` and every positive
modulus `M`, every matrix of `Γ(N)` lies in `⟨⟨T ^ N⟩⟩ ⊔ Γ(M)`. The proof is an elementary matrix
reduction due to Wohlfahrt (1964) and Kiming–Schütt–Verrill (2011):
1. Shift the upper-left entry `a` of `A ∈ Γ(N)` by left-multiplying by `T ^ (k N)` so that `a`
   becomes coprime to `M`.
2. Kill the off-diagonal entries modulo `M` by multiplying on the left by a lower shear
   `S T ^ (-m N) S⁻¹` and on the right by an upper shear `T ^ (n N)`, yielding a matrix diagonal
   modulo `M` whose reduction depends only on `a mod M`.
3. Apply the same diagonalization to the conjugate `L(-t) T ^ N L(t) ∈ ⟨⟨T ^ N⟩⟩ ∩ Γ(N)` whose
   upper-left entry `1 + N t` equals `a`; the two diagonalized matrices agree modulo `M`, so their
   ratio lies in `Γ(M)`.

Since `Γ.strictLevel ∣ 2 * Γ.withCenter.strictLevel`, the strict theorem immediately implies
Kiming–Schütt–Verrill's signed bound `Γ(2 * Γ.withCenter.strictLevel) ≤ Γ`. The subgroup
`{γ ∈ Γ(2) | γ 0 0 ≡ 1 (mod 4)}` witnesses that strict level `4` can genuinely double the signed
level `2` and that `Γ(Γ.withCenter.strictLevel) ≤ Γ` fails in general when `-I ∉ Γ`.

## Main results

* `CongruenceSubgroup.Gamma_le_normalClosure_T_pow_sup_Gamma`:
  `Γ(N) ≤ Subgroup.normalClosure {T ^ N} ⊔ Γ(M)` for every `N` and every `M ≠ 0`.
* `CongruenceSubgroup.normalClosure_T_pow_sup_Gamma_eq_Gamma_gcd`:
  `Subgroup.normalClosure {T ^ N} ⊔ Γ(M) = Γ(Nat.gcd N M)` for every `N` and every `M ≠ 0`.
* `CongruenceSubgroup.IsCongruenceSubgroup.Gamma_strictLevel_le`: every congruence subgroup `Γ`
  contains `Γ(Γ.strictLevel)`.
* `CongruenceSubgroup.isCongruenceSubgroup_iff_Gamma_strictLevel_le`: **strict Wohlfahrt's
  theorem** — when `Γ.strictLevel ≠ 0` (in particular for finite-index `Γ`),
  `IsCongruenceSubgroup Γ ↔ Γ(Γ.strictLevel) ≤ Γ`.
* `CongruenceSubgroup.IsCongruenceSubgroup.Gamma_two_mul_strictLevel_withCenter_le`: every
  congruence subgroup `Γ` contains `Γ(2 * Γ.withCenter.strictLevel)`.
* `CongruenceSubgroup.exists_isCongruenceSubgroup_strictLevel_eq_two_mul_withCenter`: concrete
  sharpness witness separating strict level `4` from signed level `2`.

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535,
  Theorem 2.
* I. Kiming, M. Schütt, and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. 83 (2011), 96–120, §3, Lemma 7, Proposition 3, and Remark 8.
-/

public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace CongruenceSubgroup

section NormalClosureReduction

/-- Every conjugate of `T ^ (k * N)` lies in the normal closure of `{T ^ N}`. -/
private lemma conj_T_zpow_mul_mem_normalClosure (N : ℕ) (σ : SL(2, ℤ)) (k : ℤ) :
    σ * ModularGroup.T ^ (k * (N : ℤ)) * σ⁻¹ ∈ Subgroup.normalClosure {ModularGroup.T ^ N} := by
  have hT : ModularGroup.T ^ (k * (N : ℤ)) = (ModularGroup.T ^ N) ^ k := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm]
  rw [hT]
  exact Subgroup.normalClosure_normal.conj_mem _
    (zpow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) k) σ

/-- The lower-triangular shear `!![1, 0; m, 1]`, realized as the conjugate `S * T ^ (-m) * S⁻¹`. -/
private def lowerShear (m : ℤ) : SL(2, ℤ) :=
  ModularGroup.S * ModularGroup.T ^ (-m) * ModularGroup.S⁻¹

private lemma coe_lowerShear (m : ℤ) :
    (lowerShear m : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; m, 1] := by
  rw [lowerShear, ModularGroup.S.coe_conj_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_S]

private lemma lowerShear_mul_mem_normalClosure (N : ℕ) (k : ℤ) :
    lowerShear (k * (N : ℤ)) ∈ Subgroup.normalClosure {ModularGroup.T ^ N} := by
  have h : -(k * (N : ℤ)) = (-k) * (N : ℤ) := by ring
  rw [lowerShear, h]
  exact conj_T_zpow_mul_mem_normalClosure N ModularGroup.S (-k)

/-- The conjugate `L(-t) * T ^ N * L(t)` in `⟨⟨T ^ N⟩⟩ ∩ Γ(N)` with upper-left entry `1 + N * t`. -/
private def diagMatch (N : ℕ) (t : ℤ) : SL(2, ℤ) :=
  lowerShear (-t) * ModularGroup.T ^ (N : ℤ) * (lowerShear (-t))⁻¹

private lemma coe_diagMatch (N : ℕ) (t : ℤ) :
    (diagMatch N t : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1 + (N : ℤ) * t, (N : ℤ); -(N : ℤ) * t ^ 2, 1 - (N : ℤ) * t] := by
  rw [diagMatch, (lowerShear (-t)).coe_conj_T_zpow]
  have h00 : (lowerShear (-t) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by simp [coe_lowerShear]
  have h10 : (lowerShear (-t) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -t := by simp [coe_lowerShear]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10]
  ring

private lemma diagMatch_mem_normalClosure (N : ℕ) (t : ℤ) :
    diagMatch N t ∈ Subgroup.normalClosure {ModularGroup.T ^ N} := by
  have h := conj_T_zpow_mul_mem_normalClosure N (lowerShear (-t)) 1
  rwa [one_mul] at h

private lemma diagMatch_mem_Gamma (N : ℕ) (t : ℤ) : diagMatch N t ∈ Gamma N := by
  rw [Gamma_mem]
  have hcoe := coe_diagMatch N t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [congr_fun₂ hcoe]

/-- Step 1 of the Wohlfahrt reduction: left-multiplying `A ∈ Γ(N)` by a suitable `T ^ (k N)`
makes its upper-left entry coprime to `M`. -/
private lemma exists_shift_isCoprime {N M : ℕ} [NeZero M] {A : SL(2, ℤ)} (hA : A ∈ Gamma N) :
    ∃ k : ℤ, IsCoprime ((ModularGroup.T ^ (k * (N : ℤ)) * A) 0 0) (M : ℤ) := by
  have hA00_N : IsCoprime (A 0 0) (N : ℤ) := by
    obtain ⟨r, hr⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 0 0) N).mp
      (by simpa using (Gamma_mem.mp hA).1.symm)
    exact ⟨1, -r, by linear_combination hr⟩
  have hA00_10 : IsCoprime (A 0 0) (A 1 0) :=
    ⟨A 1 1, -A 0 1, by linear_combination A.fin_two_mul_sub_mul_eq_one⟩
  set d : ℕ := ((N : ℤ) * A 1 0).natAbs
  have hd_cop : IsCoprime (A 0 0) (d : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact Int.isCoprime_iff_nat_coprime.mp (hA00_N.mul_right hA00_10)
  have hu : IsUnit ((A 0 0 : ℤ) : ZMod d) :=
    (ZMod.isUnit_intCast_iff_isCoprime (A 0 0) d).mpr hd_cop.symm
  obtain ⟨t, ht_cop, ht_mod⟩ := ZMod.exists_isCoprime_mul_intCast_eq M hu.unit
  have ht_M : IsCoprime t (M : ℤ) := by
    rw [Nat.cast_mul] at ht_cop
    exact ht_cop.of_mul_right_left
  have hdvd_d : (d : ℤ) ∣ t - A 0 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (A 0 0) t d).mp (by simpa using ht_mod.symm)
  obtain ⟨k, hk⟩ : (N : ℤ) * A 1 0 ∣ t - A 0 0 := Int.natAbs_dvd.mp hdvd_d
  refine ⟨k, ?_⟩
  have h00 : (ModularGroup.T ^ (k * (N : ℤ)) * A) 0 0 = t := by
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T_zpow,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -hk
  rwa [h00]

/-- Step 2 of the Wohlfahrt reduction: any `X ∈ Γ(N)` whose upper-left entry has inverse `u`
modulo `M` can be left- and right-multiplied by shears in `⟨⟨T ^ N⟩⟩` so that its reduction
modulo `M` is `!![X 0 0, 0; 0, u]`. -/
private lemma exists_diag_mod_of_mem_Gamma {N M : ℕ} {X : SL(2, ℤ)} (hX : X ∈ Gamma N)
    {u : ℤ} (hu : (u : ZMod M) * (X 0 0 : ZMod M) = 1) :
    ∃ L R : SL(2, ℤ), L ∈ Subgroup.normalClosure {ModularGroup.T ^ N} ∧
      R ∈ Subgroup.normalClosure {ModularGroup.T ^ N} ∧
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (L * X * R) :
        Matrix (Fin 2) (Fin 2) (ZMod M)) = !![(X 0 0 : ZMod M), 0; 0, (u : ZMod M)] := by
  obtain ⟨b', hb'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (X 0 1) N).mp (Gamma_mem.mp hX).2.1
  obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (X 1 0) N).mp (Gamma_mem.mp hX).2.2.1
  let L : SL(2, ℤ) := lowerShear (-(u * c') * (N : ℤ))
  let R : SL(2, ℤ) := ModularGroup.T ^ (-(u * b') * (N : ℤ))
  have hL : L ∈ Subgroup.normalClosure {ModularGroup.T ^ N} :=
    lowerShear_mul_mem_normalClosure N (-(u * c'))
  have hR : R ∈ Subgroup.normalClosure {ModularGroup.T ^ N} := by
    have h := conj_T_zpow_mul_mem_normalClosure N 1 (-(u * b'))
    rwa [one_mul, inv_one, mul_one] at h
  have h00 : ((L * X * R) 0 0 : ZMod M) = (X 0 0 : ZMod M) := by
    have h : (L * X * R) 0 0 = X 0 0 := by
      simp [L, R, coe_lowerShear, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two,
        vecMul, dotProduct]
    rw [h]
  have h01 : ((L * X * R) 0 1 : ZMod M) = 0 := by
    have h : (L * X * R) 0 1 = X 0 0 * (-(u * b') * (N : ℤ)) + X 0 1 := by
      simp [L, R, coe_lowerShear, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two,
        vecMul, dotProduct]
    rw [h, hb']
    push_cast
    linear_combination -((b' : ZMod M) * (N : ZMod M)) * hu
  have h10 : ((L * X * R) 1 0 : ZMod M) = 0 := by
    have h : (L * X * R) 1 0 = (-(u * c') * (N : ℤ)) * X 0 0 + X 1 0 := by
      simp [L, R, coe_lowerShear, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two,
        vecMul, dotProduct]
    rw [h, hc']
    push_cast
    linear_combination -((c' : ZMod M) * (N : ZMod M)) * hu
  have h11 : ((L * X * R) 1 1 : ZMod M) = (u : ZMod M) := by
    have hdet := Matrix.SpecialLinearGroup.intCast_fin_two_mul_sub_mul_eq_one (R := ZMod M)
      (L * X * R)
    rw [h00, h01, h10] at hdet
    linear_combination (u : ZMod M) * hdet - ((L * X * R) 1 1 : ZMod M) * hu
  refine ⟨L, R, hL, hR, ?_⟩
  ext i j
  rw [SL_reduction_mod_hom_val]
  fin_cases i <;> fin_cases j <;> simp [-coe_mul, h00, h01, h10, h11]

/-- **Wohlfahrt's normal-closure congruence reduction**: for every `N : ℕ` and every positive
modulus `M`, every matrix of `Γ(N)` lies in `⟨⟨T ^ N⟩⟩ ⊔ Γ(M)`. -/
theorem Gamma_le_normalClosure_T_pow_sup_Gamma (N M : ℕ) [NeZero M] :
    Gamma N ≤ Subgroup.normalClosure {ModularGroup.T ^ N} ⊔ Gamma M := by
  let K := Subgroup.normalClosure {ModularGroup.T ^ N}
  let Δ := K ⊔ Gamma M
  have hK_le : K ≤ Δ := le_sup_left
  have hM_le : Gamma M ≤ Δ := le_sup_right
  intro A hA
  obtain ⟨k, hk_cop⟩ := exists_shift_isCoprime (M := M) hA
  let S_k : SL(2, ℤ) := ModularGroup.T ^ (k * (N : ℤ))
  have hSk_K : S_k ∈ K := by
    have h := conj_T_zpow_mul_mem_normalClosure N 1 k
    rwa [one_mul, inv_one, mul_one] at h
  have hSk_Γ : S_k ∈ Gamma N := by
    simpa [S_k] using ModularGroup_T_pow_mem_Gamma (N : ℤ) (k * (N : ℤ)) (dvd_mul_left _ _)
  let A₁ : SL(2, ℤ) := S_k * A
  have hA₁_Γ : A₁ ∈ Gamma N := mul_mem hSk_Γ hA
  obtain ⟨u, v, huv⟩ := hk_cop
  have hu : (u : ZMod M) * (A₁ 0 0 : ZMod M) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod M) huv
    push_cast at h
    simpa [A₁, S_k] using h
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A₁ 0 0) N).mp
    (by simpa using (Gamma_mem.mp hA₁_Γ).1.symm)
  let C : SL(2, ℤ) := diagMatch N t
  have hC00 : C 0 0 = A₁ 0 0 := by
    have h := congr_fun₂ (coe_diagMatch N t) 0 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero] at h
    linear_combination h - ht
  obtain ⟨L₁, R₁, hL₁, hR₁, hdiag₁⟩ := exists_diag_mod_of_mem_Gamma hA₁_Γ hu
  obtain ⟨L₂, R₂, hL₂, hR₂, hdiag₂⟩ :=
    exists_diag_mod_of_mem_Gamma (diagMatch_mem_Gamma N t) (hC00.symm ▸ hu)
  have hmod : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (L₁ * A₁ * R₁) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (L₂ * C * R₂) :=
    Subtype.ext (by rw [hdiag₁, hdiag₂, hC00])
  have hratio : (L₁ * A₁ * R₁) * (L₂ * C * R₂)⁻¹ ∈ Gamma M := by
    rw [Gamma_mem', map_mul, map_inv, hmod, mul_inv_cancel]
  have hX₂_Δ : L₂ * C * R₂ ∈ Δ :=
    mul_mem (mul_mem (hK_le hL₂) (hK_le (diagMatch_mem_normalClosure N t))) (hK_le hR₂)
  have hX₁_Δ : L₁ * A₁ * R₁ ∈ Δ := by
    have h := mul_mem (hM_le hratio) hX₂_Δ
    rwa [inv_mul_cancel_right] at h
  have hA₁_Δ : A₁ ∈ Δ := by
    have h := mul_mem (mul_mem (inv_mem (hK_le hL₁)) hX₁_Δ) (inv_mem (hK_le hR₁))
    simpa [mul_assoc] using h
  have hA_Δ : A ∈ Δ := by
    have h := mul_mem (inv_mem (hK_le hSk_K)) hA₁_Δ
    simpa [A₁, mul_assoc] using h
  exact hA_Δ

/-- For every `N : ℕ` and every `M ≠ 0`, joining the normal closure of `T ^ N` with `Γ(M)`
yields `Γ(Nat.gcd N M)`. -/
theorem normalClosure_T_pow_sup_Gamma_eq_Gamma_gcd (N M : ℕ) [NeZero M] :
    Subgroup.normalClosure {ModularGroup.T ^ N} ⊔ Gamma M = Gamma (Nat.gcd N M) := by
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ (Gamma_le_Gamma_of_dvd (Nat.gcd_dvd_right N M))
    rw [Subgroup.normalClosure_T_pow_le_iff, strictLevel_Gamma]
    exact Nat.gcd_dvd_left N M
  · have : (Gamma M).Normal := Gamma_normal M
    refine (Gamma_le_normalClosure_T_pow_sup_Gamma (Nat.gcd N M) M).trans
      (sup_le ?_ le_sup_right)
    refine Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
    have hbez : (Nat.gcd N M : ℤ) = (N : ℤ) * Nat.gcdA N M + (M : ℤ) * Nat.gcdB N M :=
      Nat.gcd_eq_gcd_ab N M
    have hpow : ModularGroup.T ^ Nat.gcd N M =
        (ModularGroup.T ^ N) ^ Nat.gcdA N M * (ModularGroup.T ^ M) ^ Nat.gcdB N M := by
      rw [← zpow_natCast, hbez, _root_.zpow_add, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
        ← _root_.zpow_mul]
    rw [SetLike.mem_coe, hpow]
    refine mul_mem ?_ ?_
    · exact Subgroup.mem_sup_left
        (zpow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) _)
    · have hTM : ModularGroup.T ^ M ∈ Gamma M := by
        simpa using ModularGroup_T_pow_mem_Gamma (M : ℤ) (M : ℤ) dvd_rfl
      exact Subgroup.mem_sup_right (zpow_mem hTM _)

end NormalClosureReduction

/-! ### Strict Wohlfahrt's theorem -/

/-- **Strict Wohlfahrt's theorem (forward direction)**: every congruence subgroup `Γ ≤ SL(2, ℤ)`
contains the principal congruence subgroup of level `Γ.strictLevel`. -/
theorem IsCongruenceSubgroup.Gamma_strictLevel_le {Γ : Subgroup SL(2, ℤ)}
    (h : IsCongruenceSubgroup Γ) : Gamma Γ.strictLevel ≤ Γ := by
  obtain ⟨M, hM, hMΓ⟩ := h
  have : NeZero M := ⟨hM⟩
  exact (Gamma_le_normalClosure_T_pow_sup_Gamma Γ.strictLevel M).trans
    (sup_le Γ.normalClosure_T_pow_strictLevel_le hMΓ)

/-- **Strict Wohlfahrt's theorem**: a subgroup `Γ ≤ SL(2, ℤ)` with nonzero strict level (in
particular, any finite-index subgroup) is a congruence subgroup if and only if it contains
`Γ(Γ.strictLevel)`. -/
theorem isCongruenceSubgroup_iff_Gamma_strictLevel_le {Γ : Subgroup SL(2, ℤ)}
    [NeZero Γ.strictLevel] : IsCongruenceSubgroup Γ ↔ Gamma Γ.strictLevel ≤ Γ :=
  ⟨IsCongruenceSubgroup.Gamma_strictLevel_le, fun h ↦ ⟨Γ.strictLevel, NeZero.ne _, h⟩⟩

/-- **Kiming–Schütt–Verrill's bound**: every congruence subgroup `Γ ≤ SL(2, ℤ)` contains
`Γ(2 * Γ.withCenter.strictLevel)`, where `Γ.withCenter.strictLevel` is the signed level of `Γ`. -/
theorem IsCongruenceSubgroup.Gamma_two_mul_strictLevel_withCenter_le {Γ : Subgroup SL(2, ℤ)}
    (h : IsCongruenceSubgroup Γ) : Gamma (2 * Γ.withCenter.strictLevel) ≤ Γ :=
  (Gamma_le_Gamma_of_dvd Γ.strictLevel_dvd_two_mul_strictLevel_withCenter).trans
    h.Gamma_strictLevel_le

/-! ### Sharpness of strict versus signed level -/

/-- The index-2 subgroup `{γ ∈ Γ(2) | γ 0 0 ≡ 1 (mod 4)}` of `Γ(2)`. -/
private def level4Lift : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Gamma 2 ∧ (γ 0 0 : ZMod 4) = 1}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha2, ha4⟩ ⟨hb2, hb4⟩
    refine ⟨mul_mem ha2 hb2, ?_⟩
    obtain ⟨x, hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0 1) 2).mp (Gamma_mem.mp ha2).2.1
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (b 1 0) 2).mp (Gamma_mem.mp hb2).2.2.1
    have hcross : ((a 0 1 * b 1 0 : ℤ) : ZMod 4) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr
        ⟨x * y, by linear_combination b 1 0 * hx + 2 * x * hy⟩
    have h00 : (a * b) 0 0 = a 0 0 * b 0 0 + a 0 1 * b 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h00, Int.cast_add, Int.cast_mul, ha4, hb4, hcross, mul_one, add_zero]
  inv_mem' := by
    rintro a ⟨ha2, ha4⟩
    refine ⟨inv_mem ha2, ?_⟩
    obtain ⟨x, hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0 1) 2).mp (Gamma_mem.mp ha2).2.1
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1 0) 2).mp (Gamma_mem.mp ha2).2.2.1
    have hcross : ((a 0 1 : ZMod 4) * (a 1 0 : ZMod 4)) = 0 := by
      rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨x * y, by linear_combination a 1 0 * hx + 2 * x * hy⟩
    rw [Matrix.SpecialLinearGroup.inv_apply_zero_zero]
    have hdet := Matrix.SpecialLinearGroup.intCast_fin_two_mul_sub_mul_eq_one (R := ZMod 4) a
    rw [ha4, hcross] at hdet
    linear_combination hdet

private lemma level4Lift_withCenter : level4Lift.withCenter = Gamma 2 := by
  refine le_antisymm ?_ fun γ hγ ↦ ?_
  · exact Subgroup.withCenter_le_iff.mpr ⟨fun _ h ↦ h.1,
      Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr
        (neg_one_mem_Gamma_iff.mpr dvd_rfl)⟩
  · obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (γ 0 0) 2).mp
      (by simpa using (Gamma_mem.mp hγ).1.symm)
    rcases Int.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · refine level4Lift.le_withCenter ⟨hγ, ?_⟩
      simpa using ((ZMod.intCast_eq_intCast_iff_dvd_sub 1 (γ 0 0) 4).mpr
        ⟨r, by linear_combination hk⟩).symm
    · have hneg_mem : -γ ∈ level4Lift := by
        refine ⟨by simpa using mul_mem (neg_one_mem_Gamma_iff.mpr dvd_rfl) hγ, ?_⟩
        simpa using ((ZMod.intCast_eq_intCast_iff_dvd_sub 1 ((-γ : SL(2, ℤ)) 0 0) 4).mpr
          ⟨-r - 1, by simp only [coe_neg, Matrix.neg_apply]; linear_combination -hk⟩).symm
      exact Subgroup.mem_withCenter_iff.mpr ⟨-γ, hneg_mem, -1,
        Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (.inr rfl), by simp⟩

/-- There exists a congruence subgroup `Γ ≤ SL(2, ℤ)` with `-I ∉ Γ`, `±Γ = Γ(2)`,
`Γ.strictLevel = 4`, and `¬ Γ(2) ≤ Γ`. Thus the strict level can genuinely be twice the signed
level, and the signed level is not in general a congruence level for subgroups not containing
`-I`. -/
theorem exists_isCongruenceSubgroup_strictLevel_eq_two_mul_withCenter :
    ∃ Γ : Subgroup SL(2, ℤ), (-1 : SL(2, ℤ)) ∉ Γ ∧ Γ.withCenter = Gamma 2 ∧
      Γ.strictLevel = 4 ∧ IsCongruenceSubgroup Γ ∧ ¬ Gamma 2 ≤ Γ := by
  have hneg : (-1 : SL(2, ℤ)) ∉ level4Lift := by
    rintro ⟨_, h4⟩
    exact (by decide : (-1 : ZMod 4) ≠ 1) (by simpa using h4)
  have hcong : IsCongruenceSubgroup level4Lift :=
    ⟨4, by decide, fun γ hγ ↦ ⟨Gamma_le_Gamma_of_dvd (by decide : 2 ∣ 4) hγ, (Gamma_mem.mp hγ).1⟩⟩
  have hnot2 : ¬ Gamma 2 ≤ level4Lift := fun hle ↦
    hneg (hle (neg_one_mem_Gamma_iff.mpr dvd_rfl))
  have hlevel : level4Lift.strictLevel = 4 := by
    have hcases := level4Lift.strictLevel_eq_or_eq_two_mul_strictLevel_withCenter
    rw [level4Lift_withCenter, strictLevel_Gamma] at hcases
    rcases hcases with h2 | h4
    · have hle := hcong.Gamma_strictLevel_le
      rw [h2] at hle
      exact absurd hle hnot2
    · exact h4
  exact ⟨level4Lift, hneg, level4Lift_withCenter, hlevel, hcong, hnot2⟩

end CongruenceSubgroup
