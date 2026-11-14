/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.StrictLevel
import TauCeti.Data.Int.Progression
import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# The strict form of Wohlfahrt's theorem

A subgroup `Γ ≤ SL(2, ℤ)` of finite index — whether or not it contains `-I` — is a congruence
subgroup if and only if it contains the principal congruence subgroup `Γ(N)` at its strict level
`N = Γ.strictLevel` (`CongruenceSubgroup.isCongruenceSubgroup_iff_Gamma_strictLevel_le`). When
`-I ∈ Γ`, the strict level agrees with Klein and Wohlfahrt's signed level and this recovers
Wohlfahrt's theorem; when `-I ∉ Γ`, the signed level can be half the strict level (as for
`{γ ∈ Γ(2) | γ₀₀ ≡ 1 mod 4}`, which contains `Γ(4)` and not `Γ(2)`), so the strict level is the
exact modulus at which principal congruence containment holds.

The underlying normal-generation identity is Kiming, Schütt and Verrill's elementary matrix
reduction, sharpened from `2N` to any `N` and nonzero `ν`:
`Subgroup.normalClosure {T ^ N} ⊔ Γ(ν) = Γ(gcd N ν)`
(`CongruenceSubgroup.normalClosure_T_pow_sup_Gamma_eq`), and in particular
`Γ(N) = Subgroup.normalClosure {T ^ N} ⊔ Γ(ν)` whenever `N ∣ ν` and `ν ≠ 0`
(`CongruenceSubgroup.Gamma_eq_normalClosure_T_pow_sup_Gamma`). The hypothesis `ν ≠ 0` is genuine:
at `ν = 0` (`Γ(0) = ⊥`), the normal closure of `T ^ N` has infinite index in `Γ(N)` for `N ≥ 6`
(Fricke 1886; Wohlfahrt 1964).

## Main results

* `CongruenceSubgroup.Gamma_le_normalClosure_T_pow_sup_Gamma`,
  `CongruenceSubgroup.normalClosure_T_pow_sup_Gamma_eq`,
  `CongruenceSubgroup.Gamma_eq_normalClosure_T_pow_sup_Gamma`: the normal closure of `T ^ N`
  together with `Γ(ν)` (`ν ≠ 0`) generates `Γ(gcd N ν)`, and equals `Γ(N)` when `N ∣ ν`.
* `CongruenceSubgroup.Gamma_le_of_normal_of_T_pow_mem`: a normal subgroup containing `T ^ N` and
  `Γ(ν)` (`ν ≠ 0`) contains `Γ(N)`.
* `CongruenceSubgroup.IsCongruenceSubgroup.Gamma_strictLevel_le_normalCore`,
  `CongruenceSubgroup.IsCongruenceSubgroup.Gamma_strictLevel_le`: every congruence subgroup `Γ`
  contains `Γ(Γ.strictLevel)` inside its normal core.
* `CongruenceSubgroup.isCongruenceSubgroup_iff_strictLevel_ne_zero_and_Gamma_le`,
  `CongruenceSubgroup.isCongruenceSubgroup_iff_Gamma_le_of_dvd`,
  `CongruenceSubgroup.isCongruenceSubgroup_iff_Gamma_strictLevel_le`: **Wohlfahrt's theorem in
  strict form**.
* `CongruenceSubgroup.IsCongruenceSubgroup.Gamma_two_mul_strictLevel_withCenter_le`: Kiming,
  Schütt and Verrill's bound `Γ(2 · (Γ·{±I}).strictLevel) ≤ Γ`.

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535,
  Theorem 2.
* I. Kiming, M. Schütt and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. 83 (2011), 96–120, §3, Lemma 7, Proposition 3 and Remark 8.
-/

public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace CongruenceSubgroup

/-! ### Elementary shears in the normal closure of `T ^ N` -/

/-- The lower-unitriangular shear `!![1, 0; m, 1] = S T⁻ᵐ S⁻¹` in `SL(2, ℤ)`. -/
private def lowerShear (m : ℤ) : SL(2, ℤ) :=
  ModularGroup.S * ModularGroup.T ^ (-m) * ModularGroup.S⁻¹

private lemma coe_lowerShear (m : ℤ) :
    (lowerShear m : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; m, 1] := by
  simpa [lowerShear, ModularGroup.coe_S] using ModularGroup.S.coe_conj_T_zpow (-m)

/-- The conjugate `!![1 + m, -m; m, 1 - m] = !![1, 0; 1, 1] T⁻ᵐ !![1, 0; 1, 1]⁻¹` in
`SL(2, ℤ)`, realizing any diagonal residue `1 + m` congruent to `1` modulo `N`. -/
private def diagShear (m : ℤ) : SL(2, ℤ) :=
  lowerShear 1 * ModularGroup.T ^ (-m) * (lowerShear 1)⁻¹

private lemma coe_diagShear (m : ℤ) :
    (diagShear m : Matrix (Fin 2) (Fin 2) ℤ) = !![1 + m, -m; m, 1 - m] := by
  simpa [diagShear, coe_lowerShear, ← sub_eq_add_neg] using (lowerShear 1).coe_conj_T_zpow (-m)

private lemma conj_T_zpow_mem_normalClosure {N : ℕ} {m : ℤ} (hm : (N : ℤ) ∣ m)
    (σ : SL(2, ℤ)) :
    σ * ModularGroup.T ^ m * σ⁻¹ ∈
      Subgroup.normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ)) :=
  Subgroup.strictLevel_dvd_iff_zpow.mp
    (by simpa [Subgroup.strictLevel_normalClosure_T_pow] using hm) σ

/-- Multiplying `A ∈ Γ(N)` with `IsCoprime (A 0 0) ν` on the right by a power of `T ^ N` and on
the left by a conjugate of `T ^ N` clears both off-diagonal entries modulo `ν` without changing
`A 0 0`. -/
private lemma exists_mul_mem_normalClosure_offDiag_zero {N ν : ℕ} {A : SL(2, ℤ)}
    (hA : A ∈ Gamma N) (hcop : IsCoprime (A 0 0) (ν : ℤ)) :
    ∃ x₁ ∈ Subgroup.normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ)),
      ∃ x₂ ∈ Subgroup.normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ)),
        (x₁ * A * x₂) 0 0 = A 0 0 ∧
          (((x₁ * A * x₂) 0 1 : ℤ) : ZMod ν) = 0 ∧
          (((x₁ * A * x₂) 1 0 : ℤ) : ZMod ν) = 0 := by
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨b', hb'⟩ := (mem_Gamma_iff_dvd.mp hA).2.1
  set x₂ := ModularGroup.T ^ ((N : ℤ) * (-b' * u))
  have hx₂ : x₂ ∈ Subgroup.normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ)) := by
    simpa [x₂] using conj_T_zpow_mem_normalClosure (dvd_mul_right (N : ℤ) (-b' * u)) 1
  set A₁ := A * x₂
  have hA₁ : A₁ ∈ Gamma N := mul_mem hA (normalClosure_T_pow_le_Gamma N hx₂)
  have hA₁00 : A₁ 0 0 = A 0 0 := by
    simp [A₁, x₂, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  have hA₁01 : (ν : ℤ) ∣ A₁ 0 1 := by
    have hentry : A₁ 0 1 = A 0 0 * ((N : ℤ) * (-b' * u)) + A 0 1 := by
      simp [A₁, x₂, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨(N : ℤ) * b' * v, ?_⟩
    linear_combination hentry + hb' - (N : ℤ) * b' * huv
  obtain ⟨c', hc'⟩ := (mem_Gamma_iff_dvd.mp hA₁).2.2.1
  set x₁ := lowerShear ((N : ℤ) * (-c' * u))
  have hx₁ : x₁ ∈ Subgroup.normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ)) :=
    conj_T_zpow_mem_normalClosure (dvd_neg.mpr (dvd_mul_right (N : ℤ) (-c' * u))) ModularGroup.S
  refine ⟨x₁, hx₁, x₂, hx₂, ?_, ?_, ?_⟩
  · rw [mul_assoc, ← hA₁00]
    simp [A₁, x₁, coe_lowerShear, Matrix.mul_apply, Fin.sum_univ_two]
  · have hentry : (x₁ * A₁) 0 1 = A₁ 0 1 := by
      simp [x₁, coe_lowerShear, Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_assoc, hentry]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ν).mpr hA₁01
  · have hentry : (x₁ * A₁) 1 0 = (N : ℤ) * (-c' * u) * A₁ 0 0 + A₁ 1 0 := by
      simp [x₁, coe_lowerShear, Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_assoc, hentry, hA₁00, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨(N : ℤ) * c' * v, by linear_combination hc' - (N : ℤ) * c' * huv⟩

/-- Two matrices of `SL(2, ℤ)` that are diagonal modulo `ν` with equal `(0, 0)` entry modulo `ν`
have equal `(1, 1)` entry modulo `ν` as well (both are inverses of `(0, 0)`), so their ratio lies
in `Γ(ν)`. -/
private lemma inv_mul_mem_Gamma_of_offDiag_zero {ν : ℕ} {A B : SL(2, ℤ)}
    (h00 : ((A 0 0 : ℤ) : ZMod ν) = ((B 0 0 : ℤ) : ZMod ν))
    (hA01 : ((A 0 1 : ℤ) : ZMod ν) = 0) (hA10 : ((A 1 0 : ℤ) : ZMod ν) = 0)
    (hB01 : ((B 0 1 : ℤ) : ZMod ν) = 0) (hB10 : ((B 1 0 : ℤ) : ZMod ν) = 0) :
    A⁻¹ * B ∈ Gamma ν := by
  have hAdet := intCast_fin_two_mul_sub_mul_eq_one (R := ZMod ν) A
  have hBdet := intCast_fin_two_mul_sub_mul_eq_one (R := ZMod ν) B
  rw [hA01, hA10, mul_zero, sub_zero] at hAdet
  rw [hB01, hB10, mul_zero, sub_zero, ← h00] at hBdet
  have h11 : ((A 1 1 : ℤ) : ZMod ν) = ((B 1 1 : ℤ) : ZMod ν) := by
    linear_combination ((B 1 1 : ℤ) : ZMod ν) * hAdet - ((A 1 1 : ℤ) : ZMod ν) * hBdet
  have hmap : map (Int.castRingHom (ZMod ν)) A = map (Int.castRingHom (ZMod ν)) B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, hA01, hA10, hB01, hB10, h11]
  rw [Gamma_mem', map_mul, map_inv, hmap, inv_mul_cancel]

/-! ### Normal generation modulo `Γ(ν)` and the strict Wohlfahrt theorem -/

/-- **Kiming–Schütt–Verrill matrix reduction**: for every `N` and every nonzero `ν`, `Γ(N)` is
contained in the join of `Subgroup.normalClosure {T ^ N}` and `Γ(ν)`. -/
theorem Gamma_le_normalClosure_T_pow_sup_Gamma (N ν : ℕ) [NeZero ν] :
    Gamma N ≤ Subgroup.normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ)) ⊔ Gamma ν := by
  intro g hg
  set K := Subgroup.normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ))
  -- Step 1: shear the first column by a multiple of `N` so that the `(0, 0)` entry is prime to `ν`.
  obtain ⟨q, hq⟩ := (mem_Gamma_iff_dvd.mp hg).1
  have hcopN : IsCoprime (g 0 0) (N : ℤ) := ⟨1, -q, by linear_combination hq⟩
  obtain ⟨k, hk⟩ := (hcopN.mul_right (g.isCoprime_row 0)).exists_isCoprime_add_mul
    (Int.natCast_ne_zero.mpr (NeZero.ne ν))
  set s := lowerShear ((N : ℤ) * k)
  have hsK : s ∈ K :=
    conj_T_zpow_mem_normalClosure (dvd_neg.mpr (dvd_mul_right (N : ℤ) k)) ModularGroup.S
  set g₁ := g * s
  have hg₁ : g₁ ∈ Gamma N := mul_mem hg (normalClosure_T_pow_le_Gamma N hsK)
  have hg₁_cop : IsCoprime (g₁ 0 0) (ν : ℤ) := by
    have hentry : g₁ 0 0 = g 0 0 + k * ((N : ℤ) * g 0 1) := by
      simp [g₁, s, coe_lowerShear, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rwa [hentry]
  -- Step 2: diagonalize `g₁` modulo `ν` using left and right elements of `K`.
  obtain ⟨x₁, hx₁, x₂, hx₂, hg'00, hg'01, hg'10⟩ :=
    exists_mul_mem_normalClosure_offDiag_zero hg₁ hg₁_cop
  -- Step 3: build `M ∈ K` with the same `(0, 0)` entry as `g₁` and diagonalize `M` modulo `ν`.
  obtain ⟨m, hm⟩ := (mem_Gamma_iff_dvd.mp hg₁).1
  set M := diagShear ((N : ℤ) * m)
  have hMK : M ∈ K :=
    conj_T_zpow_mem_normalClosure (dvd_neg.mpr (dvd_mul_right (N : ℤ) m)) (lowerShear 1)
  have hM00 : M 0 0 = g₁ 0 0 := by
    have : M 0 0 = 1 + (N : ℤ) * m := by simp [M, coe_diagShear]
    linarith
  obtain ⟨y₁, hy₁, y₂, hy₂, hM'00, hM'01, hM'10⟩ :=
    exists_mul_mem_normalClosure_offDiag_zero (normalClosure_T_pow_le_Gamma N hMK)
      (hM00 ▸ hg₁_cop)
  -- `M' = y₁ * M * y₂ ∈ K` and `g' = x₁ * g₁ * x₂` agree modulo `ν`.
  have hdiff : (y₁ * M * y₂)⁻¹ * (x₁ * g₁ * x₂) ∈ Gamma ν :=
    inv_mul_mem_Gamma_of_offDiag_zero (by rw [hM'00, hM00, hg'00]) hM'01 hM'10 hg'01 hg'10
  have hM'sup : y₁ * M * y₂ ∈ K ⊔ Gamma ν :=
    Subgroup.mem_sup_left (mul_mem (mul_mem hy₁ hMK) hy₂)
  have hg'sup : x₁ * g₁ * x₂ ∈ K ⊔ Gamma ν := by
    simpa only [mul_inv_cancel_left] using mul_mem hM'sup (Subgroup.mem_sup_right hdiff)
  have hg_eq : g = x₁⁻¹ * (x₁ * g₁ * x₂) * x₂⁻¹ * s⁻¹ := by
    simp [g₁]
    group
  rw [hg_eq]
  exact mul_mem (mul_mem (mul_mem (inv_mem (Subgroup.mem_sup_left hx₁)) hg'sup)
    (inv_mem (Subgroup.mem_sup_left hx₂))) (inv_mem (Subgroup.mem_sup_left hsK))

/-- The normal closure of `T ^ N` together with `Γ(ν)` (`ν ≠ 0`) generates `Γ(gcd N ν)`. -/
theorem normalClosure_T_pow_sup_Gamma_eq (N ν : ℕ) [NeZero ν] :
    Subgroup.normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ)) ⊔ Gamma ν =
      Gamma (Nat.gcd N ν) := by
  refine le_antisymm ?_ ?_
  · exact sup_le
      ((normalClosure_T_pow_le_Gamma N).trans (Gamma_le_Gamma_of_dvd (Nat.gcd_dvd_left N ν)))
      (Gamma_le_Gamma_of_dvd (Nat.gcd_dvd_right N ν))
  · rw [Gamma_gcd_eq_sup]
    exact sup_le (Gamma_le_normalClosure_T_pow_sup_Gamma N ν) le_sup_right

/-- When `N ∣ ν` and `ν ≠ 0`, `Γ(N)` is generated as a subgroup by the normal closure of `T ^ N`
together with `Γ(ν)`. -/
theorem Gamma_eq_normalClosure_T_pow_sup_Gamma {N ν : ℕ} [NeZero ν] (hdvd : N ∣ ν) :
    Gamma N = Subgroup.normalClosure ({ModularGroup.T ^ N} : Set SL(2, ℤ)) ⊔ Gamma ν := by
  rw [normalClosure_T_pow_sup_Gamma_eq, Nat.gcd_eq_left hdvd]

/-- Any normal subgroup of `SL(2, ℤ)` containing `T ^ N` and `Γ(ν)` (`ν ≠ 0`) contains `Γ(N)`. -/
theorem Gamma_le_of_normal_of_T_pow_mem {H : Subgroup SL(2, ℤ)} [H.Normal] {N ν : ℕ}
    [NeZero ν] (hT : ModularGroup.T ^ N ∈ H) (hν : Gamma ν ≤ H) :
    Gamma N ≤ H :=
  (Gamma_le_normalClosure_T_pow_sup_Gamma N ν).trans
    (sup_le (Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hT)) hν)

/-- **Strict Wohlfahrt theorem, normal-core form**: if `Γ ≤ SL(2, ℤ)` is a congruence subgroup,
its normal core contains `Γ(Γ.strictLevel)`. -/
theorem IsCongruenceSubgroup.Gamma_strictLevel_le_normalCore {Γ : Subgroup SL(2, ℤ)}
    (h : IsCongruenceSubgroup Γ) : Gamma Γ.strictLevel ≤ Γ.normalCore := by
  obtain ⟨ν, hν, hle⟩ := h
  have : NeZero ν := ⟨hν⟩
  have := Gamma_normal ν
  exact Gamma_le_of_normal_of_T_pow_mem
    (Subgroup.strictLevel_dvd_iff_T_pow_mem_normalCore.mp dvd_rfl)
    (Subgroup.normal_le_normalCore.mpr hle)

/-- **Strict Wohlfahrt theorem, forward direction**: every congruence subgroup `Γ ≤ SL(2, ℤ)`
contains `Γ(Γ.strictLevel)`. -/
theorem IsCongruenceSubgroup.Gamma_strictLevel_le {Γ : Subgroup SL(2, ℤ)}
    (h : IsCongruenceSubgroup Γ) : Gamma Γ.strictLevel ≤ Γ :=
  h.Gamma_strictLevel_le_normalCore.trans Γ.normalCore_le

/-- **Wohlfahrt's theorem in strict form, unconditional**: an arbitrary subgroup `Γ ≤ SL(2, ℤ)` is
a congruence subgroup if and only if its strict level is nonzero and `Γ(Γ.strictLevel) ≤ Γ`. -/
theorem isCongruenceSubgroup_iff_strictLevel_ne_zero_and_Gamma_le {Γ : Subgroup SL(2, ℤ)} :
    IsCongruenceSubgroup Γ ↔ Γ.strictLevel ≠ 0 ∧ Gamma Γ.strictLevel ≤ Γ :=
  ⟨fun h ↦ ⟨h.strictLevel_ne_zero, h.Gamma_strictLevel_le⟩,
    fun ⟨hne, hle⟩ ↦ ⟨Γ.strictLevel, hne, hle⟩⟩

/-- For any nonzero multiple `N` of `Γ.strictLevel`, `Γ` is a congruence subgroup if and only if
it contains `Γ(N)`. -/
theorem isCongruenceSubgroup_iff_Gamma_le_of_dvd {Γ : Subgroup SL(2, ℤ)} {N : ℕ} [NeZero N]
    (hdvd : Γ.strictLevel ∣ N) :
    IsCongruenceSubgroup Γ ↔ Gamma N ≤ Γ :=
  ⟨fun h ↦ (Gamma_le_Gamma_of_dvd hdvd).trans h.Gamma_strictLevel_le,
    fun h ↦ ⟨N, NeZero.ne N, h⟩⟩

/-- **Wohlfahrt's theorem in strict form**: a subgroup `Γ ≤ SL(2, ℤ)` of nonzero strict level (in
particular any subgroup of finite index, via `Subgroup.instNeZeroStrictLevel`) is a congruence
subgroup if and only if it contains `Γ(Γ.strictLevel)`. -/
theorem isCongruenceSubgroup_iff_Gamma_strictLevel_le (Γ : Subgroup SL(2, ℤ))
    [NeZero Γ.strictLevel] :
    IsCongruenceSubgroup Γ ↔ Gamma Γ.strictLevel ≤ Γ :=
  isCongruenceSubgroup_iff_Gamma_le_of_dvd dvd_rfl

/-- **Kiming–Schütt–Verrill's level-doubling containment**: every congruence subgroup `Γ` contains
`Γ(2 · (Γ·{±I}).strictLevel)`. -/
theorem IsCongruenceSubgroup.Gamma_two_mul_strictLevel_withCenter_le {Γ : Subgroup SL(2, ℤ)}
    (h : IsCongruenceSubgroup Γ) :
    Gamma (2 * Γ.withCenter.strictLevel) ≤ Γ :=
  (Gamma_le_Gamma_of_dvd Γ.strictLevel_dvd_two_mul_strictLevel_withCenter).trans
    h.Gamma_strictLevel_le

/-! ### The odd lift `{γ ∈ Γ(2) | γ₀₀ ≡ 1 (mod 4)}`

The subgroup `{γ ∈ Γ(2) | γ₀₀ ≡ 1 (mod 4)}` excludes `-I`, has `±Γ = Γ(2)` of strict level `2`,
contains `T ^ 2` but not `(T * S) * T ^ 2 * (T * S)⁻¹`, and contains `Γ(4)` but not `Γ(2)`: its
strict level is `4`, showing that `Γ(strictLevel (Γ·{±I})) ≤ Γ` fails for congruence lifts when
`-I ∉ Γ`. -/

private def oddGamma2Lift : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Gamma 2 ∧ ((γ 0 0 : ℤ) : ZMod 4) = 1}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    have h4 : (4 : ZMod 4) = 0 := by decide
    rintro a b ⟨ha, ha00⟩ ⟨hb, hb00⟩
    refine ⟨mul_mem ha hb, ?_⟩
    obtain ⟨u, hu⟩ := (mem_Gamma_iff_dvd.mp ha).2.1
    obtain ⟨v, hv⟩ := (mem_Gamma_iff_dvd.mp hb).2.2.1
    have h00 : (a * b) 0 0 = a 0 0 * b 0 0 + 4 * (u * v) := by
      have : (a * b) 0 0 = a 0 0 * b 0 0 + a 0 1 * b 1 0 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [this, hu, hv]
      ring
    have hcast := congrArg (Int.cast : ℤ → ZMod 4) h00
    push_cast at hcast
    simpa [ha00, hb00, h4] using hcast
  inv_mem' := by
    have h4 : (4 : ZMod 4) = 0 := by decide
    rintro a ⟨ha, ha00⟩
    refine ⟨inv_mem ha, ?_⟩
    obtain ⟨u, hu⟩ := (mem_Gamma_iff_dvd.mp ha).2.1
    obtain ⟨v, hv⟩ := (mem_Gamma_iff_dvd.mp ha).2.2.1
    have huv : a 0 1 * a 1 0 = 4 * (u * v) := by rw [hu, hv]; ring
    have hdet : a 0 0 * a 1 1 - 4 * (u * v) = 1 := by
      rw [← huv]
      exact a.fin_two_mul_sub_mul_eq_one
    have hcast := congrArg (Int.cast : ℤ → ZMod 4) hdet
    push_cast at hcast
    rw [inv_apply_zero_zero]
    simpa [ha00, h4] using hcast

example :
    ∃ Γ : Subgroup SL(2, ℤ),
      (-1 : SL(2, ℤ)) ∉ Γ ∧
      Γ.withCenter = Gamma 2 ∧
      ModularGroup.T ^ 2 ∈ Γ ∧
      (ModularGroup.T * ModularGroup.S) * ModularGroup.T ^ 2 *
          (ModularGroup.T * ModularGroup.S)⁻¹ ∉ Γ ∧
      IsCongruenceSubgroup Γ ∧
      Γ.strictLevel = 4 ∧
      Gamma 4 ≤ Γ ∧
      ¬ Gamma 2 ≤ Γ := by
  have hneg : (-1 : SL(2, ℤ)) ∉ oddGamma2Lift := fun ⟨_, h00⟩ ↦ absurd h00 (by decide)
  have hneg2 : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by rw [Gamma_mem]; decide
  have hwith : oddGamma2Lift.withCenter = Gamma 2 := by
    refine le_antisymm (Subgroup.withCenter_le_iff.mpr ⟨fun _ h ↦ h.1, fun z hz ↦ ?_⟩) fun γ hγ ↦ ?_
    · rcases mem_center_iff_eq_one_or_eq_neg_one.mp hz with rfl | rfl
      · exact one_mem _
      · exact hneg2
    · obtain ⟨k, hk⟩ := (mem_Gamma_iff_dvd.mp hγ).1
      rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact oddGamma2Lift.le_withCenter ⟨hγ,
          (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 0 0) 1 4).mpr ⟨-m, by omega⟩⟩
      · refine Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mpr
          ⟨-γ, ⟨by simpa using mul_mem hneg2 hγ, ?_⟩, Or.inr (neg_neg γ).symm⟩
        rw [coe_neg, Matrix.neg_apply]
        exact (ZMod.intCast_eq_intCast_iff_dvd_sub (-(γ 0 0)) 1 4).mpr ⟨m + 1, by omega⟩
  have hT2 : ModularGroup.T ^ 2 ∈ oddGamma2Lift :=
    ⟨by simpa using ModularGroup_T_pow_mem_Gamma 2 2 dvd_rfl,
      by simp [sq, ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hconj : (ModularGroup.T * ModularGroup.S) * ModularGroup.T ^ 2 *
      (ModularGroup.T * ModularGroup.S)⁻¹ ∉ oddGamma2Lift := by
    rintro ⟨_, h00⟩
    have hentry : ((ModularGroup.T * ModularGroup.S) * ModularGroup.T ^ 2 *
        (ModularGroup.T * ModularGroup.S)⁻¹) 0 0 = -1 := by
      rw [← zpow_ofNat, (ModularGroup.T * ModularGroup.S).coe_conj_T_zpow 2]
      simp [ModularGroup.coe_T, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
    exact absurd (hentry ▸ h00) (by decide)
  have hG4 : Gamma 4 ≤ oddGamma2Lift := fun γ hγ ↦
    ⟨Gamma_le_Gamma_of_dvd (by decide : 2 ∣ 4) hγ, (Gamma_mem.mp hγ).1⟩
  have hlevel : oddGamma2Lift.strictLevel = 4 := by
    rcases oddGamma2Lift.strictLevel_eq_or_eq_two_mul_strictLevel_withCenter with h | h <;>
      rw [hwith, strictLevel_Gamma] at h
    · exact absurd ((Subgroup.strictLevel_dvd_iff.mp (dvd_of_eq h))
        (ModularGroup.T * ModularGroup.S)) hconj
    · exact h
  exact ⟨oddGamma2Lift, hneg, hwith, hT2, hconj, ⟨4, by decide, hG4⟩, hlevel, hG4,
    fun h ↦ hneg (h hneg2)⟩

end CongruenceSubgroup

end
