/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.StrictLevel
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.TriangleGroup
import TauCeti.Data.Int.CongrAllPrimes
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# Wohlfahrt's theorem and the congruence closure

A subgroup `Γ ≤ SL(2, ℤ)` is a congruence subgroup if it contains some principal congruence
subgroup `Γ(M)` with `M ≠ 0`. Its strict level `Γ.strictLevel` is the least positive `N` (or `0`
if none exists) such that every conjugate `σ Tᴺ σ⁻¹` of the translation `Tᴺ` lies in `Γ`.

The core arithmetic input proved here is the normal-closure join identity

`normalClosure {Tᴺ} ⊔ Γ(M) = Γ(gcd(N, M))`

for every `N : ℕ` and every nonzero `M : ℕ`, with no assumption on `-I`. The proof is elementary
matrix reduction, without invoking strong approximation: given `γ ∈ Γ(N)`, left multiplication by
`T^{kN}` makes the `(0, 0)` entry coprime to `M`; multiplying on the left by lower transvections
`L^{aN} = S⁻¹ T^{-aN} S` and on the right by `T^{bN}` kills both off-diagonal entries modulo `M`;
and an explicit diagonal witness built from conjugates of `Tᴺ` matches the resulting matrix
modulo `M`, placing their ratio in `Γ(M)`.

From this identity (together with the signed-level comparison in
`TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.StrictLevel`) we deduce:

* **Wohlfahrt's theorem in strict form**: a congruence subgroup `Γ` always contains
  `Γ(Γ.strictLevel)`, so a finite-index subgroup `Γ ≤ SL(2, ℤ)` — whether or not it contains
  `-I` — is a congruence subgroup if and only if `Γ(Γ.strictLevel) ≤ Γ`.
* **Signed and projective forms**: Kiming–Schütt–Verrill's bound
  `Γ(2 * Γ.withCenter.strictLevel) ≤ Γ` for congruence `Γ` and the projective form of
  Wohlfahrt's theorem for subgroups of `PSL(2, ℤ)`.
* **The congruence closure** `Γ.congruenceClosure`, the intersection of all congruence subgroups
  containing `Γ`: for every nonzero `N`, `Γ.congruenceClosure` has the same reduction modulo `N`
  as `Γ`; for every nonzero multiple `N` of `Γ.strictLevel` (and in particular for
  `N = Γ.strictLevel` whenever `Γ` has finite index), `Γ.congruenceClosure = Γ ⊔ Γ(N)`. A
  finite-index subgroup `Γ` is a congruence subgroup if and only if `Γ.congruenceClosure = Γ`. For
  a noncongruence subgroup `Γ` whose enlargement `±Γ` is congruence, `Γ.congruenceClosure = ±Γ`;
  for a prime-index noncongruence subgroup, `Γ.congruenceClosure = ⊤`.
* **Separating witnesses**: `{γ ∈ Γ(2) | γ₀₀ ≡ 1 (mod 4)}` is a congruence subgroup excluding `-I`
  with signed level `2` and strict level `4` that does not contain `Γ(2)`, showing that the strict
  level cannot be replaced by the signed level; and an explicit index-`8`, strict-level-`8`
  subgroup is certified noncongruence by `!![73, -32; 16, -7] ∈ Γ(8)` and shown to have congruence
  closure `⊤`.

## Main declarations

* `CongruenceSubgroup.Gamma_le_normalClosure_T_pow_sup_Gamma`,
  `CongruenceSubgroup.normalClosure_T_pow_sup_Gamma`,
  `CongruenceSubgroup.normalClosure_T_pow_sup_Gamma_of_dvd`:
  `normalClosure {Tᴺ} ⊔ Γ(M) = Γ(gcd(N, M))` for `M ≠ 0`.
* `CongruenceSubgroup.Gamma_strictLevel_le_of_isCongruenceSubgroup`,
  `CongruenceSubgroup.isCongruenceSubgroup_iff_strictLevel_ne_zero_and_Gamma_le`,
  `CongruenceSubgroup.isCongruenceSubgroup_iff_Gamma_strictLevel_le`:
  Wohlfahrt's theorem in unconditional and strict finite-index forms.
* `CongruenceSubgroup.Gamma_two_mul_strictLevel_withCenter_le_of_isCongruenceSubgroup`,
  `CongruenceSubgroup.isCongruenceSubgroup_liftSL_iff`:
  Kiming–Schütt–Verrill's signed-level bound and the projective criterion.
* `Subgroup.congruenceClosure`: the congruence closure of a subgroup of `SL(2, ℤ)`, together with
  its closure-operator API, `Subgroup.congruenceClosure_eq_sup_Gamma_of_strictLevel_dvd`,
  `Subgroup.congruenceClosure_eq_sup_Gamma_strictLevel`,
  `Subgroup.isCongruenceSubgroup_congruenceClosure`,
  `Subgroup.congruenceClosure_eq_self_iff`,
  `Subgroup.map_intCast_zmod_congruenceClosure`,
  `Subgroup.congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup`, and
  `Subgroup.congruenceClosure_eq_top_of_prime_index`.
* `CongruenceSubgroup.exists_isCongruenceSubgroup_strictLevel_eq_two_mul_strictLevel_withCenter`
  and `CongruenceSubgroup.exists_not_isCongruenceSubgroup_index_eight_congruenceClosure_eq_top`:
  the signed-vs-strict-level and index-`8` noncongruence witnesses.

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535,
  Theorem 2.
* I. Kiming, M. Schütt and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. 83 (2011), 96–120, §3, Lemma 7, Proposition 3, and Remark 8.
-/

public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise

/-! ### Normal closure of `T ^ N` and principal congruence subgroups -/

namespace CongruenceSubgroup

section NormalClosureJoin

private lemma T_zpow_mul_mem_normalClosure (N : ℕ) (k : ℤ) :
    ModularGroup.T ^ (k * N) ∈ Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} := by
  rw [mul_comm, _root_.zpow_mul, zpow_natCast]
  exact Subgroup.zpow_mem _ (Subgroup.subset_normalClosure rfl) k

private lemma conj_T_zpow_mul_mem_normalClosure (N : ℕ) (σ : SL(2, ℤ)) (k : ℤ) :
    σ * ModularGroup.T ^ (k * N) * σ⁻¹ ∈
      Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} :=
  Subgroup.normalClosure_normal.conj_mem _ (T_zpow_mul_mem_normalClosure N k) σ

private lemma transvection_mul_mem_normalClosure (N : ℕ) (k : ℤ) :
    transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (k * N) ∈
      Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} := by
  have heq : transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (k * N) =
      ModularGroup.S⁻¹ * ModularGroup.T ^ ((-k) * N) * (ModularGroup.S⁻¹)⁻¹ := by
    have hS0 : (ModularGroup.S⁻¹ : SL(2, ℤ)) 0 0 = 0 := by decide
    have hS1 : (ModularGroup.S⁻¹ : SL(2, ℤ)) 1 0 = -1 := by decide
    ext i j
    rw [Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.coe_conj_T_zpow, hS0, hS1]
    fin_cases i <;> fin_cases j <;> simp
  rw [heq]
  exact conj_T_zpow_mul_mem_normalClosure N ModularGroup.S⁻¹ (-k)

private def shearConj (m : ℤ) : SL(2, ℤ) :=
  (ModularGroup.T * ModularGroup.S⁻¹) * ModularGroup.T ^ (-m) *
    (ModularGroup.T * ModularGroup.S⁻¹)⁻¹

private lemma coe_shearConj (m : ℤ) :
    (shearConj m : Matrix (Fin 2) (Fin 2) ℤ) = !![1 + m, -m; m, 1 - m] := by
  have h0 : (ModularGroup.T * ModularGroup.S⁻¹ : SL(2, ℤ)) 0 0 = -1 := by decide
  have h1 : (ModularGroup.T * ModularGroup.S⁻¹ : SL(2, ℤ)) 1 0 = -1 := by decide
  rw [shearConj, Matrix.SpecialLinearGroup.coe_conj_T_zpow, h0, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg]

private lemma shearConj_mul_mem_normalClosure (N : ℕ) (k : ℤ) :
    shearConj (k * N) ∈ Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} := by
  simpa [shearConj, neg_mul] using
    conj_T_zpow_mul_mem_normalClosure N (ModularGroup.T * ModularGroup.S⁻¹) (-k)

private lemma transvection_mul_mul_T_zpow_entries (A : SL(2, ℤ)) (p q : ℤ) :
    (transvection (one_ne_zero : (1 : Fin 2) ≠ 0) p * A * ModularGroup.T ^ q) 0 0 = A 0 0 ∧
      (transvection (one_ne_zero : (1 : Fin 2) ≠ 0) p * A * ModularGroup.T ^ q) 0 1 =
        A 0 1 + q * A 0 0 ∧
      (transvection (one_ne_zero : (1 : Fin 2) ≠ 0) p * A * ModularGroup.T ^ q) 1 0 =
        A 1 0 + p * A 0 0 := by
  simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, transvection_coe,
    ModularGroup.coe_T_zpow, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num
  exact ⟨by ring, by ring⟩

private lemma exists_T_zpow_mul_isCoprime {N M : ℕ} (hM : M ≠ 0) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma N) :
    ∃ k : ℤ, IsCoprime ((ModularGroup.T ^ (k * N) * γ) 0 0) (M : ℤ) := by
  obtain ⟨s, hs⟩ : (N : ℤ) ∣ γ 0 0 - 1 := by
    simpa using Matrix.SpecialLinearGroup.mem_ker_map_intCast_zmod_iff.mp hγ 0 0
  have hcop_N : IsCoprime (γ 0 0) (N : ℤ) := ⟨1, -s, by linear_combination hs⟩
  have hcop_c : IsCoprime (γ 0 0) (γ 1 0) :=
    ⟨γ 1 1, -(γ 0 1), by linear_combination γ.fin_two_mul_sub_mul_eq_one⟩
  have hcop_Nc : IsCoprime (γ 0 0) ((N : ℤ) * γ 1 0) := hcop_N.mul_right hcop_c
  set d : ℕ := ((N : ℤ) * γ 1 0).natAbs
  have hcop_d : IsCoprime (d : ℤ) (γ 0 0) := by
    rcases Int.natAbs_eq ((N : ℤ) * γ 1 0) with h | h
    · rw [h] at hcop_Nc
      exact hcop_Nc.symm
    · rw [h] at hcop_Nc
      have hneg := hcop_Nc.symm.neg_left
      rwa [neg_neg] at hneg
  obtain ⟨u, hu⟩ := (ZMod.isUnit_intCast_iff_isCoprime (γ 0 0) d).mpr hcop_d
  have : NeZero M := ⟨hM⟩
  obtain ⟨t, ht_cop, ht_eq⟩ := ZMod.exists_isCoprime_mul_intCast_eq M u
  have hdvd_d : (d : ℤ) ∣ t - γ 0 0 := by
    have : ((γ 0 0 : ℤ) : ZMod d) = (t : ZMod d) := hu.symm.trans ht_eq.symm
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this
  obtain ⟨k, hk⟩ : (N : ℤ) * γ 1 0 ∣ t - γ 0 0 := Int.natAbs_dvd.mp hdvd_d
  refine ⟨k, ?_⟩
  have h00_eq : (ModularGroup.T ^ (k * N) * γ) 0 0 = t := by
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T_zpow,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination -hk
  rw [h00_eq]
  rw [Nat.cast_mul] at ht_cop
  exact ht_cop.of_mul_right_left

private lemma mem_normalClosure_T_pow_sup_Gamma_of_isCoprime {N M : ℕ} {γ₁ : SL(2, ℤ)}
    (hγ₁ : γ₁ ∈ Gamma N) (hcop : IsCoprime (γ₁ 0 0) (M : ℤ)) :
    γ₁ ∈ Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} ⊔ Gamma M := by
  set H : Subgroup SL(2, ℤ) := Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} ⊔ Gamma M
  have hnc_le : Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} ≤ H := le_sup_left
  obtain ⟨u, v, huv⟩ := hcop
  have hker := Matrix.SpecialLinearGroup.mem_ker_map_intCast_zmod_iff.mp hγ₁
  obtain ⟨r, hr⟩ : (N : ℤ) ∣ γ₁ 0 0 - 1 := by simpa using hker 0 0
  obtain ⟨b', hb'⟩ : (N : ℤ) ∣ γ₁ 0 1 := by simpa using hker 0 1
  obtain ⟨c', hc'⟩ : (N : ℤ) ∣ γ₁ 1 0 := by simpa using hker 1 0
  set γ₂ : SL(2, ℤ) :=
    transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-c' * u * N) * γ₁ * ModularGroup.T ^ (-b' * u * N)
  set X : SL(2, ℤ) :=
    transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-r * u * N) * shearConj (r * N) *
      ModularGroup.T ^ (r * u * N)
  have hγ₂_e := transvection_mul_mul_T_zpow_entries γ₁ (-c' * u * N) (-b' * u * N)
  have hX_e := transvection_mul_mul_T_zpow_entries (shearConj (r * N)) (-r * u * N) (r * u * N)
  have hX00 : (shearConj (r * N)) 0 0 = γ₁ 0 0 := by
    have h : (shearConj (r * N)) 0 0 = 1 + r * N := by simpa using congr_fun₂ (coe_shearConj _) 0 0
    linear_combination h - hr
  have h01γ₂ : ((γ₂ 0 1 : ℤ) : ZMod M) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      ⟨N * b' * v, by rw [hγ₂_e.2.1]; linear_combination hb' - N * b' * huv⟩
  have h10γ₂ : ((γ₂ 1 0 : ℤ) : ZMod M) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      ⟨N * c' * v, by rw [hγ₂_e.2.2]; linear_combination hc' - N * c' * huv⟩
  have h01X : ((X 0 1 : ℤ) : ZMod M) = 0 := by
    have h01 : (shearConj (r * N)) 0 1 = -(r * N) := by simpa using congr_fun₂ (coe_shearConj _) 0 1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      ⟨-(r * N * v), by rw [hX_e.2.1, h01, hX00]; linear_combination r * N * huv⟩
  have h10X : ((X 1 0 : ℤ) : ZMod M) = 0 := by
    have h10 : (shearConj (r * N)) 1 0 = r * N := by simpa using congr_fun₂ (coe_shearConj _) 1 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      ⟨r * N * v, by rw [hX_e.2.2, h10, hX00]; linear_combination -(r * N * huv)⟩
  have hratio : γ₂ * X⁻¹ ∈ Gamma M := by
    rw [Gamma_mem', map_mul, map_inv, mul_inv_eq_one]
    refine Matrix.SpecialLinearGroup.ext_of_isRegular_apply_zero_zero ?_ ?_ ?_ ?_
    · simpa using (isUnit_intCast_apply_zero_zero_of_mem_Gamma0 (Gamma0_mem.mpr h10γ₂)).isRegular
    · simp only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]
      exact congrArg Int.cast (hγ₂_e.1.trans (hX_e.1.trans hX00).symm)
    · simp [h01γ₂, h01X]
    · simp [h10γ₂, h10X]
  have hX_mem : X ∈ H := hnc_le <| mul_mem
    (mul_mem (transvection_mul_mem_normalClosure N (-r * u)) (shearConj_mul_mem_normalClosure N r))
    (T_zpow_mul_mem_normalClosure N (r * u))
  have hγ₂_mem : γ₂ ∈ H := by
    simpa [mul_assoc] using mul_mem ((le_sup_right : Gamma M ≤ H) hratio) hX_mem
  have hL := inv_mem (hnc_le (transvection_mul_mem_normalClosure N (-c' * u)))
  have hR := inv_mem (hnc_le (T_zpow_mul_mem_normalClosure N (-b' * u)))
  simpa [γ₂, mul_assoc] using mul_mem (mul_mem hL hγ₂_mem) hR

/-- **Elementary matrix reduction for `Γ(N)`**: for every `N` and every nonzero `M`, the principal
congruence subgroup `Γ(N)` is contained in the join of the normal closure of `T ^ N` with `Γ(M)`.

No hypothesis on `-I` is needed and `N = 0` is allowed. -/
theorem Gamma_le_normalClosure_T_pow_sup_Gamma {N M : ℕ} (hM : M ≠ 0) :
    Gamma N ≤ Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} ⊔ Gamma M := by
  intro γ hγ
  obtain ⟨k, hk_cop⟩ := exists_T_zpow_mul_isCoprime hM hγ
  have hTk_mem : ModularGroup.T ^ (k * N) ∈ Gamma N := by
    simpa [Int.natAbs_natCast] using ModularGroup_T_pow_mem_Gamma (N : ℤ) (k * N) (dvd_mul_left _ _)
  have hγ₁ : ModularGroup.T ^ (k * N) * γ ∈
      Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} ⊔ Gamma M :=
    mem_normalClosure_T_pow_sup_Gamma_of_isCoprime (mul_mem hTk_mem hγ) hk_cop
  have hTk_inv : (ModularGroup.T ^ (k * N))⁻¹ ∈
      Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} ⊔ Gamma M :=
    inv_mem ((le_sup_left : Subgroup.normalClosure _ ≤ _) (T_zpow_mul_mem_normalClosure N k))
  simpa [mul_assoc] using mul_mem hTk_inv hγ₁

/-- **Normal closure of `T ^ N` joined with `Γ(M)`**: for every `N` and every nonzero `M`,
`normalClosure {T ^ N} ⊔ Γ(M) = Γ(gcd(N, M))`.

The hypothesis `M ≠ 0` is sharp: at `M = 0`, `Γ(0) = ⊥` while `normalClosure {T ^ N}` is
strictly smaller than `Γ(N)` for `N ≥ 6`. -/
theorem normalClosure_T_pow_sup_Gamma {N M : ℕ} (hM : M ≠ 0) :
    Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} ⊔ Gamma M =
      Gamma (Nat.gcd N M) := by
  have hN_normal := Gamma_normal N
  have hnc_le_Gamma :
      Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} ≤ Gamma N := by
    refine Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
    simpa [Int.natAbs_natCast] using ModularGroup_T_pow_mem_Gamma (N : ℤ) N dvd_rfl
  refine le_antisymm ?_ ?_
  · rw [Gamma_gcd_eq_sup]
    exact sup_le_sup_right hnc_le_Gamma (Gamma M)
  · rw [Gamma_gcd_eq_sup]
    exact sup_le (Gamma_le_normalClosure_T_pow_sup_Gamma hM) le_sup_right

/-- When `N ∣ M` with `M ≠ 0`, `normalClosure {T ^ N} ⊔ Γ(M) = Γ(N)`. -/
theorem normalClosure_T_pow_sup_Gamma_of_dvd {N M : ℕ} (hM : M ≠ 0) (hNM : N ∣ M) :
    Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ N} ⊔ Gamma M = Gamma N := by
  rw [normalClosure_T_pow_sup_Gamma hM, Nat.gcd_eq_left hNM]

end NormalClosureJoin

/-! ### Wohlfahrt's theorem -/

section Wohlfahrt

variable {Γ : Subgroup SL(2, ℤ)}

/-- **Wohlfahrt's theorem (forward direction)**: every congruence subgroup `Γ ≤ SL(2, ℤ)`
contains `Γ(Γ.strictLevel)`.

No assumption on `-I` or explicit `[Γ.FiniteIndex]` instance is needed. -/
theorem Gamma_strictLevel_le_of_isCongruenceSubgroup (hΓ : IsCongruenceSubgroup Γ) :
    Gamma Γ.strictLevel ≤ Γ := by
  obtain ⟨M, hM, hMle⟩ := hΓ
  have hnc : Subgroup.normalClosure {(ModularGroup.T : SL(2, ℤ)) ^ Γ.strictLevel} ≤ Γ :=
    (Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr
      (Subgroup.strictLevel_dvd_iff_T_pow_mem_normalCore.mp dvd_rfl))).trans Γ.normalCore_le
  exact (Gamma_le_normalClosure_T_pow_sup_Gamma hM).trans (sup_le hnc hMle)

/-- **Unconditional Wohlfahrt criterion**: a subgroup `Γ ≤ SL(2, ℤ)` is a congruence subgroup if
and only if its strict level is nonzero and `Γ(Γ.strictLevel) ≤ Γ`. -/
theorem isCongruenceSubgroup_iff_strictLevel_ne_zero_and_Gamma_le (Γ : Subgroup SL(2, ℤ)) :
    IsCongruenceSubgroup Γ ↔ Γ.strictLevel ≠ 0 ∧ Gamma Γ.strictLevel ≤ Γ :=
  ⟨fun hΓ ↦
    have : Γ.FiniteIndex := hΓ.finiteIndex
    ⟨Γ.strictLevel_pos.ne', Gamma_strictLevel_le_of_isCongruenceSubgroup hΓ⟩,
   fun ⟨hpos, hle⟩ ↦ ⟨Γ.strictLevel, hpos, hle⟩⟩

/-- **Wohlfahrt's theorem in strict form**: a finite-index subgroup `Γ ≤ SL(2, ℤ)`, whether or not
it contains `-I`, is a congruence subgroup if and only if it contains the principal congruence
subgroup of its strict level.

The `[Γ.FiniteIndex]` hypothesis is needed for the backward direction, where it ensures
`Γ.strictLevel ≠ 0`; without it, `⊥` has strict level `0` and satisfies `Γ(0) = ⊥ ≤ ⊥` while not
being a congruence subgroup. -/
theorem isCongruenceSubgroup_iff_Gamma_strictLevel_le (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    IsCongruenceSubgroup Γ ↔ Gamma Γ.strictLevel ≤ Γ := by
  rw [isCongruenceSubgroup_iff_strictLevel_ne_zero_and_Gamma_le,
    and_iff_right Γ.strictLevel_pos.ne']

/-- **Kiming–Schütt–Verrill, Proposition 3**: every congruence subgroup `Γ ≤ SL(2, ℤ)` contains
`Γ(2 * Γ.withCenter.strictLevel)`, where `Γ.withCenter.strictLevel` is the signed level. -/
theorem Gamma_two_mul_strictLevel_withCenter_le_of_isCongruenceSubgroup
    (hΓ : IsCongruenceSubgroup Γ) : Gamma (2 * Γ.withCenter.strictLevel) ≤ Γ :=
  (Gamma_le_Gamma_of_dvd Γ.strictLevel_dvd_two_mul_strictLevel_withCenter).trans
    (Gamma_strictLevel_le_of_isCongruenceSubgroup hΓ)

/-- **Projective form of Wohlfahrt's theorem**: for a finite-index subgroup `Γ' ≤ PSL(2, ℤ)`, its
lift `Γ'.liftSL` is a congruence subgroup if and only if `Γ'` contains the projective image of
`Γ(N)` for `N = Γ'.liftSL.strictLevel`. -/
theorem isCongruenceSubgroup_liftSL_iff (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    IsCongruenceSubgroup Γ'.liftSL ↔
      (Gamma Γ'.liftSL.strictLevel).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) ≤ Γ' := by
  rw [isCongruenceSubgroup_iff_Gamma_strictLevel_le, Subgroup.liftSL_def,
    Subgroup.map_le_iff_le_comap]

end Wohlfahrt

end CongruenceSubgroup

/-! ### The congruence closure -/

namespace Subgroup

section CongruenceClosure

open CongruenceSubgroup

variable {Γ Δ : Subgroup SL(2, ℤ)}

/-- **The congruence closure** of a subgroup `Γ ≤ SL(2, ℤ)`: the intersection of all congruence
subgroups containing `Γ`. -/
def congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  sInf {Δ | IsCongruenceSubgroup Δ ∧ Γ ≤ Δ}

/-- Unfolding: `Γ.congruenceClosure` is the infimum of all congruence overgroups of `Γ`. -/
theorem congruenceClosure_def (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure = sInf {Δ | IsCongruenceSubgroup Δ ∧ Γ ≤ Δ} := (rfl)

/-- An element lies in `Γ.congruenceClosure` iff it lies in every congruence overgroup of `Γ`. -/
theorem mem_congruenceClosure {γ : SL(2, ℤ)} :
    γ ∈ Γ.congruenceClosure ↔ ∀ Δ, IsCongruenceSubgroup Δ → Γ ≤ Δ → γ ∈ Δ := by
  simp [congruenceClosure_def, Subgroup.mem_sInf]

/-- Every subgroup is contained in its congruence closure. -/
theorem le_congruenceClosure (Γ : Subgroup SL(2, ℤ)) : Γ ≤ Γ.congruenceClosure :=
  le_sInf fun _ h ↦ h.2

/-- Any congruence subgroup containing `Γ` contains `Γ.congruenceClosure`. -/
theorem congruenceClosure_le (hΔ : IsCongruenceSubgroup Δ) (h : Γ ≤ Δ) :
    Γ.congruenceClosure ≤ Δ :=
  sInf_le ⟨hΔ, h⟩

/-- Universal property of the congruence closure with respect to congruence overgroups. -/
theorem congruenceClosure_le_iff (hΔ : IsCongruenceSubgroup Δ) :
    Γ.congruenceClosure ≤ Δ ↔ Γ ≤ Δ :=
  ⟨Γ.le_congruenceClosure.trans, congruenceClosure_le hΔ⟩

/-- Taking the congruence closure is monotone. -/
theorem congruenceClosure_mono : Monotone Subgroup.congruenceClosure :=
  fun _ _ h ↦ le_sInf fun _ ⟨hΔ, hle⟩ ↦ congruenceClosure_le hΔ (h.trans hle)

/-- Taking the congruence closure is idempotent. -/
@[simp]
theorem congruenceClosure_congruenceClosure (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure.congruenceClosure = Γ.congruenceClosure :=
  le_antisymm
    (le_sInf fun _ ⟨hΔ, hle⟩ ↦ congruenceClosure_le hΔ (congruenceClosure_le hΔ hle))
    (le_congruenceClosure _)

/-- A congruence subgroup equals its own congruence closure. -/
theorem congruenceClosure_eq_self_of_isCongruenceSubgroup (hΓ : IsCongruenceSubgroup Γ) :
    Γ.congruenceClosure = Γ :=
  le_antisymm (congruenceClosure_le hΓ le_rfl) Γ.le_congruenceClosure

/-- The congruence closure of `SL(2, ℤ)` is `SL(2, ℤ)`. -/
@[simp]
theorem congruenceClosure_top : (⊤ : Subgroup SL(2, ℤ)).congruenceClosure = ⊤ :=
  congruenceClosure_eq_self_of_isCongruenceSubgroup isCongruenceSubgroup_top

/-- The congruence closure of the trivial subgroup is trivial: the principal congruence subgroups
`Γ(N)` (`N ≠ 0`) intersect in `⊥`. In particular, the congruence closure of an infinite-index
subgroup need not be a congruence subgroup. -/
@[simp]
theorem congruenceClosure_bot : (⊥ : Subgroup SL(2, ℤ)).congruenceClosure = ⊥ := by
  refine eq_bot_iff.mpr fun γ hγ ↦ Subgroup.mem_bot.mpr ?_
  ext i j
  refine Int.eq_of_eventually_prime_intCast_eq <| Filter.Eventually.of_forall fun p hp ↦ ?_
  have : NeZero p := ⟨hp.ne_zero⟩
  have hmem : γ ∈ Gamma p :=
    (mem_congruenceClosure.mp hγ) (Gamma p) (Gamma_is_cong_sub p) bot_le
  simpa [Matrix.one_apply] using congr_fun₂ (map_eq_one_of_mem_Gamma hmem) i j

/-- A finite-index subgroup has finite-index congruence closure. -/
instance instFiniteIndexCongruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure.FiniteIndex :=
  Subgroup.finiteIndex_of_le Γ.le_congruenceClosure

/-- The strict level of `Γ.congruenceClosure` divides the strict level of `Γ`. -/
theorem strictLevel_congruenceClosure_dvd (Γ : Subgroup SL(2, ℤ)) :
    Γ.congruenceClosure.strictLevel ∣ Γ.strictLevel :=
  strictLevel_dvd_of_le Γ.le_congruenceClosure

/-- Adjoining the centre commutes with taking the congruence closure, unconditionally for every
subgroup `Γ ≤ SL(2, ℤ)`. -/
theorem congruenceClosure_withCenter (Γ : Subgroup SL(2, ℤ)) :
    Γ.withCenter.congruenceClosure = Γ.congruenceClosure.withCenter := by
  refine le_antisymm ?_ (withCenter_le_iff.mpr
    ⟨congruenceClosure_mono Γ.le_withCenter,
      Γ.center_le_withCenter.trans Γ.withCenter.le_congruenceClosure⟩)
  intro x hx
  by_contra hxnot
  have hx1 : x ∉ Γ.congruenceClosure := fun h ↦ hxnot (le_withCenter _ h)
  have hx2 : -x ∉ Γ.congruenceClosure := fun h ↦
    hxnot (mem_withCenter_iff_exists_eq_or_eq_neg.mpr ⟨-x, h, Or.inr (neg_neg x).symm⟩)
  rw [mem_congruenceClosure] at hx1 hx2
  push Not at hx1 hx2
  obtain ⟨Δ₁, hΔ₁, hΓ₁, hxΔ₁⟩ := hx1
  obtain ⟨Δ₂, hΔ₂, hΓ₂, hxΔ₂⟩ := hx2
  set Δ : Subgroup SL(2, ℤ) := Δ₁ ⊓ Δ₂
  have hΔ_cong : IsCongruenceSubgroup Δ.withCenter :=
    isCongruenceSubgroup_trans _ _ Δ.le_withCenter (isCongruenceSubgroup_inf_iff.mpr ⟨hΔ₁, hΔ₂⟩)
  have hΓ_le : Γ.withCenter ≤ Δ.withCenter :=
    withCenter_le_iff.mpr ⟨(le_inf hΓ₁ hΓ₂).trans Δ.le_withCenter, Δ.center_le_withCenter⟩
  obtain ⟨y, hy, rfl | rfl⟩ := mem_withCenter_iff_exists_eq_or_eq_neg.mp
    (mem_congruenceClosure.mp hx Δ.withCenter hΔ_cong hΓ_le)
  · exact hxΔ₁ hy.1
  · exact hxΔ₂ (by simpa using hy.2)

/-- Conjugation commutes with taking the congruence closure. -/
theorem congruenceClosure_smul (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ)) :
    (g • Γ).congruenceClosure = g • Γ.congruenceClosure := by
  have hle : ∀ (h : ConjAct SL(2, ℤ)) (H : Subgroup SL(2, ℤ)),
      h • H.congruenceClosure ≤ (h • H).congruenceClosure := fun h H ↦ by
    refine le_sInf fun Δ ⟨hΔ, hHΔ⟩ ↦ ?_
    have hinv : H.congruenceClosure ≤ h⁻¹ • Δ :=
      congruenceClosure_le (conj_cong_is_cong h⁻¹ Δ hΔ)
        (by simpa [inv_smul_smul] using
          (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := h⁻¹)).mpr hHΔ)
    simpa [smul_inv_smul] using
      (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := h)).mpr hinv
  refine le_antisymm ?_ (hle g Γ)
  have := hle g⁻¹ (g • Γ)
  rw [inv_smul_smul] at this
  simpa [smul_inv_smul] using (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := g)).mpr this

/-- The congruence closure of a normal subgroup is normal. -/
instance instNormalCongruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.Normal] :
    Γ.congruenceClosure.Normal where
  conj_mem n hn g := by
    have hmem : ConjAct.toConjAct g • n ∈ ConjAct.toConjAct g • Γ.congruenceClosure :=
      Subgroup.smul_mem_pointwise_smul n (ConjAct.toConjAct g) Γ.congruenceClosure hn
    rw [← congruenceClosure_smul, Subgroup.Normal.conjAct ‹Γ.Normal›] at hmem
    simpa [ConjAct.smul_def] using hmem

/-- For every nonzero `N`, the join `Γ ⊔ Γ(N)` is a congruence subgroup containing `Γ`, hence
contains `Γ.congruenceClosure`. -/
theorem congruenceClosure_le_sup_Gamma (Γ : Subgroup SL(2, ℤ)) {N : ℕ} (hN : N ≠ 0) :
    Γ.congruenceClosure ≤ Γ ⊔ Gamma N :=
  have : NeZero N := ⟨hN⟩
  congruenceClosure_le (isCongruenceSubgroup_trans _ _ le_sup_right (Gamma_is_cong_sub N))
    le_sup_left

/-- **Explicit formula for the congruence closure**: for any nonzero multiple `N` of
`Γ.strictLevel`, `Γ.congruenceClosure = Γ ⊔ Γ(N)`.

By Wohlfahrt's theorem, every congruence overgroup `Δ` of `Γ` has strict level dividing
`Γ.strictLevel` and hence `N`, so `Δ` contains `Γ(N)`. -/
theorem congruenceClosure_eq_sup_Gamma_of_strictLevel_dvd {N : ℕ} (hN : N ≠ 0)
    (hdvd : Γ.strictLevel ∣ N) :
    Γ.congruenceClosure = Γ ⊔ Gamma N := by
  refine le_antisymm (Γ.congruenceClosure_le_sup_Gamma hN)
    (le_sInf fun Δ ⟨hΔ, hΓΔ⟩ ↦ sup_le hΓΔ ?_)
  exact (Gamma_le_Gamma_of_dvd ((strictLevel_dvd_of_le hΓΔ).trans hdvd)).trans
    (Gamma_strictLevel_le_of_isCongruenceSubgroup hΔ)

/-- **Congruence closure at finite index**: for a finite-index subgroup `Γ ≤ SL(2, ℤ)`,
`Γ.congruenceClosure = Γ ⊔ Γ(Γ.strictLevel)`. -/
theorem congruenceClosure_eq_sup_Gamma_strictLevel (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure = Γ ⊔ Gamma Γ.strictLevel :=
  congruenceClosure_eq_sup_Gamma_of_strictLevel_dvd Γ.strictLevel_pos.ne' dvd_rfl

/-- Every subgroup with nonzero strict level has congruence subgroup congruence closure. -/
theorem isCongruenceSubgroup_congruenceClosure_of_strictLevel_ne_zero (h : Γ.strictLevel ≠ 0) :
    IsCongruenceSubgroup Γ.congruenceClosure :=
  ⟨Γ.strictLevel, h, (congruenceClosure_eq_sup_Gamma_of_strictLevel_dvd h dvd_rfl) ▸ le_sup_right⟩

/-- The congruence closure of a finite-index subgroup is a congruence subgroup. -/
theorem isCongruenceSubgroup_congruenceClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    IsCongruenceSubgroup Γ.congruenceClosure :=
  isCongruenceSubgroup_congruenceClosure_of_strictLevel_ne_zero Γ.strictLevel_pos.ne'

/-- A subgroup with nonzero strict level equals its congruence closure if and only if it is a
congruence subgroup. -/
theorem congruenceClosure_eq_self_iff_of_strictLevel_ne_zero (h : Γ.strictLevel ≠ 0) :
    Γ.congruenceClosure = Γ ↔ IsCongruenceSubgroup Γ :=
  ⟨fun heq ↦ heq ▸ isCongruenceSubgroup_congruenceClosure_of_strictLevel_ne_zero h,
    congruenceClosure_eq_self_of_isCongruenceSubgroup⟩

/-- A finite-index subgroup equals its congruence closure if and only if it is a congruence
subgroup.

The `[Γ.FiniteIndex]` hypothesis cannot be dropped: `⊥.congruenceClosure = ⊥` while `⊥` is not a
congruence subgroup (`congruenceClosure_bot`, `not_isCongruenceSubgroup_bot`). -/
theorem congruenceClosure_eq_self_iff (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Γ.congruenceClosure = Γ ↔ IsCongruenceSubgroup Γ :=
  congruenceClosure_eq_self_iff_of_strictLevel_ne_zero Γ.strictLevel_pos.ne'

/-- **Reduction modulo any nonzero `N`**: for every subgroup `Γ ≤ SL(2, ℤ)` and every `N ≠ 0`,
`Γ.congruenceClosure` and `Γ` have the same image in `SL(2, ZMod N)`. -/
theorem map_intCast_zmod_congruenceClosure (Γ : Subgroup SL(2, ℤ)) {N : ℕ} (hN : N ≠ 0) :
    Γ.congruenceClosure.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) =
      Γ.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) := by
  refine le_antisymm ?_ (Subgroup.map_mono Γ.le_congruenceClosure)
  have hle := Subgroup.map_mono (f := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)))
    (Γ.congruenceClosure_le_sup_Gamma hN)
  rw [Subgroup.map_sup] at hle
  have hker : (Gamma N).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨γ, hγ, rfl⟩
    exact Subgroup.mem_bot.mpr (Gamma_mem'.mp hγ)
  rwa [hker, sup_bot_eq] at hle

/-- **Noncongruence lift of a congruence subgroup**: if `Γ` is not a congruence subgroup while
`Γ.withCenter = ±Γ` is, then `Γ.congruenceClosure = Γ.withCenter`. -/
theorem congruenceClosure_eq_withCenter_of_not_isCongruenceSubgroup
    (hΓ : ¬ IsCongruenceSubgroup Γ) (hpm : IsCongruenceSubgroup Γ.withCenter) :
    Γ.congruenceClosure = Γ.withCenter := by
  have hneg : (-1 : SL(2, ℤ)) ∉ Γ := fun h ↦ by
    rw [withCenter_eq_self_iff.mpr
      (Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr h)] at hpm
    exact hΓ hpm
  have : Γ.withCenter.FiniteIndex := hpm.finiteIndex
  have : Γ.FiniteIndex :=
    ⟨by
      rw [Matrix.SpecialLinearGroup.index_eq_two_mul_index_withCenter_of_neg_one_notMem hneg]
      exact mul_ne_zero two_ne_zero FiniteIndex.index_ne_zero⟩
  have hle : Γ.congruenceClosure ≤ Γ.withCenter := congruenceClosure_le hpm Γ.le_withCenter
  have hne : Γ.congruenceClosure ≠ Γ := fun h ↦ hΓ ((congruenceClosure_eq_self_iff Γ).mp h)
  have hlt : Γ < Γ.congruenceClosure := lt_of_le_of_ne Γ.le_congruenceClosure hne.symm
  obtain ⟨x, hx_cl, hx_not⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨γ, hγ, rfl | rfl⟩ := mem_withCenter_iff_exists_eq_or_eq_neg.mp (hle hx_cl)
  · exact absurd hγ hx_not
  · have hneg_cl : (-1 : SL(2, ℤ)) ∈ Γ.congruenceClosure := by
      have := mul_mem hx_cl (inv_mem (Γ.le_congruenceClosure hγ))
      simpa using this
    refine le_antisymm hle (withCenter_le_iff.mpr ⟨Γ.le_congruenceClosure, ?_⟩)
    exact Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr hneg_cl

/-- **Prime-index noncongruence subgroups have full congruence closure**: if `Γ` is not a
congruence subgroup and its index in `SL(2, ℤ)` is prime, then `Γ.congruenceClosure = ⊤`. -/
theorem congruenceClosure_eq_top_of_prime_index
    (hΓ : ¬ IsCongruenceSubgroup Γ) (hp : Γ.index.Prime) :
    Γ.congruenceClosure = ⊤ := by
  have : Γ.FiniteIndex := ⟨hp.ne_zero⟩
  have hdvd : Γ.congruenceClosure.index ∣ Γ.index := Subgroup.index_dvd_of_le Γ.le_congruenceClosure
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hself
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    have hrel : Γ.relIndex Γ.congruenceClosure = 1 := by
      have hmul := Subgroup.relIndex_mul_index Γ.le_congruenceClosure
      rw [hself] at hmul
      exact mul_right_cancel₀ hp.ne_zero (by simpa using hmul)
    have heq : Γ.congruenceClosure = Γ :=
      le_antisymm (Subgroup.relIndex_eq_one.mp hrel) Γ.le_congruenceClosure
    exact hΓ ((congruenceClosure_eq_self_iff Γ).mp heq)

end CongruenceClosure

end Subgroup

namespace CongruenceSubgroup

/-- Every principal congruence subgroup `Γ(N)` equals its congruence closure, including `N = 0`. -/
@[simp]
theorem congruenceClosure_Gamma (N : ℕ) : (Gamma N).congruenceClosure = Gamma N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [Gamma_zero_bot]
  · have : NeZero N := ⟨hN⟩
    exact Subgroup.congruenceClosure_eq_self_of_isCongruenceSubgroup (Gamma_is_cong_sub N)

/-- Every `Γ₀(N)` equals its congruence closure, including `N = 0`. -/
@[simp]
theorem congruenceClosure_Gamma0 (N : ℕ) : (Gamma0 N).congruenceClosure = Gamma0 N := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine le_antisymm (fun γ hγ ↦ mem_Gamma0_iff_dvd.mpr ?_) (Subgroup.le_congruenceClosure _)
    have h0 : γ 1 0 = 0 :=
      Int.eq_zero_of_eventually_prime_dvd <| Filter.Eventually.of_forall fun p hp ↦
        have : NeZero p := ⟨hp.ne_zero⟩
        mem_Gamma0_iff_dvd.mp <|
          Subgroup.mem_congruenceClosure.mp hγ (Gamma0 p) (Gamma0_is_congruence p)
            (Gamma0_le_Gamma0_of_dvd (dvd_zero p))
    simp [h0]
  · have : NeZero N := ⟨hN⟩
    exact Subgroup.congruenceClosure_eq_self_of_isCongruenceSubgroup (Gamma0_is_congruence N)

/-- Every `Γ₁(N)` equals its congruence closure, including `N = 0`. -/
@[simp]
theorem congruenceClosure_Gamma1 (N : ℕ) : (Gamma1 N).congruenceClosure = Gamma1 N := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine le_antisymm (fun γ hγ ↦ mem_Gamma1_iff_dvd_lowerRow.mpr ?_)
      (Subgroup.le_congruenceClosure _)
    have hM : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ 1 0 ∧ (p : ℤ) ∣ γ 1 1 - 1 := fun p hp ↦
      have : NeZero p := ⟨hp.ne_zero⟩
      mem_Gamma1_iff_dvd_lowerRow.mp <|
        Subgroup.mem_congruenceClosure.mp hγ (Gamma1 p) (Gamma1_is_congruence p)
          (Gamma1_le_Gamma1_of_dvd (dvd_zero p))
    have h10 : γ 1 0 = 0 :=
      Int.eq_zero_of_eventually_prime_dvd <| Filter.Eventually.of_forall fun p hp ↦ (hM p hp).1
    have h11 : γ 1 1 - 1 = 0 :=
      Int.eq_zero_of_eventually_prime_dvd <| Filter.Eventually.of_forall fun p hp ↦ (hM p hp).2
    simp [h10, h11]
  · have : NeZero N := ⟨hN⟩
    exact Subgroup.congruenceClosure_eq_self_of_isCongruenceSubgroup (Gamma1_is_congruence N)

/-! ### Separating witnesses -/

section Witnesses

private lemma apply_zero_zero_mul_mod_four {A B : SL(2, ℤ)} (hA : A ∈ Gamma 2)
    (hB : B ∈ Gamma 2) :
    (((A * B) 0 0 : ℤ) : ZMod 4) = ((A 0 0 : ℤ) : ZMod 4) * ((B 0 0 : ℤ) : ZMod 4) := by
  obtain ⟨b, hb⟩ : (2 : ℤ) ∣ A 0 1 := by
    simpa using Matrix.SpecialLinearGroup.mem_ker_map_intCast_zmod_iff.mp hA 0 1
  obtain ⟨c, hc⟩ : (2 : ℤ) ∣ B 1 0 := by
    simpa using Matrix.SpecialLinearGroup.mem_ker_map_intCast_zmod_iff.mp hB 1 0
  have hmul : ((A * B) 0 0 : ℤ) = A 0 0 * B 0 0 + 4 * (b * c) := by
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination B 1 0 * hb + 2 * b * hc
  have h4 : (4 : ZMod 4) = 0 := by decide
  rw [hmul]
  simp [h4]

/-- The congruence subgroup `{γ ∈ Γ(2) | γ₀₀ ≡ 1 (mod 4)}`, witnessing that a subgroup excluding
`-I` can have strict level twice its signed level and fail to contain `Γ(signed level)`. -/
private def gammaTwoModFour : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Gamma 2 ∧ ((γ 0 0 : ℤ) : ZMod 4) = 1}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' {A B} hA hB :=
    ⟨mul_mem hA.1 hB.1, by rw [apply_zero_zero_mul_mod_four hA.1 hB.1, hA.2, hB.2, mul_one]⟩
  inv_mem' {A} hA := ⟨inv_mem hA.1, by
    have h := apply_zero_zero_mul_mod_four hA.1 (inv_mem hA.1)
    rw [mul_inv_cancel, hA.2, one_mul] at h
    simpa using h.symm⟩

private lemma gammaTwoModFour_withCenter : gammaTwoModFour.withCenter = Gamma 2 := by
  refine le_antisymm
    (Subgroup.withCenter_le_iff.mpr ⟨fun _ h ↦ h.1,
      Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr
        (neg_one_mem_Gamma_iff.mpr dvd_rfl)⟩)
    fun γ hγ ↦ Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mpr ?_
  have h4 : (4 : ZMod 4) = 0 := by decide
  have hodd : ((γ 0 0 : ℤ) : ZMod 4) = 1 ∨ ((γ 0 0 : ℤ) : ZMod 4) = 3 := by
    obtain ⟨k, hk⟩ : (2 : ℤ) ∣ γ 0 0 - 1 := by
      simpa using Matrix.SpecialLinearGroup.mem_ker_map_intCast_zmod_iff.mp hγ 0 0
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      have h4eq : γ 0 0 = 1 + 4 * m := by omega
      rw [h4eq]
      simp [h4]
    · right
      have h4eq : γ 0 0 = 3 + 4 * m := by omega
      rw [h4eq]
      simp [h4]
  rcases hodd with h1 | h3
  · exact ⟨γ, ⟨hγ, h1⟩, Or.inl rfl⟩
  · refine ⟨-γ, ⟨?_, ?_⟩, Or.inr (neg_neg γ).symm⟩
    · rw [← neg_one_mul]
      exact mul_mem (neg_one_mem_Gamma_iff.mpr dvd_rfl) hγ
    · simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, h3]
      decide

/-- **Signed level is strictly weaker than strict level for lifts**: the subgroup
`{γ ∈ Γ(2) | γ₀₀ ≡ 1 (mod 4)}` is a congruence subgroup excluding `-I` whose signed level
`Γ.withCenter.strictLevel` is `2` while its strict level is `4`; it contains `Γ(4)` but does not
contain `Γ(2)`. -/
theorem exists_isCongruenceSubgroup_strictLevel_eq_two_mul_strictLevel_withCenter :
    ∃ Γ : Subgroup SL(2, ℤ),
      IsCongruenceSubgroup Γ ∧
      (-1 : SL(2, ℤ)) ∉ Γ ∧
      Γ.withCenter = Gamma 2 ∧
      Γ.withCenter.strictLevel = 2 ∧
      Γ.strictLevel = 4 ∧
      ¬ Gamma Γ.withCenter.strictLevel ≤ Γ ∧
      Gamma Γ.strictLevel ≤ Γ := by
  have h4 : Gamma 4 ≤ gammaTwoModFour := fun γ hγ ↦
    ⟨Gamma_le_Gamma_of_dvd (by decide : 2 ∣ 4) hγ, (Gamma_mem.mp hγ).1⟩
  have hcong : IsCongruenceSubgroup gammaTwoModFour := ⟨4, by decide, h4⟩
  have hneg : (-1 : SL(2, ℤ)) ∉ gammaTwoModFour := fun h ↦ by
    have h00 : ((-1 : ℤ) : ZMod 4) = 1 := by simpa using h.2
    exact absurd h00 (by decide)
  have hwc : gammaTwoModFour.withCenter = Gamma 2 := gammaTwoModFour_withCenter
  have hnot2 : ¬ gammaTwoModFour.strictLevel ∣ 2 := by
    intro hdvd
    set σ : SL(2, ℤ) := ⟨!![1, -1; 1, 0], by decide⟩
    have hmem : σ * ModularGroup.T ^ (2 : ℤ) * σ⁻¹ ∈ gammaTwoModFour := by
      simpa using Subgroup.strictLevel_dvd_iff.mp hdvd σ
    have h00 : ((σ * ModularGroup.T ^ (2 : ℤ) * σ⁻¹) 0 0 : ℤ) = -1 := by
      have := congr_fun₂ (σ.coe_conj_T_zpow 2) 0 0
      simpa [σ] using this
    have hmem2 : (((σ * ModularGroup.T ^ (2 : ℤ) * σ⁻¹) 0 0 : ℤ) : ZMod 4) = 1 := hmem.2
    rw [h00] at hmem2
    exact absurd hmem2 (by decide)
  have hsl : gammaTwoModFour.strictLevel = 4 := by
    have hwc_sl : gammaTwoModFour.withCenter.strictLevel = 2 := by rw [hwc, strictLevel_Gamma]
    rcases gammaTwoModFour.strictLevel_eq_or_eq_two_mul_strictLevel_withCenter with h | h
    · exact absurd (by rw [h, hwc_sl]) hnot2
    · rw [h, hwc_sl]
  have hnotGamma2 : ¬ Gamma 2 ≤ gammaTwoModFour := fun h ↦
    hneg (h (neg_one_mem_Gamma_iff.mpr dvd_rfl))
  refine ⟨gammaTwoModFour, hcong, hneg, hwc, by rw [hwc, strictLevel_Gamma], hsl, ?_, ?_⟩
  · rwa [hwc, strictLevel_Gamma]
  · rwa [hsl]

private def permS8 : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 3, 2, 5, 4, 7, 6]
  invFun := ![0, 1, 3, 2, 5, 4, 7, 6]
  left_inv := by decide
  right_inv := by decide

private def permT8 : Equiv.Perm (Fin 8) where
  toFun := ![1, 3, 0, 5, 7, 4, 2, 6]
  invFun := ![2, 0, 6, 1, 5, 3, 7, 4]
  left_inv := by decide
  right_inv := by decide

private def permU8 : Equiv.Perm (Fin 8) := permS8 * permT8⁻¹

private lemma permU8_pow_three : permU8 ^ 3 = 1 := by decide
private lemma permS8_sq : permS8 ^ 2 = 1 := by decide
private lemma permT8_mul_permS8_mul_permU8 : permT8 * permS8 * permU8 = 1 := by decide
private lemma permT8_pow_eight : permT8 ^ 8 = 1 := by decide

private noncomputable def hom8 : SL(2, ℤ) →* Equiv.Perm (Fin 8) :=
  ((TauCeti.TriangleGroup.lift permU8 permS8 permT8 permU8_pow_three permS8_sq (pow_zero _)
      permT8_mul_permS8_mul_permU8).comp
    TauCeti.ModularGroup.modularEquiv.symm.toMonoidHom).comp
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

private lemma hom8_S : hom8 ModularGroup.S = permS8 := by
  simp only [hom8, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.coe_mk',
    ← TauCeti.ModularGroup.modularEquiv_y, MulEquiv.symm_apply_apply,
    TauCeti.TriangleGroup.lift_y]

private lemma hom8_T : hom8 ModularGroup.T = permT8 := by
  simp only [hom8, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.coe_mk',
    ← TauCeti.ModularGroup.modularEquiv_z, MulEquiv.symm_apply_apply,
    TauCeti.TriangleGroup.lift_z]

private noncomputable def noncong8 : Subgroup SL(2, ℤ) :=
  @MulAction.stabilizer SL(2, ℤ) (Fin 8) _ (MulAction.compHom (Fin 8) hom8) 0

private lemma mem_noncong8 {g : SL(2, ℤ)} : g ∈ noncong8 ↔ hom8 g 0 = 0 := Iff.rfl

private lemma exists_permT8_pow_apply_zero (i : Fin 8) : ∃ k : Fin 8, (permT8 ^ k.val) 0 = i := by
  fin_cases i
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨7, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨6, by decide⟩
  · exact ⟨5, by decide⟩

private lemma noncong8_index : noncong8.index = 8 := by
  let : MulAction SL(2, ℤ) (Fin 8) := MulAction.compHom (Fin 8) hom8
  have : MulAction.IsPretransitive SL(2, ℤ) (Fin 8) := ⟨fun x y ↦ by
    obtain ⟨kx, hkx⟩ := exists_permT8_pow_apply_zero x
    obtain ⟨ky, hky⟩ := exists_permT8_pow_apply_zero y
    refine ⟨ModularGroup.T ^ ky.val * (ModularGroup.T ^ kx.val)⁻¹, ?_⟩
    simp only [MulAction.compHom_smul_def, map_mul, map_inv, map_pow, hom8_T]
    rw [← hkx]
    simp [hky]⟩
  rw [noncong8, MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card,
    Fintype.card_fin]

private lemma noncong8_strictLevel : noncong8.strictLevel = 8 := by
  refine Nat.dvd_antisymm ?_ ?_
  · rw [Subgroup.strictLevel_dvd_iff]
    intro σ
    rw [mem_noncong8, map_mul, map_mul, map_pow, map_inv, hom8_T, permT8_pow_eight, mul_one,
      mul_inv_cancel, Equiv.Perm.one_apply]
  · have hmem : ModularGroup.T ^ noncong8.strictLevel ∈ noncong8 := by
      simpa using Subgroup.conj_T_pow_strictLevel_mem (Γ := noncong8) 1
    rw [mem_noncong8, map_pow, hom8_T] at hmem
    have hrem : (permT8 ^ (noncong8.strictLevel % 8)) 0 = 0 := by
      have hdiv := (Nat.div_add_mod noncong8.strictLevel 8).symm
      rw [hdiv, pow_add, pow_mul, permT8_pow_eight, one_pow, one_mul] at hmem
      exact hmem
    have hlt : noncong8.strictLevel % 8 < 8 := Nat.mod_lt _ (by decide)
    have hmod : noncong8.strictLevel % 8 = 0 := by
      have : ∀ k : Fin 8, (permT8 ^ k.val) 0 = 0 → k = 0 := by decide
      exact congrArg Fin.val (this ⟨noncong8.strictLevel % 8, hlt⟩ hrem)
    exact Nat.dvd_of_mod_eq_zero hmod

private lemma not_isCongruenceSubgroup_noncong8 : ¬ IsCongruenceSubgroup noncong8 := by
  have : noncong8.FiniteIndex := ⟨by rw [noncong8_index]; decide⟩
  rw [isCongruenceSubgroup_iff_Gamma_strictLevel_le, noncong8_strictLevel]
  intro hle
  set g : SL(2, ℤ) :=
    ModularGroup.T ^ (5 : ℤ) * ModularGroup.S⁻¹ * ModularGroup.T ^ (2 : ℤ) * ModularGroup.S⁻¹ *
      ModularGroup.T ^ (-3 : ℤ) * ModularGroup.S⁻¹ * ModularGroup.T ^ (2 : ℤ) * ModularGroup.S
  have hS : (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 0] := ModularGroup.coe_S
  have hSinv : ((ModularGroup.S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hg_coe : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![73, -32; 16, -7] := by
    simp only [g, coe_mul, ModularGroup.coe_T_zpow, hS, hSinv]
    decide
  have hg_Gamma : g ∈ Gamma 8 := by
    rw [Gamma_mem]
    have h00 : g 0 0 = 73 := by simpa using congr_fun₂ hg_coe 0 0
    have h01 : g 0 1 = -32 := by simpa using congr_fun₂ hg_coe 0 1
    have h10 : g 1 0 = 16 := by simpa using congr_fun₂ hg_coe 1 0
    have h11 : g 1 1 = -7 := by simpa using congr_fun₂ hg_coe 1 1
    rw [h00, h01, h10, h11]
    decide
  have hg_mem : hom8 g 0 = 0 := hle hg_Gamma
  have hg_val : hom8 g 0 = 5 := by
    simp only [g, map_mul, map_zpow, map_inv, hom8_T, hom8_S]
    decide
  exact absurd (hg_val.symm.trans hg_mem) (by decide)

private lemma noncong8_eq_top_of_lt {H : Subgroup SL(2, ℤ)} (hH : noncong8 < H) : H = ⊤ := by
  have hS : ModularGroup.S ∈ H := hH.le (by rw [mem_noncong8, hom8_S]; decide)
  have hT8 : ModularGroup.T ^ 8 ∈ H :=
    hH.le (by rw [mem_noncong8, map_pow, hom8_T, permT8_pow_eight]; rfl)
  have hmem_of_eq : ∀ {a b : SL(2, ℤ)}, hom8 a 0 = hom8 b 0 → a ∈ H → b ∈ H := by
    intro a b hab ha
    have hdiff : a⁻¹ * b ∈ noncong8 := by
      rw [mem_noncong8, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
        Equiv.symm_apply_eq, hab]
    simpa [mul_assoc] using mul_mem ha (hH.le hdiff)
  have hT_of_cop : ∀ {m q r : ℕ}, ModularGroup.T ^ m ∈ H → m * q = 1 + 8 * r →
      ModularGroup.T ∈ H := fun {m q r} hm h ↦ by
    have h1 : ModularGroup.T = (ModularGroup.T ^ m) ^ q * ((ModularGroup.T ^ 8) ^ r)⁻¹ := by
      rw [← pow_mul, ← pow_mul, h, pow_add, pow_one, mul_inv_cancel_right]
    exact h1 ▸ mul_mem (pow_mem hm q) (inv_mem (pow_mem hT8 r))
  obtain ⟨x, hxH, hxnot⟩ := IsConcreteLE.exists_of_lt hH
  obtain ⟨k, hk⟩ := exists_permT8_pow_apply_zero (hom8 x 0)
  have hTk : ModularGroup.T ^ k.val ∈ H :=
    hmem_of_eq (a := x) (by rw [map_pow, hom8_T, hk]) hxH
  have hT : ModularGroup.T ∈ H := by
    fin_cases k
    · exact absurd (by simpa [mem_noncong8] using hk.symm) hxnot
    · simpa using hTk
    · exact hT_of_cop (m := 7) (q := 7) (r := 6)
        (hmem_of_eq (a := ModularGroup.S * ModularGroup.T ^ 2)
          (by simp only [map_mul, map_pow, hom8_S, hom8_T]; decide) (mul_mem hS hTk)) rfl
    · exact hT_of_cop hTk (q := 3) (r := 1) rfl
    · exact hT_of_cop (m := 3) (q := 3) (r := 1)
        (hmem_of_eq (a := ModularGroup.S * ModularGroup.T ^ 4)
          (by simp only [map_mul, map_pow, hom8_S, hom8_T]; decide) (mul_mem hS hTk)) rfl
    · exact hT_of_cop hTk (q := 5) (r := 3) rfl
    · exact hT_of_cop (m := 5) (q := 5) (r := 3)
        (hmem_of_eq (a := ModularGroup.S * ModularGroup.T ^ 6)
          (by simp only [map_mul, map_pow, hom8_S, hom8_T]; decide) (mul_mem hS hTk)) rfl
    · exact hT_of_cop hTk (q := 7) (r := 6) rfl
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨j, hj⟩ := exists_permT8_pow_apply_zero (hom8 y 0)
  exact hmem_of_eq (a := ModularGroup.T ^ j.val) (by rw [map_pow, hom8_T, hj]) (pow_mem hT j.val)

/-- **Index-`8` noncongruence witness with full congruence closure**: there exists a subgroup
`Γ ≤ SL(2, ℤ)` of index `8` and strict level `8` that is not a congruence subgroup and whose
congruence closure is all of `SL(2, ℤ)`. -/
theorem exists_not_isCongruenceSubgroup_index_eight_congruenceClosure_eq_top :
    ∃ Γ : Subgroup SL(2, ℤ),
      Γ.index = 8 ∧
      Γ.strictLevel = 8 ∧
      ¬ IsCongruenceSubgroup Γ ∧
      Γ.congruenceClosure = ⊤ := by
  have : noncong8.FiniteIndex := ⟨by rw [noncong8_index]; decide⟩
  have hlt : noncong8 < noncong8.congruenceClosure :=
    lt_of_le_of_ne noncong8.le_congruenceClosure fun h ↦
      not_isCongruenceSubgroup_noncong8
        ((Subgroup.congruenceClosure_eq_self_iff noncong8).mp h.symm)
  exact ⟨noncong8, noncong8_index, noncong8_strictLevel, not_isCongruenceSubgroup_noncong8,
    noncong8_eq_top_of_lt hlt⟩

end Witnesses

end CongruenceSubgroup
