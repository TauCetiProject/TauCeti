/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Width

/-!
# The strict level of a subgroup of `SL₂(ℤ)`

The **strict level** of `Γ ≤ SL(2, ℤ)` is the least `N > 0` such that every conjugate
`σ Tᴺ σ⁻¹` of the translation `Tᴺ` lies in `Γ`, or `0` if there is no such `N`. Equivalently it
is the least common multiple of the strict widths of `Γ` at all of its cusps, the strict width at
the cusp `σ ∞` being the least `h > 0` with `σ Tʰ σ⁻¹ ∈ Γ`. No sign is allowed: when `-1 ∉ Γ`, a
cusp at which only `-σ Tʰ σ⁻¹` lies in `Γ` has strict width `2h`, so the strict level can be
twice the level of `±Γ`, as for `{γ ∈ Γ(2) | a ≡ 1 mod 4}`, of strict level `4`. It is the
modulus in the strict form of Wohlfahrt's theorem: a finite-index `Γ` is a congruence subgroup
exactly when it contains `Γ(N)` for `N` its strict level.

The definition is the order of the image of `T` modulo the normal core of `Γ`, the largest normal
subgroup of `SL(2, ℤ)` contained in `Γ`, whose elements are exactly those all of whose conjugates
lie in `Γ`.

## Main declarations

* `Subgroup.strictLevel`: the strict level.
* `Subgroup.strictLevel_dvd_iff`, `Subgroup.strictLevel_dvd_iff_zpow`: the exponents `m` with
  `σ Tᵐ σ⁻¹ ∈ Γ` for every `σ` are exactly the multiples of the strict level.
* `Subgroup.strictLevel_eq_sInf`: the strict level is the least such positive exponent.
* `Subgroup.strictLevel_dvd_iff_T_pow_mem_normalCore`: the same multiples, read in the normal
  core.
* `Subgroup.strictLevel_pos`: a finite-index subgroup has positive strict level.
* `Subgroup.strictLevel_dvd_iff_forall_cuspTranslationOrbitWidth_dvd`,
  `Subgroup.strictLevel_eq_lcm_cuspTranslationOrbitWidth`: the strict level is the least common
  multiple of the widths of the cusp translation orbits.
* `Subgroup.strictLevel_inf`, `Subgroup.strictLevel_normalCore`: the strict level of an
  intersection is the least common multiple of the strict levels, and passing to the normal core
  does not change it.
* `CongruenceSubgroup.strictLevel_Gamma`, `CongruenceSubgroup.strictLevel_Gamma0`,
  `CongruenceSubgroup.strictLevel_Gamma1`: `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` have strict level `N`.
* `CongruenceSubgroup.strictLevel_dvd_of_Gamma_le`: a subgroup containing `Γ(N)` has strict level
  dividing `N`.

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535.
* I. Kiming, M. Schütt and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. 83 (2011), 96–120, §3.
-/

public section

open Matrix Matrix.SpecialLinearGroup TauCeti.ModularForm
open scoped MatrixGroups

namespace Subgroup

variable {Γ Γ₁ Γ₂ : Subgroup SL(2, ℤ)}

/-- The **strict level** of `Γ ≤ SL(2, ℤ)`: the least `N > 0` such that `σ * T ^ N * σ⁻¹ ∈ Γ`
for every `σ ∈ SL(2, ℤ)`, or `0` if there is no such `N` (`strictLevel_eq_sInf`). It is defined
as the order of the image of `T` modulo the normal core of `Γ`. -/
noncomputable def strictLevel (Γ : Subgroup SL(2, ℤ)) : ℕ :=
  orderOf (QuotientGroup.mk ModularGroup.T : SL(2, ℤ) ⧸ Γ.normalCore)

/-- The integers `m` with `σ * T ^ m * σ⁻¹ ∈ Γ` for every `σ` are the multiples of the strict
level. -/
theorem strictLevel_dvd_iff_zpow {m : ℤ} :
    (Γ.strictLevel : ℤ) ∣ m ↔ ∀ σ : SL(2, ℤ), σ * ModularGroup.T ^ m * σ⁻¹ ∈ Γ := by
  rw [strictLevel, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow,
    QuotientGroup.eq_one_iff]
  -- membership in `normalCore` is, by definition, membership of every conjugate
  exact Iff.rfl

/-- The natural numbers `m` with `σ * T ^ m * σ⁻¹ ∈ Γ` for every `σ` are the multiples of the
strict level. -/
theorem strictLevel_dvd_iff {m : ℕ} :
    Γ.strictLevel ∣ m ↔ ∀ σ : SL(2, ℤ), σ * ModularGroup.T ^ m * σ⁻¹ ∈ Γ := by
  simpa only [Int.natCast_dvd_natCast, zpow_natCast] using strictLevel_dvd_iff_zpow (m := m)

/-- The strict level divides `m` exactly when `T ^ m` lies in the normal core of `Γ`. -/
theorem strictLevel_dvd_iff_T_pow_mem_normalCore {m : ℕ} :
    Γ.strictLevel ∣ m ↔ ModularGroup.T ^ m ∈ Γ.normalCore := by
  rw [strictLevel, orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]

/-- Every conjugate of `T ^ strictLevel Γ` lies in `Γ`. -/
theorem conj_T_pow_strictLevel_mem (σ : SL(2, ℤ)) :
    σ * ModularGroup.T ^ Γ.strictLevel * σ⁻¹ ∈ Γ :=
  strictLevel_dvd_iff.mp dvd_rfl σ

/-- The strict level is at most any positive `N` all of whose conjugates `σ * T ^ N * σ⁻¹` lie
in `Γ`. -/
theorem strictLevel_le {N : ℕ} (hN : 0 < N)
    (h : ∀ σ : SL(2, ℤ), σ * ModularGroup.T ^ N * σ⁻¹ ∈ Γ) : Γ.strictLevel ≤ N :=
  Nat.le_of_dvd hN (strictLevel_dvd_iff.mpr h)

/-- The strict level is the least positive `N` with `σ * T ^ N * σ⁻¹ ∈ Γ` for every `σ`, and `0`
when there is none. -/
theorem strictLevel_eq_sInf :
    Γ.strictLevel =
      sInf {N : ℕ | 0 < N ∧ ∀ σ : SL(2, ℤ), σ * ModularGroup.T ^ N * σ⁻¹ ∈ Γ} := by
  rw [strictLevel, orderOf, Function.minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  simp only [isPeriodicPt_mul_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    ← strictLevel_dvd_iff_T_pow_mem_normalCore, strictLevel_dvd_iff, gt_iff_lt]

/-- A subgroup of finite index has positive strict level. -/
theorem strictLevel_pos [Γ.FiniteIndex] : 0 < Γ.strictLevel :=
  orderOf_pos _

/-- For a normal subgroup, the strict level divides `m` exactly when `T ^ m ∈ Γ`. -/
theorem strictLevel_dvd_iff_of_normal [Γ.Normal] {m : ℕ} :
    Γ.strictLevel ∣ m ↔ ModularGroup.T ^ m ∈ Γ := by
  rw [strictLevel_dvd_iff]
  exact ⟨fun h ↦ by simpa using h 1, fun h σ ↦ ‹Γ.Normal›.conj_mem _ h σ⟩

/-- A larger subgroup has strict level dividing that of a smaller one. -/
theorem strictLevel_dvd_of_le (h : Γ₁ ≤ Γ₂) : Γ₂.strictLevel ∣ Γ₁.strictLevel :=
  strictLevel_dvd_iff.mpr fun σ ↦ h (conj_T_pow_strictLevel_mem σ)

/-- **The intersection law**: the strict level of `Γ₁ ⊓ Γ₂` is the least common multiple of the
strict levels of `Γ₁` and `Γ₂`. -/
theorem strictLevel_inf : (Γ₁ ⊓ Γ₂).strictLevel = Γ₁.strictLevel.lcm Γ₂.strictLevel :=
  Nat.dvd_right_iff_eq.mp fun m ↦ by
    simp only [strictLevel_dvd_iff, Nat.lcm_dvd_iff, mem_inf, forall_and]

/-- Passing to the normal core does not change the strict level. -/
@[simp]
theorem strictLevel_normalCore : Γ.normalCore.strictLevel = Γ.strictLevel :=
  Nat.dvd_right_iff_eq.mp fun m ↦ by
    rw [strictLevel_dvd_iff_of_normal, strictLevel_dvd_iff_T_pow_mem_normalCore]

/-- `SL(2, ℤ)` has strict level `1`. -/
@[simp]
theorem strictLevel_top : (⊤ : Subgroup SL(2, ℤ)).strictLevel = 1 :=
  Nat.dvd_one.mp (strictLevel_dvd_iff.mpr fun _ ↦ mem_top _)

/-- **The strict level is the least common multiple of the cusp widths**: it divides `m` exactly
when the width of every cusp translation orbit of `Γ` does. -/
theorem strictLevel_dvd_iff_forall_cuspTranslationOrbitWidth_dvd {m : ℕ} :
    Γ.strictLevel ∣ m ↔
      ∀ c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)),
        cuspTranslationOrbitWidth c ∣ m := by
  rw [strictLevel_dvd_iff]
  refine ⟨fun h c ↦ ?_, fun h σ ↦ ?_⟩
  · induction c using CuspTranslationOrbit.induction_on with
    | h γ => simpa only [cuspTranslationOrbitWidth_mk_dvd_iff, inv_inv] using h γ⁻¹
  · simpa only [cuspTranslationOrbitWidth_mk_dvd_iff, inv_inv] using
      h ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict σ⁻¹)⟧

/-- For `Γ` of finite index, the strict level is the least common multiple of the widths of its
finitely many cusp translation orbits. -/
theorem strictLevel_eq_lcm_cuspTranslationOrbitWidth [Γ.FiniteIndex] :
    Γ.strictLevel =
      (Finset.univ : Finset (CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)))).lcm
        cuspTranslationOrbitWidth :=
  Nat.dvd_right_iff_eq.mp fun m ↦ by
    simp [strictLevel_dvd_iff_forall_cuspTranslationOrbitWidth_dvd, Finset.lcm_dvd_iff]

end Subgroup

namespace CongruenceSubgroup

/-- `Γ(N)` has strict level `N`. -/
@[simp]
theorem strictLevel_Gamma (N : ℕ) : (Gamma N).strictLevel = N := by
  have := Gamma_normal N
  refine Nat.dvd_right_iff_eq.mp fun m ↦ ?_
  rw [Subgroup.strictLevel_dvd_iff_of_normal, ← zpow_natCast]
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using ModularGroup_T_pow_mem_Gamma N m (by exact_mod_cast h)⟩
  have h01 := (Gamma_mem.mp h).2.1
  rw [ModularGroup.coe_T_zpow] at h01
  simpa [ZMod.natCast_eq_zero_iff] using h01

/-- A subgroup containing `Γ(N)` has strict level dividing `N`. -/
theorem strictLevel_dvd_of_Gamma_le {Γ : Subgroup SL(2, ℤ)} {N : ℕ} (h : Gamma N ≤ Γ) :
    Γ.strictLevel ∣ N :=
  strictLevel_Gamma N ▸ Subgroup.strictLevel_dvd_of_le h

/-- `Γ₀(N)` has strict level `N`. -/
@[simp]
theorem strictLevel_Gamma0 (N : ℕ) : (Gamma0 N).strictLevel = N := by
  refine Nat.dvd_antisymm (strictLevel_dvd_of_Gamma_le (Gamma_le_Gamma0 N)) ?_
  -- conjugating by `S` turns `T ^ m` into the lower-triangular `[1, 0; -m, 1]`
  have h := (TauCeti.conj_T_zpow_mem_Gamma0_iff N ModularGroup.S (Gamma0 N).strictLevel).mp
    (by simpa using Subgroup.conj_T_pow_strictLevel_mem (Γ := Gamma0 N) ModularGroup.S)
  simpa [ModularGroup.coe_S, Int.natCast_dvd_natCast] using h

/-- `Γ₁(N)` has strict level `N`. -/
@[simp]
theorem strictLevel_Gamma1 (N : ℕ) : (Gamma1 N).strictLevel = N :=
  Nat.dvd_antisymm (strictLevel_dvd_of_Gamma_le (Gamma_le_Gamma1 N))
    (by simpa using Subgroup.strictLevel_dvd_of_le (Gamma1_in_Gamma0 N))

end CongruenceSubgroup
