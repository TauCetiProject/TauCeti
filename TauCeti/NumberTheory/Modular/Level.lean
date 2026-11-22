/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.GeometryType
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.NumberTheory.Modular.CosetTriple
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Wohlfahrt
public import Mathlib.NumberTheory.Chebyshev
import TauCeti.GroupTheory.Perm.Partition
import TauCeti.NumberTheory.LcmUpto

/-!
# The general level of a subgroup of the modular group

For a subgroup `Γ' ≤ PSL(2, ℤ)` with a numbering `e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n` of its cosets, the
**general level** `TauCeti.ModularGroup.generalLevel Γ' e` is the order of the permutation
`σinf = permT Γ' e` by which `T` acts on the cosets. It is the least common multiple of the cycle
lengths of `σinf`, fixed points included, that is of the cusp widths of `Γ'`.

The kernel of the coset action is the normal core of `Γ'`, so a power `σinf ^ m` is trivial
exactly when every conjugate `σ Tᵐ σ⁻¹`, `σ ∈ SL(2, ℤ)`, lies in the full preimage `±Γ'` of `Γ'`
(`Subgroup.liftSL`). Hence the general level is the strict level of `±Γ'`: the least `N > 0` such
that the normal closure of `Tᴺ` in `SL(2, ℤ)` is contained in `±Γ'`. It does not depend on the
numbering and is a conjugacy invariant. For `Γ ≤ SL(2, ℤ)` the strict level of `Γ` is the general
level of its image in `PSL(2, ℤ)` or twice it, with equality when `-1 ∈ Γ`. The image of `Γ(N)`
has general level `N`, although for `N ≥ 3` it does not contain `-1`.

The general level is the modulus of Wohlfahrt's theorem for the full preimage: `±Γ'` is a
congruence subgroup exactly when it contains `Γ(N)` for `N` the general level. This yields the
**order obstruction** to congruence: if `±Γ'` is a congruence subgroup and `N` is the general
level of `Γ'`, then the image of `Γ(N)` in `PSL(2, ℤ)` lies in the normal core of `Γ'`, so both
the index `n` of `Γ'` and the order of its monodromy group divide the index of that image. A
subgroup whose index does not divide that number is therefore not a congruence subgroup.

## Main declarations

* `TauCeti.ModularGroup.generalLevel`: the general level `orderOf σinf`.
* `TauCeti.ModularGroup.generalLevel_dvd_iff`,
  `TauCeti.ModularGroup.generalLevel_dvd_iff_normalClosure_le`: the multiples of the general level
  are the `m` with every conjugate of `Tᵐ` in `±Γ'`.
* `TauCeti.ModularGroup.generalLevel_eq_strictLevel_liftSL`: the general level is the strict level
  of `±Γ'`.
* `TauCeti.ModularGroup.generalLevel_eq_lcm_fullCycleType`: the general level is the least common
  multiple of the cycle lengths of `σinf`.
* `TauCeti.ModularGroup.generalLevel_congr`, `TauCeti.ModularGroup.generalLevel_conjAct_smul`:
  independence of the numbering and conjugation invariance.
* `TauCeti.ModularGroup.strictLevel_eq_generalLevel_or_eq_two_mul`: the strict level of
  `Γ ≤ SL(2, ℤ)` is the general level of its image or twice it.
* `TauCeti.ModularGroup.generalLevel_map_Gamma`: the image of `Γ(N)` has general level `N`.
* `TauCeti.ModularGroup.isCongruenceSubgroup_liftSL_iff`: Wohlfahrt's theorem for `±Γ'`.
* `TauCeti.ModularGroup.map_Gamma_generalLevel_le_normalCore`: for congruence `±Γ'`, the image of
  `Γ(N)` lies in the normal core of `Γ'`.
* `TauCeti.ModularGroup.dvd_index_map_Gamma_generalLevel`,
  `TauCeti.ModularGroup.natCard_monodromyGroup_dvd_index_map_Gamma_generalLevel`,
  `TauCeti.ModularGroup.not_isCongruenceSubgroup_liftSL_of_not_dvd`: the order obstruction.

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer, 2005, §1.2 (the index of `Γ(N)` and of `±Γ(N)`).
-/

open scoped MatrixGroups Pointwise

public section

namespace TauCeti.ModularGroup

open _root_.ModularGroup _root_.CongruenceSubgroup _root_.Matrix.SpecialLinearGroup Equiv

variable {n : ℕ} (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)

/-- The **general level** of `Γ' ≤ PSL(2, ℤ)`: the order of the permutation `σinf = permT Γ' e` by
which `T` acts on the cosets of `Γ'` numbered by `e`. It does not depend on `e`
(`generalLevel_congr`); it is the strict level of the full preimage `Γ'.liftSL`
(`generalLevel_eq_strictLevel_liftSL`) and the least common multiple of the cusp widths
(`generalLevel_eq_lcm_fullCycleType`). -/
noncomputable def generalLevel : ℕ :=
  orderOf (permT Γ' e)

/-- The general level is the order of `σinf`. -/
theorem generalLevel_def : generalLevel Γ' e = orderOf (permT Γ' e) := (rfl)

/-- `σinf ^ m` is the identity exactly when every conjugate `σ * T ^ m * σ⁻¹`, `σ ∈ SL(2, ℤ)`,
lies in the full preimage `Γ'.liftSL`: the kernel of the coset action is the normal core of
`Γ'`. -/
theorem permT_pow_eq_one_iff {m : ℕ} :
    permT Γ' e ^ m = 1 ↔ ∀ σ : SL(2, ℤ), σ * T ^ m * σ⁻¹ ∈ Γ'.liftSL := by
  rw [permT, modularTriple_σinf, ← map_pow, ← MonoidHom.mem_ker,
    Equiv.ker_permutationRepresentation, ← Subgroup.normalCore_eq_ker]
  -- membership in the normal core is, by definition, membership of every conjugate
  refine QuotientGroup.mk_surjective.forall.trans (forall_congr' fun σ ↦ ?_)
  simp only [Subgroup.mem_liftSL, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_inv]

/-- The natural numbers `m` with `σ * T ^ m * σ⁻¹ ∈ Γ'.liftSL` for every `σ ∈ SL(2, ℤ)` are the
multiples of the general level. -/
theorem generalLevel_dvd_iff {m : ℕ} :
    generalLevel Γ' e ∣ m ↔ ∀ σ : SL(2, ℤ), σ * T ^ m * σ⁻¹ ∈ Γ'.liftSL := by
  rw [generalLevel, orderOf_dvd_iff_pow_eq_one, permT_pow_eq_one_iff]

/-- **The general level is the strict level of the full preimage** `±Γ' = Γ'.liftSL`. -/
theorem generalLevel_eq_strictLevel_liftSL : generalLevel Γ' e = Γ'.liftSL.strictLevel :=
  Nat.dvd_right_iff_eq.mp fun _ ↦ by
    rw [generalLevel_dvd_iff, Subgroup.strictLevel_dvd_iff]

/-- The general level does not depend on the numbering of the cosets. -/
theorem generalLevel_congr {n' : ℕ} (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n') :
    generalLevel Γ' e = generalLevel Γ' e' := by
  rw [generalLevel_eq_strictLevel_liftSL, generalLevel_eq_strictLevel_liftSL]

/-- The general level is positive. -/
theorem generalLevel_pos : 0 < generalLevel Γ' e :=
  orderOf_pos _

/-- The general level is nonzero. -/
instance instNeZeroGeneralLevel : NeZero (generalLevel Γ' e) :=
  ⟨(generalLevel_pos Γ' e).ne'⟩

/-- Every conjugate of `T ^ generalLevel Γ' e` lies in the full preimage of `Γ'`. -/
theorem conj_T_pow_generalLevel_mem_liftSL (σ : SL(2, ℤ)) :
    σ * T ^ generalLevel Γ' e * σ⁻¹ ∈ Γ'.liftSL :=
  (generalLevel_dvd_iff Γ' e).mp dvd_rfl σ

/-- `T ^ generalLevel Γ' e` lies in the full preimage of `Γ'`. -/
theorem T_pow_generalLevel_mem_liftSL : T ^ generalLevel Γ' e ∈ Γ'.liftSL := by
  simpa using conj_T_pow_generalLevel_mem_liftSL Γ' e 1

/-- The general level is at most any positive `N` all of whose conjugates `σ * T ^ N * σ⁻¹` lie
in the full preimage of `Γ'`. -/
theorem generalLevel_le {N : ℕ} (hN : 0 < N)
    (h : ∀ σ : SL(2, ℤ), σ * T ^ N * σ⁻¹ ∈ Γ'.liftSL) : generalLevel Γ' e ≤ N :=
  Nat.le_of_dvd hN ((generalLevel_dvd_iff Γ' e).mpr h)

/-- The normal closure of `T ^ m` in `SL(2, ℤ)` lies in the full preimage of `Γ'` exactly when
`m` is a multiple of the general level. -/
theorem generalLevel_dvd_iff_normalClosure_le {m : ℕ} :
    generalLevel Γ' e ∣ m ↔ Subgroup.normalClosure {T ^ m} ≤ Γ'.liftSL := by
  rw [← Subgroup.normal_le_normalCore, generalLevel_eq_strictLevel_liftSL,
    Subgroup.strictLevel_dvd_iff_T_pow_mem_normalCore]
  exact Set.singleton_subset_iff.symm.trans Subgroup.normalClosure_subset_iff

/-- **The general level is the least positive `N` such that the normal closure of `T ^ N` in
`SL(2, ℤ)` lies in the full preimage of `Γ'`.** -/
theorem generalLevel_eq_sInf :
    generalLevel Γ' e = sInf {N : ℕ | 0 < N ∧ Subgroup.normalClosure {T ^ N} ≤ Γ'.liftSL} := by
  simp only [← generalLevel_dvd_iff_normalClosure_le Γ' e]
  refine le_antisymm (le_csInf ⟨_, generalLevel_pos Γ' e, dvd_rfl⟩ fun N hN ↦ ?_)
    (Nat.sInf_le ⟨generalLevel_pos Γ' e, dvd_rfl⟩)
  exact Nat.le_of_dvd hN.1 hN.2

/-- **The general level is the least common multiple of the cusp widths**, the cycle lengths of
`σinf` with its fixed points included. -/
theorem generalLevel_eq_lcm_fullCycleType :
    generalLevel Γ' e = (permT Γ' e).fullCycleType.lcm := by
  rw [Perm.fullCycleType_def, Perm.lcm_parts_partition, generalLevel]

/-- The general level divides `lcm(1, …, n)`, every cusp width being at most the index `n`. It need
not be at most `n`. -/
theorem generalLevel_dvd_lcmUpto : generalLevel Γ' e ∣ Nat.lcmUpto n := by
  rw [generalLevel_eq_lcm_fullCycleType, Multiset.lcm_dvd]
  exact fun w hw ↦ Nat.dvd_lcmUpto (Perm.pos_of_mem_fullCycleType hw)
    (by simpa [Perm.sum_fullCycleType] using Multiset.le_sum_of_mem hw)

/-- The general level is the order of `σ1 * σ0 = σinf⁻¹`. -/
theorem orderOf_σ1_mul_σ0 :
    orderOf ((modularTriple Γ' e).σ1 * (modularTriple Γ' e).σ0) = generalLevel Γ' e := by
  rw [PermutationTriple.σ1_mul_σ0_eq_σinf_inv, orderOf_inv, generalLevel, permT]

/-! ### Invariance -/

section Invariance

variable {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)} {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}

/-- Isomorphic modular triples have the same general level. -/
theorem generalLevel_eq_of_equivalent
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    generalLevel Γ₁ e₁ = generalLevel Γ₂ e₂ := by
  rw [generalLevel, generalLevel, permT, permT, ← PermutationTriple.orderTriple_σinf,
    ← PermutationTriple.orderTriple_σinf, PermutationTriple.orderTriple_eq_of_equivalent h]

variable (g : ConjAct PSL(2, ℤ)) (e' : PSL(2, ℤ) ⧸ g • Γ' ≃ Fin n)

/-- Conjugate subgroups have the same general level, for any coset numberings. -/
theorem generalLevel_conjAct_smul : generalLevel (g • Γ') e' = generalLevel Γ' e :=
  generalLevel_eq_of_equivalent ((millington e' e).mpr ⟨g⁻¹, inv_smul_smul g Γ'⟩)

end Invariance

/-! ### Comparison with the strict level and examples -/

section Comparison

variable (Γ : Subgroup SL(2, ℤ))
  (e : PSL(2, ℤ) ⧸ Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) ≃ Fin n)

/-- The general level of the image of `Γ ≤ SL(2, ℤ)` in `PSL(2, ℤ)` is the strict level of
`Γ·{±1}`. -/
theorem generalLevel_map_eq_strictLevel_withCenter :
    generalLevel _ e = Γ.withCenter.strictLevel := by
  rw [generalLevel_eq_strictLevel_liftSL, Subgroup.liftSL_map]

/-- The general level of the image of `Γ ≤ SL(2, ℤ)` in `PSL(2, ℤ)` divides the strict level of
`Γ`. -/
theorem generalLevel_map_dvd_strictLevel : generalLevel _ e ∣ Γ.strictLevel := by
  rw [generalLevel_map_eq_strictLevel_withCenter]
  exact Γ.strictLevel_withCenter_dvd

/-- **The strict level of `Γ ≤ SL(2, ℤ)` is the general level of its image in `PSL(2, ℤ)`, or
twice it.** -/
theorem strictLevel_eq_generalLevel_or_eq_two_mul :
    Γ.strictLevel = generalLevel _ e ∨ Γ.strictLevel = 2 * generalLevel _ e := by
  rw [generalLevel_map_eq_strictLevel_withCenter]
  exact Γ.strictLevel_eq_or_eq_two_mul_strictLevel_withCenter

/-- For `Γ ≤ SL(2, ℤ)` containing `-1`, the strict level of `Γ` is the general level of its image
in `PSL(2, ℤ)`. -/
theorem strictLevel_eq_generalLevel_of_neg_one_mem (h : (-1 : SL(2, ℤ)) ∈ Γ) :
    Γ.strictLevel = generalLevel _ e := by
  rw [generalLevel_eq_strictLevel_liftSL, liftSL_map_of_neg_one_mem h]

/-- The image of `Γ(N)` in `PSL(2, ℤ)` has general level `N`. For `N ≥ 3` the group
`Γ(N)` does not contain `-1`, but neither `Tᵐ` nor `-Tᵐ` lies in `Γ(N)` unless `N ∣ m`. -/
@[simp]
theorem generalLevel_map_Gamma {N : ℕ}
    (e : PSL(2, ℤ) ⧸ (Gamma N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) ≃ Fin n) :
    generalLevel _ e = N := by
  rw [generalLevel_map_eq_strictLevel_withCenter]
  refine Nat.dvd_antisymm ?_ ?_
  · simpa only [strictLevel_Gamma] using (Gamma N).strictLevel_withCenter_dvd
  · simpa only [strictLevel_Gamma0] using
      Subgroup.strictLevel_dvd_of_le (withCenter_le_Gamma0 (Gamma_le_Gamma0 N))

end Comparison

/-- The full modular group has general level `1`. -/
@[simp]
theorem generalLevel_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin n) :
    generalLevel ⊤ e = 1 := by
  rw [generalLevel_eq_strictLevel_liftSL, Subgroup.liftSL_top, Subgroup.strictLevel_top]

/-- The image of `Γ₀(N)` in `PSL(2, ℤ)` has general level `N`. -/
@[simp]
theorem generalLevel_Gamma0Projective (N : ℕ)
    (e : PSL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0Projective N ≃ Fin n) :
    generalLevel _ e = N := by
  rw [generalLevel_eq_strictLevel_liftSL, CongruenceSubgroup.liftSL_Gamma0Projective,
    strictLevel_Gamma0]

/-! ### Wohlfahrt's theorem and the order obstruction -/

/-- **Wohlfahrt's theorem for the full preimage**: `±Γ'` is a congruence subgroup exactly when it
contains `Γ(N)` for `N` the general level of `Γ'`. -/
theorem isCongruenceSubgroup_liftSL_iff :
    IsCongruenceSubgroup Γ'.liftSL ↔ Gamma (generalLevel Γ' e) ≤ Γ'.liftSL := by
  have : NeZero Γ'.liftSL.strictLevel := by
    rw [← generalLevel_eq_strictLevel_liftSL Γ' e]
    infer_instance
  rw [generalLevel_eq_strictLevel_liftSL]
  exact isCongruenceSubgroup_iff_Gamma_strictLevel_le _

/-- If `±Γ'` is a congruence subgroup, the image of `Γ(N)` in `PSL(2, ℤ)`, for `N` the general
level, lies in the normal core of `Γ'`. -/
theorem map_Gamma_generalLevel_le_normalCore
    (h : IsCongruenceSubgroup Γ'.liftSL) :
    (Gamma (generalLevel Γ' e)).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) ≤
      Γ'.normalCore := by
  have : ((Gamma (generalLevel Γ' e)).map
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).Normal :=
    (Gamma_normal _).map _ (QuotientGroup.mk'_surjective _)
  rw [Subgroup.normal_le_normalCore]
  exact (Subgroup.map_mono ((isCongruenceSubgroup_liftSL_iff Γ' e).mp h)).trans_eq
    (Subgroup.map_liftSL Γ')

/-- **The order obstruction**: if `±Γ'` is a congruence subgroup, the index `n` of `Γ'` divides
the index in `PSL(2, ℤ)` of the image of `Γ(N)`, for `N` the general level of `Γ'`. -/
theorem dvd_index_map_Gamma_generalLevel (h : IsCongruenceSubgroup Γ'.liftSL) :
    n ∣ ((Gamma (generalLevel Γ' e)).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index := by
  have := Subgroup.index_dvd_of_le
    ((map_Gamma_generalLevel_le_normalCore Γ' e h).trans Γ'.normalCore_le)
  rwa [Subgroup.index_eq_card, Nat.card_eq_of_equiv_fin e] at this

/-- **The order obstruction, group-theoretic form**: if `±Γ'` is a congruence subgroup, the order
of the monodromy group of `Γ'` divides the index in `PSL(2, ℤ)` of the image of `Γ(N)`, for `N` the
general level of `Γ'`. -/
theorem natCard_monodromyGroup_dvd_index_map_Gamma_generalLevel
    (h : IsCongruenceSubgroup Γ'.liftSL) :
    Nat.card (modularTriple Γ' e).monodromyGroup ∣
      ((Gamma (generalLevel Γ' e)).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index := by
  rw [natCard_monodromyGroup_modularTriple]
  exact Subgroup.index_dvd_of_le (map_Gamma_generalLevel_le_normalCore Γ' e h)

/-- **Noncongruence from the order obstruction**: if the index `n` of `Γ'` does not divide the
index in `PSL(2, ℤ)` of the image of `Γ(N)`, for `N` the general level of `Γ'`, then `±Γ'` is not
a congruence subgroup. -/
theorem not_isCongruenceSubgroup_liftSL_of_not_dvd
    (h : ¬ n ∣ ((Gamma (generalLevel Γ' e)).map
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index) :
    ¬ IsCongruenceSubgroup Γ'.liftSL :=
  mt (dvd_index_map_Gamma_generalLevel Γ' e) h

end TauCeti.ModularGroup
