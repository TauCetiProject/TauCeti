/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Nat.Totient
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# Quotients and indices of the congruence subgroups `Γ₁(N)` and `Γ(N)`

At a fixed level `N`, the standard congruence subgroups sit in the normal tower
`Γ(N) ⊴ Γ₁(N) ⊴ Γ₀(N) ≤ SL(2, ℤ)`. `TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic`
computes `[SL₂(ℤ) : Γ₀(N)] = N ∏_{p ∣ N} (1 + 1/p)`. This file identifies the successive quotient
groups of the tower at every level `N : ℕ` (including `N = 0`), deduces the relative and full
indices of `Γ₁(N)` and `Γ(N)`, determines the order of `SL(2, ℤ/Nℤ)`, and records the projective
indices `[SL₂(ℤ) : ±Γ₁(N)]` and `[SL₂(ℤ) : ±Γ(N)]`.

Specifically:
* The unit-valued lower-right entry `(Gamma0Map N).toHomUnits` induces a group isomorphism
  `Γ₀(N) ⧸ Γ₁(N) ≃* (ZMod N)ˣ` (`quotientGamma1EquivUnits`), giving
  `[Γ₀(N) : Γ₁(N)] = |(ZMod N)ˣ|` for all `N` and `φ(N)` for `N ≠ 0`.
* Reading the upper-right entry modulo `N` defines a surjective homomorphism
  `gamma1UpperRightHom N : Γ₁(N) →* Multiplicative (ZMod N)` with kernel `Γ(N)` and sections given
  by powers of `T`, inducing `Γ₁(N) ⧸ Γ(N) ≃* Multiplicative (ZMod N)` (`quotientGammaEquivZMod`)
  and `[Γ₁(N) : Γ(N)] = N` for all `N`.
* Strong approximation (`Matrix.SpecialLinearGroup.map_intCast_zmod_surjective`) identifies
  `SL(2, ℤ) ⧸ Γ(N) ≃* SL(2, ZMod N)` (`quotientGammaEquiv`), equating `|SL(2, ZMod N)|` with
  `[SL₂(ℤ) : Γ(N)]`.
* Combining these with the formula for `[SL₂(ℤ) : Γ₀(N)]` yields multiplicativity in coprime
  levels, prime and prime-power formulas, factorization formulas, and cleared-denominator formulas
  `[SL₂(ℤ) : Γ₁(N)] · ∏_{p ∣ N} p² = N² · ∏_{p ∣ N} (p² - 1)` and
  `[SL₂(ℤ) : Γ(N)] · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)`.
* Since `-I` belongs to `Γ₁(N)` and to `Γ(N)` precisely when `N ∣ 2`, adjoining the centre `{±I}`
  leaves the index unchanged for `N ∣ 2` and halves it whenever `¬ N ∣ 2` (in particular for all
  `N ≥ 3`).

## Main definitions

* `CongruenceSubgroup.quotientGamma1EquivUnits`: the canonical group isomorphism
  `Γ₀(N) ⧸ Γ₁(N) ≃* (ZMod N)ˣ`.
* `CongruenceSubgroup.gamma1UpperRightHom`: the upper-right entry homomorphism
  `Γ₁(N) →* Multiplicative (ZMod N)`.
* `CongruenceSubgroup.quotientGammaEquivZMod`: the canonical group isomorphism
  `Γ₁(N) ⧸ Γ(N) ≃* Multiplicative (ZMod N)`.
* `CongruenceSubgroup.quotientGammaEquiv`: the canonical group isomorphism
  `SL(2, ℤ) ⧸ Γ(N) ≃* SL(2, ZMod N)`.

## Main results

* `CongruenceSubgroup.Gamma1_relIndex_Gamma0`,
  `CongruenceSubgroup.Gamma1_relIndex_Gamma0_eq_totient`,
  `CongruenceSubgroup.Gamma_relIndex_Gamma1`, `CongruenceSubgroup.Gamma_relIndex_Gamma0`:
  the relative indices in `Γ(N) ≤ Γ₁(N) ≤ Γ₀(N)`.
* `CongruenceSubgroup.Gamma1_index_eq_Gamma0_index_mul_totient`,
  `CongruenceSubgroup.Gamma_index_eq_Gamma1_index_mul`,
  `CongruenceSubgroup.Gamma_index_eq_Gamma0_index_mul_totient_mul`: tower relations for the full
  indices at every level `N : ℕ`.
* `CongruenceSubgroup.Gamma1_prime_index`, `CongruenceSubgroup.Gamma1_prime_power_index`,
  `CongruenceSubgroup.Gamma1_index_eq_prod_factorization`,
  `CongruenceSubgroup.Gamma1_index_mul_prod_primeFactors`: closed-form formulas for
  `[SL₂(ℤ) : Γ₁(N)]`.
* `CongruenceSubgroup.Gamma_prime_index`, `CongruenceSubgroup.Gamma_prime_power_index`,
  `CongruenceSubgroup.Gamma_index_eq_prod_factorization`,
  `CongruenceSubgroup.Gamma_index_mul_prod_primeFactors`, and
  `Matrix.SpecialLinearGroup.natCard_fin_two_zmod_mul_prod_primeFactors`: closed-form formulas for
  `[SL₂(ℤ) : Γ(N)] = |SL(2, ZMod N)|`.
* `CongruenceSubgroup.neg_one_mem_Gamma_iff`,
  `CongruenceSubgroup.two_mul_Gamma1_withCenter_index_of_not_dvd_two`,
  `CongruenceSubgroup.two_mul_Gamma_withCenter_index_of_not_dvd_two`: centre membership and the
  factor of `2` relating `[SL₂(ℤ) : Γ]` to `[SL₂(ℤ) : ±Γ]`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971], §1.6.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §1.2 and Exercise 1.2.3.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CongruenceSubgroup

/-! ### Level zero and level one -/

/-- At level one every matrix of `SL(2, ℤ)` lies in `Γ₁(1)`. -/
@[simp]
theorem Gamma1_one_top : Gamma1 1 = ⊤ :=
  top_unique (Gamma_one_top ▸ Gamma_le_Gamma1 1)

/-- `Γ₀(1)` has index `1` in `SL(2, ℤ)`. -/
theorem Gamma0_one_index : (Gamma0 1).index = 1 := by
  simp [Gamma0_one_top]

/-- `Γ₁(1)` has index `1` in `SL(2, ℤ)`. -/
theorem Gamma1_one_index : (Gamma1 1).index = 1 := by
  simp [Gamma1_one_top]

/-- `Γ(1)` has index `1` in `SL(2, ℤ)`. -/
@[simp]
theorem Gamma_one_index : (Gamma 1).index = 1 := by
  simp [Gamma_one_top]

/-- The unipotent subgroup `Γ₁(0)` has infinite index in `SL(2, ℤ)`, represented by `0` in `ℕ`. -/
@[simp]
theorem Gamma1_zero_index : (Gamma1 0).index = 0 := by
  rw [← Subgroup.relIndex_mul_index (Gamma1_in_Gamma0 0), Gamma0_zero_index, mul_zero]

/-- The trivial subgroup `Γ(0)` has infinite index in `SL(2, ℤ)`, represented by `0` in `ℕ`. -/
@[simp]
theorem Gamma_zero_index : (Gamma 0).index = 0 := by
  rw [← Subgroup.relIndex_mul_index (Gamma_le_Gamma0 0), Gamma0_zero_index, mul_zero]

/-! ### The quotient `Γ₀(N) ⧸ Γ₁(N) ≃* (ZMod N)ˣ` -/

/-- Inside `Γ₀(N)`, the subgroup `Γ₁(N)` is the kernel of `(Gamma0Map N).toHomUnits`. -/
theorem Gamma1_subgroupOf_Gamma0_eq_ker (N : ℕ) :
    (Gamma1 N).subgroupOf (Gamma0 N) = (Gamma0Map N).toHomUnits.ker := by
  ext g
  exact mem_Gamma1_iff_toHomUnits_eq_one g

/-- The pullback `(Gamma1 N).subgroupOf (Gamma0 N)` agrees with Mathlib's `Gamma1' N`. -/
theorem Gamma1_subgroupOf_Gamma0_eq_Gamma1' (N : ℕ) :
    (Gamma1 N).subgroupOf (Gamma0 N) = Gamma1' N := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_Gamma1_iff, Gamma1_mem', Gamma0Map_apply]
  exact and_iff_right g.2

/-- `Γ₁(N)` is normal in `Γ₀(N)`, as the kernel of `(Gamma0Map N).toHomUnits`. -/
instance instNormalGamma1SubgroupOfGamma0 (N : ℕ) :
    ((Gamma1 N).subgroupOf (Gamma0 N)).Normal :=
  Gamma1_subgroupOf_Gamma0_eq_ker N ▸ (Gamma0Map N).toHomUnits.normal_ker

/-- **The diamond quotient isomorphism** `Γ₀(N) ⧸ Γ₁(N) ≃* (ZMod N)ˣ`, induced by reading off the
unit-valued lower-right entry modulo `N`. Valid at every level `N : ℕ`, `N = 0` included. -/
noncomputable def quotientGamma1EquivUnits (N : ℕ) :
    ↥(Gamma0 N) ⧸ (Gamma1 N).subgroupOf (Gamma0 N) ≃* (ZMod N)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (Gamma1_subgroupOf_Gamma0_eq_ker N)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (Gamma0Map N).toHomUnits
      Gamma0Map_toHomUnits_surjective)

/-- On a coset representative `g ∈ Γ₀(N)`, `quotientGamma1EquivUnits` evaluates to the unit-valued
lower-right entry `(Gamma0Map N).toHomUnits g`. -/
@[simp]
theorem quotientGamma1EquivUnits_mk (N : ℕ) (g : ↥(Gamma0 N)) :
    quotientGamma1EquivUnits N (g : ↥(Gamma0 N) ⧸ (Gamma1 N).subgroupOf (Gamma0 N)) =
      (Gamma0Map N).toHomUnits g :=
  (rfl)

/-- The inverse of `quotientGamma1EquivUnits` sends `u : (ZMod N)ˣ` to the coset of any `g ∈ Γ₀(N)`
with lower-right entry `u`. -/
theorem quotientGamma1EquivUnits_symm_apply_eq_mk {N : ℕ} {u : (ZMod N)ˣ} (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = u) :
    (quotientGamma1EquivUnits N).symm u =
      (g : ↥(Gamma0 N) ⧸ (Gamma1 N).subgroupOf (Gamma0 N)) :=
  (quotientGamma1EquivUnits N).injective (by simp [hg])

/-- **`[Γ₀(N) : Γ₁(N)] = |(ZMod N)ˣ|`** at every level `N : ℕ` (at `N = 0` both sides equal `2`,
corresponding to `{±I}`). -/
theorem Gamma1_relIndex_Gamma0 (N : ℕ) :
    (Gamma1 N).relIndex (Gamma0 N) = Nat.card (ZMod N)ˣ :=
  Nat.card_congr (quotientGamma1EquivUnits N).toEquiv

/-- For nonzero level `N`, the relative index `[Γ₀(N) : Γ₁(N)]` is Euler's totient `φ(N)`
(at `N = 0` the relative index is `|(ℤ)ˣ| = 2`, whereas `Nat.totient 0 = 0`). -/
theorem Gamma1_relIndex_Gamma0_eq_totient {N : ℕ} (hN : N ≠ 0) :
    (Gamma1 N).relIndex (Gamma0 N) = N.totient := by
  have : NeZero N := ⟨hN⟩
  rw [Gamma1_relIndex_Gamma0, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- **`[SL₂(ℤ) : Γ₁(N)] = [SL₂(ℤ) : Γ₀(N)] · φ(N)`** at every level `N : ℕ`.
At `N = 0` both sides vanish because `Γ₀(0)` and `Γ₁(0)` have infinite index. -/
theorem Gamma1_index_eq_Gamma0_index_mul_totient (N : ℕ) :
    (Gamma1 N).index = (Gamma0 N).index * N.totient := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · rw [← Subgroup.relIndex_mul_index (Gamma1_in_Gamma0 N),
      Gamma1_relIndex_Gamma0_eq_totient hN, mul_comm]

/-! ### The quotient `Γ₁(N) ⧸ Γ(N) ≃* Multiplicative (ZMod N)` -/

/-- The principal congruence subgroup `Γ(N)` is normal in `SL(2, ℤ)` (`Gamma_normal` as an
instance). -/
instance instNormalGamma (N : ℕ) : (Gamma N).Normal :=
  Gamma_normal N

/-- **The upper-right entry homomorphism** `Γ₁(N) →* Multiplicative (ZMod N)`. Because matrices in
`Γ₁(N)` have diagonal congruent to `(1, 1)` and lower-left entry congruent to `0` modulo `N`,
matrix multiplication adds their upper-right entries modulo `N`. -/
def gamma1UpperRightHom (N : ℕ) : ↥(Gamma1 N) →* Multiplicative (ZMod N) where
  toFun g := Multiplicative.ofAdd (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod N)
  map_one' := by simp
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    obtain ⟨hA00, _, _⟩ := (Gamma1_mem N A).mp hA
    obtain ⟨_, hB11, _⟩ := (Gamma1_mem N B).mp hB
    rw [← ofAdd_add]
    congr 1
    simp only [Subgroup.coe_mul, coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
      Int.cast_mul, hA00, hB11, one_mul, mul_one]
    exact add_comm _ _

/-- Evaluation of `gamma1UpperRightHom` at `g ∈ Γ₁(N)`. -/
@[simp]
theorem gamma1UpperRightHom_apply (N : ℕ) (g : ↥(Gamma1 N)) :
    gamma1UpperRightHom N g = Multiplicative.ofAdd (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) :=
  (rfl)

/-- Additive reading of `gamma1UpperRightHom`: the upper-right entry modulo `N`. -/
theorem toAdd_gamma1UpperRightHom (N : ℕ) (g : ↥(Gamma1 N)) :
    (gamma1UpperRightHom N g).toAdd = (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) :=
  (rfl)

/-- Inside `Γ₁(N)`, the principal congruence subgroup `Γ(N)` is the kernel of
`gamma1UpperRightHom N`. -/
theorem Gamma_subgroupOf_Gamma1_eq_ker (N : ℕ) :
    (Gamma N).subgroupOf (Gamma1 N) = (gamma1UpperRightHom N).ker := by
  ext ⟨g, hg⟩
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem N g).mp hg
  simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, gamma1UpperRightHom_apply, Gamma_mem,
    h00, h11, h10]

/-- `gamma1UpperRightHom N` is surjective at every level `N : ℕ`: `Tⁿ ∈ Γ₁(N)` realises the class
of `n` modulo `N`. -/
theorem gamma1UpperRightHom_surjective (N : ℕ) :
    Function.Surjective (gamma1UpperRightHom N) := by
  intro x
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (n := N) x.toAdd
  refine ⟨⟨ModularGroup.T ^ n, T_zpow_mem_Gamma1 N n⟩, ?_⟩
  simp [gamma1UpperRightHom_apply, ModularGroup.coe_T_zpow, hn]

/-- **The unipotent quotient isomorphism** `Γ₁(N) ⧸ Γ(N) ≃* Multiplicative (ZMod N)`, induced by
the upper-right entry modulo `N`. Valid at every level `N : ℕ`, `N = 0` included. -/
noncomputable def quotientGammaEquivZMod (N : ℕ) :
    ↥(Gamma1 N) ⧸ (Gamma N).subgroupOf (Gamma1 N) ≃* Multiplicative (ZMod N) :=
  (QuotientGroup.quotientMulEquivOfEq (Gamma_subgroupOf_Gamma1_eq_ker N)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (gamma1UpperRightHom N)
      (gamma1UpperRightHom_surjective N))

/-- On a coset representative `g ∈ Γ₁(N)`, `quotientGammaEquivZMod` evaluates to
`gamma1UpperRightHom N g`. -/
@[simp]
theorem quotientGammaEquivZMod_mk (N : ℕ) (g : ↥(Gamma1 N)) :
    quotientGammaEquivZMod N (g : ↥(Gamma1 N) ⧸ (Gamma N).subgroupOf (Gamma1 N)) =
      gamma1UpperRightHom N g :=
  (rfl)

/-- Powers of `T` form an explicit section of `quotientGammaEquivZMod`: the residue class of `n`
modulo `N` lifts to the coset of `Tⁿ ∈ Γ₁(N)`. -/
@[simp]
theorem quotientGammaEquivZMod_symm_ofAdd_intCast (N : ℕ) (n : ℤ) :
    (quotientGammaEquivZMod N).symm (Multiplicative.ofAdd (n : ZMod N)) =
      ((⟨ModularGroup.T ^ n, T_zpow_mem_Gamma1 N n⟩ : ↥(Gamma1 N)) :
        ↥(Gamma1 N) ⧸ (Gamma N).subgroupOf (Gamma1 N)) :=
  (quotientGammaEquivZMod N).injective (by simp [ModularGroup.coe_T_zpow])

/-- **`[Γ₁(N) : Γ(N)] = N`** at every level `N : ℕ` (at `N = 0`, `Γ(0) = ⊥` has infinite index in
`Γ₁(0) = {Tⁿ}`, and both sides vanish). -/
@[simp]
theorem Gamma_relIndex_Gamma1 (N : ℕ) : (Gamma N).relIndex (Gamma1 N) = N :=
  (Nat.card_congr ((quotientGammaEquivZMod N).toEquiv.trans Multiplicative.toAdd)).trans
    (Nat.card_zmod N)

/-- **`[Γ₀(N) : Γ(N)] = |(ZMod N)ˣ| · N`** at every level `N : ℕ`. -/
theorem Gamma_relIndex_Gamma0_eq_card_units_mul (N : ℕ) :
    (Gamma N).relIndex (Gamma0 N) = Nat.card (ZMod N)ˣ * N := by
  rw [← Subgroup.relIndex_mul_relIndex (Gamma N) (Gamma1 N) (Gamma0 N)
    (Gamma_le_Gamma1 N) (Gamma1_in_Gamma0 N),
    Gamma_relIndex_Gamma1, Gamma1_relIndex_Gamma0, mul_comm]

/-- **`[Γ₀(N) : Γ(N)] = φ(N) · N`** at every level `N : ℕ` (at `N = 0` both sides vanish). -/
theorem Gamma_relIndex_Gamma0 (N : ℕ) :
    (Gamma N).relIndex (Gamma0 N) = N.totient * N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [Gamma_relIndex_Gamma0_eq_card_units_mul]
  · rw [Gamma_relIndex_Gamma0_eq_card_units_mul, ← Gamma1_relIndex_Gamma0,
      Gamma1_relIndex_Gamma0_eq_totient hN]

/-- **`[SL₂(ℤ) : Γ(N)] = [SL₂(ℤ) : Γ₁(N)] · N`** at every level `N : ℕ`. -/
theorem Gamma_index_eq_Gamma1_index_mul (N : ℕ) :
    (Gamma N).index = (Gamma1 N).index * N := by
  rw [← Subgroup.relIndex_mul_index (Gamma_le_Gamma1 N), Gamma_relIndex_Gamma1, mul_comm]

/-- **`[SL₂(ℤ) : Γ(N)] = [SL₂(ℤ) : Γ₀(N)] · φ(N) · N`** at every level `N : ℕ`. -/
theorem Gamma_index_eq_Gamma0_index_mul_totient_mul (N : ℕ) :
    (Gamma N).index = (Gamma0 N).index * N.totient * N := by
  rw [Gamma_index_eq_Gamma1_index_mul, Gamma1_index_eq_Gamma0_index_mul_totient]

/-! ### The quotient `SL(2, ℤ) ⧸ Γ(N) ≃* SL(2, ZMod N)` -/

/-- **Strong approximation as a quotient isomorphism**: reduction modulo `N` identifies
`SL(2, ℤ) ⧸ Γ(N)` with `SL(2, ZMod N)` at every level `N : ℕ`. -/
noncomputable def quotientGammaEquiv (N : ℕ) : SL(2, ℤ) ⧸ Gamma N ≃* SL(2, ZMod N) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)))
    map_intCast_zmod_surjective

/-- On a coset representative `γ ∈ SL(2, ℤ)`, `quotientGammaEquiv` reduces `γ` modulo `N`. -/
@[simp]
theorem quotientGammaEquiv_mk (N : ℕ) (γ : SL(2, ℤ)) :
    quotientGammaEquiv N (γ : SL(2, ℤ) ⧸ Gamma N) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :=
  (rfl)

/-- The inverse of `quotientGammaEquiv` sends `A : SL(2, ZMod N)` to the coset of any integral lift
`γ ∈ SL(2, ℤ)` of `A`. -/
theorem quotientGammaEquiv_symm_apply_eq_mk {N : ℕ} {A : SL(2, ZMod N)} (γ : SL(2, ℤ))
    (hγ : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ = A) :
    (quotientGammaEquiv N).symm A = (γ : SL(2, ℤ) ⧸ Gamma N) :=
  (quotientGammaEquiv N).injective (by simp [hγ])

/-- `[SL₂(ℤ) : Γ(N)] = |SL(2, ZMod N)|` at every level `N : ℕ`. -/
theorem Gamma_index_eq_natCard_SL (N : ℕ) :
    (Gamma N).index = Nat.card SL(2, ZMod N) :=
  Nat.card_congr (quotientGammaEquiv N).toEquiv

/-! ### Multiplicativity, prime powers, and Dedekind-type product formulas -/

/-- **`Γ₁(a b) = Γ₁(a) ⊓ Γ₁(b)` for coprime `a` and `b`**: `Gamma1_lcm_eq_inf` at coprime
levels. -/
theorem Gamma1_mul_eq_inf_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    Gamma1 (a * b) = Gamma1 a ⊓ Gamma1 b := by
  rw [← hab.lcm_eq_mul, Gamma1_lcm_eq_inf]

/-- **The index of `Γ₁` is multiplicative in the level.** For coprime `a` and `b`,
`[SL₂(ℤ) : Γ₁(a b)] = [SL₂(ℤ) : Γ₁(a)] · [SL₂(ℤ) : Γ₁(b)]`. -/
theorem Gamma1_index_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    (Gamma1 (a * b)).index = (Gamma1 a).index * (Gamma1 b).index := by
  rw [Gamma1_index_eq_Gamma0_index_mul_totient, Gamma1_index_eq_Gamma0_index_mul_totient,
    Gamma1_index_eq_Gamma0_index_mul_totient, Gamma0_index_mul_of_coprime hab,
    Nat.totient_mul hab, mul_mul_mul_comm]

/-- For coprime levels `a` and `b`, `Γ₁(a)` has the same relative index in `Γ₁(b)` as in
`SL₂(ℤ)`. -/
theorem Gamma1_relIndex_Gamma1_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    (Gamma1 a).relIndex (Gamma1 b) = (Gamma1 a).index := by
  rcases eq_or_ne b 0 with rfl | hb
  · obtain rfl := Nat.coprime_zero_right a |>.mp hab
    simp
  · have : NeZero b := ⟨hb⟩
    have hmul : (Gamma1 a).relIndex (Gamma1 b) * (Gamma1 b).index =
        (Gamma1 a).index * (Gamma1 b).index := by
      rw [← Subgroup.index_inf, ← Gamma1_mul_eq_inf_of_coprime hab,
        Gamma1_index_mul_of_coprime hab]
    exact mul_right_cancel₀ Subgroup.FiniteIndex.index_ne_zero hmul

/-- **The index of `Γ` is multiplicative in the level.** For coprime `a` and `b`,
`[SL₂(ℤ) : Γ(a b)] = [SL₂(ℤ) : Γ(a)] · [SL₂(ℤ) : Γ(b)]`. -/
theorem Gamma_index_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    (Gamma (a * b)).index = (Gamma a).index * (Gamma b).index := by
  rw [Gamma_index_eq_Gamma1_index_mul, Gamma_index_eq_Gamma1_index_mul,
    Gamma_index_eq_Gamma1_index_mul, Gamma1_index_mul_of_coprime hab, mul_mul_mul_comm]

/-- For coprime levels `a` and `b`, `Γ(a)` has the same relative index in `Γ(b)` as in
`SL₂(ℤ)`. -/
theorem Gamma_relIndex_Gamma_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    (Gamma a).relIndex (Gamma b) = (Gamma a).index := by
  rcases eq_or_ne b 0 with rfl | hb
  · obtain rfl := Nat.coprime_zero_right a |>.mp hab
    simp [Gamma_one_top]
  · have : NeZero b := ⟨hb⟩
    have hmul : (Gamma a).relIndex (Gamma b) * (Gamma b).index =
        (Gamma a).index * (Gamma b).index := by
      rw [← Subgroup.index_inf, ← Gamma_mul_eq_inf_of_coprime hab,
        Gamma_index_mul_of_coprime hab]
    exact mul_right_cancel₀ Subgroup.FiniteIndex.index_ne_zero hmul

/-- **`[SL₂(ℤ) : Γ₁(p)] = p² - 1`** for prime `p`. -/
theorem Gamma1_prime_index (p : ℕ) (hp : Nat.Prime p) :
    (Gamma1 p).index = p ^ 2 - 1 := by
  rw [Gamma1_index_eq_Gamma0_index_mul_totient, Gamma0_prime_index p hp, Nat.totient_prime hp,
    pow_two, mul_self_tsub_one, mul_comm]

/-- **`[SL₂(ℤ) : Γ₁(pᵏ)] = p^(2k - 2) * (p² - 1)`** for prime `p` and `k ≥ 1`. -/
theorem Gamma1_prime_power_index (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k) :
    (Gamma1 (p ^ k)).index = p ^ (2 * k - 2) * (p ^ 2 - 1) := by
  have hexp : k - 1 + (k - 1) = 2 * k - 2 := by omega
  rw [Gamma1_index_eq_Gamma0_index_mul_totient, Gamma0_prime_power_index p hp k hk,
    Nat.totient_prime_pow hp hk, mul_mul_mul_comm, ← pow_add, hexp, pow_two, mul_self_tsub_one,
    mul_comm (p + 1)]

/-- **`[SL₂(ℤ) : Γ(p)] = p * (p² - 1)`** for prime `p`. -/
theorem Gamma_prime_index (p : ℕ) (hp : Nat.Prime p) :
    (Gamma p).index = p * (p ^ 2 - 1) := by
  rw [Gamma_index_eq_Gamma1_index_mul, Gamma1_prime_index p hp, mul_comm]

/-- **`[SL₂(ℤ) : Γ(pᵏ)] = p^(3k - 2) * (p² - 1)`** for prime `p` and `k ≥ 1`. -/
theorem Gamma_prime_power_index (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k) :
    (Gamma (p ^ k)).index = p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  have hexp : 2 * k - 2 + k = 3 * k - 2 := by omega
  rw [Gamma_index_eq_Gamma1_index_mul, Gamma1_prime_power_index p hp k hk,
    mul_right_comm, ← pow_add, hexp]

/-- **The index of `Γ₁(N)`** as a product over the prime factorization of the level:
`[SL₂(ℤ) : Γ₁(N)] = ∏_{pᵏ ∥ N} p^(2k - 2) (p² - 1)` for `N ≠ 0`. -/
theorem Gamma1_index_eq_prod_factorization {N : ℕ} (hN : N ≠ 0) :
    (Gamma1 N).index = N.factorization.prod fun p k ↦ p ^ (2 * k - 2) * (p ^ 2 - 1) := by
  rw [Nat.multiplicative_factorization (fun n ↦ (Gamma1 n).index)
    (fun _ _ ↦ Gamma1_index_mul_of_coprime) (by simp) hN]
  refine Finsupp.prod_congr fun p hp ↦ ?_
  exact Gamma1_prime_power_index p (Nat.prime_of_mem_primeFactors hp) _
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))

/-- **Product formula for the index of `Γ₁(N)`**, with denominators cleared:
`[SL₂(ℤ) : Γ₁(N)] · ∏_{p ∣ N} p² = N² · ∏_{p ∣ N} (p² - 1)` at every level `N : ℕ`.
At `N = 0` both sides vanish. -/
theorem Gamma1_index_mul_prod_primeFactors {N : ℕ} :
    (Gamma1 N).index * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 2 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  calc (Gamma1 N).index * ∏ p ∈ N.primeFactors, p ^ 2
      = ((Gamma0 N).index * ∏ p ∈ N.primeFactors, p) *
          (N.totient * ∏ p ∈ N.primeFactors, p) := by
        rw [Gamma1_index_eq_Gamma0_index_mul_totient, mul_mul_mul_comm, ← Finset.prod_mul_distrib]
        simp_rw [pow_two]
    _ = (N * ∏ p ∈ N.primeFactors, (p + 1)) * (N * ∏ p ∈ N.primeFactors, (p - 1)) := by
        rw [Gamma0_index_mul_prod_primeFactors, Nat.totient_mul_prod_primeFactors]
    _ = N ^ 2 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
        rw [mul_mul_mul_comm, ← pow_two, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun p _ ↦ ?_
        rw [pow_two, mul_self_tsub_one, mul_comm]

/-- **The index of `Γ(N)`** as a product over the prime factorization of the level:
`[SL₂(ℤ) : Γ(N)] = ∏_{pᵏ ∥ N} p^(3k - 2) (p² - 1)` for `N ≠ 0`. -/
theorem Gamma_index_eq_prod_factorization {N : ℕ} (hN : N ≠ 0) :
    (Gamma N).index = N.factorization.prod fun p k ↦ p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  rw [Nat.multiplicative_factorization (fun n ↦ (Gamma n).index)
    (fun _ _ ↦ Gamma_index_mul_of_coprime) (by simp) hN]
  refine Finsupp.prod_congr fun p hp ↦ ?_
  exact Gamma_prime_power_index p (Nat.prime_of_mem_primeFactors hp) _
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))

/-- **Product formula for the index of `Γ(N)`**, with denominators cleared:
`[SL₂(ℤ) : Γ(N)] · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)` at every level `N : ℕ`.
At `N = 0` both sides vanish. -/
theorem Gamma_index_mul_prod_primeFactors {N : ℕ} :
    (Gamma N).index * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  calc (Gamma N).index * ∏ p ∈ N.primeFactors, p ^ 2
      = N * ((Gamma1 N).index * ∏ p ∈ N.primeFactors, p ^ 2) := by
        rw [Gamma_index_eq_Gamma1_index_mul]; ring
    _ = N * (N ^ 2 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1)) := by
        rw [Gamma1_index_mul_prod_primeFactors]
    _ = N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by ring

/-! ### Centre membership and projective (`withCenter`) indices -/

/-- `-I` lies in the principal congruence subgroup `Γ(N)` exactly when `N ∣ 2` (i.e. `N ∈ {1, 2}`),
matching `neg_one_mem_Gamma1_iff`. -/
theorem neg_one_mem_Gamma_iff {N : ℕ} : (-1 : SL(2, ℤ)) ∈ Gamma N ↔ N ∣ 2 := by
  refine ⟨fun h ↦ neg_one_mem_Gamma1_iff.mp (Gamma_le_Gamma1 N h), fun h ↦ ?_⟩
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem N (-1)).mp (neg_one_mem_Gamma1_iff.mpr h)
  exact Gamma_mem.mpr ⟨h00, by simp, h10, h11⟩

/-- The centre `{±I}` of `SL(2, ℤ)` is contained in `Γ₁(N)` iff `N ∣ 2`. -/
theorem center_le_Gamma1_iff {N : ℕ} : Subgroup.center SL(2, ℤ) ≤ Gamma1 N ↔ N ∣ 2 := by
  rw [← neg_one_mem_Gamma1_iff]
  refine ⟨fun h ↦ h (mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)), fun h z hz ↦ ?_⟩
  rcases mem_center_iff_eq_one_or_eq_neg_one.mp hz with rfl | rfl
  · exact one_mem _
  · exact h

/-- The centre `{±I}` of `SL(2, ℤ)` is contained in `Γ(N)` iff `N ∣ 2`. -/
theorem center_le_Gamma_iff {N : ℕ} : Subgroup.center SL(2, ℤ) ≤ Gamma N ↔ N ∣ 2 := by
  rw [← neg_one_mem_Gamma_iff]
  refine ⟨fun h ↦ h (mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)), fun h z hz ↦ ?_⟩
  rcases mem_center_iff_eq_one_or_eq_neg_one.mp hz with rfl | rfl
  · exact one_mem _
  · exact h

/-- Adjoining the centre `{±I}` leaves `Γ₀(N)` unchanged, since `-I ∈ Γ₀(N)` at every level. -/
@[simp]
theorem Gamma0_withCenter (N : ℕ) : (Gamma0 N).withCenter = Gamma0 N :=
  le_antisymm (withCenter_le_Gamma0 le_rfl) (Gamma0 N).le_withCenter

/-- `[SL₂(ℤ) : ±Γ₀(N)] = [SL₂(ℤ) : Γ₀(N)]` at every level `N : ℕ`. -/
theorem Gamma0_withCenter_index (N : ℕ) : (Gamma0 N).withCenter.index = (Gamma0 N).index := by
  rw [Gamma0_withCenter]

/-- Adjoining the centre leaves `Γ₁(N)` unchanged iff `N ∣ 2`. -/
theorem Gamma1_withCenter_eq_self_iff {N : ℕ} :
    (Gamma1 N).withCenter = Gamma1 N ↔ N ∣ 2 :=
  Subgroup.withCenter_eq_self_iff.trans center_le_Gamma1_iff

/-- Adjoining the centre leaves `Γ(N)` unchanged iff `N ∣ 2`. -/
theorem Gamma_withCenter_eq_self_iff {N : ℕ} :
    (Gamma N).withCenter = Gamma N ↔ N ∣ 2 :=
  Subgroup.withCenter_eq_self_iff.trans center_le_Gamma_iff

/-- For `N ∣ 2`, `[SL₂(ℤ) : ±Γ₁(N)] = [SL₂(ℤ) : Γ₁(N)]`. -/
theorem Gamma1_withCenter_index_of_dvd_two {N : ℕ} (hN : N ∣ 2) :
    (Gamma1 N).withCenter.index = (Gamma1 N).index := by
  rw [Gamma1_withCenter_eq_self_iff.mpr hN]

/-- For `N ∣ 2`, `[SL₂(ℤ) : ±Γ(N)] = [SL₂(ℤ) : Γ(N)]`. -/
theorem Gamma_withCenter_index_of_dvd_two {N : ℕ} (hN : N ∣ 2) :
    (Gamma N).withCenter.index = (Gamma N).index := by
  rw [Gamma_withCenter_eq_self_iff.mpr hN]

/-- When `¬ N ∣ 2` (`N = 0` or `N ≥ 3`), `-I ∉ Γ₁(N)`, so
`2 · [SL₂(ℤ) : ±Γ₁(N)] = [SL₂(ℤ) : Γ₁(N)]`. -/
theorem two_mul_Gamma1_withCenter_index_of_not_dvd_two {N : ℕ} (hN : ¬ N ∣ 2) :
    2 * (Gamma1 N).withCenter.index = (Gamma1 N).index :=
  (TauCeti.ModularForm.index_eq_two_mul_index_withCenter_of_neg_one_notMem
    (mt neg_one_mem_Gamma1_iff.mp hN)).symm

/-- When `¬ N ∣ 2` (`N = 0` or `N ≥ 3`), `[SL₂(ℤ) : ±Γ₁(N)] = [SL₂(ℤ) : Γ₁(N)] / 2`. -/
theorem Gamma1_withCenter_index_of_not_dvd_two {N : ℕ} (hN : ¬ N ∣ 2) :
    (Gamma1 N).withCenter.index = (Gamma1 N).index / 2 := by
  rw [← two_mul_Gamma1_withCenter_index_of_not_dvd_two hN, Nat.mul_div_right _ two_pos]

/-- For `N ≥ 3`, `2 · [SL₂(ℤ) : ±Γ₁(N)] = [SL₂(ℤ) : Γ₁(N)]`. -/
theorem two_mul_Gamma1_withCenter_index {N : ℕ} (hN : 3 ≤ N) :
    2 * (Gamma1 N).withCenter.index = (Gamma1 N).index :=
  two_mul_Gamma1_withCenter_index_of_not_dvd_two fun h ↦ by
    have := Nat.le_of_dvd two_pos h; omega

/-- For `N ≥ 3`, `[SL₂(ℤ) : ±Γ₁(N)] = [SL₂(ℤ) : Γ₁(N)] / 2`. -/
theorem Gamma1_withCenter_index_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    (Gamma1 N).withCenter.index = (Gamma1 N).index / 2 :=
  Gamma1_withCenter_index_of_not_dvd_two fun h ↦ by
    have := Nat.le_of_dvd two_pos h; omega

/-- When `¬ N ∣ 2` (`N = 0` or `N ≥ 3`), `-I ∉ Γ(N)`, so
`2 · [SL₂(ℤ) : ±Γ(N)] = [SL₂(ℤ) : Γ(N)]`. -/
theorem two_mul_Gamma_withCenter_index_of_not_dvd_two {N : ℕ} (hN : ¬ N ∣ 2) :
    2 * (Gamma N).withCenter.index = (Gamma N).index :=
  (TauCeti.ModularForm.index_eq_two_mul_index_withCenter_of_neg_one_notMem
    (mt neg_one_mem_Gamma_iff.mp hN)).symm

/-- When `¬ N ∣ 2` (`N = 0` or `N ≥ 3`), `[SL₂(ℤ) : ±Γ(N)] = [SL₂(ℤ) : Γ(N)] / 2`. -/
theorem Gamma_withCenter_index_of_not_dvd_two {N : ℕ} (hN : ¬ N ∣ 2) :
    (Gamma N).withCenter.index = (Gamma N).index / 2 := by
  rw [← two_mul_Gamma_withCenter_index_of_not_dvd_two hN, Nat.mul_div_right _ two_pos]

/-- For `N ≥ 3`, `2 · [SL₂(ℤ) : ±Γ(N)] = [SL₂(ℤ) : Γ(N)]`. -/
theorem two_mul_Gamma_withCenter_index {N : ℕ} (hN : 3 ≤ N) :
    2 * (Gamma N).withCenter.index = (Gamma N).index :=
  two_mul_Gamma_withCenter_index_of_not_dvd_two fun h ↦ by
    have := Nat.le_of_dvd two_pos h; omega

/-- For `N ≥ 3`, `[SL₂(ℤ) : ±Γ(N)] = [SL₂(ℤ) : Γ(N)] / 2`. -/
theorem Gamma_withCenter_index_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    (Gamma N).withCenter.index = (Gamma N).index / 2 :=
  Gamma_withCenter_index_of_not_dvd_two fun h ↦ by
    have := Nat.le_of_dvd two_pos h; omega

end CongruenceSubgroup

namespace Matrix.SpecialLinearGroup

/-- The order of `SL(2, ZMod N)` equals the index `[SL₂(ℤ) : Γ(N)]` at every level `N : ℕ`
(both vanish at `N = 0`). -/
theorem natCard_fin_two_zmod_eq_Gamma_index (N : ℕ) :
    Nat.card SL(2, ZMod N) = (CongruenceSubgroup.Gamma N).index :=
  (CongruenceSubgroup.Gamma_index_eq_natCard_SL N).symm

/-- **The order of `SL(2, ZMod N)`** as a product over the prime factorization of `N ≠ 0`:
`|SL(2, ZMod N)| = ∏_{pᵏ ∥ N} p^(3k - 2) (p² - 1)`. -/
theorem natCard_fin_two_zmod_eq_prod_factorization {N : ℕ} (hN : N ≠ 0) :
    Nat.card SL(2, ZMod N) = N.factorization.prod fun p k ↦ p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  rw [natCard_fin_two_zmod_eq_Gamma_index, CongruenceSubgroup.Gamma_index_eq_prod_factorization hN]

/-- **Product formula for `|SL(2, ZMod N)|`**, with denominators cleared:
`|SL(2, ZMod N)| · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)` at every `N : ℕ`. -/
theorem natCard_fin_two_zmod_mul_prod_primeFactors {N : ℕ} :
    Nat.card SL(2, ZMod N) * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [natCard_fin_two_zmod_eq_Gamma_index, CongruenceSubgroup.Gamma_index_mul_prod_primeFactors]

end Matrix.SpecialLinearGroup
