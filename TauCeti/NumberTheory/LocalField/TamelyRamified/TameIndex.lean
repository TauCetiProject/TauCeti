/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic
import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup

/-!
# The tame index and the wild ramification exponent

Let `L/K` be an extension of nonarchimedean local fields with residue characteristic `p` and
ramification index `e = e(L/K)`. This file splits `e` into its `p`-part and its prime-to-`p` part,

`e = ε · p ^ w` with `p ∤ ε`,

where `w = v_p(e)` is the **wild ramification exponent** and `ε` is the **tame index** of `L/K`.
The tame index is the ramification index of the maximal tamely ramified subextension
(`IntermediateField.ramificationIndex_maximalTameExtension_inf`), and `p ^ w` is the ramification
index of the wild step above it; for `L/K` Galois, `p ^ w` is the order of the wild inertia group
`G_1` (`TauCeti.LocalFieldsRamification.natCard_lowerRamificationGroup_one`).

The exponent `w` is not Serre's wild exponent `c(L) = d(L) + 1 − [L : K]` of the mass formula
(`IntermediateField.wildExponent`), which is measured by the discriminant rather than by the
ramification index.

## Main definitions

* `TauCeti.wildRamificationExponent K L`: the exponent `w = v_p(e(L/K))`.
* `TauCeti.tameRamificationIndex K L`: the prime-to-`p` part `ε = e(L/K) / p ^ w`.

## Main results

* `TauCeti.tameRamificationIndex_mul_pow_wildRamificationExponent`: `ε · p ^ w = e(L/K)`.
* `TauCeti.tameRamificationIndex_pos` and `TauCeti.not_dvd_tameRamificationIndex`: the tame index
  is positive and prime to `p`.
* `TauCeti.wildRamificationExponent_eq_of_mul_pow` and
  `TauCeti.tameRamificationIndex_eq_of_mul_pow`: the pair `(ε, w)` is the unique pair with
  `e(L/K) = ε · p ^ w` and `p ∤ ε`.
* `TauCeti.wildRamificationExponent_eq_zero_iff` and
  `TauCeti.tameRamificationIndex_eq_ramificationIndex_iff`: `L/K` is tamely ramified exactly when
  `w = 0`, equivalently when `ε = e(L/K)`.
* `TauCeti.wildRamificationExponent_tower` and `TauCeti.tameRamificationIndex_tower`: in a tower
  `M/L/K` the wild ramification exponents add and the tame indices multiply.
* `TauCeti.wildRamificationExponent_eq_of_algEquiv` and
  `TauCeti.tameRamificationIndex_eq_of_algEquiv`: both are invariant under `K`-algebra
  equivalence.
* `TauCeti.tameRamificationIndex_dvd_card_residueField_sub_one`: for `L/K` Galois, `ε` divides
  `#𝓀[L] - 1 = q ^ f - 1`, where `q = #𝓀[K]` and `f = f(L/K)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L]

section Defs

variable (K L)

/-- The **wild ramification exponent** of an extension `L/K` of nonarchimedean local fields: the
exponent `w = v_p(e(L/K))` of the residue characteristic `p` in the ramification index, so that
`p ^ w` is the wild part of `e(L/K)`. -/
def wildRamificationExponent : ℕ :=
  (ramificationIndex K L).factorization (ringChar 𝓀[K])

/-- The **tame index** of an extension `L/K` of nonarchimedean local fields: the prime-to-`p`
part `ε = e(L/K) / p ^ w` of the ramification index, where `p` is the residue characteristic and
`w` the wild ramification exponent. -/
def tameRamificationIndex : ℕ :=
  ramificationIndex K L / ringChar 𝓀[K] ^ wildRamificationExponent K L

/-- The defining formula of `wildRamificationExponent`: the multiplicity of the residue
characteristic in the ramification index. -/
theorem wildRamificationExponent_def :
    wildRamificationExponent K L = (ramificationIndex K L).factorization (ringChar 𝓀[K]) :=
  (rfl)

/-- The defining formula of `tameRamificationIndex`: the ramification index divided by its
residue-characteristic part. -/
theorem tameRamificationIndex_def :
    tameRamificationIndex K L =
      ramificationIndex K L / ringChar 𝓀[K] ^ wildRamificationExponent K L :=
  (rfl)

/-- The tame index is the prime-to-`p` part `ordCompl[p] e = e / p ^ v_p(e)` of the ramification
index, in Mathlib's notation, so that Mathlib's API for `ordCompl` applies to it. -/
theorem tameRamificationIndex_eq_ordCompl :
    tameRamificationIndex K L = ordCompl[ringChar 𝓀[K]] (ramificationIndex K L) :=
  (rfl)

/-- **The tame index times the wild part is the ramification index**: `ε · p ^ w = e(L/K)`. -/
@[simp]
theorem tameRamificationIndex_mul_pow_wildRamificationExponent :
    tameRamificationIndex K L * ringChar 𝓀[K] ^ wildRamificationExponent K L =
      ramificationIndex K L := by
  rw [tameRamificationIndex_eq_ordCompl, wildRamificationExponent_def, mul_comm]
  exact Nat.ordProj_mul_ordCompl_eq_self _ _

end Defs

variable [ValuativeExtension K L]

/-- The tame index is positive. -/
theorem tameRamificationIndex_pos : 0 < tameRamificationIndex K L := by
  rw [tameRamificationIndex_eq_ordCompl]
  exact Nat.ordCompl_pos _ ramificationIndex_pos.ne'

variable (K L) in
/-- The tame index is prime to the residue characteristic. -/
theorem not_dvd_tameRamificationIndex : ¬ ringChar 𝓀[K] ∣ tameRamificationIndex K L := by
  rw [tameRamificationIndex_eq_ordCompl]
  exact Nat.not_dvd_ordCompl (CharP.prime_ringChar 𝓀[K]) ramificationIndex_pos.ne'

/-- The wild ramification exponent is determined by any factorization `e(L/K) = a · p ^ k` with
`p ∤ a`: it is `k`. -/
theorem wildRamificationExponent_eq_of_mul_pow {a k : ℕ}
    (h : ramificationIndex K L = a * ringChar 𝓀[K] ^ k) (ha : ¬ ringChar 𝓀[K] ∣ a) :
    wildRamificationExponent K L = k := by
  have hp := CharP.prime_ringChar 𝓀[K]
  have ha0 : a ≠ 0 := by rintro rfl; simp [ramificationIndex_pos.ne'] at h
  rw [wildRamificationExponent_def, h, Nat.factorization_mul ha0 (pow_ne_zero _ hp.ne_zero),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd ha, hp.factorization_pow,
    Finsupp.single_eq_same, zero_add]

/-- The tame index is determined by any factorization `e(L/K) = a · p ^ k` with `p ∤ a`: it is
`a`. -/
theorem tameRamificationIndex_eq_of_mul_pow {a k : ℕ}
    (h : ramificationIndex K L = a * ringChar 𝓀[K] ^ k) (ha : ¬ ringChar 𝓀[K] ∣ a) :
    tameRamificationIndex K L = a := by
  rw [tameRamificationIndex_def, wildRamificationExponent_eq_of_mul_pow h ha, h,
    Nat.mul_div_cancel _ (pow_pos (CharP.prime_ringChar 𝓀[K]).pos _)]

variable (K L) in
/-- **The tame criterion.** An extension is tamely ramified exactly when its wild ramification
exponent vanishes. -/
@[simp]
theorem wildRamificationExponent_eq_zero_iff :
    wildRamificationExponent K L = 0 ↔ IsTamelyRamified K L := by
  rw [wildRamificationExponent_def, Nat.factorization_eq_zero_iff, isTamelyRamified_iff]
  simp [CharP.prime_ringChar 𝓀[K], ramificationIndex_pos.ne']

variable (K L) in
/-- An extension is tamely ramified exactly when its tame index is its whole ramification
index. -/
theorem tameRamificationIndex_eq_ramificationIndex_iff :
    tameRamificationIndex K L = ramificationIndex K L ↔ IsTamelyRamified K L := by
  conv_lhs => rw [← tameRamificationIndex_mul_pow_wildRamificationExponent K L, eq_comm,
    Nat.mul_eq_left tameRamificationIndex_pos.ne',
    Nat.pow_eq_one, or_iff_right (CharP.prime_ringChar 𝓀[K]).ne_one]
  exact wildRamificationExponent_eq_zero_iff K L

section Tower

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension L M]

/-- **Additivity of the wild ramification exponent in a tower** `M/L/K`:
`w(M/K) = w(L/K) + w(M/L)`. -/
theorem wildRamificationExponent_tower :
    wildRamificationExponent K M = wildRamificationExponent K L + wildRamificationExponent L M := by
  rw [wildRamificationExponent_def, wildRamificationExponent_def, wildRamificationExponent_def,
    ← Algebra.ringChar_eq 𝓀[K] 𝓀[L], ramificationIndex_tower (K := K) (L := L) M,
    Nat.factorization_mul ramificationIndex_pos.ne' ramificationIndex_pos.ne', Finsupp.add_apply]

/-- **Multiplicativity of the tame index in a tower** `M/L/K`: `ε(M/K) = ε(L/K) · ε(M/L)`. -/
theorem tameRamificationIndex_tower :
    tameRamificationIndex K M = tameRamificationIndex K L * tameRamificationIndex L M := by
  rw [tameRamificationIndex_eq_ordCompl, tameRamificationIndex_eq_ordCompl,
    tameRamificationIndex_eq_ordCompl, ← Algebra.ringChar_eq 𝓀[K] 𝓀[L],
    ramificationIndex_tower (K := K) (L := L) M, Nat.ordCompl_mul]

end Tower

section AlgEquiv

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M]

variable (K L) in
/-- The wild ramification exponent is unchanged by an equivalence of extensions over the base
field. -/
theorem wildRamificationExponent_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    wildRamificationExponent K L = wildRamificationExponent K M := by
  rw [wildRamificationExponent_def, wildRamificationExponent_def,
    ramificationIndex_eq_of_algEquiv K L M e]

variable (K L) in
/-- The tame index is unchanged by an equivalence of extensions over the base field. -/
theorem tameRamificationIndex_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    tameRamificationIndex K L = tameRamificationIndex K M := by
  rw [tameRamificationIndex_eq_ordCompl, tameRamificationIndex_eq_ordCompl,
    ramificationIndex_eq_of_algEquiv K L M e]

end AlgEquiv

open LocalFieldsRamification in
/-- **The tame index divides `q ^ f - 1`.** For a finite Galois extension `L/K` of nonarchimedean
local fields, the tame index `ε` divides `#𝓀[L] - 1`, where `#𝓀[L] = q ^ f` with `q = #𝓀[K]` and
`f = f(L/K)` (`TauCeti.natCard_residueField`). The quotient `G_0 / G_1` of the inertia group by
wild inertia has order `e / p ^ w = ε` and embeds into `𝓀[L]ˣ` through the tame character. -/
theorem tameRamificationIndex_dvd_card_residueField_sub_one [IsGalois K L] :
    tameRamificationIndex K L ∣ Nat.card 𝓀[L] - 1 := by
  have := finite_of_valuativeExtension K L
  have hG := card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one L (L ≃ₐ[K] L)
  -- `G_1` has index `ε` in `G_0`, since `#G_0 = e = ε · p ^ w` and `#G_1 = p ^ w`.
  have hrel := Subgroup.relIndex_mul_card (lowerRamificationGroup K L 1)
    (lowerRamificationGroup K L 0)
  rw [inf_of_le_left (lowerRamificationGroup_antitone K L zero_le_one),
    natCard_lowerRamificationGroup_one, natCard_lowerRamificationGroup_zero,
    ← wildRamificationExponent_def,
    ← tameRamificationIndex_mul_pow_wildRamificationExponent] at hrel
  have hε := Nat.eq_of_mul_eq_mul_right (pow_pos (CharP.prime_ringChar 𝓀[K]).pos _) hrel
  rwa [IsLocalRing.RamificationGroupGraded, zero_add, ← lowerRamificationGroup_def,
    ← lowerRamificationGroup_def, ← Subgroup.index_eq_card, ← Subgroup.relIndex, hε] at hG

end TauCeti
