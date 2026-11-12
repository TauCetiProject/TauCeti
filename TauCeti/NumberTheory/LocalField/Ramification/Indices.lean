/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic
import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup

/-!
# Tame and wild parts of the ramification index

For an extension of nonarchimedean local fields with residue characteristic `p`, we write
`e = ε * p ^ w`. Here `ε` is the tame ramification index and `w` is the wild ramification
exponent. The exponent `w` is not the different exponent or Serre's wild exponent.

We establish positivity, the tame criterion, invariance under algebra equivalence, and the
tower laws: tame indices multiply, whereas wild ramification exponents add. In the Galois
case the two factors are the order of the tame quotient and the order of wild inertia,
respectively. In particular, the tame index divides the order of the multiplicative group
of the residue field of the extension.

The group-theoretic input is the tame character and wild-inertia order from
`TamelyRamified.Basic`, following Serre, *Local Fields*, Chapter IV, §2.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L]

/-- The exponent of the residue characteristic in the ramification index. -/
noncomputable def wildRamificationExponent : ℕ :=
  (ramificationIndex K L).factorization (ringChar 𝓀[K])

/-- The prime-to-residue-characteristic part of the ramification index. -/
noncomputable def tameRamificationIndex : ℕ :=
  ramificationIndex K L / ringChar 𝓀[K] ^ wildRamificationExponent K L

/-- The wild ramification exponent is the multiplicity of the residue characteristic. -/
theorem wildRamificationExponent_eq_multiplicity :
    wildRamificationExponent K L = multiplicity (ringChar 𝓀[K]) (ramificationIndex K L) :=
  Nat.factorization_def _ (CharP.prime_ringChar 𝓀[K])

/-- The defining formula for the wild ramification exponent. -/
theorem wildRamificationExponent_def :
    wildRamificationExponent K L =
      (ramificationIndex K L).factorization (ringChar 𝓀[K]) := (rfl)

/-- The defining quotient formula for the tame ramification index. -/
theorem tameRamificationIndex_def :
    tameRamificationIndex K L =
      ramificationIndex K L / ringChar 𝓀[K] ^ wildRamificationExponent K L := (rfl)

variable [ValuativeExtension K L]

/-- The tame index is positive. -/
theorem tameRamificationIndex_pos : 0 < tameRamificationIndex K L := by
  rw [tameRamificationIndex_def, wildRamificationExponent_def]
  exact Nat.ordCompl_pos _ (ramificationIndex_pos (K := K) (L := L)).ne'

/-- The residue characteristic does not divide the tame index. -/
theorem not_dvd_tameRamificationIndex : ¬ ringChar 𝓀[K] ∣ tameRamificationIndex K L := by
  rw [tameRamificationIndex_def, wildRamificationExponent_def]
  exact Nat.not_dvd_ordCompl (CharP.prime_ringChar 𝓀[K])
    (ramificationIndex_pos (K := K) (L := L)).ne'

omit [ValuativeExtension K L] in
/-- The ramification index factors into its tame and wild parts. -/
theorem tameRamificationIndex_mul_pow_wildRamificationExponent :
    tameRamificationIndex K L * ringChar 𝓀[K] ^ wildRamificationExponent K L =
      ramificationIndex K L := by
  rw [mul_comm, tameRamificationIndex_def, wildRamificationExponent_def]
  exact Nat.ordProj_mul_ordCompl_eq_self _ _

/-- Tameness is equivalent to vanishing of the wild ramification exponent. -/
@[simp]
theorem wildRamificationExponent_eq_zero_iff :
    wildRamificationExponent K L = 0 ↔ IsTamelyRamified K L := by
  rw [wildRamificationExponent_def, isTamelyRamified_iff,
    (CharP.prime_ringChar 𝓀[K]).dvd_iff_one_le_factorization ramificationIndex_pos.ne']
  omega

variable {K L} in
/-- For a tame extension the tame index is the full ramification index. -/
@[simp]
theorem IsTamelyRamified.tameRamificationIndex_eq (h : IsTamelyRamified K L) :
    tameRamificationIndex K L = ramificationIndex K L := by
  simp [tameRamificationIndex_def, (wildRamificationExponent_eq_zero_iff K L).2 h]

section Equivalence

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M]

/-- The wild ramification exponent is an invariant of the extension up to algebra equivalence. -/
theorem wildRamificationExponent_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    wildRamificationExponent K L = wildRamificationExponent K M := by
  simp only [wildRamificationExponent_def, ramificationIndex_eq_of_algEquiv K L M e]

/-- The tame ramification index is an invariant of the extension up to algebra equivalence. -/
theorem tameRamificationIndex_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    tameRamificationIndex K L = tameRamificationIndex K M := by
  simp only [tameRamificationIndex_def, wildRamificationExponent_def,
    ramificationIndex_eq_of_algEquiv K L M e]

end Equivalence

section Tower

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M] [ValuativeExtension L M]

/-- Wild ramification exponents add in a tower. -/
theorem wildRamificationExponent_tower :
    wildRamificationExponent K M =
      wildRamificationExponent K L + wildRamificationExponent L M := by
  simp only [wildRamificationExponent_def, ramificationIndex_tower (K := K) (L := L) M,
    Nat.factorization_mul (ramificationIndex_pos (K := K) (L := L)).ne'
      (ramificationIndex_pos (K := L) (L := M)).ne', Finsupp.add_apply,
    Algebra.ringChar_eq 𝓀[K] 𝓀[L]]

/-- Tame ramification indices multiply in a tower. -/
theorem tameRamificationIndex_tower :
    tameRamificationIndex K M = tameRamificationIndex K L * tameRamificationIndex L M := by
  simp only [tameRamificationIndex_def, wildRamificationExponent_def,
    ramificationIndex_tower (K := K) (L := L) M, Nat.ordCompl_mul,
    Algebra.ringChar_eq 𝓀[K] 𝓀[L]]

end Tower

section Galois

open LocalFieldsRamification

variable [IsGalois K L]

/-- The tame index is the order of the quotient of inertia by wild inertia. -/
theorem tameRamificationIndex_eq_natCard_tameQuotient [Module.Finite K L] :
    tameRamificationIndex K L = Nat.card
      (lowerRamificationGroup K L 0 ⧸
        (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) := by
  rw [← Subgroup.index_eq_card, Subgroup.index_eq_card_div,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (lowerRamificationGroup_antitone K L (by omega : (0 : ℤ) ≤ 1))).toEquiv,
    natCard_lowerRamificationGroup_zero, natCard_lowerRamificationGroup_one]
  simp only [tameRamificationIndex_def, wildRamificationExponent_def]

/-- The tame index divides the order of the multiplicative group of the residue field of `L`. -/
theorem tameRamificationIndex_dvd_card_residueField_sub_one :
    tameRamificationIndex K L ∣ Nat.card 𝓀[L] - 1 := by
  have := finite_of_valuativeExtension K L
  rw [tameRamificationIndex_eq_natCard_tameQuotient]
  rw [lowerRamificationGroup_def, lowerRamificationGroup_def]
  exact card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one L (L ≃ₐ[K] L)

/-- The tame index divides `q ^ f - 1`, where `q` is the residue cardinality of the base. -/
theorem tameRamificationIndex_dvd_card_pow_inertiaDegree_sub_one :
    tameRamificationIndex K L ∣ Nat.card 𝓀[K] ^ inertiaDegree K L - 1 := by
  rw [← natCard_residueField K L]
  exact tameRamificationIndex_dvd_card_residueField_sub_one K L

end Galois

end TauCeti
