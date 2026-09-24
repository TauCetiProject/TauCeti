/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Length
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NonSimplyLaced
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString

/-!
# Root strings in the pinned F₄ root system

This file derives root-string bounds from the invariant root-length identity. The proofs use the
abstract root-system API after the pinned length table has supplied the two possible squared
lengths. They avoid case splits over the forty-eight root coordinates.

The initial results cover the strings needed to construct the characteristic-two short-root
submodule. In particular, a short-short bracket landing in a long root has absolute structure
constant two, while a long-root direction preserves the short-root span.
-/

public section

namespace TauCeti.DynkinType

/-- The pinned index of the root opposite to `α`. -/
noncomputable def f4OppositeRootIndex (α : Fin 48) : Fin 48 :=
  f4SimplyConnectedRootDatum.reflectionPerm α α

/-- The opposite index is the self-reflection in the pinned root datum. -/
theorem f4OppositeRootIndex_eq_reflectionPerm (α : Fin 48) :
    f4OppositeRootIndex α = f4SimplyConnectedRootDatum.reflectionPerm α α := (rfl)

/-- Taking the opposite pinned root index twice restores the index. -/
@[simp] theorem f4OppositeRootIndex_f4OppositeRootIndex (α : Fin 48) :
    f4OppositeRootIndex (f4OppositeRootIndex α) = α := by
  exact f4SimplyConnectedRootDatum.indexNeg.neg_neg α

/-- Negation of pinned roots is exactly the opposite-index permutation. -/
theorem f4_root_eq_neg_iff (α β : Fin 48) :
    f4SimplyConnectedRootDatum.root β = -f4SimplyConnectedRootDatum.root α ↔
      β = f4OppositeRootIndex α := by
  exact f4SimplyConnectedRootDatum.root_eq_neg_iff

/-- Being non-opposite is symmetric in the two pinned root indices. -/
theorem ne_f4OppositeRootIndex_comm (α β : Fin 48) :
    β ≠ f4OppositeRootIndex α ↔ α ≠ f4OppositeRootIndex β := by
  constructor
  · intro h h'
    apply h
    rw [h', f4OppositeRootIndex_f4OppositeRootIndex]
  · intro h h'
    apply h
    rw [h', f4OppositeRootIndex_f4OppositeRootIndex]

/-- The tabulated F4 root length is quadratic along every integral root relation. -/
theorem f4Length_of_root_eq_add_zsmul (α β γ : Fin 48) (n : ℤ)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + n • f4SimplyConnectedRootDatum.root α) :
    f4Length γ = f4Length β + n * f4Length α *
      f4SimplyConnectedRootDatum.pairing β α + n ^ 2 * f4Length α :=
  f4SimplyConnectedRootDatum.length_of_root_eq_add_zsmul f4Length
    f4Length_mul_pairing_comm α β γ n h


/-- Distinct non-opposite F4 roots of equal length have pairing `-1`, `0`, or `1`. -/
theorem f4_pairing_mem_neg_one_zero_one_of_length_eq (α β : Fin 48)
    (hαβ : f4Length α = f4Length β) (hne : β ≠ α)
    (hneg : f4SimplyConnectedRootDatum.root β ≠
      -f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.pairing β α ∈ ({-1, 0, 1} : Set ℤ) :=
  f4SimplyConnectedRootDatum.pairing_mem_neg_one_zero_one_of_length_eq f4Length
    f4Length_mul_pairing_comm α β (abs_pairing_f4SimplyConnectedRootDatum_le_two β α)
    (f4Length_pos α) hαβ hne hneg

/-- An equal-length, non-opposite F4 root string has no second positive endpoint. -/
theorem f4_not_root_eq_add_nsmul_of_length_eq_of_two_le (α β γ : Fin 48) (n : ℕ)
    (hαβ : f4Length α = f4Length β)
    (hneg : f4SimplyConnectedRootDatum.root β ≠
      -f4SimplyConnectedRootDatum.root α) (hn : 2 ≤ n)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (n : ℤ) • f4SimplyConnectedRootDatum.root α) : False :=
  f4SimplyConnectedRootDatum.not_root_eq_add_nsmul_of_length_eq_of_two_le f4Length
    f4Length_mul_pairing_comm α β γ n (abs_pairing_f4SimplyConnectedRootDatum_le_two β α)
    (f4Length_pos α) hαβ (by
      rcases f4Length_eq_one_or_eq_two α with hα | hα <;>
        rcases f4Length_eq_one_or_eq_two γ with hγ | hγ <;>
        omega) hneg hn h

/-- When the sum of two short F4 roots is long, their Cartan pairing is zero. -/
theorem f4_pairing_eq_zero_of_short_add_short_eq_long (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 1) (hγ : f4Length γ = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.pairing β α = 0 :=
  f4SimplyConnectedRootDatum.pairing_eq_zero_of_short_add_short_eq_long f4Length
    f4Length_mul_pairing_comm α β γ hα hβ hγ h

/-- A positive root string from a short root in a long-root direction has at most
one step, and that step is again short. -/
theorem f4_n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
    (α β γ : Fin 48) (n : ℕ)
    (hα : f4Length α = 2) (hβ : f4Length β = 1) (hn : 0 < n)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (n : ℤ) • f4SimplyConnectedRootDatum.root α) :
    n = 1 ∧ f4SimplyConnectedRootDatum.pairing β α = -1 ∧ f4Length γ = 1 :=
  RootPairing.n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
    (P := f4SimplyConnectedRootDatum) f4Length f4Length_mul_pairing_comm
    α β γ n (abs_pairing_f4SimplyConnectedRootDatum_le_two α β)
    hα hβ (f4Length_eq_one_or_eq_two γ) hn h

/-- The short-short-to-long root edge has descending chain coefficient one,
so its Chevalley bracket coefficient has absolute value two. -/
theorem f4_chainBotCoeff_eq_one_of_short_add_short_eq_long (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 1) (hγ : f4Length γ = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.chainBotCoeff α β = 1 :=
  f4SimplyConnectedRootDatum.chainBotCoeff_eq_one_of_short_add_short_eq_long f4Length
    f4Length_mul_pairing_comm α β γ (fun δ _ => f4Length_eq_one_or_eq_two δ)
    hα hβ hγ h

/-- If two steps in a short-root direction carry a long root to another root, the Cartan
pairings are `-2` and `-1`, and the endpoint is long. This is the root string underlying the
quadratic term in the characteristic-two special isogeny. -/
theorem f4_pairings_of_long_add_two_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.pairing β α = -2 ∧
      f4SimplyConnectedRootDatum.pairing α β = -1 ∧ f4Length γ = 2 :=
  f4SimplyConnectedRootDatum.pairings_of_long_add_two_short f4Length
    f4Length_mul_pairing_comm α β γ hα hβ (f4Length_eq_one_or_eq_two γ) h

/-- A long root and a short direction joined by a two-step root string have descending
coefficient zero and ascending coefficient two. The intermediate root is short, and its outgoing
bracket coefficient has absolute value two. -/
theorem exists_f4_short_midpoint_of_long_add_two_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    ∃ δ : Fin 48,
      f4SimplyConnectedRootDatum.root δ =
          f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α ∧
        f4Length δ = 1 ∧
        f4SimplyConnectedRootDatum.chainBotCoeff α β = 0 ∧
        f4SimplyConnectedRootDatum.chainTopCoeff α β = 2 ∧
        f4SimplyConnectedRootDatum.chainBotCoeff α δ = 1 ∧
        f4SimplyConnectedRootDatum.chainTopCoeff α δ = 1 :=
  f4SimplyConnectedRootDatum.exists_short_midpoint_of_long_add_two_short f4Length
    f4Length_mul_pairing_comm α β γ hα hβ (f4Length_eq_one_or_eq_two γ) h

/-- An F4 root edge whose source and target have equal length has descending chain coefficient
zero, regardless of the length of the root direction. -/
theorem f4_chainBotCoeff_eq_zero_of_add_of_length_eq (α β γ : Fin 48)
    (hβγ : f4Length β = f4Length γ)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.chainBotCoeff α β = 0 :=
  f4SimplyConnectedRootDatum.chainBotCoeff_eq_zero_of_add_of_length_eq f4Length
    f4Length_mul_pairing_comm α β γ (f4Length_pos α)
    (fun δ _ => by rcases f4Length_eq_one_or_eq_two δ with hδ | hδ <;> omega)
    (f4Length_pos β) hβγ h

/-- Distinct or equal non-opposite roots of equal length have Cartan pairing at least `-1`. -/
theorem f4_pairing_ge_neg_one_of_length_eq_ne_opposite
    (α β : Fin 48) (hαβ : f4Length α = f4Length β)
    (hopp : β ≠ f4OppositeRootIndex α) :
    -1 ≤ f4SimplyConnectedRootDatum.pairing β α := by
  have hnegroot : f4SimplyConnectedRootDatum.root β ≠
      -f4SimplyConnectedRootDatum.root α := by
    intro hroot
    exact hopp ((f4_root_eq_neg_iff α β).mp hroot)
  by_cases hsame : β = α
  · subst β
    simp only [f4SimplyConnectedRootDatum.pairing_same]
    omega
  · have hpair := f4_pairing_mem_neg_one_zero_one_of_length_eq
      α β hαβ hsame hnegroot
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
    rcases hpair with hpair | hpair | hpair <;> omega

/-- The sum of two long roots, when it is a root, is long. -/
theorem f4Length_eq_two_of_root_eq_add_of_long_long (α β γ : Fin 48)
    (hα : f4Length α = 2) (hβ : f4Length β = 2)
    (hγ : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4Length γ = 2 := by
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 1
    (by simpa only [one_zsmul] using hγ)
  have hγ := f4Length_eq_one_or_eq_two γ
  rw [hα, hβ] at hlen
  norm_num at hlen
  omega

/-- A short-root direction has no third step from a long root. -/
theorem f4_not_root_eq_long_add_three_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (hγ : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + (3 : ℤ) •
        f4SimplyConnectedRootDatum.root α) : False := by
  have hpair := abs_pairing_f4SimplyConnectedRootDatum_le_two β α
  have hpairLower : -2 ≤ f4SimplyConnectedRootDatum.pairing β α :=
    (abs_le.mp hpair).1
  rw [f4SimplyConnectedRootDatum_pairing] at hpairLower
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 3 hγ
  have hγ := f4Length_eq_one_or_eq_two γ
  rw [hα, hβ] at hlen
  norm_num at hlen
  omega

/-- A short root with Cartan pairing one has no positive step in the given root direction. -/
theorem f4_chainTopCoeff_eq_zero_of_short_pairing_eq_one (α β : Fin 48)
    (hβ : f4Length β = 1)
    (hpair : f4SimplyConnectedRootDatum.pairing β α = 1) :
    f4SimplyConnectedRootDatum.chainTopCoeff α β = 0 := by
  rw [f4SimplyConnectedRootDatum.chainTopCoeff_eq_zero_iff]
  right
  rintro ⟨γ, hγ⟩
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 1 (by
    simpa only [one_zsmul] using hγ)
  rcases f4Length_eq_one_or_eq_two α with hα | hα <;>
    rcases f4Length_eq_one_or_eq_two γ with hγlen | hγlen <;>
    rw [hα, hβ, hγlen, hpair] at hlen <;> norm_num at hlen

/-- A short root orthogonal to a long root has no positive step in the long-root direction. -/
theorem f4_chainTopCoeff_eq_zero_of_short_long_pairing_eq_zero (α β : Fin 48)
    (hα : f4Length α = 2) (hβ : f4Length β = 1)
    (hpair : f4SimplyConnectedRootDatum.pairing β α = 0) :
    f4SimplyConnectedRootDatum.chainTopCoeff α β = 0 := by
  rw [f4SimplyConnectedRootDatum.chainTopCoeff_eq_zero_iff]
  right
  rintro ⟨γ, hγ⟩
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 1 (by
    simpa only [one_zsmul] using hγ)
  rcases f4Length_eq_one_or_eq_two γ with hγlen | hγlen <;>
    rw [hα, hβ, hγlen, hpair] at hlen <;> norm_num at hlen

end TauCeti.DynkinType
