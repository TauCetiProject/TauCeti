/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.GroupTheory.PGroup

/-!
# Maximal primary subextensions of finite abelian extensions

Mathlib's Galois correspondence and `IsPGroup` give `IsAbelianGalois.primarySubfield`,
the largest subextension of `p`-power degree for prime `p` (`le_primarySubfield_iff`).
Its degree is the `p`-part of the full degree (`finrank_primarySubfield`).
-/

public section

open scoped IsMulCommutative Nat

namespace IsAbelianGalois

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L]

/-- The fixed field of the image of the power map with exponent the `p`-part of `[L : K]`. For
a finite abelian extension and prime `p`, this is the maximal `p`-power degree subextension. -/
noncomputable def primarySubfield (p : ℕ) : IntermediateField K L :=
  IntermediateField.fixedField
    (powMonoidHom (α := Gal(L/K)) (ordProj[p] (Module.finrank K L))).range

/-- The primary subfield is the fixed field of the image of the `ordProj[p] [L : K]` power map. -/
theorem primarySubfield_def (p : ℕ) :
    primarySubfield K L p = IntermediateField.fixedField
      (powMonoidHom (α := Gal(L/K)) (ordProj[p] (Module.finrank K L))).range := (rfl)

variable {K L}

-- Not a simp lemma: it expands membership into a quantified fixed-point condition.
/-- The primary subfield consists of the elements fixed by the indicated powers. -/
theorem mem_primarySubfield_iff {p : ℕ} {x : L} :
    x ∈ primarySubfield K L p ↔ ∀ σ : Gal(L/K), (σ ^ ordProj[p] (Module.finrank K L)) x = x := by
  rw [primarySubfield_def, IntermediateField.mem_fixedField_iff]
  exact ⟨fun h σ ↦ h _ ⟨σ, rfl⟩, fun h _ ⟨σ, hσ⟩ ↦ hσ ▸ h σ⟩

-- Not a simp lemma: it would replace a field inclusion by an existential degree condition.
/-- A subextension of a finite abelian extension lies in the primary subfield for prime `p`
if and only if its degree is a power of `p`. -/
theorem le_primarySubfield_iff [FiniteDimensional K L] {p : ℕ} (hp : p.Prime)
    {E : IntermediateField K L} :
    E ≤ primarySubfield K L p ↔ ∃ n : ℕ, Module.finrank K E = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  rw [primarySubfield_def, IntermediateField.le_fixedField_iff_le_fixingSubgroup,
    ← E.restrictNormalHom_ker, ← IsGalois.card_aut_eq_finrank K E, ← IsPGroup.iff_card]
  constructor
  · intro h τ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L τ
    refine ⟨(Module.finrank K L).factorization p, ?_⟩
    rw [← map_pow, ← MonoidHom.mem_ker]
    exact h ⟨σ, rfl⟩
  · intro h σ hσ
    obtain ⟨τ, rfl⟩ := hσ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
    have hd : Nat.card Gal(E/K) ∣ ordProj[p] (Module.finrank K L) := by
      rw [hn, ← hp.pow_dvd_iff_dvd_ordProj Module.finrank_pos.ne', ← hn,
        IsGalois.card_aut_eq_finrank]
      exact Module.finrank_dvd_finrank_right K E L
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, ← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_natCard _).trans hd

/-- The primary subfield is the base field when the `p`-part of the degree is `1`. -/
@[simp] theorem primarySubfield_eq_bot_of_ordProj_eq_one {p : ℕ}
    (hdeg : ordProj[p] (Module.finrank K L) = 1) : primarySubfield K L p = ⊥ := by
  rw [primarySubfield_def, hdeg]
  have h : Function.Surjective (powMonoidHom (α := Gal(L/K)) 1) := fun σ ↦ ⟨σ, pow_one σ⟩
  rw [MonoidHom.range_eq_top_of_surjective _ h, InfiniteGalois.fixedField_bot]

/-- The primary subfield has degree the `p`-part of the full degree. -/
theorem finrank_primarySubfield (p : ℕ) :
    Module.finrank K (primarySubfield K L p) = ordProj[p] (Module.finrank K L) := by
  by_cases hdeg : ordProj[p] (Module.finrank K L) = 1
  · rw [primarySubfield_eq_bot_of_ordProj_eq_one hdeg, IntermediateField.finrank_bot, hdeg]
  have hp : p.Prime := by by_contra hn; exact hdeg (Nat.ordProj_of_not_prime _ _ hn)
  have : FiniteDimensional K L := by
    by_contra hn
    exact hdeg (by simp [Module.finrank_of_infinite_dimensional hn])
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (le_primarySubfield_iff hp).mp (le_refl (primarySubfield K L p))
  have hprimeTo : ¬ p ∣ Module.finrank (primarySubfield K L p) L := by
    rw [primarySubfield_def, IntermediateField.finrank_fixedField_eq_card]
    intro hd
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' p hd
    obtain ⟨τ, hτ⟩ := σ.property
    have hpow : (σ : Gal(L/K)) ^ ordCompl[p] (Module.finrank K L) = 1 := by
      rw [← hτ, powMonoidHom_apply, ← pow_mul, Nat.ordProj_mul_ordCompl_eq_self,
        ← IsGalois.card_aut_eq_finrank K L]
      exact pow_card_eq_one'
    rw [← Subgroup.orderOf_coe] at hσ
    exact Nat.not_dvd_ordCompl hp Module.finrank_pos.ne'
      (hσ ▸ orderOf_dvd_of_pow_eq_one hpow)
  rw [← Module.finrank_mul_finrank K (primarySubfield K L p) L,
    Nat.ordProj_mul p Module.finrank_pos.ne' Module.finrank_pos.ne']
  simp only [hn, Nat.ordProj_self_pow hp, Nat.factorization_eq_zero_of_not_dvd hprimeTo,
    pow_zero, mul_one]

end IsAbelianGalois
