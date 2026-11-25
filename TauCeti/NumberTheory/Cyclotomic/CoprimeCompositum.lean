/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.RingTheory.Cyclotomic.ComplexField

/-!
# Cyclotomic fields of coprime orders

Let `F₁` and `F₂` be an `m`-th and an `n`-th cyclotomic extension of `ℚ` inside a field `K` of
characteristic zero, with `m` and `n` coprime. Their compositum `F₁ ⊔ F₂` is an `mn`-th
cyclotomic extension, of degree `φ(mn) = φ(m) φ(n)`, so `F₁` and `F₂` are linearly disjoint and
`F₁ ⊓ F₂ = ℚ`. Every pair of automorphisms of `F₁` and `F₂` extends to a unique automorphism of
the compositum: the restriction map `Gal(F₁ ⊔ F₂ / ℚ) → Gal(F₁/ℚ) × Gal(F₂/ℚ)` is injective, and
both sides have `φ(m) φ(n)` elements (Glauberman 1968, Lemma 1, p. 1469).

For the cyclotomic fields `ℚ(ζ_m) = TauCeti.Cyclotomic.complexField m` of `ℂ` this reads
`ℚ(ζ_m) ⊓ ℚ(ζ_n) = ℚ` and `ℚ(ζ_m) ⊔ ℚ(ζ_n) = ℚ(ζ_{mn})`. Coprimality is needed:
`ℚ(ζ₄) ⊓ ℚ(ζ₈) = ℚ(ζ₄) = ℚ(i)`.

## Main results

* `IsCyclotomicExtension.linearDisjoint_of_coprime`, `IsCyclotomicExtension.inf_eq_bot_of_coprime`:
  cyclotomic fields of coprime orders are linearly disjoint and meet in `ℚ`.
* `IsCyclotomicExtension.isCyclotomicExtension_sup_of_coprime`: their compositum is cyclotomic of
  order `mn`.
* `IsCyclotomicExtension.restrictNormalHomSupProd_bijective_of_coprime`: automorphisms of the two
  factors extend uniquely to the compositum.
* `TauCeti.Cyclotomic.complexField_inf_eq_bot`, `TauCeti.Cyclotomic.complexField_sup_eq`: the
  statements for `ℚ(ζ_m) ⊆ ℂ`.

## References

* G. Glauberman, *Correspondences of characters for relatively prime operator groups*,
  Canad. J. Math. 20 (1968), Lemma 1, p. 1469.
-/

public section

open IntermediateField Module

namespace IsCyclotomicExtension

variable {K : Type*} [Field K] [CharZero K] {F₁ F₂ : IntermediateField ℚ K} {m n : ℕ} [NeZero m]
  [NeZero n] [IsCyclotomicExtension {m} ℚ F₁] [IsCyclotomicExtension {n} ℚ F₂]

/-- The compositum of an `m`-th and an `n`-th cyclotomic extension of `ℚ`, for coprime `m` and
`n`, is an `mn`-th cyclotomic extension. -/
theorem isCyclotomicExtension_sup_of_coprime (h : m.Coprime n) :
    IsCyclotomicExtension {m * n} ℚ (F₁ ⊔ F₂ : IntermediateField ℚ K) := by
  rw [← h.lcm_eq_mul]
  exact isCyclotomicExtension_lcm_sup ℚ K m n F₁ F₂

/-- **Cyclotomic fields of coprime orders are linearly disjoint**: the compositum has degree
`φ(mn) = φ(m) φ(n)`. -/
theorem linearDisjoint_of_coprime (h : m.Coprime n) : F₁.LinearDisjoint F₂ := by
  have := isCyclotomicExtension_sup_of_coprime (F₁ := F₁) (F₂ := F₂) h
  have : FiniteDimensional ℚ F₁ := finite_of_singleton m ℚ F₁
  have : FiniteDimensional ℚ F₂ := finite_of_singleton n ℚ F₂
  refine LinearDisjoint.of_finrank_sup ?_
  rw [Rat.finrank (m * n), Rat.finrank m, Rat.finrank n, Nat.totient_mul h]

/-- **Cyclotomic fields of coprime orders meet in `ℚ`** (Glauberman 1968, Lemma 1, p. 1469). -/
theorem inf_eq_bot_of_coprime (h : m.Coprime n) : F₁ ⊓ F₂ = ⊥ :=
  (linearDisjoint_of_coprime h).inf_eq_bot

/-- **Automorphisms of cyclotomic fields of coprime orders extend to the compositum.** The
restriction map `Gal(F₁ ⊔ F₂ / ℚ) → Gal(F₁/ℚ) × Gal(F₂/ℚ)` is bijective, so every pair of
automorphisms of `F₁` and `F₂` is the pair of restrictions of exactly one automorphism of
`F₁ ⊔ F₂` (Glauberman 1968, Lemma 1, p. 1469). -/
theorem restrictNormalHomSupProd_bijective_of_coprime (h : m.Coprime n) :
    haveI : IsGalois ℚ F₁ := isGalois {m} ℚ F₁
    haveI : IsGalois ℚ F₂ := isGalois {n} ℚ F₂
    Function.Bijective (restrictNormalHomSupProd F₁ F₂) := by
  have : IsGalois ℚ F₁ := isGalois {m} ℚ F₁
  have : IsGalois ℚ F₂ := isGalois {n} ℚ F₂
  have := isCyclotomicExtension_sup_of_coprime (F₁ := F₁) (F₂ := F₂) h
  have : IsGalois ℚ (F₁ ⊔ F₂ : IntermediateField ℚ K) := isGalois {m * n} ℚ _
  have : FiniteDimensional ℚ F₁ := finite_of_singleton m ℚ F₁
  have : FiniteDimensional ℚ F₂ := finite_of_singleton n ℚ F₂
  have : FiniteDimensional ℚ (F₁ ⊔ F₂ : IntermediateField ℚ K) :=
    finite_of_singleton (m * n) ℚ _
  refine (restrictNormalHomSupProd_injective F₁ F₂).bijective_of_nat_card_le ?_
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    IsGalois.card_aut_eq_finrank, (linearDisjoint_of_coprime h).finrank_sup]

end IsCyclotomicExtension

namespace TauCeti.Cyclotomic

variable {m n : ℕ}

/-- `ℚ(ζ_m) ⊓ ℚ(ζ_n) = ℚ` in `ℂ` for coprime `m` and `n`. -/
theorem complexField_inf_eq_bot [NeZero m] [NeZero n] (h : m.Coprime n) :
    complexField m ⊓ complexField n = ⊥ :=
  IsCyclotomicExtension.inf_eq_bot_of_coprime h

/-- `ℚ(ζ_m) ⊔ ℚ(ζ_n) = ℚ(ζ_{mn})` in `ℂ` for coprime `m` and `n`. -/
theorem complexField_sup_eq [NeZero m] [NeZero n] (h : m.Coprime n) :
    complexField m ⊔ complexField n = complexField (m * n) := by
  have := IsCyclotomicExtension.isCyclotomicExtension_sup_of_coprime
    (F₁ := complexField m) (F₂ := complexField n) h
  exact IntermediateField.isCyclotomicExtension_eq (S := {m * n}) (K := ℚ) (L := ℂ) _ _

/-- For `m ∣ n`, `ℚ(ζ_m) ≤ ℚ(ζ_n)` in `ℂ`. -/
theorem complexField_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    complexField m ≤ complexField n := by
  obtain ⟨k, rfl⟩ := h
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  rw [complexField_def, adjoin_simple_le_iff, mul_comm, ← complexRoot_mul_pow hk]
  exact pow_mem (complexRoot_mem_complexField _) k

end TauCeti.Cyclotomic
