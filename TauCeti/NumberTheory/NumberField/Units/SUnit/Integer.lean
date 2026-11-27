/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.SUnit.FundamentalSystem
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit.Torsion

import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.NumberTheory.NumberField.Units.Dirichlet

/-!
# The unit group of a ring of `S`-integers

Let `F` be a number field with `r₁` real and `r₂` complex places, `S` a finite set of finite
places of `F`, and `A = 𝒪_{F,S}` the ring of `S`-integers `S.integer F`. This file describes the
unit group `Aˣ` as an abstract group, on the carrier `(S.integer F)ˣ` of the ring itself rather
than on the subgroup `S.unit F` of `Fˣ` where Dirichlet's `S`-unit theorem is proved.

* Its torsion subgroup is the group `μ(F)` of roots of unity of `F`: inverting primes creates no
  new roots of unity, so it is cyclic of order `NumberField.Units.torsionOrder F`, the same for
  every `S`.
* Its rank is `r₁ + r₂ + |S| - 1`.
* Every unit is uniquely a root of unity times a product of integral powers of a fixed
  fundamental system, transported from `TauCeti.NumberField.SUnit.fundSystem`.
* Consequently `Aˣ` has an element of infinite order, equivalently positive rank, exactly when
  `r₁ + r₂ + |S| ≥ 2`. This includes `S = ∅`, where it says that `𝒪_F` has a unit of infinite
  order unless `F` is `ℚ` or imaginary quadratic.

The positive-rank criterion is the hypothesis under which Serre's theorem on the congruence
subgroup problem for `SL₂(A)` holds: a unit of infinite order is what produces congruence levels
inside normal subgroups of `SL₂(A)`.

## Main results

* `TauCeti.NumberField.SUnit.finrank_units_integer`: `rank Aˣ = rank 𝒪_Fˣ + |S|`.
* `TauCeti.NumberField.SUnit.finrank_units_integer_add_one`: `rank Aˣ + 1 = r₁ + r₂ + |S|`.
* `TauCeti.NumberField.SUnit.natCard_torsion_units_integer`: the torsion of `Aˣ` has order
  `torsionOrder F`.
* `TauCeti.NumberField.SUnit.torsion_units_integer_eq_rootsOfUnity`: the torsion of `Aˣ` is the
  group of `torsionOrder F`-th roots of unity of `A`.
* `TauCeti.NumberField.SUnit.exist_unique_eq_mul_prod_units_integer`: the fundamental-system
  decomposition of a unit of `A`.
* `TauCeti.NumberField.SUnit.exists_not_isOfFinOrder_units_integer_iff`: `Aˣ` has an element of
  infinite order if and only if `r₁ + r₂ + |S| ≥ 2`.

## References

* J.-P. Serre, *Le problème des groupes de congruence pour SL₂*, Ann. of Math. **92** (1970),
  §1.1.
* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS **33** (1967), Appendix, (A.4).
* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 11.6.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (RingOfIntegers K)))

/-! ### Torsion -/

/-- **The torsion of the units of the `S`-integers has order `torsionOrder K`**, the number of
roots of unity of `K`, for every set `S` of primes. -/
theorem natCard_torsion_units_integer :
    Nat.card (CommGroup.torsion (S.integer K)ˣ) = Units.torsionOrder K := by
  rw [Nat.card_congr (S.unitsIntegerTorsionEquiv K).toEquiv, Units.torsionOrder, Units.torsion]

/-- **The torsion of the units of the `S`-integers is the group of roots of unity**: it consists
of the `torsionOrder K`-th roots of unity of `S.integer K`. -/
theorem torsion_units_integer_eq_rootsOfUnity :
    CommGroup.torsion (S.integer K)ˣ = rootsOfUnity (Units.torsionOrder K) (S.integer K) := by
  ext u
  rw [mem_rootsOfUnity]
  refine ⟨fun hu ↦ ?_, fun hu ↦ isOfFinOrder_iff_pow_eq_one.2
    ⟨_, Units.torsionOrder_pos K, hu⟩⟩
  have h := pow_card_eq_one' (G := CommGroup.torsion (S.integer K)ˣ) (x := ⟨u, hu⟩)
  rw [natCard_torsion_units_integer] at h
  exact congrArg Subtype.val h

/-! ### Rank -/

variable [Finite S]

/-- **The rank of the units of the `S`-integers** is the rank of the units of `𝒪_K` plus the
number of primes in `S`. -/
theorem finrank_units_integer :
    Module.finrank ℤ (Additive (S.integer K)ˣ) = Units.rank K + Nat.card S :=
  ((MulEquiv.toAdditive (S.unitEquivUnitsInteger K)).toIntLinearEquiv.finrank_eq).symm.trans
    (finrank_sUnits_numberField K S)

/-- **The rank of the units of the `S`-integers** is `r₁ + r₂ + |S| - 1`, where `r₁` and `r₂`
are the numbers of real and complex places of `K`. -/
theorem finrank_units_integer_add_one :
    Module.finrank ℤ (Additive (S.integer K)ˣ) + 1 =
      InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K + Nat.card S := by
  rw [finrank_units_integer, add_right_comm, Units.rank_add_one K,
    Nat.card_eq_fintype_card, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

/-! ### The fundamental-system decomposition -/

/-- **The fundamental-system decomposition of the units of the `S`-integers.** Every unit of
`S.integer K` is uniquely a torsion unit times a product of integral powers of the images of the
fundamental `S`-units `fundSystem S`. -/
theorem exist_unique_eq_mul_prod_units_integer (u : (S.integer K)ˣ) :
    ∃! ζe : CommGroup.torsion (S.integer K)ˣ × (Fin (Units.rank K + Nat.card S) → ℤ),
      u = ζe.1 * ∏ i, S.unitEquivUnitsInteger K (fundSystem S i) ^ ζe.2 i := by
  set e := S.unitEquivUnitsInteger K
  -- transport along `e` the decomposition of the corresponding `S`-unit
  obtain ⟨⟨ζ, f⟩, hx, huniq⟩ := exist_unique_eq_mul_prod S (e.symm u)
  have hζ : e ζ ∈ CommGroup.torsion (S.integer K)ˣ := e.toMonoidHom.isOfFinOrder ζ.property
  refine ⟨⟨⟨e ζ, hζ⟩, f⟩, ?_, ?_⟩
  · simpa [map_mul, map_prod, map_zpow] using congrArg e hx
  · rintro ⟨⟨ζ', hζ'⟩, f'⟩ h
    have h' : e.symm u = e.symm ζ' * ∏ i, fundSystem S i ^ f' i := by
      simp [h, map_mul, map_prod, map_zpow]
    have hsymm : e.symm ζ' ∈ CommGroup.torsion (S.unit K) := e.symm.toMonoidHom.isOfFinOrder hζ'
    obtain ⟨hζeq, rfl⟩ := Prod.mk.inj (huniq ⟨⟨e.symm ζ', hsymm⟩, f'⟩ h')
    simp [← congrArg Subtype.val hζeq]

/-! ### Units of infinite order -/

/-- **The units of the `S`-integers have positive rank exactly when `r₁ + r₂ + |S| ≥ 2`.** -/
theorem finrank_units_integer_pos_iff :
    0 < Module.finrank ℤ (Additive (S.integer K)ˣ) ↔
      2 ≤ Nat.card (InfinitePlace K) + Nat.card S := by
  rw [finrank_units_integer, ← Units.rank_add_one K]
  omega

/-- **The units of the `S`-integers have an element of infinite order exactly when
`r₁ + r₂ + |S| ≥ 2`**, where `r₁ + r₂` is the number of infinite places of `K`. Equivalently,
by `finrank_units_integer_add_one`, exactly when they have positive rank. -/
theorem exists_not_isOfFinOrder_units_integer_iff :
    (∃ u : (S.integer K)ˣ, ¬ IsOfFinOrder u) ↔
      2 ≤ Nat.card (InfinitePlace K) + Nat.card S := by
  rw [← finrank_units_integer_pos_iff, finrank_units_integer]
  constructor
  · -- with no fundamental units, every unit is a torsion unit
    rintro ⟨u, hu⟩
    by_contra! h0
    have : IsEmpty (Fin (Units.rank K + Nat.card S)) := ⟨fun i ↦ by have := i.isLt; omega⟩
    obtain ⟨⟨ζ, f⟩, hζ, -⟩ := exist_unique_eq_mul_prod_units_integer S u
    rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hζ
    exact hu (hζ ▸ ζ.property)
  · -- a fundamental unit has infinite order: its class modulo torsion is a basis vector
    intro h
    refine ⟨S.unitEquivUnitsInteger K (fundSystem S ⟨0, h⟩), fun hfin ↦ ?_⟩
    have hmem : fundSystem S ⟨0, h⟩ ∈ CommGroup.torsion (S.unit K) := by
      simpa [CommGroup.mem_torsion] using
        (S.unitEquivUnitsInteger K).symm.toMonoidHom.isOfFinOrder hfin
    refine (basisModTorsion S).ne_zero ⟨0, h⟩ ?_
    rw [← fundSystem_mk, Submodule.Quotient.mk_eq_zero]
    exact ofMul_mem_torsion_int_iff.2 hmem

end TauCeti.NumberField.SUnit
