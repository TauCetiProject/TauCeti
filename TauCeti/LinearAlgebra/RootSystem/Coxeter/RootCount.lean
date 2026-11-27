/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Exponents

/-!
# Root counts and Coxeter numbers for root pairings of Cartan type

Supplements `TauCeti.LinearAlgebra.RootSystem.Coxeter.Number` with additional root-count,
exponent-sum, and fundamental-degree formulas (`∑ dᵢ = |Φ⁺| + r`, `|Φ| = r * h`, and
`h = |Φ| / r`) for bases of valid Cartan type and for classified finite irreducible reduced
crystallographic root systems.

## Main results

* `TauCeti.HasCartanType.card_posRootsFinset_eq_sum_exponents`,
  `sum_degrees_eq_ncard_posRoots_add_card_support`, `natCard_eq_card_support_mul_coxeterNumber`,
  and `coxeterNumber_eq_natCard_div_card_support`.
* `RootPairing.Base.card_posRootsFinset_eq_sum_exponents_classifiedDynkinType`,
  `sum_degrees_classifiedDynkinType_eq_ncard_posRoots_add_card_support`, and
  `coxeterNumber_classifiedDynkinType_eq_natCard_div_card_support` for classified finite
  irreducible root systems.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2, and Ch. VI, §1.11.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §§ 3.16--3.18.
-/

public section

namespace TauCeti

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Finite ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]

/-- Finset version of `TauCeti.HasCartanType.sum_exponents_eq_ncard_posRoots`. -/
theorem HasCartanType.card_posRootsFinset_eq_sum_exponents {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    (posRootsFinset P b).card = t.exponents.sum :=
  (card_posRootsFinset P b).trans (h.sum_exponents_eq_ncard_posRoots ht).symm

/-- **The sum of the fundamental degrees of `t` equals `|Φ⁺| + r`** for any base `b` of valid
Cartan type `t`. -/
theorem HasCartanType.sum_degrees_eq_ncard_posRoots_add_card_support {b : P.Base}
    {t : DynkinType} (h : HasCartanType P b t) (ht : t.Valid) :
    t.degrees.sum = (posRoots P b).ncard + b.support.card := by
  rw [t.sum_degrees, ← t.sum_exponents, h.sum_exponents_eq_ncard_posRoots ht, h.card_support]

/-- **For a base `b` of valid Cartan type `t`, `|Φ| = r * h`**, where `r = b.support.card` is the
rank and `h = t.coxeterNumber` is the Coxeter number. -/
theorem HasCartanType.natCard_eq_card_support_mul_coxeterNumber {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    Nat.card ι = b.support.card * t.coxeterNumber := by
  rw [h.natCard_eq_numRoots ht, h.card_support, t.numRoots_eq_rank_mul_coxeterNumber]

/-- **For a base `b` of valid Cartan type `t`, `h = |Φ| / r`**, where `r = b.support.card`. -/
theorem HasCartanType.coxeterNumber_eq_natCard_div_card_support {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    t.coxeterNumber = Nat.card ι / b.support.card := by
  have hpos : 0 < b.support.card := h.card_support ▸ DynkinType.rank_pos ht
  rw [h.natCard_eq_card_support_mul_coxeterNumber ht, Nat.mul_div_right _ hpos]

end HasCartanType

end TauCeti

/-! ### Invariants of classified finite irreducible root systems -/

namespace RootPairing.Base

section Classified

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Finite ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

open TauCeti

/-- Finset version of `RootPairing.Base.sum_exponents_eq_ncard_posRoots`. -/
theorem card_posRootsFinset_eq_sum_exponents_classifiedDynkinType (b : P.Base) :
    (posRootsFinset P b).card = (classifiedDynkinType b).exponents.sum :=
  (hasCartanType_classifiedDynkinType b).card_posRootsFinset_eq_sum_exponents
    (valid_classifiedDynkinType b)

/-- The sum of fundamental degrees of `classifiedDynkinType b` equals `|Φ⁺| + r`. -/
theorem sum_degrees_classifiedDynkinType_eq_ncard_posRoots_add_card_support (b : P.Base) :
    (classifiedDynkinType b).degrees.sum = (posRoots P b).ncard + b.support.card :=
  (hasCartanType_classifiedDynkinType b).sum_degrees_eq_ncard_posRoots_add_card_support
    (valid_classifiedDynkinType b)

/-- The Coxeter number of `classifiedDynkinType b` is `|Φ| / r`. -/
theorem coxeterNumber_classifiedDynkinType_eq_natCard_div_card_support (b : P.Base) :
    (classifiedDynkinType b).coxeterNumber = Nat.card ι / b.support.card :=
  (hasCartanType_classifiedDynkinType b).coxeterNumber_eq_natCard_div_card_support
    (valid_classifiedDynkinType b)

end Classified

end RootPairing.Base
