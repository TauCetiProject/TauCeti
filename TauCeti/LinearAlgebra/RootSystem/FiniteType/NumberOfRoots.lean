/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Isomorphism
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Root counts of bases of a given Cartan type

Comparing any finite reduced crystallographic root pairing carrying a base of valid Cartan type `t`
with `t.simplyConnectedRootDatum` via `RootPairing.Base.indexEquivOfCartanMatrixEq` shows that it
has `t.numRoots` roots and twice its number of positive roots is `t.numRoots`.

## Main results

* `TauCeti.HasCartanType.nonempty_equiv_fin_numRoots`: `Nonempty (ι ≃ Fin t.numRoots)`.
* `TauCeti.HasCartanType.natCard_eq_numRoots` and
  `TauCeti.HasCartanType.two_mul_ncard_posRoots_eq_numRoots`.
* `RootPairing.Base.natCard_eq_numRoots_classifiedDynkinType` and
  `RootPairing.Base.two_mul_ncard_posRoots_eq_numRoots_classifiedDynkinType`.
* `RootPairing.natCard_eq_of_hasCartanType_A` and `RootPairing.ncard_posRoots_of_hasCartanType_A`:
  specializations to type `Aₙ`, including the rank-zero case `n = 0`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.5 and §4.
-/

public section

namespace TauCeti

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- **Any finite reduced crystallographic root pairing carrying a base of valid Cartan type `t` has
root index type in bijection with `Fin t.numRoots`.** -/
theorem HasCartanType.nonempty_equiv_fin_numRoots {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) : Nonempty (ι ≃ Fin t.numRoots) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨e₁, he₁⟩ := (hasCartanType_iff b t).mp h
  obtain ⟨e₂, he₂⟩ := (hasCartanType_iff (t.simplyConnectedBase ht) t).mp
    (t.hasCartanType_simplyConnectedRootDatum ht)
  exact ⟨b.indexEquivOfCartanMatrixEq (t.simplyConnectedBase ht) (e₁.trans e₂.symm) fun i j => by
    simp only [Equiv.trans_apply, he₂, he₁, Equiv.apply_symm_apply]⟩

/-- **A finite reduced crystallographic root pairing with a base of valid Cartan type `t` has
`t.numRoots` roots.** -/
theorem HasCartanType.natCard_eq_numRoots {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) : Nat.card ι = t.numRoots := by
  obtain ⟨e⟩ := h.nonempty_equiv_fin_numRoots ht; simpa using Nat.card_congr e

/-- **Twice the number of positive roots of a base of valid Cartan type `t` is `t.numRoots`.** -/
theorem HasCartanType.two_mul_ncard_posRoots_eq_numRoots {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) : 2 * (posRoots P b).ncard = t.numRoots :=
  (TauCeti.two_mul_ncard_posRoots P b).trans (h.natCard_eq_numRoots ht)

end HasCartanType

end TauCeti

namespace RootPairing.Base

open TauCeti

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]

/-- **The number of roots of an irreducible reduced crystallographic finite root system is the root
count of its classified Dynkin type.** -/
theorem natCard_eq_numRoots_classifiedDynkinType (b : P.Base) :
    Nat.card ι = (classifiedDynkinType b).numRoots :=
  (hasCartanType_classifiedDynkinType b).natCard_eq_numRoots (valid_classifiedDynkinType b)

/-- **Twice the number of positive roots of an irreducible reduced crystallographic finite root
system is the root count of its classified Dynkin type.** -/
theorem two_mul_ncard_posRoots_eq_numRoots_classifiedDynkinType (b : P.Base) :
    2 * (posRoots P b).ncard = (classifiedDynkinType b).numRoots :=
  (hasCartanType_classifiedDynkinType b).two_mul_ncard_posRoots_eq_numRoots
    (valid_classifiedDynkinType b)

end RootPairing.Base

namespace RootPairing

section TypeA

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base) {n : ℕ}

/-- A root pairing with a base of Cartan type `Aₙ` has `n (n + 1)` roots. -/
theorem natCard_eq_of_hasCartanType_A (h : TauCeti.HasCartanType P b (.A n)) :
    Nat.card ι = n * (n + 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsEmpty ι := ⟨fun i => P.ne_zero i
      (by simpa [Finset.card_eq_zero.mp h.card_support] using b.root_mem_span_int i)⟩
    simp
  · simpa [TauCeti.DynkinType.numRoots_A] using
      h.natCard_eq_numRoots (TauCeti.DynkinType.valid_A.mpr (Nat.pos_of_ne_zero hn))

/-- A base of Cartan type `Aₙ` has `n (n + 1) / 2` positive roots. -/
theorem ncard_posRoots_of_hasCartanType_A (h : TauCeti.HasCartanType P b (.A n)) :
    (TauCeti.posRoots P b).ncard = n * (n + 1) / 2 := by
  rw [TauCeti.ncard_posRoots_eq_natCard_div_two, P.natCard_eq_of_hasCartanType_A b h]

end TypeA

end RootPairing

end
