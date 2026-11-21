/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Orbit
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible

/-!
# Root counts for the exceptional Cartan types

For any finite, reduced, crystallographic root pairing `P` over a commutative domain of
characteristic zero with a base `b` of exceptional Cartan type `E₆`, `E₇`, `E₈`, `F₄`, or `G₂`,
we determine the total number of roots `Nat.card ι` and the number of positive roots
`(posRoots P b).ncard`, without assuming root spanning or `[P.IsIrreducible]`:

| type | rank `r` | Coxeter number `h` | `|Φ| = r · h` | `|Φ⁺| = r · h / 2` |
|---|---|---|---|---|
| `E₆` | 6 | 12 | 72 | 36 |
| `E₇` | 7 | 18 | 126 | 63 |
| `E₈` | 8 | 30 | 240 | 120 |
| `F₄` | 4 | 12 | 48 | 24 |
| `G₂` | 2 | 6 | 12 | 6 |

These counts specialize Bourbaki's formula `|Φ| = r · h`
(`RootPairing.Base.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType`) using the
exceptional Coxeter numbers proved in `TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every`,
verifying the exceptional values recorded by `TauCeti.DynkinType.numRoots` for any abstract root
pairing matching `TauCeti.HasCartanType`.

## Main results

* `RootPairing.natCard_eq_of_hasCartanType_E6`, `RootPairing.ncard_posRoots_of_hasCartanType_E6`:
  type `E₆` has `72` roots and `36` positive roots.
* `RootPairing.natCard_eq_of_hasCartanType_E7`, `RootPairing.ncard_posRoots_of_hasCartanType_E7`:
  type `E₇` has `126` roots and `63` positive roots.
* `RootPairing.natCard_eq_of_hasCartanType_E8`, `RootPairing.ncard_posRoots_of_hasCartanType_E8`:
  type `E₈` has `240` roots and `120` positive roots.
* `RootPairing.natCard_eq_of_hasCartanType_F4`, `RootPairing.ncard_posRoots_of_hasCartanType_F4`:
  type `F₄` has `48` roots and `24` positive roots.
* `RootPairing.natCard_eq_of_hasCartanType_G2`, `RootPairing.ncard_posRoots_of_hasCartanType_G2`:
  type `G₂` has `12` roots and `6` positive roots.

## References

* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2; Ch. VI, §1, no. 11;
  and Plates V–IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.18.
-/

public section

open TauCeti

namespace RootPairing

section ExceptionalRootCounts

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

private theorem natCard_eq_of_hasCartanType_aux {t : DynkinType} {h₀ n : ℕ}
    (ht : t.Valid) (hft : IsFiniteType t.cartanMatrix) (h : HasCartanType P b t)
    (hord : ∀ {l : List b.support}, l.Nodup → (∀ i, i ∈ l) → orderOf (wordProd P b l) = h₀)
    (hn : t.rank * h₀ = n) : Nat.card ι = n := by
  classical
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  have hnd := Finset.nodup_toList (Finset.univ : Finset b.support)
  have hall : ∀ i, i ∈ (Finset.univ : Finset b.support).toList := fun _ ↦ by simp
  rw [b.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType
      ((Matrix.ext he) ▸ hft.submatrix e.injective)
      (h.connected_diagramGraph_cartanMatrix ht).preconnected hnd hall,
    h.card_support, hord hnd hall, hn]

/-- **A root pairing with a base of Cartan type `E₆` has `72` roots.** -/
theorem natCard_eq_of_hasCartanType_E6 (h : HasCartanType P b .E6) : Nat.card ι = 72 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_E6 DynkinType.isFiniteType_cartanMatrix_E6 h
    (Coxeter.orderOf_wordProd_of_hasCartanType_E6 h) rfl

/-- **A base of Cartan type `E₆` has `36` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_E6 (h : HasCartanType P b .E6) :
    (posRoots P b).ncard = 36 :=
  (ncard_posRoots_eq_natCard_div_two P b).trans (by rw [P.natCard_eq_of_hasCartanType_E6 b h])

/-- **A root pairing with a base of Cartan type `E₇` has `126` roots.** -/
theorem natCard_eq_of_hasCartanType_E7 (h : HasCartanType P b .E7) : Nat.card ι = 126 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_E7 DynkinType.isFiniteType_cartanMatrix_E7 h
    (Coxeter.orderOf_wordProd_of_hasCartanType_E7 h) rfl

/-- **A base of Cartan type `E₇` has `63` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_E7 (h : HasCartanType P b .E7) :
    (posRoots P b).ncard = 63 :=
  (ncard_posRoots_eq_natCard_div_two P b).trans (by rw [P.natCard_eq_of_hasCartanType_E7 b h])

/-- **A root pairing with a base of Cartan type `E₈` has `240` roots.** -/
theorem natCard_eq_of_hasCartanType_E8 (h : HasCartanType P b .E8) : Nat.card ι = 240 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_E8 DynkinType.isFiniteType_cartanMatrix_E8 h
    (Coxeter.orderOf_wordProd_of_hasCartanType_E8 h) rfl

/-- **A base of Cartan type `E₈` has `120` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_E8 (h : HasCartanType P b .E8) :
    (posRoots P b).ncard = 120 :=
  (ncard_posRoots_eq_natCard_div_two P b).trans (by rw [P.natCard_eq_of_hasCartanType_E8 b h])

/-- **A root pairing with a base of Cartan type `F₄` has `48` roots.** -/
theorem natCard_eq_of_hasCartanType_F4 (h : HasCartanType P b .F4) : Nat.card ι = 48 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_F4 DynkinType.isFiniteType_cartanMatrix_F4 h
    (Coxeter.orderOf_wordProd_of_hasCartanType_F4 h) rfl

/-- **A base of Cartan type `F₄` has `24` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_F4 (h : HasCartanType P b .F4) :
    (posRoots P b).ncard = 24 :=
  (ncard_posRoots_eq_natCard_div_two P b).trans (by rw [P.natCard_eq_of_hasCartanType_F4 b h])

/-- **A root pairing with a base of Cartan type `G₂` has `12` roots.** -/
theorem natCard_eq_of_hasCartanType_G2 (h : HasCartanType P b .G2) : Nat.card ι = 12 :=
  P.natCard_eq_of_hasCartanType_aux b DynkinType.valid_G2 DynkinType.isFiniteType_cartanMatrix_G2 h
    (Coxeter.orderOf_wordProd_of_hasCartanType_G2 h) rfl

/-- **A base of Cartan type `G₂` has `6` positive roots.** -/
theorem ncard_posRoots_of_hasCartanType_G2 (h : HasCartanType P b .G2) :
    (posRoots P b).ncard = 6 :=
  (ncard_posRoots_eq_natCard_div_two P b).trans (by rw [P.natCard_eq_of_hasCartanType_G2 b h])

end ExceptionalRootCounts

end RootPairing

end
