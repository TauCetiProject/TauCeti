/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Orbit
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
import TauCeti.LinearAlgebra.RootSystem.Isomorphism
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Root counts of bases of a given Cartan type

Comparing any finite reduced crystallographic root pairing carrying a base of valid Cartan type `t`
with `t.simplyConnectedRootDatum` via `RootPairing.Base.indexEquivOfCartanMatrixEq` shows that it
has `t.numRoots` roots and `t.numRoots / 2` positive roots. Specializing Steinberg's orbit formula
`RootPairing.Base.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType` via
`TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every` also gives the exceptional root counts:
`E₆` (`72`/`36`), `E₇` (`126`/`63`), `E₈` (`240`/`120`), `F₄` (`48`/`24`), and `G₂` (`12`/`6`),
without assuming root spanning or `[P.IsIrreducible]`.

## Main results

* `TauCeti.HasCartanType.nonempty_equiv_fin_numRoots`: `Nonempty (ι ≃ Fin t.numRoots)`.
* `TauCeti.HasCartanType.natCard_eq_numRoots`,
  `TauCeti.HasCartanType.two_mul_ncard_posRoots_eq_numRoots`, and
  `TauCeti.HasCartanType.ncard_posRoots_eq_numRoots_div_two`.
* `RootPairing.Base.natCard_eq_numRoots_classifiedDynkinType`,
  `RootPairing.Base.two_mul_ncard_posRoots_eq_numRoots_classifiedDynkinType`, and
  `RootPairing.Base.ncard_posRoots_eq_numRoots_classifiedDynkinType_div_two`.
* `RootPairing.natCard_eq_of_hasCartanType_A` and `RootPairing.ncard_posRoots_of_hasCartanType_A`:
  specializations to type `Aₙ`, including the rank-zero case `n = 0`.
* `RootPairing.natCard_eq_of_hasCartanType_E6` / `ncard_posRoots_of_hasCartanType_E6`: `72`, `36`.
* `RootPairing.natCard_eq_of_hasCartanType_E7` / `ncard_posRoots_of_hasCartanType_E7`: `126`, `63`.
* `RootPairing.natCard_eq_of_hasCartanType_E8` / `ncard_posRoots_of_hasCartanType_E8`: `240`, `120`.
* `RootPairing.natCard_eq_of_hasCartanType_F4` / `ncard_posRoots_of_hasCartanType_F4`: `48`, `24`.
* `RootPairing.natCard_eq_of_hasCartanType_G2` / `ncard_posRoots_of_hasCartanType_G2`: `12`, `6`.

## References

* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2; Ch. VI, §1.5, §1.11,
  §4, and Plates V–IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§ 3.16–3.18.
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

/-- **A base of valid Cartan type `t` has `t.numRoots / 2` positive roots.** -/
theorem HasCartanType.ncard_posRoots_eq_numRoots_div_two {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) : (posRoots P b).ncard = t.numRoots / 2 := by
  rw [ncard_posRoots_eq_natCard_div_two, h.natCard_eq_numRoots ht]

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

/-- **An irreducible reduced crystallographic finite root system has `numRoots / 2` positive
roots.** -/
theorem ncard_posRoots_eq_numRoots_classifiedDynkinType_div_two (b : P.Base) :
    (posRoots P b).ncard = (classifiedDynkinType b).numRoots / 2 :=
  (hasCartanType_classifiedDynkinType b).ncard_posRoots_eq_numRoots_div_two
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

section ExceptionalRootCounts

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

private theorem natCard_eq_of_hasCartanType_aux {t : DynkinType} {h₀ n : ℕ}
    (ht : t.Valid) (hft : IsFiniteType t.cartanMatrix) (h : HasCartanType P b t)
    (hord : ∀ {l : List b.support}, l.Nodup → (∀ i, i ∈ l) → orderOf (wordProd P b l) = h₀)
    (hn : t.rank * h₀ = n) : Nat.card ι = n := by
  classical
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  rw [b.natCard_eq_card_support_mul_orderOf_wordProd_of_isFiniteType
      ((Matrix.ext he) ▸ hft.submatrix e.injective)
      (h.connected_diagramGraph_cartanMatrix ht).preconnected
      (Finset.nodup_toList Finset.univ) (fun _ ↦ by simp),
    h.card_support, hord (Finset.nodup_toList Finset.univ) (fun _ ↦ by simp), hn]

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
