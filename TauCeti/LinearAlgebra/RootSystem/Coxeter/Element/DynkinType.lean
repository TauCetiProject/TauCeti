/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Datum

/-!
# Coxeter elements of the exceptional Dynkin types, stated with `TauCeti.HasCartanType`

For a root system with a base of Dynkin type `t ∈ {E₆, E₇, E₈, F₄, G₂}`, the product `c` of the
simple reflections taken in the order of the Bourbaki numbering has order the Coxeter number `h` of
`t`, and its matrix on the simple roots has characteristic polynomial the product of the `Φ_d` over
the orders `d` of the eigenvalues `exp (2πi e / h)`, `e` running over the exponents:

| type | `h` | characteristic polynomial |
|---|---|---|
| `E₆` | 12 | `Φ₁₂ Φ₃` |
| `E₇` | 18 | `Φ₁₈ Φ₂` |
| `E₈` | 30 | `Φ₃₀` |
| `F₄` | 12 | `Φ₁₂` |
| `G₂` | 6 | `Φ₆` |

The statements are phrased with `TauCeti.HasCartanType`, so they apply to any base that the
classification has matched to a type. TauCeti's `G₂` Cartan matrix is the transpose of Mathlib's
`CartanMatrix.G₂`. `TauCeti.Coxeter.coxeterElement_e8SimplyConnectedRootDatum` instantiates the `E₈`
statement on TauCeti's pinned simply connected root datum of type `E₈`, so the hypotheses are
satisfiable.
-/

@[expose] public section

open Matrix Polynomial RootPairing TauCeti

namespace TauCeti.Coxeter

theorem orderOf_coxG2_transpose : orderOf (coxeterElement CartanMatrix.G₂.transpose) = 6 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem charpoly_coxG2_transpose :
    (coxeterElement CartanMatrix.G₂.transpose).charpoly = cyclotomic 6 ℤ := by
  refine charpoly_eq_cyclotomic _ (by norm_num) (by decide) ?_
  simp only [cyclotomic_six_int, map_add, map_sub, map_pow, aeval_X, map_one]
  decide +kernel

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [CharZero R]
  [Finite ι] [IsDomain R]

/-- A base of Dynkin type `t` has a Coxeter element whose order and characteristic polynomial
(of its matrix on the simple roots) are those of `coxeterElement t.cartanMatrix`. -/
theorem exists_coxeterElement_of_hasCartanType {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) :
    ∃ e : b.support ≃ Fin t.rank,
      orderOf (wordProd P b ((List.finRange t.rank).map e.symm)) =
          orderOf (coxeterElement t.cartanMatrix) ∧
        ∀ W, ActsBy b (wordProd P b ((List.finRange t.rank).map e.symm)) W →
          W.charpoly = (coxeterElement t.cartanMatrix).charpoly := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).1 h
  exact ⟨e, orderOf_wordProd_of_cartanMatrix_eq b _ e he,
    fun _ hW => charpoly_of_actsBy_wordProd b _ e he hW⟩

/-- **Coxeter element of `E₈`**: order 30, characteristic polynomial `Φ₃₀`. -/
theorem exists_coxeterElement_E8 {b : P.Base} (h : HasCartanType P b .E8) :
    ∃ e : b.support ≃ Fin 8,
      orderOf (wordProd P b ((List.finRange 8).map e.symm)) = 30 ∧
        ∀ W, ActsBy b (wordProd P b ((List.finRange 8).map e.symm)) W →
          W.charpoly = cyclotomic 30 ℤ := by
  obtain ⟨e, ho, hc⟩ := exists_coxeterElement_of_hasCartanType h
  refine ⟨e, ho.trans ?_, fun W hW => (hc W hW).trans ?_⟩
  · rw [DynkinType.cartanMatrix_E8]; exact orderOf_coxE8
  · rw [DynkinType.cartanMatrix_E8]; exact charpoly_coxE8

/-- **Coxeter element of `E₇`**: order 18, characteristic polynomial `Φ₁₈ Φ₂`. -/
theorem exists_coxeterElement_E7 {b : P.Base} (h : HasCartanType P b .E7) :
    ∃ e : b.support ≃ Fin 7,
      orderOf (wordProd P b ((List.finRange 7).map e.symm)) = 18 ∧
        ∀ W, ActsBy b (wordProd P b ((List.finRange 7).map e.symm)) W →
          W.charpoly = cyclotomic 18 ℤ * cyclotomic 2 ℤ := by
  obtain ⟨e, ho, hc⟩ := exists_coxeterElement_of_hasCartanType h
  refine ⟨e, ho.trans ?_, fun W hW => (hc W hW).trans ?_⟩
  · rw [DynkinType.cartanMatrix_E7]; exact orderOf_coxE7
  · rw [DynkinType.cartanMatrix_E7]; exact charpoly_coxE7

/-- **Coxeter element of `E₆`**: order 12, characteristic polynomial `Φ₁₂ Φ₃`. -/
theorem exists_coxeterElement_E6 {b : P.Base} (h : HasCartanType P b .E6) :
    ∃ e : b.support ≃ Fin 6,
      orderOf (wordProd P b ((List.finRange 6).map e.symm)) = 12 ∧
        ∀ W, ActsBy b (wordProd P b ((List.finRange 6).map e.symm)) W →
          W.charpoly = cyclotomic 12 ℤ * cyclotomic 3 ℤ := by
  obtain ⟨e, ho, hc⟩ := exists_coxeterElement_of_hasCartanType h
  refine ⟨e, ho.trans ?_, fun W hW => (hc W hW).trans ?_⟩
  · rw [DynkinType.cartanMatrix_E6]; exact orderOf_coxE6
  · rw [DynkinType.cartanMatrix_E6]; exact charpoly_coxE6

/-- **Coxeter element of `F₄`**: order 12, characteristic polynomial `Φ₁₂`. -/
theorem exists_coxeterElement_F4 {b : P.Base} (h : HasCartanType P b .F4) :
    ∃ e : b.support ≃ Fin 4,
      orderOf (wordProd P b ((List.finRange 4).map e.symm)) = 12 ∧
        ∀ W, ActsBy b (wordProd P b ((List.finRange 4).map e.symm)) W →
          W.charpoly = cyclotomic 12 ℤ := by
  obtain ⟨e, ho, hc⟩ := exists_coxeterElement_of_hasCartanType h
  refine ⟨e, ho.trans ?_, fun W hW => (hc W hW).trans ?_⟩
  · rw [DynkinType.cartanMatrix_F4]; exact orderOf_coxF4
  · rw [DynkinType.cartanMatrix_F4]; exact charpoly_coxF4

/-- **Coxeter element of `G₂`**: order 6, characteristic polynomial `Φ₆`. -/
theorem exists_coxeterElement_G2 {b : P.Base} (h : HasCartanType P b .G2) :
    ∃ e : b.support ≃ Fin 2,
      orderOf (wordProd P b ((List.finRange 2).map e.symm)) = 6 ∧
        ∀ W, ActsBy b (wordProd P b ((List.finRange 2).map e.symm)) W →
          W.charpoly = cyclotomic 6 ℤ := by
  obtain ⟨e, ho, hc⟩ := exists_coxeterElement_of_hasCartanType h
  refine ⟨e, ho.trans ?_, fun W hW => (hc W hW).trans ?_⟩
  · rw [DynkinType.cartanMatrix_G2]; exact orderOf_coxG2_transpose
  · rw [DynkinType.cartanMatrix_G2]; exact charpoly_coxG2_transpose

/-- Non-vacuity: on TauCeti's pinned simply connected root datum of type `E₈`, a Coxeter element
of the Weyl group has order 30 and characteristic polynomial `Φ₃₀`. -/
theorem coxeterElement_e8SimplyConnectedRootDatum :
    ∃ e : DynkinType.e8SimplyConnectedBase.support ≃ Fin 8,
      orderOf (wordProd DynkinType.e8SimplyConnectedRootDatum DynkinType.e8SimplyConnectedBase
          ((List.finRange 8).map e.symm)) = 30 ∧
        ∀ W, ActsBy DynkinType.e8SimplyConnectedBase
            (wordProd DynkinType.e8SimplyConnectedRootDatum DynkinType.e8SimplyConnectedBase
              ((List.finRange 8).map e.symm)) W →
          W.charpoly = cyclotomic 30 ℤ :=
  exists_coxeterElement_E8 DynkinType.hasCartanType_e8SimplyConnectedRootDatum

end TauCeti.Coxeter

end
