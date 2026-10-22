/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import TauCeti.Data.Matrix.Block
public import TauCeti.RingTheory.CyclicCohomology.Matrix

/-!
# The even pairing of cyclic cohomology with idempotents

Let `A` be a unital algebra over a field `R` of characteristic zero and `M` an `R`-module. For an
idempotent `e` of `A` and a cyclic `M`-valued cocycle `φ` of degree `2m`, the value
`(m!)⁻¹ φ(e, …, e)` depends only on the cyclic cohomology class of `φ`. This file constructs the
resulting linear map `HC²ᵐ(A; M) → M`. Composed with matrix extension
`HC²ᵐ(A; M) → HC²ᵐ(Matrix ι ι A; M)`, it gives Connes' even pairing
`⟨[e], [φ]⟩ = (m!)⁻¹ (φ#Tr)(e, …, e)` of idempotent matrices with cyclic cohomology, the pairing
from which the Chern character of `K₀` is built.

The pairing descends to cohomology because every Hochschild face fixes the constant tuple
`(e, …, e)`: if `φ = bψ` with `ψ` cyclic of odd degree, then `φ(e, …, e) = ψ(e, …, e)`, while
cyclicity in odd degree forces `ψ(e, …, e) = -ψ(e, …, e)`.

## Main definitions

* `TauCeti.cyclicCohomology.evenPairing`: the pairing `HC²ᵐ(A; M) → M` with an idempotent.

## Main results

* `TauCeti.apply_const_eq_zero_of_mem_cyclicCoboundaries`: when `2` is invertible, an
  even-degree cyclic coboundary vanishes on constant idempotent tuples.
* `TauCeti.cyclicCohomology.evenPairing_mk`: the pairing evaluated on the class of a cocycle.
* `TauCeti.cyclicCohomology.evenPairing_matrixExtension_mk`: Connes' formula
  `⟨[e], [φ]⟩ = (m!)⁻¹ (φ#Tr)(e, …, e)` for an idempotent matrix `e`.
* `TauCeti.cyclicCohomology.evenPairing_fromBlocks_matrixExtension`: the pairing is additive on
  direct sums, `⟨[e ⊕ f], [φ]⟩ = ⟨[e], [φ]⟩ + ⟨[f], [φ]⟩`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §3.
* J.-L. Loday, *Cyclic Homology*, §8.3.
-/

public section

noncomputable section

namespace TauCeti

open scoped Nat

section Coboundary

variable {R A M : Type*} [CommRing R] [Invertible (2 : R)] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- When `2` is invertible, a cyclic coboundary of even degree vanishes on a constant tuple with
idempotent entry. -/
theorem apply_const_eq_zero_of_mem_cyclicCoboundaries {n : ℕ} (hn : Even n)
    {φ : cyclicCochains R A M n} (hφ : φ ∈ cyclicCoboundaries R A M n) {e : A}
    (he : IsIdempotentElem e) :
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (fun _ ↦ e) = 0 := by
  cases n with
  | zero =>
    rw [cyclicCoboundaries_zero, Submodule.mem_bot] at hφ
    rw [hφ, ZeroMemClass.coe_zero, zero_apply]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := (mem_cyclicCoboundaries_succ_iff _ _ _).1 hφ
    have hodd : ¬Even n := by simpa [Nat.even_add_one] using hn
    rw [coe_cyclicHochschildCoboundary_apply,
      hochschildCoboundary_apply_const_of_isIdempotentElem _ he]
    simp only [hodd, ↓reduceIte]
    -- Cyclicity in odd degree gives `v = -v` for the value `v = ψ(e, …, e)`, so `2 • v = 0`.
    have h := apply_const_eq_neg_of_mem_cyclicCochains ψ.2 (Nat.not_even_iff_odd.1 hodd) e
    have h2 : (2 : R) • (ψ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (fun _ ↦ e) = 0 := by
      rw [two_smul]
      nth_rw 2 [h]
      exact add_neg_cancel _
    rw [← one_smul R ((ψ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) fun _ ↦ e),
      ← invOf_mul_self (2 : R), mul_smul, h2, smul_zero]

end Coboundary

variable {R A M : Type*} [Field R] [CharZero R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

namespace cyclicCohomology

/-- The even pairing `⟨[e], [φ]⟩ = (m!)⁻¹ φ(e, …, e)` of an idempotent `e` with cyclic cohomology
classes of degree `2m`. -/
def evenPairing (e : A) (he : IsIdempotentElem e) (m : ℕ) :
    cyclicCohomology R A M (2 * m) →ₗ[R] M :=
  desc (2 * m)
    ((m ! : R)⁻¹ •
      { toFun φ := ((φ : cyclicCochains R A M (2 * m)) :
          MultilinearMap R (fun _ : Fin (2 * m + 1) ↦ A) M) fun _ ↦ e
        map_add' _ _ := rfl
        map_smul' _ _ := rfl })
    fun _ hφ ↦ by
      let := invertibleOfNonzero (two_ne_zero (α := R))
      simp [apply_const_eq_zero_of_mem_cyclicCoboundaries (even_two_mul m) hφ he]

/-- The even pairing of an idempotent `e` with the class of a cyclic cocycle `φ` is
`(m!)⁻¹ φ(e, …, e)`. -/
@[simp]
theorem evenPairing_mk (e : A) (he : IsIdempotentElem e) (m : ℕ)
    (φ : cyclicCocycles R A M (2 * m)) :
    evenPairing e he m (mk R A M (2 * m) φ) =
      (m ! : R)⁻¹ • ((φ : cyclicCochains R A M (2 * m)) :
        MultilinearMap R (fun _ : Fin (2 * m + 1) ↦ A) M) fun _ ↦ e := by
  simp [evenPairing]

/-- **Connes' even pairing** of an idempotent matrix `e` with cyclic cohomology: on the class of a
cyclic cocycle `φ` of degree `2m`, it is `(m!)⁻¹ (φ#Tr)(e, …, e)`. -/
theorem evenPairing_matrixExtension_mk {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Matrix ι ι A) (he : IsIdempotentElem e) (m : ℕ) (φ : cyclicCocycles R A M (2 * m)) :
    evenPairing e he m (matrixExtension M ι (2 * m) (mk R A M (2 * m) φ)) =
      (m ! : R)⁻¹ • matrixCochainExtension ι (2 * m)
        ((φ : cyclicCochains R A M (2 * m)) :
          MultilinearMap R (fun _ : Fin (2 * m + 1) ↦ A) M) fun _ ↦ e := by
  rw [matrixExtension_mk, evenPairing_mk, coe_matrixCyclicCochainExtension_apply]

/-- **Additivity of the even pairing on direct sums**: the even pairing of the block-diagonal
idempotent matrix `e ⊕ f` is the sum of the even pairings of `e` and `f`. -/
theorem evenPairing_fromBlocks_matrixExtension {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {e : Matrix ι ι A} {f : Matrix κ κ A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (m : ℕ) (c : cyclicCohomology R A M (2 * m)) :
    evenPairing (Matrix.fromBlocks e 0 0 f) (he.fromBlocks_zero₁₂_zero₂₁ hf) m
        (matrixExtension M (ι ⊕ κ) (2 * m) c) =
      evenPairing e he m (matrixExtension M ι (2 * m) c) +
        evenPairing f hf m (matrixExtension M κ (2 * m) c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M (2 * m) c
  simp only [evenPairing_matrixExtension_mk, matrixCochainExtension_fromBlocks_zero₁₂_zero₂₁,
    smul_add]

end cyclicCohomology

end TauCeti
