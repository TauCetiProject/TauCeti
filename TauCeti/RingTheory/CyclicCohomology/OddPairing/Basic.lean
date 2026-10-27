/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.RingTheory.CyclicCohomology.Matrix

import TauCeti.Data.Fin.Basic

/-!
# The odd pairing of cyclic cohomology with invertibles

Let `A` be a unital complex algebra and `M` a complex vector space. For an invertible `u` of `A`
and a cyclic `M`-valued cocycle `φ` of odd degree `n = 2m + 1`, Connes' odd pairing is
`⟨[u], [φ]⟩ = (1 + i)⁻¹ 2⁻ⁿ Γ(n/2 + 1)⁻¹ φ(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)`,
with `n + 1` alternating arguments. This file shows that the value depends only on the cyclic
cohomology class of `φ`, and constructs the resulting linear map `HC²ᵐ⁺¹(A; M) → M`. Composed with
matrix extension `HC²ᵐ⁺¹(A; M) → HC²ᵐ⁺¹(Matrix ι ι A; M)`, it pairs invertible matrices with cyclic
cohomology through `φ#Tr`. Its homotopy invariance and multiplicativity, the relations through
which it descends to algebraic `K₁`, are proved in
`TauCeti.RingTheory.CyclicCohomology.OddPairing.Invariance`.

The pairing descends to cohomology because the entries `x = u⁻¹ - 1` and `y = u - 1` are
quasi-inverse to each other in both orders: `y + x + xy = 0 = x + y + yx`. More generally, if
cyclically adjacent entries of a tuple `(x₀, …, xₙ₊₁)` are quasi-inverse, then every Hochschild
face `xᵢxᵢ₊₁ = -(xᵢ + xᵢ₊₁)` splits into the two tuples deleting `xᵢ₊₁` or `xᵢ`. For a cyclic
cochain `ψ` the alternating sum of these terms telescopes, so `(bψ)(x₀, …, xₙ₊₁) = 0`
(`TauCeti.hochschildCoboundary_apply_eq_zero_of_add_add_mul_eq_zero`).

## Main definitions

* `TauCeti.cyclicCohomology.oddPairing`: the pairing `HC²ᵐ⁺¹(A; M) → M` with an invertible.

## Main results

* `TauCeti.apply_eq_zero_of_mem_cyclicCoboundaries_of_add_add_mul_eq_zero`: a cyclic coboundary
  vanishes on a tuple whose cyclically adjacent entries are quasi-inverse.
* `TauCeti.cyclicCohomology.oddPairing_mk`: the pairing evaluated on the class of a cocycle.
* `TauCeti.cyclicCohomology.oddPairing_matrixExtension_mk`: Connes' formula
  `⟨[u], [φ]⟩ = (1 + i)⁻¹ 2⁻ⁿ Γ(n/2 + 1)⁻¹ (φ#Tr)(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)` for an
  invertible matrix `u`.
* `TauCeti.cyclicCohomology.oddPairing_matrixExtension_of_val_eq_fromBlocks`: the pairing is
  additive on direct sums, `⟨[u ⊕ v], [φ]⟩ = ⟨[u], [φ]⟩ + ⟨[v], [φ]⟩`.
* `TauCeti.cyclicCohomology.oddPairing_matrixExtension_of_val_eq_fromBlocks_one`: the pairing is
  unchanged by stabilization `u ↦ u ⊕ 1`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §3.
* J.-L. Loday, *Cyclic Homology*, §8.3.
-/

public section

noncomputable section

namespace TauCeti

section Coboundary

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- A cyclic coboundary vanishes on a tuple whose cyclically adjacent entries `xᵢ`, `xᵢ₊₁` are
quasi-inverse, `xᵢ₊₁ + xᵢ + xᵢxᵢ₊₁ = 0`. -/
theorem apply_eq_zero_of_mem_cyclicCoboundaries_of_add_add_mul_eq_zero {n : ℕ}
    {φ : cyclicCochains R A M n} (hφ : φ ∈ cyclicCoboundaries R A M n) {x : Fin (n + 1) → A}
    (hx : ∀ i, x (finRotate (n + 1) i) + x i + x i * x (finRotate (n + 1) i) = 0) :
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) x = 0 := by
  cases n with
  | zero =>
    rw [cyclicCoboundaries_zero, Submodule.mem_bot] at hφ
    rw [hφ, ZeroMemClass.coe_zero, zero_apply]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := (mem_cyclicCoboundaries_succ_iff _ _ _).1 hφ
    rw [coe_cyclicHochschildCoboundary_apply]
    exact hochschildCoboundary_apply_eq_zero_of_add_add_mul_eq_zero ψ.2 hx

end Coboundary

section Units

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- The cyclically adjacent entries of `(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)` are quasi-inverse. -/
private theorem add_add_mul_eq_zero_of_units (u : Aˣ) {m : ℕ} {x : Fin (2 * m + 2) → A}
    (hx : x = fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then (↑u⁻¹ - 1 : A) else ↑u - 1)
    (i : Fin (2 * m + 2)) :
    x (finRotate (2 * m + 2) i) + x i + x i * x (finRotate (2 * m + 2) i) = 0 := by
  subst hx
  have h₁ : (↑u - 1 : A) + (↑u⁻¹ - 1) + (↑u⁻¹ - 1) * (↑u - 1) = 0 := by
    simp only [sub_mul, mul_sub, Units.inv_mul, mul_one, one_mul]
    abel
  have h₂ : (↑u⁻¹ - 1 : A) + (↑u - 1) + (↑u - 1) * (↑u⁻¹ - 1) = 0 := by
    simp only [sub_mul, mul_sub, Units.mul_inv, mul_one, one_mul]
    abel
  induction i using Fin.lastCases with
  | last =>
    have hodd : ¬Even (2 * m + 1) := by simp
    simpa [finRotate_last, hodd] using h₂
  | cast j =>
    rw [Fin.finRotate_castSucc]
    by_cases hj : Even (j : ℕ)
    · simpa [hj, Nat.even_add_one] using h₁
    · simpa [hj, Nat.even_add_one] using h₂

/-- A cyclic coboundary of odd degree `2m + 1` vanishes on the tuple
`(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)` of an invertible `u`. -/
theorem apply_units_eq_zero_of_mem_cyclicCoboundaries (u : Aˣ) {m : ℕ}
    {φ : cyclicCochains R A M (2 * m + 1)} (hφ : φ ∈ cyclicCoboundaries R A M (2 * m + 1)) :
    (φ : MultilinearMap R (fun _ : Fin (2 * m + 2) ↦ A) M)
      (fun k ↦ if Even (k : ℕ) then ↑u⁻¹ - 1 else ↑u - 1) = 0 :=
  apply_eq_zero_of_mem_cyclicCoboundaries_of_add_add_mul_eq_zero hφ
    (add_add_mul_eq_zero_of_units u rfl)

end Units

namespace cyclicCohomology

variable {A M : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]

/-- **Connes' odd pairing** `⟨[u], [φ]⟩ = (1 + i)⁻¹ 2⁻ⁿ Γ(n/2 + 1)⁻¹ φ(u⁻¹ - 1, u - 1, …, u - 1)`
of an invertible `u` with cyclic cohomology classes of odd degree `n = 2m + 1`. -/
def oddPairing (u : Aˣ) (m : ℕ) : cyclicCohomology ℂ A M (2 * m + 1) →ₗ[ℂ] M :=
  desc (2 * m + 1)
    (((1 + Complex.I)⁻¹ * ((2 : ℂ) ^ (2 * m + 1))⁻¹ *
        ((Real.Gamma ((2 * m + 1 : ℝ) / 2 + 1) : ℂ))⁻¹) •
      { toFun φ := ((φ : cyclicCochains ℂ A M (2 * m + 1)) :
          MultilinearMap ℂ (fun _ : Fin (2 * m + 2) ↦ A) M)
            fun k ↦ if Even (k : ℕ) then ↑u⁻¹ - 1 else ↑u - 1
        map_add' _ _ := rfl
        map_smul' _ _ := rfl })
    fun _ hφ ↦ by simp [apply_units_eq_zero_of_mem_cyclicCoboundaries u hφ]

/-- The odd pairing of an invertible `u` with the class of a cyclic cocycle `φ` of degree
`n = 2m + 1` is `(1 + i)⁻¹ 2⁻ⁿ Γ(n/2 + 1)⁻¹ φ(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)`. -/
@[simp]
theorem oddPairing_mk (u : Aˣ) (m : ℕ) (φ : cyclicCocycles ℂ A M (2 * m + 1)) :
    oddPairing u m (mk ℂ A M (2 * m + 1) φ) =
      ((1 + Complex.I)⁻¹ * ((2 : ℂ) ^ (2 * m + 1))⁻¹ *
          ((Real.Gamma ((2 * m + 1 : ℝ) / 2 + 1) : ℂ))⁻¹) •
        ((φ : cyclicCochains ℂ A M (2 * m + 1)) :
          MultilinearMap ℂ (fun _ : Fin (2 * m + 2) ↦ A) M)
            fun k ↦ if Even (k : ℕ) then ↑u⁻¹ - 1 else ↑u - 1 := by
  simp [oddPairing]

/-- The odd pairing of the unit vanishes. -/
@[simp]
theorem oddPairing_one (m : ℕ) :
    oddPairing (1 : Aˣ) m = (0 : cyclicCohomology ℂ A M (2 * m + 1) →ₗ[ℂ] M) := by
  ext φ
  simp [← Pi.zero_def]

/-- **Connes' odd pairing** of an invertible matrix `u` with cyclic cohomology: on the class of a
cyclic cocycle `φ` of degree `n = 2m + 1`, it is
`(1 + i)⁻¹ 2⁻ⁿ Γ(n/2 + 1)⁻¹ (φ#Tr)(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)`. -/
theorem oddPairing_matrixExtension_mk {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι A)ˣ) (m : ℕ) (φ : cyclicCocycles ℂ A M (2 * m + 1)) :
    oddPairing u m (matrixExtension M ι (2 * m + 1) (mk ℂ A M (2 * m + 1) φ)) =
      ((1 + Complex.I)⁻¹ * ((2 : ℂ) ^ (2 * m + 1))⁻¹ *
          ((Real.Gamma ((2 * m + 1 : ℝ) / 2 + 1) : ℂ))⁻¹) •
        matrixCochainExtension ι (2 * m + 1)
          ((φ : cyclicCochains ℂ A M (2 * m + 1)) :
            MultilinearMap ℂ (fun _ : Fin (2 * m + 2) ↦ A) M)
          fun k ↦ if Even (k : ℕ) then ↑u⁻¹ - 1 else ↑u - 1 := by
  rw [matrixExtension_mk, oddPairing_mk, coe_matrixCyclicCochainExtension_apply]

/-- **Additivity of the odd pairing on direct sums**: the odd pairing of an invertible matrix `w`
which is block diagonal with diagonal blocks `u` and `v` is the sum of the odd pairings of `u`
and `v`. -/
theorem oddPairing_matrixExtension_of_val_eq_fromBlocks {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {w : (Matrix (ι ⊕ κ) (ι ⊕ κ) A)ˣ} {u : (Matrix ι ι A)ˣ}
    {v : (Matrix κ κ A)ˣ} (hw : (w : Matrix (ι ⊕ κ) (ι ⊕ κ) A) = Matrix.fromBlocks u 0 0 v)
    (m : ℕ) (c : cyclicCohomology ℂ A M (2 * m + 1)) :
    oddPairing w m (matrixExtension M (ι ⊕ κ) (2 * m + 1) c) =
      oddPairing u m (matrixExtension M ι (2 * m + 1) c) +
        oddPairing v m (matrixExtension M κ (2 * m + 1) c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective ℂ A M (2 * m + 1) c
  have hw' : ((w⁻¹ : (Matrix (ι ⊕ κ) (ι ⊕ κ) A)ˣ) : Matrix (ι ⊕ κ) (ι ⊕ κ) A) =
      Matrix.fromBlocks ↑u⁻¹ 0 0 ↑v⁻¹ :=
    Units.inv_eq_of_mul_eq_one_left (by simp [hw, Matrix.fromBlocks_multiply])
  -- Both entries `w⁻¹ - 1` and `w - 1` of the pairing are block diagonal.
  have hx : (fun k : Fin (2 * m + 2) ↦
        if Even (k : ℕ) then (↑w⁻¹ - 1 : Matrix (ι ⊕ κ) (ι ⊕ κ) A) else ↑w - 1) =
      fun k : Fin (2 * m + 2) ↦
        Matrix.fromBlocks (if Even (k : ℕ) then (↑u⁻¹ - 1 : Matrix ι ι A) else ↑u - 1) 0 0
        (if Even (k : ℕ) then (↑v⁻¹ - 1 : Matrix κ κ A) else ↑v - 1) := by
    funext k
    ext (i | i) (j | j) <;> split_ifs <;> simp [hw, hw', Matrix.one_apply]
  simp only [oddPairing_matrixExtension_mk, hx, matrixCochainExtension_fromBlocks_zero₁₂_zero₂₁,
    smul_add]

/-- **Stabilization of the odd pairing**: enlarging an invertible matrix `u` to the block diagonal
matrix `u ⊕ 1` does not change its odd pairing. -/
theorem oddPairing_matrixExtension_of_val_eq_fromBlocks_one {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] {w : (Matrix (ι ⊕ κ) (ι ⊕ κ) A)ˣ}
    {u : (Matrix ι ι A)ˣ} (hw : (w : Matrix (ι ⊕ κ) (ι ⊕ κ) A) = Matrix.fromBlocks u 0 0 1)
    (m : ℕ) (c : cyclicCohomology ℂ A M (2 * m + 1)) :
    oddPairing w m (matrixExtension M (ι ⊕ κ) (2 * m + 1) c) =
      oddPairing u m (matrixExtension M ι (2 * m + 1) c) := by
  rw [oddPairing_matrixExtension_of_val_eq_fromBlocks (v := 1) hw, oddPairing_one,
    LinearMap.zero_apply, add_zero]

end cyclicCohomology

end TauCeti
