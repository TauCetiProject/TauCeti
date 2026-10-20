/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.RingTheory.CyclicCohomology.Matrix

import TauCeti.Data.Fin.Tuple.Basic

/-!
# The odd pairing of cyclic cohomology with invertibles

Let `A` be a unital complex algebra and `M` a complex vector space. For an invertible `u` of `A`
and a cyclic `M`-valued cocycle `φ` of odd degree `n = 2m + 1`, Connes' odd pairing is
`⟨[u], [φ]⟩ = (1 + i)⁻¹ 2⁻ⁿ Γ(n/2 + 1)⁻¹ φ(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)`,
with `n + 1` alternating arguments. This file shows that the value depends only on the cyclic
cohomology class of `φ`, and constructs the resulting linear map `HC²ᵐ⁺¹(A; M) → M`. Composed with
matrix extension `HC²ᵐ⁺¹(A; M) → HC²ᵐ⁺¹(Matrix ι ι A; M)`, it pairs invertible matrices with cyclic
cohomology through `φ#Tr`. Its descent to algebraic `K₁` is not treated here.

The pairing descends to cohomology because the entries `x = u⁻¹ - 1` and `y = u - 1` are
quasi-inverse to each other in both orders: `y + x + xy = 0 = x + y + yx`. More generally, if
cyclically adjacent entries of a tuple `(x₀, …, xₙ₊₁)` are quasi-inverse, then every Hochschild
face `xᵢxᵢ₊₁ = -(xᵢ + xᵢ₊₁)` splits into the two tuples deleting `xᵢ₊₁` or `xᵢ`. For a cyclic
cochain `ψ` the alternating sum of these terms telescopes, so `(bψ)(x₀, …, xₙ₊₁) = 0`.

## Main definitions

* `TauCeti.cyclicCohomology.oddPairing`: the pairing `HC²ᵐ⁺¹(A; M) → M` with an invertible.

## Main results

* `TauCeti.hochschildCoboundary_apply_eq_zero_of_add_add_mul_eq_zero`: the Hochschild
  coboundary of a cyclic cochain vanishes on a tuple whose cyclically adjacent entries are
  quasi-inverse.
* `TauCeti.apply_eq_zero_of_mem_cyclicCoboundaries_of_add_add_mul_eq_zero`: a cyclic coboundary
  vanishes on such a tuple.
* `TauCeti.cyclicCohomology.oddPairing_mk`: the pairing evaluated on the class of a cocycle.
* `TauCeti.cyclicCohomology.oddPairing_matrixExtension_mk`: Connes' formula
  `⟨[u], [φ]⟩ = (1 + i)⁻¹ 2⁻ⁿ Γ(n/2 + 1)⁻¹ (φ#Tr)(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)` for an
  invertible matrix `u`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §3.
* J.-L. Loday, *Cyclic Homology*, §8.3.
-/

public section

noncomputable section

namespace TauCeti

section Coboundary

section Cochain

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- **The Hochschild coboundary of a cyclic cochain vanishes on quasi-inverse chains.** If the
cyclically adjacent entries `xᵢ`, `xᵢ₊₁` (indices modulo `n + 2`) of a tuple satisfy
`xᵢ₊₁ + xᵢ + xᵢxᵢ₊₁ = 0`, then `(bψ)(x₀, …, xₙ₊₁) = 0` for every cyclic `n`-cochain `ψ`. -/
theorem hochschildCoboundary_apply_eq_zero_of_add_add_mul_eq_zero
    {ψ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hψ : ψ ∈ cyclicCochains R A M n)
    {x : Fin (n + 2) → A}
    (hx : ∀ i, x (finRotate (n + 2) i) + x i + x i * x (finRotate (n + 2) i) = 0) :
    hochschildCoboundary R A M n ψ x = 0 := by
  -- A product `yz` of quasi-inverse entries in one slot splits into the values on `y` and on `z`.
  have hsplit (r : Fin (n + 1) → A) (j : Fin (n + 1)) {y z : A} (h : z + y + y * z = 0) :
      ψ (Function.update r j (y * z)) =
        -(ψ (Function.update r j y) + ψ (Function.update r j z)) := by
    have h0 := ψ.map_update_zero r j
    rw [← h, ψ.map_update_add, ψ.map_update_add, add_comm (ψ _) (ψ (Function.update r j y))] at h0
    exact eq_neg_of_add_eq_zero_right h0
  -- With `g i = (-1)ⁱ ψ(x with entry i deleted)`, the inner faces contribute `g (j + 1) - g j`.
  set g : Fin (n + 2) → M := fun i ↦ (-1 : ℤ) ^ (i : ℕ) • ψ (Fin.removeNth i x) with hg
  have hinner (j : Fin (n + 1)) : (-1 : ℤ) ^ (j : ℕ) • ψ (Fin.contractNth j.castSucc (· * ·) x) =
      g j.succ - g j.castSucc := by
    have hj := hx j.castSucc
    rw [show finRotate (n + 2) j.castSucc = j.succ from Fin.ext (by simp)] at hj
    rw [Fin.contractNth_castSucc_eq_update_removeNth_succ, hsplit _ _ hj,
      Fin.update_removeNth_succ_eq_removeNth_castSucc,
      Function.update_eq_self_iff.2 (by simp [Fin.removeNth_apply])]
    simp only [hg, Fin.val_succ, Fin.val_castSucc, pow_succ, mul_neg_one, neg_smul, smul_neg,
      smul_add]
    abel
  -- The last face contributes `g 0 - g (n + 1)`, by cyclicity of `ψ`.
  have hlast : (-1 : ℤ) ^ (n + 1) •
      ψ (Fin.cons (x (Fin.last (n + 1)) * x 0) fun k ↦ x k.castSucc.succ) =
        g 0 - g (Fin.last (n + 1)) := by
    have hl := hx (Fin.last (n + 1))
    rw [finRotate_last] at hl
    have hinit : (Fin.cons (x 0) fun k ↦ x k.castSucc.succ : Fin (n + 1) → A) = Fin.init x := by
      funext k
      cases k using Fin.cases <;> rfl
    have htail : (Fin.cons (x (Fin.last (n + 1))) fun k ↦ x k.castSucc.succ : Fin (n + 1) → A) =
        Fin.tail x ∘ (finRotate (n + 1)).symm := by
      funext k
      cases k using Fin.cases with
      | zero =>
        rw [Function.comp_apply, (Equiv.symm_apply_eq _).2 finRotate_last.symm]
        simp [Fin.tail]
      | succ k =>
        rw [Function.comp_apply, (Equiv.symm_apply_eq _).2 (Fin.ext (by simp) :
          finRotate (n + 1) k.castSucc = k.succ).symm]
        simp [Fin.tail]
    rw [← Fin.update_cons_zero (x (Fin.last (n + 1))), hsplit _ _ hl, Fin.update_cons_zero,
      Fin.update_cons_zero, hinit, htail, mem_cyclicCochains_iff.1 hψ]
    have hsign : (-1 : ℤ) ^ (n + 1) * (-1) ^ n = -1 := by
      rw [← pow_add]
      exact Odd.neg_one_pow ⟨n, by ring⟩
    simp only [hg, Fin.val_zero, Fin.val_last, Fin.removeNth_zero, Fin.removeNth_last, pow_zero,
      one_smul, smul_neg, smul_add, smul_smul, hsign, neg_one_smul]
    abel
  rw [hochschildCoboundary_apply_eq_sum_contractNth_add, Finset.sum_congr rfl fun j _ ↦ hinner j,
    Finset.sum_sub_distrib, hlast]
  have hsucc := Fin.sum_univ_succ g
  rw [Fin.sum_univ_castSucc] at hsucc
  rw [sub_add_sub_comm, ← sub_eq_zero_of_eq hsucc.symm]
  abel

end Cochain

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
    rw [show finRotate (2 * m + 2) j.castSucc = j.succ from Fin.ext (by simp)]
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

end cyclicCohomology

end TauCeti
