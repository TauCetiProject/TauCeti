/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.Basic

/-!
# Principal congruence quotients and index formulas

This file develops the finite-quotient and index arithmetic of `Γ(N) ≤ Γ₁(N) ≤ SL₂(ℤ)`:
* `CongruenceSubgroup.quotientGammaEquiv`: `(SL₂(ℤ) ⧸ Γ(N)) ≃* SL₂(ℤ/Nℤ)`.
* `CongruenceSubgroup.gamma1UpperRightHom` and `gamma1QuotientGammaEquiv`:
  `(Γ₁(N) ⧸ Γ(N)) ≃* Multiplicative (ZMod N)`, `[Γ₁(N) : Γ(N)] = N`, and
  `[SL₂(ℤ) : Γ(N)] = |ZMod N| · [SL₂(ℤ) : Γ₁(N)]`.
* Prime, prime-power, prime-factorization, and cleared Euler-product formulas for `[SL₂(ℤ) : Γ(N)]`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005, §1.2.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton, 1971,
  §1.6.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CongruenceSubgroup

attribute [local instance] Gamma_normal

/-! ### Principal quotients and `Γ₁(N) ⧸ Γ(N) ≃* Multiplicative (ZMod N)` -/

/-- **Canonical isomorphism `(SL(2, ℤ) ⧸ Γ(N)) ≃* SL(2, ZMod N)`** induced by entrywise reduction
modulo `N` and strong approximation (`Matrix.SpecialLinearGroup.map_intCast_zmod_surjective`). -/
noncomputable def quotientGammaEquiv (N : ℕ) :
    (SL(2, ℤ) ⧸ Gamma N) ≃* SL(2, ZMod N) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)))
    Matrix.SpecialLinearGroup.map_intCast_zmod_surjective

/-- `quotientGammaEquiv N` evaluates on coset representatives by entrywise reduction modulo `N`. -/
@[simp]
theorem quotientGammaEquiv_mk (N : ℕ) (γ : SL(2, ℤ)) :
    quotientGammaEquiv N (QuotientGroup.mk γ) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ := (rfl)

/-- The upper-right-entry homomorphism `Γ₁(N) →* Multiplicative (ZMod N)` sending `γ` to
`Multiplicative.ofAdd (γ 0 1 : ZMod N)`. Since matrices in `Γ₁(N)` are congruent to `!![1, *; 0, 1]`
modulo `N`, matrix multiplication adds their upper-right entries modulo `N`. -/
def gamma1UpperRightHom (N : ℕ) : Gamma1 N →* Multiplicative (ZMod N) where
  toFun g := Multiplicative.ofAdd (g.val 0 1 : ZMod N)
  map_one' := by simp
  map_mul' := fun ⟨A, hA⟩ ⟨B, hB⟩ ↦ by
    obtain ⟨hA00, -, -⟩ := (Gamma1_mem N A).mp hA
    obtain ⟨-, hB11, -⟩ := (Gamma1_mem N B).mp hB
    rw [← ofAdd_add]
    congr 1
    simp only [Subgroup.coe_mul, coe_mul, (Matrix.two_mul_expl A.val B.val).2.1, Int.cast_add,
      Int.cast_mul, hA00, hB11, one_mul, mul_one]
    exact add_comm _ _

/-- Evaluation formula for `gamma1UpperRightHom`. -/
theorem gamma1UpperRightHom_apply (N : ℕ) (g : Gamma1 N) :
    gamma1UpperRightHom N g = Multiplicative.ofAdd (g.val 0 1 : ZMod N) := (rfl)

/-- Converting the value of `gamma1UpperRightHom N g` back to `ZMod N` yields the upper-right
entry `g 0 1` modulo `N`. -/
@[simp]
theorem toAdd_gamma1UpperRightHom_apply (N : ℕ) (g : Gamma1 N) :
    Multiplicative.toAdd (gamma1UpperRightHom N g) = (g.val 0 1 : ZMod N) := by
  rw [gamma1UpperRightHom_apply, toAdd_ofAdd]

/-- Powers of the translation matrix `ModularGroup.T` witness surjectivity of
`gamma1UpperRightHom N` at every level `N : ℕ`. -/
theorem gamma1UpperRightHom_surjective (N : ℕ) :
    Function.Surjective (gamma1UpperRightHom N) := fun x ↦ by
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (Multiplicative.toAdd x)
  exact ⟨⟨ModularGroup.T ^ z, T_zpow_mem_Gamma1 N z⟩,
    Multiplicative.toAdd.injective (by simp [ModularGroup.coe_T_zpow, hz])⟩

/-- Inside `Γ₁(N)`, the kernel of the upper-right entry modulo `N` is `Γ(N)`. -/
theorem ker_gamma1UpperRightHom (N : ℕ) :
    (gamma1UpperRightHom N).ker = (Gamma N).subgroupOf (Gamma1 N) := by
  ext ⟨A, hA⟩
  obtain ⟨hA00, hA11, hA10⟩ := (Gamma1_mem N A).mp hA
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Gamma_mem,
    ← Multiplicative.toAdd.injective.eq_iff, toAdd_gamma1UpperRightHom_apply, toAdd_one]
  exact ⟨fun hA01 ↦ ⟨hA00, hA01, hA10, hA11⟩, fun h ↦ h.2.1⟩

/-- **Canonical isomorphism `(Γ₁(N) ⧸ Γ(N)) ≃* Multiplicative (ZMod N)`.** -/
noncomputable def gamma1QuotientGammaEquiv (N : ℕ) :
    (Gamma1 N ⧸ (Gamma N).subgroupOf (Gamma1 N)) ≃* Multiplicative (ZMod N) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_gamma1UpperRightHom N).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (gamma1UpperRightHom N)
      (gamma1UpperRightHom_surjective N))

/-- `gamma1QuotientGammaEquiv N` evaluates on coset representatives via `gamma1UpperRightHom N`. -/
@[simp]
theorem gamma1QuotientGammaEquiv_mk (N : ℕ) (g : Gamma1 N) :
    gamma1QuotientGammaEquiv N (QuotientGroup.mk g) = gamma1UpperRightHom N g := (rfl)

/-! ### Relative and global index formulas for `Γ(N)` -/

/-- At every level `N : ℕ`, `[Γ₁(N) : Γ(N)] = N` (including `0` at `N = 0`). -/
theorem Gamma_relIndex_Gamma1 (N : ℕ) :
    (Gamma N).relIndex (Gamma1 N) = N := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card,
    Nat.card_congr (gamma1QuotientGammaEquiv N).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- Tower relation `[SL₂(ℤ) : Γ(N)] = |ZMod N| · [SL₂(ℤ) : Γ₁(N)]`, valid at every level `N : ℕ`. -/
theorem index_Gamma_eq_card_zmod_mul_Gamma1_index (N : ℕ) :
    (Gamma N).index = Nat.card (ZMod N) * (Gamma1 N).index := by
  rw [← Subgroup.relIndex_mul_index (Gamma_le_Gamma1 N), Gamma_relIndex_Gamma1, Nat.card_zmod]

/-- For a prime `p`, `[SL₂(ℤ) : Γ(p)] = p(p² - 1)`. -/
theorem index_Gamma_prime {p : ℕ} (hp : p.Prime) :
    (Gamma p).index = p * (p ^ 2 - 1) := by
  rw [index_Gamma, card_fin_two_zmod_prime hp]

/-- For a prime `p` and `1 ≤ k`, `[SL₂(ℤ) : Γ(p^k)] = p^{3k - 2}(p² - 1)`. -/
theorem index_Gamma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (Gamma (p ^ k)).index = p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  rw [index_Gamma, card_fin_two_zmod_prime_pow hp hk]

/-- For `N ≠ 0`, `[SL₂(ℤ) : Γ(N)] = ∏_{p^k ∥ N} p^{3k - 2}(p² - 1)`. -/
theorem index_Gamma_eq_prod_factorization {N : ℕ} (hN : N ≠ 0) :
    (Gamma N).index = N.factorization.prod fun p k ↦ p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  rw [index_Gamma, card_fin_two_zmod_eq_prod_factorization hN]

/-- **Cleared Euler product for `[SL₂(ℤ) : Γ(N)]`** (valid for every `N : ℕ`):
`[SL₂(ℤ) : Γ(N)] · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)`. -/
theorem index_Gamma_mul_prod_primeFactors_sq (N : ℕ) :
    (Gamma N).index * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [index_Gamma, card_fin_two_zmod_mul_prod_primeFactors_sq]

end CongruenceSubgroup
