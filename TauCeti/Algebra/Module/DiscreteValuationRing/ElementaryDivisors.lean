/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Length
import TauCeti.Algebra.Order.BigOperators.Sum.Min
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.Length.SMulTop

/-!
# Elementary divisors of torsion modules over a discrete valuation ring

Let `R` be a discrete valuation ring with maximal ideal `𝔪`. A finitely generated torsion
`R`-module is a finite product `∏ i, R ⧸ 𝔪 ^ e i`
(`TauCeti.Module.equiv_pi_prod_pi_quotient_span_pow` with no free part). This file shows that
the exponents `e i`, its *elementary divisors* or *type*, are well defined, and computes the
graded pieces of the `𝔪`-adic filtration in terms of them: for `M ≃ ∏ i, R ⧸ 𝔪 ^ e i`,

* `M ⧸ 𝔪 ^ k M` has length `∑ i, min k (e i)`, and
* the graded piece `𝔪 ^ k M ⧸ 𝔪 ^ (k + 1) M` is a vector space over `R ⧸ 𝔪` of dimension
  `#{i | k < e i}`, the number of exponents exceeding `k`.

The truncated sums `∑ i, min k (e i)` determine a family of positive exponents up to reindexing
(`Fintype.exists_equiv_of_forall_sum_min_eq`), so the type of a module is an isomorphism
invariant. For the ring of Witt vectors `W(k)` of a perfect field, a discrete valuation ring with
maximal ideal `(p)`, this is the type `(λ₁ ≥ ⋯ ≥ λₙ)` of a finite `p`-power torsion module
`⊕ W(k) ⧸ p ^ λⱼ`, whose graded pieces `p ^ i Q ⧸ p ^ (i + 1) Q` have the column lengths
`#{j | i < λⱼ}` as dimensions. For `ℤ_[p]` this recovers the uniqueness of the elementary divisors
of a finite abelian `p`-group (`ZMod.exists_equiv_exponents_of_pi_pow_addEquiv`).

## Main results

* `TauCeti.IsDiscreteValuationRing.length_quotient_pi_pow_maximalIdeal_smul_top`: the quotient of
  `∏ i, R ⧸ 𝔪 ^ e i` by `∏ i, 𝔪 ^ a i (R ⧸ 𝔪 ^ e i)` has length `∑ i, min (a i) (e i)`.
* `TauCeti.IsDiscreteValuationRing.length_quotient_pow_maximalIdeal_smul_top`: for
  `M ≃ ∏ i, R ⧸ 𝔪 ^ e i`, the length of `M ⧸ 𝔪 ^ k M` is `∑ i, min k (e i)`.
* `TauCeti.IsDiscreteValuationRing.length_pow_maximalIdeal_smul_top_quotient_smul_top`: the
  graded piece `𝔪 ^ k M ⧸ 𝔪 ^ (k + 1) M` has length `#{i | k < e i}`.
* `TauCeti.IsDiscreteValuationRing.finrank_pow_maximalIdeal_smul_top_quotient_smul_top`: the
  same graded piece has dimension `#{i | k < e i}` over the residue field `R ⧸ 𝔪`.
* `TauCeti.IsDiscreteValuationRing.exists_equiv_of_linearEquiv_pi_quotient_pow`: two products
  `∏ i, R ⧸ 𝔪 ^ e i` and `∏ j, R ⧸ 𝔪 ^ e' j` with positive exponents are isomorphic only if
  their exponents agree up to a bijection of the index types.

## References

* I. G. Macdonald, *Symmetric functions and Hall polynomials*, Chapter II, §1.
* B. Bhatt, P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, §7.
-/

public section

namespace TauCeti.IsDiscreteValuationRing

open Finset IsLocalRing Module Submodule

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The quotient of the cyclic module `R ⧸ 𝔪 ^ e` by `𝔪 ^ k` times itself is `R ⧸ 𝔪 ^ min k e`,
so it has length `min k e`. -/
@[simp]
theorem length_quotient_pow_maximalIdeal_quotient_smul_top (e k : ℕ) :
    length R ((R ⧸ maximalIdeal R ^ e) ⧸
        (maximalIdeal R ^ k • ⊤ : Submodule R (R ⧸ maximalIdeal R ^ e))) = min k e := by
  -- `𝔪 ^ k` times `R ⧸ 𝔪 ^ e` is the image of `𝔪 ^ k`, and `𝔪 ^ e ⊔ 𝔪 ^ k = 𝔪 ^ min k e`.
  have hmap : (maximalIdeal R ^ k • ⊤ : Submodule R (R ⧸ maximalIdeal R ^ e)) =
      Submodule.map (maximalIdeal R ^ e).mkQ (maximalIdeal R ^ k) := by
    rw [← range_mkQ, ← Submodule.map_top, ← map_smul'', Ideal.smul_eq_mul, Ideal.mul_top]
  have hsup : maximalIdeal R ^ e ⊔ maximalIdeal R ^ k = maximalIdeal R ^ min k e := by
    rcases le_total k e with h | h
    · rw [min_eq_left h, sup_eq_right.mpr (Ideal.pow_le_pow_right h)]
    · rw [min_eq_right h, sup_eq_left.mpr (Ideal.pow_le_pow_right h)]
  rw [(quotEquivOfEq _ _ hmap).length_eq,
    (quotientQuotientEquivQuotientSup (maximalIdeal R ^ e) (maximalIdeal R ^ k)).length_eq,
    (quotEquivOfEq _ _ hsup).length_eq,
    _root_.IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

variable {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] {e : ι → ℕ}

variable (e) in
/-- **Quotients by products of powers of `𝔪`.** The quotient of `∏ i, R ⧸ 𝔪 ^ e i` by the product
of the submodules `𝔪 ^ a i (R ⧸ 𝔪 ^ e i)` has length `∑ i, min (a i) (e i)`. -/
theorem length_quotient_pi_pow_maximalIdeal_smul_top (a : ι → ℕ) :
    length R ((∀ i, R ⧸ maximalIdeal R ^ e i) ⧸ Submodule.pi Set.univ fun i ↦
      (maximalIdeal R ^ a i • ⊤ : Submodule R (R ⧸ maximalIdeal R ^ e i))) =
        ∑ i, min (a i) (e i) := by
  rw [length_quotient_pi]
  simp [length_quotient_pow_maximalIdeal_quotient_smul_top]

/-- **The length of `M ⧸ 𝔪 ^ k M` for a module of type `e`.** If `M ≃ ∏ i, R ⧸ 𝔪 ^ e i`, then
`M ⧸ 𝔪 ^ k M` has length `∑ i, min k (e i)`. -/
theorem length_quotient_pow_maximalIdeal_smul_top (f : M ≃ₗ[R] ∀ i, R ⧸ maximalIdeal R ^ e i)
    (k : ℕ) :
    length R (M ⧸ (maximalIdeal R ^ k • ⊤ : Submodule R M)) = ∑ i, min k (e i) := by
  rw [length_quotient_smul_top_congr f, length_pi_quotient_smul_top]
  simp [length_quotient_pow_maximalIdeal_quotient_smul_top]

/-- **The graded pieces of the `𝔪`-adic filtration of a module of type `e`.** If
`M ≃ ∏ i, R ⧸ 𝔪 ^ e i`, then `𝔪 ^ k M ⧸ 𝔪 ^ (k + 1) M` has length `#{i | k < e i}`, the number
of exponents exceeding `k`. -/
theorem length_pow_maximalIdeal_smul_top_quotient_smul_top
    (f : M ≃ₗ[R] ∀ i, R ⧸ maximalIdeal R ^ e i) (k : ℕ) :
    length R (↥(maximalIdeal R ^ k • ⊤ : Submodule R M) ⧸
      (maximalIdeal R • ⊤ : Submodule R ↥(maximalIdeal R ^ k • ⊤ : Submodule R M))) =
        #{i | k < e i} := by
  classical
  have h := length_quotient_smul_eq_length_quotient_smul_top_add (maximalIdeal R)
    (maximalIdeal R ^ k • ⊤ : Submodule R M)
  rw [← Submodule.mul_smul, ← pow_succ', length_quotient_pow_maximalIdeal_smul_top f,
    length_quotient_pow_maximalIdeal_smul_top f] at h
  rw [Finset.sum_min_add_one, Nat.cast_add, add_comm] at h
  exact (WithTop.add_right_cancel (ENat.natCast_ne_top _) h).symm

/-- **The graded ranks of a module of type `e`.** If `M ≃ ∏ i, R ⧸ 𝔪 ^ e i`, then the graded
piece `𝔪 ^ k M ⧸ 𝔪 ^ (k + 1) M` of the `𝔪`-adic filtration is a vector space over the residue
field `R ⧸ 𝔪` of dimension `#{i | k < e i}`, the number of exponents exceeding `k`. -/
theorem finrank_pow_maximalIdeal_smul_top_quotient_smul_top
    (f : M ≃ₗ[R] ∀ i, R ⧸ maximalIdeal R ^ e i) (k : ℕ) :
    finrank (R ⧸ maximalIdeal R) (↥(maximalIdeal R ^ k • ⊤ : Submodule R M) ⧸
      (maximalIdeal R • ⊤ : Submodule R ↥(maximalIdeal R ^ k • ⊤ : Submodule R M))) =
        #{i | k < e i} := by
  have : Module.Finite R M := Module.Finite.equiv f.symm
  let := Ideal.Quotient.field (maximalIdeal R)
  have hsurj : Function.Surjective (algebraMap R (R ⧸ maximalIdeal R)) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  rw [← Nat.cast_inj (R := ℕ∞), ← length_eq_finrank, ← length_eq_of_surjective hsurj,
    length_pow_maximalIdeal_smul_top_quotient_smul_top f]

/-- **Uniqueness of elementary divisors over a discrete valuation ring.** If the products
`∏ i, R ⧸ 𝔪 ^ e i` and `∏ j, R ⧸ 𝔪 ^ e' j` are isomorphic, all exponents being positive and the
first index type finite, then the exponents agree after a bijection of the index types. -/
theorem exists_equiv_of_linearEquiv_pi_quotient_pow {ι κ : Type*} [Finite ι] {e : ι → ℕ}
    {e' : κ → ℕ} (he : ∀ i, 0 < e i) (he' : ∀ j, 0 < e' j)
    (f : (∀ i, R ⧸ maximalIdeal R ^ e i) ≃ₗ[R] ∀ j, R ⧸ maximalIdeal R ^ e' j) :
    ∃ σ : ι ≃ κ, ∀ i, e i = e' (σ i) := by
  classical
  let := Fintype.ofFinite ι
  have : Finite κ := by
    -- Each factor maps onto `R ⧸ 𝔪`, so an infinite `κ` would give the product infinite length.
    by_contra hκ
    rw [not_finite_iff_infinite] at hκ
    have hsurj : Function.Surjective (LinearMap.pi fun j ↦ (Submodule.factor
        (Ideal.pow_le_self (he' j).ne' : maximalIdeal R ^ e' j ≤ maximalIdeal R)).comp
          (LinearMap.proj j) : (∀ j, R ⧸ maximalIdeal R ^ e' j) →ₗ[R] κ → R ⧸ maximalIdeal R) :=
      fun y ↦ ⟨fun j ↦ Submodule.Quotient.mk (Quotient.out (y j)), funext fun j ↦ by simp⟩
    have hle := length_le_of_surjective _ hsurj
    rw [length_pi, ENat.card_eq_top_of_infinite, Ideal.length_quotient_eq_one, mul_one, top_le_iff,
      ← f.length_eq, length_pi_of_fintype] at hle
    simp only [_root_.IsDiscreteValuationRing.length_quotient_pow_maximalIdeal] at hle
    exact ENat.natCast_ne_top _ (by rwa [Nat.cast_sum])
  let := Fintype.ofFinite κ
  refine Fintype.exists_equiv_of_forall_sum_min_eq he he' fun k ↦ ?_
  have h := length_quotient_pow_maximalIdeal_smul_top (LinearEquiv.refl R _) (e := e) k
  rw [length_quotient_pow_maximalIdeal_smul_top f k] at h
  exact_mod_cast h.symm

end TauCeti.IsDiscreteValuationRing
