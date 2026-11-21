/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Coordinate coroot functionals

For a base `b` of a crystallographic root pairing `P`, the pairings `P.pairingIn ℤ (i : ι) j`
define the coordinate coroot functional `b.corootEval S j : (b.support → S) →ₗ[S] S` over any
commutative ring `S` without `[P.IsRootSystem]` or an algebra map `R → S`. At any coordinate vector
`y : b.support → S` over a partially ordered commutative ring `S` where every simple coroot
functional `b.corootEval S (k : ι) y` is strictly positive, positivity of `b.corootEval S j y`
characterizes `j ∈ posRoots P b`.

## Main definitions
* `RootPairing.Base.corootEval`: coordinate evaluation of the `j`-th coroot on `b.support → S`.

## Main results
* `RootPairing.Base.coroot'_sum_smul_root`, `RootPairing.Base.liftBaseChange_coroot'_sum_tmul_root`:
  agreement of `corootEval` with `P.coroot'` on simple-root combinations in `M` and `S ⊗[R] M`.
* `RootPairing.Base.exists_corootEval_eq_sum_nat_of_mem_posRoots`,
  `RootPairing.Base.corootEval_pos_iff_mem_posRoots`,
  `RootPairing.Base.corootEval_ne_zero_of_forall_pos`: positive coroot expansion and sign
  characterization over any partially ordered commutative ring.
-/

public section

open TauCeti

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] (b : P.Base)

/-- Evaluation of the `j`-th coroot functional on formal simple-root coordinate vectors
`b.support → S`, defined using the crystallographic integer pairings `⟨αᵢ, αⱼ^∨⟩`. -/
noncomputable def corootEval (S : Type*) [CommRing S] (j : ι) : (b.support → S) →ₗ[S] S where
  toFun y := ∑ i : b.support, (P.pairingIn ℤ (i : ι) j : S) * y i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c y := by simp [mul_left_comm, Finset.mul_sum]

/-- Explicit formula for `RootPairing.Base.corootEval`. -/
theorem corootEval_apply (S : Type*) [CommRing S] (j : ι) (y : b.support → S) :
    b.corootEval S j y = ∑ i : b.support, (P.pairingIn ℤ (i : ι) j : S) * y i := (rfl)

/-- On `Pi.single i c`, `corootEval` evaluates to the `i`-th pairing scaled by `c`. -/
@[simp]
theorem corootEval_single [DecidableEq b.support] (S : Type*) [CommRing S] (j : ι)
    (i : b.support) (c : S) :
    b.corootEval S j (Pi.single i c) = (P.pairingIn ℤ (i : ι) j : S) * c := by
  simp [corootEval_apply, Pi.single_apply]

/-- On a simple root `k : b.support`, `corootEval` pairs against column `k` of `b.cartanMatrix`. -/
theorem corootEval_coe_support (S : Type*) [CommRing S] (k : b.support) (y : b.support → S) :
    b.corootEval S (k : ι) y = ∑ i : b.support, (b.cartanMatrix i k : S) * y i := by
  simp_rw [corootEval_apply, b.cartanMatrixIn_def ℤ]

/-- On `∑ i, y i • P.root i` in `M`, `P.coroot' j` agrees with `b.corootEval R j y`. -/
theorem coroot'_sum_smul_root (j : ι) (y : b.support → R) :
    P.coroot' j (∑ i : b.support, y i • P.root i) = b.corootEval R j y := by
  rw [map_sum, corootEval_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [map_smul, smul_eq_mul, root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, eq_intCast,
      mul_comm]

open TensorProduct in
/-- After scalar extension to a commutative `R`-algebra `S`, lifting `P.coroot' j` to
`S ⊗[R] M →ₗ[S] S` evaluates on simple-root coordinate combinations to `b.corootEval S j`. -/
theorem liftBaseChange_coroot'_sum_tmul_root {S : Type*} [CommRing S] [Algebra R S]
    (j : ι) (y : b.support → S) :
    LinearMap.liftBaseChange S (Algebra.linearMap R S ∘ₗ P.coroot' j)
      (∑ i : b.support, y i ⊗ₜ[R] P.root i) = b.corootEval S j y := by
  rw [map_sum, corootEval_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [← P.algebraMap_pairingIn ℤ, mul_comm]

/-- Root negation negates `corootEval`. -/
@[simp]
theorem corootEval_reflectionPerm_self [CharZero R] (S : Type*) [CommRing S] (j : ι) :
    b.corootEval S (P.reflectionPerm j j) = -b.corootEval S j := by
  ext y; simp [corootEval_apply, P.pairingIn_reflectionPerm_self_right, ← Finset.sum_neg_distrib]

variable [Finite ι] [CharZero R] [IsDomain R] [P.IsReduced]

/-- Positive coroot expansion for `corootEval`: for a positive root `j`, `b.corootEval S j` is a
nonnegative integer combination of the simple `corootEval` functionals, not all zero. -/
theorem exists_corootEval_eq_sum_nat_of_mem_posRoots {j : ι} (hj : j ∈ posRoots P b) :
    ∃ f : b.support → ℕ, (∃ k : b.support, f k ≠ 0) ∧
      ∀ (S : Type*) [CommRing S] (y : b.support → S),
        b.corootEval S j y = ∑ k : b.support, (f k : S) * b.corootEval S (k : ι) y := by
  have := P.flip_isReduced
  obtain ⟨f, ⟨k₀, hk₀, hfk₀⟩, hcor'⟩ := exists_coroot'_eq_sum_nat_of_mem_posRoots P b hj
  have hint (i : b.support) :
      P.pairingIn ℤ (i : ι) j = ∑ k : b.support, (f k : ℤ) * P.pairingIn ℤ (i : ι) (k : ι) := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    have hval := LinearMap.congr_fun hcor' (P.root i)
    rw [root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, LinearMap.sum_apply,
      ← Finset.sum_coe_sort b.support] at hval
    rw [hval, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by
      rw [LinearMap.smul_apply, smul_eq_mul, root_coroot'_eq_pairing, map_mul, map_natCast,
        P.algebraMap_pairingIn ℤ]
  refine ⟨fun k ↦ f k, ⟨⟨k₀, hk₀⟩, hfk₀⟩, fun S _ y ↦ ?_⟩
  simp only [corootEval_apply, Finset.mul_sum, hint, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    Finset.sum_mul]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

variable {S : Type*} [CommRing S] [PartialOrder S] [IsOrderedAddMonoid S]

/-- Positive simple coroot evaluations imply positive evaluation on every positive root. -/
theorem corootEval_pos_of_mem_posRoots {y : b.support → S}
    (hy : ∀ k : b.support, 0 < b.corootEval S (k : ι) y) {j : ι} (hj : j ∈ posRoots P b) :
    0 < b.corootEval S j y := by
  obtain ⟨f, ⟨k₀, hk₀⟩, hsum⟩ := b.exists_corootEval_eq_sum_nat_of_mem_posRoots hj
  rw [hsum S y]; simp_rw [← nsmul_eq_mul]
  exact Finset.sum_pos' (fun k _ ↦ nsmul_nonneg (hy k).le _)
    ⟨k₀, Finset.mem_univ k₀, nsmul_pos (hy k₀) hk₀⟩

/-- Positive simple coroot evaluations imply negative evaluation on every negative root. -/
theorem corootEval_neg_of_mem_negRoots {y : b.support → S}
    (hy : ∀ k : b.support, 0 < b.corootEval S (k : ι) y) {j : ι} (hj : j ∈ negRoots P b) :
    b.corootEval S j y < 0 := by
  have h := b.corootEval_pos_of_mem_posRoots hy
    ((mem_posRoots P b _).mpr ((isPos_reflectionPerm_self_iff_mem_negRoots P b j).mpr hj))
  rwa [corootEval_reflectionPerm_self, LinearMap.neg_apply, neg_pos] at h

/-- At `y` with positive simple coroots, `0 < b.corootEval S j y` characterizes `posRoots P b`. -/
theorem corootEval_pos_iff_mem_posRoots {y : b.support → S}
    (hy : ∀ k : b.support, 0 < b.corootEval S (k : ι) y) (j : ι) :
    0 < b.corootEval S j y ↔ j ∈ posRoots P b :=
  ⟨fun h ↦ by_contra fun hn ↦ lt_asymm
      (b.corootEval_neg_of_mem_negRoots hy ((not_mem_posRoots_iff_mem_negRoots P b j).mp hn)) h,
    b.corootEval_pos_of_mem_posRoots hy⟩

/-- When all simple coroot evaluations are positive, no coroot functional vanishes. -/
theorem corootEval_ne_zero_of_forall_pos {y : b.support → S}
    (hy : ∀ k : b.support, 0 < b.corootEval S (k : ι) y) (j : ι) :
    b.corootEval S j y ≠ 0 :=
  (em (j ∈ posRoots P b)).elim (fun hj ↦ (b.corootEval_pos_of_mem_posRoots hy hj).ne') fun hj ↦
    (b.corootEval_neg_of_mem_negRoots hy ((not_mem_posRoots_iff_mem_negRoots P b j).mp hj)).ne

end RootPairing.Base
