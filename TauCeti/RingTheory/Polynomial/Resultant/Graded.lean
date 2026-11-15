/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMonoid
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.RingTheory.Polynomial.Resultant.Normalization

/-!
# Graded degree of the discriminant

Let `A` be a commutative ring equipped with a multiplicative grading `𝒜 : M → S` by additive
subgroups, and let `f : A[X]` be a polynomial of degree `m = f.natDegree` whose `k`-th coefficient
lies in `𝒜 ((m - k) • w)` for every `k ≤ m`. Then the discriminant `f.discr` lies in
`𝒜 ((m * (m - 1)) • w)`. When `f` is monic, its leading coefficient `1` automatically lies in
`𝒜 0`, so the hypothesis need only be checked for `k < m`.

Rather than tracking homogeneity entry by entry through the Sylvester matrix, we prove weighted
homogeneity once for the universal degree-`m` polynomial `∑_{i ≤ m} Xᵢ Tⁱ` over
`ℤ[X₀, …, Xₘ]`, where `Xᵢ` has weight `m - i`: scaling `Xᵢ` by `2 ^ (m - i)` is root-scaling by
`2`, which multiplies the discriminant by `2 ^ (m * (m - 1))` (`Polynomial.discr_scaleRoots`).
Specializing `Xᵢ ↦ f.coeff i` preserves `natDegree` and maps the universal discriminant into the
pulled-back `ℕ`-grading `n ↦ 𝒜 (n • w)` via `MvPolynomial.IsWeightedHomogeneous.eval₂_mem`.

## Main results

* `Polynomial.discr_mem_graded`: if `f.coeff k ∈ 𝒜 ((f.natDegree - k) • w)` for all
  `k ≤ f.natDegree`, then `f.discr ∈ 𝒜 ((f.natDegree * (f.natDegree - 1)) • w)`.
* `Polynomial.Monic.discr_mem_graded`: for monic `f`, it suffices that
  `f.coeff k ∈ 𝒜 ((f.natDegree - k) • w)` for all `k < f.natDegree`.
-/

public section

namespace Polynomial

/-- The universal polynomial `∑_{i ≤ m} Xᵢ Tⁱ` over `ℤ[X₀, …, Xₘ]`. -/
private noncomputable def universalPoly (m : ℕ) : Polynomial (MvPolynomial (Fin (m + 1)) ℤ) :=
  ∑ i : Fin (m + 1), C (MvPolynomial.X i) * X ^ i.val

private theorem coeff_universalPoly (m k : ℕ) :
    (universalPoly m).coeff k =
      if hk : k < m + 1 then MvPolynomial.X ⟨k, hk⟩ else 0 := by
  rw [universalPoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  split_ifs with hk
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro i _ hne
      exact ite_eq_right fun h ↦ hne (Fin.ext h.symm)
    · simp
  · exact Finset.sum_eq_zero fun i _ ↦ ite_eq_right (by omega)

private theorem natDegree_universalPoly (m : ℕ) : (universalPoly m).natDegree = m := by
  refine le_antisymm ?_ ?_
  · rw [universalPoly]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ ?_
    exact natDegree_C_mul_X_pow_le (MvPolynomial.X i) i.val |>.trans (Nat.lt_succ_iff.mp i.isLt)
  · refine le_natDegree_of_ne_zero ?_
    simp [coeff_universalPoly]

/-- The discriminant of `∑_{i ≤ m} Xᵢ Tⁱ` is weighted homogeneous of weight `m * (m - 1)` when
`Xᵢ` has weight `m - i`. -/
private theorem isWeightedHomogeneous_discr_universalPoly (m : ℕ) :
    (universalPoly m).discr.IsWeightedHomogeneous (fun i : Fin (m + 1) ↦ m - i.val)
      (m * (m - 1)) := by
  let u : Fin (m + 1) → ℕ := fun i ↦ m - i.val
  let ψ : MvPolynomial (Fin (m + 1)) ℤ →ₐ[ℤ] MvPolynomial (Fin (m + 1)) ℤ :=
    MvPolynomial.aeval fun i ↦ MvPolynomial.C ((2 : ℤ) ^ u i) * MvPolynomial.X i
  -- Scaling `Xᵢ` by `2 ^ (m - i)` agrees coefficient by coefficient with `scaleRoots` by `2`.
  have hscale : (universalPoly m).map ψ.toRingHom =
      (universalPoly m).scaleRoots (MvPolynomial.C (2 : ℤ)) := by
    ext k
    rw [coeff_map, coeff_scaleRoots, natDegree_universalPoly, coeff_universalPoly]
    split_ifs with hk
    · simp [ψ, u, mul_comm]
    · simp
  have hdeg : ((universalPoly m).map ψ.toRingHom).natDegree = (universalPoly m).natDegree := by
    rw [hscale, natDegree_scaleRoots]
  have h2 : Function.Injective ((2 : ℤ) ^ · : ℕ → ℤ) := fun a b (hab : (2 : ℤ) ^ a = (2 : ℤ) ^ b) ↦
    Nat.pow_right_injective (by decide : 2 ≤ 2) (by exact_mod_cast hab)
  refine MvPolynomial.isWeightedHomogeneous_of_aeval_C_pow_mul_X_eq h2 ?_
  have hmap := discr_map_of_natDegree_eq ψ.toRingHom hdeg
  rw [hscale, discr_scaleRoots, natDegree_universalPoly, ← map_pow, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] at hmap
  exact hmap.symm

variable {A M S : Type*} [CommRing A] [AddMonoid M] [SetLike S A] [AddSubgroupClass S A]
  {𝒜 : M → S} [SetLike.GradedMonoid 𝒜]

/-- If the `k`-th coefficient of `f : A[X]` lies in the graded piece `𝒜 ((f.natDegree - k) • w)`
for every `k ≤ f.natDegree`, then `f.discr` lies in `𝒜 ((f.natDegree * (f.natDegree - 1)) • w)`. -/
theorem discr_mem_graded {f : A[X]} {w : M}
    (hc : ∀ k ≤ f.natDegree, f.coeff k ∈ 𝒜 ((f.natDegree - k) • w)) :
    f.discr ∈ 𝒜 ((f.natDegree * (f.natDegree - 1)) • w) := by
  set m := f.natDegree
  -- Pull `𝒜` back along `(· • w)` to an `ℕ`-grading by additive subgroups of `A`.
  let ℬ : ℕ → AddSubgroup A := fun n ↦
    { carrier := 𝒜 (n • w)
      add_mem' := add_mem
      zero_mem' := zero_mem _
      neg_mem' := neg_mem }
  have : SetLike.GradedMonoid ℬ :=
    { one_mem := by simpa [ℬ] using SetLike.one_mem_graded 𝒜
      mul_mem := fun i j a b ha hb ↦ by
        simpa [ℬ, add_nsmul] using SetLike.mul_mem_graded (A := 𝒜) ha hb }
  let φ : MvPolynomial (Fin (m + 1)) ℤ →+* A :=
    MvPolynomial.eval₂Hom (Int.castRingHom A) (fun i : Fin (m + 1) ↦ f.coeff i.val)
  have hmap : (universalPoly m).map φ = f := by
    ext k
    rw [coeff_map, coeff_universalPoly]
    split_ifs with hk
    · simp [φ]
    · simp only [map_zero]
      exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hdeg : ((universalPoly m).map φ).natDegree = (universalPoly m).natDegree := by
    rw [hmap, natDegree_universalPoly]
  have hmem : MvPolynomial.eval₂ (Int.castRingHom A) (fun i : Fin (m + 1) ↦ f.coeff i.val)
      (universalPoly m).discr ∈ ℬ (m * (m - 1)) := by
    refine (isWeightedHomogeneous_discr_universalPoly m).eval₂_mem (𝒜 := ℬ) (fun r ↦ ?_)
      fun i ↦ hc i.val (Nat.lt_succ_iff.mp i.isLt)
    simpa using (ℬ 0).zsmul_mem (SetLike.one_mem_graded ℬ) r
  rw [← hmap, discr_map_of_natDegree_eq φ hdeg]
  exact hmem

/-- For a monic polynomial `f : A[X]`, if `f.coeff k ∈ 𝒜 ((f.natDegree - k) • w)` for every
`k < f.natDegree`, then `f.discr ∈ 𝒜 ((f.natDegree * (f.natDegree - 1)) • w)`. -/
theorem Monic.discr_mem_graded {f : A[X]} (hf : f.Monic) {w : M}
    (hc : ∀ k < f.natDegree, f.coeff k ∈ 𝒜 ((f.natDegree - k) • w)) :
    f.discr ∈ 𝒜 ((f.natDegree * (f.natDegree - 1)) • w) := by
  refine Polynomial.discr_mem_graded fun k hk ↦ ?_
  rcases hk.lt_or_eq with hlt | rfl
  · exact hc k hlt
  · rw [tsub_self, zero_nsmul, hf.coeff_natDegree]
    exact SetLike.GradedOne.one_mem

end Polynomial
