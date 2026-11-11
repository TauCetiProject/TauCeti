/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.AddSubgroup.RationalSpan
public import TauCeti.Geometry.Convex.Cone.Alternative
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Positive weights orthogonal to integer subgroups

A subgroup of `ι → ℤ` contains no nonzero nonnegative vector exactly when it is orthogonal to a
vector of strictly positive integer weights. This is the integer-lattice form of Stiemke's theorem.

For a pointed Heegaard diagram, `ι` indexes its regions, and `P` is the subgroup of periodic
domains. Weak admissibility, for all `Spin^c` structures at once, says every nonzero periodic
domain has positive and negative multiplicities. Since `P` is closed under negation, this is the
condition below. The weights give positive target areas for the regions, with zero signed area
for every periodic domain. Applying the result to diagrams requires a separate construction of
their periodic-domain subgroup.

## Main results

* `AddSubgroup.exists_pos_dotProduct_eq_zero_iff`.
* `AddSubgroup.exists_pos_sum_mul_intCast_eq_zero_iff`: the same with weights in an ordered
  field.
* `TauCeti.sum_mul_intCast_eq_of_sub_mem`: weights orthogonal to a subgroup of `ι → ℤ` pair
  equally with all vectors of a coset.

## Reference

* P. Ozsváth, Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. 159 (2004), Lemma 4.12.
-/

public section

namespace TauCeti

variable {ι : Type*}

/-- A subgroup `P` of `ι → ℤ` contains no nonzero nonnegative vector exactly when some vector of
strictly positive integer weights is orthogonal to all of `P`.

For the group of periodic domains of a pointed Heegaard diagram, the weights are the areas of the
regions for an area form in which every periodic domain has signed area zero; compare
Ozsváth–Szabó, *Holomorphic disks and topological invariants for closed three-manifolds*,
Lemma 4.12. -/
theorem _root_.AddSubgroup.exists_pos_dotProduct_eq_zero_iff [Fintype ι] (P : AddSubgroup (ι → ℤ)) :
    (∃ c : ι → ℤ, (∀ i, 0 < c i) ∧ ∀ p ∈ P, c ⬝ᵥ p = 0) ↔ ∀ p ∈ P, 0 ≤ p → p = 0 := by
  constructor
  · rintro ⟨c, hc, hP⟩ p hp hp0
    exact (dotProduct_eq_zero_iff_of_pos hc hp0).1 (hP p hp)
  · intro h
    set f : (ι → ℤ) →+ ι → ℚ := (Int.castAddHom ℚ).compLeft ι
    set S := Submodule.span ℚ (P.map f : Set (ι → ℚ))
    -- The rational span of `P` has no nonzero nonnegative vector either.
    have hS : ∀ x ∈ S, 0 ≤ x → x = 0 := by
      intro x hx hx0
      obtain ⟨N, hN, p, hp, hpx⟩ := (P.map f).mem_rat_span_iff_exists_nsmul_mem.1 hx
      have hfp : 0 ≤ f p := hpx ▸ nsmul_nonneg hx0 N
      have hp0 : p = 0 := h p hp fun i => by simpa [f] using hfp i
      rw [hp0, map_zero, eq_comm, smul_eq_zero] at hpx
      exact hpx.resolve_left hN.ne'
    obtain ⟨c, hc, hcS⟩ := S.exists_pos_dotProduct_eq_zero_iff.2 hS
    -- Clear the denominators of the rational weights.
    set N : ℕ := ∏ i, (c i).den
    have hN : 0 < N := Finset.prod_pos fun i _ => (c i).den_pos
    have hint : ∀ i, ∃ z : ℤ, (z : ℚ) = N * c i := fun i => by
      obtain ⟨m, hm⟩ : (c i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨m * (c i).num, ?_⟩
      rw [hm]
      push_cast
      rw [← Rat.mul_den_eq_num]
      ring
    choose e he using hint
    refine ⟨e, fun i => ?_, fun p hp => ?_⟩
    · have : (0 : ℚ) < e i := by
        rw [he]
        exact mul_pos (Nat.cast_pos.2 hN) (hc i)
      exact_mod_cast this
    · have hcp := hcS _ (Submodule.subset_span (P.mem_map_of_mem f hp))
      have : ((e ⬝ᵥ p : ℤ) : ℚ) = N * (c ⬝ᵥ f p) := by
        simp only [dotProduct, Int.cast_sum, Int.cast_mul, he, Finset.mul_sum, f,
          AddMonoidHom.compLeft_apply, Function.comp_apply, Int.coe_castAddHom, mul_assoc]
      rw [hcp, mul_zero] at this
      exact_mod_cast this

/-- A subgroup `P` of `ι → ℤ` contains no nonzero nonnegative vector exactly when some vector of
strictly positive weights in an ordered field `K` is orthogonal to all of `P`. -/
theorem _root_.AddSubgroup.exists_pos_sum_mul_intCast_eq_zero_iff [Fintype ι] {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] (P : AddSubgroup (ι → ℤ)) :
    (∃ w : ι → K, (∀ i, 0 < w i) ∧ ∀ p ∈ P, ∑ i, w i * p i = 0) ↔
      ∀ p ∈ P, 0 ≤ p → p = 0 := by
  refine ⟨fun ⟨w, hw, hwP⟩ p hp hp₀ => ?_, fun h => ?_⟩
  · have hp₀' : (0 : ι → K) ≤ fun i => (p i : K) := fun i => Int.cast_nonneg (hp₀ i)
    have := (dotProduct_eq_zero_iff_of_pos hw hp₀').1 (hwP p hp)
    exact funext fun i => by simpa using congrFun this i
  · -- Integer weights are weights in `K`.
    obtain ⟨c, hc, hcP⟩ := P.exists_pos_dotProduct_eq_zero_iff.2 h
    refine ⟨fun i => c i, fun i => Int.cast_pos.2 (hc i), fun p hp => ?_⟩
    simpa [dotProduct] using congrArg (Int.cast : ℤ → K) (hcP p hp)

/-- Weights `w` orthogonal to every element of a subgroup `P` of `ι → ℤ` pair equally with any two
vectors that differ by an element of `P`. -/
theorem sum_mul_intCast_eq_of_sub_mem [Fintype ι] {R : Type*} [CommRing R]
    {P : AddSubgroup (ι → ℤ)} {w : ι → R} (hw : ∀ p ∈ P, ∑ i, w i * p i = 0) {v v' : ι → ℤ}
    (h : v' - v ∈ P) : ∑ i, w i * v' i = ∑ i, w i * v i := by
  simpa [mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using hw _ h

end TauCeti
