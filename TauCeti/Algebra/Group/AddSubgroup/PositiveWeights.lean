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

## Main result

* `AddSubgroup.exists_pos_dotProduct_eq_zero_iff`.

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
    set S := Submodule.span ℚ ((fun p : ι → ℤ => ((↑) : ℤ → ℚ) ∘ p) '' P)
    -- The rational span of `P` has no nonzero nonnegative vector either.
    have hS : ∀ x ∈ S, 0 ≤ x → x = 0 := by
      intro x hx hx0
      obtain ⟨N, hN, p, hp, hpx⟩ := AddSubgroup.exists_nat_mul_eq_intCast_of_mem_span hx
      have hp0 : p = 0 := h p hp fun i => by
        have : (0 : ℚ) ≤ p i := by
          rw [hpx]
          exact mul_nonneg (Nat.cast_nonneg N) (hx0 i)
        exact_mod_cast this
      funext i
      have := hpx i
      rw [hp0, Pi.zero_apply, Int.cast_zero, eq_comm, mul_eq_zero] at this
      exact this.resolve_left (Nat.cast_ne_zero.2 hN.ne')
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
    · have hcp := hcS _ (Submodule.subset_span ⟨p, hp, rfl⟩)
      have : ((e ⬝ᵥ p : ℤ) : ℚ) = N * (c ⬝ᵥ (((↑) : ℤ → ℚ) ∘ p)) := by
        simp only [dotProduct, Int.cast_sum, Int.cast_mul, he, Finset.mul_sum,
          Function.comp_apply, mul_assoc]
      rw [hcp, mul_zero] at this
      exact_mod_cast this

end TauCeti
