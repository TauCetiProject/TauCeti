/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Nonnegative weighted orbit counting

An invariant extended nonnegative weight on a set acted on by a finite group can be summed
orbitwise. Dividing the total weight by the group order gives one term per orbit, divided by
the order of its stabilizer. The set and its orbit space need not be finite, and the weights
may be infinite. This is the counting identity relating labelled objects to automorphism-weighted
isomorphism classes.
-/

public section

noncomputable section

open scoped ENNReal

namespace MulAction

variable {G X : Type*} [Group G] [Finite G] [MulAction G X]

/-- An invariant nonnegative weight sums to the orbit size times the weight of a representative,
summed over all orbits. No finiteness of the acted-on set is required. -/
theorem tsum_eq_tsum_natCard_orbit_mul (f : X → ℝ≥0∞)
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    ∑' x, f x = ∑' ω : orbitRel.Quotient G X,
      (Nat.card (orbit G ω.out) : ℝ≥0∞) * f ω.out := by
  classical
  rw [← tsum_fiberwise f (Quotient.mk'' : X → orbitRel.Quotient G X)]
  apply tsum_congr
  intro ω
  have hset : (Quotient.mk'' : X → orbitRel.Quotient G X) ⁻¹' {ω} = orbit G ω.out := by
    rw [← orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
    ext x
    exact orbitRel.Quotient.mem_orbit.symm
  rw [hset]
  have := (Finite.finite_mulAction_orbit (M := G) ω.out).to_subtype
  have hconst (x : orbit G ω.out) : f x = f ω.out := by
    obtain ⟨g, hg⟩ := x.property
    rw [← hg, hf]
  simp_rw [hconst]
  simp [ENNReal.tsum_const, ← Set.coe_ncard_eq_encard]

/-- Dividing a labelled sum by the order of the finite acting group gives the sum over orbits
with inverse-stabilizer weights. Infinite orbit spaces and infinite weights are allowed. -/
theorem inv_natCard_mul_tsum_eq_tsum_div_natCard_stabilizer (f : X → ℝ≥0∞)
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    (Nat.card G : ℝ≥0∞)⁻¹ * ∑' x, f x =
      ∑' ω : orbitRel.Quotient G X, f ω.out / (Nat.card (stabilizer G ω.out) : ℝ≥0∞) := by
  classical
  rw [tsum_eq_tsum_natCard_orbit_mul f hf, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro ω
  have hc : Nat.card (orbit G ω.out) * Nat.card (stabilizer G ω.out) = Nat.card G := by
    rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup G ω.out)]
  have := (Finite.finite_mulAction_orbit (M := G) ω.out).to_subtype
  have : Nonempty (orbit G ω.out) := ⟨⟨ω.out, mem_orbit_self _⟩⟩
  have ho : (Nat.card (orbit G ω.out) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := orbit G ω.out)).ne'
  rw [← hc, Nat.cast_mul]
  simpa only [ENNReal.div_eq_inv_mul] using
    ENNReal.mul_div_mul_left (f ω.out) (Nat.card (stabilizer G ω.out)) ho (by simp)

end MulAction
