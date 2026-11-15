/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Sign
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Polynomial relations on semialgebraic sets with empty interior

A real semialgebraic set with empty interior is contained in the zero set of a single nonzero
polynomial. No boundedness, closedness or regularity assumption is needed. This is the algebraic
step that turns semialgebraic graphs into algebraic relations.

In a finite sign presentation, a point where none of the nonzero defining polynomials vanishes
is an interior point: all the signs are locally constant there. Consequently the product of
the nonzero defining polynomials vanishes on the set. Identically zero polynomials must be
omitted from this product. The empty set is included, with the empty product equal to one.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998,
  Section 2.8 (dimension) and Section 8.1 (Nash functions).
-/

public section

open Filter MvPolynomial Set Topology

namespace TauCeti

/-- A real semialgebraic set with empty interior satisfies a nonzero polynomial equation.
The index type need not be finite: a semialgebraic presentation uses only finitely many
polynomials, each involving only finitely many coordinates. -/
theorem IsSemialgebraic.exists_ne_zero_polynomial_of_interior_eq_empty {σ : Type*}
    {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) (hint : interior s = ∅) :
    ∃ p : MvPolynomial σ ℝ, p ≠ 0 ∧ ∀ x ∈ s, eval x p = 0 := by
  classical
  obtain ⟨m, p, Φ, hpres⟩ := hs.exists_eq_setOf_sign_eval
  let I : Finset (Fin m) := Finset.univ.filter fun i ↦ p i ≠ 0
  refine ⟨∏ i ∈ I, p i, Finset.prod_ne_zero_iff.mpr (fun i hi ↦ (Finset.mem_filter.mp hi).2), ?_⟩
  intro x hx
  have hzero : ∃ i ∈ I, eval x (p i) = 0 := by
    by_contra h
    have hne (i : Fin m) (hi : p i ≠ 0) : eval x (p i) ≠ 0 :=
      fun hxi ↦ h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hxi⟩
    have hsign (i : Fin m) :
        ∀ᶠ y in 𝓝 x, SignType.sign (eval y (p i)) = SignType.sign (eval x (p i)) := by
      by_cases hi : p i = 0
      · simp [hi]
      · exact ((continuousAt_sign_of_ne_zero (hne i hi)).comp
          (f := fun y : σ → ℝ ↦ eval y (p i)) (p i).continuous_eval.continuousAt).preimage_mem_nhds
            ((isOpen_discrete _).mem_nhds (mem_singleton _))
    have hmem : s ∈ 𝓝 x := by
      filter_upwards [eventually_all.mpr hsign] with y hy
      rw [hpres] at hx ⊢
      simpa only [mem_ofPred_eq, funext hy] using hx
    have := mem_interior_iff_mem_nhds.mpr hmem
    simp [hint] at this
  obtain ⟨i, hi, hxi⟩ := hzero
  rw [map_prod]
  exact Finset.prod_eq_zero hi hxi

end TauCeti
