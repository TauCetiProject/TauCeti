/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.UpperBound.Lattice
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# From invariant upper bounds to Laurent membership

For subrings of a fixed ring, upper-bound invariance and one-step membership of
generators imply that every reachable generator belongs to every reachable chart.
This separates the global propagation argument from the local exchange algebra:
there are no rank, commutativity, or finiteness assumptions in this file.

The argument abstracts Berenstein–Fomin–Zelevinsky, *Cluster algebras III: Upper bounds
and double Bruhat cells*, Corollary 1.9, and Berenstein–Zelevinsky, *Quantum cluster
algebras*, §5. It asserts no local exchange theorem for a seed.
-/

public section

namespace TauCeti.Mutation

variable {K V D I : Type*} [NonAssocRing D]
variable (μ : K → V → V) (T : V → Subring D)

/-- Membership in an upper bound means membership in the initial and all adjacent
chart subrings. -/
@[simp]
theorem mem_upperBound {s : V} {x : D} :
    x ∈ upperBound μ T s ↔ x ∈ T s ∧ ∀ k, x ∈ T (μ k s) := by
  simp [upperBound_def, Subring.mem_iInf]

/-- Every reachable generator lies in every reachable chart if upper bounds are
invariant and initial and one-step generators lie in the initial chart at every state.
The ambient ring may be noncommutative, and the labels may be infinite or empty. -/
theorem mem_chart_foldl_of_upperBound_invariant
    (hμ : ∀ k, Function.Involutive (μ k))
    (hinv : ∀ s k, upperBound μ T (μ k s) = upperBound μ T s)
    (g : V → I → D) (hself : ∀ s a, g s a ∈ T s)
    (hstep : ∀ s k a, g (μ k s) a ∈ T s)
    (s : V) (p w : List K) (a : I) :
    g (w.foldl (fun t k ↦ μ k t) s) a ∈ T (p.foldl (fun t k ↦ μ k t) s) := by
  have hg (t : V) : g t a ∈ upperBound μ T t := by
    refine (mem_upperBound μ T).2 ⟨hself t a, fun k ↦ ?_⟩
    simpa only [hμ k t] using hstep (μ k t) k a
  have heq : upperBound μ T (w.foldl (fun t k ↦ μ k t) s) =
      upperBound μ T (p.foldl (fun t k ↦ μ k t) s) :=
    (upperBound_foldl μ T hinv s w).trans (upperBound_foldl μ T hinv s p).symm
  exact upperBound_le μ T _ (heq ▸ hg _)

end TauCeti.Mutation
