/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Independence
public import Mathlib.Topology.Algebra.Algebra

/-!
# Free independence and topological closure

For a continuous normalised functional on an algebra with separately continuous multiplication,
a family of subalgebras is free if and only if its topological closures are free. This applies
both to norm closures and to weak operator closures when the functional is weak-operator
continuous, for example a vector state. Positivity, traciality and completeness are unnecessary.

The proof approximates one letter at a time and centres it by subtracting its expectation.
Joint continuity of multiplication is not needed: all other letters stay fixed.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 5.
-/

public section

namespace TauCeti

variable {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A]
  [TopologicalSpace R] [T1Space R] [TopologicalSpace A] [IsSemitopologicalRing A]
  [ContinuousSMul R A] {φ : A →ₗ[R] R} {B : ι → Subalgebra R A}

/-- Extend a centered alternating word from right to left, leaving an original-algebra prefix
and a closure-algebra suffix. Only the next letter is varied in each approximation. -/
private theorem apply_prod_append_eq_zero (h : IsFreelyIndependent φ B)
    (hφ : φ 1 = 1) (hcont : Continuous φ) (v : List (ι × A)) :
    ∀ u : List (ι × A), u ++ v ≠ [] → ((u ++ v).map Prod.fst).IsChain (· ≠ ·) →
      (∀ x ∈ u, x.2 ∈ B x.1) → (∀ x ∈ v, x.2 ∈ (B x.1).topologicalClosure) →
      (∀ x ∈ u ++ v, φ x.2 = 0) → φ ((u ++ v).map Prod.snd).prod = 0 := by
  induction v with
  | nil =>
    intro u hne halt hu _ hc
    simpa using isFreelyIndependent_iff.1 h u (by simpa using hne)
      (by simpa using halt) hu (by simpa using hc)
  | cons x v ih =>
    intro u hne halt hu hv hc
    let F (a : A) := φ ((u.map Prod.snd).prod *
      (a - algebraMap R A (φ a)) * (v.map Prod.snd).prod)
    have hF : Continuous F :=
      hcont.comp (((continuous_id.sub ((continuous_algebraMap R A).comp hcont)).const_mul
        (u.map Prod.snd).prod).mul_const (v.map Prod.snd).prod)
    have hz : (B x.1 : Set A) ⊆ F ⁻¹' {0} := by
      intro a ha
      have hlabels : ((u ++ [(x.1, a - algebraMap R A (φ a))]) ++ v).map Prod.fst =
          (u ++ x :: v).map Prod.fst := by simp
      have := ih (u ++ [(x.1, a - algebraMap R A (φ a))])
        (by simp) (hlabels ▸ halt) ?_ (fun y hy => hv y (by simp [hy])) ?_
      · simpa [F, List.map_append, List.prod_append, mul_assoc] using this
      · simp only [List.mem_append, List.mem_singleton]
        rintro y (hy | rfl)
        · exact hu y hy
        · exact sub_mem ha (Subalgebra.algebraMap_mem _ _)
      · simp only [List.mem_append, List.mem_singleton]
        rintro y ((hy | rfl) | hy)
        · exact hc y (by simp [hy])
        · simp [Algebra.algebraMap_eq_smul_one, hφ]
        · exact hc y (by simp [hy])
    have hx : F x.2 = 0 :=
      closure_minimal hz (isClosed_singleton.preimage hF) (hv x (by simp))
    simpa [F, hc x (by simp), List.map_append, List.prod_append, mul_assoc] using hx

/-- Free independence for a continuous normalised functional passes to the topological
closures of the subalgebras. Separately continuous multiplication suffices, including for
weak operator closures and a weak-operator continuous functional. -/
theorem IsFreelyIndependent.topologicalClosure (h : IsFreelyIndependent φ B)
    (hφ : φ 1 = 1) (hcont : Continuous φ) :
    IsFreelyIndependent φ fun i => (B i).topologicalClosure := by
  rw [isFreelyIndependent_iff]
  intro w hne halt hw hc
  simpa using apply_prod_append_eq_zero h hφ hcont w [] (by simpa using hne)
    (by simpa using halt) (by simp) hw (by simpa using hc)

/-- Taking topological closures does not change free independence for a continuous
normalised functional. -/
theorem isFreelyIndependent_topologicalClosure_iff (hφ : φ 1 = 1) (hcont : Continuous φ) :
    (IsFreelyIndependent φ fun i => (B i).topologicalClosure) ↔ IsFreelyIndependent φ B :=
  ⟨fun h => h.mono fun i => (B i).le_topologicalClosure,
    fun h => h.topologicalClosure hφ hcont⟩

end TauCeti
