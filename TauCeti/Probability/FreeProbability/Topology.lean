/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Independence
public import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.NhdsWithin

/-!
# Free independence and topological closure

For a continuous normalised functional on a topological algebra, a family of subalgebras is
free if and only if its topological closures are free. In particular this applies to norm
closures in a C*-probability space. Positivity, traciality and completeness are unnecessary.

The proof approximates arbitrary letters and centres them by subtracting their expectations.
Thus the approximating letters remain centred, although the original approximations need not
have zero expectation.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 5.
-/

public section

namespace TauCeti

variable {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A]
  [TopologicalSpace R] [T1Space R] [TopologicalSpace A] [IsTopologicalRing A]
  [ContinuousSMul R A] {φ : A →ₗ[R] R} {B : ι → Subalgebra R A}

/-- Free independence for a continuous normalised functional passes to the topological
closures of the subalgebras. In normed algebras these are the norm closures. -/
theorem IsFreelyIndependent.topologicalClosure (h : IsFreelyIndependent φ B)
    (hφ : φ 1 = 1) (hcont : Continuous φ) :
    IsFreelyIndependent φ fun i => (B i).topologicalClosure := by
  rw [isFreelyIndependent_iff]
  intro w hne halt hw hc
  let F (a : {x // x ∈ w} → A) := φ (w.attach.map fun x => a x - algebraMap R A (φ (a x))).prod
  have hF : Continuous F := by
    apply hcont.comp
    exact continuous_list_prod w.attach fun x _ =>
      (continuous_apply x).sub ((continuous_algebraMap R A).comp
        (hcont.comp (continuous_apply x)))
  have hzero : Set.pi Set.univ (fun x : {x // x ∈ w} => (B x.val.1 : Set A)) ⊆ F ⁻¹' {0} := by
    intro a ha
    have hz := isFreelyIndependent_iff.1 h
      (w.attach.map fun x => (x.val.1, a x - algebraMap R A (φ (a x))))
      (by simpa only [ne_eq, List.map_eq_nil_iff, List.attach_eq_nil_iff] using hne)
      (by simpa only [List.map_map, Function.comp_def,
        List.attach_map_val (f := Prod.fst)] using halt) ?_ ?_
    · simpa only [F, Set.mem_preimage, Set.mem_singleton_iff, List.map_map,
        Function.comp_def] using hz
    · simp only [List.mem_map]
      rintro _ ⟨x, _, rfl⟩
      exact sub_mem (ha x (Set.mem_univ _)) (Subalgebra.algebraMap_mem _ _)
    · simp only [List.mem_map]
      rintro _ ⟨x, _, rfl⟩
      simp [Algebra.algebraMap_eq_smul_one, hφ]
  have hz : F (fun x : {x // x ∈ w} => x.val.2) = 0 :=
    closure_minimal hzero (isClosed_singleton.preimage hF)
      (mem_closure_pi.2 fun x _ => hw x.val x.property)
  have hcenter (x : {x // x ∈ w}) : x.val.2 - algebraMap R A (φ x.val.2) = x.val.2 := by
    rw [hc x.val x.property, map_zero, sub_zero]
  simpa only [F, hcenter, List.attach_map_val (f := Prod.snd)] using hz

/-- Taking topological closures does not change free independence for a continuous
normalised functional. -/
theorem isFreelyIndependent_topologicalClosure_iff (hφ : φ 1 = 1) (hcont : Continuous φ) :
    (IsFreelyIndependent φ fun i => (B i).topologicalClosure) ↔ IsFreelyIndependent φ B :=
  ⟨fun h => h.mono fun i => (B i).le_topologicalClosure,
    fun h => h.topologicalClosure hφ hcont⟩

end TauCeti
