/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.Data.Fintype.Lattice

/-!
# Finite intersections of covering sieves

This file records that in any Grothendieck topology, the intersection of a finite family of
covering sieves is again a covering sieve (`CategoryTheory.GrothendieckTopology.iInf_mem`).
-/

public section

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {X : C}

/-- The intersection of a finite family of covering sieves in a Grothendieck topology is a
covering sieve. -/
theorem iInf_mem {ι : Type*} [Finite ι] {R : ι → Sieve X} (hR : ∀ i, R i ∈ J X) :
    (⨅ i, R i) ∈ J X := by
  have := Fintype.ofFinite ι
  rw [← Finset.inf_univ_eq_iInf]
  exact Finset.inf_induction (p := (· ∈ J X)) (J.top_mem X)
    (fun _ h₁ _ h₂ ↦ J.intersection_covering h₁ h₂) (fun i _ ↦ hR i)

/-- The intersection of a finite family of sieves in a Grothendieck topology is a covering sieve
if and only if every sieve in the family is covering. -/
theorem iInf_mem_iff {ι : Type*} [Finite ι] {R : ι → Sieve X} :
    (⨅ i, R i) ∈ J X ↔ ∀ i, R i ∈ J X :=
  ⟨fun h i ↦ J.superset_covering (iInf_le R i) h, J.iInf_mem⟩

end CategoryTheory.GrothendieckTopology
